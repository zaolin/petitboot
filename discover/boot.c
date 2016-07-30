
#if defined(HAVE_CONFIG_H)
#include "config.h"
#endif

#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>
#include <dirent.h>
#include <string.h>
#include <fcntl.h>
#include <sys/types.h>

#include <log/log.h>
#include <pb-protocol/pb-protocol.h>
#include <process/process.h>
#include <system/system.h>
#include <talloc/talloc.h>
#include <url/url.h>
#include <util/util.h>
#include <i18n/i18n.h>

#if defined(HAVE_LIBGPGME)
#include <gpgme.h>
#endif

#include "device-handler.h"
#include "boot.h"
#include "paths.h"
#include "resource.h"

#define MAX_FILENAME_SIZE	8192
#define FILE_XFER_BUFFER_SIZE	8192

static const char *boot_hook_dir = PKG_SYSCONF_DIR "/boot.d";
enum {
	BOOT_HOOK_EXIT_OK	= 0,
	BOOT_HOOK_EXIT_UPDATE	= 2,
};

enum {
	KEXEC_LOAD_DECRYPTION_FALURE = 252,
	KEXEC_LOAD_SIG_SETUP_INVALID = 253,
	KEXEC_LOAD_SIGNATURE_FAILURE = 254,
};

struct boot_task {
	struct load_url_result *image;
	struct load_url_result *initrd;
	struct load_url_result *dtb;
	const char *local_image;
	const char *local_initrd;
	const char *local_dtb;
	const char *args;
	boot_status_fn status_fn;
	void *status_arg;
	bool dry_run;
	bool cancelled;
	bool verify_signature;
	bool decrypt_files;
	struct load_url_result *image_signature;
	struct load_url_result *initrd_signature;
	struct load_url_result *dtb_signature;
	struct load_url_result *cmdline_signature;
	const char *local_image_signature;
	const char *local_initrd_signature;
	const char *local_dtb_signature;
	const char *local_cmdline_signature;
};

static int copy_file_to_destination(const char * source_file,
	char * destination_file, int max_dest_filename_size) {
	int result = 0;
	char template[21] = "/tmp/petitbootXXXXXX";
	FILE *source_handle = fopen(source_file, "r");
	int destination_fd = mkstemp(template);
	FILE *destination_handle = fdopen(destination_fd, "w");
	if (!source_handle || !(destination_handle)) {
		// handle open error
		pb_log("%s: failed: unable to open source file '%s'\n",
			__func__, source_file);
		result = 1;
	}

	size_t l1;
	unsigned char buffer[FILE_XFER_BUFFER_SIZE];

	/* Copy data */
	while ((l1 = fread(buffer, 1, sizeof buffer, source_handle)) > 0) {
		size_t l2 = fwrite(buffer, 1, l1, destination_handle);
		if (l2 < l1) {
			if (ferror(destination_handle)) {
				/* General error */
				result = 1;
				pb_log("%s: failed: unknown fault\n", __func__);
			}
			else {
				/* No space on destination device */
				result = 2;
				pb_log("%s: failed: temporary storage full\n",
					__func__);
			}
		}
	}

	if (result) {
		destination_file[0] = '\0';
	}
	else {
		ssize_t r;
		char readlink_buffer[MAX_FILENAME_SIZE];
		snprintf(readlink_buffer, MAX_FILENAME_SIZE, "/proc/self/fd/%d",
			destination_fd);
		r = readlink(readlink_buffer, destination_file,
			max_dest_filename_size);
		if (r < 0) {
			/* readlink failed */
			result = 3;
			pb_log("%s: failed: unable to obtain temporary filename"
				"\n", __func__);
		}
		destination_file[r] = '\0';
	}

	fclose(source_handle);
	fclose(destination_handle);

	return result;
}

#if defined(HAVE_LIBGPGME)
static int decrypt_file(const char * filename,
	FILE * authorized_signatures_handle, const char * keyring_path)
{
	int result = 0;
	int valid = 0;
	size_t bytes_read = 0;
	unsigned char buffer[8192];

	if (filename == NULL)
		return -1;

	gpgme_signature_t verification_signatures;
	gpgme_verify_result_t verification_result;
	gpgme_data_t ciphertext_data;
	gpgme_data_t plaintext_data;
	gpgme_engine_info_t enginfo;
	gpgme_ctx_t gpg_context;
	gpgme_error_t err;

	/* Initialize gpgme */
	setlocale (LC_ALL, "");
	gpgme_check_version(NULL);
	gpgme_set_locale(NULL, LC_CTYPE, setlocale (LC_CTYPE, NULL));
	err = gpgme_engine_check_version(GPGME_PROTOCOL_OpenPGP);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: OpenPGP support not available\n", __func__);
		return -1;
	}
	err = gpgme_get_engine_info(&enginfo);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: GPG engine failed to initialize\n", __func__);
		return -1;
	}
	err = gpgme_new(&gpg_context);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: GPG context could not be created\n", __func__);
		return -1;
	}
	err = gpgme_set_protocol(gpg_context, GPGME_PROTOCOL_OpenPGP);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: GPG protocol could not be set\n", __func__);
		return -1;
	}
	if (keyring_path)
		err = gpgme_ctx_set_engine_info (gpg_context,
			GPGME_PROTOCOL_OpenPGP,
			enginfo->file_name, keyring_path);
	else
		err = gpgme_ctx_set_engine_info (gpg_context,
			GPGME_PROTOCOL_OpenPGP,
			enginfo->file_name, enginfo->home_dir);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: Could not set GPG engine information\n", __func__);
		return -1;
	}
	err = gpgme_data_new(&plaintext_data);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: Could not create GPG plaintext data buffer\n",
			__func__);
		return -1;
	}
	err = gpgme_data_new_from_file(&ciphertext_data, filename, 1);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: Could not create GPG ciphertext data buffer"
			" from file '%s'\n", __func__, filename);
		return -1;
	}

	/* Decrypt and verify file */
	err = gpgme_op_decrypt_verify(gpg_context, ciphertext_data,
		plaintext_data);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: Could not decrypt file\n", __func__);
		return -1;
	}
	verification_result = gpgme_op_verify_result(gpg_context);
	verification_signatures = verification_result->signatures;
	while (verification_signatures) {
		if (verification_signatures->status == GPG_ERR_NO_ERROR) {
			pb_log("%s: Good signature for key ID '%s' ('%s')\n",
				__func__,
				verification_signatures->fpr, filename);
			/* Verify fingerprint is present in authorized
			 * signatures file
			 */
			char *auth_sig_line = NULL;
			size_t auth_sig_len = 0;
			ssize_t auth_sig_read;
			rewind(authorized_signatures_handle);
			while ((auth_sig_read = getline(&auth_sig_line,
				&auth_sig_len,
				authorized_signatures_handle)) != -1) {
				auth_sig_len = strlen(auth_sig_line);
				while ((auth_sig_line[auth_sig_len-1] == '\n')
					|| (auth_sig_line[auth_sig_len-1] == '\r'))
					auth_sig_len--;
				auth_sig_line[auth_sig_len] = 0;
				if (strcmp(auth_sig_line,
					verification_signatures->fpr) == 0)
					valid = 1;
			}
			free(auth_sig_line);
		}
		else {
			pb_log("%s: Signature for key ID '%s' ('%s') invalid."
				"  Status: %08x\n", __func__,
				verification_signatures->fpr, filename,
				verification_signatures->status);
		}
		verification_signatures = verification_signatures->next;
	}

	gpgme_data_release(ciphertext_data);

	if (valid) {
		/* Write decrypted file over ciphertext */
		FILE *plaintext_file_handle = NULL;
		plaintext_file_handle = fopen(filename, "wb");
		if (!plaintext_file_handle) {
			pb_log("%s: Could not create GPG plaintext file '%s'\n",
				__func__, filename);
			return -1;
		}
		gpgme_data_seek(plaintext_data, 0, SEEK_SET);
		if (err != GPG_ERR_NO_ERROR) {
			pb_log("%s: Could not seek in GPG plaintext buffer\n",
				__func__);
			return -1;
		}
		while ((bytes_read = gpgme_data_read(plaintext_data, buffer,
			8192)) > 0) {
			size_t l2 = fwrite(buffer, 1, bytes_read,
				plaintext_file_handle);
			if (l2 < bytes_read) {
				if (ferror(plaintext_file_handle)) {
					/* General error */
					result = -1;
					pb_log("%s: failed: unknown fault\n",
						__func__);
				}
				else {
					/* No space on destination device */
					result = -1;
					pb_log("%s: failed: temporary storage"
						" full\n", __func__);
				}
			}
		}
		fclose(plaintext_file_handle);
	}

	/* Clean up */
	gpgme_data_release(plaintext_data);
	gpgme_release(gpg_context);

	if (!valid) {
		pb_log("%s: Incorrect GPG signature\n", __func__);
		return -1;
	}
	else {
		pb_log("%s: GPG signature for decrypted file '%s' verified\n",
			__func__, filename);
	}

	return result;
}

static int verify_file_signature(const char * plaintext_filename,
	const char * signature_filename, FILE * authorized_signatures_handle,
	const char * keyring_path)
{
	int valid = 0;

	if (signature_filename == NULL)
		return -1;

	gpgme_signature_t verification_signatures;
	gpgme_verify_result_t verification_result;
	gpgme_data_t plaintext_data;
	gpgme_data_t signature_data;
	gpgme_engine_info_t enginfo;
	gpgme_ctx_t gpg_context;
	gpgme_error_t err;

	/* Initialize gpgme */
	setlocale (LC_ALL, "");
	gpgme_check_version(NULL);
	gpgme_set_locale(NULL, LC_CTYPE, setlocale (LC_CTYPE, NULL));
	err = gpgme_engine_check_version(GPGME_PROTOCOL_OpenPGP);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: OpenPGP support not available\n", __func__);
		return -1;
	}
	err = gpgme_get_engine_info(&enginfo);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: GPG engine failed to initialize\n", __func__);
		return -1;
	}
	err = gpgme_new(&gpg_context);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: GPG context could not be created\n", __func__);
		return -1;
	}
	err = gpgme_set_protocol(gpg_context, GPGME_PROTOCOL_OpenPGP);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: GPG protocol could not be set\n", __func__);
		return -1;
	}
	if (keyring_path)
		err = gpgme_ctx_set_engine_info (gpg_context,
			GPGME_PROTOCOL_OpenPGP, enginfo->file_name,
			keyring_path);
	else
		err = gpgme_ctx_set_engine_info (gpg_context,
			GPGME_PROTOCOL_OpenPGP, enginfo->file_name,
			enginfo->home_dir);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: Could not set GPG engine information\n", __func__);
		return -1;
	}
	err = gpgme_data_new_from_file(&plaintext_data, plaintext_filename, 1);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: Could not create GPG plaintext data buffer"
			" from file '%s'\n", __func__, plaintext_filename);
		return -1;
	}
	err = gpgme_data_new_from_file(&signature_data, signature_filename, 1);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: Could not create GPG signature data buffer"
			" from file '%s'\n", __func__, signature_filename);
		return -1;
	}

	/* Check signature */
	err = gpgme_op_verify(gpg_context, signature_data, plaintext_data,
		NULL);
	if (err != GPG_ERR_NO_ERROR) {
		pb_log("%s: Could not verify file using GPG signature '%s'\n",
			__func__, signature_filename);
		return -1;
	}
	verification_result = gpgme_op_verify_result(gpg_context);
	verification_signatures = verification_result->signatures;
	while (verification_signatures) {
		if (verification_signatures->status == GPG_ERR_NO_ERROR) {
			pb_log("%s: Good signature for key ID '%s' ('%s')\n",
				__func__, verification_signatures->fpr,
				signature_filename);
			/* Verify fingerprint is present in
			 * authorized signatures file
			 */
			char *auth_sig_line = NULL;
			size_t auth_sig_len = 0;
			ssize_t auth_sig_read;
			rewind(authorized_signatures_handle);
			while ((auth_sig_read = getline(&auth_sig_line,
				&auth_sig_len,
				authorized_signatures_handle)) != -1) {
				auth_sig_len = strlen(auth_sig_line);
				while ((auth_sig_line[auth_sig_len-1] == '\n')
					|| (auth_sig_line[auth_sig_len-1] == '\r'))
					auth_sig_len--;
				auth_sig_line[auth_sig_len] = '\0';
				if (strcmp(auth_sig_line,
					verification_signatures->fpr) == 0)
					valid = 1;
			}
			free(auth_sig_line);
		}
		else {
			pb_log("%s: Signature for key ID '%s' ('%s') invalid."
				"  Status: %08x\n", __func__,
				verification_signatures->fpr,
				signature_filename,
				verification_signatures->status);
		}
		verification_signatures = verification_signatures->next;
	}

	/* Clean up */
	gpgme_data_release(plaintext_data);
	gpgme_data_release(signature_data);
	gpgme_release(gpg_context);

	if (!valid) {
		pb_log("%s: Incorrect GPG signature\n", __func__);
		return -1;
	}
	else {
		pb_log("%s: GPG signature '%s' for file '%s' verified\n",
			__func__, signature_filename, plaintext_filename);
	}

	return 0;
}
#endif

/**
 * kexec_load - kexec load helper.
 */
static int kexec_load(struct boot_task *boot_task)
{
	int result;
	const char *argv[7];
	const char **p;
	char *s_initrd = NULL;
	char *s_dtb = NULL;
	char *s_args = NULL;

	const char* local_initrd = boot_task->local_initrd;
	const char* local_dtb = boot_task->local_dtb;
	const char* local_image = boot_task->local_image;

#if defined(HAVE_LIBGPGME)
	const char* local_initrd_signature = (boot_task->verify_signature) ?
		boot_task->local_initrd_signature : NULL;
	const char* local_dtb_signature = (boot_task->verify_signature) ?
		boot_task->local_dtb_signature : NULL;
	const char* local_image_signature = (boot_task->verify_signature) ?
		boot_task->local_image_signature : NULL;
	const char* local_cmdline_signature =
		(boot_task->verify_signature || boot_task->decrypt_files) ?
		boot_task->local_cmdline_signature : NULL;

	if ((boot_task->verify_signature) || (boot_task->decrypt_files)) {
		char kernel_filename[MAX_FILENAME_SIZE];
		char initrd_filename[MAX_FILENAME_SIZE];
		char dtb_filename[MAX_FILENAME_SIZE];

		kernel_filename[0] = '\0';
		initrd_filename[0] = '\0';
		dtb_filename[0] = '\0';

		FILE *authorized_signatures_handle = NULL;

		/* Load authorized signatures file */
		authorized_signatures_handle = fopen(LOCKDOWN_FILE, "r");
		if (!authorized_signatures_handle) {
			pb_log("%s: unable to read lockdown file\n", __func__);
			result = KEXEC_LOAD_SIG_SETUP_INVALID;
			return result;
		}

		/* Copy files to temporary directory for verification / boot */
		result = copy_file_to_destination(boot_task->local_image,
			kernel_filename, MAX_FILENAME_SIZE);
		if (result) {
			pb_log("%s: image copy failed: (%d)\n",
				__func__, result);
			return result;
		}
		if (boot_task->local_initrd) {
			result = copy_file_to_destination(
				boot_task->local_initrd,
				initrd_filename, MAX_FILENAME_SIZE);
			if (result) {
				pb_log("%s: initrd copy failed: (%d)\n",
					__func__, result);
				unlink(local_image);
				return result;
			}
		}
		if (boot_task->local_dtb) {
			result = copy_file_to_destination(boot_task->local_dtb,
				dtb_filename, MAX_FILENAME_SIZE);
			if (result) {
				pb_log("%s: dtb copy failed: (%d)\n",
					__func__, result);
				unlink(local_image);
				if (local_initrd)
					unlink(local_initrd);
				return result;
			}
		}
		local_image = talloc_strdup(boot_task,
			kernel_filename);
		if (boot_task->local_initrd)
			local_initrd = talloc_strdup(boot_task,
				initrd_filename);
		if (boot_task->local_dtb)
			local_dtb = talloc_strdup(boot_task,
				dtb_filename);

		/* Write command line to temporary file for verification */
		char cmdline_template[21] = "/tmp/petitbootXXXXXX";
		int cmdline_fd = mkstemp(cmdline_template);
		FILE *cmdline_handle = NULL;
		if (cmdline_fd < 0) {
			// handle mkstemp error
			pb_log("%s: failed: unable to create command line"
				" temporary file for verification\n",
				__func__);
			result = -1;
		}
		else {
			cmdline_handle = fdopen(cmdline_fd, "w");
		}
		if (!cmdline_handle) {
			// handle open error
			pb_log("%s: failed: unable to write command line"
				" temporary file for verification\n",
				__func__);
			result = -1;
		}
		else {
			fwrite(boot_task->args, sizeof(char),
				strlen(boot_task->args), cmdline_handle);
			fflush(cmdline_handle);
		}

		if (boot_task->verify_signature) {
			/* Check signatures */
			if (verify_file_signature(kernel_filename,
				local_image_signature,
				authorized_signatures_handle,
				"/etc/gpg"))
				result = KEXEC_LOAD_SIGNATURE_FAILURE;
			if (verify_file_signature(cmdline_template,
				local_cmdline_signature,
				authorized_signatures_handle,
				"/etc/gpg"))
				result = KEXEC_LOAD_SIGNATURE_FAILURE;
			if (boot_task->local_initrd_signature)
				if (verify_file_signature(initrd_filename,
					local_initrd_signature,
					authorized_signatures_handle,
					"/etc/gpg"))
					result = KEXEC_LOAD_SIGNATURE_FAILURE;
			if (boot_task->local_dtb_signature)
				if (verify_file_signature(dtb_filename,
					local_dtb_signature,
					authorized_signatures_handle,
					"/etc/gpg"))
					result = KEXEC_LOAD_SIGNATURE_FAILURE;

			/* Clean up */
			if (cmdline_handle) {
				fclose(cmdline_handle);
				unlink(cmdline_template);
			}
			fclose(authorized_signatures_handle);

			if (result == KEXEC_LOAD_SIGNATURE_FAILURE) {
				pb_log("%s: Aborting kexec due to signature"
					" verification failure\n", __func__);
				goto abort_kexec;
			}
		}
		else if (boot_task->decrypt_files) {
			/* Decrypt files */
			if (decrypt_file(kernel_filename,
				authorized_signatures_handle,
				"/etc/gpg"))
				result = KEXEC_LOAD_DECRYPTION_FALURE;
			if (verify_file_signature(cmdline_template,
				local_cmdline_signature,
				authorized_signatures_handle,
				"/etc/gpg"))
				result = KEXEC_LOAD_SIGNATURE_FAILURE;
			if (boot_task->local_initrd)
				if (decrypt_file(initrd_filename,
					authorized_signatures_handle,
					"/etc/gpg"))
					result = KEXEC_LOAD_DECRYPTION_FALURE;
			if (boot_task->local_dtb)
				if (decrypt_file(dtb_filename,
					authorized_signatures_handle,
					"/etc/gpg"))
					result = KEXEC_LOAD_DECRYPTION_FALURE;

			/* Clean up */
			if (cmdline_handle) {
				fclose(cmdline_handle);
				unlink(cmdline_template);
			}
			fclose(authorized_signatures_handle);

			if (result == KEXEC_LOAD_DECRYPTION_FALURE) {
				pb_log("%s: Aborting kexec due to"
					" decryption failure\n", __func__);
				goto abort_kexec;
			}
			if (result == KEXEC_LOAD_SIGNATURE_FAILURE) {
				pb_log("%s: Aborting kexec due to signature"
					" verification failure\n", __func__);
				goto abort_kexec;
			}
		}
	}
#endif

	p = argv;
	*p++ = pb_system_apps.kexec;	/* 1 */
	*p++ = "-l";			/* 2 */

	if (local_initrd) {
		s_initrd = talloc_asprintf(boot_task, "--initrd=%s",
				local_initrd);
		assert(s_initrd);
		*p++ = s_initrd;	 /* 3 */
	}

	if (local_dtb) {
		s_dtb = talloc_asprintf(boot_task, "--dtb=%s",
						local_dtb);
		assert(s_dtb);
		*p++ = s_dtb;		 /* 4 */
	}

	if (boot_task->args) {
		s_args = talloc_asprintf(boot_task, "--append=%s",
						boot_task->args);
		assert(s_args);
		*p++ = s_args;		/* 5 */
	}

	*p++ = local_image;	/* 6 */
	*p++ = NULL;			/* 7 */

	result = process_run_simple_argv(boot_task, argv);

	if (result)
		pb_log("%s: failed: (%d)\n", __func__, result);

#if defined(HAVE_LIBGPGME)
abort_kexec:
	if ((boot_task->verify_signature) || (boot_task->decrypt_files)) {
		unlink(local_image);
		if (local_initrd)
			unlink(local_initrd);
		if (local_dtb)
			unlink(local_dtb);

		talloc_free((char*)local_image);
		if (local_initrd)
			talloc_free((char*)local_initrd);
		if (local_dtb)
			talloc_free((char*)local_dtb);
	}
#endif

	return result;
}

/**
 * kexec_reboot - Helper to boot the new kernel.
 *
 * Must only be called after a successful call to kexec_load().
 */

static int kexec_reboot(struct boot_task *task)
{
	int result;

	/* First try running shutdown.  Init scripts should run 'exec -e' */
	result = process_run_simple(task, pb_system_apps.shutdown, "-r",
			"now", NULL);

	/* On error, force a kexec with the -e option */
	if (result) {
		result = process_run_simple(task, pb_system_apps.kexec,
						"-e", NULL);
	}

	if (result)
		pb_log("%s: failed: (%d)\n", __func__, result);

	/* okay, kexec -e -f */
	if (result) {
		result = process_run_simple(task, pb_system_apps.kexec,
						"-e", "-f", NULL);
	}

	if (result)
		pb_log("%s: failed: (%d)\n", __func__, result);


	return result;
}

static void __attribute__((format(__printf__, 4, 5))) update_status(
		boot_status_fn fn, void *arg, int type, char *fmt, ...)
{
	struct boot_status status;
	va_list ap;

	va_start(ap, fmt);
	status.message = talloc_vasprintf(NULL, fmt, ap);
	va_end(ap);

	status.type = type;
	status.progress = -1;
	status.detail = NULL;

	pb_debug("boot status: [%d] %s\n", type, status.message);

	fn(arg, &status);

	talloc_free(status.message);
}

static void boot_hook_update_param(void *ctx, struct boot_task *task,
		const char *name, const char *value)
{
	struct p {
		const char *name;
		const char **p;
	} *param, params[] = {
		{ "boot_image",		&task->local_image },
		{ "boot_initrd",	&task->local_initrd },
		{ "boot_dtb",		&task->local_dtb },
		{ "boot_args",		&task->args },
		{ NULL, NULL },
	};

	for (param = params; param->name; param++) {
		if (strcmp(param->name, name))
			continue;

		*param->p = talloc_strdup(ctx, value);
		return;
	}
}

static void boot_hook_update(struct boot_task *task, const char *hookname,
		char *buf)
{
	char *line, *name, *val, *sep;
	char *saveptr;

	for (;; buf = NULL) {

		line = strtok_r(buf, "\n", &saveptr);
		if (!line)
			break;

		sep = strchr(line, '=');
		if (!sep)
			continue;

		*sep = '\0';
		name = line;
		val = sep + 1;

		boot_hook_update_param(task, task, name, val);

		pb_log("boot hook %s specified %s=%s\n",
				hookname, name, val);
	}
}

static void boot_hook_setenv(struct boot_task *task)
{
	unsetenv("boot_image");
	unsetenv("boot_initrd");
	unsetenv("boot_dtb");
	unsetenv("boot_args");

	setenv("boot_image", task->local_image, 1);
	if (task->local_initrd)
		setenv("boot_initrd", task->local_initrd, 1);
	if (task->local_dtb)
		setenv("boot_dtb", task->local_dtb, 1);
	if (task->args)
		setenv("boot_args", task->args, 1);
}

static int hook_filter(const struct dirent *dirent)
{
	return dirent->d_type == DT_REG || dirent->d_type == DT_LNK;
}

static int hook_cmp(const struct dirent **a, const struct dirent **b)
{
	return strcmp((*a)->d_name, (*b)->d_name);
}

static void run_boot_hooks(struct boot_task *task)
{
	struct dirent **hooks;
	int i, n;

	n = scandir(boot_hook_dir, &hooks, hook_filter, hook_cmp);
	if (n < 1)
		return;

	update_status(task->status_fn, task->status_arg, BOOT_STATUS_INFO,
			_("running boot hooks"));

	boot_hook_setenv(task);

	for (i = 0; i < n; i++) {
		const char *argv[2] = { NULL, NULL };
		struct process *process;
		char *path;
		int rc;

		path = join_paths(task, boot_hook_dir, hooks[i]->d_name);

		if (access(path, X_OK)) {
			talloc_free(path);
			continue;
		}

		process = process_create(task);

		argv[0] = path;
		process->path = path;
		process->argv = argv;
		process->keep_stdout = true;

		pb_log("running boot hook %s\n", hooks[i]->d_name);

		rc = process_run_sync(process);
		if (rc) {
			pb_log("boot hook exec failed!\n");

		} else if (WIFEXITED(process->exit_status) &&
			   WEXITSTATUS(process->exit_status)
				== BOOT_HOOK_EXIT_UPDATE) {
			/* if the hook returned with BOOT_HOOK_EXIT_UPDATE,
			 * then we process stdout to look for updated params
			 */
			boot_hook_update(task, hooks[i]->d_name,
					process->stdout_buf);
			boot_hook_setenv(task);
		}

		process_release(process);
		talloc_free(path);
	}

	free(hooks);
}

static bool load_pending(struct load_url_result *result)
{
	return result && result->status == LOAD_ASYNC;
}

static int check_load(struct boot_task *task, const char *name,
		struct load_url_result *result)
{
	if (!result)
		return 0;
	if (result->status != LOAD_ERROR)
		return 0;

	update_status(task->status_fn, task->status_arg,
			BOOT_STATUS_ERROR,
			_("Couldn't load %s"), name);
	return -1;
}

static void cleanup_load(struct load_url_result *result)
{
	if (!result)
		return;
	if (result->status != LOAD_OK)
		return;
	if (!result->cleanup_local)
		return;
	unlink(result->local);
}

static void cleanup_cancellations(struct boot_task *task,
		struct load_url_result *cur_result)
{
	struct load_url_result *result, **results[] = {
		&task->image, &task->initrd, &task->dtb,
	};
	bool pending = false;
	unsigned int i;

	for (i = 0; i < ARRAY_SIZE(results); i++) {
		result = *results[i];

		if (!result)
			continue;

		/* We need to cleanup and free any completed loads */
		if (result == cur_result || result->status == LOAD_OK
				|| result->status == LOAD_ERROR) {
			cleanup_load(result);
			talloc_free(result);
			*results[i] = NULL;

		/* ... and cancel any pending loads, which we'll free in
		 * the completion callback */
		} else if (result->status == LOAD_ASYNC) {
			load_url_async_cancel(result);
			pending = true;

		/* if we're waiting for a cancellation, we still need to
		 * wait for the completion before freeing the boot task */
		} else if (result->status == LOAD_CANCELLED) {
			pending = true;
		}
	}

	if (!pending)
		talloc_free(task);
}

static void boot_process(struct load_url_result *result, void *data)
{
	struct boot_task *task = data;
	int rc = -1;

	if (task->cancelled) {
		cleanup_cancellations(task, result);
		return;
	}

	if (load_pending(task->image) ||
			load_pending(task->initrd) ||
			load_pending(task->dtb))
		return;

	if (check_load(task, "kernel image", task->image) ||
			check_load(task, "initrd", task->initrd) ||
			check_load(task, "dtb", task->dtb))
		goto no_load;

#if defined(HAVE_LIBGPGME)
	if (task->verify_signature) {
		if (load_pending(task->image_signature) ||
				load_pending(task->initrd_signature) ||
				load_pending(task->dtb_signature) ||
				load_pending(task->cmdline_signature))
			return;
	}
	if (task->decrypt_files) {
		if (load_pending(task->cmdline_signature))
			return;
	}

	if (task->verify_signature) {
		if (check_load(task, "kernel image signature",
					task->image_signature) ||
				check_load(task, "initrd signature",
					task->initrd_signature) ||
				check_load(task, "dtb signature",
					task->dtb_signature) ||
				check_load(task, "command line signature",
					task->cmdline_signature))
			goto no_sig_load;
	}
	if (task->decrypt_files) {
		if (load_pending(task->cmdline_signature))
			return;

		if (check_load(task, "command line signature",
					task->cmdline_signature))
			goto no_decrypt_sig_load;
	}
#endif

	/* we make a copy of the local paths, as the boot hooks might update
	 * and/or create these */
	task->local_image = task->image ? task->image->local : NULL;
	task->local_initrd = task->initrd ? task->initrd->local : NULL;
	task->local_dtb = task->dtb ? task->dtb->local : NULL;

#if defined(HAVE_LIBGPGME)
	if (task->verify_signature) {
		task->local_image_signature = task->image_signature ?
			task->image_signature->local : NULL;
		task->local_initrd_signature = task->initrd_signature ?
			task->initrd_signature->local : NULL;
		task->local_dtb_signature = task->dtb_signature ?
			task->dtb_signature->local : NULL;
	}
	if (task->verify_signature || task->decrypt_files) {
		task->local_cmdline_signature = task->cmdline_signature ?
			task->cmdline_signature->local : NULL;
	}
#endif

	run_boot_hooks(task);

	update_status(task->status_fn, task->status_arg, BOOT_STATUS_INFO,
			_("performing kexec_load"));

	rc = kexec_load(task);
	if (rc == KEXEC_LOAD_DECRYPTION_FALURE) {
		update_status(task->status_fn, task->status_arg,
				BOOT_STATUS_ERROR, _("decryption failed"));
	}
	else if (rc == KEXEC_LOAD_SIGNATURE_FAILURE) {
		update_status(task->status_fn, task->status_arg,
				BOOT_STATUS_ERROR,
				_("signature verification failed"));
	}
	else if (rc == KEXEC_LOAD_SIG_SETUP_INVALID) {
		update_status(task->status_fn, task->status_arg,
				BOOT_STATUS_ERROR,
				_("invalid signature configuration"));
	}
	else if (rc) {
		update_status(task->status_fn, task->status_arg,
				BOOT_STATUS_ERROR,
				_("kexec load failed"));
	}

no_sig_load:
	cleanup_load(task->image_signature);
	cleanup_load(task->initrd_signature);
	cleanup_load(task->dtb_signature);

no_decrypt_sig_load:
	cleanup_load(task->cmdline_signature);

no_load:
	cleanup_load(task->image);
	cleanup_load(task->initrd);
	cleanup_load(task->dtb);

	if (!rc) {
		update_status(task->status_fn, task->status_arg,
				BOOT_STATUS_INFO,
				_("performing kexec reboot"));

		rc = kexec_reboot(task);
		if (rc) {
			update_status(task->status_fn, task->status_arg,
					BOOT_STATUS_ERROR,
					_("kexec reboot failed"));
		}
	}
}

static int start_url_load(struct boot_task *task, const char *name,
		struct pb_url *url, struct load_url_result **result)
{
	if (!url)
		return 0;

	*result = load_url_async(task, url, boot_process, task);
	if (!*result) {
		update_status(task->status_fn, task->status_arg,
				BOOT_STATUS_ERROR,
				_("Error loading %s"), name);
		return -1;
	}
	return 0;
}

struct boot_task *boot(void *ctx, struct discover_boot_option *opt,
		struct boot_command *cmd, int dry_run,
		boot_status_fn status_fn, void *status_arg)
{
	struct pb_url *image = NULL, *initrd = NULL, *dtb = NULL;
	struct pb_url *image_sig = NULL, *initrd_sig = NULL, *dtb_sig = NULL,
		*cmdline_sig = NULL;
	struct boot_task *boot_task;
	const char *boot_desc;
	int rc;

	if (opt && opt->option->name)
		boot_desc = opt->option->name;
	else if (cmd && cmd->boot_image_file)
		boot_desc = cmd->boot_image_file;
	else
		boot_desc = _("(unknown)");

	update_status(status_fn, status_arg, BOOT_STATUS_INFO,
			_("Booting %s."), boot_desc);

	if (cmd && cmd->boot_image_file) {
		image = pb_url_parse(opt, cmd->boot_image_file);
	} else if (opt && opt->boot_image) {
		image = opt->boot_image->url;
	} else {
		pb_log("%s: no image specified\n", __func__);
		update_status(status_fn, status_arg, BOOT_STATUS_INFO,
				_("Boot failed: no image specified"));
		return NULL;
	}

	if (cmd && cmd->initrd_file) {
		initrd = pb_url_parse(opt, cmd->initrd_file);
	} else if (opt && opt->initrd) {
		initrd = opt->initrd->url;
	}

	if (cmd && cmd->dtb_file) {
		dtb = pb_url_parse(opt, cmd->dtb_file);
	} else if (opt && opt->dtb) {
		dtb = opt->dtb->url;
	}

	boot_task = talloc_zero(ctx, struct boot_task);
	boot_task->dry_run = dry_run;
	boot_task->status_fn = status_fn;
	boot_task->status_arg = status_arg;
#if defined(HAVE_LIBGPGME)
	if (access(LOCKDOWN_FILE, F_OK) == -1) {
		boot_task->verify_signature = false;
		boot_task->decrypt_files = false;
	}
	else {
		/* determine lockdown type */
		FILE *authorized_signatures_handle = NULL;
		authorized_signatures_handle = fopen(LOCKDOWN_FILE, "r");
		if (authorized_signatures_handle) {
			char *auth_sig_line = NULL;
			size_t auth_sig_len = 0;
			ssize_t auth_sig_read;
			rewind(authorized_signatures_handle);
			if ((auth_sig_read = getline(&auth_sig_line,
				&auth_sig_len,
				authorized_signatures_handle)) != -1) {
				auth_sig_len = strlen(auth_sig_line);
				while ((auth_sig_line[auth_sig_len-1] == '\n')
					|| (auth_sig_line[auth_sig_len-1] == '\r'))
					auth_sig_len--;
				auth_sig_line[auth_sig_len] = 0;
				if (strcmp(auth_sig_line, "ENCRYPTED") == 0) {
					/* first line indicates encrypted files
					 * expected.  enable decryption.
					 */
					boot_task->verify_signature = false;
					boot_task->decrypt_files = true;
				}
			}
			else {
				/* file present but empty.  assume most
				 * restrictive lockdown type
				 */
				boot_task->verify_signature = true;
				boot_task->decrypt_files = false;
			}
			free(auth_sig_line);
		}
		else {
			/* assume most restrictive lockdown type */
			boot_task->verify_signature = true;
			boot_task->decrypt_files = false;
		}
	}
#else
	boot_task->verify_signature = false;
	boot_task->decrypt_files = false;
#endif

	if (cmd && cmd->boot_args) {
		boot_task->args = talloc_strdup(boot_task, cmd->boot_args);
	} else if (opt && opt->option->boot_args) {
		boot_task->args = talloc_strdup(boot_task,
						opt->option->boot_args);
	} else {
		boot_task->args = NULL;
	}

	if (boot_task->verify_signature || boot_task->decrypt_files) {
		if (cmd && cmd->args_sig_file) {
			cmdline_sig = pb_url_parse(opt, cmd->args_sig_file);
		} else if (opt && opt->args_sig_file) {
			cmdline_sig = opt->args_sig_file->url;
		} else {
			pb_log("%s: no command line signature file"
				" specified\n", __func__);
			update_status(status_fn, status_arg, BOOT_STATUS_INFO,
					_("Boot failed: no command line"
						" signature file specified"));
			return NULL;
		}
	}

	/* start async loads for boot resources */
	rc = start_url_load(boot_task, "kernel image", image, &boot_task->image)
	  || start_url_load(boot_task, "initrd", initrd, &boot_task->initrd)
	  || start_url_load(boot_task, "dtb", dtb, &boot_task->dtb);

	if (boot_task->verify_signature) {
		/* Generate names of associated signature files and load */
		if (image) {
			image_sig = pb_url_copy(ctx, image);
			talloc_free(image_sig->file);
			image_sig->file = talloc_asprintf(image_sig,
				"%s.sig", image->file);
			talloc_free(image_sig->path);
			image_sig->path = talloc_asprintf(image_sig,
				"%s.sig", image->path);
			rc |= start_url_load(boot_task,
				"kernel image signature", image_sig,
				&boot_task->image_signature);
		}
		if (initrd) {
			initrd_sig = pb_url_copy(ctx, initrd);
			talloc_free(initrd_sig->file);
			initrd_sig->file = talloc_asprintf(initrd_sig,
				"%s.sig", initrd->file);
			talloc_free(initrd_sig->path);
			initrd_sig->path = talloc_asprintf(initrd_sig,
				"%s.sig", initrd->path);
			rc |= start_url_load(boot_task, "initrd signature",
				initrd_sig, &boot_task->initrd_signature);
		}
		if (dtb) {
			dtb_sig = pb_url_copy(ctx, dtb);
			talloc_free(dtb_sig->file);
			dtb_sig->file = talloc_asprintf(dtb_sig,
				"%s.sig", dtb->file);
			talloc_free(dtb_sig->path);
			dtb_sig->path = talloc_asprintf(dtb_sig,
				"%s.sig", dtb->path);
			rc |= start_url_load(boot_task, "dtb signature",
				dtb_sig, &boot_task->dtb_signature);
		}
	}

	if (boot_task->verify_signature || boot_task->decrypt_files) {
		rc |= start_url_load(boot_task,
			"kernel command line signature", cmdline_sig,
			&boot_task->cmdline_signature);
	}

	/* If all URLs are local, we may be done. */
	if (rc) {
		talloc_free(boot_task);
		return NULL;
	}

	boot_process(NULL, boot_task);

	return boot_task;
}

void boot_cancel(struct boot_task *task)
{
	task->cancelled = true;

	update_status(task->status_fn, task->status_arg, BOOT_STATUS_INFO,
			_("Boot cancelled"));

	cleanup_cancellations(task, NULL);
}
