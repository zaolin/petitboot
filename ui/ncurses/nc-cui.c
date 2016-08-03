/*
 *  Copyright (C) 2009 Sony Computer Entertainment Inc.
 *  Copyright 2009 Sony Corp.
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; version 2 of the License.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#if defined(HAVE_CONFIG_H)
#include "config.h"
#endif

#include <assert.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/reboot.h>

#include "log/log.h"
#include "pb-protocol/pb-protocol.h"
#include "talloc/talloc.h"
#include "waiter/waiter.h"
#include "process/process.h"
#include "i18n/i18n.h"
#include "ui/common/discover-client.h"
#include "ui/common/ui-system.h"
#include "nc-cui.h"
#include "nc-boot-editor.h"
#include "nc-config.h"
#include "nc-add-url.h"
#include "nc-sysinfo.h"
#include "nc-lang.h"
#include "nc-helpscreen.h"

extern const struct help_text main_menu_help_text;

static struct pmenu *main_menu_init(struct cui *cui);

static void cui_start(void)
{
	initscr();			/* Initialize ncurses. */
	cbreak();			/* Disable line buffering. */
	noecho();			/* Disable getch() echo. */
	keypad(stdscr, TRUE);		/* Enable num keypad keys. */
	nonl();				/* Disable new-line translation. */
	intrflush(stdscr, FALSE);	/* Disable interrupt flush. */
	curs_set(0);			/* Make cursor invisible */
	nodelay(stdscr, TRUE);		/* Enable non-blocking getch() */

	/* We may be operating with an incorrect $TERM type; in this case
	 * the keymappings will be slightly broken. We want at least
	 * backspace to work though, so we'll define both DEL and ^H to
	 * map to backspace */
	define_key("\x7f", KEY_BACKSPACE);
	define_key("\x08", KEY_BACKSPACE);

	/* we need backtab too, for form navigation. vt220 doesn't include
	 * this (kcbt), but we don't want to require a full linux/xterm termcap
	 */
	define_key("\x1b[Z", KEY_BTAB);

	while (getch() != ERR)		/* flush stdin */
		(void)0;
}

static void cui_atexit(void)
{
	clear();
	refresh();
	endwin();

	bool lockdown = false;
	if (access(LOCKDOWN_FILE, F_OK) != -1)
		lockdown = true;

	while (lockdown) {
		sync();
		reboot(RB_AUTOBOOT);
	}
}

/**
 * cui_abort - Signal the main cui program loop to exit.
 *
 * Sets cui.abort, which causes the cui_run() routine to return.
 */

void cui_abort(struct cui *cui)
{
	pb_log("%s: exiting\n", __func__);
	cui->abort = 1;
}

/**
 * cui_resize - Signal the main cui program loop to resize
 *
 * Called at SIGWINCH.
 */

void cui_resize(struct cui *cui)
{
	pb_debug("%s: resizing\n", __func__);
	cui->resize = 1;
}

/**
 * cui_on_exit - A generic main menu exit callback.
 */

void cui_on_exit(struct pmenu *menu)
{
	cui_abort(cui_from_pmenu(menu));
}

/**
 * cui_run_cmd - A generic cb to run the supplied command.
 */

int cui_run_cmd(struct pmenu_item *item)
{
	int result;
	struct cui *cui = cui_from_item(item);
	const char **cmd_argv = item->data;

	nc_scr_status_printf(cui->current, _("Running %s..."), cmd_argv[0]);

	def_prog_mode();

	result = process_run_simple_argv(item, cmd_argv);

	reset_prog_mode();
	redrawwin(cui->current->main_ncw);

	if (result) {
		pb_log("%s: failed: '%s'\n", __func__, cmd_argv[0]);
		nc_scr_status_printf(cui->current, _("Failed: %s"),
				cmd_argv[0]);
	}

	return result;
}

/**
 * cui_boot - A generic cb to run kexec.
 */

static int cui_boot(struct pmenu_item *item)
{
	int result;
	struct cui *cui = cui_from_item(item);
	struct cui_opt_data *cod = cod_from_item(item);

	assert(cui->current == &cui->main->scr);

	pb_debug("%s: %s\n", __func__, cod->name);

	nc_scr_status_printf(cui->current, _("Booting %s..."), cod->name);

	result = discover_client_boot(cui->client, NULL, cod->opt, cod->bd);

	if (result) {
		nc_scr_status_printf(cui->current,
				_("Failed: boot %s"), cod->bd->image);
	}

	return 0;
}

static void cui_boot_editor_on_exit(struct cui *cui,
		struct pmenu_item *item,
		struct pb_boot_data *bd)
{
	struct pmenu *menu = cui->main;
	struct cui_opt_data *cod;
	static int user_idx = 0;

	/* Was the edit cancelled? */
	if (!bd) {
		cui_set_current(cui, &cui->main->scr);
		talloc_free(cui->boot_editor);
		cui->boot_editor = NULL;
		return;
	}

	/* Is this was a new item, we'll need to update the menu */
	if (!item) {
		int insert_pt;

		cod = talloc_zero(NULL, struct cui_opt_data);
		cod->name = talloc_asprintf(cod, _("User item %u"), ++user_idx);

		item = pmenu_item_create(menu, cod->name);
		if (!item) {
			talloc_free(cod);
			goto out;
		}

		item->on_edit = cui_item_edit;
		item->on_execute = cui_boot;
		item->data = cod;

		talloc_steal(item, cod);

		/* Detach the items array. */
		set_menu_items(menu->ncm, NULL);

		/* Insert new item at insert_pt. */
		insert_pt = pmenu_grow(menu, 1);
		pmenu_item_insert(menu, item, insert_pt);

		/* Re-attach the items array. */
		set_menu_items(menu->ncm, menu->items);
		nc_scr_post(&menu->scr);
	} else {
		cod = item->data;
	}

	cod->bd = talloc_steal(cod, bd);

	set_current_item(item->pmenu->ncm, item->nci);
out:
	cui_set_current(cui, &cui->main->scr);
	talloc_free(cui->boot_editor);
	cui->boot_editor = NULL;
}

void cui_item_edit(struct pmenu_item *item)
{
	struct cui *cui = cui_from_item(item);
	cui->boot_editor = boot_editor_init(cui, item, cui->sysinfo,
					cui_boot_editor_on_exit);
	cui_set_current(cui, boot_editor_scr(cui->boot_editor));
}

void cui_item_new(struct pmenu *menu)
{
	struct cui *cui = cui_from_pmenu(menu);
	cui->boot_editor = boot_editor_init(cui, NULL, cui->sysinfo,
					cui_boot_editor_on_exit);
	cui_set_current(cui, boot_editor_scr(cui->boot_editor));
}

static void cui_sysinfo_exit(struct cui *cui)
{
	cui_set_current(cui, &cui->main->scr);
	talloc_free(cui->sysinfo_screen);
	cui->sysinfo_screen = NULL;
}

void cui_show_sysinfo(struct cui *cui)
{
	cui->sysinfo_screen = sysinfo_screen_init(cui, cui->sysinfo,
			cui_sysinfo_exit);
	cui_set_current(cui, sysinfo_screen_scr(cui->sysinfo_screen));
}

static void cui_config_exit(struct cui *cui)
{
	cui_set_current(cui, &cui->main->scr);
	talloc_free(cui->config_screen);
	cui->config_screen = NULL;
}

void cui_show_config(struct cui *cui)
{
	cui->config_screen = config_screen_init(cui, cui->config,
			cui->sysinfo, cui_config_exit);
	cui_set_current(cui, config_screen_scr(cui->config_screen));
}

static void cui_lang_exit(struct cui *cui)
{
	cui_set_current(cui, &cui->main->scr);
	talloc_free(cui->lang_screen);
	cui->lang_screen = NULL;
}

void cui_show_lang(struct cui *cui)
{
	cui->lang_screen = lang_screen_init(cui, cui->config, cui_lang_exit);
	cui_set_current(cui, lang_screen_scr(cui->lang_screen));
}

static void cui_add_url_exit(struct cui *cui)
{
	cui_set_current(cui, &cui->main->scr);
	talloc_free(cui->add_url_screen);
	cui->add_url_screen = NULL;
}

void cui_show_add_url(struct cui *cui)
{
	cui->add_url_screen = add_url_screen_init(cui, cui_add_url_exit);
	cui_set_current(cui, add_url_screen_scr(cui->add_url_screen));
}

static void cui_help_exit(struct cui *cui)
{
	cui_set_current(cui, help_screen_return_scr(cui->help_screen));
	talloc_free(cui->help_screen);
	cui->help_screen = NULL;
}

void cui_show_help(struct cui *cui, const char *title,
		const struct help_text *text)
{
	if (!cui->current)
		return;

	if (cui->help_screen)
		return;

	cui->help_screen = help_screen_init(cui, cui->current,
			title, text, cui_help_exit);

	if (cui->help_screen)
		cui_set_current(cui, help_screen_scr(cui->help_screen));
}

/**
 * cui_set_current - Set the currently active screen and redraw it.
 */

struct nc_scr *cui_set_current(struct cui *cui, struct nc_scr *scr)
{
	struct nc_scr *old;

	DBGS("%p -> %p\n", cui->current, scr);

	assert(cui->current != scr);

	old = cui->current;
	nc_scr_unpost(old);

	cui->current = scr;

	nc_scr_post(cui->current);

	return old;
}

static bool process_global_keys(struct cui *cui, int key)
{
	switch (key) {
	case 0xc:
		if (cui->current && cui->current->main_ncw)
			wrefresh(curscr);
		return true;
	}
	return false;
}

/**
 * cui_process_key - Process input on stdin.
 */

static int cui_process_key(void *arg)
{
	struct cui *cui = cui_from_arg(arg);

	assert(cui->current);

	for (;;) {
		int c = getch();

		pb_debug("%s: got key %d\n", __func__, c);

		if (c == ERR)
			break;

		if (!cui->has_input) {
			pb_log("UI input received (key = %d), aborting "
					"default boot\n", c);
			discover_client_cancel_default(cui->client);
			cui->has_input = true;
		}

		if (process_global_keys(cui, c))
			continue;

		cui->current->process_key(cui->current, c);
	}

	return 0;
}

/**
 * cui_process_js - Process joystick events.
 */

static int cui_process_js(void *arg)
{
	struct cui *cui = cui_from_arg(arg);
	int c;

	c = pjs_process_event(cui->pjs);

	if (c) {
		ungetch(c);
		cui_process_key(arg);
	}

	return 0;
}

/**
 * cui_handle_resize - Handle the term resize.
 */

static void cui_handle_resize(struct cui *cui)
{
	struct winsize ws;

	if (ioctl(1, TIOCGWINSZ, &ws) == -1) {
		pb_log("%s: ioctl failed: %s\n", __func__, strerror(errno));
		return;
	}

	pb_debug("%s: {%u,%u}\n", __func__, ws.ws_row, ws.ws_col);

	wclear(cui->current->main_ncw);
	resize_term(ws.ws_row, ws.ws_col);
	cui->current->resize(cui->current);

	/* For some reason this makes ncurses redraw the screen */
	getch();
	redrawwin(cui->current->main_ncw);
	wrefresh(cui->current->main_ncw);
}

/**
 * cui_device_add - Client device_add callback.
 *
 * Creates menu_items for all the device boot_options and inserts those
 * menu_items into the main menu.  Redraws the main menu if it is active.
 */

static int cui_boot_option_add(struct device *dev, struct boot_option *opt,
		void *arg)
{
	struct pmenu_item *i, *dev_hdr = NULL;
	struct cui *cui = cui_from_arg(arg);
	struct cui_opt_data *cod;
	const char *tab = "  ";
	unsigned int insert_pt;
	int result, rows, cols;
	ITEM *selected;
	char *name;

	pb_debug("%s: %p %s\n", __func__, opt, opt->id);

	selected = current_item(cui->main->ncm);
	menu_format(cui->main->ncm, &rows, &cols);

	if (cui->current == &cui->main->scr)
		nc_scr_unpost(cui->current);

	/* Check if the boot device is new */
	dev_hdr = pmenu_find_device(cui->main, dev, opt);

	/* All actual boot entries are 'tabbed' across */
	name = talloc_asprintf(cui->main, "%s%s",
			tab, opt->name ? : "Unknown Name");

	/* Save the item in opt->ui_info for cui_device_remove() */
	opt->ui_info = i = pmenu_item_create(cui->main, name);
	talloc_free(name);
	if (!i)
		return -1;

	i->on_edit = cui_item_edit;
	i->on_execute = cui_boot;
	i->data = cod = talloc(i, struct cui_opt_data);

	cod->opt = opt;
	cod->dev = dev;
	cod->opt_hash = pb_opt_hash(dev, opt);
	cod->name = opt->name;
	cod->bd = talloc(i, struct pb_boot_data);

	cod->bd->image = talloc_strdup(cod->bd, opt->boot_image_file);
	cod->bd->initrd = talloc_strdup(cod->bd, opt->initrd_file);
	cod->bd->dtb = talloc_strdup(cod->bd, opt->dtb_file);
	cod->bd->args = talloc_strdup(cod->bd, opt->boot_args);
	cod->bd->args_sig_file = talloc_strdup(cod->bd, opt->args_sig_file);

	/* This disconnects items array from menu. */
	result = set_menu_items(cui->main->ncm, NULL);

	if (result)
		pb_log("%s: set_menu_items failed: %d\n", __func__, result);

	/* Insert new items at insert_pt. */
	if (dev_hdr) {
		insert_pt = pmenu_grow(cui->main, 2);
		pmenu_item_insert(cui->main, dev_hdr, insert_pt);
		pb_log("%s: adding new device hierarchy %s\n",
			__func__,opt->device_id);
		pmenu_item_insert(cui->main, i, insert_pt+1);
	} else {
		insert_pt = pmenu_grow(cui->main, 1);
		pmenu_item_add(cui->main, i, insert_pt);
	}

	pb_log("%s: adding opt '%s'\n", __func__, cod->name);
	pb_log("   image  '%s'\n", cod->bd->image);
	pb_log("   initrd '%s'\n", cod->bd->initrd);
	pb_log("   args   '%s'\n", cod->bd->args);
	pb_log("   argsig '%s'\n", cod->bd->args_sig_file);

	/* Re-attach the items array. */
	result = set_menu_items(cui->main->ncm, cui->main->items);

	if (result)
		pb_log("%s: set_menu_items failed: %d\n", __func__, result);

	if (0) {
		pb_log("%s\n", __func__);
		pmenu_dump_items(cui->main->items,
			item_count(cui->main->ncm) + 1);
	}

	if (!item_visible(selected)) {
		int idx, top;

		top = top_row(cui->main->ncm);
		idx = item_index(selected);

		/* If our index is above the current top row, align
		 * us to the new top. Otherwise, align us to the new
		 * bottom */
		top = top < idx ? idx - rows : idx;

		set_top_row(cui->main->ncm, top);
		set_current_item(cui->main->ncm, selected);
	}

	if (cui->current == &cui->main->scr)
		nc_scr_post(cui->current);

	return 0;
}

/**
 * cui_device_remove - Client device remove callback.
 *
 * Removes all the menu_items for the device from the main menu and redraws the
 * main menu if it is active.
 */

static void cui_device_remove(struct device *dev, void *arg)
{
	struct cui *cui = cui_from_arg(arg);
	struct boot_option *opt;
	unsigned int i;
	int result;

	pb_log("%s: %p %s\n", __func__, dev, dev->id);

	if (cui->current == &cui->main->scr)
		nc_scr_unpost(cui->current);

	/* This disconnects items array from menu. */

	result = set_menu_items(cui->main->ncm, NULL);

	if (result)
		pb_log("%s: set_menu_items failed: %d\n", __func__, result);

	list_for_each_entry(&dev->boot_options, opt, list) {
		struct pmenu_item *item = pmenu_item_from_arg(opt->ui_info);

		assert(pb_protocol_device_cmp(dev, cod_from_item(item)->dev));
		pmenu_remove(cui->main, item);
	}

	/* Manually remove remaining device hierarchy item */
	for (i=0; i < cui->main->item_count; i++) {
		struct pmenu_item *item = item_userptr(cui->main->items[i]);
		if (!item || !item->data )
			continue;

		struct cui_opt_data *data = item->data;
		if (data && data->dev && data->dev == dev)
			pmenu_remove(cui->main,item);
	}

	/* Re-attach the items array. */

	result = set_menu_items(cui->main->ncm, cui->main->items);

	if (result)
		pb_log("%s: set_menu_items failed: %d\n", __func__, result);

	if (0) {
		pb_log("%s\n", __func__);
		pmenu_dump_items(cui->main->items,
			item_count(cui->main->ncm) + 1);
	}

	if (cui->current == &cui->main->scr)
		nc_scr_post(cui->current);
}

static void cui_update_status(struct boot_status *status, void *arg)
{
	struct cui *cui = cui_from_arg(arg);

	nc_scr_status_printf(cui->current,
			"%s: %s",
			status->type == BOOT_STATUS_ERROR ?
				_("Error") : _("Info"),
			status->message);

}

static void cui_update_mm_title(struct cui *cui)
{
	struct nc_frame *frame = &cui->main->scr.frame;

	talloc_free(frame->rtitle);

	frame->rtitle = talloc_strdup(cui->main, cui->sysinfo->type);
	if (cui->sysinfo->identifier)
		frame->rtitle = talloc_asprintf_append(frame->rtitle,
				" %s", cui->sysinfo->identifier);

	if (cui->current == &cui->main->scr)
		nc_scr_post(cui->current);
}

static void cui_update_sysinfo(struct system_info *sysinfo, void *arg)
{
	struct cui *cui = cui_from_arg(arg);
	cui->sysinfo = talloc_steal(cui, sysinfo);

	/* if we're currently displaying the system info screen, inform it
	 * of the updated information. */
	if (cui->sysinfo_screen)
		sysinfo_screen_update(cui->sysinfo_screen, sysinfo);

	/* ... and do the same with the config screen... */
	if (cui->config_screen)
		config_screen_update(cui->config_screen, cui->config, sysinfo);

	/* ... and the boot editor. */
	if (cui->boot_editor)
		boot_editor_update(cui->boot_editor, sysinfo);

	cui_update_mm_title(cui);
}

static void cui_update_language(struct cui *cui, char *lang)
{
	bool repost_menu;
	char *cur_lang;

	cur_lang = setlocale(LC_ALL, NULL);
	if (cur_lang && !strcmp(cur_lang, lang))
		return;

	setlocale(LC_ALL, lang);

	/* we'll need to update the menu: drop all items and repopulate */
	repost_menu = cui->current == &cui->main->scr;
	if (repost_menu)
		nc_scr_unpost(cui->current);

	talloc_free(cui->main);
	cui->main = main_menu_init(cui);

	if (repost_menu) {
		cui->current = &cui->main->scr;
		nc_scr_post(cui->current);
	}

	discover_client_enumerate(cui->client);
}

static void cui_update_config(struct config *config, void *arg)
{
	struct cui *cui = cui_from_arg(arg);
	cui->config = talloc_steal(cui, config);

	if (config->lang)
		cui_update_language(cui, config->lang);

	if (cui->config_screen)
		config_screen_update(cui->config_screen, config, cui->sysinfo);

	if (config->safe_mode)
		nc_scr_status_printf(cui->current,
				_("SAFE MODE: select '%s' to continue"),
				_("Rescan devices"));
}

int cui_send_config(struct cui *cui, struct config *config)
{
	return discover_client_send_config(cui->client, config);
}

int cui_send_url(struct cui *cui, char * url)
{
	return discover_client_send_url(cui->client, url);
}

void cui_send_reinit(struct cui *cui)
{
	discover_client_send_reinit(cui->client);
}

static int menu_sysinfo_execute(struct pmenu_item *item)
{
	cui_show_sysinfo(cui_from_item(item));
	return 0;
}

static int menu_config_execute(struct pmenu_item *item)
{
	cui_show_config(cui_from_item(item));
	return 0;
}

static int menu_lang_execute(struct pmenu_item *item)
{
	cui_show_lang(cui_from_item(item));
	return 0;
}

static int menu_reinit_execute(struct pmenu_item *item)
{
	cui_send_reinit(cui_from_item(item));
	return 0;
}

static int menu_add_url_execute(struct pmenu_item *item)
{
	cui_show_add_url(cui_from_item(item));
	return 0;
}

/**
 * pb_mm_init - Setup the main menu instance.
 */
static struct pmenu *main_menu_init(struct cui *cui)
{
	struct pmenu_item *i;
	struct pmenu *m;
	int result;
	bool lockdown = false;
	if (access(LOCKDOWN_FILE, F_OK) != -1)
		lockdown = true;

	m = pmenu_init(cui, 7, cui_on_exit);
	if (!m) {
		pb_log("%s: failed\n", __func__);
		return NULL;
	}

	m->on_new = cui_item_new;

	m->scr.frame.ltitle = talloc_asprintf(m,
		"Petitboot (" PACKAGE_VERSION ")");
	m->scr.frame.rtitle = NULL;
	m->scr.frame.help = talloc_strdup(m,
		_("Enter=accept, e=edit, n=new, x=exit, l=language, h=help"));
	m->scr.frame.status = talloc_strdup(m, _("Welcome to Petitboot"));

	/* add a separator */
	i = pmenu_item_create(m, " ");
	item_opts_off(i->nci, O_SELECTABLE);
	pmenu_item_insert(m, i, 0);

	/* add system items */
	i = pmenu_item_create(m, _("System information"));
	i->on_execute = menu_sysinfo_execute;
	pmenu_item_insert(m, i, 1);

	i = pmenu_item_create(m, _("System configuration"));
	i->on_execute = menu_config_execute;
	pmenu_item_insert(m, i, 2);

	/* this label isn't translated, so we don't want a gettext() here */
	i = pmenu_item_create(m, "Language");
	i->on_execute = menu_lang_execute;
	pmenu_item_insert(m, i, 3);

	i = pmenu_item_create(m, _("Rescan devices"));
	i->on_execute = menu_reinit_execute;
	pmenu_item_insert(m, i, 4);

	i = pmenu_item_create(m, _("Retrieve config from URL"));
	i->on_execute = menu_add_url_execute;
	pmenu_item_insert(m, i, 5);

	if (lockdown) {
		i = pmenu_item_create(m, _("Reboot"));
		i->on_execute = pmenu_exit_cb;
		pmenu_item_insert(m, i, 6);
	}
	else {
		i = pmenu_item_create(m, _("Exit to shell"));
		i->on_execute = pmenu_exit_cb;
		pmenu_item_insert(m, i, 6);
	}

	result = pmenu_setup(m);

	if (result) {
		pb_log("%s:%d: pmenu_setup failed: %s\n", __func__, __LINE__,
			strerror(errno));
		goto fail_setup;
	}

	m->help_title = _("main menu");
	m->help_text = &main_menu_help_text;

	menu_opts_off(m->ncm, O_SHOWDESC);
	set_menu_mark(m->ncm, " *");
	set_current_item(m->ncm, i->nci);

	return m;

fail_setup:
	talloc_free(m);
	return NULL;
}

static struct discover_client_ops cui_client_ops = {
	.device_add = NULL,
	.boot_option_add = cui_boot_option_add,
	.device_remove = cui_device_remove,
	.update_status = cui_update_status,
	.update_sysinfo = cui_update_sysinfo,
	.update_config = cui_update_config,
};

/**
 * cui_init - Setup the cui instance.
 * @platform_info: A value for the struct cui platform_info member.
 *
 * Returns a pointer to a struct cui on success, or NULL on error.
 *
 * Allocates the cui instance, sets up the client and stdin waiters, and
 * sets up the ncurses menu screen.
 */

struct cui *cui_init(void* platform_info,
	int (*js_map)(const struct js_event *e), int start_deamon)
{
	struct cui *cui;
	unsigned int i;

	cui = talloc_zero(NULL, struct cui);
	if (!cui) {
		pb_log("%s: alloc cui failed.\n", __func__);
		fprintf(stderr, _("%s: alloc cui failed.\n"), __func__);
		goto fail_alloc;
	}

	cui->c_sig = pb_cui_sig;
	cui->platform_info = platform_info;
	cui->waitset = waitset_create(cui);

	process_init(cui, cui->waitset, false);

	/* Loop here for scripts that just started the server. */

retry_start:
	for (i = start_deamon ? 2 : 10; i; i--) {
		cui->client = discover_client_init(cui->waitset,
				&cui_client_ops, cui);
		if (cui->client || !i)
			break;
		pb_log("%s: waiting for server %d\n", __func__, i);
		sleep(1);
	}

	if (!cui->client && start_deamon) {
		int result;

		start_deamon = 0;

		result = pb_start_daemon(cui);

		if (!result)
			goto retry_start;

		pb_log("%s: discover_client_init failed.\n", __func__);
		fprintf(stderr, _("%s: error: discover_client_init failed.\n"),
			__func__);
		fprintf(stderr, _("could not start pb-discover, the petitboot "
			"daemon.\n"));
		goto fail_client_init;
	}

	if (!cui->client) {
		pb_log("%s: discover_client_init failed.\n", __func__);
		fprintf(stderr, _("%s: error: discover_client_init failed.\n"),
			__func__);
		fprintf(stderr, _("check that pb-discover, "
			"the petitboot daemon is running.\n"));
		goto fail_client_init;
	}

	atexit(cui_atexit);
	talloc_steal(cui, cui->client);
	cui_start();

	cui->main = main_menu_init(cui);
	if (!cui->main)
		goto fail_client_init;

	waiter_register_io(cui->waitset, STDIN_FILENO, WAIT_IN,
			cui_process_key, cui);

	if (js_map) {

		cui->pjs = pjs_init(cui, js_map);

		if (cui->pjs)
			waiter_register_io(cui->waitset, pjs_get_fd(cui->pjs),
					WAIT_IN, cui_process_js, cui);
	}

	return cui;

fail_client_init:
	talloc_free(cui);
fail_alloc:
	return NULL;
}

/**
 * cui_run - The main cui program loop.
 * @cui: The cui instance.
 * @main: The menu to use as the main menu.
 *
 * Runs the cui engine.  Does not return until indicated to do so by some
 * user action, or an error occurs.  Frees the cui object on return.
 * Returns 0 on success (return to shell), -1 on error (should restart).
 */

int cui_run(struct cui *cui)
{
	assert(main);

	cui->current = &cui->main->scr;
	cui->default_item = 0;

	nc_scr_post(cui->current);

	while (1) {
		int result = waiter_poll(cui->waitset);

		if (result < 0) {
			pb_log("%s: poll: %s\n", __func__, strerror(errno));
			break;
		}

		if (cui->abort)
			break;

		while (cui->resize) {
			cui->resize = 0;
			cui_handle_resize(cui);
		}
	}

	cui_atexit();

	return cui->abort ? 0 : -1;
}
