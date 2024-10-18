# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import os
import shutil
import threading

import wx

from logging_configuration import LoggingLevel, LoggingDestination
from verification import Verification
from workflow_runtime_verification.errors import AbortRun, EventLogFileMissing


class MainWindow(wx.Frame):
    def __init__(self):
        super().__init__(parent=None, title="Runtime Monitor")
        self.Bind(wx.EVT_CLOSE, self.on_close)
        self._set_up_control_panel()
        self._adjust_size_and_show()

    def _set_up_control_panel(self):
        self.control_panel = ControlPanel(parent=self)
        self.main_sizer = wx.BoxSizer(wx.VERTICAL)
        self.main_sizer.Add(self.control_panel)

    def _adjust_size_and_show(self):
        self.SetSizerAndFit(self.main_sizer)
        self.Centre()
        self.Show()

    def on_close(self, event):
        self.control_panel.close()
        self.Destroy()
        wx.Exit()


class ControlPanel(wx.Notebook):
    def __init__(self, parent):
        super().__init__(parent=parent)

        self.monitor_configuration_panel = MonitorConfigurationPanel(parent=self)
        self.logging_configuration_panel = LoggingConfigurationPanel(parent=self)
        self.monitoring_panel = MonitoringPanel(parent=self)
        self.monitor_configuration_panel.SetFocus()

        self.AddPage(self.monitor_configuration_panel, "Monitor configuration")
        self.AddPage(self.logging_configuration_panel, "Log configuration")
        self.AddPage(self.monitoring_panel, "Monitoring status")

    def close(self):
        self.monitoring_panel.close()

    def logging_destination(self):
        return self.logging_configuration_panel.logging_destination()

    def logging_verbosity(self):
        return self.logging_configuration_panel.logging_verbosity()

    def disable_logging_configuration_components(self):
        self.logging_configuration_panel.Disable()

    def enable_logging_configuration_components(self):
        self.logging_configuration_panel.Enable()


class MonitorConfigurationPanel(wx.Panel):
    def __init__(self, parent):
        super().__init__(parent=parent)
        self.framework_specification_chosen = False
        self.event_report_file_chosen = False
        self.specification_dir = ""
        self._render()

    def select_specification(self, event):
        # Open Dialog
        dialog = wx.FileDialog(
            self,
            "Select analysis framework file (.toml):",
            "",
            "",
            "All files (*.*)|*.*",
            wx.FD_OPEN | wx.FD_FILE_MUST_EXIST,
        )
        if dialog.ShowModal() == wx.ID_OK:
            self.framework_specification_file_path_field.SetValue(dialog.GetPath())
            self.framework_specification_chosen = True
            self.specification_dir = self.framework_specification_file_path_field.Value
            wx.CallAfter(self.log_folder_button.Enable)
        dialog.Destroy()

    def select_report(self, event):
        # Open Dialog
        dialog = wx.FileDialog(
            self,
            "Select event report file list",
            "",
            "",
            "All files (*.*)|*.*",
            wx.FD_OPEN | wx.FD_FILE_MUST_EXIST,
        )
        if dialog.ShowModal() == wx.ID_OK:
            self.event_report_file_path_field.SetValue(dialog.GetPath())
            self.event_report_file_chosen = True
            self._update_amount_of_events_to_verify()
            self.Parent.monitoring_panel.update_start_button()
        dialog.Destroy()

    def _set_up_workflow_selection_components(self):
        action_label = "Select analysis framework file (.toml):"
        action = self.select_specification
        self.framework_specification_file_path_field = wx.TextCtrl(
            self, -1, "", size=(600, 33), style=wx.TE_READONLY
        )
        action_label_component = wx.StaticText(self, label=action_label)
        self.main_sizer.Add(action_label_component, 0, wx.LEFT | wx.TOP, border=15)

        folder_icon = wx.ArtProvider.GetBitmap(wx.ART_FOLDER, wx.ART_OTHER, (16, 16))
        folder_selection_button = wx.BitmapButton(self, bitmap=folder_icon)
        folder_selection_button.Bind(wx.EVT_BUTTON, action)

        folder_selection_sizer = wx.BoxSizer(wx.HORIZONTAL)
        folder_selection_sizer.Add(self.framework_specification_file_path_field, 0, wx.ALL, border=10)
        folder_selection_sizer.Add(
            folder_selection_button, 0, wx.TOP | wx.BOTTOM | wx.RIGHT, border=10
        )
        self.main_sizer.Add(folder_selection_sizer, 0)

    def _set_up_log_file_selection_components(self):
        action_label = "Select event report files (.txt):"
        action = self.select_report
        self.event_report_file_path_field = wx.TextCtrl(
            self, -1, "", size=(600, 33), style=wx.TE_READONLY
        )
        action_label_component = wx.StaticText(self, label=action_label)
        self.main_sizer.Add(action_label_component, 0, wx.LEFT | wx.TOP, border=15)

        folder_icon = wx.ArtProvider.GetBitmap(wx.ART_FOLDER, wx.ART_OTHER, (16, 16))
        folder_selection_button = wx.BitmapButton(self, bitmap=folder_icon)
        folder_selection_button.Bind(wx.EVT_BUTTON, action)
        self.log_folder_button = folder_selection_button
        wx.CallAfter(self.log_folder_button.Disable)

        folder_selection_sizer = wx.BoxSizer(wx.HORIZONTAL)
        folder_selection_sizer.Add(self.event_report_file_path_field, 0, wx.ALL, border=10)
        folder_selection_sizer.Add(
            folder_selection_button, 0, wx.TOP | wx.BOTTOM | wx.RIGHT, border=10
        )
        self.main_sizer.Add(folder_selection_sizer, 0)

    def _add_dividing_line(self):
        self.main_sizer.Add(wx.StaticLine(self), 0, wx.EXPAND)

    def _set_up_components(self):
        self._set_up_workflow_selection_components()
        self._add_dividing_line()
        self._set_up_log_file_selection_components()

    def _render(self):
        self.main_sizer = wx.BoxSizer(wx.VERTICAL)
        self._set_up_components()
        self.SetSizer(self.main_sizer)

    def _update_amount_of_events_to_verify(self):
        main_log_path = None
        with open(self.event_report_file_path_field.GetValue(), "r") as file:
            for line in file:
                split_line = line.strip().split(",")
                device_name = split_line[0]
                if device_name == "main":
                    main_log_path = split_line[1]
            if main_log_path is None:
                raise EventLogFileMissing("main")
        with open(main_log_path, "r") as file:
            self.Parent.monitoring_panel._amount_of_events_to_verify = len(file.readlines())
            file.close()
        self.Parent.monitoring_panel.amount_of_events_to_verify_text_label.SetLabel(
            self.Parent.monitoring_panel.amount_of_events_to_verify_label()
        )
        self.Parent.monitoring_panel.progress_bar.SetRange(self.Parent.monitoring_panel._amount_of_events_to_verify)

    @staticmethod
    def _unpack_specification_file(file_path):
        split_file_path = os.path.split(file_path)
        file_directory = split_file_path[0]
        file_name = split_file_path[1]

        file_name_without_extension = os.path.splitext(file_name)[0]
        specification_directory = os.path.join(
            file_directory, file_name_without_extension
        )
        try:
            os.mkdir(specification_directory)
        except FileExistsError:
            shutil.rmtree(specification_directory)
            os.mkdir(specification_directory)

        shutil.unpack_archive(file_path, specification_directory)
        return specification_directory


class LoggingConfigurationPanel(wx.Panel):
    def __init__(self, parent):
        super().__init__(parent=parent)
        self._set_up_components()

    def _set_up_components(self):
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self._set_up_logging_configuration_components()
        self.SetSizer(self.sizer)

    def _set_up_logging_configuration_components(self):
        logging_configuration_label_component = wx.StaticText(
            self, label="Log configuration"
        )
        self.sizer.Add(
            logging_configuration_label_component, 0, wx.LEFT | wx.TOP, border=15
        )
        self.sizer.AddStretchSpacer()
        self._set_up_logging_verbosity_configuration_components()
        self._set_up_logging_destination_configuration_components()
        self.sizer.AddStretchSpacer()

    def _set_up_logging_verbosity_configuration_components(self):
        label = wx.StaticText(self, label="Type of log entries to register:")
        self._logging_verbosity_selector = wx.Choice(
            self, choices=LoggingConfigurationPanel._logging_verbosity_options(), size=(200, 35)
        )
        self._logging_verbosity_selector.Bind(
            wx.EVT_CHOICE, self._select_logging_verbosity
        )
        self._select_default_logging_verbosity(self._logging_verbosity_selector)
        logging_verbosity_selection_sizer = wx.BoxSizer(wx.HORIZONTAL)
        logging_verbosity_selection_sizer.Add(
            label, 0, wx.LEFT | wx.ALIGN_CENTER_VERTICAL, border=15
        )
        logging_verbosity_selection_sizer.Add(
            self._logging_verbosity_selector, 0, wx.LEFT | wx.RIGHT, border=15
        )
        self.sizer.Add(logging_verbosity_selection_sizer, 0, wx.CENTER)

    def _set_up_logging_destination_configuration_components(self):
        label = wx.StaticText(self, label="Log destination:")

        self._logging_destination_selector = wx.Choice(
            self, choices=LoggingConfigurationPanel._logging_destination_options(), size=(200, 35)
        )
        self._logging_destination_selector.Bind(
            wx.EVT_CHOICE, self._select_logging_destination
        )
        self._select_default_logging_destination(self._logging_destination_selector)

        logging_destination_selection_sizer = wx.BoxSizer(wx.HORIZONTAL)
        logging_destination_selection_sizer.Add(
            label, 0, wx.LEFT | wx.TOP | wx.BOTTOM | wx.ALIGN_CENTER_VERTICAL, border=15
        )
        logging_destination_selection_sizer.Add(
            self._logging_destination_selector,
            0,
            wx.LEFT | wx.TOP | wx.BOTTOM | wx.RIGHT,
            border=15,
        )

        self.sizer.Add(logging_destination_selection_sizer, 0, wx.CENTER)

    def _select_default_logging_verbosity(self, selector):
        default_selection_index = 0
        selector.SetSelection(default_selection_index)
        self._logging_verbosity = self._logging_verbosity_from_text(
            selector.GetString(default_selection_index)
        )

    def _select_logging_verbosity(self, event):
        selected_option = event.GetString()
        self._logging_verbosity = LoggingConfigurationPanel._logging_verbosity_from_text(selected_option)

    @staticmethod
    def _logging_verbosity_from_text(selected_option):
        return LoggingConfigurationPanel._text_to_logging_verbosity_map()[selected_option]

    @staticmethod
    def _text_to_logging_verbosity_map():
        return {
            "All entries": LoggingLevel.INFO,
            "Analysis related entries": LoggingLevel.PROPERTY_ANALYSIS,
            "Error and warning entries": LoggingLevel.WARNING,
            "Error entries": LoggingLevel.ERROR,
        }

    @staticmethod
    def _logging_verbosity_options():
        return list(LoggingConfigurationPanel._text_to_logging_verbosity_map().keys())

    def _select_default_logging_destination(self, selector):
        default_selection_index = 0
        selector.SetSelection(default_selection_index)
        self._logging_destination = selector.GetString(default_selection_index)

    def _select_logging_destination(self, event):
        self._logging_destination = event.GetString()

    @staticmethod
    def _logging_destination_options():
        return LoggingDestination.all()

    def logging_destination(self):
        return self._logging_destination

    def logging_verbosity(self):
        return self._logging_verbosity


class MonitoringPanel(wx.Panel):
    def __init__(self, parent):
        super().__init__(parent=parent)

        self._verification = None
        self._set_up_initial_verification_status()
        self._render()

    def update_start_button(self):
        if (self.Parent.monitor_configuration_panel.framework_specification_chosen and
                self.Parent.monitor_configuration_panel.event_report_file_chosen):
            self._enable_multi_action_button()
        else:
            self._disable_multi_action_button()

    def on_start(self, _event):
        try:
            self._set_up_initial_verification_status()
            self._verification = Verification.new_from_toml_file(
                self.Parent.monitor_configuration_panel.specification_dir
            )
            self._verification.run_for_report(
                self.Parent.monitor_configuration_panel.event_report_file_path_field.Value,
                self.Parent.logging_destination(),
                self.Parent.logging_verbosity(),
                self._pause_event,
                self._stop_event,
                self,
            )
            self._start_timer()
        except AbortRun():
            logging.critical(f"Runtime monitoring process ABORTED.")

    def on_pause(self, event):
        self._pause_event.set()
        logging.warning(
            "Verification will be paused when it finishes processing "
            "the current event."
        )
        self._show_multi_action_button_as_play()
        self._stop_timer(event)

    def on_play(self, _event):
        self._show_multi_action_button_as_pause()
        logging.warning("Verification resumed.")
        self._pause_event.clear()
        self._start_timer()

    def on_stop(self, _event):
        logging.warning(
            "Verification is gracefully stopping in background. "
            "It will stop when it finishes processing the current event."
        )
        self._stop_verification()

    def close(self):
        if self._stop_event.is_set():
            return
        self._stop_verification()

    def run_verification(self, process_thread):
        self._stop_event.clear()
        self._pause_event.clear()
        self._enable_stop_button()
        self._show_multi_action_button_as_pause()
        self._disable_logging_configuration_components()

        process_thread.start()
        while process_thread.is_alive():
            if self._stop_event.is_set():
                logging.warning(
                    "You will be able to restart the verification when "
                    "the last one finishes."
                )
                break

        self._disable_stop_button()
        self._show_multi_action_button_as_start()
        self._disable_multi_action_button()
        self._enable_logging_configuration_components()

        process_thread.join()
        if self._stop_event.is_set():
            logging.warning("Verification stopped.")

        self.close()
        self._enable_multi_action_button()

    def update_amount_of_processed_events(self):
        self._amount_of_processed_events += 1

    def _set_up_initial_verification_status(self):
        self._amount_of_events_to_verify = 0
        self._amount_of_processed_events = 0
        self._elapsed_seconds = 0

    def _stop_verification(self):
        self._disable_stop_button()
        self._timer.Stop()

        self._stop_event.set()

        if self._verification is not None:
            self._verification.stop_component_monitoring()

    def _render(self):
        self.main_sizer = wx.BoxSizer(wx.VERTICAL)
        self._set_up_components()
        self.SetSizer(self.main_sizer)

    def _set_up_components(self):
        self._set_up_monitoring_status_components()
        self._add_dividing_line()
        self._set_up_action_components()

    def _add_dividing_line(self):
        self.main_sizer.Add(wx.StaticLine(self), 0, wx.EXPAND)

    def _set_up_monitoring_status_components(self):
        monitoring_status_label = wx.StaticText(self, label="Monitoring state")
        self.main_sizer.Add(monitoring_status_label, 0, wx.TOP | wx.LEFT, border=15)

        grid = wx.GridSizer(2, 2, 5, 5)
        self._set_up_events_to_verify(grid)
        self._set_up_elapsed_time(grid)
        self._set_up_processed_events(grid)
        self._set_up_estimated_remaining_time(grid)

        self.main_sizer.Add(grid, 0, wx.EXPAND)

        self._set_up_progress_bar()

    def _set_up_progress_bar(self):
        self._percentage_of_processed_events_label = wx.StaticText(
            self, label=self._percentage_of_processed_events_label_text()
        )
        self.progress_bar = wx.Gauge(self, range=self._amount_of_events_to_verify)
        progress_bar_sizer = wx.BoxSizer(wx.HORIZONTAL)
        progress_bar_sizer.Add(self.progress_bar, 1, wx.ALIGN_CENTER_VERTICAL)
        progress_bar_sizer.Add(
            self._percentage_of_processed_events_label,
            0,
            wx.ALIGN_CENTER_VERTICAL | wx.LEFT,
            border=10,
        )
        self.main_sizer.Add(
            progress_bar_sizer, 0, wx.EXPAND | wx.LEFT | wx.RIGHT | wx.BOTTOM, border=25
        )

    def _add_to_grid(self, grid, text_label, numeric_label):
        sizer = wx.BoxSizer(wx.VERTICAL)

        sizer.Add(text_label, 0, wx.ALIGN_LEFT)
        sizer.Add(numeric_label, 0, wx.EXPAND)

        grid.Add(sizer, 0, wx.LEFT | wx.RIGHT | wx.TOP | wx.EXPAND, border=25)

    def _set_up_processed_events(self, grid):
        text_label = wx.StaticText(self, label="Processed events:")
        self.amount_of_processed_events_text_label = wx.StaticText(
            self, label=self._amount_of_processed_events_label()
        )

        self._add_to_grid(grid, text_label, self.amount_of_processed_events_text_label)

    def _set_up_events_to_verify(self, grid):
        text_label = wx.StaticText(self, label="Events to process:")
        self.amount_of_events_to_verify_text_label = wx.StaticText(
            self, label=self.amount_of_events_to_verify_label()
        )

        self._add_to_grid(grid, text_label, self.amount_of_events_to_verify_text_label)

    def _set_up_elapsed_time(self, grid):
        self._timer = wx.Timer(self)
        self.Bind(wx.EVT_TIMER, self._update_timer, source=self._timer)

        text_label = wx.StaticText(self, label="Elapsed time of analysis:")
        self._elapsed_time_label = wx.StaticText(
            self, label=self._elapsed_time_label_text()
        )

        self._add_to_grid(grid, text_label, self._elapsed_time_label)

    def _set_up_estimated_remaining_time(self, grid):
        text_label = wx.StaticText(self, label="Estimated time to completion:")
        self._estimated_remaining_time_label = wx.StaticText(
            self, label=self._estimated_remaining_time_label_text()
        )
        self._add_to_grid(grid, text_label, self._estimated_remaining_time_label)

    def _set_up_action_components(self):
        self._pause_event = threading.Event()
        self._stop_event = threading.Event()

        self.multi_action_button = wx.Button(self, label="Start")
        self.multi_action_button.Bind(wx.EVT_BUTTON, self.on_start)
        self._disable_multi_action_button()

        self.stop_button = wx.Button(self, label="Stop")
        self.stop_button.Bind(wx.EVT_BUTTON, self.on_stop)
        self._disable_stop_button()

        action_buttons_sizer = wx.BoxSizer(wx.HORIZONTAL)
        action_buttons_sizer.Add(self.multi_action_button, 0, wx.ALL, border=10)
        action_buttons_sizer.Add(self.stop_button, 0, wx.ALL, border=10)

        self.main_sizer.Add(action_buttons_sizer, 0, wx.CENTER)

    def amount_of_events_to_verify_label(self):
        return f"{self._amount_of_events_to_verify}\n"

    def _amount_of_processed_events_label(self):
        return f"{self._amount_of_processed_events}\n"

    def _percentage_of_processed_events_label_text(self):
        if self._amount_of_events_to_verify == 0:
            percentage = 0
        else:
            percentage = (
                self._amount_of_processed_events / self._amount_of_events_to_verify
            ) * 100

        return f"{int(percentage)}%"

    def _elapsed_time_label_text(self):
        hours = self._elapsed_seconds // 3600
        minutes = (self._elapsed_seconds % 3600) // 60
        seconds = self._elapsed_seconds % 60

        return f"{hours:02d}:{minutes:02d}:{seconds:02d}"

    def _estimated_remaining_time_label_text(self):
        if (
            self._amount_of_events_to_verify == 0
            or self._amount_of_processed_events == 0
        ):
            estimated_remaining_seconds = 0
        else:
            seconds_per_event = self._elapsed_seconds / self._amount_of_processed_events
            remaining_events = (
                self._amount_of_events_to_verify - self._amount_of_processed_events
            )
            estimated_remaining_seconds = int(seconds_per_event * remaining_events)

        hours = estimated_remaining_seconds // 3600
        minutes = (estimated_remaining_seconds % 3600) // 60
        seconds = estimated_remaining_seconds % 60

        return f"{hours:02d}:{minutes:02d}:{seconds:02d}"

    def _start_timer(self):
        self._last_updated_time = MonitoringPanel._current_time()
        self._timer.Start(10)

    def _update_timer(self, _event):
        if self._last_updated_time is not None:
            self._update_status()

    def _stop_timer(self, _event):
        if self._last_updated_time is not None:
            self._timer.Stop()
            self._update_status()

    def _update_status(self):
        current_time = MonitoringPanel._current_time()
        self._elapsed_seconds += (current_time - self._last_updated_time).GetSeconds()
        self._last_updated_time = current_time

        self._elapsed_time_label.SetLabel(self._elapsed_time_label_text())
        self._estimated_remaining_time_label.SetLabel(
            self._estimated_remaining_time_label_text()
        )

        self.amount_of_processed_events_text_label.SetLabel(
            self._amount_of_processed_events_label()
        )

        self._update_progress_bar()
        self._percentage_of_processed_events_label.SetLabel(
            self._percentage_of_processed_events_label_text()
        )

        self.Update()

    def _update_progress_bar(self):
        wx.Yield()
        self.progress_bar.SetValue(self._amount_of_processed_events)

    @staticmethod
    def _current_time():
        return wx.DateTime.Now()

    def _show_multi_action_button_as_start(self):
        self.multi_action_button.SetLabel("Start")
        self.multi_action_button.Bind(wx.EVT_BUTTON, self.on_start)
        self._enable_multi_action_button()

    def _show_multi_action_button_as_pause(self):
        self.multi_action_button.SetLabel("Pause")
        self.multi_action_button.Bind(wx.EVT_BUTTON, self.on_pause)
        self._enable_multi_action_button()

    def _show_multi_action_button_as_play(self):
        self.multi_action_button.SetLabel("Play")
        self.multi_action_button.Bind(wx.EVT_BUTTON, self.on_play)
        self._enable_multi_action_button()

    def _disable_stop_button(self):
        wx.CallAfter(self.stop_button.Disable)

    def _enable_stop_button(self):
        wx.CallAfter(self.stop_button.Enable)

    def _disable_multi_action_button(self):
        wx.CallAfter(self.multi_action_button.Disable)

    def _enable_multi_action_button(self):
        wx.CallAfter(self.multi_action_button.Enable)

    def _disable_logging_configuration_components(self):
        self.Parent.disable_logging_configuration_components()

    def _enable_logging_configuration_components(self):
        self.Parent.enable_logging_configuration_components()


if __name__ == "__main__":
    app = wx.App()
    mainWindow = MainWindow()
    app.MainLoop()
