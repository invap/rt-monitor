# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import os
import shutil
import threading

import toml
import wx

from errors.monitor_errors import FrameworkError, ReportListError, MonitorConstructionError, AbortRun
from monitor import Monitor


class MonitoringPanel(wx.Panel):
    def __init__(self, parent):
        super().__init__(parent=parent)
        self._monitor = None
        self._pause_event = threading.Event()
        self._stop_event = threading.Event()
        self._amount_of_events_to_verify = 0
        self._amount_of_processed_events = 0
        self._elapsed_seconds = 0
        self._render()

    def update_start_button(self):
        if (self.Parent.monitor_configuration_panel.framework_chosen and
                self.Parent.monitor_configuration_panel.event_report_file_chosen):
            self._enable_multi_action_button()
        else:
            self._disable_multi_action_button()

    def on_start(self, event):
        try:
            self._monitor = (
                Monitor.new_from_files(
                    self.Parent.logging_destination(),
                    self.Parent.logging_verbosity(),
                    self.Parent.monitor_configuration_panel.framework_file_path_field.Value,
                    self.Parent.monitor_configuration_panel.report_list_file_path_field.Value,
                    True
                )
            )
        except FrameworkError:
            logging.error(f"Monitor construction failed due to a framework creation error.")
        except ReportListError:
            logging.error(f"Monitor construction failed due to a report list error.")
        except MonitorConstructionError:
            logging.error(f"Monitor construction failed.")
        else:
            amount_of_events = 0
            # All this just to show the total numbers of events to be monitored!!!
            # The report list file is guarantied to be correct because the Monitor already was created
            toml_reports_map = toml.load(self.Parent.monitor_configuration_panel.report_list_file_path_field.Value)
            for event_report in toml_reports_map["event_reports"]:
                # The main report file is guarantied to be present in the report list file
                if event_report["name"] == "main":
                    with open(event_report["file"], "r") as main_report_file:
                        amount_of_events = len(main_report_file.readlines())
                    main_report_file.close()
                    break
            #
            self._amount_of_events_to_verify = amount_of_events
            self.amount_of_events_to_verify_text_label.SetLabel(self.amount_of_events_to_verify_label())
            self._amount_of_processed_events = 0
            self.progress_bar.SetRange(self._amount_of_events_to_verify)
            # Building threads for executing the monitor and the events managing concurrently
            monitor_thread = threading.Thread(
                target=self._monitor.run,
                args=[self._pause_event, self._stop_event, self.update_amount_of_processed_events])
            application_thread = threading.Thread(
                target=self.run_verification, args=[monitor_thread]
            )
            self._start_timer()
            try:
                application_thread.start()
            except AbortRun():
                logging.critical(f"Runtime monitoring process ABORTED.")

    def on_pause(self, event):
        self._pause_event.set()
        logging.warning("Verification will be paused when it finishes processing the current event.")
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

    def close(self, event):
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
                logging.warning("You will be able to restart the verification when the last one finishes.")
                break
        self._disable_stop_button()
        self.show_multi_action_button_as_start()
        self._disable_multi_action_button()
        self._enable_logging_configuration_components()
        process_thread.join()
        if self._stop_event.is_set():
            logging.warning("Verification stopped.")
        self._stop_verification()
        self._enable_multi_action_button()

    def update_amount_of_processed_events(self):
        self._amount_of_processed_events += 1

    def _stop_verification(self):
        self._disable_stop_button()
        self._timer.Stop()
        self._stop_event.set()
        if self._monitor is not None:
            self._monitor.stop_component_monitoring()

    def _render(self):
        self.main_sizer = wx.BoxSizer(wx.VERTICAL)
        # Seting up components
        self._set_up_monitoring_status_components()
        self._add_dividing_line()
        self._set_up_action_components()
        self.SetSizer(self.main_sizer)

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

    @staticmethod
    def _add_to_grid(grid, text_label, numeric_label):
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
            percentage = (self._amount_of_processed_events / self._amount_of_events_to_verify) * 100

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

    def show_multi_action_button_as_start(self):
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

    @staticmethod
    def _unpack_framework_file(file_path):
        split_file_path = os.path.split(file_path)
        file_directory = split_file_path[0]
        file_name = split_file_path[1]

        file_name_without_extension = os.path.splitext(file_name)[0]
        framework_directory = os.path.join(
            file_directory, file_name_without_extension
        )
        try:
            os.mkdir(framework_directory)
        except FileExistsError:
            shutil.rmtree(framework_directory)
            os.mkdir(framework_directory)

        shutil.unpack_archive(file_path, framework_directory)
        return framework_directory
