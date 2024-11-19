# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import threading
from enum import Enum, auto

import wx

from errors.monitor_errors import FrameworkError, EventLogListError, MonitorConstructionError, AbortRun
from logging_configuration import (
    _set_up_logging,
    _configure_logging_destination,
    _configure_logging_level
)
from monitor import Monitor
from monitor_builder import MonitorBuilder


class MonitoringPanel(wx.Panel):
    class AnalysisStatus(Enum):
        NOT_RUNNING = auto()
        RUNNING = auto()
        PAUSING = auto()
        PAUSED = auto()
        STOPPING = auto()

    def __init__(self, parent):
        super().__init__(parent=parent)
        self._monitor = None
        # Events for managing the analysis process
        self._pause_event = threading.Event()
        self._has_paused_event = threading.Event()
        self._stop_event = threading.Event()
        self._has_stopped_event = threading.Event()
        self._analysis_process_status = MonitoringPanel.AnalysisStatus.NOT_RUNNING
        # To be assigned whenever the monitor is created
        self._event_count_function = None
        # Variables for keeping the event count and elapsed time.
        self._elapsed_seconds = 0
        self._amount_of_events_to_verify = 0
        self._amount_of_processed_events = 0
        self._render()

    def on_start(self, event):
        # Configure logging
        _set_up_logging()
        _configure_logging_destination(self.Parent.logging_destination())
        _configure_logging_level(self.Parent.logging_verbosity())
        # Create the Monitor
        monitor_builder = MonitorBuilder(
            self.Parent.monitor_configuration_panel.framework_file_path_field.Value,
            self.Parent.monitor_configuration_panel.report_list_file_path_field.Value,
        )
        try:
            self._monitor = monitor_builder.build_monitor(True)
        except FrameworkError:
            logging.error(f"Monitor construction failed due to a framework creation error.")
        except EventLogListError:
            logging.error(f"Monitor construction failed due to a report list error.")
        except MonitorConstructionError:
            logging.error(f"Monitor construction failed.")
        else:
            # Launches the runtime verification
            # Set the function for retrieve statistics from monitor
            self._event_count_function = self._monitor.get_event_count
            # Variables for keeping the event count and elapsed time.
            self._elapsed_seconds = 0
            self._amount_of_events_to_verify = self._event_count_function()[0]
            self._amount_of_processed_events = 0
            # Set up the information on the visual interface
            self.amount_of_events_to_verify_text_label.SetLabel(self._amount_of_events_to_verify_label())
            self.progress_bar.SetRange(self._amount_of_events_to_verify)
            # Events setup for managing the running mode.
            self._pause_event.set()
            self._has_paused_event.set()
            self._stop_event.set()
            self._has_stopped_event.set()
            self._analysis_process_status = MonitoringPanel.AnalysisStatus.RUNNING
            # Creates a thread for controlling the analysis process
            application_thread = threading.Thread(
                target=self._run_verification, args=[self._monitor]
            )
            # Update visual interface according to STARTED.
            self._disable_logging_configuration_components()
            self._show_multi_action_button_as_pause()
            self._enable_stop_button()
            self._start_timer()
            try:
                application_thread.start()
            except AbortRun():
                logging.critical(f"Runtime verification process ABORTED.")

    def on_pause(self, event):
        if self._analysis_process_status == MonitoringPanel.AnalysisStatus.RUNNING:
            # Trigger pause event.
            self._pause_event.clear()
            self._analysis_process_status = MonitoringPanel.AnalysisStatus.PAUSING
            logging.warning(
                "Verification is gracefully pausing in background. "
                "It will PAUSE when it finishes processing the current event."
            )
            # Wait until the monitor thread notifies that the analysis haf been gracefully paused
            while self._has_paused_event.is_set():
                pass
            self._analysis_process_status = MonitoringPanel.AnalysisStatus.PAUSED
            logging.warning("Verification PAUSED.")
            # Update visual interface according to PAUSED.
            self._show_multi_action_button_as_play()
            self._disable_stop_button()
            self._stop_timer()

    def on_play(self, event):
        if self._analysis_process_status == MonitoringPanel.AnalysisStatus.PAUSED:
            # Recover from pause.
            self._pause_event.set()
            self._analysis_process_status = MonitoringPanel.AnalysisStatus.RUNNING
            logging.warning("Verification RESUMED.")
            # Update visual interface according to RESUMED.
            self._show_multi_action_button_as_pause()
            self._enable_stop_button()
            self._start_timer()

    def on_stop(self, event):
        if self._analysis_process_status == MonitoringPanel.AnalysisStatus.RUNNING:
            # Trigger stop event.
            self._stop_event.clear()
            self._analysis_process_status = MonitoringPanel.AnalysisStatus.STOPPING
            logging.warning(
                "Verification is gracefully stopping in background. "
                "It will STOP when it finishes processing the current event."
            )
            # Wait until the monitor thread notifies that the analysis haf been gracefully stopped
            while self._has_stopped_event.is_set():
                pass
            logging.warning("Verification STOPPED.")

    def close(self, event):
        was_vetoed = False
        if self._analysis_process_status != MonitoringPanel.AnalysisStatus.NOT_RUNNING:
            event.Veto()
            was_vetoed = True
        return was_vetoed

    def _run_verification(self, process_thread):
        # Configure the monitor by setting up control events.
        self._monitor.set_events(self._pause_event, self._has_paused_event, self._stop_event, self._has_stopped_event)
        # Starts the monitor thread
        process_thread.start()
        # Waiting for the verification process to finish, either naturally or manually.
        process_thread.join()
        # Change analysis status.
        self._analysis_process_status = MonitoringPanel.AnalysisStatus.NOT_RUNNING
        # Update visual interface according to STOPPED or FINISHED.
        self._enable_logging_configuration_components()
        self.show_multi_action_button_as_start()
        self._disable_stop_button()
        self._stop_timer()

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
            self, label=self._amount_of_events_to_verify_label()
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

    def _amount_of_events_to_verify_label(self):
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

    def _stop_timer(self):
        if self._last_updated_time is not None:
            self._timer.Stop()
            self._update_status()

    def _update_status(self):
        # Retrieve statistics from monitor.
        self._amount_of_processed_events = self._event_count_function()[1]
        # Update status.
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

    # DEPRECATED but maybe we return to accepting zipped frameworks
    # @staticmethod
    # def _unpack_framework_file(file_path):
    #     split_file_path = os.path.split(file_path)
    #     file_directory = split_file_path[0]
    #     file_name = split_file_path[1]
    #
    #     file_name_without_extension = os.path.splitext(file_name)[0]
    #     framework_directory = os.path.join(
    #         file_directory, file_name_without_extension
    #     )
    #     try:
    #         os.mkdir(framework_directory)
    #     except FileExistsError:
    #         shutil.rmtree(framework_directory)
    #         os.mkdir(framework_directory)
    #
    #     shutil.unpack_archive(file_path, framework_directory)
    #     return framework_directory
