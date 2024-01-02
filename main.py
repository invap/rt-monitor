import importlib
import logging
import os
import shutil
import sys
import threading

import wx

from workflow_runtime_verification.monitor import Monitor
from workflow_runtime_verification.specification.workflow_specification import (
    WorkflowSpecification,
)


class MainWindow(wx.Frame):
    def __init__(self):
        super().__init__(parent=None, title="Run-time Monitor")
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

        self.simulation_panel = SimulationPanel(parent=self)
        self.simulation_panel.SetFocus()
        self.AddPage(self.simulation_panel, "Run-time monitor setup")

    def close(self):
        self.simulation_panel.close()


class LoggingConf:
    def __init__(self):
        self.level = None
        # Log destination
        self.log_dest = None
        # log_dest = "FILE" : file destination
        self.filename = ""
        self.filemode = "w"
        # log_dest = "VISUAL" : Window box destination
        # log_dest = "STDOUT" : Standard output destination
        self.stream = None


def _configure_logging(logging_cfg):
    match logging_cfg.log_dest:
        case "FILE":
            logging.basicConfig(
                filename=logging_cfg.filename + ".log",
                filemode="w",
                level=logging_cfg.level,
                datefmt="%d/%m/%Y %H:%M:%S",
                format="%(asctime)s : [%(name)s:%(levelname)s] - %(message)s",
                encoding="utf-8",
            )
        case "VISUAL":
            logging.basicConfig(
                stream=sys.stdout,
                level=logging_cfg.level,
                datefmt="%d/%m/%Y %H:%M:%S",
                format="%(asctime)s : [%(name)s:%(levelname)s] - %(message)s",
                encoding="utf-8",
            )
        case "STDOUT":
            logging.basicConfig(
                stream=sys.stdout,
                level=logging_cfg.level,
                datefmt="%d/%m/%Y %H:%M:%S",
                format="%(asctime)s : [%(name)s:%(levelname)s] - %(message)s",
                encoding="utf-8",
            )
        case _:
            logging.basicConfig(
                stream=sys.stdout,
                level=logging.INFO,
                datefmt="%d/%m/%Y %H:%M:%S",
                format="%(asctime)s : [%(name)s:%(levelname)s] - %(message)s",
                encoding="utf-8",
            )


# noinspection PyPropertyAccess
class SimulationPanel(wx.Panel):
    def __init__(self, parent):
        super().__init__(parent=parent)

        self._render()

    def select_report(self, event):
        # Open Dialog
        dialog = wx.FileDialog(
            self,
            "Seleccionar reporte a verificar",
            "",
            "",
            "All files (*.*)|*.*",
            wx.FD_OPEN | wx.FD_FILE_MUST_EXIST,
        )
        if dialog.ShowModal() == wx.ID_OK:
            self.event_report_file_path_field.SetValue(dialog.GetPath())
            self.update_report_properties()
            self._update_start_button()
        dialog.Destroy()

    def select_specification(self, event):
        # Open Dialog
        dialog = wx.FileDialog(
            self,
            "Seleccionar archivo con la especificación del framework (.zip):",
            "",
            "",
            "All files (*.*)|*.*",
            wx.FD_OPEN | wx.FD_FILE_MUST_EXIST,
        )
        if dialog.ShowModal() == wx.ID_OK:
            self.framework_specification_file_path_field.SetValue(dialog.GetPath())
            self._update_start_button()
        dialog.Destroy()

    def update_report_properties(self):
        with open(self.event_report_file_path_field.Value, "r") as f:
            self.total_events_count = sum(1 for _ in f)
            f.close()
        self.simulation_status_text_label.SetLabel(self._simulation_status_label())
        self._refresh_window_layout()

    def on_start(self, _event):
        split_file_path = os.path.split(
            self.framework_specification_file_path_field.Value
        )
        file_directory = split_file_path[0]
        file_name = split_file_path[1]

        file_name_without_extension = os.path.splitext(file_name)[0]
        specification_directory = file_directory + "/" + file_name_without_extension

        try:
            os.mkdir(specification_directory)
        except FileExistsError:
            shutil.rmtree(specification_directory)
            os.mkdir(specification_directory)
        shutil.unpack_archive(file_directory + "/" + file_name, specification_directory)

        # Read variables dictionary, hardware specification and workflow specification from file
        workflow_specification = WorkflowSpecification.new_from_open_file(
            open(specification_directory + "/workflow.desc", "r")
        )
        hardware_specification = self._new_hardware_map_from_open_file(
            open(specification_directory + "/hardware.desc", "r")
        )

        verification = Verification()
        verification.run()

        self.monitor = Monitor(workflow_specification, hardware_specification)

        event_report_file = open(self.event_report_file_path_field.Value, "r")
        process_thread = threading.Thread(
            target=self.monitor.run,
            args=[event_report_file, self._pause_event, self._stop_event],
        )

        verification_thread = threading.Thread(
            target=self._run_verification, args=[process_thread]
        )
        verification_thread.start()

    def on_stop(self, _event):
        self._disable_stop_button()
        self.monitor.stop_hardware_simulation()
        logging.info(
            "Verification is gracefully stopping in the background. "
            "It will stop when it finishes processing the current event."
        )
        self._stop_event.set()

    def on_pause(self, _event):
        self._pause_event.set()
        logging.info(
            "Verification will be paused when it finishes processing "
            "the current event."
        )
        self._show_multi_action_button_as_play()

    def on_play(self, _event):
        self._show_multi_action_button_as_pause()
        logging.info("Verification resumed.")
        self._pause_event.clear()

    def close(self):
        self.on_stop(None)

    def _run_verification(self, process_thread):
        self._stop_event.clear()
        self._pause_event.clear()
        self._enable_stop_button()
        self._show_multi_action_button_as_pause()
        process_thread.start()

        while process_thread.is_alive():
            if self._stop_event.is_set():
                break

        self._disable_stop_button()
        self._show_multi_action_button_as_start()
        self._disable_multi_action_button()

        logging.info(
            "You will be able to restart the verification when the last one is finished."
        )
        process_thread.join()
        if self._stop_event.is_set():
            logging.info("Verification stopped.")

        self.close()
        self._enable_multi_action_button()

    def _render(self):
        self.main_sizer = wx.BoxSizer(wx.VERTICAL)
        self._set_up_components()
        self.SetSizer(self.main_sizer)

    def _set_up_components(self):
        self._set_up_log_file_selection_components()
        self._set_up_workflow_selection_components()
        self._set_up_simulation_status_components()
        self._add_dividing_line()
        self._set_up_action_components()

    def _add_dividing_line(self):
        self.main_sizer.Add(wx.StaticLine(self), 0, wx.EXPAND)

    def _set_up_log_file_selection_components(self):
        action_label = "Seleccionar archivo de reporte de eventos (.txt):"
        action = self.select_report
        self.event_report_file_path_field = wx.TextCtrl(
            self, -1, "", size=(600, 33), style=wx.TE_READONLY
        )

        self._set_up_file_selection_components_with(
            action, action_label, self.event_report_file_path_field
        )

    def _set_up_workflow_selection_components(self):
        action_label = "Seleccionar archivo de especificación del framework:"
        action = self.select_specification
        self.framework_specification_file_path_field = wx.TextCtrl(
            self, -1, "", size=(600, 33), style=wx.TE_READONLY
        )

        self._set_up_file_selection_components_with(
            action, action_label, self.framework_specification_file_path_field
        )

    def _set_up_file_selection_components_with(self, action, action_label, text_field):
        action_label_component = wx.StaticText(self, label=action_label)
        self.main_sizer.Add(action_label_component, 0, wx.LEFT | wx.TOP, border=15)

        folder_icon = wx.ArtProvider.GetBitmap(wx.ART_FOLDER, wx.ART_OTHER, (16, 16))
        folder_selection_button = wx.BitmapButton(self, bitmap=folder_icon)
        folder_selection_button.Bind(wx.EVT_BUTTON, action)

        folder_selection_sizer = wx.BoxSizer(wx.HORIZONTAL)
        folder_selection_sizer.Add(text_field, 0, wx.ALL, border=10)
        folder_selection_sizer.Add(
            folder_selection_button, 0, wx.TOP | wx.BOTTOM | wx.RIGHT, border=10
        )

        self.main_sizer.Add(folder_selection_sizer, 0)

    def _set_up_simulation_status_components(self):
        self.total_events_count = 0
        self.simulation_status_text_label = wx.StaticText(
            self, label=self._simulation_status_label(), style=wx.ALIGN_CENTRE
        )
        self.main_sizer.Add(
            self.simulation_status_text_label, 0, wx.EXPAND | wx.ALL, border=10
        )

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

    def _simulation_status_label(self):
        return f"Cantidad de eventos a verificar: {self.total_events_count}\n"

    def _update_start_button(self):
        report_file_path = self.event_report_file_path_field.Value
        report_file_was_selected = report_file_path.endswith(".txt")

        specification_file_path = self.framework_specification_file_path_field.Value
        specification_file_was_selected = specification_file_path.endswith(".zip")

        if report_file_was_selected and specification_file_was_selected:
            self._enable_multi_action_button()
        else:
            self._disable_multi_action_button()

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
        self.stop_button.Disable()

    def _enable_stop_button(self):
        self.stop_button.Enable()

    def _disable_multi_action_button(self):
        self.multi_action_button.Disable()

    def _enable_multi_action_button(self):
        self.multi_action_button.Enable()

    def _refresh_window_layout(self):
        self.main_sizer.Layout()

    def _new_hardware_map_from_open_file(self, hardware_file):
        hardware_map = {}

        for line in hardware_file:
            split_line = line.split(",")

            device_name = split_line[0]

            component_class_path = split_line[1].strip()
            split_component_class_path = component_class_path.rsplit(".", 1)
            component_module = importlib.import_module(split_component_class_path[0])
            component_class = getattr(component_module, split_component_class_path[1])

            hardware_map[device_name] = component_class()

        return hardware_map


class Verification:
    def run(self):
        self._set_up()

    def _set_up(self):
        self._set_up_logging()

    def _set_up_logging(self):
        logging_cfg = LoggingConf()
        logging_cfg.log_dest = "STDOUT"
        logging_cfg.level = logging.INFO
        _configure_logging(logging_cfg)


if __name__ == "__main__":
    app = wx.App()
    mainWindow = MainWindow()
    app.MainLoop()
