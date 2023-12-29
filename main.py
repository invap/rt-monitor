import importlib
import logging
import os
import shutil
import sys
import threading

import wx

from workflow_runtime_verification.monitor import Monitor, AbortRun
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
        # del self.control_panel
        self.Destroy()
        wx.Exit()


class ControlPanel(wx.Notebook):
    def __init__(self, parent):
        super().__init__(parent=parent)

        simulation_panel = SimulationPanel(parent=self)
        simulation_panel.SetFocus()
        self.AddPage(simulation_panel, "Run-time monitor setup")


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


class SimulationPanel(wx.Panel):
    def __init__(self, parent):
        super().__init__(parent=parent)
        self.main_sizer = wx.BoxSizer(wx.VERTICAL)
        self._set_up_components()
        self.SetSizer(self.main_sizer)

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
        dialog.Destroy()

    def select_specification(self, event):
        # Open Dialog
        dialog = wx.FileDialog(
            self,
            "Seleccionar archivo con la especificación del framework",
            "",
            "",
            "All files (*.*)|*.*",
            wx.FD_OPEN | wx.FD_FILE_MUST_EXIST,
        )
        if dialog.ShowModal() == wx.ID_OK:
            self.framework_specification_file_path_field.SetValue(dialog.GetPath())
        dialog.Destroy()

    def update_report_properties(self):
        with open(self.event_report_file_path_field.Value, "r") as f:
            self.total_events_count = sum(1 for _ in f)
            f.close()
        self.simulation_status_text_label.SetLabel(self._simulation_status_label())
        self.main_sizer.Layout()
        self.event_report_file_path_field.Refresh()

    @staticmethod
    def __new_hardware_map_from_open_file(hardware_file):
        hardware_map = {}
        for line in hardware_file:
            line_ = line.split(",")
            # line_[0]: device name
            # line_[1]: complete class name (including package, module, etc.)
            classname_str = "".join(line_[1:])
            pkg_mod_class_str = classname_str.strip()
            mod_classname = pkg_mod_class_str.rsplit(".", 1)
            module = importlib.import_module(mod_classname[0])
            my_class = getattr(module, mod_classname[1])
            hardware_map[line_[0]] = my_class()
        return hardware_map

    def on_start(self, event):
        path_file = os.path.split(self.framework_specification_file_path_field.Value)
        file_ext = os.path.splitext(path_file[1])
        directory = path_file[0] + "/" + file_ext[0]
        try:
            os.mkdir(directory)
        except FileExistsError:
            shutil.rmtree(directory)
            os.mkdir(directory)
        shutil.unpack_archive(path_file[0] + "/" + path_file[1], directory)
        # Read variables dictionary, hardware specification and workflow specification from file
        workflow_specification = WorkflowSpecification.new_from_open_file(
            open(directory + "/workflow.desc", "r")
        )
        # Configuring logger
        hardware_specification = SimulationPanel.__new_hardware_map_from_open_file(
            open(directory + "/hardware.desc", "r")
        )
        # Setting up logger
        logging_cfg = LoggingConf()
        logging_cfg.log_dest = "STDOUT"
        logging_cfg.level = logging.INFO
        _configure_logging(logging_cfg)
        # Running the monitor
        self._monitor = Monitor(workflow_specification, hardware_specification)
        # Create a new thread to read from the pipe
        event_report_file = open(self.event_report_file_path_field.Value, "r")
        try:
            self.__process_thread = threading.Thread(
                target=self._monitor.run, args=[event_report_file]
            )
        except AbortRun:
            logging.critical(f"Runtime monitoring process ABORTED.")

        self.__process_thread.start()

    def on_stop(self, event):
        pass

    def _set_up_components(self):
        self._set_up_log_file_selection_components()
        self._set_up_workflow_selection_components()
        self._set_up_simulation_status_components()
        self._add_dividing_line()
        self._set_up_action_components()

    def _add_dividing_line(self):
        self.main_sizer.Add(wx.StaticLine(self), 0, wx.EXPAND)

    def _set_up_log_file_selection_components(self):
        action_label = "Seleccionar archivo de eventos a reportar:"
        action = self.select_report
        self.event_report_file_path_field = wx.TextCtrl(self, -1, "", size=(600, 33))

        self._set_up_file_selection_components_with(
            action, action_label, self.event_report_file_path_field
        )

    def _set_up_workflow_selection_components(self):
        action_label = "Seleccionar archivo de especificación del framework:"
        action = self.select_specification
        self.framework_specification_file_path_field = wx.TextCtrl(
            self, -1, "", size=(600, 33)
        )

        self._set_up_file_selection_components_with(
            action, action_label, self.framework_specification_file_path_field
        )

    def _set_up_file_selection_components_with(self, action, action_label, text_field):
        action_label_component = wx.StaticText(
            self, label=action_label, style=wx.ALIGN_CENTRE
        )
        self.main_sizer.Add(
            action_label_component, 0, wx.EXPAND | wx.ALL, border=10
        )

        folder_icon = wx.ArtProvider.GetBitmap(wx.ART_FOLDER, wx.ART_OTHER, (16, 16))
        folder_selection_button = wx.BitmapButton(self, bitmap=folder_icon)
        folder_selection_button.Bind(wx.EVT_BUTTON, action)

        folder_selection_sizer = wx.BoxSizer(wx.HORIZONTAL)
        folder_selection_sizer.Add(text_field, 0, wx.ALL, border=10)
        folder_selection_sizer.Add(folder_selection_button, 0, wx.ALL, border=10)

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
        start_button = wx.Button(self, label="Start")
        start_button.Bind(wx.EVT_BUTTON, self.on_start)

        stop_button = wx.Button(self, label="Stop")
        stop_button.Bind(wx.EVT_BUTTON, self.on_stop)

        action_buttons_sizer = wx.BoxSizer(wx.HORIZONTAL)
        action_buttons_sizer.Add(start_button, 0, wx.ALL, border=10)
        action_buttons_sizer.Add(stop_button, 0, wx.ALL, border=10)

        self.main_sizer.Add(action_buttons_sizer, 0, wx.CENTER)

    def _simulation_status_label(self):
        return f"Cantidad de eventos a verificar: {self.total_events_count}\n"


if __name__ == "__main__":
    app = wx.App()
    mainWindow = MainWindow()
    app.MainLoop()
