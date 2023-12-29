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
        # Creamos un divisor para dividir la ventana en dos partes
        # splitter = wx.SplitterWindow(self, -1, style=wx.SP_3DSASH)

        # Creamos un notebook con 3 páginas
        self.control_panel = ControlPanel(parent=self)

        # Agregamos los paneles al sizer principal
        self.main_sizer = wx.BoxSizer(wx.VERTICAL)
        self.main_sizer.Add((20, 20))
        self.main_sizer.Add(self.control_panel, 1, wx.EXPAND)

        # Establecemos el tamaño de la ventana y la mostramos
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

        self.setup_reporter_panel = SimulationPanel(parent=self)
        self.AddPage(self.setup_reporter_panel, "Run-time monitor setup")


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
            self.text_report_events.SetValue(dialog.GetPath())
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
            self.framework_specification_text.SetValue(dialog.GetPath())
        dialog.Destroy()

    def update_report_properties(self):
        with open(self.text_report_events.Value, "r") as f:
            self.total_events_count = sum(1 for _ in f)
            f.close()
        self.text_status.SetValue(
            f"Cant. Total de eventos a verificar: {self.total_events_count}\n"
        )
        self.text_report_events.Refresh()

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
        path_file = os.path.split(self.framework_specification_text.Value)
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
        event_report_file = open(self.text_report_events.Value, "r")
        try:
            self.__process_thread = threading.Thread(
                target=self._monitor.run, args=[event_report_file]
            )
        except AbortRun:
            logging.critical(f"Runtime monitoring process ABORTED.")

        # Create a flag to stop and pause the process
        self.__stop_event = threading.Event()
        self.__delay = 0
        self.__process_thread.start()

    def on_stop(self, event):
        pass

    def _set_up_components(self):
        self._set_up_log_file_selection_components()
        self._set_up_workflow_selection_components()
        self._set_up_simulation_status_components()
        self._set_up_action_components()

    def _set_up_log_file_selection_components(self):
        self.button_Obj = wx.Button(
            self, label="Seleccionar archivo de eventos a reportar:"
        )
        self.button_Obj.Bind(wx.EVT_BUTTON, self.select_report)
        self.text_report_events = wx.TextCtrl(self, -1, "", size=(600, -1))
        self.main_sizer.Add(self.button_Obj, 0, wx.ALL, border=10)
        self.main_sizer.Add(self.text_report_events, 0, wx.ALL, border=10)

    def _set_up_workflow_selection_components(self):
        self.select_specification_button = wx.Button(
            self, label="Seleccionar archivo de especificación del framework:"
        )
        self.select_specification_button.Bind(wx.EVT_BUTTON, self.select_specification)
        self.framework_specification_text = wx.TextCtrl(self, -1, "", size=(600, -1))
        self.main_sizer.Add(self.select_specification_button, 0, wx.ALL, border=10)
        self.main_sizer.Add(self.framework_specification_text, 0, wx.ALL, border=10)

    def _set_up_simulation_status_components(self):
        self.Value_status_title = wx.StaticText(self, label="Estado de la simulación:")
        self.main_sizer.Add(self.Value_status_title, 0, wx.ALL, border=10)
        self.total_events_count = 0
        self.text_status = wx.TextCtrl(self, -1, "", size=(600, -1))
        self.main_sizer.Add(self.text_status, 0, wx.ALL, border=10)
        self.panel_actividad = wx.Panel(self)
        self.main_sizer.Add(self.panel_actividad)

    def _set_up_action_components(self):
        self.main_sizer.Add(wx.StaticLine(self), 0, wx.EXPAND | wx.TOP | wx.BOTTOM,
                            border=10)
        self.play_button = wx.Button(self, label="Start")
        self.stop_button = wx.Button(self, label="Stop")
        self.play_button.Bind(wx.EVT_BUTTON, self.on_start)
        self.stop_button.Bind(wx.EVT_BUTTON, self.on_stop)
        self.run_ctrl_sizer = wx.BoxSizer(wx.HORIZONTAL)
        self.run_ctrl_sizer.Add(self.play_button, 0, wx.BOTTOM | wx.RIGHT | wx.LEFT,
                                border=10)
        self.run_ctrl_sizer.Add(self.stop_button, 0, wx.BOTTOM | wx.RIGHT | wx.LEFT,
                                border=10)
        self.main_sizer.Add(self.run_ctrl_sizer, 0, wx.CENTER)


if __name__ == "__main__":
    app = wx.App()
    mainWindow = MainWindow()
    app.MainLoop()
