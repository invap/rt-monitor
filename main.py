import logging
import threading

import wx

from logging_configuration import LoggingLevel, LoggingDestination
from verification import Verification


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


# noinspection PyPropertyAccess
class SimulationPanel(wx.Panel):
    def __init__(self, parent):
        super().__init__(parent=parent)

        self._verification = None
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
        specification_path = self.framework_specification_file_path_field.Value
        event_report_path = self.event_report_file_path_field.Value

        self._verification = Verification.new_for_workflow_in_file(specification_path)

        self._verification.run_for_report(
            event_report_path,
            self._logging_destination,
            self._logging_verbosity,
            self._pause_event,
            self._stop_event,
            self,
        )

    def on_stop(self, _event):
        logging.warning(
            "Verification is gracefully stopping in the background. "
            "It will stop when it finishes processing the current event."
        )
        self._stop_verification()

    def on_pause(self, _event):
        self._pause_event.set()
        logging.warning(
            "Verification will be paused when it finishes processing "
            "the current event."
        )
        self._show_multi_action_button_as_play()

    def on_play(self, _event):
        self._show_multi_action_button_as_pause()
        logging.warning("Verification resumed.")
        self._pause_event.clear()

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
                    "the last one is finished."
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

    def _stop_verification(self):
        self._disable_stop_button()

        if self._verification is not None:
            self._verification.stop_hardware_simulation()

        self._stop_event.set()

    def _render(self):
        self.main_sizer = wx.BoxSizer(wx.VERTICAL)
        self._set_up_components()
        self.SetSizer(self.main_sizer)

    def _set_up_components(self):
        self._set_up_log_file_selection_components()
        self._set_up_workflow_selection_components()
        self._set_up_simulation_status_components()
        self._add_dividing_line()
        self._set_up_logging_configuration_components()
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

    def _set_up_logging_configuration_components(self):
        logging_configuration_label_component = wx.StaticText(
            self, label="Configurar el registro de información en el log"
        )
        self.main_sizer.Add(
            logging_configuration_label_component, 0, wx.LEFT | wx.TOP, border=15
        )

        self._set_up_logging_verbosity_configuration_components()
        self._set_up_logging_destination_configuration_components()

    def _set_up_logging_verbosity_configuration_components(self):
        label = wx.StaticText(self, label="Tipo de información a registrar:")

        self._logging_verbosity_selector = wx.Choice(
            self, choices=self._logging_verbosity_options(), size=(200, 35)
        )
        self._logging_verbosity_selector.Bind(wx.EVT_CHOICE, self._select_logging_verbosity)
        self._select_default_logging_verbosity(self._logging_verbosity_selector)

        logging_verbosity_selection_sizer = wx.BoxSizer(wx.HORIZONTAL)
        self._add_horizontal_stretching_space(logging_verbosity_selection_sizer)
        logging_verbosity_selection_sizer.Add(
            label, 0, wx.TOP | wx.LEFT | wx.ALIGN_CENTER_VERTICAL, border=15
        )
        logging_verbosity_selection_sizer.Add(
            self._logging_verbosity_selector, 0, wx.TOP | wx.LEFT | wx.RIGHT, border=15
        )

        self.main_sizer.Add(logging_verbosity_selection_sizer, 0, wx.EXPAND)

    def _set_up_logging_destination_configuration_components(self):
        label = wx.StaticText(self, label="Dónde registrar la información:")

        self._logging_destination_selector = wx.Choice(
            self, choices=self._logging_destination_options(), size=(200, 35)
        )
        self._logging_destination_selector.Bind(wx.EVT_CHOICE, self._select_logging_destination)
        self._select_default_logging_destination(self._logging_destination_selector)

        logging_destination_selection_sizer = wx.BoxSizer(wx.HORIZONTAL)
        self._add_horizontal_stretching_space(logging_destination_selection_sizer)
        logging_destination_selection_sizer.Add(
            label, 0, wx.TOP | wx.BOTTOM | wx.LEFT | wx.ALIGN_CENTER_VERTICAL, border=15
        )
        logging_destination_selection_sizer.Add(self._logging_destination_selector, 0, wx.ALL, border=15)

        self.main_sizer.Add(logging_destination_selection_sizer, 0, wx.EXPAND)

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

    def _disable_logging_configuration_components(self):
        self._logging_verbosity_selector.Disable()
        self._logging_destination_selector.Disable()

    def _enable_logging_configuration_components(self):
        self._logging_verbosity_selector.Enable()
        self._logging_destination_selector.Enable()

    def _refresh_window_layout(self):
        self.main_sizer.Layout()

    def _select_default_logging_verbosity(self, selector):
        selector.SetSelection(0)
        self._logging_verbosity = self._logging_verbosity_from_text(
            selector.GetString(0)
        )

    def _select_logging_verbosity(self, event):
        selected_option = event.GetString()
        self._logging_verbosity = self._logging_verbosity_from_text(selected_option)

    def _logging_verbosity_from_text(self, selected_option):
        return self._text_to_logging_verbosity_map()[selected_option]

    def _text_to_logging_verbosity_map(self):
        return {
            "Todo": LoggingLevel.INFO,
            "Información de análisis": LoggingLevel.PROPERTY_ANALYSIS,
            "Errores y advertencias": LoggingLevel.WARNING,
            "Errores": LoggingLevel.ERROR,
        }

    def _logging_verbosity_options(self):
        return list(self._text_to_logging_verbosity_map().keys())

    def _select_default_logging_destination(self, selector):
        selector.SetSelection(0)
        self._logging_destination = selector.GetString(0)

    def _select_logging_destination(self, event):
        self._logging_destination = event.GetString()

    def _logging_destination_options(self):
        return LoggingDestination.all()

    def _add_horizontal_stretching_space(self, sizer):
        sizer.Add((0, 0), 1, wx.EXPAND | wx.ALL)


if __name__ == "__main__":
    app = wx.App()
    mainWindow = MainWindow()
    app.MainLoop()
