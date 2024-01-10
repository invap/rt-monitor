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
        self.logging_configuration_panel = LoggingConfigurationPanel(parent=self)
        self.simulation_panel.SetFocus()

        self.AddPage(self.simulation_panel, "Simulación")
        self.AddPage(self.logging_configuration_panel, "Configuración del log")

    def close(self):
        self.simulation_panel.close()

    def logging_destination(self):
        return self.logging_configuration_panel.logging_destination()

    def logging_verbosity(self):
        return self.logging_configuration_panel.logging_verbosity()

    def disable_logging_configuration_components(self):
        self.logging_configuration_panel.Disable()

    def enable_logging_configuration_components(self):
        self.logging_configuration_panel.Enable()


# noinspection PyPropertyAccess
class SimulationPanel(wx.Panel):
    def __init__(self, parent):
        super().__init__(parent=parent)

        self._verification = None
        self._amount_of_events_to_verify = 0
        self._amount_of_processed_events = 0
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
            self._update_amount_of_events_to_verify()
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

    def on_start(self, _event):
        specification_path = self.framework_specification_file_path_field.Value
        event_report_path = self.event_report_file_path_field.Value

        self._verification = Verification.new_for_workflow_in_file(specification_path)
        self._verification.run_for_report(
            event_report_path,
            self.Parent.logging_destination(),
            self.Parent.logging_verbosity(),
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
        if self._verification is not None:
            self._verification.stop_hardware_simulation()

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

    def update_amount_of_processed_events(self):
        self._amount_of_processed_events += 1
        self.amount_of_processed_events_text_label.SetLabel(
            self._amount_of_processed_events_label()
        )
        self._progress_bar.SetValue(self._amount_of_processed_events)

    def _update_amount_of_events_to_verify(self):
        with open(self.event_report_file_path_field.Value, "r") as file:
            self._amount_of_events_to_verify = len(file.readlines())
            file.close()
        self.amount_of_events_to_verify_text_label.SetLabel(
            self._amount_of_events_to_verify_label()
        )
        self._progress_bar.SetRange(self._amount_of_events_to_verify)

    def _stop_verification(self):
        self._disable_stop_button()

        self._stop_event.set()

    def _render(self):
        self.main_sizer = wx.BoxSizer(wx.VERTICAL)
        self._set_up_components()
        self.SetSizer(self.main_sizer)

    def _set_up_components(self):
        self._set_up_log_file_selection_components()
        self._set_up_workflow_selection_components()
        self._add_dividing_line()
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
        simulation_status_label = wx.StaticText(self, label="Estado de la simulación")
        self.amount_of_events_to_verify_text_label = wx.StaticText(
            self, label=self._amount_of_events_to_verify_label()
        )
        self.amount_of_processed_events_text_label = wx.StaticText(
            self, label=self._amount_of_processed_events_label()
        )

        self._percentage_of_processed_events_text = wx.StaticText(
            self, label=self._percentage_of_processed_events_label()
        )
        self._progress_bar = wx.Gauge(self, range=self._amount_of_events_to_verify)
        progress_bar_sizer = wx.BoxSizer(wx.HORIZONTAL)
        progress_bar_sizer.Add(self._progress_bar, 1, wx.ALIGN_CENTER_VERTICAL)
        progress_bar_sizer.Add(
            self._percentage_of_processed_events_text,
            0,
            wx.ALIGN_CENTER_VERTICAL | wx.LEFT,
            border=10,
        )

        self.main_sizer.Add(simulation_status_label, 0, wx.TOP | wx.LEFT, border=15)
        self.main_sizer.Add(
            self.amount_of_events_to_verify_text_label,
            0,
            wx.EXPAND | wx.TOP | wx.LEFT,
            border=25,
        )
        self.main_sizer.Add(
            self.amount_of_processed_events_text_label,
            0,
            wx.EXPAND | wx.LEFT,
            border=25,
        )
        self.main_sizer.Add(
            progress_bar_sizer, 0, wx.EXPAND | wx.LEFT | wx.RIGHT | wx.BOTTOM, border=25
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

    def _amount_of_events_to_verify_label(self):
        return f"Eventos a verificar: {self._amount_of_events_to_verify}\n"

    def _amount_of_processed_events_label(self):
        return f"Eventos procesados: {self._amount_of_processed_events}\n"

    def _percentage_of_processed_events_label(self):
        if self._amount_of_events_to_verify == 0:
            percentage = 0
        else:
            percentage = (
                self._amount_of_processed_events / self._amount_of_events_to_verify
            ) * 100

        return f"{int(percentage)}%"

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
            self, label="Configurar el registro de información en el log"
        )
        self.sizer.Add(
            logging_configuration_label_component, 0, wx.LEFT | wx.TOP, border=15
        )
        self.sizer.AddStretchSpacer()
        self._set_up_logging_verbosity_configuration_components()
        self._set_up_logging_destination_configuration_components()
        self.sizer.AddStretchSpacer()

    def _set_up_logging_verbosity_configuration_components(self):
        label = wx.StaticText(self, label="Tipo de información a registrar:")

        self._logging_verbosity_selector = wx.Choice(
            self, choices=self._logging_verbosity_options(), size=(200, 35)
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
        label = wx.StaticText(self, label="Dónde registrar la información:")

        self._logging_destination_selector = wx.Choice(
            self, choices=self._logging_destination_options(), size=(200, 35)
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
        default_selection_index = 0
        selector.SetSelection(default_selection_index)
        self._logging_destination = selector.GetString(default_selection_index)

    def _select_logging_destination(self, event):
        self._logging_destination = event.GetString()

    def _logging_destination_options(self):
        return LoggingDestination.all()

    def _add_horizontal_stretching_space(self, sizer):
        sizer.Add((0, 0), 1, wx.EXPAND | wx.ALL)

    def logging_destination(self):
        return self._logging_destination

    def logging_verbosity(self):
        return self._logging_verbosity


if __name__ == "__main__":
    app = wx.App()
    mainWindow = MainWindow()
    app.MainLoop()
