# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import wx

from rt_monitor.gui.logging_configuration_panel import LoggingConfigurationPanel
from rt_monitor.gui.monitor_configuration_panel import MonitorConfigurationPanel
from rt_monitor.gui.monitoring_panel import MonitoringPanel


class MainWindow(wx.Frame):
    def __init__(self):
        super().__init__(
            parent=None,
            title="Runtime Monitor",
            style=wx.DEFAULT_FRAME_STYLE & ~wx.MAXIMIZE_BOX & ~wx.RESIZE_BORDER
        )
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
        was_vetoed = self.control_panel.close(event)
        if not was_vetoed:
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

    def close(self, event):
        was_vetoed = self.monitoring_panel.close(event)
        return was_vetoed

    def logging_destination(self):
        return self.logging_configuration_panel.logging_destination()

    def logging_verbosity(self):
        return self.logging_configuration_panel.logging_verbosity()

    def disable_logging_configuration_components(self):
        self.logging_configuration_panel.Disable()

    def enable_logging_configuration_components(self):
        self.logging_configuration_panel.Enable()
