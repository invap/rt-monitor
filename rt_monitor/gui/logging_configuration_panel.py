# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import wx

from logging_configuration import LoggingLevel, LoggingDestination


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
            "Analysis related entries": LoggingLevel.ANALYSIS,
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
