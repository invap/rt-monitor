# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import wx


class MonitorConfigurationPanel(wx.Panel):
    def __init__(self, parent):
        super().__init__(parent=parent)
        self.framework_chosen = False
        self.event_report_file_chosen = False
        self.framework_dir = ""
        self._render()

    def select_framework(self, event):
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
            self.framework_file_path_field.SetValue(dialog.GetPath())
            self.framework_chosen = True
            wx.CallAfter(self.report_list_folder_button.Enable)
        dialog.Destroy()

    def select_report(self, event):
        # Open Dialog
        dialog = wx.FileDialog(
            self,
            "Select event report list file",
            "",
            "",
            "All files (*.*)|*.*",
            wx.FD_OPEN | wx.FD_FILE_MUST_EXIST,
        )
        if dialog.ShowModal() == wx.ID_OK:
            self.report_list_file_path_field.SetValue(dialog.GetPath())
            self.event_report_file_chosen = True
            self.Parent.monitoring_panel.show_multi_action_button_as_start()
        dialog.Destroy()

    def _set_up_framework_selection_components(self):
        action_label = "Select analysis framework file (.toml):"
        action = self.select_framework
        self.framework_file_path_field = wx.TextCtrl(
            self, -1, "", size=(600, 33), style=wx.TE_READONLY
        )
        action_label_component = wx.StaticText(self, label=action_label)
        self.main_sizer.Add(action_label_component, 0, wx.LEFT | wx.TOP, border=15)

        folder_icon = wx.ArtProvider.GetBitmap(wx.ART_FOLDER, wx.ART_OTHER, (16, 16))
        folder_selection_button = wx.BitmapButton(self, bitmap=folder_icon)
        folder_selection_button.Bind(wx.EVT_BUTTON, action)

        folder_selection_sizer = wx.BoxSizer(wx.HORIZONTAL)
        folder_selection_sizer.Add(self.framework_file_path_field, 0, wx.ALL, border=10)
        folder_selection_sizer.Add(
            folder_selection_button, 0, wx.TOP | wx.BOTTOM | wx.RIGHT, border=10
        )
        self.main_sizer.Add(folder_selection_sizer, 0)

    def _set_up_reports_file_selection_components(self):
        action_label = "Select event report list file (.txt):"
        action = self.select_report
        self.report_list_file_path_field = wx.TextCtrl(
            self, -1, "", size=(600, 33), style=wx.TE_READONLY
        )
        action_label_component = wx.StaticText(self, label=action_label)
        self.main_sizer.Add(action_label_component, 0, wx.LEFT | wx.TOP, border=15)

        folder_icon = wx.ArtProvider.GetBitmap(wx.ART_FOLDER, wx.ART_OTHER, (16, 16))
        folder_selection_button = wx.BitmapButton(self, bitmap=folder_icon)
        folder_selection_button.Bind(wx.EVT_BUTTON, action)
        self.report_list_folder_button = folder_selection_button
        wx.CallAfter(self.report_list_folder_button.Disable)

        folder_selection_sizer = wx.BoxSizer(wx.HORIZONTAL)
        folder_selection_sizer.Add(self.report_list_file_path_field, 0, wx.ALL, border=10)
        folder_selection_sizer.Add(
            folder_selection_button, 0, wx.TOP | wx.BOTTOM | wx.RIGHT, border=10
        )
        self.main_sizer.Add(folder_selection_sizer, 0)

    def _add_dividing_line(self):
        self.main_sizer.Add(wx.StaticLine(self), 0, wx.EXPAND)

    def _set_up_components(self):
        self._set_up_framework_selection_components()
        self._add_dividing_line()
        self._set_up_reports_file_selection_components()

    def _render(self):
        self.main_sizer = wx.BoxSizer(wx.VERTICAL)
        self._set_up_components()
        self.SetSizer(self.main_sizer)
