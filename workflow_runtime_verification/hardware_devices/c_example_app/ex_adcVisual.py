import wx


class adcVisual(wx.Frame):
    def __init__(self, parent, adc_component):
        super().__init__(
            None, title="Component: ADC", style=wx.CAPTION | wx.RESIZE_BORDER
        )

        self.adc_component = adc_component
        self._render()

        self.timer = wx.CallLater(50, self.on_timer)
        self.Centre()
        self.Show()

    def close(self):
        self.timer.Stop()
        self.Close(True)

    def on_timer(self):
        self.counter_display_number.SetLabel(self._counter_value())
        self.measured_value_display.SetLabel(self._measured_value())
        self.measured_binary_value_display.SetLabel(self._measured_binary_value())

        self.Refresh()
        self.Update()

        self.timer.Restart(50)

    def _render(self):
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self._set_up_components()
        self.SetSizerAndFit(self.sizer)

    def _set_up_components(self):
        self._set_up_counter_display()
        self._set_up_value_display()
        self._set_up_binary_value_display()

    def _set_up_counter_display(self):
        counter_display_sizer = wx.BoxSizer(wx.HORIZONTAL)

        self.counter_display_label = wx.StaticText(self, label="Cantidad de lecturas: ")
        counter_display_sizer.Add(self.counter_display_label, 0, wx.ALL, border=10)

        self.counter_display_number = wx.StaticText(
            self, label=self._counter_value(), style=wx.ALIGN_RIGHT
        )
        self._set_up_display(self.counter_display_number, counter_display_sizer)

        self.sizer.Add(counter_display_sizer, 0, wx.CENTER)

    def _set_up_value_display(self):
        self.measured_value_display = wx.StaticText(
            self, label=self._measured_value(), style=wx.ALIGN_RIGHT
        )
        self._set_up_display(self.measured_value_display, self.sizer, self._blue())

    def _set_up_binary_value_display(self):
        self.measured_binary_value_display = wx.StaticText(
            self, label=self._measured_binary_value(), style=wx.ALIGN_RIGHT
        )
        self._set_up_display(self.measured_binary_value_display, self.sizer)

    def _set_up_display(self, display_text, sizer, foreground_color=None):
        if foreground_color is None:
            foreground_color = self._silver()

        font = wx.Font(
            18, wx.FONTFAMILY_TELETYPE, wx.FONTSTYLE_NORMAL, wx.FONTWEIGHT_NORMAL
        )
        display_text.SetFont(font)

        display_text.SetBackgroundColour(self._black())
        display_text.SetForegroundColour(foreground_color)

        maximum_digits = 10
        minimum_counter_display_size = wx.Size(
            font.GetPixelSize().GetWidth() * maximum_digits, -1
        )
        display_text.SetMinSize(minimum_counter_display_size)

        sizer.Add(display_text, 0, wx.ALL, border=10)

    def _counter_value(self):
        return str(self.adc_component.get_status()[0])

    def _measured_value(self):
        return str(self.adc_component.get_status()[1])

    def _measured_binary_value(self):
        return str(bin(self.adc_component.get_status()[1]))[2:]

    def _silver(self):
        return wx.Colour(128, 128, 128)

    def _blue(self):
        return wx.Colour(64, 224, 208)

    def _black(self):
        return wx.Colour(0, 0, 0)
