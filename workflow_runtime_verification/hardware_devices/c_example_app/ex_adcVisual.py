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
        self.value_display.SetValue(self._value_display_label())

        self.Refresh()
        self.Update()

        self.timer.Restart(50)

    def _render(self):
        self.sizer = wx.BoxSizer(wx.VERTICAL)
        self._set_up_components()
        self.SetSizer(self.sizer)

    def _set_up_components(self):
        self._set_up_counter_display()
        self._set_up_value_display()

    def _set_up_counter_display(self):
        self.counter_display_label = wx.StaticText(self, label="Cantidad de lecturas: ")
        self.counter_display_number = wx.StaticText(self, label=self._counter_value())

        counter_display_sizer = wx.BoxSizer(wx.HORIZONTAL)
        counter_display_sizer.Add(self.counter_display_label, 0, wx.ALL, border=10)
        counter_display_sizer.Add(self.counter_display_number, 0, wx.ALL, border=10)

        self.sizer.Add(counter_display_sizer, 0, wx.CENTER)

    def _set_up_value_display(self):
        self.value_display = wx.TextCtrl(self, -1, "", size=(600, -1))
        self.value_display.SetValue("Valor actual: -")
        self.sizer.Add(self.value_display, 0, wx.EXPAND, 5)

    def _counter_value(self):
        return str({self.adc_component.get_status()[0]})

    def _value_display_label(self):
        return (
            f"Valor actual: {self.adc_component.get_status()[1]} "
            f"<<== [{str(bin(self.adc_component.get_status()[1]))[2:]}]"
        )
