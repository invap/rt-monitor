import wx


class adcVisual(wx.Frame):
    def __init__(self, parent, adc_component):
        super().__init__(
            None, title="Component: ADC", style=wx.CAPTION | wx.RESIZE_BORDER
        )

        self.adc_component = adc_component

        self.status_text = wx.TextCtrl(self, -1, "", size=(600, -1))
        self.sizer = wx.BoxSizer(wx.HORIZONTAL)
        self.sizer.Add(self.status_text)
        self.Centre()
        self.status_text.SetLabel("Iniciando...")
        # Init timer to reload the data from Logic
        self.timer = wx.CallLater(50, self.on_timer)

        # show
        self.Show()

    def close(self):
        self.timer.Stop()
        self.Close(True)

    def on_timer(self):
        # update values
        self.status_text.SetValue(
            f"Cant. Total de lecturas: {self.adc_component.get_status()[0]}\n"
            + f"Valor actual: {self.adc_component.get_status()[1]} <<== [{str(bin(self.adc_component.get_status()[1]))[2:]}]\n"
        )
        self.status_text.Refresh()
        self.Refresh()
        self.Update()
        self.timer.Restart(50)
