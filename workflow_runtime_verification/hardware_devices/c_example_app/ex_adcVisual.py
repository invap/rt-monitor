import wx


class adcVisual(wx.Frame):
    def __init__(self, parent, adc_comp):
        super().__init__(
            None, title="Component: ADC", style=wx.CAPTION | wx.RESIZE_BORDER
        )  # TODO take some name of the component
        # self.Bind(wx.EVT_CLOSE, ignore_event)
        self.adc_comp = adc_comp
        # Crear ventanita capaz de mostrar un int y la tira de bits
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
        self.status_text.SetLabel(
            f"Cant. Total de lecturas: {self.adc_comp.get_status()[0]}\n"
            + f"Valor actual: {self.adc_comp.get_status()[1]} <<== [{str(bin(self.adc_comp.get_status()[1]))[2:]}]\n"
        )
        self.status_text.Refresh()
        self.Refresh()
        self.Update()
        self.timer.Restart(50)
