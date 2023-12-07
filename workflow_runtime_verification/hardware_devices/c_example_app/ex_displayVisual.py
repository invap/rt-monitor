import wx


class ex_displayVisual(wx.Frame):
    def __init__(self, parent, display):
        super().__init__(
            None,
            title="Component: SSD1963 Display",
            style=wx.CAPTION | wx.RESIZE_BORDER,
        )  # TODO take some name of the component
        # self.Bind(wx.EVT_CLOSE, ignore_event)
        self.display = display
        # Create a scrolled window
        #        self.visual_lcd = wx.ScrolledWindow(self, style=wx.VSCROLL | wx.HSCROLL | wx.STAY_ON_TOP)
        self.visual_lcd = wx.Window(self, style=wx.STAY_ON_TOP)
        self.visual_lcd.SetVirtualSize((self.display.height, self.display.width))
        self.SetSize((self.display.height + 250, self.display.width))
        self.visual_lcd.Bind(wx.EVT_PAINT, self.on_paint)
        # Init timer to reload the data from Logic
        self.timer = wx.CallLater(50, self.on_timer)
        # show
        self.Show()

    def close(self):
        self.timer.Stop()
        self.Close(True)

    def force_refresh(self):
        self.on_paint()

    def on_timer(self):
        self.Refresh()
        self.Update()
        self.timer.Restart(50)

    def on_paint(self, event):
        dc = wx.PaintDC(self.visual_lcd)
        gc = wx.GraphicsContext.Create(dc)
        image = wx.Bitmap.FromBuffer(
            self.display.height, self.display.width, self.display.get_display_pixels()
        )
        width, height = image.GetSize()
        gc.DrawBitmap(image, 0, 0, width, height)
