import wx


class displayVisual(wx.Frame):
    def __init__(self, parent, display):
        super().__init__(
            None,
            title="Display",
            style=wx.CAPTION | wx.RESIZE_BORDER,
        )

        self.display = display

        self.visual_lcd = wx.Window(self)
        self.SetClientSize((self.display.height, self.display.width))
        self.visual_lcd.Bind(wx.EVT_PAINT, self.on_paint)

        self.timer = wx.CallLater(50, self.on_timer)
        self.Show()

    def close(self):
        self.timer.Stop()
        self.Destroy()

    def on_timer(self):
        if not self.timer.IsRunning():
            return

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