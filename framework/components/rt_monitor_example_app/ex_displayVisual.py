# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

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
        self.Hide()

    def on_timer(self):
        self.Refresh()
        self.Update()
        self.timer.Restart()

    def on_paint(self, event):
        dc = wx.PaintDC(self.visual_lcd)
        gc = wx.GraphicsContext.Create(dc)
        image = wx.Bitmap.FromBuffer(
            self.display.height, self.display.width, self.display.get_display_pixels()
        )
        width, height = image.GetSize()
        gc.DrawBitmap(image, 0, 0, width, height)
