# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import inspect
import threading
from enum import Enum

import numpy as np

from errors.component_errors import FunctionNotImplementedError
from framework.components.component import Component
from framework.components.rt_monitor_example_app import (
    ex_displayVisual,
)


class LCDCmdsCodes:
    """command's codes for display"""

    NO_OPERATION: np.uint8 = 0x00
    SET_COLUMN_ADDRESS: np.uint8 = 0x2A
    SET_PAGE_ADDRESS: np.uint8 = 0x2B
    WRITE_MEMORY_START: np.uint8 = 0x2C
    CURSOR_DIRECTION: np.uint8 = 0x36


class CursorDirection(Enum):
    """
    different writing cursor directions,
    the possibilities are, Vertical (row/page) first and then Horizontal (col) or vice versa
    then the possibility of each of them, i.e: incremental or decremental
    Vertical incremental: TopDown (T) (row/page++), Vertical decremental: DownTop (D) (row/page--)
    Horizontal incremental: LeftRight (L) (col++), Horizontal decremental: RightLeft (R) (col--)
    first (?_): inner movement, second(_?): outer movement, example: TR (TopDown first, RightLeft second)
    ---------
    in display after command 0x36, the positions [B7,B6,B5,B4,B3,B2,B1,B0]
    means: B5 (0:horiz first 1:vert first) B6(0: Horiz++,1 Horiz--) B7(0: Vert++,1 Vert--)
    example 0x60 means [0,1,1,0,_,_,_,_] TR, that is  row/page++ then col--
    """

    LT = 0
    LD = 1
    RT = 2
    RD = 3
    TR = 4
    TL = 5
    DR = 6
    DL = 7


class PixelGamma(Enum):
    R = 0
    G = 1
    B = 2


class Color:
    def __init__(self, r, g, b: int):
        self.r = r
        self.g = g
        self.b = b


class TextConfiguration:
    def __init__(
        self,
        origin_x: np.uint16,
        height: np.uint16,
        width: np.uint16,
        height2: np.uint16,
        width2: np.uint16,
        color,
        bgcolor: Color,
        scale: int,
    ):
        # Text character sizes by default (defined as constant in driver)
        self.char_width = 6  # related to font spec matrix
        self.char_height = 8  # related to font spec matrix
        # text properties
        self.bgcolor = bgcolor
        self.color = color
        self.width2 = width2
        self.height2 = height2
        self.height = height
        self.width = width
        self.origin_x = origin_x
        self.scale = scale

    def set_bgcolor_RGB(self, r, g, b: int):
        self.bgcolor.r = r
        self.bgcolor.g = g
        self.bgcolor.b = b

    def set_color_RGB(self, r, g, b: int):
        self.color.r = r
        self.color.g = g
        self.color.b = b


"""   uint16_t origin_x; /**< Horizontal position in pixels */
      uint16_t HEIGHT;       /**< Vertical position in pixels */
      uint16_t WIDTH;       /**< Horizontal position in pixels */
      uint16_t HEIGHT2;       /**< Vertical position in pixels */
      uint16_t WIDTH2;       /**< Horizontal position in pixels */
      rgb color;     /**< Text foreground color */
      rgb bgcolor;   /**< Text background color */
      uint8_t scale;    /**< Text scale */   """


class display(Component):
    def __init__(self, visual):
        # TODO driver must have the base configuration of the display, such as the commands codes, etc.
        # in this prototype we assume the display configuration
        # set the default width and height of the display, note that some drivers can update the size with the
        # respective command
        super().__init__(visual)
        self.width = 480
        self.height = 200
        # create and initialize the display's information with (0,0,0) RGB
        self.__display_pixels = np.zeros((self.width, self.height, 3), dtype=np.uint8)
        # create the lock to get exclusive access when publish or update the display
        self.__display_lock = threading.Lock()
        # initialization of status variables which coordinates the displaying process
        # - Current index position Start and EndColum, Start and End Pages(rows).
        #   INV => (startCol <= endCol and startPage <= endPage)
        self.__start_col: np.uint16 = np.uint16(0)
        self.__start_page: np.uint16 = np.uint16(0)
        self.__end_col: np.uint16 = np.uint16(0)
        self.__end_page: np.uint16 = np.uint16(0)
        # - Current pixel
        self.__current_col: np.uint16 = np.uint16(0)
        self.__current_page: np.uint16 = np.uint16(0)
        # - Current cursor direction
        self.__current_cursor_direction = CursorDirection.TR
        # - Current lcd mode
        self.__lcd_mode_status: np.uint8 = LCDCmdsCodes.NO_OPERATION
        # - current byte number (to count the partial reception)
        self.__current_byte = 0
        # - total expected and reached bytes for the current command in execution
        self.__bytes_expected = 0
        self.__bytes_reached = 0
        # - Current Text configuration (Driver)
        self.__text_conf = TextConfiguration(
            np.uint16(0),
            np.uint16(0),
            np.uint16(0),
            np.uint16(0),
            np.uint16(0),
            Color(255, 255, 255),
            Color(0, 0, 0),
            1,
        )
        # - Default Font Matrix Map 6_8
        self.__font_matrix = Font6_8()
        if self._visual:
            # create the visualization features associated
            self.__visualDisplay = ex_displayVisual.displayVisual(parent=self, display=self)
            self.__visualDisplay.Show()

    def stop(self):
        if self._visual:
            # closes the visualization features associated
            self.__visualDisplay.close()

    def state(self):
        """state.__display_pixels is a 3d (heigth, width, 3) matrix where the last axis
        is interpreted 0 = red (R), 1 = green (G) and 2 = blue (B)"""
        state = {
            "height": ("Int", self.height),
            "width": ("Int", self.width),
            "pixels": ("(Array Int (Array Int (Array Int Int)))", self.__display_pixels)
        }
        return state

    def __set_pixel_pos_gamma(
        self, w: int, h: int, px_gamma: PixelGamma, value: np.uint8
    ):
        """Set the display at position (w,h) the value of the gamma px_gamma (R=0,G=1,B=2)"""
        self.__display_pixels[w, h, px_gamma.value] = value

    def get_display_pixels(self):
        # lock the display publish and then unlock it
        self.__display_lock.acquire()
        try:
            temp_display = self.__display_pixels
        finally:
            self.__display_lock.release()
        return temp_display

    def __process_lcd_write_command(self, cmd: np.uint8):
        """
        Regarding the command code received, set the lcd_mode and the bytes to be expected for each command
        """
        self.__lcd_mode_status = cmd
        match self.__lcd_mode_status:
            case LCDCmdsCodes.NO_OPERATION:
                # No information is expected
                self.__bytes_expected = 0
            case LCDCmdsCodes.SET_PAGE_ADDRESS:
                # WITH (2 x 16bit start and end columns' addresses)
                self.__bytes_expected = 4
                self.__bytes_reached = 0
                self.__current_byte = 1
            case LCDCmdsCodes.SET_COLUMN_ADDRESS:
                # HEIGHT (2 x 16bit start and end columns' addresses)
                self.__bytes_expected = 4
                self.__bytes_reached = 0
                self.__current_byte = 1
            case LCDCmdsCodes.WRITE_MEMORY_START:
                # calculate the area to write (stated by set_page and set_colum)
                # area * 3 (RGB)
                self.__bytes_expected = (
                    (self.__end_col - self.__start_col + 1)
                    * (self.__end_page - self.__start_page + 1)
                    * 3
                )
                self.__bytes_reached = 0
                self.__current_byte = 1

    def __process_lcd_write_data(self, data: np.uint8):
        """
        regarding the current LCD mode status which indicates to which command the data received belongs to,
        the corresponding data process is invoked
        """
        match self.__lcd_mode_status:
            case LCDCmdsCodes.NO_OPERATION:
                pass
            case LCDCmdsCodes.SET_COLUMN_ADDRESS:
                self.__process_column_address(data)
            case LCDCmdsCodes.SET_PAGE_ADDRESS:
                self.__process_page_address(data)
            case LCDCmdsCodes.WRITE_MEMORY_START:
                self.__process_write_memory(data)
            case _:
                pass

    def __process_page_address(self, data: np.uint8):
        """
        first two bytes for the start page, then the last two bytes are for the end page
        """
        match self.__current_byte:
            case 1:
                self.__start_page = data << 8  # shift the upper byte value
            case 2:
                self.__start_page += data  # add the lower byte value
            case 3:
                self.__end_page = data << 8  # shift the upper byte value
            case 4:
                self.__end_page += data  # add the lower byte value
        self.__current_byte += 1
        self.__bytes_reached += 1
        if self.__bytes_expected == self.__bytes_reached:
            # update the current page regarding the cursor direction
            match self.__current_cursor_direction:
                case CursorDirection.LT | CursorDirection.RT | CursorDirection.TR | CursorDirection.TL:
                    self.__current_page = self.__start_page
                case CursorDirection.LD | CursorDirection.RD | CursorDirection.DR | CursorDirection.DL:
                    self.__current_page = self.__end_page
        # TODO: call to some control status (END of incoming data)

    def __process_column_address(self, data: np.uint8):
        """
        first two bytes for the start column, then the last two bytes are for the end column
        """
        match self.__current_byte:
            case 1:
                self.__start_col = data << 8  # shift the upper byte value
            case 2:
                self.__start_col += data  # add the lower byte value
            case 3:
                self.__end_col = data << 8  # shift the upper byte value
            case 4:
                self.__end_col += data  # add the lower byte value
        self.__current_byte += 1
        self.__bytes_reached += 1
        if self.__bytes_expected == self.__bytes_reached:
            # update the current page regarding the cursor direction
            match self.__current_cursor_direction:
                case CursorDirection.LT | CursorDirection.LD | CursorDirection.DL | CursorDirection.TL:
                    self.__current_col = self.__start_col
                case CursorDirection.RD | CursorDirection.RT | CursorDirection.TR | CursorDirection.DR:
                    self.__current_col = self.__end_col
        # TODO: call to some control status (END of incoming data)

    def __process_write_memory(self, data: np.uint8):
        """
        precondition  startCol <= current_x< = startCol, startPag <= current_y< = startPag
        """
        # lock the display_pixel (avoiding partial lectures)
        if self.__current_byte == 1 and self.__bytes_reached == 0:
            self.__display_lock.acquire()
        # UPDATE the display. The gamma code match with the current_byte-1 0=R 1=G 2=B
        self.__set_pixel_pos_gamma(
            480 - 1 - self.__current_col,
            self.__current_page,
            PixelGamma(self.__current_byte - 1),
            data,
        )
        if self.__current_byte == 3:
            # if is the last byte update the cursor position and reset the current byte number
            self.__update_current_pos()
            self.__current_byte = 1
        else:
            # update the current by received
            self.__current_byte += 1
        # update the bytes reached
        self.__bytes_reached += 1
        if self.__bytes_reached == self.__bytes_expected:
            # End of write command, unlock the display_pixel TODO do something if want to check
            self.__display_lock.release()

    def __update_current_pos(self):
        """
        Process all combinations of cursor mode and the status of the regarding conditions of columns and pages
        """
        match self.__current_cursor_direction:
            case CursorDirection.LT:
                if self.__current_col < self.__end_col:
                    self.__current_col += 1
                else:
                    self.__current_col = self.__start_col
                    if self.__current_page < self.__end_page:
                        self.__current_page += 1
            case CursorDirection.LD:
                if self.__current_col > self.__start_col:
                    self.__current_col -= 1
                else:
                    self.__current_col = self.__end_col
                    if self.__current_page > self.__start_page:
                        self.__current_page -= 1
            case CursorDirection.RT:
                if self.__current_col > self.__start_col:
                    self.__current_col -= 1
                else:
                    self.__current_col = self.__end_col
                    if self.__current_page < self.__end_page:
                        self.__current_page += 1
            case CursorDirection.RD:
                if self.__current_col > self.__start_col:
                    self.__current_col -= 1
                else:
                    self.__current_col = self.__end_col
                    if self.__current_page > self.__start_page:
                        self.__current_page -= 1
            case CursorDirection.TR:
                if self.__current_page < self.__end_page:
                    self.__current_page += 1
                else:
                    self.__current_page = self.__start_page
                    if self.__current_col > self.__start_col:
                        self.__current_col -= 1
            case CursorDirection.TL:
                if self.__current_page < self.__end_page:
                    self.__current_page += 1
                else:
                    self.__current_page = self.__start_page
                    if self.__current_col < self.__end_col:
                        self.__current_col += 1
            case CursorDirection.DR:
                if self.__current_page > self.__start_page:
                    self.__current_page -= 1
                else:
                    self.__current_page = self.__end_page
                    if self.__current_col > self.__start_col:
                        self.__current_col -= 1
            case CursorDirection.DL:
                if self.__current_page > self.__start_page:
                    self.__current_page -= 1
                else:
                    self.__current_page = self.__end_page
                    if self.__current_col < self.__end_col:
                        self.__current_col += 1

    def __write_data(self, data: np.uint8):
        byte = data & 0x0000FF
        self.__process_lcd_write_data(byte)

    def __write_command(self, cmd: np.uint8):
        self.__process_lcd_write_command(cmd)

    def __display_ram_address(
        self, y0: np.uint16, y1: np.uint16, x0: np.uint16, x1: np.uint16
    ):
        """ "/* 1. Set Column Address */"""
        self.__write_command(np.uint8(0x2A))
        self.__write_data(y0 >> 8)
        self.__write_data(y0)
        self.__write_data(y1 >> 8)
        self.__write_data(y1)
        """"/* 1. Set Page Address */"""
        self.__write_command(np.uint8(0x2B))
        self.__write_data(x0 >> 8)
        self.__write_data(x0)
        self.__write_data(x1 >> 8)
        self.__write_data(x1)

    def display_set_text_color(self, r: int, g: int, b: int):
        self.__text_conf.color.r = r
        self.__text_conf.color.g = g
        self.__text_conf.color.b = b

    def display_set_text_bgcolor(self, r: int, g: int, b: int):
        self.__text_conf.bgcolor.r = r
        self.__text_conf.bgcolor.g = g
        self.__text_conf.bgcolor.b = b

    def display_set_text_scale(self, scale: int):
        self.__text_conf.scale = scale

    def display_set_text_pos(self, height: int, width: int):
        self.__text_conf.height = (
            height * self.__text_conf.char_height * self.__text_conf.scale
        )
        self.__text_conf.width = (
            width * self.__text_conf.char_width * self.__text_conf.scale
        )

    def display_set_text_pos2(self, height: int, width: int):
        self.__text_conf.height = height
        self.__text_conf.width = width + 68

    def display_show_rgb(
        self,
        r: np.uint8,
        g: np.uint8,
        b: np.uint8,
        height0: np.uint16,
        height1: np.uint16,
        width0: np.uint16,
        width1: np.uint16,
    ):
        self.__display_ram_address(height0, height1, width0, width1)
        self.__write_command(np.uint8(0x2C))
        for i in range(width1 - width0 + 1):
            for j in range(height1 - height0 + 1):
                self.__write_data(r)
                self.__write_data(g)
                self.__write_data(b)

    def display_rect(
        self,
        height: np.uint16,
        width: np.uint16,
        w: np.uint16,
        h: np.uint16,
        r: int,
        g: int,
        b: int,
    ):
        if w * h <= 0:
            return
        self.__display_ram_address(
            np.uint16(height),
            np.uint16(height + w - 1),
            np.uint16(width + 68),
            np.uint16(width + 68 + h - 1),
        )
        self.__write_command(np.uint8(0x2C))
        for n in range(w * h):
            self.__write_data(np.uint8(r))
            self.__write_data(np.uint8(g))
            self.__write_data(np.uint8(b))

    def __write_char(self, char_code: np.uint8):
        h = self.__text_conf.char_width * self.__text_conf.scale
        w = self.__text_conf.char_height * self.__text_conf.scale
        char_code = char_code & 0x7F
        if char_code < ord(" "):
            char_code = 0
        else:
            char_code -= ord(" ")  # start 1 index as "!"
        self.__display_ram_address(
            np.uint16(self.__text_conf.height),
            np.uint16(self.__text_conf.height + w - 1),
            np.uint16(self.__text_conf.width),
            np.uint16(self.__text_conf.width + h - 1),
        )
        self.__write_command(np.uint8(0x2C))  # Write Memory Start
        # Copy pixels
        for iy in range(self.__text_conf.char_height):
            for i in range(self.__text_conf.scale):
                for ix in range(self.__text_conf.char_width):
                    state = self.__font_matrix.font[char_code][ix] & (1 << iy)
                    for j in range(self.__text_conf.scale):
                        self.__write_data(
                            self.__text_conf.color.r
                            if state
                            else self.__text_conf.bgcolor.r
                        )
                        self.__write_data(
                            self.__text_conf.color.g
                            if state
                            else self.__text_conf.bgcolor.g
                        )
                        self.__write_data(
                            self.__text_conf.color.b
                            if state
                            else self.__text_conf.bgcolor.b
                        )

    def display_write_text(self, text: str):
        for c in text:
            if c == "\n":
                self.__text_conf.height -= (
                    self.__text_conf.char_height * self.__text_conf.scale
                )
                self.__text_conf.width = self.__text_conf.origin_x + 68
            else:
                self.__write_char(ord(c))
                self.__text_conf.width += (
                    self.__text_conf.char_width * self.__text_conf.scale
                )

    def display_box(
        self,
        height: np.uint16,
        width: np.uint16,
        w: np.uint16,
        h: np.uint16,
        r: int,
        g: int,
        b: int,
    ):
        r = np.uint8(r)
        g = np.uint8(g)
        b = np.uint8(b)
        height = np.uint16(height)
        width = np.uint16(width)
        w = np.uint16(w)
        h = np.uint16(h)
        self.display_rect(height, width, w, np.uint16(1), r, g, b)
        self.display_rect(height, width + h - 1, w, np.uint16(1), r, g, b)
        self.display_rect(height, width, np.uint16(1), h, r, g, b)
        self.display_rect(height + w - 1, width, np.uint16(1), h, r, g, b)

    def display_set_text_origin_position(self, width: int):
        self.__text_conf.origin_x = (
            width * self.__text_conf.char_width * self.__text_conf.scale
        )

    def display_set_pixel(
        self, height: np.uint16, width: np.uint16, r: int, g: int, b: int
    ):
        self.__display_ram_address(
            np.uint16(height),
            np.uint16(height),
            np.uint16(width + 68),
            np.uint16(width + 68),
        )
        self.__write_command(np.uint8(0x2C))
        self.__write_data(np.uint8(r))
        self.__write_data(np.uint8(g))
        self.__write_data(np.uint8(b))

        # component exported methods

    exported_functions = {
        "display_set_text_origin_position": display_set_text_origin_position,
        "display_box": display_box,
        "display_write_text": display_write_text,
        "display_rect": display_rect,
        "display_Show_RGB": display_show_rgb,
        "display_set_text_color": display_set_text_color,
        "display_set_text_bgcolor": display_set_text_bgcolor,
        "display_set_text_scale": display_set_text_scale,
        "display_set_text_pos": display_set_text_pos,
        "display_set_text_pos2": display_set_text_pos2,
        "display_set_pixel": display_set_pixel,
    }

    def process_high_level_call(self, string_call):
        """
        This method receive as parameter a string_call containing a sequence of values,
        the first one is the class method name (e.g. lectura), then a lists of
        parameters for its call.
        """
        # get information from string
        ls = string_call.split(",")
        function_name = ls[0]

        if function_name not in self.exported_functions:
            raise FunctionNotImplementedError(function_name)

        function = self.exported_functions[function_name]
        # get parameters
        args_str = ls[1:]
        # call the function
        self.run_with_args(function, args_str)
        return True

    def run_with_args(self, function, args):
        signature = inspect.signature(function)
        parameters = signature.parameters
        new_args = [self]
        for name, param in parameters.items():
            exp_type = param.annotation
            if exp_type is not inspect.Parameter.empty:
                try:
                    value = args[0]
                    args = args[1:]
                    value = exp_type(value)
                    new_args.append(value)
                except (TypeError, ValueError):
                    print(
                        f"Error: Can't convert the arg '{name}' al tipo {exp_type.__name__}"
                    )

        return function(*new_args)


class Font6_8:
    def __init__(self):
        self.font = [
            [0x00, 0x00, 0x00, 0x00, 0x00, 0x00],  # ,0x00
            [0x5F, 0x00, 0x00, 0x00, 0x00, 0x00],  # ,0x00 !
            [0x03, 0x00, 0x03, 0x00, 0x00, 0x00],  # ,0x00 "
            [0x14, 0x7F, 0x14, 0x7F, 0x14, 0x00],  # ,0x00 #
            [0x6F, 0x49, 0xC9, 0x7B, 0x00, 0x00],  # ,0x00 $
            [0x63, 0x13, 0x08, 0x64, 0x63, 0x00],  # ,0x00 %
            [0x7F, 0xC9, 0x49, 0x63, 0x00, 0x00],  # ,0x00 &
            [0x03, 0x00, 0x00, 0x00, 0x00, 0x00],  # ,0x00 '
            [0x3E, 0x41, 0x00, 0x00, 0x00, 0x00],  # ,0x00 (
            [0x41, 0x3E, 0x00, 0x00, 0x00, 0x00],  # ,0x00 )
            [0x0A, 0x04, 0x1F, 0x04, 0x0A, 0x00],  # ,0x00 *
            [0x08, 0x08, 0x3E, 0x08, 0x08, 0x00],  # ,0x00 +
            [0x00, 0x00, 0xC0, 0x00, 0x00, 0x00],  # ,0x00 ,
            [0x08, 0x08, 0x08, 0x08, 0x00, 0x00],  # ,0x00 -
            [0x00, 0x00, 0x40, 0x00, 0x00, 0x00],  # ,0x00 .
            [0x60, 0x10, 0x08, 0x04, 0x03, 0x00],  # ,0x00 /
            [0x7F, 0x41, 0x41, 0x7F, 0x00, 0x00],  # ,0x00 0
            [0x01, 0x7F, 0x00, 0x00, 0x00, 0x00],  # ,0x00 1
            [0x7B, 0x49, 0x49, 0x6F, 0x00, 0x00],  # ,0x00 2
            [0x63, 0x49, 0x49, 0x7F, 0x00, 0x00],  # ,0x00 3
            [0x0F, 0x08, 0x08, 0x7F, 0x00, 0x00],  # ,0x00 4
            [0x6F, 0x49, 0x49, 0x7B, 0x00, 0x00],  # ,0x00 5
            [0x7F, 0x49, 0x49, 0x7B, 0x00, 0x00],  # ,0x00 6
            [0x03, 0x01, 0x01, 0x7F, 0x00, 0x00],  # ,0x00 7
            [0x7F, 0x49, 0x49, 0x7F, 0x00, 0x00],  # ,0x00 8
            [0x0F, 0x09, 0x09, 0x7F, 0x00, 0x00],  # ,0x00 9
            [0x41, 0x00, 0x00, 0x00, 0x00, 0x00],  # ,0x00 :
            [0xC1, 0x00, 0x00, 0x00, 0x00, 0x00],  # ,0x00 ;
            [0x08, 0x14, 0x22, 0x00, 0x00, 0x00],  # ,0x00 <
            [0x14, 0x14, 0x14, 0x14, 0x00, 0x00],  # ,0x00 =
            [0x22, 0x14, 0x08, 0x00, 0x00, 0x00],  # ,0x00 >
            [0x03, 0x59, 0x09, 0x0F, 0x00, 0x00],  # ,0x00 ?
            [0x7F, 0x41, 0x5D, 0x55, 0x5F, 0x00],  # ,0x00 @
            [0x7F, 0x09, 0x09, 0x7F, 0x00, 0x00],  # ,0x00 A
            [0x7F, 0x49, 0x49, 0x77, 0x00, 0x00],  # ,0x00 B
            [0x7F, 0x41, 0x41, 0x63, 0x00, 0x00],  # ,0x00 C
            [0x7F, 0x41, 0x41, 0x3E, 0x00, 0x00],  # ,0x00 D
            [0x7F, 0x49, 0x49, 0x63, 0x00, 0x00],  # ,0x00 E
            [0x7F, 0x09, 0x09, 0x03, 0x00, 0x00],  # ,0x00 F
            [0x7F, 0x41, 0x49, 0x7B, 0x00, 0x00],  # ,0x00 G
            [0x7F, 0x08, 0x08, 0x7F, 0x00, 0x00],  # ,0x00 H
            [0x41, 0x7F, 0x41, 0x00, 0x00, 0x00],  # ,0x00 I
            [0x60, 0x40, 0x40, 0x7F, 0x00, 0x00],  # ,0x00 J
            [0x7F, 0x08, 0x08, 0x77, 0x00, 0x00],  # ,0x00 K
            [0x7F, 0x40, 0x40, 0x60, 0x00, 0x00],  # ,0x00 L
            [0x7F, 0x01, 0x01, 0x7F, 0x01, 0x01],  # ,0x7f M
            [0x7F, 0x01, 0x01, 0x7F, 0x00, 0x00],  # ,0x00 N
            [0x7F, 0x41, 0x41, 0x7F, 0x00, 0x00],  # ,0x00 O
            [0x7F, 0x09, 0x09, 0x0F, 0x00, 0x00],  # ,0x00 P
            [0x7F, 0x41, 0xC1, 0x7F, 0x00, 0x00],  # ,0x00 Q
            [0x7F, 0x09, 0x09, 0x77, 0x00, 0x00],  # ,0x00 R
            [0x6F, 0x49, 0x49, 0x7B, 0x00, 0x00],  # ,0x00 S
            [0x01, 0x01, 0x7F, 0x01, 0x01, 0x00],  # ,0x00 T
            [0x7F, 0x40, 0x40, 0x7F, 0x00, 0x00],  # ,0x00 U
            [0x7F, 0x20, 0x10, 0x0F, 0x00, 0x00],  # ,0x00 V
            [0x7F, 0x40, 0x40, 0x7F, 0x40, 0x40],  # ,0x7f W
            [0x6C, 0x10, 0x10, 0x6C, 0x00, 0x00],  # ,0x00 X
            [0x6F, 0x48, 0x48, 0x7F, 0x00, 0x00],  # ,0x00 Y
            [0x71, 0x49, 0x49, 0x47, 0x00, 0x00],  # ,0x00 Z
            [0x7F, 0x41, 0x00, 0x00, 0x00, 0x00],  # ,0x00 [
            [0x03, 0x04, 0x08, 0x10, 0x60, 0x00],  # ,0x00 \
            [0x41, 0x7F, 0x00, 0x00, 0x00, 0x00],  # ,0x00 ]
            [0x04, 0x02, 0x01, 0x02, 0x04, 0x00],  # ,0x00 ^
            [0x80, 0x80, 0x80, 0x80, 0x80, 0x80],  # ,0x80 _
            [0x03, 0x00, 0x00, 0x00, 0x00, 0x00],  # ,0x00 `
            [0x74, 0x54, 0x54, 0x7C, 0x00, 0x00],  # ,0x00 a
            [0x7F, 0x44, 0x44, 0x7C, 0x00, 0x00],  # ,0x00 b
            [0x7C, 0x44, 0x44, 0x6C, 0x00, 0x00],  # ,0x00 c
            [0x7C, 0x44, 0x44, 0x7F, 0x00, 0x00],  # ,0x00 d
            [0x7C, 0x54, 0x54, 0x5C, 0x00, 0x00],  # ,0x00 e
            [0x7F, 0x05, 0x05, 0x01, 0x00, 0x00],  # ,0x00 f
            [0xBC, 0xA4, 0xA4, 0xFC, 0x00, 0x00],  # ,0x00 g
            [0x7F, 0x04, 0x04, 0x7C, 0x00, 0x00],  # ,0x00 h
            [0x7D, 0x00, 0x00, 0x00, 0x00, 0x00],  # ,0x00 i
            [0x80, 0xFD, 0x00, 0x00, 0x00, 0x00],  # ,0x00 j
            [0x7F, 0x04, 0x04, 0x7A, 0x00, 0x00],  # ,0x00 k
            [0x7F, 0x00, 0x00, 0x00, 0x00, 0x00],  # ,0x00 l
            [0x7C, 0x04, 0x04, 0x7C, 0x04, 0x04],  # ,0x7c m
            [0x7C, 0x04, 0x04, 0x7C, 0x00, 0x00],  # ,0x00 n
            [0x7C, 0x44, 0x44, 0x7C, 0x00, 0x00],  # ,0x00 o
            [0xFC, 0x44, 0x44, 0x7C, 0x00, 0x00],  # ,0x00 p
            [0x7C, 0x44, 0x44, 0xFC, 0x00, 0x00],  # ,0x00 q
            [0x7C, 0x04, 0x04, 0x0C, 0x00, 0x00],  # ,0x00 r
            [0x5C, 0x54, 0x54, 0x74, 0x00, 0x00],  # ,0x00 s
            [0x7F, 0x44, 0x44, 0x60, 0x00, 0x00],  # ,0x00 t
            [0x7C, 0x40, 0x40, 0x7C, 0x00, 0x00],  # ,0x00 u
            [0x7C, 0x20, 0x10, 0x0C, 0x00, 0x00],  # ,0x00 v
            [0x7C, 0x40, 0x40, 0x7C, 0x40, 0x40],  # ,0x7c w
            [0x6C, 0x10, 0x10, 0x6C, 0x00, 0x00],  # ,0x00 x
            [0xBC, 0xA0, 0xA0, 0xFC, 0x00, 0x00],  # ,0x00 y
            [0x64, 0x54, 0x54, 0x4C, 0x00, 0x00],  # ,0x00 z
            [0x08, 0x3E, 0x41, 0x00, 0x00, 0x00],  # ,0x00 {
            [0xFF, 0x00, 0x00, 0x00, 0x00, 0x00],  # ,0x00 |
            [0x41, 0x3E, 0x08, 0x00, 0x00, 0x00],  # ,0x00 }
            [0x1C, 0x04, 0x1C, 0x10, 0x1C, 0x00],  # ,0x00 ~
            [0x00, 0x00, 0x00, 0x00, 0x00, 0x00],  # ,0x00
        ]
