# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

class ClockException(Exception):
    def __init__(self, clockname):
        super().__init__()
        self._clockname = clockname

    def get_clockname(self):
        return self._clockname


class UndeclaredClock(ClockException):
    def __init__(self, clockname):
        super().__init__(clockname)


class ClockWasNotStarted(ClockException):
    def __init__(self, clockname):
        super().__init__(clockname)


class ClockWasAlreadyStarted(ClockException):
    def __init__(self, clockname):
        super().__init__(clockname)


class ClockWasAlreadyPaused(ClockException):
    def __init__(self, clockname):
        super().__init__(clockname)


class ClockWasNotPaused(ClockException):
    def __init__(self, clockname):
        super().__init__(clockname)

