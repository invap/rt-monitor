# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

from workflow_runtime_verification.errors import ClockWasNotStarted, ClockWasAlreadyStarted, ClockWasAlreadyPaused, \
    ClockWasNotPaused


class Clock:
    def __init__(self, name):
        super().__init__()
        self._clockname = name
        self._pauseStart = 0
        self._dragTime = 0
        self._startTime = 0
        self._isPaused = False
        self._hasStarted = False

    def get_clockname(self):
        return self._clockname

    def start(self, start_time):
        if not self._hasStarted:
            self._hasStarted = True
            self._startTime = start_time
            self._dragTime = 0
            self._isPaused = False
            self._pauseStart = 0
        else:
            raise ClockWasAlreadyStarted(self.get_clockname())

    def pause(self, pause_time):
        if self._hasStarted:
            if not self._isPaused:
                self._isPaused = True
                self._pauseStart = pause_time
            else:
                raise ClockWasAlreadyPaused(self.get_clockname())
        else:
            raise ClockWasNotStarted(self.get_clockname())

    def resume(self, resume_time):
        if self._hasStarted:
            if self._isPaused:
                self._dragTime += resume_time - self._pauseStart
                self._pauseStart = 0
                self._isPaused = False
            else:
                raise ClockWasNotPaused(self.get_clockname())
        else:
            raise ClockWasNotStarted(self.get_clockname())

    def reset(self, start_time):
        if self._hasStarted:
            self._hasStarted = True
            self._startTime = start_time
            self._dragTime = 0
            self._isPaused = False
            self._pauseStart = 0
        else:
            raise ClockWasNotStarted(self.get_clockname())

    def get_time(self, now):
        if self._hasStarted:
            return now - self._startTime - self._dragTime
        else:
            raise ClockWasNotStarted(self.get_clockname())
