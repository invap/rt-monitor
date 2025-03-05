# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial


class ClockError(Exception):
    def __init__(self):
        super().__init__()


class ClockWasAlreadyStartedError(Exception):
    def __init__(self):
        super().__init__()


class UndeclaredClockError(Exception):
    def __init__(self):
        super().__init__()


class ClockWasNotStartedError(Exception):
    def __init__(self):
        super().__init__()


class ClockWasAlreadyPausedError(Exception):
    def __init__(self):
        super().__init__()


class ClockWasNotPausedError(Exception):
    def __init__(self):
        super().__init__()

