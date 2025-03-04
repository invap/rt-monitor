# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

class InvalidEvent(Exception):
    def __init__(self, event):
        super().__init__()
        self._event = event

    def event(self):
        return self._event
