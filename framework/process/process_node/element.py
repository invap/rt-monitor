# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

class Element:
    def __init__(self, name):
        super().__init__()
        self._name = name

    def is_named(self, name):
        return self._name == name

    def name(self):
        return self._name

    def type(self):
        raise NotImplementedError