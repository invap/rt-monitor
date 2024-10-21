# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

class Component:
    def __init__(self, visual=False):
        self._visual = visual

    def stop(self):
        raise NotImplementedError

    def state(self):
        raise NotImplementedError

    def get_status(self):
        raise NotImplementedError

    def process_high_level_call(self, string_call):
        raise NotImplementedError

    def run_with_args(self, function, args):
        raise NotImplementedError


class SelfLoggableComponent(Component):
    def __init__(self, visual):
        super().__init__(visual)

    def process_log(self, log_file, mark):
        raise NotImplementedError
