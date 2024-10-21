# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import unittest

from attic.tests.test_object_factories.test_object_factory import (
    TestObjectFactory,
)


class Test(unittest.TestCase):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.objects = TestObjectFactory()
        self.set_up()

    def set_up(self):
        pass

    def _resource_path_for(self, filename):
        return f"{self._resources_folder()}/{filename}"

    def _resources_folder(self):
        return "framework/tests/sandbox"
