import unittest

from workflow_runtime_verification.tests.test_object_factories.test_object_factory import (
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
        return "workflow_runtime_verification/tests/sandbox"
