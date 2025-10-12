from verification import VerificationFromTest
from workflow_runtime_verification.tests.test import Test


class SimpleExampleVerificationTest(Test):
    def test_simple_example_verification_is_successful(self):
        verification = VerificationFromTest.new_for_workflow_in_file(
            self._simple_example_specification_file_path()
        )

        is_report_valid = verification.run_for_report(
            self._simple_example_report_file_path()
        )

        self.assertTrue(is_report_valid)

    def _simple_example_specification_file_path(self):
        return self._simple_example_file_path_for("framework.zip")

    def _simple_example_report_file_path(self):
        return self._simple_example_file_path_for("main_log.txt")

    def _simple_example_file_path_for(self, filename):
        return f"{self._simple_example_folder()}/{filename}"

    def _simple_example_folder(self):
        return "example/simple_example"
