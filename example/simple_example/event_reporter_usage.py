import os
import shutil
import sys

from workflow_runtime_verification.reporting.event_reporter.event_reporter import (
    EventReporter,
)


class Clock:
    def __init__(self):
        self._count = 0

    def current(self):
        return self._tick()

    def _tick(self):
        self._count += 1
        return self._count


clock = Clock()

report_file_name = "main_log.txt"


def log_common_branch_declarations():
    event_reporter.report_declared_variable("fail_safe_lock", "int", clock.current())
    event_reporter.report_declared_variable("stage", "int", clock.current())
    event_reporter.report_declared_variable("pressure", "int", clock.current())
    event_reporter.report_declared_variable("temperature", "int", clock.current())


def log_test_run_branch_declarations():
    event_reporter.report_declared_variable("results", "char*", clock.current())
    event_reporter.report_declared_variable("signatures", "char*", clock.current())


def log_common_branch():
    event_reporter.report_variable_value_assigned(
        "fail_safe_lock", "0", clock.current()
    )

    event_reporter.report_variable_value_assigned("stage", "1", clock.current())
    event_reporter.report_task_started(
        "initiate_pressure_measurements", clock.current()
    )
    event_reporter.report_checkpoint_reached("control_failsafe", clock.current())

    event_reporter.report_variable_value_assigned("pressure", "156", clock.current())
    event_reporter.report_component_event(
        "display", "display_write,156", clock.current()
    )
    event_reporter.report_task_finished(
        "initiate_pressure_measurements", clock.current()
    )
    event_reporter.report_task_started("start_coolant_pump", clock.current())
    event_reporter.report_variable_value_assigned("stage", "2", clock.current())
    event_reporter.report_task_finished("start_coolant_pump", clock.current())
    event_reporter.report_task_started(
        "initiate_temperature_measurements", clock.current()
    )
    event_reporter.report_checkpoint_reached("control_failsafe", clock.current())
    event_reporter.report_variable_value_assigned("temperature", "617", clock.current())
    event_reporter.report_component_event(
        "display", "display_write,156", clock.current()
    )
    event_reporter.report_task_finished(
        "initiate_temperature_measurements", clock.current()
    )


def log_test_run_branch():
    event_reporter.report_variable_value_assigned(
        "results", '"resultsOK"', clock.current()
    )
    event_reporter.report_variable_value_assigned(
        "signatures", '"supervisor1supervisor2"', clock.current()
    )
    event_reporter.report_task_started("stop_coolant_pump", clock.current())
    event_reporter.report_variable_value_assigned("stage", "1", clock.current())
    event_reporter.report_task_finished("stop_coolant_pump", clock.current())
    event_reporter.report_checkpoint_reached("log_test_run_results", clock.current())


def log_real_run_branch():
    event_reporter.report_checkpoint_reached(
        "control_pressure_manually", clock.current()
    )
    event_reporter.report_checkpoint_reached(
        "control_temperature_manually", clock.current()
    )
    event_reporter.report_task_started("withdraw_control_rods", clock.current())
    event_reporter.report_variable_value_assigned("stage", "3", clock.current())
    event_reporter.report_task_finished("withdraw_control_rods", clock.current())


with open(report_file_name, "w+") as report_file:
    event_reporter = EventReporter(report_file)

    LOOPS = 3

    log_common_branch_declarations()
    log_test_run_branch_declarations()

    for _loop in range(LOOPS):
        log_common_branch()
        log_test_run_branch()
        log_common_branch()
        log_real_run_branch()
