# Copyright (c) 2024 Fundacion Sadosky, info@fundacionsadosky.org.ar
# Copyright (c) 2024 INVAP, open@invap.com.ar
# SPDX-License-Identifier: AGPL-3.0-or-later OR Fundacion-Sadosky-Commercial

import logging
import sys
import threading
from enum import Enum, auto

from pynput import keyboard

from errors.monitor_errors import FrameworkError, MonitorConstructionError, EventLogListError, AbortRun
from logging_configuration import (
    LoggingLevel,
    LoggingDestination,
    _set_up_logging,
    _configure_logging_destination,
    _configure_logging_level
)
from monitor_builder import MonitorBuilder


class AnalysisStatus(Enum):
    NOT_RUNNING = auto()
    RUNNING = auto()
    PAUSING = auto()
    PAUSED = auto()
    STOPPING = auto()


# Events for managing the analysis process
pause_event = threading.Event()
has_paused_event = threading.Event()
stop_event = threading.Event()
has_stopped_event = threading.Event()
analysis_process_status = AnalysisStatus.NOT_RUNNING


def _run_verification(process_thread):
    # Start the listener in a separate thread
    listener = keyboard.Listener(on_press=on_press)
    listener.start()
    # Configure the monitor by setting up control events and callback function.
    process_thread.set_events(pause_event, has_paused_event, stop_event, has_stopped_event)
    # Starts the monitor thread
    process_thread.start()
    # Waiting for the verification process to finish, either naturally or manually.
    process_thread.join()
    listener.stop()


def on_press(key):
    global pause_event
    global has_paused_event
    global stop_event
    global has_stopped_event
    global analysis_process_status
    try:
        # Check if the key has a `char` attribute (printable key)
        match key.char:
            case "s":
                if analysis_process_status == AnalysisStatus.RUNNING:
                    # Trigger stop event.
                    stop_event.clear()
                    analysis_process_status = AnalysisStatus.STOPPING
                    logging.warning(
                        "Verification is gracefully stopping in background. "
                        "It will STOP when it finishes processing the current event."
                    )
                    # Wait until the monitor thread notifies that the analysis haf been gracefully stopped
                    while has_stopped_event.is_set():
                        pass
                    logging.warning("Verification STOPPED.")
            case "p":
                if analysis_process_status == AnalysisStatus.RUNNING:
                    # Trigger pause event.
                    pause_event.clear()
                    analysis_process_status = AnalysisStatus.PAUSING
                    logging.warning(
                        "Verification is gracefully pausing in background. "
                        "It will PAUSE when it finishes processing the current event."
                    )
                    # Wait until the monitor thread notifies that the analysis haf been gracefully paused
                    while has_paused_event.is_set():
                        pass
                    analysis_process_status = AnalysisStatus.PAUSED
                    logging.warning("Verification PAUSED.")
                elif analysis_process_status == AnalysisStatus.PAUSED:
                    # Recover from pause.
                    pause_event.set()
                    analysis_process_status = AnalysisStatus.RUNNING
                    logging.warning("Verification RESUMED.")
                else:
                    pass
            case _:
                pass
    except AttributeError:
        # Handle special keys (like ctrl, alt, etc.) here if needed
        pass


def main():
    global pause_event
    global has_paused_event
    global stop_event
    global has_stopped_event
    global analysis_process_status
    # Build argument map.
    argument_map = {}
    for argument in range(1, len(sys.argv)):
        if sys.argv[argument].startswith("--framework="):
            if "framework" in argument_map:
                print("Multiple --framework argument.", file=sys.stderr)
                exit(-11)
            else:
                split_argument = sys.argv[argument].split("=")
                argument_map["framework"] = split_argument[1]
        elif sys.argv[argument].startswith("--reports="):
            if "reports" in argument_map:
                print("Multiple --reports argument.", file=sys.stderr)
                exit(-12)
            else:
                split_argument = sys.argv[argument].split("=")
                argument_map["reports"] = split_argument[1]
        elif sys.argv[argument] == "--log-file":
            if "log-file" in argument_map:
                print("Multiple --log-file argument.", file=sys.stderr)
                exit(-13)
            else:
                argument_map["log-file"] = ""
        elif sys.argv[argument].startswith("--log-level="):
            if "log-level" in argument_map:
                print("Multiple --log-level argument.", file=sys.stderr)
                exit(-14)
            else:
                split_argument = sys.argv[argument].split("=")
                argument_map["log-level"] = split_argument[1]
        else:
            print("Erroneous argument.", file=sys.stderr)
            exit(-1)
    if "framework" not in argument_map:
        print("Missing --framework argument.", file=sys.stderr)
        exit(-2)
    if "reports" not in argument_map:
        print("Missing --reports argument.", file=sys.stderr)
        exit(-3)
    # Choose logging destination.
    if "log-file" in argument_map:
        logging_destination = LoggingDestination.FILE
    else:
        logging_destination = LoggingDestination.CONSOLE
    # Choose logging level.
    if "log-level" in argument_map:
        match argument_map["log-level"]:
            case "all":
                logging_level = LoggingLevel.INFO
            case "analysis":
                logging_level = LoggingLevel.ANALYSIS
            case "warnings":
                logging_level = LoggingLevel.WARNING
            case "errors":
                logging_level = LoggingLevel.ERROR
            case _:
                print("Erroneous logging level.", file=sys.stderr)
                exit(-141)
    else:
        logging_level = LoggingLevel.ANALYSIS
    # Configure logger.
    _set_up_logging()
    _configure_logging_destination(logging_destination)
    _configure_logging_level(logging_level)
    # Create the Monitor
    monitor_builder = MonitorBuilder(argument_map["framework"], argument_map["reports"])
    try:
        monitor = monitor_builder.build_monitor(False)
    except FrameworkError:
        logging.critical(f"Runtime monitoring process ABORTED.")
    except EventLogListError:
        logging.critical(f"Runtime monitoring process ABORTED.")
    except MonitorConstructionError:
        logging.critical(f"Runtime monitoring process ABORTED.")
    else:
        # Events setup for managing the running mode.
        pause_event.set()
        has_paused_event.set()
        stop_event.set()
        has_stopped_event.set()
        analysis_process_status = AnalysisStatus.RUNNING
        # Creates a thread for controlling the analysis process
        application_thread = threading.Thread(
            target=_run_verification, args=[monitor]
        )
        try:
            application_thread.start()
        except AbortRun():
            logging.critical(f"Runtime verification process ABORTED.")


if __name__ == "__main__":
    main()
