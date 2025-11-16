import numpy as np

from workflow_runtime_verification.components.component import Component


class SimpleDisplay(Component):
    def __init__(self):
        super().__init__()
        self._state = {"data": np.uint16(0)}

    def write(self, data: np.uint16):
        self._state["data"] = data

    def stop(self):
        pass

    def state(self):
        return self._state

    def exported_functions(self):
        return {"display_write": self.write}
