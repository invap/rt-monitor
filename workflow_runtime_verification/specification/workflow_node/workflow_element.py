class WorkflowElement:
    def __init__(self, name):
        super().__init__()
        self._name = name

    def is_named(self, name):
        return self._name == name

    def name(self):
        return self._name
