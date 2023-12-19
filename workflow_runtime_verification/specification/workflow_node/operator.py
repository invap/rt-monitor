class Operator:
    @classmethod
    def new_of_type(cls, operator_type):
        return cls(operator_type)

    def __init__(self, operator_type):
        super().__init__()
        self._type = operator_type
