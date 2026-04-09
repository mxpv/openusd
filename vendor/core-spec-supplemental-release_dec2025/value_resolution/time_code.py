import math


class timeCode:
    """Time Code for Value Resolution"""

    value: float = 1.0

    def __init__(self, value: float):
        self.value = value

    def is_default(self) -> bool:
        """Check if the time code is default (NaN)"""
        return math.isnan(self.value)

    def get_value(self):
        """Get the numeric value of the time code"""
        return self.value

    @staticmethod
    def default():
        """Get the default time code (NaN)"""
        return timeCode(float("nan"))

    @staticmethod
    def safe_step(time_value, step_back=True, epsilon=1e-9):
        """
        Create a time value that is slightly offset by epsilon.
        Useful for value clips to handle jump discontinuities.

        Args:
            time_value (float): The original time value
            step_back (bool): If True, subtract epsilon; if False, add epsilon
            epsilon (float): Small value for offset (default: 1e-9)

        Returns:
            timeCode: A new timeCode instance with the offset value
        """
        if step_back:
            return timeCode(time_value - epsilon)
        else:
            return timeCode(time_value + epsilon)
