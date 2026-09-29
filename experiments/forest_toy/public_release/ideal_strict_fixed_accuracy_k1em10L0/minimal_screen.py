"""Override only the observable screen diameter threshold in an isolated worker."""
from contextlib import contextmanager

import robustness
from deferred_screen import packed_screen


class ScreenParameters:
    """Please leave preprocessing calibration and controller caps unchanged."""
    def __init__(self, original, threshold):
        if not 0 < threshold <= 1:
            raise ValueError('Please use a positive TV detection threshold at most one.')
        self.original, self.threshold = original, threshold

    @property
    def eps(self):
        # The existing screen compares diameter to 2*eps. This adapter changes
        # that comparison only; it does not assert an oracle approximation bound.
        return self.threshold/2

    def __getattr__(self, name):
        return getattr(self.original, name)


@contextmanager
def screen_threshold(threshold):
    original = robustness.packed_screen
    def changed(oracle, params, *args, **kwargs):
        return packed_screen(oracle, ScreenParameters(params, threshold), *args, **kwargs)
    robustness.packed_screen = changed
    try:
        yield
    finally:
        robustness.packed_screen = original
