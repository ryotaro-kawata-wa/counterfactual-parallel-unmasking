"""Evaluate the same packed screen with deferred, row-local exact vote counting."""

from contextlib import contextmanager
from math import ceil

import numpy as np

import toy


class DeferredVotes:
    """Store each observed source-color subset, then replay exact bit-sliced sums.

    Please keep the threshold at the originally requested M//2 even when inspecting
    a prefix. No candidate or oracle call is discarded by this storage strategy.
    """

    def __init__(self, n, count):
        self.n, self.count = n, count
        self.threshold = count//2
        self.universe = (1 << n)-1
        self.patterns = np.zeros((n, count), dtype=np.uint32)
        self.group_masks = []
        self.cache = {}

    def start_coloring(self, groups):
        masks = []
        for group in groups:
            bits = np.zeros(self.n, dtype=np.uint8)
            bits[group] = 1
            masks.append(int.from_bytes(np.packbits(bits, bitorder='little').tobytes(), 'little'))
        self.group_masks.append(masks)
        self.cache.clear()

    def majority_mask(self, readout, threshold=None):
        threshold = self.threshold if threshold is None else threshold
        if threshold == self.threshold and readout in self.cache:
            return self.cache[readout]
        planes = [0]*self.count.bit_length()
        for pattern, masks in zip(self.patterns[readout], self.group_masks):
            pattern, voters = int(pattern), 0
            while pattern:
                low = pattern & -pattern
                voters |= masks[low.bit_length()-1]
                pattern ^= low
            for bit in range(len(planes)):
                if not voters:
                    break
                old = planes[bit]
                planes[bit] = old ^ voters
                voters &= old
        equal, greater = self.universe, 0
        for bit in reversed(range(len(planes))):
            plane = planes[bit]
            if (threshold >> bit) & 1:
                equal &= plane
            else:
                greater |= equal & plane
                equal &= ~plane
        if threshold == self.threshold:
            self.cache[readout] = greater
        return greater

    def row(self, readout, cutoff):
        return toy.MajorityVotes.row(self, readout, cutoff)


def packed_screen(oracle, params, history, draft, columns, rng, colorings=None, observer=None):
    if params.palette > 32:
        raise ValueError('Please use at most 32 colors for the compact source-subset storage.')
    residual = np.flatnonzero(history < 0)
    if observer is not None:
        observer.start_screen(history, draft, columns)
    if len(columns) <= 1 or not len(residual):
        return {int(j): set() for j in residual}
    count = params.colorings if colorings is None else len(colorings)
    votes = DeferredVotes(params.n, count)
    width = ceil(params.n/params.chunks)
    for tau in range(count):
        colors = (rng.integers(params.palette, size=params.n) if colorings is None
                  else np.asarray(colorings[tau]))
        groups = [residual[colors[residual] == c] for c in range(params.palette)]
        votes.start_coloring(groups)
        if observer is not None:
            observer.observe_coloring(groups, draft, columns)
        prepared = oracle.prepare_screen_coloring(history, draft, colors, columns, params.palette)
        for readout_color, group in enumerate(groups):
            sources = np.array([c for c in range(params.palette) if c != readout_color])
            for start in range(0, len(group), width):
                chunk = group[start:start+width]
                rows = oracle.submit_chunk_family(prepared, chunk, sources)
                diameter = np.zeros((len(chunk), len(sources)))
                for first in range(len(columns)):
                    for second in range(first):
                        diameter = np.maximum(diameter, np.abs(rows[first]-rows[second]).sum(axis=-1)/2)
                if observer is not None:
                    observer.observe_chunk(chunk, sources, diameter)
                positive_readouts, positive_sources = np.nonzero(diameter > 2*params.eps)
                patterns = np.zeros(len(chunk), dtype=np.uint32)
                source_bits = np.left_shift(np.uint32(1), sources[positive_sources].astype(np.uint32))
                np.bitwise_or.at(patterns, positive_readouts, source_bits)
                votes.patterns[chunk, tau] = patterns
        if observer is not None:
            observer.observe_prefix(tau+1, count, votes)
    result = {int(j): votes.row(int(j), params.d) for j in residual}
    if observer is not None:
        observer.finish_screen(result)
    return result


@contextmanager
def use_deferred_screen():
    """Please isolate this runtime choice within one worker process or a replay."""
    original = toy.packed_screen
    toy.packed_screen = packed_screen
    try:
        yield
    finally:
        toy.packed_screen = original
