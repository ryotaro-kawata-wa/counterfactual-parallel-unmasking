# Exact finite public signal lower bound

`ForestSampling/ObservedSignalLower.lean` closes the final packaging distinction for `app:cor:signal-calibrated-finite-lower` in `appendix_benchmarks.tex`.

- `signalCalibrated_observed_public_class_lower_any_vocabulary` quantifies an arbitrary finite nonempty vocabulary, public signal and radius, arbitrary full-feedback observed sampler, and actual uniform public-class budgets and seed-averaged TV risk. It constructs the contained matching family, transports it to the specified vocabulary, restricts the public guarantee, and obtains the exact `floor(signal^(-1/exponent))/8` query threshold or the finite minimum of the two printed round thresholds. The cubic A2 condition is a hypothesis; family inclusion and relabeling are proved consequences.
- `benchmark_observed_public_class_lower_floor_any_vocabulary` specializes the signal to the benchmark and retains the exact floor and round minimum. It uses the proved real-power calibration identities. The older `benchmark_observed_public_class_lower_any_vocabulary` remains useful for asymptotics but weakens the floor threshold to a simpler power divided by 16.

The signal theorem permits nonnegative radius and omits unnecessary explicit lower bounds on N or R, so it includes the manuscript domain. It uses the same normalized response exponent, response constant and frequency constant of one as the printed corollary. The benchmark theorem assumes positive radius and positive N, and therefore covers the printed N >= 4 domain.

Validation: `lake build ForestSampling.ObservedSignalLower` passed (8778 jobs). Both declarations were checked by `#print axioms`; each uses only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, or new axiom occurs. No existing module or manuscript was edited.
