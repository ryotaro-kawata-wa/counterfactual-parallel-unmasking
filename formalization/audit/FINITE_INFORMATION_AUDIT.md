# Finite information and actual masking bridge

Verified modules: `FiniteInformation`, `FiniteErasureInformation`, `FiniteChannelInformation`, `FiniteMaskedInformation`, and `PathPairInformation`.

The definitions use actual finite probability laws. Mutual information is KL divergence from the joint law to the product of its own marginals. Conditional mutual information averages the ordinary normalized posterior mutual information over the actual background marginal; its posterior agrees with the existing `conditionalMap` operation.

The independent erasure channel is implemented as a genuine finite mixture of independent endpoint coins. The full configuration mask law similarly mixes coordinate product channels over the original (possibly dependent) target. An explicit coordinate equivalence extracts the masked background and the two masked endpoints. Bayes cancellation identifies the underlying conditional pair with `MaskedState.exactPair`. The resulting masked-pair CMI is exactly the endpoint-survival probability q² times the actual background average of this exact pair information. No conditional-independence assumption replaces the original probability law.

The path emission lemma proves exact KL/MI preservation under the two-type pushforward for any normalized pair density π(a)π(b)f(type(a),type(b)); positivity then bounds the actual token MI by log 2. The actual path posterior identification is supplied separately by `PathPairConditionals`.

Scope: these modules establish finite probability identities. They do not by themselves claim the effective-TC linear lower/upper bounds; those additionally need actual path separation, boundary positivity, mask-pattern probabilities, finite pair counting, and integral estimates.

Validation: Lake builds passed for all five modules on the pinned Lean 4.33.0/mathlib release. Every public theorem in these modules (73 total) was checked with `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound` occur. No `sorry`, added axiom, or admitted analytic/measurability premise was introduced.
