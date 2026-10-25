/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.CorrelatedSampling.Embeddability

/-! # Local embeddings

Independent private samples embed exactly; a common value known to both parties is embedded by
Lemma 8; and Corollary 9 and Fact 11 are guarded.
-/

namespace ComplexityTests.Embeddability

open Cslib.Probability.CorrelatedSampling
open scoped Cslib.Probability.PMF

-- Lemma 10: independent private samples embed with error `0`.
example (P₀ : PMF (Bool × Bool)) (KS : Bool → PMF Bool) (KT : Bool → PMF Bool) :
    IsEmbeddable P₀
      (P₀.bind fun xy => (KS xy.1).bind fun s => (KT xy.2).map fun t => (xy, (s, t))) 0 :=
  isEmbeddable_bind_prod P₀ KS KT

-- Lemma 8 applies to every joint law.
example (J : PMF ((Bool × Bool) × Bool)) :
    IsEmbeddable (J.map Prod.fst) (J.map fun z => (z.1, (z.2, z.2)))
      (2 * dist J (withKernel (J.map Prod.fst) fun xy => condX J xy.1) +
        2 * dist J (withKernel (J.map Prod.fst) fun xy => condY J xy.2)) :=
  isEmbeddable_diag J

/--
info: 'Cslib.Probability.CorrelatedSampling.isEmbeddable_diag_of_dist_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isEmbeddable_diag_of_dist_le

/--
info: 'Cslib.Probability.CorrelatedSampling.isEmbeddable_bind_prod' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isEmbeddable_bind_prod

/--
info: 'Cslib.Probability.CorrelatedSampling.dist_filter_le_two_mul' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dist_filter_le_two_mul

end ComplexityTests.Embeddability
