/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.ProductConditioning.SideInformation

/-! # Holenstein's Corollary 6

Without a conditioning variable or side information, Corollary 6 specializes to Raz's
conditioning lemma; and the side-information form applies to any joint distribution with a product
first marginal.
-/

namespace ComplexityTests.SideInformation

open Cslib.Probability.PMF
open scoped Cslib.Probability.PMF

-- With trivial `T` and `V`, Corollary 6 bounds the coordinate distances of a conditioned product.
example {ι : Type} [Fintype ι] {β : ι → Type} [∀ i, Fintype (β i)] (p : ∀ i, PMF (β i))
    (W : Set ((Unit × Unit) × (∀ i, β i)))
    (hW : ∃ x ∈ W, x ∈ (sideJoint (PMF.pure ()) fun _ => (pi p).map (·, ())).support) :
    ∑ j, dist (((sideJoint (PMF.pure ()) fun _ => (pi p).map (·, ())).filter W hW).map
          fun z => (z.1, z.2 j))
        ((((sideJoint (PMF.pure ()) fun _ => (pi p).map (·, ())).filter W hW).map Prod.fst).bind
          fun s => (p j).map (s, ·)) ≤
      Real.sqrt (Fintype.card ι * Real.log (Fintype.card Unit /
        ((sideJoint (PMF.pure ()) fun _ => (pi p).map (·, ())).toOuterMeasure W).toReal) / 2) :=
  sum_dist_filter_sideJoint_le (PMF.pure ()) (fun i _ => p i) (fun _ => (pi p).map (·, ()))
    (fun _ => by rw [PMF.map_comp]; exact PMF.map_id _) W hW

end ComplexityTests.SideInformation
