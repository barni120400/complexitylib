/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flat.NetworkPolynomial
import Mathlib.Algebra.Ring.Int.Defs

/-! Tests of the polynomial of the complete network, as a client that sees only the public
statements: what the two nodes of one wire see; the coefficient at equal and at different strings
at the two ends of the wire; the same strings at both ends of all wires on three nodes. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationFlatNetwork

open Finset MvPolynomial Cslib Cslib.Circuits.Arithmetic.Separation.Flat

/-- The wire of the complete network on two nodes. -/
def wire : Pair 2 := ⟨0, 1, by decide⟩

/-- The smaller node sees the string at its end of the wire, and the zero string for itself. -/
example (x : Pair 2 → Bool → BitString 1) :
    assemble x 0 1 = x wire false ∧ assemble x 1 0 = x wire true ∧
      assemble x 0 0 = fun _ => false :=
  ⟨assemble_low x wire, assemble_high x wire, assemble_self x 0⟩

/-- One wire with one bit: the coefficient is `1` when both ends have the bit `true`. -/
example :
    (networkPolynomial ℤ 2 1).coeff (blockMonomial Prod.fst univ
      (BlockChoice.ofProd univ (assemble fun _ _ _ => true))) = 1 := by
  rw [coeff_networkPolynomial, ite_eq_left fun _ => rfl]

/-- One wire with one bit: the coefficient is `0` when the ends have different bits. -/
example :
    (networkPolynomial ℤ 2 1).coeff (blockMonomial Prod.fst univ
      (BlockChoice.ofProd univ (assemble fun _ d _ => d))) = 0 := by
  rw [coeff_networkPolynomial, ite_eq_right]
  exact fun h => Bool.false_ne_true (congrFun (h wire) 0)

/-- Three nodes: strings that do not depend on the end give the coefficient `1`, over any
semiring. -/
example {F : Type} [CommSemiring F] (s : Pair 3 → BitString 2) :
    (networkPolynomial F 3 2).coeff (blockMonomial Prod.fst univ
      (BlockChoice.ofProd univ (assemble fun e _ => s e))) = 1 := by
  rw [coeff_networkPolynomial, ite_eq_left fun _ => rfl]

end CslibFrontierTests.SeparationFlatNetwork
