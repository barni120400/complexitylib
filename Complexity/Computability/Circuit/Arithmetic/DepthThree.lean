/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.SumOfTerms
public import Complexity.Foundations.LinearAlgebra.Matrix.PartialDerivatives
public import Mathlib.Data.Nat.Choose.Central
import Complexity.Computability.Circuit.Simulation

/-!
# Depth-three circuits for the determinant and permanent

A depth-three circuit with product fan-in `d` adds products of `d` affine forms. Following Nisan
and Wigderson [NisanWigderson1996], measure a polynomial by the dimension of the span of its
`k`-th order partial derivatives (`MvPolynomial.partialDerivatives`). The measure is subadditive,
and a product of `d` affine forms has measure at most `choose d k`
(`MvPolynomial.rank_partialDerivatives_prod_le`). The generic `n × n` determinant and permanent
have measure at least `choose n k ^ 2` (`Matrix.choose_sq_le_rank_partialDerivatives_det`). So
every such circuit computing either one has at least `choose n k ^ 2 / choose d k` product gates.
For homogeneous circuits, whose product fan-in is the degree `n`, the middle split gives an
exponential bound.

Circuits add dictionary terms (`Cslib.Circuits.SumOfTerms`): additions and wiring are free, and a
reused product gate is charged once. The field is arbitrary, and the premise is equality of
formal polynomials. These are bounds for this restricted model, not for unrestricted arithmetic
circuits.

## Main definitions

* `Cslib.Circuits.DepthThree.Term`: a product of `d` affine forms.

## Main results

* `Cslib.Circuits.DepthThree.rank_partialDerivatives_le_mul_cost`: every output has `k`-th order
  partial-derivative dimension at most `choose d k` times the number of product gates.
* `Cslib.Circuits.DepthThree.choose_sq_le_mul_cost_det`,
  `Cslib.Circuits.DepthThree.choose_sq_le_mul_cost_permanent`: product-gate lower bounds for the
  determinant and permanent.
* `Cslib.Circuits.DepthThree.four_pow_lt_mul_cost_det`,
  `Cslib.Circuits.DepthThree.four_pow_lt_mul_cost_permanent`: homogeneous depth-three circuits for
  the `2n × 2n` determinant and permanent need more than `4 ^ n / n` product gates.

## References

* [N. Nisan, A. Wigderson, *Lower bounds on arithmetic circuits via partial
  derivatives*][NisanWigderson1996]
-/

@[expose] public section

namespace Cslib.Circuits.DepthThree

open MvPolynomial

/-- A product of `d` affine forms in the variables `σ`: one product gate of a depth-three circuit
with product fan-in `d`. -/
structure Term (K σ : Type*) (d : ℕ) where
  /-- The coefficient of each variable in each factor. -/
  coefficients : Fin d → σ → K
  /-- The constant term of each factor. -/
  constants : Fin d → K

variable {K σ : Type*} {d : ℕ}

/-- The polynomial represented by a depth-three term. -/
noncomputable def Term.polynomial [CommSemiring K] [Fintype σ] (t : Term K σ d) :
    MvPolynomial σ K :=
  ∏ i, (∑ v, t.coefficients i v • X v + C (t.constants i))

variable [Field K]

/-- **Nisan-Wigderson.** Every output of a depth-three circuit with product fan-in `d` has
`k`-th order partial-derivative dimension at most `choose d k` times the number of product gates.
Additions and wiring are free, and shared gates are charged once. -/
theorem rank_partialDerivatives_le_mul_cost [Fintype σ] {m : ℕ}
    (c : Circuit (SumOfTerms.signature (Term K σ d)) 0 m) (k : ℕ) (j : Fin m) :
    (partialDerivatives k (c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j)).rank ≤
      (d.choose k * c.program.cost SumOfTerms.termCost : ℕ) := by
  have hcost : c.program.cost (SumOfTerms.dictionaryCost fun _ : Term K σ d => d.choose k) =
      d.choose k * c.program.cost SumOfTerms.termCost := by
    rw [Program.cost_eq_sum, Program.cost_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by cases (c.program.lines i).op <;> simp
  rw [← hcost]
  exact SumOfTerms.rank_trace_le c.program Term.polynomial (partialDerivatives k) _
    (fun t => rank_partialDerivatives_prod_le t.coefficients t.constants k) Fin.elim0
    (fun i => i.elim0) (c.outputs j)

variable {n m : ℕ}

/-- **Nisan-Wigderson.** A depth-three circuit with product fan-in `d` computing the generic
`n × n` determinant has at least `choose n k ^ 2 / choose d k` product gates, for every `k`. -/
theorem choose_sq_le_mul_cost_det
    (c : Circuit (SumOfTerms.signature (Term K (Fin n × Fin n) d)) 0 m) (k : ℕ) (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j =
      (Matrix.mvPolynomialX (Fin n) (Fin n) K).det) :
    n.choose k ^ 2 ≤ d.choose k * c.program.cost SumOfTerms.termCost := by
  have h := rank_partialDerivatives_le_mul_cost c k j
  rw [hcompute] at h
  exact_mod_cast (Matrix.choose_sq_le_rank_partialDerivatives_det k).trans h

/-- **Nisan-Wigderson.** A depth-three circuit with product fan-in `d` computing the generic
`n × n` permanent has at least `choose n k ^ 2 / choose d k` product gates, for every `k`. -/
theorem choose_sq_le_mul_cost_permanent
    (c : Circuit (SumOfTerms.signature (Term K (Fin n × Fin n) d)) 0 m) (k : ℕ) (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j =
      (Matrix.mvPolynomialX (Fin n) (Fin n) K).permanent) :
    n.choose k ^ 2 ≤ d.choose k * c.program.cost SumOfTerms.termCost := by
  have h := rank_partialDerivatives_le_mul_cost c k j
  rw [hcompute] at h
  exact_mod_cast (Matrix.choose_sq_le_rank_partialDerivatives_permanent k).trans h

/-- The middle split of a bound `choose (2n) n ^ 2 ≤ choose (2n) n * s`, with the
central-binomial estimate. -/
private theorem four_pow_lt_mul_of_sq_le {s : ℕ} (hn : 4 ≤ n)
    (h : (2 * n).choose n ^ 2 ≤ (2 * n).choose n * s) : 4 ^ n < n * s := by
  rw [sq] at h
  have hle := Nat.le_of_mul_le_mul_left h (Nat.choose_pos (by omega))
  exact (Nat.four_pow_lt_mul_centralBinom n hn).trans_le
    (Nat.mul_le_mul_left n (Nat.centralBinom_eq_two_mul_choose n ▸ hle))

/-- Homogeneous depth-three circuits for the generic `2n × 2n` determinant need more than
`4 ^ n / n` product gates. -/
theorem four_pow_lt_mul_cost_det (hn : 4 ≤ n)
    (c : Circuit (SumOfTerms.signature (Term K (Fin (2 * n) × Fin (2 * n)) (2 * n))) 0 m)
    (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j =
      (Matrix.mvPolynomialX (Fin (2 * n)) (Fin (2 * n)) K).det) :
    4 ^ n < n * c.program.cost SumOfTerms.termCost :=
  four_pow_lt_mul_of_sq_le hn (choose_sq_le_mul_cost_det c n j hcompute)

/-- Homogeneous depth-three circuits for the generic `2n × 2n` permanent need more than
`4 ^ n / n` product gates. -/
theorem four_pow_lt_mul_cost_permanent (hn : 4 ≤ n)
    (c : Circuit (SumOfTerms.signature (Term K (Fin (2 * n) × Fin (2 * n)) (2 * n))) 0 m)
    (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j =
      (Matrix.mvPolynomialX (Fin (2 * n)) (Fin (2 * n)) K).permanent) :
    4 ^ n < n * c.program.cost SumOfTerms.termCost :=
  four_pow_lt_mul_of_sq_le hn (choose_sq_le_mul_cost_permanent c n j hcompute)

end Cslib.Circuits.DepthThree
