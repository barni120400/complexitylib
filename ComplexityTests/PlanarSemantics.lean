/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/
import Complexity.Computability.Complexity.Problems.SAT.Planar.Correctness

open Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Complexity.SAT.PlanarCompile

-- Concrete nonempty actual compiler outputs have satisfying assignments for both polarities.
example : (rawFormula [[(0, true)]]).eval (fun _ => true) = true := by decide +kernel
example : (rawFormula [[(0, false)]]).eval (fun _ => false) = true := by decide +kernel

-- The actual compact output cannot manufacture a model of contradictory unit clauses.
example : ¬ (formula [[(0, true)], [(0, false)]]).Satisfiable := by
  intro hs
  obtain ⟨τ, hτ⟩ := satisfiable_source_of_formula
    (by decide : ∀ c ∈ ([[(0, true)], [(0, false)]] : CNF ℕ), c.length ≤ 3)
    (fun v => (List.count_le_length :
      (CNF.vars ([[(0, true)], [(0, false)]] : CNF ℕ)).count v ≤
        (CNF.vars ([[(0, true)], [(0, false)]] : CNF ℕ)).length).trans (by decide)) hs
  cases hv : τ 0 <;> simp [CNF.eval, Clause.eval, Literal.eval, hv] at hτ
