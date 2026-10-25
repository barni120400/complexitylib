/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Orthogonal
import Mathlib.Tactic

/-!
# Unit subdivision of finite orthogonal routes

## Main definitions

* `Cslib.Orthogonal.walk`: a finite sequence of repeated integer vector steps.
* `Cslib.Orthogonal.segmentWalk`, `Cslib.Orthogonal.subdivide`: unit subdivision of a segment
  or an entire polygonal route, listing a shared endpoint only once.

## Main results

* `Cslib.Orthogonal.walk_length`, `Cslib.Orthogonal.walk_head`,
  `Cslib.Orthogonal.walk_last`: size and endpoint formulas.
* `Cslib.Orthogonal.subdivide_head`, `Cslib.Orthogonal.subdivide_last`: endpoint preservation.
* `Cslib.Orthogonal.subdivide_length`: exact point count from original Manhattan wire length.
* `Cslib.Orthogonal.subdivide_unit`: every subdivided segment has Manhattan length one.
* `Cslib.Orthogonal.support_subdivide`: equality of the complete continuous real supports.
* `Cslib.Orthogonal.wireLength_subdivide`: exact wire-length preservation.
-/

@[expose] public section

namespace Cslib.Orthogonal

/-- The `k+1` lattice points obtained by taking `k` copies of vector `d` from `a`. -/
def walk (a d : Point) : ℕ → Route
  | 0 => [a]
  | k + 1 => a :: walk (a + d) d k

/-- One more listed point than steps. -/
@[simp] theorem walk_length (a d : Point) (k : ℕ) : (walk a d k).length = k + 1 := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [walk, ih]

/-- The walk always starts at its prescribed first point. -/
@[simp] theorem walk_head (a d : Point) (k : ℕ) : (walk a d k).head? = some a := by
  cases k <;> rfl

/-- The walk ends after precisely `k` copies of the step vector. -/
@[simp] theorem walk_last (a d : Point) (k : ℕ) :
    (walk a d k).getLast? = some (a + k • d) := by
  induction k generalizing a with
  | zero => simp [walk]
  | succ k ih =>
    rw [walk, List.getLast?_cons, ih]
    simp only [Option.getD_some]
    congr 1
    rw [add_smul, one_smul]
    abel

private theorem support_cons_of_head (a b : Point) {r : Route} (h : r.head? = some b) :
    support (a :: r) = segment a b ∪ support r := by
  cases r with
  | nil => simp at h
  | cons c r =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst c
    exact support_cons_cons a b r

/-- A step vector in one of the four cardinal unit directions. -/
def UnitVector (d : Point) : Prop :=
  d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)

private theorem segment_step_union (a d : Point) (k : ℕ) (hd : UnitVector d) :
    segment a (a + d) ∪ segment (a + d) (a + (k + 1) • d) =
      segment a (a + (k + 1) • d) := by
  rcases a with ⟨x, y⟩
  rcases hd with rfl | rfl | rfl | rfl
  all_goals ext p
  all_goals norm_num [segment, realPoint, Prod.smul_mk, nsmul_eq_mul]
  all_goals
    first
    | rw [mem_horizontal, mem_horizontal, mem_horizontal]
    | rw [mem_vertical, mem_vertical, mem_vertical]
  all_goals have hk : (0 : ℝ) ≤ k := by positivity
  all_goals simp only [Set.mem_uIcc]
  all_goals grind

/-- Cardinal walks cover exactly the original continuous segment. -/
theorem support_walk (a d : Point) (k : ℕ) (hd : UnitVector d) :
    support (walk a d k) = segment a (a + k • d) := by
  induction k generalizing a with
  | zero => simp [walk, support, segment, List.consecutivePairs]
  | succ k ih =>
    rw [walk, support_cons_of_head a (a + d) (walk_head _ _ _), ih]
    have heq : a + d + k • d = a + (k + 1) • d := by rw [add_smul, one_smul]; abel
    rw [heq]
    exact segment_step_union a d k hd

private theorem consecutivePairs_walk (a d : Point) (k : ℕ) :
    (walk a d (k + 1)).consecutivePairs =
      (a, a + d) :: (walk (a + d) d k).consecutivePairs := by
  cases k <;> rfl

/-- Every consecutive pair in a repeated walk is exactly one prescribed step. -/
theorem walk_step {a d : Point} {k : ℕ} {e : Point × Point}
    (he : e ∈ (walk a d k).consecutivePairs) : e.2 = e.1 + d := by
  induction k generalizing a with
  | zero => simp [walk, List.consecutivePairs] at he
  | succ k ih =>
    rw [consecutivePairs_walk] at he
    rcases List.mem_cons.1 he with rfl | he
    · rfl
    · exact ih he

/-- Cardinal steps have Manhattan length one. -/
theorem length_add_unit (a d : Point) (hd : UnitVector d) : length a (a + d) = 1 := by
  rcases a with ⟨x, y⟩
  rcases hd with rfl | rfl | rfl | rfl <;> simp [length]

/-- Every consecutive pair of a cardinal walk is unit-adjacent. -/
theorem walk_unit {a d : Point} {k : ℕ} (hd : UnitVector d) {e : Point × Point}
    (he : e ∈ (walk a d k).consecutivePairs) : length e.1 e.2 = 1 := by
  rw [walk_step he]
  exact length_add_unit _ _ hd

/-- A `k`-step cardinal walk has exactly `k` units of wire. -/
theorem wireLength_walk (a d : Point) (k : ℕ) (hd : UnitVector d) :
    wireLength (walk a d k) = k := by
  induction k generalizing a with
  | zero => simp [walk, wireLength, List.consecutivePairs]
  | succ k ih =>
    simp only [wireLength, consecutivePairs_walk, List.map_cons, List.sum_cons]
    rw [length_add_unit a d hd, ← wireLength, ih]
    omega

/-- Cardinal direction from `a` toward `b`; equal points use an arbitrary unit direction. -/
def direction (a b : Point) : Point :=
  if a.1 < b.1 then (1, 0) else if b.1 < a.1 then (-1, 0) else
    if a.2 < b.2 then (0, 1) else (0, -1)

/-- The chosen direction is always a cardinal unit vector. -/
theorem direction_unit (a b : Point) : UnitVector (direction a b) := by
  unfold direction UnitVector
  split_ifs <;> simp

/-- An axis-aligned displacement is its Manhattan length times its chosen unit direction. -/
theorem add_length_direction {a b : Point} (h : a.1 = b.1 ∨ a.2 = b.2) :
    a + length a b • direction a b = b := by
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by'⟩
  unfold direction
  split_ifs <;> ext <;> norm_num [length, nsmul_eq_mul] <;>
    (try simp only [abs_eq_max_neg]) <;> omega

/-- Unit subdivision of one segment, including both endpoints. -/
def segmentWalk (a b : Point) : Route := walk a (direction a b) (length a b)

/-- Segment subdivision uses exactly one more point than its Manhattan length. -/
@[simp] theorem segmentWalk_length (a b : Point) :
    (segmentWalk a b).length = length a b + 1 := walk_length ..

/-- Segment subdivision preserves the first endpoint. -/
@[simp] theorem segmentWalk_head (a b : Point) : (segmentWalk a b).head? = some a := walk_head ..

/-- Segment subdivision preserves the last endpoint of every axis-aligned segment. -/
theorem segmentWalk_last {a b : Point} (h : a.1 = b.1 ∨ a.2 = b.2) :
    (segmentWalk a b).getLast? = some b := by
  rw [segmentWalk, walk_last, add_length_direction h]

/-- The subdivision covers the entire original real segment, without adding points. -/
theorem support_segmentWalk {a b : Point} (h : a.1 = b.1 ∨ a.2 = b.2) :
    support (segmentWalk a b) = segment a b := by
  rw [segmentWalk, support_walk _ _ _ (direction_unit _ _), add_length_direction h]

/-- Each subdivided segment has unit Manhattan length. -/
theorem segmentWalk_unit (a b : Point) {e : Point × Point}
    (he : e ∈ (segmentWalk a b).consecutivePairs) : length e.1 e.2 = 1 :=
  walk_unit (direction_unit a b) he

/-- Segment subdivision preserves wire length exactly. -/
theorem wireLength_segmentWalk (a b : Point) : wireLength (segmentWalk a b) = length a b :=
  wireLength_walk _ _ _ (direction_unit _ _)

private theorem consecutivePairs_join {q r : Route} {p : Point}
    (hq : q.getLast? = some p) (hr : r.head? = some p) :
    (q ++ r.tail).consecutivePairs = q.consecutivePairs ++ r.consecutivePairs := by
  induction q with
  | nil => simp at hq
  | cons a q ih =>
    cases q with
    | nil =>
      cases r with
      | nil => simp at hr
      | cons b r =>
        simp only [List.getLast?_singleton, Option.some.injEq] at hq
        simp only [List.head?_cons, Option.some.injEq] at hr
        subst a
        subst b
        rfl
    | cons b q =>
      have hq' : (b :: q).getLast? = some p := by
        simpa only [List.getLast?_cons_cons] using hq
      change (a, b) :: ((b :: q) ++ r.tail).consecutivePairs =
        (a, b) :: ((b :: q).consecutivePairs ++ r.consecutivePairs)
      rw [ih hq']

private theorem support_join {q r : Route} {p : Point}
    (hq : q.getLast? = some p) (hr : r.head? = some p) :
    support (q ++ r.tail) = support q ∪ support r := by
  have hmem := List.mem_of_getLast? hq
  have hpairs := consecutivePairs_join hq hr
  cases r with
  | nil => simp at hr
  | cons b r =>
    simp only [List.head?_cons, Option.some.injEq] at hr
    subst b
    ext z
    simp only [support, Set.mem_ofPred_eq, List.mem_append, List.mem_cons,
      List.tail_cons, Set.mem_union, or_and_right, exists_or, exists_eq_left]
    aesop

private theorem last_join {q r : Route} {p : Point}
    (hq : q.getLast? = some p) (hr : r.head? = some p) :
    (q ++ r.tail).getLast? = r.getLast? := by
  cases r with
  | nil => simp at hr
  | cons b r =>
    cases r with
    | nil =>
      simp only [List.head?_cons, Option.some.injEq] at hr
      subst b
      simpa using hq
    | cons c r =>
      simp [List.getLast?_append,
        List.getLast?_eq_some_getLast (l := c :: r) (by simp)]

private theorem wireLength_join {q r : Route} {p : Point}
    (hq : q.getLast? = some p) (hr : r.head? = some p) :
    wireLength (q ++ r.tail) = wireLength q + wireLength r := by
  simp only [wireLength, consecutivePairs_join hq hr, List.map_append, List.sum_append]

/-- Replace each consecutive segment by its unit walk, retaining a shared endpoint once. -/
def subdivide : Route → Route
  | [] => []
  | [a] => [a]
  | a :: b :: r => segmentWalk a b ++ (subdivide (b :: r)).tail

/-- Subdivision preserves the first listed point, including the empty-route convention. -/
@[simp] theorem subdivide_head (r : Route) : (subdivide r).head? = r.head? := by
  cases r with
  | nil => rfl
  | cons a r =>
    cases r with
    | nil => rfl
    | cons b r => simp [subdivide, List.head?_append]

/-- The exact point count is wire length plus one for a nonempty route. -/
theorem subdivide_length (r : Route) :
    (subdivide r).length = wireLength r + if r = [] then 0 else 1 := by
  induction r with
  | nil => simp [subdivide, wireLength, List.consecutivePairs]
  | cons a r ih =>
    cases r with
    | nil => simp [subdivide, wireLength, List.consecutivePairs]
    | cons b r =>
      have hwire : wireLength (a :: b :: r) = length a b + wireLength (b :: r) := rfl
      simp only [subdivide, List.length_append, List.length_tail, segmentWalk_length,
        List.cons_ne_nil, ↓reduceIte] at ih ⊢
      rw [hwire]
      omega

/-- Subdivision preserves the final endpoint of an orthogonal route. -/
theorem subdivide_last {r : Route} (hr : IsOrthogonal r) :
    (subdivide r).getLast? = r.getLast? := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r =>
      have hab := (hr (a, b) (by simp [List.consecutivePairs])).1
      have htail : IsOrthogonal (b :: r) := by
        intro e he
        exact hr e (by simpa only [List.consecutivePairs, List.tail_cons,
          List.zip_cons_cons, List.mem_cons] using Or.inr he)
      rw [subdivide, last_join (segmentWalk_last hab) (subdivide_head (b :: r)), ih htail,
        List.getLast?_cons_cons]

/-- Subdivision preserves the complete real support of every orthogonal route. -/
theorem support_subdivide {r : Route} (hr : IsOrthogonal r) :
    support (subdivide r) = support r := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r =>
      have hab := (hr (a, b) (by simp [List.consecutivePairs])).1
      have htail : IsOrthogonal (b :: r) := by
        intro e he
        exact hr e (by simpa only [List.consecutivePairs, List.tail_cons,
          List.zip_cons_cons, List.mem_cons] using Or.inr he)
      rw [subdivide, support_join (segmentWalk_last hab) (subdivide_head (b :: r)),
        support_segmentWalk hab, ih htail, support_cons_cons]

/-- Every consecutive pair in the subdivided orthogonal route is a unit grid step. -/
theorem subdivide_unit {r : Route} (hr : IsOrthogonal r) {e : Point × Point}
    (he : e ∈ (subdivide r).consecutivePairs) : length e.1 e.2 = 1 := by
  induction r with
  | nil => simp [subdivide, List.consecutivePairs] at he
  | cons a r ih =>
    cases r with
    | nil => simp [subdivide, List.consecutivePairs] at he
    | cons b r =>
      have hab := (hr (a, b) (by simp [List.consecutivePairs])).1
      have htail : IsOrthogonal (b :: r) := by
        intro e he
        exact hr e (by simpa only [List.consecutivePairs, List.tail_cons,
          List.zip_cons_cons, List.mem_cons] using Or.inr he)
      rw [subdivide, consecutivePairs_join (segmentWalk_last hab) (subdivide_head (b :: r)),
        List.mem_append] at he
      rcases he with he | he
      · exact segmentWalk_unit a b he
      · exact ih htail he

/-- Unit subdivision preserves total Manhattan wire length exactly. -/
theorem wireLength_subdivide {r : Route} (hr : IsOrthogonal r) :
    wireLength (subdivide r) = wireLength r := by
  induction r with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r =>
      have hab := (hr (a, b) (by simp [List.consecutivePairs])).1
      have htail : IsOrthogonal (b :: r) := by
        intro e he
        exact hr e (by simpa only [List.consecutivePairs, List.tail_cons,
          List.zip_cons_cons, List.mem_cons] using Or.inr he)
      rw [subdivide, wireLength_join (segmentWalk_last hab) (subdivide_head (b :: r)),
        wireLength_segmentWalk, ih htail]
      rfl

/-- A pair of lattice points one Manhattan unit apart forms a proper axis-aligned segment. -/
theorem axisAligned_of_length_eq_one {a b : Point} (h : length a b = 1) : AxisAligned a b := by
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by'⟩
  simp only [length] at h
  simp only [AxisAligned, ne_eq, Prod.mk.injEq]
  omega

/-- Unit subdivision is itself a proper orthogonal route. -/
theorem subdivide_orthogonal {r : Route} (hr : IsOrthogonal r) : IsOrthogonal (subdivide r) :=
  fun _ he => axisAligned_of_length_eq_one (subdivide_unit hr he)

end Cslib.Orthogonal
