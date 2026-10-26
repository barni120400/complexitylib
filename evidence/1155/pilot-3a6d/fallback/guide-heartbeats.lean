/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import VersoManual
import Mathlib.Util.CountHeartbeats
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.CircuitSAT
import Complexity.Computability.Complexity.Problems.Clique
import Complexity.Computability.Complexity.Problems.Coloring
import Complexity.Computability.Complexity.Problems.ExactThreeSAT
import Complexity.Computability.Complexity.Problems.Hamiltonian.Directed
import Complexity.Computability.Complexity.Problems.Hamiltonian.Undirected
import Complexity.Computability.Complexity.Problems.IntegerProgramming
import Complexity.Computability.Complexity.Problems.Knapsack
import Complexity.Computability.Complexity.Problems.Partition
import Complexity.Computability.Complexity.Problems.PlanarThreeSATThree
import Complexity.Computability.Complexity.Problems.SubsetSum
import Complexity.Computability.Complexity.Problems.TSP
import Complexity.Computability.Complexity.Problems.ThreeSAT
import Complexity.Computability.Complexity.Problems.ThreeSATThree
import Complexity.Computability.Complexity.Problems.VertexCover
import Complexity.Tactic.PolyTime

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 80

open Cslib.Complexity Turing.MultiTapeTM

example : ComputableInPolyTime (fun p : List ℕ × ℕ => p.1.filter (· ≤ p.2))
    (encPair (encList encNat) encNat) (encList encNat) := by
  #count_heartbeats polytime
