import Lax899194.NetworkCreationGame
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
---
title: Individual cost in the network creation game
type: definition
---
For an edge price $\alpha>0$, player $i$ has cost
$c_i(s)=\alpha|s_i|+\sum_j d_{G[s]}(i,j)$.
The distance is the length of a shortest path, and is infinite if there is no
path. A player pays for every edge it purchases, including an edge also
purchased by its other endpoint.

# Formalization notes

Costs take values in the extended nonnegative reals so that disconnected
networks retain the infinite penalty. `SimpleGraph.edist` supplies the graph
distance, and `ENat.toENNReal` preserves both finite distances and infinity.
The edge price is a finite nonnegative real; the theorem assumes it is positive.
-/

namespace Lax899194.PlayerCost

open Lax899194.NetworkCreationGame
open scoped BigOperators NNReal ENNReal

/-- Edge expenditure plus the sum of distances from player `i` to all players. -/
noncomputable def playerCost {n : ℕ} (α : ℝ≥0) (s : Profile n)
    (i : Fin n) : ℝ≥0∞ :=
  (α : ℝ≥0∞) * (s i).val.ncard +
    ∑ j : Fin n, ((graph s).edist i j).toENNReal

end Lax899194.PlayerCost
