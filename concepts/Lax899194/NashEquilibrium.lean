import Lax899194.PlayerCost

/-!
---
title: Pure Nash equilibrium
type: definition
---
A strategy profile is a pure Nash equilibrium when no player can reduce its
individual cost by changing its own strategy while all other players keep
their strategies. A deviation may replace the entire set of purchased edges.

# Formalization notes

The comparison is between costs in the two resulting networks, including
deviations that disconnect the network. Equality is allowed, so weak and
transient equilibria are included.

The displayed equilibrium inequality on p. 348 of the paper has its direction
reversed. We use cost minimization, as specified by the surrounding discussion
and explicitly by footnote 4 on p. 350: the current cost is at most the cost
after any unilateral deviation.
-/

namespace Lax899194.NashEquilibrium

open Lax899194.NetworkCreationGame Lax899194.PlayerCost
open scoped NNReal

/-- No unilateral replacement of a player's strategy lowers that player's cost. -/
def IsNashEquilibrium {n : ℕ} (α : ℝ≥0) (s : Profile n) : Prop :=
  ∀ (i : Fin n) (t : Profile n),
    (∀ j : Fin n, j ≠ i → t j = s j) →
      playerCost α s i ≤ playerCost α t i

end Lax899194.NashEquilibrium
