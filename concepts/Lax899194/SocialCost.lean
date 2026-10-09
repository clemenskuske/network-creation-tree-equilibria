import Lax899194.PlayerCost

/-!
---
title: Social cost
type: definition
---
The social cost of a strategy profile is the sum of all players' individual
costs: $C(s)=\sum_i c_i(s)$. Distances are counted over ordered pairs of
players. An edge purchased by both endpoints is charged twice.

# Formalization notes

Social cost is defined on profiles so that it accounts for who purchases each
edge. The graph alone does not determine the expenditure when both endpoints
purchase an edge. No absence of double purchases is assumed in this definition.
-/

namespace Lax899194.SocialCost

open Lax899194.NetworkCreationGame Lax899194.PlayerCost
open scoped BigOperators

/-- The sum of all players' individual costs, with distances counted in both directions. -/
noncomputable def socialCost {n : ℕ} (α : ℝ≥0) (s : Profile n) : ℝ≥0∞ :=
  ∑ i : Fin n, playerCost α s i

end Lax899194.SocialCost
