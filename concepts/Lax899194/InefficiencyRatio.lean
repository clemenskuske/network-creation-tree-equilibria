import Lax899194.SocialCost

/-!
---
title: Inefficiency relative to the social optimum
type: definition
---
For fixed $n$ and edge price $\alpha$, the social optimum is the minimum
social cost over all strategy profiles. The inefficiency of a profile is
$\rho(s)=C(s)/\operatorname{OPT}(n,\alpha)$.

# Formalization notes

The optimum is encoded as an infimum. There are finitely many profiles and
the set of profiles is nonempty. For $n\ge2$, a connected profile exists and
every profile has social cost at least $n(n-1)>0$. Thus the infimum is an
attained finite minimum with a positive denominator in the theorem's domain.

The optimum ranges over all profiles, including networks with cycles. This
uses the actual social optimum for every edge price rather than prescribing
a star. The paper uses $\rho(G)$ for the ratio of an individual equilibrium;
the worst ratio over all equilibria is the price of anarchy.
-/

namespace Lax899194.InefficiencyRatio

open Lax899194.NetworkCreationGame Lax899194.SocialCost

/-- The least social cost among all strategy profiles with `n` players. -/
noncomputable def optimalCost (n : ℕ) (α : ℝ≥0) : ℝ≥0∞ :=
  ⨅ s : Profile n, socialCost α s

/-- The social cost of a profile divided by the social optimum for the same game. -/
noncomputable def inefficiencyRatio {n : ℕ} (α : ℝ≥0) (s : Profile n) : ℝ≥0∞ :=
  socialCost α s / optimalCost n α

end Lax899194.InefficiencyRatio
