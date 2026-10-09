import Lax899194Proofs.SocialBounds

namespace Lax899194Proofs

open Lax899194.NetworkCreationGame Lax899194.PlayerCost Lax899194.SocialCost
open Lax899194.NashEquilibrium Lax899194.InefficiencyRatio
open scoped NNReal ENNReal BigOperators

/--
---
conclusion: Lax899194.TreeNashEfficiency.statement
---
Every tree Nash equilibrium has inefficiency strictly below five.

# Proof strategy

For a path of length $D$, let $r$ be its integer midpoint. Every vertex lies
beyond $r$ from at least one endpoint. If both endpoints buy a link to $r$,
their combined distance savings are at least $n(\lfloor D/2\rfloor-1)$.
The two Nash inequalities bound this by $2\alpha$, giving
$D\le 3+4\alpha/n$.

Positive edge price rules out duplicate purchases at equilibrium. A tree
therefore has $n-1$ purchases, and its social cost is at most
$5\alpha(n-1)+3n(n-1)$. Every connected profile has social cost at least
$\alpha(n-1)+n(n-1)$; disconnected profiles have infinite cost. Since
$n\ge2$, the former upper bound is strictly less than five times the latter
lower bound. The optimum is positive and finite, so division proves the claim.

# Attribution

The conclusion is Theorem 3 of Fabrikant, Luthra, Maneva, Papadimitriou,
and Shenker, *On a Network Creation Game* (PODC 2003, p. 350).
This proof uses a midpoint argument instead of the paper's centroid argument.
Tree paths, distances, and finite edge counting use mathlib.
-/
theorem tree_nash_efficiency (n : ℕ) (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (s : Profile n) (hNash : IsNashEquilibrium α s) (hTree : (graph s).IsTree) :
    inefficiencyRatio α s < 5 := by
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn1R : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (by omega : 0 < n - 1)
  have hfinite := socialCost_ne_top α s hTree.connected
  have hoptfinite : optimalCost n α ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (iInf_le (fun t : Profile n => socialCost α t) s)
  have hlower := ENNReal.toReal_mono hoptfinite (optimalCost_lower hnpos α)
  rw [costLowerBound_toReal] at hlower
  have hbasepos : (0 : ℝ) < (α : ℝ) * (n - 1 : ℕ) + (n : ℝ) * (n - 1 : ℕ) := by
    have h₁ := mul_nonneg α.coe_nonneg hn1R.le
    have h₂ := mul_pos hnR hn1R
    linarith
  have hoptzero : optimalCost n α ≠ 0 := by
    intro h
    simp only [h, ENNReal.toReal_zero] at hlower
    linarith
  have hupper := tree_nash_socialCost_upper n hn α hα s hNash hTree
  have hstrict : (socialCost α s).toReal < 5 * (optimalCost n α).toReal := by
    have hgap := mul_pos hnR hn1R
    nlinarith
  unfold inefficiencyRatio
  apply (ENNReal.div_lt_iff (Or.inl hoptzero) (Or.inl hoptfinite)).mpr
  apply (ENNReal.toReal_lt_toReal hfinite
    (ENNReal.mul_ne_top (by norm_num) hoptfinite)).mp
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hstrict

end Lax899194Proofs
