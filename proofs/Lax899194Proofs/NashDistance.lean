import Lax899194Proofs.Costs
import Lax899194Proofs.TreeGeometry

namespace Lax899194Proofs

open Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped NNReal ENNReal BigOperators

variable {n : ℕ}

lemma insertLink_dist_le (s : Profile n) (hs : (graph s).Connected)
    (i r : Fin n) (hir : i ≠ r) (v : Fin n) :
    (graph (insertLink s i r hir)).dist i v ≤
      min ((graph s).dist i v) (1 + (graph s).dist r v) := by
  apply le_min
  · exact (hs i v).dist_anti (graph_insertLink_ge s i r hir)
  · have hc := graph_insertLink_connected s hs i r hir
    have h := hc.dist_triangle (u := i) (v := r) (w := v)
    have he : (graph (insertLink s i r hir)).dist i r = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr (graph_insertLink_adj s i r hir)
    have hrv := (hs r v).dist_anti (graph_insertLink_ge s i r hir)
    omega

noncomputable def linkSaving (G : SimpleGraph (Fin n)) (i r v : Fin n) : ℝ :=
  (G.dist i v : ℝ) - min (G.dist i v : ℝ) (1 + (G.dist r v : ℝ))

lemma linkSaving_nonneg (G : SimpleGraph (Fin n)) (i r v : Fin n) :
    0 ≤ linkSaving G i r v := by
  exact sub_nonneg.mpr (min_le_left _ _)

lemma nash_linkSaving_sum_le (α : ℝ≥0) (s : Profile n) (hs : (graph s).Connected)
    (hNash : IsNashEquilibrium α s) (i r : Fin n) (hir : i ≠ r) :
    (∑ v : Fin n, linkSaving (graph s) i r v) ≤ (α : ℝ) := by
  have h := nash_finiteCost_le α s (insertLink s i r hir) hs
    (graph_insertLink_connected s hs i r hir) hNash i
    (fun j hj => insertLink_other s i r j hir hj)
  have hcard : ((insertLink s i r hir i).val.ncard : ℝ) ≤ (s i).val.ncard + 1 :=
    by exact_mod_cast insertLink_card_le s i r hir
  have hdist : distanceSum (graph (insertLink s i r hir)) i ≤
      ∑ v : Fin n, min ((graph s).dist i v : ℝ) (1 + ((graph s).dist r v : ℝ)) := by
    apply Finset.sum_le_sum
    intro v _
    exact_mod_cast insertLink_dist_le s hs i r hir v
  have hmul := mul_le_mul_of_nonneg_left hcard α.coe_nonneg
  unfold finiteCost at h
  unfold linkSaving
  rw [Finset.sum_sub_distrib]
  change distanceSum (graph s) i - _ ≤ _
  nlinarith

lemma tree_nash_dist_bound (n : ℕ) (hn : 2 ≤ n) (α : ℝ≥0) (s : Profile n)
    (hNash : IsNashEquilibrium α s) (hTree : (graph s).IsTree) (a b : Fin n) :
    ((graph s).dist a b : ℝ) ≤ 3 + 4 * (α : ℝ) / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  by_cases hsmall : (graph s).dist a b ≤ 3
  · have hsmallR : ((graph s).dist a b : ℝ) ≤ 3 := by exact_mod_cast hsmall
    have hnonneg : 0 ≤ 4 * (α : ℝ) / n := by positivity
    linarith
  obtain ⟨r, hleft, hright, hsep⟩ := tree_midpoint hTree a b
  let k := (graph s).dist a b / 2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have har : a ≠ r := by
    intro h; subst r
    simp only [SimpleGraph.dist_self] at hleft
    dsimp [k] at hk; omega
  have hbr : b ≠ r := by
    intro h; subst r
    simp only [SimpleGraph.dist_self] at hright
    dsimp [k] at hk; omega
  have ha := nash_linkSaving_sum_le α s hTree.connected hNash a r har
  have hb := nash_linkSaving_sum_le α s hTree.connected hNash b r hbr
  have hpoint (v : Fin n) : (k : ℝ) - 1 ≤
      linkSaving (graph s) a r v + linkSaving (graph s) b r v := by
    have hna := linkSaving_nonneg (graph s) a r v
    have hnb := linkSaving_nonneg (graph s) b r v
    rcases hsep v with hv | hv
    · have hvR : ((graph s).dist a v : ℝ) =
          (k : ℝ) + ((graph s).dist r v : ℝ) := by
        rw [hleft] at hv
        exact_mod_cast hv
      have hm := min_le_right ((graph s).dist a v : ℝ)
        (1 + ((graph s).dist r v : ℝ))
      unfold linkSaving at *
      linarith
    · have hvR : ((graph s).dist b v : ℝ) =
          ((graph s).dist b r : ℝ) + ((graph s).dist r v : ℝ) := by exact_mod_cast hv
      have hrR : (k : ℝ) ≤ (graph s).dist b r := by exact_mod_cast hright
      have hm := min_le_right ((graph s).dist b v : ℝ)
        (1 + ((graph s).dist r v : ℝ))
      unfold linkSaving at *
      linarith
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin n))) => hpoint v)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_add_distrib] at hsum
  have hD : (graph s).dist a b ≤ 2 * k + 1 := by dsimp [k]; omega
  have hDR : ((graph s).dist a b : ℝ) ≤ 2 * (k : ℝ) + 1 := by exact_mod_cast hD
  have hcalc : ((graph s).dist a b : ℝ) - 3 ≤ 4 * (α : ℝ) / n :=
    (le_div_iff₀ hnpos).mpr (by nlinarith)
  linarith

end Lax899194Proofs
