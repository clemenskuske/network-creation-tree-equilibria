import Lax899194.TreeNashEfficiency
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

namespace Lax899194Proofs

open Lax899194.NetworkCreationGame Lax899194.PlayerCost Lax899194.SocialCost
open Lax899194.NashEquilibrium Lax899194.InefficiencyRatio
open scoped NNReal ENNReal BigOperators

variable {n : ℕ}

noncomputable def distanceSum (G : SimpleGraph (Fin n)) (i : Fin n) : ℝ :=
  ∑ j : Fin n, (G.dist i j : ℝ)

noncomputable def finiteCost (α : ℝ≥0) (s : Profile n) (i : Fin n) : ℝ :=
  (α : ℝ) * (s i).val.ncard + distanceSum (graph s) i

lemma distance_coe (G : SimpleGraph (Fin n)) (hG : G.Connected) (i j : Fin n) :
    (G.edist i j).toENNReal = (G.dist i j : ℝ≥0∞) := by
  rw [← (hG i j).coe_dist_eq_edist]
  simp

lemma playerCost_ne_top (α : ℝ≥0) (s : Profile n) (hs : (graph s).Connected)
    (i : Fin n) : playerCost α s i ≠ ⊤ := by
  unfold playerCost
  simp only [distance_coe _ hs, ENNReal.add_ne_top, ENNReal.sum_ne_top]
  constructor
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp)
  · simp

lemma playerCost_toReal (α : ℝ≥0) (s : Profile n) (hs : (graph s).Connected)
    (i : Fin n) : (playerCost α s i).toReal = finiteCost α s i := by
  unfold playerCost finiteCost distanceSum
  simp only [distance_coe _ hs]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp))
    (ENNReal.sum_ne_top.mpr (by simp))]
  rw [ENNReal.toReal_sum (by simp)]
  simp

lemma socialCost_ne_top (α : ℝ≥0) (s : Profile n) (hs : (graph s).Connected) :
    socialCost α s ≠ ⊤ := by
  exact ENNReal.sum_ne_top.mpr (fun i _ => playerCost_ne_top α s hs i)

lemma socialCost_toReal (α : ℝ≥0) (s : Profile n) (hs : (graph s).Connected) :
    (socialCost α s).toReal = ∑ i : Fin n, finiteCost α s i := by
  unfold socialCost
  rw [ENNReal.toReal_sum (fun i _ => playerCost_ne_top α s hs i)]
  simp_rw [playerCost_toReal α s hs]

noncomputable def insertLink (s : Profile n) (i r : Fin n) (hir : i ≠ r) : Profile n :=
  fun j => ⟨if j = i then insert r (s j).val else (s j).val, by
    split_ifs with hj
    · subst j; simp [hir, (s i).property]
    · exact (s j).property⟩

noncomputable def eraseLink (s : Profile n) (i r : Fin n) : Profile n :=
  fun j => ⟨if j = i then (s j).val \ {r} else (s j).val, by
    split_ifs
    · exact fun h => (s j).property h.1
    · exact (s j).property⟩

lemma insertLink_other (s : Profile n) (i r j : Fin n) (hir : i ≠ r) (hji : j ≠ i) :
    insertLink s i r hir j = s j := by
  apply Subtype.ext
  simp [insertLink, hji]

lemma graph_insertLink_ge (s : Profile n) (i r : Fin n) (hir : i ≠ r) :
    graph s ≤ graph (insertLink s i r hir) := by
  intro a b hab
  change b ∈ (s a).val ∨ a ∈ (s b).val at hab
  change b ∈ (insertLink s i r hir a).val ∨ a ∈ (insertLink s i r hir b).val
  by_cases ha : a = i <;> by_cases hb : b = i <;>
    subst_vars <;> simp [insertLink, *] at * <;> tauto

lemma graph_insertLink_adj (s : Profile n) (i r : Fin n) (hir : i ≠ r) :
    (graph (insertLink s i r hir)).Adj i r := by
  left
  simp [insertLink]

lemma graph_insertLink_connected (s : Profile n) (hs : (graph s).Connected)
    (i r : Fin n) (hir : i ≠ r) : (graph (insertLink s i r hir)).Connected :=
  hs.mono (graph_insertLink_ge s i r hir)

lemma insertLink_card_le (s : Profile n) (i r : Fin n) (hir : i ≠ r) :
    (insertLink s i r hir i).val.ncard ≤ (s i).val.ncard + 1 := by
  simp only [insertLink, Subtype.coe_mk]
  exact Set.ncard_insert_le _ _

lemma nash_finiteCost_le (α : ℝ≥0) (s t : Profile n) (hs : (graph s).Connected)
    (ht : (graph t).Connected) (hNash : IsNashEquilibrium α s) (i : Fin n)
    (hother : ∀ j : Fin n, j ≠ i → t j = s j) :
    finiteCost α s i ≤ finiteCost α t i := by
  rw [← playerCost_toReal α s hs, ← playerCost_toReal α t ht]
  exact (ENNReal.toReal_le_toReal (playerCost_ne_top α s hs i)
    (playerCost_ne_top α t ht i)).mpr (hNash i t hother)

end Lax899194Proofs
