import Lax899194Proofs.Ownership
import Lax899194Proofs.NashDistance

namespace Lax899194Proofs

open Lax899194.NetworkCreationGame Lax899194.PlayerCost Lax899194.SocialCost
open Lax899194.NashEquilibrium Lax899194.InefficiencyRatio
open scoped NNReal ENNReal BigOperators

variable {n : ℕ}

lemma socialCost_eq_top_of_not_connected (hn : 0 < n) (α : ℝ≥0) (s : Profile n)
    (hs : ¬(graph s).Connected) : socialCost α s = ⊤ := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h : ¬∀ i j : Fin n, (graph s).Reachable i j := fun h => hs ⟨h⟩
  push Not at h
  obtain ⟨i, j, hij⟩ := h
  have hd : ((graph s).edist i j).toENNReal = ⊤ := by
    simp [(graph s).edist_eq_top_of_not_reachable hij]
  have hp : playerCost α s i = ⊤ := by
    unfold playerCost
    rw [ENNReal.sum_eq_top.mpr ⟨j, Finset.mem_univ j, hd⟩, add_top]
  exact ENNReal.sum_eq_top.mpr ⟨i, Finset.mem_univ i, hp⟩

lemma distanceSum_erase (G : SimpleGraph (Fin n)) (i : Fin n) :
    distanceSum G i = ∑ j ∈ Finset.univ.erase i, (G.dist i j : ℝ) := by
  classical
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun j => (G.dist i j : ℝ)) (Finset.mem_univ i)
  simp_all [distanceSum]

lemma connected_distanceSum_lower (G : SimpleGraph (Fin n)) (hG : G.Connected) (i : Fin n) :
    (n - 1 : ℕ) ≤ distanceSum G i := by
  classical
  rw [distanceSum_erase]
  have h : (∑ _j ∈ (Finset.univ : Finset (Fin n)).erase i, (1 : ℝ)) ≤
      ∑ j ∈ Finset.univ.erase i, (G.dist i j : ℝ) := by
    apply Finset.sum_le_sum
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    exact_mod_cast hG.pos_dist_of_ne hji.symm
  simpa using h

lemma finiteCost_sum (α : ℝ≥0) (s : Profile n) :
    (∑ i : Fin n, finiteCost α s i) =
      (α : ℝ) * (∑ i : Fin n, (s i).val.ncard : ℕ) +
        ∑ i : Fin n, distanceSum (graph s) i := by
  simp [finiteCost, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma connected_socialCost_lower_real (α : ℝ≥0) (s : Profile n)
    (hs : (graph s).Connected) :
    (α : ℝ) * (n - 1 : ℕ) + (n : ℝ) * (n - 1 : ℕ) ≤ (socialCost α s).toReal := by
  rw [socialCost_toReal α s hs, finiteCost_sum]
  have hp : (n - 1 : ℕ) ≤ (∑ i : Fin n, (s i).val.ncard : ℕ) :=
    connected_purchase_count s hs
  have hpR : ((n - 1 : ℕ) : ℝ) ≤ (∑ i : Fin n, (s i).val.ncard : ℕ) :=
    by exact_mod_cast hp
  have hd := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    connected_distanceSum_lower (graph s) hs i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hd
  exact add_le_add (mul_le_mul_of_nonneg_left hpR α.coe_nonneg) hd

noncomputable def costLowerBound (n : ℕ) (α : ℝ≥0) : ℝ≥0∞ :=
  (α : ℝ≥0∞) * (n - 1 : ℕ) + (n : ℝ≥0∞) * (n - 1 : ℕ)

lemma costLowerBound_ne_top (n : ℕ) (α : ℝ≥0) : costLowerBound n α ≠ ⊤ := by
  unfold costLowerBound
  finiteness

lemma costLowerBound_toReal (n : ℕ) (α : ℝ≥0) :
    (costLowerBound n α).toReal =
      (α : ℝ) * (n - 1 : ℕ) + (n : ℝ) * (n - 1 : ℕ) := by
  unfold costLowerBound
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_natCast]

lemma socialCost_lower (hn : 0 < n) (α : ℝ≥0) (s : Profile n) :
    costLowerBound n α ≤ socialCost α s := by
  by_cases hs : (graph s).Connected
  · apply (ENNReal.toReal_le_toReal (costLowerBound_ne_top n α)
      (socialCost_ne_top α s hs)).mp
    rw [costLowerBound_toReal]
    exact connected_socialCost_lower_real α s hs
  · rw [socialCost_eq_top_of_not_connected hn α s hs]
    exact le_top

lemma optimalCost_lower (hn : 0 < n) (α : ℝ≥0) :
    costLowerBound n α ≤ optimalCost n α := by
  exact le_iInf (socialCost_lower hn α)

lemma tree_nash_distanceSum_upper (n : ℕ) (hn : 2 ≤ n) (α : ℝ≥0) (s : Profile n)
    (hNash : IsNashEquilibrium α s) (hTree : (graph s).IsTree) (i : Fin n) :
    distanceSum (graph s) i ≤ (n - 1 : ℕ) * (3 + 4 * (α : ℝ) / n) := by
  classical
  rw [distanceSum_erase]
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n)).erase i) =>
    tree_nash_dist_bound n hn α s hNash hTree i j)
  simpa only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

lemma tree_nash_socialCost_upper (n : ℕ) (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (s : Profile n) (hNash : IsNashEquilibrium α s) (hTree : (graph s).IsTree) :
    (socialCost α s).toReal ≤
      5 * (α : ℝ) * (n - 1 : ℕ) + 3 * (n : ℝ) * (n - 1 : ℕ) := by
  rw [socialCost_toReal α s hTree.connected, finiteCost_sum,
    tree_nash_purchase_count α hα s hNash hTree]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    tree_nash_distanceSum_upper n hn α s hNash hTree i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have he : (n : ℝ) * ((n - 1 : ℕ) * (3 + 4 * (α : ℝ) / n)) =
      3 * (n : ℝ) * (n - 1 : ℕ) + 4 * (α : ℝ) * (n - 1 : ℕ) := by
    field_simp
  rw [he] at h
  linarith

end Lax899194Proofs
