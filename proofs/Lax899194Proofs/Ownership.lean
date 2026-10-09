import Lax899194Proofs.Costs
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace Lax899194Proofs

open Lax899194.NetworkCreationGame Lax899194.NashEquilibrium
open scoped NNReal ENNReal BigOperators

variable {n : ℕ}

lemma eraseLink_other (s : Profile n) (i r j : Fin n) (hji : j ≠ i) :
    eraseLink s i r j = s j := by
  apply Subtype.ext
  simp [eraseLink, hji]

lemma graph_eraseLink_eq (s : Profile n) (i r : Fin n)
    (hr : i ∈ (s r).val) : graph (eraseLink s i r) = graph s := by
  have hir : i ≠ r := by
    intro h; subst r; exact (s i).property hr
  apply SimpleGraph.ext
  funext a b
  apply propext
  change (b ∈ (eraseLink s i r a).val ∨ a ∈ (eraseLink s i r b).val) ↔
    (b ∈ (s a).val ∨ a ∈ (s b).val)
  by_cases ha : a = i
  · subst a
    by_cases hb : b = i
    · subst b; simp [eraseLink, (s i).property]
    · by_cases hbr : b = r
      · subst b; simp [eraseLink, hir.symm, hr]
      · simp [eraseLink, hb, hbr]
  · by_cases hb : b = i
    · subst b
      by_cases har : a = r
      · subst a; simp [eraseLink, hir.symm, hr]
      · simp [eraseLink, ha, har]
    · simp [eraseLink, ha, hb]

lemma nash_no_double_purchase (α : ℝ≥0) (hα : 0 < α) (s : Profile n)
    (hs : (graph s).Connected) (hNash : IsNashEquilibrium α s)
    (i r : Fin n) (hr : r ∈ (s i).val) : i ∉ (s r).val := by
  intro hi
  have he := graph_eraseLink_eq s i r hi
  have ht : (graph (eraseLink s i r)).Connected := by rw [he]; exact hs
  have hc := nash_finiteCost_le α s (eraseLink s i r) hs ht hNash i
    (fun j hj => eraseLink_other s i r j hj)
  have hcard : (eraseLink s i r i).val.ncard + 1 = (s i).val.ncard := by
    simp only [eraseLink, Subtype.coe_mk]
    exact Set.ncard_sdiff_singleton_add_one hr
  have hcardR : ((eraseLink s i r i).val.ncard : ℝ) + 1 = (s i).val.ncard :=
    by exact_mod_cast hcard
  have hαR : (0 : ℝ) < α := by exact_mod_cast hα
  unfold finiteCost at hc
  rw [he] at hc
  nlinarith

abbrev Purchase (s : Profile n) := Σ i : Fin n, {j : Fin n // j ∈ (s i).val}

def purchaseEdge (s : Profile n) (p : Purchase s) : (graph s).edgeSet :=
  ⟨s(p.1, p.2.val), (SimpleGraph.mem_edgeSet (graph s)).mpr (Or.inl p.2.property)⟩

lemma purchaseEdge_surjective (s : Profile n) : Function.Surjective (purchaseEdge s) := by
  intro e
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf i j =>
    rcases (SimpleGraph.mem_edgeSet (graph s)).mp he with h | h
    · exact ⟨⟨i, j, h⟩, rfl⟩
    · refine ⟨⟨j, i, h⟩, ?_⟩
      apply Subtype.ext
      exact Sym2.eq_swap

lemma purchase_card (s : Profile n) : Nat.card (Purchase s) = ∑ i : Fin n, (s i).val.ncard := by
  classical
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.card_eq_fintype_card, Set.fintypeCard_eq_ncard]

lemma purchaseEdge_injective (s : Profile n)
    (hno : ∀ i r, r ∈ (s i).val → i ∉ (s r).val) :
    Function.Injective (purchaseEdge s) := by
  rintro ⟨i, j, hj⟩ ⟨a, b, hb⟩ he
  have h : s(i, j) = s(a, b) := congrArg Subtype.val he
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨hia, hjb⟩
  · rfl
  · subst a; subst b
    exact False.elim (hno i j hj hb)

lemma connected_purchase_count (s : Profile n) (hs : (graph s).Connected) :
    n - 1 ≤ ∑ i : Fin n, (s i).val.ncard := by
  have he := hs.card_vert_le_card_edgeSet_add_one
  have hp := Nat.card_le_card_of_surjective (purchaseEdge s) (purchaseEdge_surjective s)
  rw [purchase_card] at hp
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at he
  omega

lemma tree_nash_purchase_count (α : ℝ≥0) (hα : 0 < α) (s : Profile n)
    (hNash : IsNashEquilibrium α s) (hTree : (graph s).IsTree) :
    ∑ i : Fin n, (s i).val.ncard = n - 1 := by
  have hp := Nat.card_congr (Equiv.ofBijective (purchaseEdge s)
    ⟨purchaseEdge_injective s (nash_no_double_purchase α hα s hTree.connected hNash),
      purchaseEdge_surjective s⟩)
  rw [purchase_card] at hp
  have he := (SimpleGraph.isTree_iff_connected_and_card.mp hTree).2
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at he
  omega

end Lax899194Proofs
