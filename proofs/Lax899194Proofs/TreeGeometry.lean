import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

namespace Lax899194Proofs

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

lemma tree_path_length (hG : G.IsTree) {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) : p.length = G.dist a b := by
  obtain ⟨q, hq, hlen⟩ := hG.connected.exists_path_of_dist a b
  have heq : p = q := Subtype.mk.inj
    (hG.isAcyclic.subsingleton_path a b |>.elim ⟨p, hp⟩ ⟨q, hq⟩)
  simpa [heq] using hlen

lemma tree_dist_split (hG : G.IsTree) {a b r : V} {p : G.Walk a b}
    (hp : p.IsPath) (hr : r ∈ p.support) :
    G.dist a b = G.dist a r + G.dist r b := by
  obtain ⟨q, t, hq, ht, rfl⟩ := hp.mem_support_iff_exists_append.mp hr
  rw [← tree_path_length hG hp, Walk.length_append,
    tree_path_length hG hq, tree_path_length hG ht]

lemma tree_path_separation (hG : G.IsTree) {a b r : V} {p : G.Walk a b}
    (hp : p.IsPath) (hr : r ∈ p.support) (v : V) :
    G.dist a v = G.dist a r + G.dist r v ∨
      G.dist b v = G.dist b r + G.dist r v := by
  classical
  obtain ⟨q, hq, _⟩ := hG.connected.exists_path_of_dist a v
  obtain ⟨t, ht, _⟩ := hG.connected.exists_path_of_dist b v
  have hmem : r ∈ q.support ∨ r ∈ t.support := by
    let w := q.append t.reverse
    have heq : p = w.bypass := Subtype.mk.inj
      (hG.isAcyclic.subsingleton_path a b |>.elim ⟨p, hp⟩ ⟨w.bypass, w.bypass_isPath⟩)
    have hw : r ∈ w.support := w.support_bypass_subset_support (heq ▸ hr)
    simpa [w, Walk.mem_support_append_iff] using hw
  exact hmem.elim (fun h => Or.inl (tree_dist_split hG hq h))
    (fun h => Or.inr (tree_dist_split hG ht h))

lemma tree_midpoint (hG : G.IsTree) (a b : V) :
    ∃ r : V, G.dist a r = G.dist a b / 2 ∧
      G.dist a b / 2 ≤ G.dist b r ∧
      (∀ v : V, G.dist a v = G.dist a r + G.dist r v ∨
        G.dist b v = G.dist b r + G.dist r v) := by
  obtain ⟨p, hp, hlen⟩ := hG.connected.exists_path_of_dist a b
  let k := G.dist a b / 2
  let r := p.getVert k
  have hk : k ≤ p.length := by dsimp [k]; omega
  have hleft : G.dist a r = k := by
    have h := length_eq_dist_of_subwalk hlen (p.isSubwalk_take k)
    simpa [r, Walk.take_length, Nat.min_eq_left hk] using h.symm
  have hsplit := tree_dist_split hG hp (p.getVert_mem_support k)
  refine ⟨r, hleft, ?_, tree_path_separation hG hp (p.getVert_mem_support k)⟩
  change G.dist a b = G.dist a r + G.dist r b at hsplit
  rw [SimpleGraph.dist_comm (u := r) (v := b)] at hsplit
  dsimp [k] at hleft
  omega

end Lax899194Proofs
