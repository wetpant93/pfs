import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Pfs.IsSeparator

variable {V W : Type*} {u v w x y z : V} {G : SimpleGraph V} {G' : SimpleGraph W}
variable {S : Set V}


namespace SimpleGraph

def IsVertexConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  (∃ X : Set V, X.ncard > k) ∧ ¬(∃ S : Set V, S.Finite ∧ S.ncard < k ∧ G.IsSeparator S)


lemma IsVertexConnected.nonempty {k : ℕ} (h : G.IsVertexConnected k) : Nonempty V := by
  rcases h.1 with ⟨X, hX⟩
  have: X ≠ ∅ := by
    intro rfl
    rw[Set.ncard_empty] at hX
    contradiction
  obtain ⟨x⟩ := Set.nonempty_iff_empty_ne.2 this.symm
  use x


lemma IsVertexConnected.Connected {k : ℕ} (h : G.IsVertexConnected k) (hk : k > 0)
  : G.Connected := by
  have preconnected: G.Preconnected := by
    intro x y
    by_contra! h'
    apply h.2
    refine ⟨∅, (∅ : Set V).toFinite, by linarith[Set.ncard_empty V], IsSeparator.empty_sep h'⟩

  have := h.nonempty
  exact ⟨preconnected⟩


lemma exists_edge_of_connected_nontrivial [Nontrivial V]
  (h : G.Connected) : ∃ u v : V, G.Adj u v := by
  obtain ⟨u, v, h_neq⟩ := exists_pair_ne V
  obtain ⟨p⟩ := h.preconnected u v
  cases p with
  | nil => contradiction
  | cons h_adj _ => exact ⟨_, _, h_adj⟩

lemma IsVertexConnected.card {k : ℕ} [Fintype V] (h : G.IsVertexConnected k) :
  Fintype.card V > k:= by
  obtain ⟨X, _⟩ := h.1
  rw[Fintype.card_eq_nat_card, ← Set.ncard_univ]
  linarith[Set.ncard_le_ncard (Set.subset_univ X)]

lemma IsVertexConnected.exists_edge {k : ℕ} (hk : k ≥ 1) (h : G.IsVertexConnected k) :
  ∃ x y : V, G.Adj x y := by
  have: Nontrivial V := by
    obtain ⟨X, hX⟩ := h.1
    have: X.ncard > 1 := by omega
    obtain ⟨x⟩ := h.nonempty
    obtain ⟨b, hb⟩ := Set.exists_ne_of_one_lt_ncard this x
    exact ⟨x, b, hb.2.symm⟩
  exact exists_edge_of_connected_nontrivial (h.Connected (by omega))


lemma IsVertexConnected.iso {k : ℕ} {G' : SimpleGraph W} (h : G.IsVertexConnected k) (ψ : G ≃g G') :
  G'.IsVertexConnected k := by
  obtain ⟨⟨X, hX⟩, h⟩ := h
  refine ⟨⟨ψ '' X, ?_⟩, ?_⟩
  · rwa[Set.ncard_image_of_injective _ ψ.injective]
  · rintro ⟨S, hS⟩
    apply h
    use ψ.symm '' S
    refine ⟨Set.Finite.image ψ.symm hS.1 , ?_ , IsSeparator.image_iso hS.2.2 ψ.symm⟩
    rw[Set.ncard_image_of_injective _ ψ.symm.injective]
    exact hS.2.1

open Classical in
lemma IsVertexConnected.le_degree [Fintype V] {k : ℕ} (h : G.IsVertexConnected k) (x : V) :
  G.degree x ≥ k := by
  by_contra! h_deg
  apply h.2
  let S := G.neighborSet x
  have S_card : S.ncard < k := by
    rwa[Set.ncard_eq_toFinset_card', ← G.neighborFinset_def, G.card_neighborFinset_eq_degree x]
  use S, Set.toFinite S, S_card
  have: ∃ y, y ≠ x ∧ y ∉ S := by
    obtain ⟨X, hX⟩ := h.1
    by_contra! hy
    have Xss : X ⊆ insert x S := by
      intro z _
      by_cases zeq : z = x
      · exact Or.inl zeq
      · exact Or.inr <| hy z zeq
    have insert_card : (insert x S).ncard ≤ S.ncard + 1 := Set.ncard_insert_le x S
    have X_card_le : X.ncard ≤ (insert x S).ncard := Set.ncard_le_ncard Xss
    linarith
  obtain ⟨y, hy⟩ := this
  use x, y
  refine ⟨?_, ?_⟩
  · intro p
    use Walk.snd p
    simp
    rw[G.mem_neighborSet]
    exact p.adj_snd (p.not_nil_of_ne hy.1.symm)
  · have: x ∉ S := by
      intro hx
      rw[G.mem_neighborSet] at hx
      exact G.irrefl hx
    exact ⟨this, hy.2⟩

lemma IsVertexConnected.eq_completeGraph_of_card_eq [Fintype V] {k : ℕ}
  (h : G.IsVertexConnected k) (h_card : Fintype.card V = k + 1) : G = (completeGraph V) := by
  classical
  ext x y
  constructor
  · exact G.ne_of_adj
  · intro e'
    by_contra! e
    let S := G.neighborSet x
    have hn : insert x (G.neighborSet x) = Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      have: k + 1 ≤ (insert x (G.neighborSet x)).ncard := by
        have : x ∉ G.neighborSet x := by simp
        rw[Set.ncard_insert_of_notMem this, Set.ncard_eq_toFinset_card',
          ← G.neighborFinset_def, G.card_neighborFinset_eq_degree x]
        linarith[h.le_degree x]
      simpa[h_card]
    rcases (hn ▸ Set.mem_univ y) with (yeq | yadj)
    · exact (completeGraph V).irrefl (yeq ▸ e')
    · exact e <| (G.mem_neighborSet x y).1 yadj


lemma IsVertexConnected.ncard_completeGraph {k : ℕ}
  (h_card : (Set.univ : Set V).ncard = k) (hk : k ≥ 1) :
  (completeGraph V).IsVertexConnected (k - 1) := by
  refine ⟨⟨Set.univ, by simpa[h_card, hk]⟩ , ?_⟩
  · rintro ⟨S, hS⟩
    obtain ⟨x, y, hxy⟩ := hS.2.2
    have e: (completeGraph V).Adj x y := hxy.ne
    obtain ⟨s, hs⟩ := hxy.1 e.toWalk
    have: s = x ∨ s = y := by simpa using hs.2
    rcases this with (rfl | rfl)
    · exact hxy.2.1 hs.1
    · exact hxy.2.2 hs.1

lemma IsVertexConnected.is_minimum_separator_of_ncard_le [Fintype V] {k : ℕ} {X : Set V}
  (h : G.IsVertexConnected k) (h_sep : G.IsSeparator X) (h_card : X.ncard ≤ k) :
  G.IsMinimumSeparator X := by
  refine ⟨h_sep, ?_⟩
  by_contra hS
  rcases not_forall.1 hS with ⟨S, hS⟩
  push_neg at hS
  apply h.2
  refine ⟨S, S.toFinite , lt_of_lt_of_le hS.2 h_card, hS.1⟩

end SimpleGraph
