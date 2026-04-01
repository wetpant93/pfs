import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

variable {V W : Type*} {u v w x y z : V} {G : SimpleGraph V} {G' : SimpleGraph W}
variable {S : Set V}

namespace SimpleGraph

def IsVertexSeparator (G : SimpleGraph V) (S : Set V) (v w : V) : Prop :=
  (∀ p : G.Walk v w, ∃ s ∈ S, s ∈ p.support) ∧ (v ∉ S ∧ w ∉ S)

def IsSeparator (G : SimpleGraph V) (S : Set V) : Prop :=
  ∃ x : V, ∃ y : V, G.IsVertexSeparator S x y


lemma IsVertexSeparator.toSeparator (h : G.IsVertexSeparator S v w) : G.IsSeparator S := ⟨v, w, h⟩

lemma IsVertexSeparator.symm (h : G.IsVertexSeparator S x y) : G.IsVertexSeparator S y x := by
  refine ⟨?_ , by simp[h.2]⟩
  intro p
  obtain ⟨s, ⟨hs, hp⟩⟩ := h.1 p.reverse
  refine ⟨s, hs, by simpa[Walk.support_reverse] using hp⟩

lemma IsVertexSeparator.ne (h : G.IsVertexSeparator S x y) : x ≠ y := by
  rintro rfl
  obtain ⟨hp, _, _⟩ := h
  have hp' := hp Walk.nil
  simp only [Walk.support_nil, List.mem_singleton, exists_eq_right] at hp'
  contradiction


lemma IsSeparator.image_iso (h : G.IsSeparator S) (ψ : G ≃g G') : G'.IsSeparator (ψ '' S) := by
  obtain ⟨x, y, hxy⟩ := h
  use ψ x, ψ y
  refine ⟨?_, by simpa using hxy.2⟩
  · intro p'
    have hx : ψ.symm.toHom (ψ x) = x := by simp
    have hy : ψ.symm.toHom (ψ y) = y := by simp
    let p : G.Walk x y := Walk.copy (p'.map (ψ.symm).toHom) hx hy
    let p_supp := Walk.support_copy (p'.map (ψ.symm).toHom) hx hy
    obtain ⟨s, ⟨hS , hp⟩⟩ := hxy.1 p
    use ψ s
    refine ⟨by simp[hS], ?_⟩
    obtain ⟨a, ⟨ha, rfl⟩⟩ := List.mem_map.1 <| Walk.support_map ψ.symm.toHom p' ▸ p_supp ▸ hp
    simpa

lemma IsSeparator.not_connected {X : Set V} (h : G.IsSeparator X) :
  ¬(G.induce Xᶜ).Connected := by
  intro h_conn
  rcases h with ⟨x, y, h⟩
  obtain ⟨p⟩ := h_conn.preconnected ⟨x, h.2.1⟩ ⟨y, h.2.2⟩
  rcases h.1 <| p.map (Embedding.induce Xᶜ).toHom with ⟨v, ⟨hv₀, hv₁⟩⟩
  obtain ⟨v', ⟨_, rfl⟩⟩ := List.mem_map.1 <| Walk.support_map (Embedding.induce Xᶜ).toHom p ▸ hv₁
  exact v'.property hv₀

lemma IsSeparator.compl_nonempty (h : G.IsSeparator S) : Nonempty ↑Sᶜ := by
  obtain ⟨a, b, h⟩ := h
  use a
  exact h.2.1


lemma IsVertexSeparator.fromComponents (C D : (G.induce Sᶜ).ConnectedComponent) (h_ne : C ≠ D) :
  ∀ v ∈ C.supp, ∀ w ∈ D.supp, G.IsVertexSeparator S (↑v) (↑w) := by
  intro v hv w hw
  refine ⟨?_, ⟨v.property, w.property⟩⟩
  intro p
  by_cases hS: ∀ v ∈ p.support, v ∈ Sᶜ
  · let p' := p.induce _ hS
    exfalso; apply h_ne
    rw[ConnectedComponent.mem_supp_iff] at hv hw
    rw[← hv, ← hw, ConnectedComponent.sound p'.reachable]
  · grind

lemma IsVertexSeparator.fromAdj (e : G.Adj v u) (h : G.IsVertexSeparator S v w) (hu : u ∉ S) :
  G.IsVertexSeparator S u w := by
  refine ⟨?_, ?_⟩
  · intro p
    let p' := Walk.cons e p
    obtain ⟨s, hs⟩ := h.1 p'
    use s
    refine ⟨hs.1, ?_⟩
    obtain (rfl | h₀) := p'.mem_support_iff.1 hs.2
    · exfalso
      exact h.2.1 hs.1
    exact h₀
  exact ⟨hu, h.2.2⟩



end SimpleGraph
