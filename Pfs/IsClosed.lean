import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Subgraph

variable {V : Type*} {G : SimpleGraph V} {S T : Set V} {v w : V}
variable {V' : Type*} {G' : SimpleGraph V'} {S' T' : Set V'}

namespace SimpleGraph

lemma exists_crossing_edge {v w : V}
  {X : Set V} (h₀ : v ∈ X) (h₁ : w ∉ X) (h : G.Reachable v w) : ∃ x ∈ X, ∃ y ∈ Xᶜ, G.Adj x y := by
  rcases h with ⟨p⟩
  induction p with
   | nil => contradiction
   | @cons u x _ ux _ ih =>
     by_cases h: x ∈ X
     · exact ih h h₁
     · exact ⟨u, h₀, x, h, ux⟩


def IsClosed (G : SimpleGraph V) (S : Set V) : Prop :=
    ¬∃ x ∈ S, ∃y ∈ Sᶜ, G.Adj x y


lemma IsClosed.compl (h : G.IsClosed S) : G.IsClosed Sᶜ := by
    rintro ⟨x, hx, y, hy, xy⟩
    have: S = Sᶜᶜ := by simp
    rw[← this] at hy
    exact h ⟨y, hy, x, hx, G.adj_symm xy⟩


lemma IsClosed.union (h₀ : G.IsClosed S) (h₁ : G.IsClosed T) : G.IsClosed (S ∪ T) := by
  rintro ⟨x, (hx | hx), y, hy, xy⟩
  · rw[Set.mem_compl_iff, Set.mem_union] at hy
    push_neg at hy
    exact h₀ ⟨x, hx, y, hy.1, xy⟩
  · rw[Set.mem_compl_iff, Set.mem_union] at hy
    push_neg at hy
    exact h₁ ⟨x, hx, y, hy.2, xy⟩

lemma IsClosed.biUnion {α : Type*} (S : Set α) (f : α → Set V)
 (hS : ∀ s ∈ S, G.IsClosed (f s)) :
  G.IsClosed (⋃ s ∈ S, (f s)) := by
  rintro ⟨x, hx, y, hy, xy⟩
  simp at hx hy
  obtain ⟨s, hs⟩ := hx
  exact (hS s hs.1) ⟨x, hs.2, y, hy s hs.1, xy⟩

lemma IsClosed.iUnion {ι : Type*} (s : ι → Set V) (hS : (i : ι) → G.IsClosed (s i))
  : G.IsClosed (⋃ (i : ι), s i) := by
  rintro ⟨x, hx , y, hy, xy⟩
  rw[Set.compl_iUnion, Set.mem_iInter] at hy
  rcases Set.mem_iUnion.1 hx with ⟨w, hw⟩
  exact (hS w) ⟨x, hw, y, hy w, xy⟩

lemma ConnectedComponent.isClosed_supp (C : G.ConnectedComponent) : G.IsClosed C.supp := by
  rintro ⟨x, hx, y, hy, xy⟩
  apply hy
  rw[← hx]
  exact ConnectedComponent.connectedComponentMk_eq_of_adj xy.symm


lemma IsClosed.val_preimage_closed (B : Set V) (h₁ : G.IsClosed S) :
  (G.induce B).IsClosed ((↑) ⁻¹' S) :=
  fun ⟨⟨x, _⟩, hx, ⟨y, _⟩, hy, xy⟩ ↦ h₁ ⟨x, hx, y, hy, xy⟩


lemma IsClosed.induce_of_not_adj {B : Set {x // x ∈ S}}
  (hc : (G.induce S).IsClosed B) (he : ¬(∃ x ∈ T \ S, ∃ y ∈ B, G.Adj x y)) :
  (G.induce T).IsClosed (Subtype.val ⁻¹' (↑B)) := by
  rintro ⟨⟨x, xt⟩, hx, ⟨y, yt⟩, hy, xy⟩
  simp at hx hy
  rcases hx with ⟨x', hx'⟩
  by_cases hy': y ∈ S
  · exact hc ⟨⟨x, x'⟩, hx', ⟨y, hy'⟩, hy hy', xy⟩
  · exact he ⟨y, ⟨yt, hy'⟩, ⟨x, x'⟩, hx', xy.symm⟩


lemma IsClosed.mem_of_reachable {v w : V}
  (vs : v ∈ S) (h₀ : G.IsClosed S) (h₁ : G.Reachable v w) : w ∈ S := by
  by_contra! wns
  exact h₀ <| exists_crossing_edge vs wns h₁


lemma IsClosed.reachable_induce {v w} {S : Set V}
  (vs : v ∈ S) (h₀ : G.IsClosed S) (h₁ : G.Reachable v w) :
  ∃(ws : w ∈ S), (G.induce S).Reachable ⟨v, vs⟩ ⟨w, ws⟩ := by
  obtain ⟨p⟩ := h₁
  induction p with
    | nil =>
      use vs
    | @cons u v w uv p ih =>
      have h': v ∈ S := IsClosed.mem_of_reachable vs h₀ ⟨uv.toWalk⟩
      have adj: (G.induce S).Adj ⟨u, vs⟩ ⟨v, h'⟩ := uv
      rcases ih h' with ⟨ws, ⟨p⟩⟩
      exact ⟨ws, ⟨Walk.cons adj p⟩⟩

lemma IsClosed.connectedComponent_subset_or_subset_compl
  (h : G.IsClosed S) (C : G.ConnectedComponent) :
  C.supp ⊆ S ∨ C.supp ⊆ Sᶜ := by
  by_contra! h'
  obtain ⟨v, vc, vns⟩ := Set.not_subset.1 h'.1
  obtain ⟨w, wc, wnsc⟩ := Set.not_subset.1 h'.2
  have: w ∈ S := by
    simp at wnsc
    exact wnsc

  exact h <| exists_crossing_edge this vns <| C.reachable_of_mem_supp wc vc


lemma IsClosed.connectedComponent_map_induce_injective (h : G.IsClosed S) :
  Function.Injective (ConnectedComponent.map (Embedding.induce S : G.induce S ↪g G).toHom) := by
  intro C C' h'
  obtain ⟨⟨v, vs⟩, rfl⟩ := C.nonempty_supp
  obtain ⟨w, rfl⟩ := C'.nonempty_supp
  simp only [ConnectedComponent.map_mk, ConnectedComponent.eq] at h'
  exact ConnectedComponent.sound (h.reachable_induce vs h').2


lemma IsClosed.connectedComponent_map_induce_supp_subset
  (h : G.IsClosed S) (C : (G.induce S).ConnectedComponent) :
  (C.map (Embedding.induce S).toHom).supp ⊆ S := by
  intro _ h'
  obtain ⟨⟨_, vs⟩, rfl⟩ := C.nonempty_supp
  rw[ConnectedComponent.map_mk, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq] at h'
  exact h.mem_of_reachable vs h'.symm


lemma IsClosed.connectedComponent_eq_map_induce_iff
  (h : G.IsClosed S) {C : (G.induce S).ConnectedComponent} {v : {x // x ∈ S}} :
  (G.connectedComponentMk ↑v) = C.map (Embedding.induce S).toHom ↔
  (G.induce S).connectedComponentMk v = C := by
  refine C.ind fun u => ?_
  simp only [← h.connectedComponent_map_induce_injective.eq_iff, ConnectedComponent.map_mk]
  rfl


lemma IsClosed.connectedComponent_map_induce_supp_eq {S : Set V} (h : G.IsClosed S)
  (C : (G.induce S).ConnectedComponent) :
  (C.map (Embedding.induce S).toHom).supp = ↑C.supp := by
  ext x; simp[← h.connectedComponent_eq_map_induce_iff]
  exact fun hx ↦
        h.connectedComponent_map_induce_supp_subset C
        <| (ConnectedComponent.mem_supp_iff _ _).2 hx

abbrev ι : G.induce S ↪g G := Embedding.induce S

lemma IsClosed.connectedComponent_map_induce_range (h : G.IsClosed S) :
  Set.range (ConnectedComponent.map (ι.toHom : (G.induce S) →g G)) =
  {C : G.ConnectedComponent | C.supp ⊆ S} := by
  ext x
  simp only [Set.range, Set.mem_setOf]
  constructor
  · exact fun ⟨y, hy⟩ ↦ hy ▸ h.connectedComponent_map_induce_supp_subset y
  · refine x.ind fun u ↦ ?_
    intro hu
    have: u ∈ S := hu ConnectedComponent.connectedComponentMk_mem
    exact ⟨(G.induce S).connectedComponentMk ⟨u, this⟩, rfl⟩




lemma IsClosed.connectedComponent_ncard_eq
  (h : G.IsClosed S) (C : (G.induce S).ConnectedComponent) :
  (C.map (Embedding.induce S).toHom).supp.ncard = C.supp.ncard := by
  rw[h.connectedComponent_map_induce_supp_eq,
     Set.ncard_image_of_injective _ Subtype.val_injective]


variable [Fintype V] in
theorem IsClosed.oddComponents_ncard_add_compl_eq (h : G.IsClosed S) :
  (G.induce S).oddComponents.ncard + (G.induce Sᶜ).oddComponents.ncard = G.oddComponents.ncard := by
  rw[← Set.ncard_image_of_injective _ h.connectedComponent_map_induce_injective,
     ← Set.ncard_image_of_injective _ h.compl.connectedComponent_map_induce_injective,
     ← Set.ncard_union_eq]
  · congr; ext x
    refine x.ind (fun u ↦ ?_)
    simp only [Set.mem_union, Set.mem_image, Set.mem_setOf]
    constructor
    · rintro (⟨c, ⟨_, h'⟩⟩ | ⟨c, ⟨_, h'⟩⟩)
      · rwa[← h', h.connectedComponent_ncard_eq c]
      · rwa[← h', h.compl.connectedComponent_ncard_eq c]
    rintro h'
    by_cases us: u ∈ S
    · left
      refine ⟨(G.induce S).connectedComponentMk ⟨u, us⟩, ⟨?_ , rfl⟩⟩
      rwa[← h.connectedComponent_ncard_eq]
    · right
      refine ⟨(G.induce Sᶜ).connectedComponentMk ⟨u, us⟩ , ⟨?_ , rfl⟩⟩
      rwa[← h.compl.connectedComponent_ncard_eq]

  rw[Set.disjoint_iff]
  rintro x ⟨⟨xs, ⟨_, xim⟩⟩, ⟨xsc, ⟨_, ximsc⟩⟩⟩
  obtain ⟨⟨y,ys⟩, rfl⟩ := xs.nonempty_supp
  obtain ⟨⟨z,zs⟩, rfl⟩ := xsc.nonempty_supp
  rw[← ximsc, ConnectedComponent.map_mk, ConnectedComponent.map_mk, ConnectedComponent.eq] at xim
  exact h <| exists_crossing_edge ys zs xim


noncomputable
def IsClosed.connectedComponentEquiv (h : G.IsClosed S) :
  (G.induce S).ConnectedComponent ≃ {C : G.ConnectedComponent | C.supp ⊆ S} :=
  h.connectedComponent_map_induce_range ▸
  Equiv.ofInjective _ h.connectedComponent_map_induce_injective

end SimpleGraph
