import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Pfs.IsClosed

variable {V : Type*}
variable {G H : SimpleGraph V}
variable {S : Set V}

namespace SimpleGraph


lemma iso_closed_is_closed (φ : G ≃g G') (h : G.IsClosed S) : G'.IsClosed (φ '' S) := by
  rintro ⟨x', hx, y', hy, x'y'⟩
  simp at hy
  rcases hx with ⟨x, ⟨xs, imx⟩⟩
  let imy := RelIso.apply_symm_apply φ y'
  by_cases h': φ.symm y' ∈ S
  · exact hy (φ.symm y') h' imy
  rw[← imx, ← imy] at x'y'
  exact h ⟨x, xs, φ.symm y', h', (Iso.map_adj_iff φ).1 x'y'⟩

lemma exists_crossing_edge {v w : V}
  {X : Set V} (h₀ : v ∈ X) (h₁ : w ∉ X) (h : G.Reachable v w) : ∃ x ∈ X, ∃ y ∈ Xᶜ, G.Adj x y := by
  rcases h with ⟨p⟩
  induction p with
   | nil =>
     contradiction
   | @cons u x _ ux _ ih =>
     by_cases h: x ∈ X
     · exact ih h h₁
     · exact ⟨u, h₀, x, h, ux⟩


lemma ss_comp (C : G.ConnectedComponent) (h₀ : H ≤ G) (h₁ : C.toSimpleGraph ≤ H.induce C.supp) :
  ∃ C' : H.ConnectedComponent, C'.supp = C.supp := by
  let v := C.nonempty_supp.choose
  let vinC := C.nonempty_supp.choose_spec
  set Gc := C.toSimpleGraph

  use H.connectedComponentMk v

  ext w; constructor
  · intro h
    simp at *
    have: G.Reachable w v := SimpleGraph.Reachable.mono h₀ h
    rw[ConnectedComponent.sound this]
    rw[← ConnectedComponent.mem_supp_iff]
    exact vinC

  · intro h
    simp
    have: Gc.Reachable ⟨w, h⟩ ⟨v, vinC⟩  := by
      let h' := (connected_iff_exists_forall_reachable Gc).1 (C.connected_toSimpleGraph)
      rcases h' with ⟨x, h'⟩
      let wx := SimpleGraph.Reachable.symm <| h' ⟨w, h⟩
      let xv := h' ⟨v, vinC⟩
      exact Reachable.trans wx xv

    let reachable_Hind := SimpleGraph.Reachable.mono h₁ this
    let hom : (H.induce C.supp →g H) := (SimpleGraph.Embedding.induce C.supp).toHom
    exact reachable_Hind.map hom

lemma ss_comp_ind (C : G.ConnectedComponent) (h₀ : H ≤ G)
  (h₁ : ¬(∃ x ∈ H.support, ∃ y ∈ H.supportᶜ, G.Adj x y))
  (h₂ : ∀ x ∈ H.support, ∀ y ∈ H.support, G.Adj x y → H.Adj x y) :
  (∃ C' : H.ConnectedComponent, C'.supp = C.supp) ∨
  (∃ C' : (G \ H).ConnectedComponent, C'.supp = C.supp) := by

  have h₃: G \ H ≤ G := sdiff_le

  have Hcss: (G \ H).support ⊆ H.supportᶜ := by
    intro x h hx
    push_neg at h₁
    rw[mem_support] at h
    rcases h with ⟨y, xy⟩
    rw[sdiff_adj] at xy
    by_cases hy: y ∈ H.support
    · exact xy.2 <| h₂ x hx y hy xy.1
    exact h₁ x hx y hy <| xy.1

  have: C.toSimpleGraph ≤ H.induce C.supp ∨ C.toSimpleGraph ≤ (G \ H).induce C.supp := by
    contrapose! h₁
    obtain ⟨x₀, x₁⟩ := h₁
    rw[SimpleGraph.le_iff_adj] at *
    push_neg at *
    rcases x₀ with ⟨⟨v, vc⟩, v₁, ⟨f₀, f₁⟩⟩
    rcases x₁ with ⟨⟨w, wc⟩, w₁, ⟨g₀, g₁⟩⟩

    have winH : w ∈ H.support := by
      rw[mem_support]
      use w₁
      have: ¬(G \ H).Adj w w₁ := g₁
      rw[sdiff_adj] at this
      push_neg at this
      exact this g₀

    have vinHc : v ∈ (G \ H).support := by
      rw[mem_support]
      use v₁
      rw[sdiff_adj]
      exact ⟨f₀, f₁⟩

    have wvReach: G.Reachable w v := ConnectedComponent.reachable_of_mem_supp C wc vc

    exact exists_crossing_edge winH (Hcss vinHc) wvReach

  rcases this with (h|h)
  · left
    exact ss_comp C h₀ h
  · right
    exact ss_comp C h₃ h

end SimpleGraph
