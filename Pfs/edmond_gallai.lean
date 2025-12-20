import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Tutte

variable {V V' : Type*}
variable {G H : SimpleGraph V}
variable {G' H' : SimpleGraph V'}
variable {S B : Set V}
variable {S' : Set V'}
variable {C : G.ConnectedComponent}

namespace SimpleGraph


#check G \ H


def IsClosed (G : SimpleGraph V) (S : Set V) : Prop :=
    ¬∃ x ∈ S, ∃y ∈ Sᶜ, G.Adj x y

def IsFactorCritical : Prop :=
    ∀ v : V, ∃ M : G.Subgraph, M.IsMatching ∧ M.support = {v}ᶜ


def IsFactorCriticalArea (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ v ∈ S, ∃ M : G.Subgraph, M.IsMatching ∧ M.support = S \ {v}


def IsMatchableToComps (S : Set V) : Prop :=
  ∃ (f : S → (G.induce Sᶜ).ConnectedComponent),
  Function.Injective f ∧ (∀ s : S, ∃ y ∈ (f s), G.Adj ↑s ↑y)




lemma exists_of_disjoint_sets_of_injective {A B : Set V} (f : A → B) (hd : Disjoint A B)
  (hf : ∀ a : A, G.Adj a (f a)) (hinj : Function.Injective f) :
  ∃ M : G.Subgraph, M.verts = A ∪ (↑(Set.range f)) ∧ M.IsMatching := by
  use {
      verts := A ∪ (↑(Set.range f))
      Adj x y := (∃ (ha: x ∈ A), f ⟨x, ha⟩ = y) ∨ (∃ (ha: y ∈ A), f ⟨y, ha⟩ = x)
      adj_sub := by
        rintro v w (⟨ha, rfl⟩ | ⟨ha, rfl⟩)
        · exact hf ⟨v, ha⟩
        · exact (hf ⟨w, ha⟩).symm
      edge_vert := by
        rintro v w (⟨ha, h⟩ | ⟨ha, rfl⟩)
        · left
          exact ha
        · right
          use f ⟨w, ha⟩
          refine ⟨?_, rfl⟩
          use ⟨w, ha⟩
  }
  simp only [Subgraph.IsMatching, Set.mem_union, true_and]
  rintro v (hv | ⟨⟨v', vb'⟩, ⟨⟨⟨w, wa⟩, hw⟩, h⟩⟩ )
  · use f ⟨v, hv⟩
    simp only [hv, exists_const, true_or,
               true_and, exists_true_left]
    rintro y (rfl | ⟨ha, h⟩)
    · rfl
    · have: v ∈ B := by
        rw[← h]
        obtain ⟨_ , hb⟩ := f ⟨y, ha⟩
        exact hb
      exfalso
      exact hd.le_bot ⟨hv, this⟩
  use w
  simp only [wa, exists_true_left, hw, h, or_true, true_and]
  rintro y (⟨va, _⟩ | ⟨hy, hy'⟩)
  · have vb: v ∈ B := by
      rw[← h]
      exact vb'
    exfalso
    exact hd.le_bot ⟨va, vb⟩
  rw[← Subtype.val_inj, h, ← hy', Subtype.val_inj] at hw
  apply hinj at hw
  rw[← Subtype.val_inj] at hw
  exact hw.symm


open Subgraph in
lemma factor_critcal_image (h : G.IsFactorCriticalArea S) (f : G ↪g G') :
  G'.IsFactorCriticalArea (f '' S) := by
  rintro s ⟨s', ⟨hs, hs'⟩⟩
  choose M hM hM' using h
  use (M s' hs).map f.toHom
  have img_match := Subgraph.IsMatching.map (f.toHom) (f.injective) (hM s' hs)
  refine ⟨img_match, ?_⟩
  rw[IsMatching.support_eq_verts img_match]
  simp
  rw[← IsMatching.support_eq_verts (hM s' hs),
     hM', Set.image_diff (f.injective), Set.image_singleton, hs']


lemma factor_area_odd (h : G.IsFactorCriticalArea S) : Odd S.ncard := by
  sorry




abbrev ι : G.induce S ↪g G := Embedding.induce S

def comp_ι (S) (C : (G.induce S).ConnectedComponent) : G.ConnectedComponent :=
  C.map ι.toHom

theorem comp_ι_mk {v : {x // x ∈ S}} :
  comp_ι S ((G.induce S).connectedComponentMk v) = G.connectedComponentMk (G.ι v) := rfl

lemma cmpl_of_closed_closed (h : G.IsClosed S) : G.IsClosed Sᶜ := by
    rintro ⟨x, hx, y, hy, xy⟩
    have: S = Sᶜᶜ := by simp
    rw[← this] at hy
    exact h ⟨y, hy, x, hx, G.adj_symm xy⟩

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


lemma closed_mem_of_reachable {v w : V}
  (vs : v ∈ S) (h₀ : G.IsClosed S) (h₁ : G.Reachable v w) : w ∈ S := by
  by_contra! wns
  exact h₀ <| exists_crossing_edge vs wns h₁

lemma closed_reachable_induce {v w : V} {S : Set V}
  (vs : v ∈ S) (h₀ : G.IsClosed S) (h₁ : G.Reachable v w) :
    ∃(ws : w ∈ S),  (G.induce S).Reachable ⟨v, vs⟩ ⟨w, ws⟩ := by

  have ws := closed_mem_of_reachable vs h₀ h₁

  rcases h₁ with ⟨p⟩
  have hw: (x : V) → x ∈ p.support → x ∈ S := by
    intro x h
    induction p with
      | nil =>
        rw[Walk.support_nil, List.mem_singleton] at h
        rwa[h]
      | @cons v u w vu h ih =>
        rw[Walk.mem_support_iff] at h
        rcases h with (h | h)
        · rwa[h]
        by_cases us: u ∈ S
        · exact ih us ws h
        · let nvu := h₀ ⟨v, vs, u, us, vu⟩
          contradiction
  use ws
  use Walk.induce S p hw


lemma closed_comp_dichotomy (h : G.IsClosed S) (C : G.ConnectedComponent) :
  C.supp ⊆ S ∨ C.supp ⊆ Sᶜ := by
  by_contra! h'
  obtain ⟨v, vc, vns⟩ := Set.not_subset.1 h'.1
  obtain ⟨w, wc, wnsc⟩ := Set.not_subset.1 h'.2
  have: w ∈ S := by
    simp at wnsc
    exact wnsc

  exact h <| exists_crossing_edge this vns <| C.reachable_of_mem_supp wc vc


lemma closed_comp_ι_supp_subset_closed (h : G.IsClosed S) (C : (G.induce S).ConnectedComponent) :
  ((G.comp_ι S) C).supp ⊆ S := by
  intro x hx
  obtain ⟨⟨v, vs⟩, rfl⟩ := C.nonempty_supp
  rw[comp_ι_mk, ConnectedComponent.mem_supp_iff, ConnectedComponent.eq] at hx
  exact closed_mem_of_reachable vs h hx.symm


lemma closed_comp_ι_inj (h : G.IsClosed S) : Function.Injective (G.comp_ι S) := by
  intro C C' h'
  obtain ⟨⟨v, vs⟩, rfl⟩ := C.nonempty_supp
  obtain ⟨w, rfl⟩ := C'.nonempty_supp
  rw[comp_ι_mk, comp_ι_mk, ConnectedComponent.eq] at h'
  exact ConnectedComponent.sound (closed_reachable_induce vs h h').2

lemma comp_ι_surj (C : G.ConnectedComponent) (CS : C.supp ⊆ S) :
  ∃ C' : (G.induce S).ConnectedComponent, (G.comp_ι S) C' = C := by
  obtain ⟨v, vs⟩ := C.nonempty_supp
  use (G.induce S).connectedComponentMk ⟨v, CS vs⟩
  simpa


noncomputable
def comp_ι_inv (C : G.ConnectedComponent) (CS : C.supp ⊆ S) :
  (G.induce S).ConnectedComponent := (comp_ι_surj C CS).choose


lemma comp_ι_inv_comp_ι (C : G.ConnectedComponent) (CS : C.supp ⊆ S) :
  (G.comp_ι S) (G.comp_ι_inv C CS) = C := by
  exact (comp_ι_surj C CS).choose_spec

lemma comp_ι_comp_ι_inv (C : (G.induce S).ConnectedComponent) (h : G.IsClosed S) :
  ∃(CS : (G.comp_ι S C).supp ⊆ S), (G.comp_ι_inv (G.comp_ι S C) CS) = C := by
  use closed_comp_ι_supp_subset_closed h C
  apply closed_comp_ι_inj h
  apply comp_ι_inv_comp_ι


lemma closed_comp_ι_supp (h : G.IsClosed S) (C : (G.induce S).ConnectedComponent) :
  (G.comp_ι S C).supp = G.ι '' C.supp := by
  ext x; constructor
  · intro hx
    use ⟨x, closed_comp_ι_supp_subset_closed h C <| hx⟩
    refine ⟨?_, by rfl⟩
    apply closed_comp_ι_inj h
    simpa
  rintro ⟨_, ⟨hy', hy⟩⟩
  rw[← hy', comp_ι_mk, hy]
  rfl

lemma closed_comp_ι_supp_card (h : G.IsClosed S) (C : (G.induce S).ConnectedComponent) :
  (G.comp_ι S C).supp.ncard = C.supp.ncard := by
  rw[closed_comp_ι_supp, Set.ncard_image_of_injective]
  · exact Subtype.coe_injective
  · assumption


variable [Fintype V] in
lemma odd_comp_eq (h : G.IsClosed S) :
  (G.induce S).oddComponents.ncard + (G.induce Sᶜ).oddComponents.ncard = G.oddComponents.ncard := by
  let hc := cmpl_of_closed_closed h
  let ImS  := (G.induce S).oddComponents.image <| G.comp_ι S
  let ImSc := (G.induce Sᶜ).oddComponents.image <| G.comp_ι Sᶜ

  let ImScard  := Set.ncard_image_of_injective (G.induce S).oddComponents <| closed_comp_ι_inj h
  let ImSccard := Set.ncard_image_of_injective (G.induce Sᶜ).oddComponents <| closed_comp_ι_inj hc

  have ImD: Disjoint ImS ImSc := by
      rw[Set.disjoint_iff]
      rintro x ⟨⟨xs, ⟨_, xim⟩⟩, ⟨xsc, ⟨_, ximsc⟩⟩⟩
      obtain ⟨⟨y,ys⟩, rfl⟩ := xs.nonempty_supp
      obtain ⟨⟨z,zs⟩, rfl⟩ := xsc.nonempty_supp
      rw[← ximsc, comp_ι_mk, comp_ι_mk, ConnectedComponent.eq] at xim
      exact h <| exists_crossing_edge ys zs xim

  have Imss: ImS ∪ ImSc ⊆ G.oddComponents := by
    rintro x (hx | hx) <;> {
      obtain ⟨w, odd, rfl⟩ := hx
      simp
      rw[closed_comp_ι_supp_card]
      assumption'
    }

  have Gss: G.oddComponents ⊆ ImS ∪ ImSc := by
    intro C _
    rcases closed_comp_dichotomy h C with (h' | h')
    · left
      use comp_ι_inv C h'
      simp[comp_ι_inv_comp_ι]
      rw[← closed_comp_ι_supp_card, comp_ι_inv_comp_ι]
      assumption'

    · right
      use comp_ι_inv C h'
      simp[comp_ι_inv_comp_ι]
      rw[← closed_comp_ι_supp_card, comp_ι_inv_comp_ι]
      assumption'

  rwa[← ImScard, ← ImSccard, ← Set.ncard_union_eq, Set.Subset.antisymm Imss Gss]


lemma comp_is_closed (C : G.ConnectedComponent) : G.IsClosed C.supp := by
  rintro ⟨x, hx, y, hy, xy⟩
  simp at hy hx
  apply hy
  rw[← hx]
  exact ConnectedComponent.connectedComponentMk_eq_of_adj xy.symm

lemma pullback_closed_is_closed (B : Set V) (h₁ : G.IsClosed S) :
  (G.induce B).IsClosed ((↑) ⁻¹' S) := by
  rintro ⟨⟨x, xb⟩, hx, ⟨y, yb⟩, hy, xy⟩
  simp at hx hy
  exact h₁ ⟨x, hx, y, hy, xy⟩

lemma iso_closed_is_closed (φ : G ≃g G') (h : G.IsClosed S) : G'.IsClosed (φ '' S) := by
  rintro ⟨x', hx, y', hy, x'y'⟩
  simp at hy
  rcases hx with ⟨x, ⟨xs, imx⟩⟩
  let imy := RelIso.apply_symm_apply φ y'
  by_cases h': φ.symm y' ∈ S
  · exact hy (φ.symm y') h' imy
  rw[← imx, ← imy] at x'y'
  exact h ⟨x, xs, φ.symm y', h', (Iso.map_adj_iff φ).1 x'y'⟩


lemma iso_comp_card_eq (φ : G ≃g G') :
  ∀ C : G.ConnectedComponent, C.supp.ncard = (C.map φ.toHom).supp.ncard := by
  intro C
  rw[Set.ncard_congr]
  · intro v vc
    use (φ v)
  · intro v vc
    simpa
  · intro v w vc wc h
    simp at h
    exact h
  · intro v vc
    use (φ.symm) v
    simp
    rw[← ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map]
    simpa

lemma iso_odd_card_eq (φ : G ≃g G') : G.oddComponents.ncard = G'.oddComponents.ncard := by
  let comp_card_eq := iso_comp_card_eq φ
  rw[Set.ncard_congr]
  · intro C _
    exact C.map φ.toHom
  · intro C Codd
    simp at *
    rwa[← comp_card_eq C]
  · intro C C' _ _ h
    let mapped := congr_arg (ConnectedComponent.map φ.symm.toHom) h
    rw[ConnectedComponent.map_comp] at mapped
    simpa using mapped

  intro C Codd
  use C.map φ.symm.toHom
  let p := comp_card_eq <| C.map φ.symm.toHom
  rw[ConnectedComponent.map_comp] at p
  simp at *
  rwa[p]


def induce_induce_iso_set_ss' (G : SimpleGraph V) (h : B ⊆ S) :
  (G.induce S).induce ((↑) ⁻¹' B) ≃g G.induce B where
  toFun := fun ⟨⟨x, _⟩, hx⟩ ↦ ⟨x, hx⟩
  invFun := fun ⟨x, hx⟩ ↦ ⟨⟨x, h hx⟩, hx⟩
  map_rel_iff' := by rfl

def induce_congr (h : B = S) : G.induce B ≃g G.induce S where
  toFun := by subst h; exact id
  invFun := by subst h; exact id
  map_rel_iff' := by
    intro a b
    subst h
    rfl

  left_inv := by intro x; subst h; rfl
  right_inv := by intro x; subst h; rfl



lemma image_induce_induce_iso_preimage
  (G : SimpleGraph V) (h : B ⊆ S) (X : Set {s // s ∈ S}) :
  (G.induce_induce_iso_set_ss' h) '' (Subtype.val ⁻¹' X) = ((Subtype.val ⁻¹' X) : (Set (↑B))) := by
  ext x; constructor
  · rintro ⟨x', ⟨hx', hx''⟩⟩
    use x'; constructor;
    · assumption
    rw[← hx'']
    dsimp[induce_induce_iso_set_ss']

  rintro ⟨x', ⟨hx', hx''⟩⟩
  rw[Set.mem_image]
  dsimp[induce_induce_iso_set_ss']
  obtain ⟨y, hy⟩ := x'
  simp at *
  rw[← hx'']
  exact ⟨hy, hx'⟩


variable [Fintype V] [Fintype V']

def induce_induce_iso (G : SimpleGraph V) (C : Set {x // x ∈ S}) :
  (G.induce S).induce C ≃g (G.induce <| (↑) '' C) where
  toFun := by
    rintro ⟨⟨s, hs⟩, hc⟩
    use s
    use ⟨s, hs⟩

  invFun := by
    rintro ⟨s, hs⟩
    have: s ∈ S := by rcases hs with ⟨⟨_, hs'⟩, ⟨_, rfl⟩⟩; exact hs'
    use ⟨s, this⟩
    have: ⟨s, this⟩ ∈ C := by
      rcases hs with ⟨x, hx, rfl⟩; exact hx
    assumption


  map_rel_iff' := by rfl


lemma odd_comp_eq_zero_induce_even_comp
  (C : G.ConnectedComponent) (h : Even C.supp.ncard) :
  (G.induce C.supp).oddComponents.ncard = 0 := by
  rw[Set.ncard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro C'; simp
  obtain ⟨⟨x, xc⟩, rfl⟩ := C'.nonempty_supp
  rwa[← closed_comp_ι_supp_card (comp_is_closed C),
        comp_ι_mk,
        (ConnectedComponent.mem_supp_iff C (G.ι ⟨x, xc⟩)).1 xc]


noncomputable
def d (G : SimpleGraph V) (S : Set V) : ℤ :=
    (G.induce Sᶜ).oddComponents.ncard - S.ncard

noncomputable
def score (G : SimpleGraph V) (B : Set V) : Lex (ℤ × ℕ) :=
  (d G B, B.ncard)

def exists_maximal_score (G : SimpleGraph V) :
  ∃ (B : Set V), ∀ (S : Set V), score G S ≤ score G B := by
  let ps : (Set (Set V)) := Set.univ
  have psnonempty: ps.Nonempty := by simp[ps]
  have psfinite: ps.Finite := by simp[Set.toFinite]
  rcases Set.exists_max_image ps (score G) psfinite psnonempty with ⟨B', _, h⟩
  use B'
  intro S
  exact Set.mem_univ S |> h S

noncomputable
def edmond_gallai_set (G : SimpleGraph V) : (Set V) := (exists_maximal_score G).choose


lemma edmond_gallai_is_maximal_d (G : SimpleGraph V) :
  ∀ (B : Set V), d G B ≤ d G (edmond_gallai_set G) := by
  intro B
  have h := (exists_maximal_score G).choose_spec B
  apply Prod.Lex.monotone_fst at h
  rw[edmond_gallai_set]; exact h

lemma edmond_gallai_is_maximal_card (G : SimpleGraph V) (h : d G S = d G (edmond_gallai_set G)) :
  S.ncard ≤ (edmond_gallai_set G).ncard := by
  have h' := (exists_maximal_score G).choose_spec S
  rw[score, Prod.Lex.le_iff] at h'
  rcases h' with h_lt | ⟨_ , h'⟩
  · rw[h] at h_lt
    apply lt_irrefl at h_lt
    contradiction
  · exact h'

def fromFunction (f : S → V) (hf : ∀ (s : S), G.Adj s (f s)) : G.Subgraph where
  verts := S ∪ (Set.range f)
  Adj x y := ∃ (s : S), s(x,y) = s(s.val, f s)
  adj_sub := by
    rintro x y ⟨s, hs⟩
    rw[← G.mem_edgeSet, hs, G.mem_edgeSet]
    exact (hf s)
  edge_vert := by
    rintro x y ⟨⟨s, hs⟩, h⟩
    rcases Sym2.eq_iff.1 h with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · left
      assumption
    · right
      use ⟨s, hs⟩



open Subgraph

open Fintype in
open Classical in
lemma one_factor_iff' (h₀ : G.IsMatchableToComps S)
  (h₁ : ∀ (C : (G.induce Sᶜ).ConnectedComponent), (G.induce Sᶜ).IsFactorCriticalArea C.supp) :
  card S = card (G.induce Sᶜ).ConnectedComponent ↔ ∃ M : Subgraph G, M.IsPerfectMatching := by
  obtain ⟨f, finj, hf⟩ := h₀
  choose c c_mem c_adj using hf
  choose M hM hM' using fun s ↦ h₁ (f s) (c s) (c_mem s)
    --fun s ↦ (factor_critcal_image (h₁ <| f s) G.ι) (c s) (Set.mem_image_of_mem G.ι (c_mem s))

  constructor
  · intro card_eq

    have fbij := (Fintype.bijective_iff_injective_and_card f).2 ⟨finj, card_eq⟩

    have hd: Pairwise fun s s' ↦ Disjoint (M s).support (M s').support := by
      intro s s' h
      rw[hM', hM']
      exact Disjoint.mono (by simp) (by simp) <|
            ((G.induce Sᶜ).pairwise_disjoint_supp_connectedComponent (finj.ne h))


    have cinj: Function.Injective c := by
      intro s s' h
      by_contra! ts
      have cinfs': c s ∈ (f s') := by rw[h]; exact c_mem s'
      exact ((G.induce Sᶜ).pairwise_disjoint_supp_connectedComponent (finj.ne ts)).le_bot <|
            ⟨c_mem s, cinfs'⟩

    have dj: Disjoint S Sᶜ := by rw[Set.disjoint_compl_right_iff_subset]


    obtain ⟨P, ⟨hP, hP'⟩⟩ := exists_of_disjoint_sets_of_injective c dj c_adj cinj
    let cM' := ⨆ s : S, (M s)
    let hcM' := Subgraph.IsMatching.iSup hM hd
    let hcM := hcM'.map (G.ι.toHom) (G.ι.injective)
    let cM := cM'.map G.ι.toHom

    have P_D_cM: Disjoint P.support cM.support := by
      rw[IsMatching.support_eq_verts, IsMatching.support_eq_verts, Set.disjoint_iff]
      · rintro x ⟨hl , ⟨⟨v, vc⟩, ⟨hC, hv⟩⟩⟩
        rcases hP ▸ hl with (hs | ⟨⟨y, yc⟩, ⟨⟨w, h⟩, hw⟩ ⟩)
        · rw[← hv] at hs
          exact vc hs
        rw[verts_iSup] at hC
        rcases hC with ⟨C, ⟨⟨s, hs'⟩, vC⟩⟩
        dsimp at hs'
        rw[← IsMatching.support_eq_verts, hM' s] at hs'
        · rw[← hs'] at vC
          have: G.ι.toHom ⟨v, vc⟩ = (⟨v, vc⟩ : ↑(Sᶜ)) := rfl
          rw[← hw, this, Subtype.val_inj] at hv
          rw[hv, ← h] at vC
          rcases vC with ⟨h1, h2⟩
          by_cases ws : w = s
          · rw[ws] at h2
            exact h2 rfl
          · exact ((G.induce Sᶜ).pairwise_disjoint_supp_connectedComponent (finj.ne ws)).le_bot <|
                  ⟨c_mem w, h1⟩
        exact hM s
      · exact hcM
      exact hP'

    let pMatch := P ⊔ cM

    have: pMatch.IsSpanning := by
      sorry

    refine ⟨pMatch, ⟨IsMatching.sup hP' hcM P_D_cM, this⟩⟩

  intro h
  let nonviolator := tutte.1 h S

  have Sleq: S.ncard ≥ (G.induce Sᶜ).oddComponents.ncard := by -- ≤ wg. tutte
    by_contra!
    apply nonviolator
    sorry

  have Sgeq: S.ncard ≤ (G.induce Sᶜ).oddComponents.ncard := by -- ≥ wg. h₀
    sorry

  have oddeq: card (induce Sᶜ G).ConnectedComponent = (induce Sᶜ G).oddComponents.ncard := by
    sorry

  have Seq: card S = S.ncard := by rw[← Nat.card_coe_set_eq, Fintype.card_eq_nat_card]

  rw[Seq, oddeq, le_antisymm Sgeq Sleq]



theorem aux (G : SimpleGraph V) : ∃ (B : Set V),
  (∀ X ⊆ B, {C : (G.induce Bᶜ).ConnectedComponent | ∃v ∈ C, ∃x ∈ X, G.Adj x v.val}.ncard ≥ X.ncard) ∧
  (∀ (C : (G.induce Bᶜ).ConnectedComponent), C.toSimpleGraph.IsFactorCritical) := by
  classical
  generalize hn : Fintype.card V = n

  induction' n using Nat.strong_induction_on with n ih

  rcases n with _ | n
  · use ∅
    have hempty := Fintype.card_eq_zero_iff.1 hn
    constructor <;> simp_all [IsFactorCritical]

  · use edmond_gallai_set G
    set B := edmond_gallai_set G
    have hnonempty := Fintype.card_pos_iff.1 (by linarith)

    have all_odd: ∀ (C : (G.induce Bᶜ).ConnectedComponent), Odd C.supp.ncard := by
      intro C
      by_contra! h -- assume |C| is even

      obtain ⟨c, cinC⟩ := C.nonempty_supp

      let C' := C.supp \ {c}

      let C'_val := Subtype.val '' C' -- C \ {c}
      let T := B ∪ {c.val} -- consider T := B ∪ {c}

      have C'ssTc: C'_val ⊆ Tᶜ := by
        intro x h
        simp[C'_val, C'] at h
        rcases h with ⟨⟨h₀, h₁⟩, h⟩
        simp[T]
        exact ⟨h, h₀⟩

      have cnotinB: c.val ∉ B := by
        obtain ⟨_, cinBc⟩ := c
        intro h'
        exact cinBc h'

      have T_card_gt_B_card: T.ncard = B.ncard + 1 := by
        simp[T]
        rw[Set.ncard_insert_of_notMem cnotinB]

      have one_odd: (G.induce C'_val).oddComponents.ncard ≥ 1 := by -- q(C - c) ≥ 1
        have: Odd (G.induce C'_val).oddComponents.ncard := by
          rw[odd_ncard_oddComponents]
          have: C.supp.ncard = C'_val.ncard + 1 := by
            rw[Set.ncard_image_of_injective C' Subtype.coe_injective]
            rw[Set.ncard_diff_singleton_add_one cinC C.supp.toFinite]
          have: C'_val.ncard = C.supp.ncard - 1 := by simp[this]
          rw[Nat.card_coe_set_eq, this, Nat.odd_sub]
          constructor <;> {
            intro
            try simp
            contradiction
          }
          have: 0 < C.supp.ncard := by
            rw[Set.ncard_pos]
            exact C.nonempty_supp
          linarith

        rcases this with ⟨k, hk⟩
        linarith


      let C_pb : Set ↑(Tᶜ) := Subtype.val ⁻¹' C.supp -- = C'
      let GindC := (G.induce Tᶜ).induce C_pb -- G[Tᶜ][C']
      let GindCc := (G.induce Tᶜ).induce C_pbᶜ -- G[Tᶜ][C'ᶜ] ≃ G[Tᶜ ∩ C'ᶜ] ≃ G[(S ∪ C)ᶜ]

      have: Tᶜ ⊆ Bᶜ := by simp[T]

      have pb_eq: C'_val = (↑) '' C_pb := by
        simp[C'_val, C_pb, C', T]
        ext x; constructor
        · rintro ⟨hx, xneqc⟩
          refine ⟨?_, hx⟩
          simp
          refine ⟨xneqc, ?_⟩
          obtain ⟨⟨y, ynb⟩, ⟨yc, rfl⟩⟩ := hx
          exact ynb

        · rintro ⟨xb, xc⟩
          simp at xb
          exact ⟨xc, xb.1⟩

      have pbc_eq: Tᶜ \ C'_val = (↑) '' C_pbᶜ := by
        rw[pb_eq]
        simp


      let ψ := (G.induce_congr pb_eq.symm).comp (G.induce_induce_iso C_pb)  -- G[Tᶜ][C'] ≃ G[C']

      let φ := induce_induce_iso_set_ss' G this
      let C_pb_closed := pullback_closed_is_closed ((↑) ⁻¹' Tᶜ) (comp_is_closed C) -- π(C) is closed in G[Sᶜ][Tᶜ] ≃g G[Tᶜ]
      let j := iso_closed_is_closed φ C_pb_closed


      have: ¬(∃ x ∈ C_pb, ∃ y ∈ C_pbᶜ, (G.induce Tᶜ).Adj x y) := by
        have: φ '' ((↑) ⁻¹' C.supp) = C_pb := image_induce_induce_iso_preimage G this C.supp
        rwa[this] at j


      have: GindC.oddComponents.ncard + GindCc.oddComponents.ncard = (G.induce Tᶜ).oddComponents.ncard:= by
        exact odd_comp_eq this

      have GCc_odd_eq_GBc_odd: GindCc.oddComponents.ncard = (G.induce Bᶜ).oddComponents.ncard := by
        let eq1 := odd_comp_eq (comp_is_closed C)
        simp at h
        rw[odd_comp_eq_zero_induce_even_comp C h] at eq1

        have: Subtype.val '' C.suppᶜ = Tᶜ \ C'_val := by
          simp[C'_val, T, C']
          ext x; constructor
          rintro ⟨xBc, xnC⟩
          by_cases xeqc : x = c
          · rw[xeqc] at xnC
            have: ↑c ∈ Subtype.val '' C.supp := by use c
            contradiction
          refine ⟨not_or.2 ⟨xeqc, xBc⟩, ?_⟩
          intro ⟨xinC, _⟩
          contradiction
          rintro ⟨xBcc, xnCc⟩
          obtain ⟨xneqc, xinBc⟩ := not_or.1 xBcc
          refine ⟨xinBc, ?_⟩
          intro xinC
          have: x ∈ Subtype.val '' C.supp \ {↑c} := by
            exact ⟨xinC, xneqc⟩
          contradiction

        rw[pbc_eq] at this

        let γ := (G.induce_induce_iso C_pbᶜ).symm.comp <|
                 (G.induce_congr this).comp <|
                  G.induce_induce_iso C.suppᶜ

        rw[← iso_odd_card_eq γ.symm] at eq1
        simp at eq1
        exact eq1

      have eq_odd: (G.induce Tᶜ).oddComponents.ncard = (G.induce Bᶜ).oddComponents.ncard + (G.induce C'_val).oddComponents.ncard := by
        rw[← GCc_odd_eq_GBc_odd, iso_odd_card_eq ψ.symm]
        linarith

      have tutte_eq: d G T = d G B := by
        apply eq_of_le_of_ge
        exact edmond_gallai_is_maximal_d G T
        calc
          d G B = (G.induce Bᶜ).oddComponents.ncard - B.ncard := rfl
          _ = (G.induce Bᶜ).oddComponents.ncard + 1 - (B.ncard + 1) := by linarith
          _ ≤ (G.induce Bᶜ).oddComponents.ncard + (G.induce C'_val).oddComponents.ncard - T.ncard := by linarith
          _ ≤ (G.induce Tᶜ).oddComponents.ncard - T.ncard := by linarith
          _ = d G T := rfl

      linarith[edmond_gallai_is_maximal_card G tutte_eq]




end SimpleGraph
