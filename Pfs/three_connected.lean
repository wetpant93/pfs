import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Pfs.IsSeparator
import Pfs.IsVertexConnected

variable {V W : Type*} {u v w x y z : V} {G : SimpleGraph V} {G' : SimpleGraph W}
variable {e : G.Adj x y}
variable {S : Set V}

namespace SimpleGraph

section

def contractEdge (G : SimpleGraph V) (_e : G.Adj x y) : SimpleGraph {z // z ≠ y} where
  Adj a b := a ≠ b ∧ (G.Adj ↑a ↑b ∨ (x = ↑a ∧ G.Adj ↑b y) ∨ (x = ↑b ∧ G.Adj ↑a y))
  symm a b h := by tauto
  loopless a := by tauto

local notation:50 G " / " e => contractEdge G e

open Classical in
noncomputable
def Adj.proj (e : G.Adj x y) (v : V) : {z // z ≠ y} :=
  if h : v = y then ⟨x, e.ne⟩ else ⟨v, h⟩

lemma Adj.proj_adj (e : G.Adj x y) (e' : G.Adj v w) :
  (G / e).Adj (e.proj v) (e.proj w) ∨ (e.proj v = e.proj w) := by
  by_cases h : e.proj v = e.proj w
  · exact Or.inr h
  · simp[contractEdge, Adj.proj] at *
    split_ifs at *
    all_goals simp_all
    exact Or.inr e'.symm

lemma Adj.proj_of_ne (h : v ≠ y) : ↑(e.proj v) = v := by simp[Adj.proj, h]

lemma Adj.proj_val (v : {z // z ≠ y}) : e.proj ↑v = v := by simp[v.property, Adj.proj]

lemma Adj.proj_id (e : G.Adj x y) (hv : v ≠ x ∧ v ≠ y) (h_eq : e.proj v = e.proj u) : u = v := by
  simp[Adj.proj, hv] at h_eq
  split_ifs at h_eq
  · exfalso
    exact congr_arg Subtype.val h_eq |> hv.1
  · symm
    exact congr_arg Subtype.val h_eq


noncomputable
def Adj.proj_walk (e : G.Adj x y) {u v : V} : G.Walk u v → (G / e).Walk (e.proj u) (e.proj v)
  | Walk.nil => Walk.nil
  | Walk.cons e' p => by
    rename_i w
    by_cases h₀ : e.proj u = e.proj w
    · exact (e.proj_walk p).copy h₀.symm rfl
    · exact Walk.cons (Or.resolve_right (e.proj_adj e') h₀) (e.proj_walk p)

lemma Adj.proj_walk_prop {u v : V} (e : G.Adj x y) (p : G.Walk u v) :
  ∀ z ∈ (e.proj_walk p).support, ↑z ∈ p.support ∨ (↑z = x ∧ y ∈ p.support) := by
  induction p with
    | nil =>
      rename_i u
      simp only [Walk.support_nil, List.mem_singleton, Adj.proj_walk]
      intro _ hz
      by_cases h : u = y <;> rw[hz] <;> simp[Adj.proj, h]
    | cons e' p ih =>
      rename_i u w v
      intro _ hz
      by_cases hu : e.proj u = e.proj w
      · simp[Adj.proj_walk, hu] at hz
        rcases ih _ hz with h' | h' <;> simp[h']
      · simp[Adj.proj_walk, hu] at hz
        simp only [Walk.support_cons, List.mem_cons]
        rcases hz with rfl | hz
        · by_cases ueq : u = y
          · right
            rw[Adj.proj, dif_pos ueq]
            exact ⟨rfl, Or.inl ueq.symm⟩
          · exact Or.inl <| Or.inl <| e.proj_of_ne ueq
        rcases ih _ hz with h' | h' <;> simp[h']


noncomputable
def Adj.expandEdge {u v : {z // z ≠ y}} (e' : (G / e).Adj u v) : G.Walk u v := by
  obtain ⟨_, h⟩ := e'
  by_cases h_adj : G.Adj ↑u ↑v
  · exact h_adj.toWalk
  by_cases hv : x = ↑u ∧ G.Adj ↑v y
  · exact Walk.cons (hv.1 ▸ e) (hv.2.symm.toWalk)
  simp[h_adj, hv] at h
  exact Walk.cons h.2 (h.1 ▸ e.symm).toWalk

noncomputable
def Walk.expand {u v : {z // z ≠ y}} : (G / e).Walk u v → G.Walk u v
  | Walk.nil => Walk.nil
  | Walk.cons e' p' => Walk.append (e.expandEdge e') (p'.expand)


lemma Adj.support_expand {e : G.Adj x y} {u v : {z // z ≠ y}}
  (e' : (G / e).Adj u v) {a : V} (ha : a ∈ (Adj.expandEdge e').support) :
  a = ↑u ∨ a = ↑v ∨ (a = y ∧ (x = ↑u ∨ x = ↑v)) := by
  rw [Adj.expandEdge] at ha
  rcases e' with ⟨ne, e_norm | ⟨rfl, e_u⟩ | ⟨rfl, e_v⟩⟩ <;>
  try split_ifs at ha <;>
  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons] at ha <;>
  tauto

lemma Walk.support_expand {e : G.Adj x y} {u v : {z // z ≠ y}} (p : (G / e).Walk u v) :
  ∀ a ∈ (Walk.expand p).support, e.proj a ∈ p.support := by
  intro a ha
  induction p with
   | nil =>
     simp[Walk.expand] at *
     rw[ha, e.proj_val]
   | cons _ _ ih =>
     simp [Walk.expand, Walk.support_cons] at *
     rcases ha with (ha | ha)
     · rcases e.support_expand _ ha with rfl | rfl | ⟨rfl, rfl | rfl⟩
        <;> simp[e.proj_val] <;> simp[Adj.proj]
     simp[ih ha]


lemma Adj.image_proj_separates_walks {u v : V} (e : G.Adj x y) (hu : u ≠ y) (hv : v ≠ y)
  (hS : ∀ p : G.Walk u v, ∃ s ∈ S, s ∈ p.support) :
   ∀ p' : (G / e).Walk (e.proj u) (e.proj v), ∃ s ∈ (e.proj '' S), s ∈ p'.support := by
  have v_eq : ↑(e.proj v) = v := e.proj_of_ne hv
  have u_eq : ↑(e.proj u) = u := e.proj_of_ne hu
  intro p
  let p' := (Walk.expand p).copy u_eq v_eq
  have p'_support := (Walk.expand p).support_copy u_eq v_eq  ▸ Walk.support_expand p
  obtain ⟨s, ⟨hS, hp'⟩⟩ := hS p'
  exact ⟨e.proj s, Set.mem_image_of_mem _ hS, p'_support _ hp'⟩


lemma IsVertexSeparator.image_proj_not_mem (e : G.Adj x y)
  (h : G.IsVertexSeparator S v x) (hy : y ∉ S) (hv : v ≠ y) :
  (G / e).IsVertexSeparator (e.proj '' S) (e.proj v) (e.proj x) := by
  have vnex := h.ne
  refine ⟨e.image_proj_separates_walks hv e.ne h.1,
    fun ⟨_, as, ha⟩ ↦ h.2.1 <| e.proj_id ⟨vnex, hv⟩ ha.symm ▸ as, ?_⟩
  intro ⟨a, as, ha⟩
  apply h.2.2
  have aney : a ≠ y := by
    intro rfl
    exact hy as
  rwa[← e.proj_of_ne e.ne, ← ha, e.proj_of_ne aney]

lemma IsVertexSeparator.image_proj_ne (e : G.Adj x y)
  (hv : v ≠ x ∧ v ≠ y) (hw : w ≠ x ∧ w ≠ y) (h : G.IsVertexSeparator S v w) :
  (G / e).IsVertexSeparator (e.proj '' S) (e.proj v) (e.proj w) := by
  refine ⟨e.image_proj_separates_walks hv.2 hw.2 h.1,
    fun ⟨_, as, ha⟩ ↦ h.2.1 (e.proj_id hv ha.symm ▸ as),
    fun ⟨_, as, ha⟩ ↦ h.2.2 (e.proj_id hw ha.symm ▸ as)⟩


lemma IsSeparator.image_val_of_not_mem {X : Set {z // z ≠ y}} (hX : (G / e).IsSeparator X)
  (xne : x ∉ Subtype.val '' X) : G.IsSeparator (Subtype.val '' X) := by
  obtain ⟨v, w, h⟩ := hX
  refine ⟨↑v, ↑w, ⟨?_, by simp [h.2]⟩⟩
  intro p
  let p' := (e.proj_walk p).copy (e.proj_val v) (e.proj_val w)
  obtain ⟨s, xs, hp'⟩ := h.1 p'
  refine ⟨↑s, Set.mem_image_of_mem _ xs, ?_⟩
  have p'_support := Walk.support_copy _ (e.proj_val v) (e.proj_val w) ▸ e.proj_walk_prop p
  rcases p'_support s hp' with hs | ⟨rfl, _⟩
  · exact hs
  · exact False.elim (xne (Set.mem_image_of_mem _ xs))

lemma IsSeparator.insert_image_val {X : Set {z // z ≠ y}} (hX : (G / e).IsSeparator X) :
  G.IsSeparator (Subtype.val '' X ∪ {y}) := by
  obtain ⟨v, w, h⟩ := hX
  refine ⟨↑v, ↑w, ⟨?_, by simp[h.2, v.property, w.property]⟩⟩
  intro p
  let p' := (e.proj_walk p).copy (e.proj_val v) (e.proj_val w)
  have p'_support := Walk.support_copy _ (e.proj_val v) (e.proj_val w) ▸ e.proj_walk_prop p
  obtain ⟨s, xs, hp'⟩ := h.1 p'
  by_cases hy : y ∈ p.support
  · refine ⟨y, Or.inr <| Set.mem_singleton _, hy⟩
  refine ⟨↑s, Or.inl <| Set.mem_image_of_mem _ xs, ?_⟩
  rcases p'_support _ hp' with hs | ⟨_, yin⟩
  · exact hs
  · exact False.elim <| hy yin


private lemma aux₀ [Fintype V] (e : G.Adj x y) (h_card : Fintype.card V > 4)
  (h_conn : G.IsVertexConnected 3)
  (h_sep : ¬((G / e).IsVertexConnected 3)) :
  ∃ z , G.IsSeparator {x, y, z} := by
  classical
  dsimp[IsVertexConnected] at h_sep
  push_neg at h_sep
  have contract_card : ∃ X : Set {x // x ≠ y}, X.ncard > 3 := by
    use Set.univ
    simp; omega

  rcases h_sep contract_card with ⟨S, ⟨S_fin, S_bound, S_sep⟩⟩

  have S_card: S.ncard = 2 := by
    by_cases h' : S.ncard < 2
    · have sep_ncard : ((Subtype.val '' S) ∪ {y}).ncard < 3 := by
        apply lt_of_le_of_lt <| Set.ncard_union_le (Subtype.val '' S) {y}
        rw[Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_singleton]
        omega
      exfalso
      apply h_conn.2
      use (Subtype.val '' S) ∪ {y}
      refine ⟨?_, sep_ncard, S_sep.insert_image_val⟩
      rw[Set.finite_union]
      exact ⟨Set.Finite.image Subtype.val S_fin, Set.finite_singleton y⟩
    omega

  have xinS: ⟨x, e.ne⟩ ∈ S := by
    by_contra! hx
    have: x ∉ Subtype.val '' S := by simp[hx]
    exfalso
    apply h_conn.2
    use Subtype.val '' S
    refine ⟨Set.Finite.image Subtype.val S_fin, ?_, S_sep.image_val_of_not_mem this⟩
    rw[Set.ncard_image_of_injective _ Subtype.val_injective]
    omega

  rcases Set.ncard_eq_two.1 S_card with ⟨a, b, hS'⟩
  wlog ha : a = x with H
  · have wl: b ≠ a ∧ S = {b, a} := by
      constructor
      · symm; exact hS'.1
      · rw[Set.pair_comm]
        exact hS'.2

    have beqx: ↑b = x := by
      rw[hS'.2] at xinS
      rcases xinS with rfl | rfl
      · contradiction
      · rfl

    exact H e h_card h_conn h_sep contract_card S S_fin S_bound S_sep S_card xinS b a wl beqx

  use b
  have: Subtype.val '' S ∪ {y} = {x, y, ↑b} := by grind
  exact this ▸ S_sep.insert_image_val



lemma exists_min_comp_card [Nonempty V] [Fintype V] :
  ∃ C : G.ConnectedComponent, ∀ C' : G.ConnectedComponent, C.supp.ncard ≤ C'.supp.ncard := by
  haveI : Finite G.ConnectedComponent := Quot.finite _
  exact Finite.exists_min _

lemma Set.three_le_ncard {x y z : V} : ({x,y,z} : Set V).ncard ≤ 3 := by
  linarith[Set.ncard_insert_le x ({y,z} : Set V),
           Set.ncard_insert_le y ({z} : Set V),
           Set.ncard_singleton z]


lemma three_compl_nonempty [Fintype V] (x y z : V) (h_card : Fintype.card V > 4) :
  Nonempty ({x,y,z}ᶜ : Set V) := by
  rw[Set.nonempty_coe_sort, Set.nonempty_iff_empty_ne]
  intro h
  have univ: {x,y,z} = (Set.univ : Set V) := Set.compl_empty_iff.1 h.symm
  have univ_card : ({x,y,z} : Set V).ncard ≤ 3:= Set.three_le_ncard
  rw[Fintype.card_eq_nat_card, ← Set.ncard_univ, ← univ] at h_card
  omega

noncomputable
def score_sep [Fintype V] (x y z : V) (h_card : Fintype.card V > 4) :
  (G.induce {x,y,z}ᶜ).ConnectedComponent := by
  classical
  have nonempty := three_compl_nonempty x y z h_card
  exact ((G.induce {x,y,z}ᶜ).exists_min_comp_card).choose


lemma score_sep_prop [Fintype V]
  (x y z : V) (h_card : Fintype.card V > 4) (C : (G.induce {x,y,z}ᶜ).ConnectedComponent) :
  (G.score_sep x y z h_card).supp.ncard ≤ C.supp.ncard := by
  classical
  have nonempty := three_compl_nonempty x y z h_card
  exact ((G.induce {x,y,z}ᶜ).exists_min_comp_card).choose_spec C


lemma score_sep_min [Fintype V] (h_card : Fintype.card V > 4)
  (h_exists : ∃ x y z, G.Adj x y ∧ G.IsSeparator {x, y, z}) :
  ∃ (x y z : V), G.Adj x y ∧ G.IsSeparator {x, y, z} ∧
  ∀ (x' y' z' : V), G.Adj x' y' ∧ G.IsSeparator {x', y', z'} →
    (G.score_sep x y z h_card).supp.ncard ≤ (G.score_sep x' y' z' h_card).supp.ncard := by
  classical
  let P := fun (n : ℕ) ↦ ∃ (x y z : V)
                            (e : G.Adj x y)
                            (hz : G.IsSeparator {x,y,z}) ,
                            (G.score_sep x y z h_card).supp.ncard = n

  have hP_exists : ∃ n, P n := by
    obtain ⟨x, y, z, ⟨e, hz⟩⟩ := h_exists
    refine ⟨(G.score_sep x y z h_card).supp.ncard, ⟨x,y,z,e,hz,rfl⟩⟩
  rcases Nat.find_spec hP_exists with ⟨x,y,z, ⟨h₀,h₁,h₂⟩⟩
  refine ⟨x, y, z, h₀, h₁, ?_⟩
  intro x' y' z' h'
  rw[h₂]
  apply Nat.find_min'
  use x', y', z', h'.1, h'.2

lemma exists_edge_induced {S : Set V} (e : G.Adj x y) (hx : x ∈ S) (hy : y ∈ S) :
  ∃ x' y', (G.induce S).Adj x' y' ∧ ↑x' = x ∧ ↑y' = y := by
  use ⟨x, hx⟩, ⟨y, hy⟩
  simpa


lemma not_conn_exists_comps [Nonempty V] (h : ¬G.Connected) :
  ∃ C D : G.ConnectedComponent, C ≠ D := by
  rw[connected_iff_exists_forall_reachable] at h
  push_neg at h
  obtain ⟨x⟩ := ‹Nonempty V›
  obtain ⟨y, _⟩ := h x
  exact ⟨G.connectedComponentMk x, G.connectedComponentMk y, by simpa⟩


lemma not_conn_comp_ne [Nonempty V] (h : ¬G.Connected) (C : G.ConnectedComponent) :
  ∃ D, C ≠ D := by
  obtain ⟨C₀, C₁, h⟩ := not_conn_exists_comps h
  by_cases h_eq : C = C₀
  · use C₁
    rwa[h_eq]
  · use C₀

lemma ind_not_conn_exists_comp (x : V) (hC : ¬(G.induce S).Connected) (hS : Nonempty S) :
  ∃ C : (G.induce S).ConnectedComponent, x ∉ Subtype.val '' C.supp := by
  obtain ⟨C, D, h_ne⟩ := not_conn_exists_comps hC
  by_cases hx : x ∈ (↑) '' C.supp
  · use D
    obtain ⟨x, ⟨hx, rfl⟩⟩ := hx
    rw[Subtype.val_injective.mem_set_image]
    exact ((G.induce S).pairwise_disjoint_supp_connectedComponent h_ne).notMem_of_mem_left hx
  use C


lemma ind_not_conn_edge_free_comp {S : Set V}
  (e : G.Adj x y) (hC : ¬(G.induce S).Connected) (hS : Nonempty S) :
  ∃ C : (G.induce S).ConnectedComponent, x ∉ Subtype.val '' C.supp ∧ y ∉ Subtype.val '' C.supp := by
  obtain ⟨C, hCx⟩ := ind_not_conn_exists_comp x hC hS
  by_cases hCy : y ∈ Subtype.val '' C.supp
  · obtain ⟨D, h_ne⟩ := not_conn_comp_ne hC C
    refine ⟨D, ?_, ?_⟩
    · rintro ⟨⟨x', hx'⟩, hxD, rfl⟩
      obtain ⟨⟨y', hy'⟩, hyC, rfl⟩ := hCy
      apply h_ne.symm
      rw [← (ConnectedComponent.mem_supp_iff _ _).1 hxD,
          ← (ConnectedComponent.mem_supp_iff _ _).1 hyC]
      exact ConnectedComponent.connectedComponentMk_eq_of_adj e
    · rintro ⟨⟨y', hy'⟩, hyD, rfl⟩
      obtain ⟨⟨y'', hy''⟩, hyC, rfl⟩ := hCy
      have hdj := (G.induce S).pairwise_disjoint_supp_connectedComponent h_ne
      exact hdj.notMem_of_mem_left hyC hyD
  · exact ⟨C, hCx, hCy⟩



lemma aux_main [Fintype V] (h : G.IsVertexConnected 3) (h_card : Fintype.card V > 4) :
  ∃ (x y : V) (e : G.Adj x y), (G / e).IsVertexConnected 3 := by
  classical
  by_contra! no_edge
  obtain ⟨x₀, y₀, xy₀⟩ := h.exists_edge (by decide)
  have not_conn_xy := no_edge x₀ y₀ xy₀
  obtain ⟨z₀, hz⟩ := aux₀ xy₀ h_card h not_conn_xy
  obtain ⟨x, y, z, xy, h_sep, h_min⟩ := G.score_sep_min h_card (by refine ⟨x₀, y₀, z₀, xy₀, hz⟩)

  have h_sep_min: G.IsMinimumSeparator {x,y,z} :=
    h.is_minimum_separator_of_ncard_le h_sep Set.three_le_ncard

  obtain ⟨v, hv⟩ := h_sep_min.adj_comp (score_sep x y z h_card) z (by simp)
  have not_conn_zv := no_edge z v hv.2
  obtain ⟨w, h_zv_sep⟩ := aux₀ hv.2 h_card h not_conn_zv
  have nonempty_compl := three_compl_nonempty z ↑v w h_card

  obtain ⟨D, hD⟩ := ind_not_conn_edge_free_comp xy h_zv_sep.not_connected nonempty_compl

  have h_sep_min_zv : G.IsMinimumSeparator {z, ↑v, w} :=
    IsVertexConnected.is_minimum_separator_of_ncard_le h h_zv_sep Set.three_le_ncard

  obtain ⟨d, vd⟩ := h_sep_min_zv.adj_comp D v (by simp)

  have Dss_compl: Subtype.val '' D.supp ⊆ {x,y,z}ᶜ := by
    intro a ha
    apply Set.mem_compl
    rintro (aeqx | aeqy | _)
    · exact hD.1 <| aeqx ▸ ha
    · exact hD.2 <| aeqy ▸ ha
    obtain ⟨a', ⟨_, rfl⟩⟩ := ha
    apply a'.property
    left
    assumption

  have hd : ↑d ∈ ({x,y,z}ᶜ : Set V) := Dss_compl <| Subtype.val_injective.mem_set_image.2 vd.1

  have dscore: ↑d ∈ Subtype.val '' (G.score_sep x y z h_card).supp := by
    obtain ⟨v', d', vd', hv', hd'⟩ := exists_edge_induced vd.2 v.property hd
    have veqv': v' = v := by grind
    exact hd' ▸ Subtype.val_injective.mem_set_image.2 <|
          ConnectedComponent.mem_supp_of_adj_mem_supp _ hv.1 (veqv' ▸ vd')

  have Dss: ↑D.supp ⊆ Subtype.val '' (G.score_sep x y z h_card).supp := by
    rintro _ ⟨a, ⟨ha, rfl⟩⟩
    obtain ⟨Dwalk⟩ := D.reachable_of_mem_supp vd.1 ha
    have walkssD: ∀ t ∈ Dwalk.support, t ∈ D.supp := by
      intro t ht
      let pt := Dwalk.takeUntil t ht
      rw[ConnectedComponent.mem_supp_iff,
        ← ConnectedComponent.sound ⟨pt⟩,
        ← ConnectedComponent.mem_supp_iff]
      exact vd.1

    let Gwalk := Dwalk.map (Embedding.induce _).toHom
    have: ∀ t ∈ Gwalk.support, t ∈ ({x,y,z}ᶜ : Set V) := by
      intro t ht
      obtain ⟨t', ht'⟩ := List.mem_map.1 <| Dwalk.support_map (Embedding.induce _).toHom ▸ ht
      have: ↑t' ∈ Subtype.val '' D.supp := Subtype.val_injective.mem_set_image.2 <| walkssD t' ht'.1
      exact ht'.2 ▸ Dss_compl this

    have din : ⟨↑d, hd⟩ ∈ (G.score_sep x y z h_card).supp := by grind
    have ain := (ConnectedComponent.mem_supp_iff _ _).1 din ▸
                 ConnectedComponent.sound (Gwalk.induce _ this).reachable
    exact Subtype.val_injective.mem_set_image.2 <| (ConnectedComponent.mem_supp_iff _ _).2 ain.symm


  have: D.supp.ncard < (G.score_sep x y z h_card).supp.ncard := by
     repeat rw[← Set.ncard_image_of_injective _ Subtype.val_injective]
     apply Set.ncard_lt_ncard _ (Set.toFinite _)
     rw[Set.ssubset_iff_exists]
     refine ⟨Dss, ⟨v, by grind⟩⟩

  linarith[(G.score_sep_prop z ↑v w h_card D),
          h_min z ↑v w ⟨hv.2, h_zv_sep⟩]


lemma IsSeparator.image_proj (e : G.Adj x y) (hS : x ∉ S ∧ y ∉ S) (h : G.IsSeparator S) :
  (G / e).IsSeparator (e.proj '' S) := by
  have nonempty: Nonempty ↑Sᶜ := h.compl_nonempty
  let not_conn := h.not_connected
  obtain ⟨C, hC⟩ := ind_not_conn_edge_free_comp e not_conn nonempty
  obtain ⟨D, h_ne⟩ := not_conn_comp_ne not_conn C
  obtain ⟨v, vC⟩ := C.nonempty_supp
  obtain ⟨w, wD⟩ := D.nonempty_supp
  let vw_sep := IsVertexSeparator.fromComponents C D h_ne _ vC _ wD
  have v_ne: v ≠ x ∧ v ≠ y := by grind
  by_cases hw : ↑w = y
  · let xv_sep := vw_sep.symm.fromAdj (hw ▸ e.symm) hS.1
    exact (IsVertexSeparator.image_proj_not_mem e xv_sep.symm hS.2 v_ne.2).toSeparator
  · by_cases weq : ↑w = x
    · exact (IsVertexSeparator.image_proj_not_mem e (weq ▸ vw_sep) hS.2 v_ne.2).toSeparator
    · exact (vw_sep.image_proj_ne e ⟨v_ne.1, v_ne.2⟩ ⟨weq, hw⟩).toSeparator


open Classical in
lemma has_neighbor_outside {k : ℕ} [Fintype V] (h : G.degree x ≥ k) (hS : S.ncard < k) :
  ∃ v, G.Adj x v ∧ v ∉ S := by
  by_contra! hv
  have h_sub: G.neighborSet x ⊆ S := hv
  have: (G.neighborSet x).ncard ≥ k := by
    rwa[Set.ncard_eq_toFinset_card', ← G.neighborFinset_def, G.card_neighborFinset_eq_degree x]
  linarith[Set.ncard_le_ncard h_sub]


open Classical in
inductive TutteConstructable.{u} : ∀ {V : Type u} [Fintype V], SimpleGraph V → Prop
  | k4 {V : Type u} [Fintype V] (G : SimpleGraph V) :
      Nonempty (G ≃g completeGraph (Fin 4)) →
      TutteConstructable G
  | step {V V' : Type u} [Fintype V] [Fintype V']
      (G : SimpleGraph V) (G' : SimpleGraph V') (x y : V) (e : G.Adj x y):
      G.degree x ≥ 3 →
      G.degree y ≥ 3 →
      Nonempty (G' ≃g (G / e)) →
      TutteConstructable G'→
      TutteConstructable G

lemma TutteConstructable.is_three_connected [Fintype V]
  (h : TutteConstructable G) : G.IsVertexConnected 3 := by
  induction h with
    | k4 G k4_iso =>
      obtain ⟨ψ⟩ := k4_iso
      have k4_3conn: (completeGraph (Fin 4)).IsVertexConnected (4 - 1)
        := IsVertexConnected.ncard_completeGraph (by simp) (by simp)
      exact IsVertexConnected.iso k4_3conn ψ.symm

    | step G G' x y e h_deg_x h_deg_y h_iso hG' ih =>
      obtain ⟨ψ⟩ := h_iso
      classical
      by_contra! h
      rw[IsVertexConnected] at h
      push_neg at h
      rename_i V _ _ _
      have: ∃ X : Set V, X.ncard > 3 := by
        use Set.univ
        rw[Set.ncard_univ, ← Fintype.card_eq_nat_card]
        linarith [G.degree_lt_card_verts x]

      obtain ⟨S, hS⟩ := h this
      have S_card: S.ncard ≤ 2 := by grind
      have not_conn: ¬(G.induce Sᶜ).Connected := IsSeparator.not_connected hS.2.2
      have nonempty: Nonempty ↑Sᶜ := hS.2.2.compl_nonempty

      obtain ⟨C, hC⟩ := ind_not_conn_edge_free_comp e not_conn nonempty
      obtain ⟨D, h_ne⟩ := not_conn_comp_ne not_conn C
      obtain ⟨v, vC⟩ := C.nonempty_supp
      obtain ⟨w, wD⟩ := D.nonempty_supp
      let vw_sep := IsVertexSeparator.fromComponents C D h_ne _ vC _ wD
      have v_ne: v ≠ x ∧ v ≠ y := by grind
      apply (IsVertexConnected.iso ih ψ).2
      refine ⟨(e.proj '' S), Set.Finite.image e.proj S.toFinite,
              by linarith[Set.ncard_image_le (f := e.proj) S.toFinite], ?_⟩
      by_cases w_ne: w ≠ x ∧ w ≠ y
      · exact (vw_sep.image_proj_ne e v_ne w_ne).toSeparator
      simp only [not_and_or, not_ne_iff] at w_ne
      have: S.ncard < 3 := by linarith
      rcases w_ne with rfl | rfl
      · by_cases hy : y ∈ S
        · obtain ⟨u, hu⟩ := has_neighbor_outside h_deg_x this
          have une : u ≠ y := by grind
          have uv_sep := (vw_sep.symm.fromAdj hu.1 hu.2)
          exact (uv_sep.image_proj_ne e ⟨Ne.symm hu.1.ne, une⟩ v_ne).toSeparator
        · exact IsSeparator.image_proj e ⟨w.property, hy⟩ hS.2.2

      · by_cases hx : x ∈ S
        · obtain ⟨u, hu⟩ := has_neighbor_outside h_deg_y this
          have une : u ≠ x := by grind
          have uv_sep := (vw_sep.symm.fromAdj hu.1 hu.2)
          exact (uv_sep.image_proj_ne e ⟨une, Ne.symm hu.1.ne⟩ v_ne).toSeparator
        · exact IsSeparator.image_proj e ⟨hx, w.property⟩ hS.2.2


private lemma is_three_connected_tutte_helper.{u} (m : ℕ) :
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
  Fintype.card V = m + 4 → G.IsVertexConnected 3 → TutteConstructable G := by
  classical
  induction m with
  | zero =>
    intro V _ G h_card h_conn
    apply TutteConstructable.k4 G
    rw[h_conn.eq_completeGraph_of_card_eq h_card]
    have h_eq : Fintype.card V = Fintype.card (Fin 4) := by simp[h_card]
    let equiv : V ≃ Fin 4 := Fintype.equivOfCardEq h_eq
    exact ⟨Iso.completeGraph equiv⟩

  | succ k ih =>
    intro V _ G h_card h_conn
    obtain ⟨x, y, ⟨e, h⟩⟩ := aux_main h_conn (by simp[h_card])
    have constructable := ih {z // z ≠ y} (G / e) (by simp[h_card]) h
    exact TutteConstructable.step G (G / e)
          x y e (h_conn.le_degree x) (h_conn.le_degree y) ⟨Iso.refl⟩ constructable


lemma is_three_connected_tutte [Fintype V] (h : G.IsVertexConnected 3) : TutteConstructable G := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (by linarith[h.card] : Fintype.card V ≥ 4)
  exact is_three_connected_tutte_helper m V G hm h


theorem tutte_3_connected [Fintype V] : G.IsVertexConnected 3 ↔ TutteConstructable G :=
    ⟨is_three_connected_tutte, TutteConstructable.is_three_connected⟩

end

end SimpleGraph
