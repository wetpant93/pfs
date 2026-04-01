import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Pfs.IsClosed
import Pfs.IsSeparator
import Pfs.IsVertexConnected

variable {V W : Type*} {u v w x y z : V} {G : SimpleGraph V} {G' : SimpleGraph W}
variable {S : Set V}

namespace SimpleGraph

def IsMinimumSeparator (G : SimpleGraph V) (X : Set V) : Prop :=
  X.Finite ∧ G.IsSeparator X ∧ ∀ S, S.Finite ∧ G.IsSeparator S → X.ncard ≤ S.ncard

def absorbInto (G : SimpleGraph V) (x y : V) : SimpleGraph {z // z ≠ y} where
  Adj a b := a ≠ b ∧ (G.Adj ↑a ↑b ∨ (x = ↑a ∧ G.Adj ↑b y) ∨ (x = ↑b ∧ G.Adj ↑a y))
  symm a b h := by tauto
  loopless a := by tauto

lemma sub_walker {x z : V} (p : G.Path x z) (h_ne : x ≠ z) (adj_ne : ¬G.Adj x z) :
  ∃ y : V, ∃ p' : G.Walk y z, x ∉ p'.support ∧ p'.support ⊆ p.val.support ∧ G.Adj x y := by
  classical
  rcases p with (_ | ⟨e, p⟩)
  · contradiction
  rename_i y hp
  refine ⟨y, p, ⟨?_, ?_⟩⟩
  · intro hx
    let h' := hp.support_nodup
    rw[Walk.support_cons, List.nodup_cons] at h'
    exact h'.1 hx
  simpa

noncomputable
def proj (v : V) (h : x ≠ y) : {z // z ≠ y} := by
  by_cases hv : v = y
  · exact ⟨x, h⟩
  · exact ⟨v, hv⟩


lemma proj_adj (e : G.Adj v w) (h : x ≠ y) :
  (G.absorbInto x y).Adj (proj v h) (proj w h) ∨ proj v h = proj w h := by
  by_cases hp : proj v h = proj w h
  · exact Or.inr hp
  · simp [absorbInto, proj] at *
    split_ifs at *
    all_goals simp_all
    right
    exact e.symm



lemma proj_of_ne (h : x ≠ y) (hv : v ≠ y) : proj v h = v := by simp[proj, hv]

lemma proj_val (v : {z // z ≠ y}) (h : x ≠ y) : proj (↑v) h = v := by simp[v.property, proj]

noncomputable
def transport (h : x ≠ y) {u v : V} : G.Walk u v → (G.absorbInto x y).Walk (proj u h) (proj v h)
  | Walk.nil => Walk.nil
  | Walk.cons e p => by
    rename_i w
    by_cases h₀ : proj u h = proj w h
    · exact (transport h p).copy h₀.symm rfl
    · exact Walk.cons (Or.resolve_right (proj_adj e h) h₀) (transport h p)

noncomputable
def liftEdge {u v : {z // z ≠ y}}
  (e : G.Adj x y) (e' : (G.absorbInto x y).Adj u v) : G.Walk ↑u ↑v := by
  obtain ⟨_, h⟩ := e'
  by_cases h_adj : G.Adj ↑u ↑v
  · exact h_adj.toWalk
  by_cases hv : x = ↑u ∧ G.Adj ↑v y
  · exact Walk.cons (hv.1 ▸ e) (hv.2.symm.toWalk)
  simp[h_adj, hv] at h
  exact Walk.cons h.2 (h.1 ▸ e.symm).toWalk

noncomputable
def liftWalk {u v : {z // z ≠ y}} (e : G.Adj x y) : (G.absorbInto x y).Walk u v →  G.Walk u v
  | Walk.nil => Walk.nil
  | Walk.cons e' p' => Walk.append (liftEdge e e') (liftWalk e p')


lemma support_liftEdge {e : G.Adj x y} {u v : {z // z ≠ y}}
  (e' : (G.absorbInto x y).Adj u v) {a : V} (ha : a ∈ (liftEdge e e').support) :
  a = ↑u ∨ a = ↑v ∨ (a = y ∧ (x = ↑u ∨ x = ↑v)) := by
  rw [liftEdge] at ha
  rcases e' with ⟨ne, e_norm | ⟨rfl, e_u⟩ | ⟨rfl, e_v⟩⟩ <;>
  try split_ifs at ha <;>
  simp only [Walk.support_cons, Walk.support_nil, List.mem_cons] at ha <;>
  tauto

lemma support_liftWalk {e : G.Adj x y} {u v : {z // z ≠ y}} (p : (G.absorbInto x y).Walk u v) :
  ∀ a ∈ (liftWalk e p).support, proj a e.ne ∈ p.support := by
  intro a ha
  induction p with
   | nil =>
     simp[liftWalk] at *
     rw[ha, proj_val]
   | cons _ _ ih =>
     simp [liftWalk, Walk.support_cons] at *
     rcases ha with (ha | ha)
     · rcases support_liftEdge _ ha with rfl | rfl | ⟨rfl, rfl | rfl⟩
        <;> simp[proj_val] <;> simp[proj]
     simp[ih ha]


lemma IsVertexSeparator.liftSep' {u v : {z // z ≠ y}} (e : G.Adj x y)
  (h : G.IsVertexSeparator S ↑u ↑v) (hu : x ≠ u) (hv : x ≠ v) :
  (G.absorbInto x y).IsVertexSeparator ((proj · e.ne) '' S) u v := by
  refine ⟨?_, ?_⟩
  · intro p
    obtain ⟨s, ⟨hS, h_supp⟩⟩ := h.1 <| liftWalk e p
    refine ⟨proj s e.ne, ⟨s, hS, rfl⟩, support_liftWalk p s h_supp⟩
  let := h.2
  refine ⟨?_, ?_⟩
  · rintro ⟨z, ⟨hz, rfl⟩⟩
    have zne: z ≠ y := by
      rintro rfl
      apply hu
      simp[proj]
    simp[proj_of_ne _ zne] at this
    exact this.1 hz
  rintro ⟨z, ⟨hz, rfl⟩⟩
  have zne: z ≠ y := by
    rintro rfl
    apply hv
    simp[proj]
  simp[proj_of_ne _ zne] at this
  exact this.2 hz

lemma IsVertexSeparator.liftSep'' (e : G.Adj x y)
  (hv : x ≠ v ∧ y ≠ v) (hw : x ≠ w ∧ y ≠ w) (h : G.IsVertexSeparator S v w) :
  (G.absorbInto x y).IsVertexSeparator ((proj · e.ne) '' S) (proj v e.ne) (proj w e.ne) := by
  have v_eq : ↑(proj v e.ne) = v := proj_of_ne e.ne hv.2.symm
  have w_eq : ↑(proj w e.ne) = w := proj_of_ne e.ne hw.2.symm
  have hvx : x ≠ ↑(proj v e.ne) := by simp[v_eq, hv.1]
  have hwx : x ≠ ↑(proj w e.ne) := by simp[w_eq, hw.1]
  exact (w_eq ▸ v_eq ▸ h).liftSep' e hvx hwx


lemma transport_prop {u v : V} (h : x ≠ y) (p : G.Walk u v) :
  ∀ z ∈ (transport h p).support, ↑z ∈ p.support ∨ ↑z = x := by
  induction p with
    | nil =>
      intro z hz
      simp[transport] at *
      by_cases hz' : z = x
      · exact Or.inr hz'
      left
      rw[hz]
      apply proj_of_ne
      intro hu
      simp[proj, hu] at hz
      exact hz' (Subtype.val_inj.2 hz)
    | cons e p ih =>
      intro z hz
      rename_i u w v
      by_cases heq : proj u h = proj w h
      · simp[transport, heq] at hz
        rcases ih z hz with (h | h)
        · rw[Walk.support_cons, List.mem_cons]
          left; right;
          exact h
        · exact Or.inr h
      simp[transport, heq] at hz
      rw[Walk.support_cons, List.mem_cons] at *
      rcases hz with (h' | h')
      by_cases hu : proj u h = u
      · simp[h', hu]
      · right
        have: u = y := by
          contrapose hu
          push_neg
          apply proj_of_ne
          exact hu
        simp[h', proj, this]
      rcases ih z h' with (h' | h')
      · left; right; exact h'
      · exact Or.inr h'


lemma transport_y_free_walk {u v : V} (p : G.Walk u v) (h : x ≠ y) (hy : y ∉ p.support) :
  ∀ z ∈ (transport h p).support, z.val ∈ p.support := by
  induction p with
    | nil =>
      intro z hz
      rw[transport, Walk.mem_support_nil_iff] at *
      subst hz
      apply proj_of_ne
      intro; apply hy; symm; assumption
    | cons e p ih =>
      intro z hz
      rename_i u w v
      rw[transport, Walk.support_cons, List.mem_cons] at *
      split_ifs at hz
      · rw[Walk.support_copy] at hz
        exact Or.inr <| ih (not_or.1 hy).2 z hz
      · rw[Walk.support_cons, List.mem_cons] at hz
        rcases hz with (hz | hz)
        · subst hz
          left
          apply proj_of_ne
          symm
          exact(not_or.1 hy).1
        · exact Or.inr <| ih (not_or.1 hy).2 z hz


lemma keep_sep_no_x {X : Set {z // z ≠ y}} (h : x ≠ y) (hX : (G.absorbInto x y).IsSeparator X)
  (xne : x ∉ Subtype.val '' X) :
  G.IsSeparator (Subtype.val '' X) := by
  rcases hX with ⟨v, w, h'⟩
  refine ⟨↑v, ↑w, ⟨?_, ?_⟩⟩
  · intro p
    let p_trans := Walk.copy (transport h p) (proj_val v h) (proj_val w h)
    rcases h'.1 p_trans with ⟨s, hs⟩
    use ↑s
    constructor
    · use s
      exact ⟨hs.1, rfl⟩

    rw[Walk.support_copy] at hs
    rcases (transport_prop h p) s hs.2 with (h' | rfl)
    · assumption
    · exfalso
      apply xne
      use s
      exact ⟨hs.1, rfl⟩
  simp only [Set.mem_image, Subtype.val_inj]
  simpa using h'.2


lemma keep_sep {X : Set {z // z ≠ y}} (h : x ≠ y) (hX : (G.absorbInto x y).IsSeparator X) :
  G.IsSeparator ((Subtype.val '' X) ∪ {y}) := by
  rcases hX with ⟨v, w, h'⟩
  refine ⟨↑v, ↑w, ⟨?_, ?_⟩⟩
  · intro p
    let p_trans := Walk.copy (transport h p) (proj_val v h) (proj_val w h)
    by_cases hy : y ∈ p.support
    · use y
      exact ⟨by simp, hy⟩
    · rcases h'.1 p_trans with ⟨s, hs⟩
      use ↑s
      constructor
      · left
        use s
        exact ⟨hs.1, rfl⟩
      rw[Walk.support_copy] at hs
      exact transport_y_free_walk p h hy s hs.2
  simp[h'.2, Set.mem_image, Subtype.val_inj, v.property, w.property]


lemma IsMinimumSeparator.adj_comp [Fintype V] {X : Set V} (h : G.IsMinimumSeparator X) :
  ∀ C : (G.induce Xᶜ).ConnectedComponent, ∀ x ∈ X, ∃ c ∈ C.supp, G.Adj x c := by
  classical
  by_contra! h'
  rcases h' with ⟨C, x, ⟨hx, hC⟩⟩
  have X_sep : G.IsSeparator (X \ {x}) := by
    obtain ⟨c, hC'⟩ := C.nonempty_supp
    have xneqc : x ≠ ↑c := by
      intro rfl
      exact c.property hx

    have cX : ↑c ∉ X \ {x} := by
      rintro ⟨cinX, _⟩
      exact c.property cinX

    refine ⟨x, c, ⟨?_, ⟨by simp, cX⟩⟩⟩
    intro p
    by_contra! hp
    rcases sub_walker p.toPath xneqc (hC c hC') with ⟨y, p', hp'⟩
    have p'_avoids_X : ∀ v ∈ p'.support, v ∈ Xᶜ := by
      intro v vp' vx
      by_cases hv : v = x
      · apply hp'.1
        rwa[← hv]
      have: v ∈ X \ {x} := by exact ⟨vx, hv⟩
      apply hp v this
      exact Set.Subset.trans hp'.2.1 (Walk.support_toPath_subset p) vp'

    let p'' := p'.induce Xᶜ p'_avoids_X
    have: y ∉ Subtype.val '' C.supp := by
      intro ⟨_ , ⟨hy, hy'⟩⟩
      exact hp'.2.2 |> hy' ▸ hC _ hy

    have: ⟨y, p'_avoids_X _ p'.start_mem_support⟩ ∉ C.supp := by
      rintro hy
      have: y ∈ Subtype.val '' C.supp := by use ⟨y, p'_avoids_X _ p'.start_mem_support⟩
      contradiction
    exact C.isClosed_supp <| exists_crossing_edge hC' this p''.reachable.symm
  have: (X \ {x}).Finite := Set.Finite.diff h.1

  linarith[h.2.2 (X \ {x}) ⟨this, X_sep⟩, Set.ncard_diff_singleton_lt_of_mem hx]

lemma aux₀ [Fintype V] (e : G.Adj x y) (h_card : Fintype.card V > 4)
  (h_conn : G.IsVertexConnected 3)
  (h_sep : ¬((G.absorbInto x y).IsVertexConnected 3)) :
  ∃ z , G.IsSeparator {x, y, z} := by
  classical
  dsimp[IsVertexConnected] at h_sep
  push_neg at h_sep
  have absorb_card : ∃ X : Set {x // x ≠ y}, X.ncard > 3 := by
    use Set.univ
    simp; omega

  rcases h_sep absorb_card with ⟨S, hS⟩

  have S_card: S.ncard = 2 := by
    by_cases h' : S.ncard < 2
    · have sep_ncard : ((Subtype.val '' S) ∪ {y}).ncard < 3 := by
        apply lt_of_le_of_lt <| Set.ncard_union_le (Subtype.val '' S) {y}
        rw[Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_singleton]
        omega
      exfalso
      apply h_conn.2
      use (Subtype.val '' S) ∪ {y}
      refine ⟨?_, sep_ncard, keep_sep e.ne hS.2.2⟩
      rw[Set.finite_union]
      exact ⟨Set.Finite.image Subtype.val hS.1, Set.finite_singleton y⟩
    omega

  have xinS: ⟨x, e.ne⟩ ∈ S := by
    by_contra! hx
    have: x ∉ Subtype.val '' S := by simp[hx]
    exfalso
    apply h_conn.2
    use Subtype.val '' S
    refine ⟨Set.Finite.image Subtype.val hS.1, ?_, keep_sep_no_x e.ne hS.2.2 this⟩
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

    exact H e h_card h_conn h_sep absorb_card S hS S_card xinS b a wl beqx

  use b
  have: Subtype.val '' S ∪ {y} = {x, y, ↑b} := by grind
  exact this ▸ keep_sep e.ne hS.2.2


lemma exists_edge_of_connected_nontrivial [Nontrivial V]
  (h : G.Connected) : ∃ u v : V, G.Adj u v := by
  obtain ⟨u, v, h_neq⟩ := exists_pair_ne V
  obtain ⟨p⟩ := h.preconnected u v
  cases p with
  | nil => contradiction
  | cons h_adj _ =>
    exact ⟨_, _, h_adj⟩


lemma IsVertexConnected.exists_edge {k : ℕ} (hk : k ≥ 1) (h : G.IsVertexConnected k) :
  ∃ x y : V, G.Adj x y := by
  have: Nontrivial V := by
    obtain ⟨X, hX⟩ := h.1
    have: X.ncard > 1 := by omega
    obtain ⟨x⟩ := h.nonempty
    obtain ⟨b, hb⟩ := Set.exists_ne_of_one_lt_ncard this x
    exact ⟨x, b, hb.2.symm⟩
  exact exists_edge_of_connected_nontrivial (h.Connected (by omega))


lemma exists_min_comp_card [Nonempty V] [Fintype V] :
  ∃ C : G.ConnectedComponent, ∀ C' : G.ConnectedComponent, C.supp.ncard ≤ C'.supp.ncard :=
  Finite.exists_min _


lemma three_compl_nonempty [Fintype V] (x y z : V) (h_card : Fintype.card V > 4) :
  Nonempty ({x,y,z}ᶜ : Set V) := by
  rw[Set.nonempty_coe_sort, Set.nonempty_iff_empty_ne]
  intro h
  have univ: {x,y,z} = (Set.univ : Set V) := Set.compl_empty_iff.1 h.symm
  have univ_card : ({x,y,z} : Set V).ncard ≤ 3:= by
    linarith [Set.ncard_insert_le x {y, z}, Set.ncard_insert_le y {z}, Set.ncard_singleton z]
  rw[Fintype.card_eq_nat_card, ← Set.ncard_univ, ← univ] at h_card
  omega

noncomputable
def score_sep' [Fintype V] (x y z : V) (h_card : Fintype.card V > 4) :
  (G.induce {x,y,z}ᶜ).ConnectedComponent := by
  classical
  let nonempty := three_compl_nonempty x y z h_card
  exact ((G.induce {x,y,z}ᶜ).exists_min_comp_card).choose


lemma score_sep'_prop [Fintype V]
  (x y z : V) (h_card : Fintype.card V > 4) (C : (G.induce {x,y,z}ᶜ).ConnectedComponent) :
  (G.score_sep' x y z h_card).supp.ncard ≤ C.supp.ncard := by
  classical
  let nonempty := three_compl_nonempty x y z h_card
  exact ((G.induce {x,y,z}ᶜ).exists_min_comp_card).choose_spec C


noncomputable
def score_sep [Fintype V] (x y z : V) (h_card : Fintype.card V > 4) : ℕ := by
  classical
  let nonempty := three_compl_nonempty x y z h_card
  let min_comp := ((G.induce {x,y,z}ᶜ).exists_min_comp_card).choose
  exact min_comp.supp.ncard


lemma score_sep_min' [Fintype V] (h_card : Fintype.card V > 4)
  (h_exists : ∃ x y z, G.Adj x y ∧ G.IsSeparator {x, y, z}) :
  ∃ (x y z : V), G.Adj x y ∧ G.IsSeparator {x, y, z} ∧
  ∀ (x' y' z' : V), G.Adj x' y' ∧ G.IsSeparator {x', y', z'} →
    (G.score_sep' x y z h_card).supp.ncard ≤ (G.score_sep' x' y' z' h_card).supp.ncard := by
  classical
  let P := fun (n : ℕ) ↦ ∃ (x y z : V)
                            (e : G.Adj x y)
                            (hz : G.IsSeparator {x,y,z}) ,
                            (G.score_sep' x y z h_card).supp.ncard = n

  have hP_exists : ∃ n, P n := by
    obtain ⟨x, y, z, ⟨e, hz⟩⟩ := h_exists
    refine ⟨G.score_sep x y z h_card, ⟨x,y,z,e,hz,rfl⟩⟩
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

lemma not_connected_exists_components [Nonempty V] (h : ¬G.Connected) :
  ∃ C D : G.ConnectedComponent, C ≠ D := by
  contrapose! h
  rw[connected_iff_exists_forall_reachable]
  obtain ⟨x⟩ := ‹Nonempty V›
  use x
  intro y
  exact ConnectedComponent.eq.1 <| h (G.connectedComponentMk x) (G.connectedComponentMk y)

lemma adj_exists_connectedComponent (e : G.Adj x y) :
  ∃ C : G.ConnectedComponent, x ∈ C.supp ∧ y ∈ C.supp := by
  use G.connectedComponentMk x
  constructor
  · exact ConnectedComponent.connectedComponentMk_mem
  · rw[← ConnectedComponent.connectedComponentMk_eq_of_adj e.symm]
    exact ConnectedComponent.connectedComponentMk_mem


lemma not_conn_comp_ne [Nonempty V] (h : ¬G.Connected) (C : G.ConnectedComponent) :
  ∃ D, C ≠ D := by
  obtain ⟨C₀, C₁, h⟩ := not_connected_exists_components h
  by_cases h_eq : C = C₀
  · use C₁
    rwa[h_eq]
  · use C₀

lemma not_conn_exists_comp' (x : V) (hC : ¬(G.induce S).Connected) (hS : Nonempty S) :
  ∃ C : (G.induce S).ConnectedComponent, x ∉ (↑) '' C.supp := by
  obtain ⟨C, D, h_ne⟩ := not_connected_exists_components hC
  by_cases hx : x ∈ (↑) '' C.supp
  · use D
    obtain ⟨x, ⟨hx, rfl⟩⟩ := hx
    rw[Subtype.val_injective.mem_set_image]
    exact ((G.induce S).pairwise_disjoint_supp_connectedComponent h_ne).notMem_of_mem_left hx
  use C


lemma not_conn_exist_comp {S : Set V}
  (e : G.Adj x y) (hC : ¬(G.induce S).Connected) (hS : Nonempty S) :
  ∃ C : (G.induce S).ConnectedComponent, x ∉ Subtype.val '' C.supp ∧ y ∉ Subtype.val '' C.supp := by
  obtain ⟨C, hCx⟩ := not_conn_exists_comp' x hC hS
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


lemma IsVertexConnected.is_minimum_separator_of_ncard_le [Fintype V] {k : ℕ} {X : Set V}
  (h : G.IsVertexConnected k) (h_sep : G.IsSeparator X) (h_card : X.ncard ≤ k) :
  G.IsMinimumSeparator X := by
  refine ⟨Set.toFinite X, h_sep, ?_⟩
  by_contra hS
  rcases not_forall.1 hS with ⟨S, hS⟩
  push_neg at hS
  apply h.2
  refine ⟨S, hS.1.1, lt_of_lt_of_le hS.2 h_card, hS.1.2⟩

lemma Set.three_le_ncard {x y z : V} : ({x,y,z} : Set V).ncard ≤ 3 := by
  linarith[Set.ncard_insert_le x ({y,z} : Set V),
           Set.ncard_insert_le y ({z} : Set V),
           Set.ncard_singleton z]


lemma aux_main [Fintype V] (h : G.IsVertexConnected 3) (h_card : Fintype.card V > 4) :
  ∃ x y : V, G.Adj x y ∧ (G.absorbInto x y).IsVertexConnected 3 := by
  classical
  by_contra! no_edge
  obtain ⟨x₀, y₀, xy₀⟩ := h.exists_edge (by decide)
  have not_conn_xy := no_edge x₀ y₀ xy₀
  obtain ⟨z₀, hz⟩ := aux₀ xy₀ h_card h not_conn_xy
  obtain ⟨x, y, z, xy, h_sep, h_min⟩ := G.score_sep_min' h_card (by refine ⟨x₀, y₀, z₀, xy₀, hz⟩)

  have h_sep_min: G.IsMinimumSeparator {x,y,z} :=
    h.is_minimum_separator_of_ncard_le h_sep Set.three_le_ncard

  obtain ⟨v, hv⟩ := h_sep_min.adj_comp (score_sep' x y z h_card) z (by simp)
  have not_conn_zv := no_edge z v hv.2
  obtain ⟨w, h_zv_sep⟩ := aux₀ hv.2 h_card h not_conn_zv
  have nonempty_compl := three_compl_nonempty z ↑v w h_card

  obtain ⟨D, hD⟩ := not_conn_exist_comp xy h_zv_sep.not_connected nonempty_compl

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

  have dscore: ↑d ∈ Subtype.val '' (G.score_sep' x y z h_card).supp := by
    obtain ⟨v', d', vd', hv', hd'⟩ := exists_edge_induced vd.2 v.property hd
    have veqv': v' = v := by grind
    exact hd' ▸ Subtype.val_injective.mem_set_image.2 <|
          ConnectedComponent.mem_supp_of_adj_mem_supp _ hv.1 (veqv' ▸ vd')

  have Dss: ↑D.supp ⊆ Subtype.val '' (G.score_sep' x y z h_card).supp := by
    rintro _ ⟨a, ⟨ha, rfl⟩⟩
    obtain ⟨Dwalk⟩ := D.reachable_of_mem_supp vd.1 ha
    have walkssD: ∀ t ∈ Dwalk.support, t ∈ D.supp := by
      intro t ht
      exact D.isClosed_supp.mem_of_reachable vd.1 (Walk.takeUntil Dwalk t ht).reachable

    let Gwalk := Dwalk.map (Embedding.induce _).toHom
    have: ∀ t ∈ Gwalk.support, t ∈ ({x,y,z}ᶜ : Set V) := by
      intro t ht
      obtain ⟨t', ht'⟩ := List.mem_map.1 <| Dwalk.support_map (Embedding.induce _).toHom ▸ ht
      have: ↑t' ∈ Subtype.val '' D.supp := Subtype.val_injective.mem_set_image.2 <| walkssD t' ht'.1
      exact ht'.2 ▸ Dss_compl this

    have din : ⟨↑d, hd⟩ ∈ (G.score_sep' x y z h_card).supp := by grind
    have ain := (ConnectedComponent.mem_supp_iff _ _).1 din ▸
                 ConnectedComponent.sound (Gwalk.induce _ this).reachable
    exact Subtype.val_injective.mem_set_image.2 <| (ConnectedComponent.mem_supp_iff _ _).2 ain.symm


  have: D.supp.ncard < (G.score_sep' x y z h_card).supp.ncard := by
     repeat rw[← Set.ncard_image_of_injective _ Subtype.val_injective]
     apply Set.ncard_lt_ncard _ (Set.toFinite _)
     rw[Set.ssubset_iff_exists]
     refine ⟨Dss, ⟨v, by grind⟩⟩

  linarith[(G.score_sep'_prop z ↑v w h_card D),
          h_min z ↑v w ⟨hv.2, h_zv_sep⟩]


lemma IsVertexSeparator.funny_lemma (e : G.Adj x y)
  (h : G.IsVertexSeparator S v x) (hy : y ∉ S) (hv : v ≠ x ∧ v ≠ y) :
  (G.absorbInto x y).IsVertexSeparator ((proj · e.ne) '' S) (proj v e.ne) (proj x e.ne) := by
  refine ⟨?_, ?_⟩
  · intro p
    let p' := liftWalk e p
    let p'_copy : G.Walk v x := p'.copy (by simp[hv.2, proj]) (by simp[e.ne, proj])
    obtain ⟨s, ⟨hs, hp⟩⟩ := h.1 p'_copy
    have s_ne : s ≠ y := by grind
    refine ⟨⟨s, s_ne⟩, ⟨?_, ?_⟩⟩
    · use s, hs
      simp[s_ne, proj]
    rw[Walk.support_copy] at hp
    apply support_liftWalk _ _ at hp
    simp[proj, s_ne] at hp
    assumption
  refine ⟨?_, ?_⟩
  · rintro ⟨v', hv'⟩
    have v'_ne : v' ≠ y := by grind
    simp[proj, hv.2, v'_ne] at hv'
    exact hv'.2 ▸ h.2.1 <| hv'.1
  simp[proj, e.ne]
  intro s hs
  refine ⟨by intro h; exact h ▸ hy <| hs, by intro h'; exact h' ▸ h.2.2 <| hs⟩

lemma IsSeparator.trans' (e : G.Adj x y) (hS : x ∉ S ∧ y ∉ S) (h : G.IsSeparator S) :
  (G.absorbInto x y).IsSeparator ((proj · e.ne) '' S) := by
  have nonempty: Nonempty ↑Sᶜ := h.compl_nonempty
  let not_conn := h.not_connected
  obtain ⟨C, hC⟩ := not_conn_exist_comp e not_conn nonempty
  obtain ⟨D, h_ne⟩ := not_conn_comp_ne not_conn C
  obtain ⟨v, vC⟩ := C.nonempty_supp
  obtain ⟨w, wD⟩ := D.nonempty_supp
  let vw_sep := IsVertexSeparator.fromComponents C D h_ne _ vC _ wD
  have v_ne: v ≠ x ∧ v ≠ y := by grind
  by_cases hw : ↑w = y
  · let xv_sep := vw_sep.symm.fromAdj (hw ▸ e.symm) hS.1
    exact (IsVertexSeparator.funny_lemma e xv_sep.symm hS.2 v_ne).toSeparator
  · by_cases weq : ↑w = x
    · exact (IsVertexSeparator.funny_lemma e (weq ▸ vw_sep) hS.2 v_ne).toSeparator
    · exact (vw_sep.liftSep'' e ⟨v_ne.1.symm, v_ne.2.symm⟩ ⟨by symm; exact weq, by symm; exact hw⟩).toSeparator


open Classical in
lemma has_neighbor_outside {k : ℕ} [Fintype V] (h : G.degree x ≥ k) (hS : S.ncard < k) :
  ∃ v, G.Adj x v ∧ v ∉ S := by
  by_contra! hv
  have h_sub: G.neighborSet x ⊆ S := hv
  have: (G.neighborSet x).ncard ≥ k := by
    rwa[Set.ncard_eq_toFinset_card', ← G.neighborFinset_def, G.card_neighborFinset_eq_degree x]
  linarith[Set.ncard_le_ncard h_sub]

universe u

open Classical in
inductive TutteConstructable : ∀ {V : Type u} [Fintype V], SimpleGraph V → Prop
  | k4 {V : Type u} [Fintype V] (G : SimpleGraph V) :
      Nonempty (G ≃g completeGraph (Fin 4)) →
      TutteConstructable G
  | step {V V' : Type u} [Fintype V] [Fintype V']
      (G : SimpleGraph V) (G' : SimpleGraph V') (x y : V) :
      G.Adj x y →
      G.degree x ≥ 3 →
      G.degree y ≥ 3 →
      Nonempty (G' ≃g G.absorbInto x y) →
      TutteConstructable G'→
      TutteConstructable G

lemma TutteConstructable.is_three_connected [Fintype V]
  (h : TutteConstructable G) : G.IsVertexConnected 3 := by
  induction h with
    | k4 G k4_iso =>
      obtain ⟨ψ⟩ := k4_iso
      have: (completeGraph (Fin 4)).IsVertexConnected (4 - 1)
        := IsVertexConnected.is_vertex_connected_completeGraph_of_ncard_eq (by simp) (by decide)
      exact IsVertexConnected.iso this ψ.symm

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

      obtain ⟨C, hC⟩ := not_conn_exist_comp e not_conn nonempty
      obtain ⟨D, h_ne⟩ := not_conn_comp_ne not_conn C
      obtain ⟨v, vC⟩ := C.nonempty_supp
      obtain ⟨w, wD⟩ := D.nonempty_supp
      let vw_sep := IsVertexSeparator.fromComponents C D h_ne _ vC _ wD
      have v_ne: x ≠ v ∧ y ≠ v := by grind
      apply ih.2
      let S' := ψ.symm '' ((proj · e.ne) '' S)
      have S'_fin : S'.Finite := by
          repeat apply Set.Finite.image
          exact Set.toFinite S
      have S'_card_le : S'.ncard ≤ S.ncard := by
        simpa only [S', Set.image_image] using Set.ncard_image_le (Set.toFinite S)

      refine ⟨S', S'_fin, by linarith, ?_⟩
      apply IsSeparator.image_iso ?_ ψ.symm
      by_cases w_ne: x ≠ w ∧ y ≠ w
      · exact (vw_sep.liftSep'' e v_ne w_ne).toSeparator
      simp only [not_and_or, not_ne_iff] at w_ne
      have: S.ncard < 3 := by linarith
      rcases w_ne with rfl | rfl
      · by_cases hy : y ∈ S
        · obtain ⟨u, hu⟩ := has_neighbor_outside h_deg_x this
          have une : y ≠ u := by grind
          let uv_sep := (vw_sep.symm.fromAdj hu.1 hu.2)
          exact (uv_sep.liftSep'' e ⟨hu.1.ne, une⟩ v_ne).toSeparator
        · exact IsSeparator.trans' e ⟨w.property, hy⟩ hS.2.2
      · by_cases hx : x ∈ S
        · obtain ⟨u, hu⟩ := has_neighbor_outside h_deg_y this
          have une : x ≠ u := by grind
          let uv_sep := (vw_sep.symm.fromAdj hu.1 hu.2)
          exact (uv_sep.liftSep'' e ⟨une, hu.1.ne⟩ v_ne).toSeparator
        · exact IsSeparator.trans' e ⟨hx, w.property⟩ hS.2.2

private lemma is_three_connected_tutte_helper (m : ℕ) :
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
  Fintype.card V = m + 4 → G.IsVertexConnected 3 → TutteConstructable G := by
  classical
  induction m with
  | zero =>
    intro V _ G h_card h_conn
    apply TutteConstructable.k4 G
    rw[h_conn.eq_completeGraph_of_card_eq h_card]
    have h_eq : Fintype.card V = Fintype.card (Fin 4) := by simp[h_card]
    let e : V ≃ Fin 4 := Fintype.equivOfCardEq h_eq
    exact ⟨Iso.completeGraph e⟩

  | succ k ih =>
    intro V _ G h_card h_conn
    obtain ⟨x, y, ⟨e, h⟩⟩ := aux_main h_conn (by simp[h_card])
    let constructable := ih {z // z ≠ y} (G.absorbInto x y) (by simp[h_card]) h
    exact TutteConstructable.step G (G.absorbInto x y)
          x y e (h_conn.le_degree x) (h_conn.le_degree y) ⟨Iso.refl⟩ constructable


lemma is_three_connected_tutte [Fintype V] (h : G.IsVertexConnected 3) : TutteConstructable G := by
  have: Fintype.card V ≥ 4 := by
    obtain ⟨X, _⟩ := h.1
    rw[Fintype.card_eq_nat_card, ← Set.ncard_univ]
    linarith[Set.ncard_le_ncard (Set.subset_univ X)]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le this
  exact is_three_connected_tutte_helper m V G (by linarith[hm]) h


theorem thm_325 [Fintype V] : G.IsVertexConnected 3 ↔ TutteConstructable G :=
    Iff.intro is_three_connected_tutte TutteConstructable.is_three_connected



end SimpleGraph
