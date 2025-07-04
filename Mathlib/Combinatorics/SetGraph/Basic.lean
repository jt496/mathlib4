import Mathlib.Data.Finite.Prod
import Mathlib.Data.Rel
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fintype.Powerset
set_option linter.style.header false
universe u v
variable {ι : Sort*} {V : Type u} {W : Type v}

/-!
Version of SimpleGraph API based on Subgraph/SimpleGraph but with nicer vertex sets
-/

@[ext]
structure SetGraph (V : Type u)  where
  /-- Vertices of the graph -/
  verts : Set V
  /-- Edges of the graph -/
  Adj : V → V → Prop
  edge_vert : ∀ {v w : V}, Adj v w → v ∈ verts
  symm : Symmetric Adj
  loopless : Irreflexive Adj

initialize_simps_projections SetGraph (Adj → adj)


namespace SetGraph

variable {G₁ G₂ : SetGraph V} {a b : V}


@[simp]
protected theorem irrefl (G : SetGraph V) {v : V} : ¬ G.Adj v v :=
  G.loopless v

theorem adj_comm (G : SetGraph V) (v w : V) : G.Adj v w ↔ G.Adj w v :=
  ⟨fun x ↦ G.symm x, fun x ↦ G.symm x⟩

@[symm]
theorem adj_symm (G : SetGraph V) {u v : V} (h : G.Adj u v) : G.Adj v u :=
  G.symm h

protected theorem Adj.symm {G : SetGraph V} {u v : V} (h : G.Adj u v) : G.Adj v u :=
  G.symm h

@[simp]
protected lemma Adj.mem_verts {G : SetGraph V} {v w : V} (h : G.Adj v w) : v ∈ G.verts :=
   G.edge_vert h

@[simp]
protected lemma Adj.mem_verts' {G : SetGraph V} {v w : V} (h : G.Adj w v) :
    v ∈ G.verts := h.symm.mem_verts

variable (G : SetGraph V)

theorem ne_of_adj (h : G.Adj a b) : a ≠ b := by
  rintro rfl
  exact G.irrefl h

variable {G}
protected theorem Adj.ne {a b : V} (h : G.Adj a b) : a ≠ b :=
  ne_of_adj G h

protected theorem Adj.ne' {a b : V} (h : G.Adj a b) : b ≠ a :=
  h.ne.symm

protected theorem Adj.fst_mem {H : SetGraph V} {u v : V} (h : H.Adj u v) : u ∈ H.verts :=
  H.edge_vert h

protected theorem Adj.snd_mem {H : SetGraph V} {u v : V} (h : H.Adj u v) : v ∈ H.verts :=
  h.symm.fst_mem

theorem ne_of_adj_of_not_adj {v w x : V} (h : G.Adj v x) (hn : ¬G.Adj w x) : v ≠ w := fun h' =>
  hn (h' ▸ h)

theorem adj_congr_of_sym2 {H : SetGraph V} {u v w x : V} (h2 : s(u, v) = s(w, x)) :
    H.Adj u v ↔ H.Adj w x := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at h2
  rcases h2 with hl | hr
  · rw [hl.1, hl.2]
  · rw [hr.1, hr.2, SetGraph.adj_comm]

lemma not_adj_of_notMem_verts {u v : V} {G : SetGraph V} (h : u ∉ G.verts) : ¬ G.Adj u v := by
  contrapose! h
  exact h.mem_verts


/--
A SetGraph is called a *spanning SetGraph* if it contains all the vertices in the vertex type
-/
def IsSpanning (G : SetGraph V) : Prop :=
  G.verts = Set.univ


def toSpanning (G : SetGraph V) : SetGraph V where
  verts := Set.univ
  Adj := G.Adj
  edge_vert h := by trivial
  symm := G.symm
  loopless := G.loopless

@[simp]
lemma toSpanning_verts {G : SetGraph V} : G.toSpanning.verts = Set.univ := rfl

@[simp]
lemma toSpanning_adj {G : SetGraph V} : G.toSpanning.Adj = G.Adj := rfl


@[simp]
lemma toSpanning_eq_iff : G.toSpanning = G ↔ G.verts = Set.univ := by
  constructor <;> intro h
  · rw [SetGraph.ext_iff, toSpanning_verts] at h
    exact h.1.symm
  · rw [SetGraph.ext_iff, toSpanning_verts, toSpanning_adj]
    exact ⟨h.symm, rfl⟩

theorem isSpanning_iff {G : SetGraph V} : G.IsSpanning ↔ G.verts = Set.univ := Iff.rfl

protected alias ⟨IsSpanning.verts_eq_univ, _⟩ := isSpanning_iff

/-- `H.support` is the set of vertices that form edges in the SetGraph `H`. -/
def support (H : SetGraph V) : Set V := Rel.dom H.Adj

theorem mem_support (H : SetGraph V) {v : V} : v ∈ H.support ↔ ∃ w, H.Adj v w := Iff.rfl

theorem support_subset_verts (H : SetGraph V) : H.support ⊆ H.verts :=
  fun _ ⟨_, h⟩ ↦ H.edge_vert h

/-- `G.neighborSet v` is the set of vertices adjacent to `v` in `G`.
We don't restrict to `v ∈ G.verts` since for any `v ∉ G.verts` this set is empty -/
def neighborSet (G : SetGraph V) (v : V) : Set V := {w | G.Adj v w}

instance neighborSet.memDecidable (v : V) [DecidableRel G.Adj] :
    DecidablePred (· ∈ G.neighborSet v) :=
  inferInstanceAs <| DecidablePred (Adj G v)

theorem neighborSet_subset_verts (G : SetGraph V) (v : V) : G.neighborSet v ⊆ G.verts :=
  fun _ h ↦ G.edge_vert (adj_symm G h)

theorem neighborSet_subset_support (G : SetGraph V) (v : V) : G.neighborSet v ⊆ G.support := by
  intro x h
  rw [mem_support]
  use v, h.symm

@[simp]
theorem mem_neighborSet (G : SetGraph V) (v w : V) : w ∈ G.neighborSet v ↔ G.Adj v w := Iff.rfl

/-- The edge set of `G` consists of a subset of edges of `G`. -/
def edgeSet (G : SetGraph V) : Set (Sym2 V) := Sym2.fromRel G.symm

@[simp]
lemma mem_edgeSet {G : SetGraph V} {v w : V} : s(v, w) ∈ G.edgeSet ↔ G.Adj v w := .rfl

lemma edgeSet_subset_edgeSet  {G H : SetGraph V} : G.edgeSet ⊆ H.edgeSet ↔ G.Adj ≤ H.Adj := by
  constructor <;> intro h
  · intro u v h'
    rw [← mem_edgeSet] at *
    exact h h'
  · intro e h'
    cases e with
    | h u v =>
    rw [mem_edgeSet] at *
    exact h _ _ h'

lemma edgeSet_eq_iff  {G H : SetGraph V} : G.edgeSet = H.edgeSet ↔ G.Adj = H.Adj := by
  constructor <;> intro h
  · exact le_antisymm (edgeSet_subset_edgeSet.1 h.le) (edgeSet_subset_edgeSet.1 h.symm.le)
  · exact le_antisymm (edgeSet_subset_edgeSet.2 h.le) (edgeSet_subset_edgeSet.2 h.symm.le)

@[simp]
lemma toSpanning_edgeSet {G : SetGraph V} : G.toSpanning.edgeSet = G.edgeSet := rfl

lemma edgeSet_eq_empty_iff {G : SetGraph V} : G.edgeSet = ∅  ↔ ∀ {u v}, ¬ G.Adj u v := by
  rw [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h1 u v h2
    apply h1 s(u,v) h2
  · intro h1 e h2
    cases e with
    | h u v =>
      apply h1 h2

theorem mem_verts_of_mem_edge {G : SetGraph V} {e : Sym2 V} {v : V} (he : e ∈ G.edgeSet)
    (hv : v ∈ e) : v ∈ G.verts := by
  induction e
  rcases Sym2.mem_iff.mp hv with (rfl | rfl)
  · exact G.edge_vert he
  · exact G.edge_vert (G.symm he)

variable {e : Sym2 V} (G)
theorem not_isDiag_of_mem_edgeSet : e ∈ edgeSet G → ¬e.IsDiag :=
  Sym2.ind (fun _ _ => Adj.ne) e

@[deprecated (since := "2024-10-01")] alias mem_verts_if_mem_edge := mem_verts_of_mem_edge

/-- The `incidenceSet` is the set of edges incident to a given vertex. -/
def incidenceSet (G : SetGraph V) (v : V) : Set (Sym2 V) := {e ∈ G.edgeSet | v ∈ e}

theorem incidenceSet_subset (G : SetGraph V) (v : V) : G.incidenceSet v ⊆ G.edgeSet :=
  fun _ h ↦ h.1

/-- Give a vertex as an element of the SetGraph's vertex type. -/
abbrev vert (G : SetGraph V) (v : V) (h : v ∈ G.verts) : G.verts := ⟨v, h⟩

/--
Create an equal copy of a SetGraph (see `copy_eq`) with possibly different definitional equalities.
See Note [range copy pattern].
-/
def copy (G : SetGraph V) (V'' : Set V) (hV : V'' = G.verts)
    (adj' : V → V → Prop) (hadj : adj' = G.Adj) : SetGraph V where
  verts := V''
  Adj := adj'
  edge_vert := hV.symm ▸ hadj.symm ▸ G.edge_vert
  symm := hadj.symm ▸ G.symm
  loopless := hadj.symm ▸ G.loopless

theorem copy_eq (G : SetGraph V) (V'' : Set V) (hV : V'' = G.verts)
    (adj' : V → V → Prop) (hadj : adj' = G.Adj) : G.copy V'' hV adj' hadj = G :=
  SetGraph.ext hV hadj

section Order

def IsSubgraph (x y : SetGraph V) : Prop :=
  x.verts ⊆ y.verts ∧ ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

instance : LE (SetGraph V) :=
  ⟨IsSubgraph⟩

@[simp]
theorem isSubgraph_eq_le : (IsSubgraph : SetGraph V → SetGraph V → Prop) = (· ≤ ·) :=
  rfl


/-- The union of two SetGraphs. -/
instance : Max (SetGraph V) where
  max G₁ G₂ :=
    { verts := G₁.verts ∪ G₂.verts
      Adj := G₁.Adj ⊔ G₂.Adj
      edge_vert := Or.imp (fun h => G₁.edge_vert h) fun h => G₂.edge_vert h
      symm := fun _ _ => Or.imp G₁.adj_symm G₂.adj_symm
      loopless := fun _ h => by
        cases h with
        | inl h => exact G₁.loopless _ h
        | inr h => exact G₂.loopless _ h}

/-- The intersection of two SetGraphs. -/
instance : Min (SetGraph V) where
  min G₁ G₂ :=
    { verts := G₁.verts ∩ G₂.verts
      Adj := G₁.Adj ⊓ G₂.Adj
      edge_vert := And.imp (fun h => G₁.edge_vert h) fun h => G₂.edge_vert h
      symm := fun _ _ => And.imp G₁.adj_symm G₂.adj_symm
      loopless := fun _ h => G₁.loopless _ h.1}

/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices
adjacent. In `Mathlib`, this is usually referred to as `⊤`. -/
@[simp]
def completeGraph (V : Type u) : SetGraph V where
  verts := Set.univ
  Adj := Ne
  edge_vert h := by trivial
  symm := (fun _ _ h ↦ Ne.symm h)
  loopless := (fun _ a ↦ a rfl)

/-- The `bot` SetGraph is the empty graph (on V) with no vertices or edges. -/
instance : Bot (SetGraph V) where
  bot :=
    { verts := ∅
      Adj := fun _ _ ↦ False
      edge_vert := False.elim
      symm := fun _ _ => id
      loopless :=  fun _ h => h}

instance : SupSet (SetGraph V) where
  sSup s :=
    { verts := ⋃ G ∈ s, verts G
      Adj := fun a b => ∃ G ∈ s, Adj G a b
      edge_vert := by
        rintro a b ⟨G, hG, hab⟩
        exact Set.mem_iUnion₂_of_mem hG (G.edge_vert hab)
      symm := fun a b h => by simpa [adj_comm] using h
      loopless := fun _ ⟨h, h'⟩ => h.loopless _ h'.2}

instance : InfSet (SetGraph V) where
  sInf s :=
    { verts := ⋂ G ∈ s, verts G
      Adj := fun a b => (∀ ⦃G⦄, G ∈ s → Adj G a b) ∧ a ≠ b
      edge_vert := fun hab ↦ Set.mem_iInter₂_of_mem fun G hG ↦
                           G.edge_vert <| hab.1 hG
      symm := fun _ _ ↦ And.imp (forall₂_imp fun _ _ ↦ Adj.symm) Ne.symm
      loopless := fun _ h ↦ h.2 rfl}

@[simp]
theorem sup_adj : (G₁ ⊔ G₂).Adj a b ↔ G₁.Adj a b ∨ G₂.Adj a b :=
  Iff.rfl

@[simp]
theorem sup_verts (G₁ G₂ : SetGraph V) : (G₁ ⊔ G₂).verts = G₁.verts ∪ G₂.verts :=
  rfl

@[simp]
theorem inf_adj : (G₁ ⊓ G₂).Adj a b ↔ G₁.Adj a b ∧ G₂.Adj a b :=
  Iff.rfl

@[simp]
theorem inf_verts (G₁ G₂ : SetGraph V) : (G₁ ⊓ G₂).verts = G₁.verts ∩ G₂.verts :=
  rfl

@[simp]
theorem not_bot_adj : ¬ (⊥ : SetGraph V).Adj a b :=
  not_false

@[simp]
theorem bot_adj : (⊥ : SetGraph V).Adj a b ↔ False := by
  simp

@[simp]
theorem bot_verts : (⊥ : SetGraph V).verts = ∅ :=
  rfl

@[simp]
theorem sSup_adj {s : Set (SetGraph V)} : (sSup s).Adj a b ↔ ∃ G ∈ s, Adj G a b :=
  Iff.rfl


@[simp]
theorem sSup_verts (s : Set (SetGraph V)) : (sSup s).verts = ⋃ G ∈ s, verts G :=
  rfl

@[simp]
theorem sInf_adj {s : Set (SetGraph V)} : (sInf s).Adj a b ↔ (∀ G ∈ s, Adj G a b) ∧ a ≠ b :=
  Iff.rfl


@[simp]
theorem sInf_verts (s : Set (SetGraph V)) : (sInf s).verts = ⋂ G ∈ s, verts G :=
  rfl

@[simp]
theorem iSup_adj {f : ι → SetGraph V} : (⨆ i, f i).Adj a b ↔ ∃ i, (f i).Adj a b := by
  simp [iSup]

@[simp]
theorem iSup_verts {f : ι → SetGraph V} : (⨆ i, f i).verts = ⋃ i, (f i).verts := by
  ext
  simp [iSup]

@[simp]
theorem iInf_adj {f : ι → SetGraph V} : (⨅ i, f i).Adj a b ↔ (∀ i, (f i).Adj a b) ∧ a ≠ b := by
  simp [iInf]

@[simp]
theorem iInf_verts {f : ι → SetGraph V} : (⨅ i, f i).verts = ⋂ i, (f i).verts := by
  ext
  simp [iInf]

theorem sInf_adj_of_nonempty {s : Set (SetGraph V)} (hs : s.Nonempty) :
    (sInf s).Adj a b ↔ ∀ G ∈ s, Adj G a b :=
  sInf_adj.trans <|
    and_iff_left_of_imp <| by
      obtain ⟨G, hG⟩ := hs
      exact fun h h' ↦ (h _ hG).ne h'

theorem iInf_adj_of_nonempty [Nonempty ι] {f : ι → SetGraph V} :
    (⨅ i, f i).Adj a b ↔ ∀ i, (f i).Adj a b := by
  rw [iInf, sInf_adj_of_nonempty (Set.range_nonempty _)]
  simp

@[simps]
instance (V : Type u) : Inhabited (SetGraph V) :=
  ⟨⊥⟩

instance [IsEmpty V] : Unique (SetGraph V) where
  default := ⊥
  uniq G := by
    ext a b <;> exact False.elim <| IsEmpty.false a



/-- For SetGraphs `G₁`, `G₂`, `G₁ ≤ G₂` iff `G₁.verts ⊆ G₂.verts` and
`∀ a b, G₁.adj a b → G₂.adj a b`. -/
instance distribLattice : DistribLattice (SetGraph V) where
  le := (· ≤ ·)
  le_refl := fun x => ⟨subset_refl x.verts, fun _ _ h => h⟩
  le_trans :=  fun _ _ _ h h' => ⟨h.1.trans h'.1, by intro v w h''; exact h'.2 (h.2 h'')⟩
  le_antisymm := fun x y h h' => by
    apply SetGraph.ext (h.1.antisymm h'.1)
    ext a b;
    constructor <;> intro h1
    · exact h.2 h1
    · exact h'.2 h1
  sup := (· ⊔ ·)
  inf := (· ⊓ ·)
  le_sup_left := fun x y => ⟨Set.subset_union_left, fun _ _ h => Or.inl h⟩
  le_sup_right := fun x y => ⟨Set.subset_union_right, fun _ _ h => Or.inr h⟩
  sup_le := fun x y z h h' => ⟨Set.union_subset h.1 h'.1,
                                fun _ _ h'' => Or.elim h'' (by apply h.2) (by apply h'.2)⟩
  inf_le_left := fun x y => ⟨Set.inter_subset_left, fun _ _ h => h.1⟩
  inf_le_right := fun x y => ⟨Set.inter_subset_right, fun _ _ h => h.2⟩
  le_inf := fun x y z h h' => ⟨Set.subset_inter h.1 h'.1, fun _ _ h'' => ⟨h.2 h'', h'.2 h''⟩⟩
  le_sup_inf :=  by
    intro x y z
    constructor
    · intro a ha; rwa [inf_verts, sup_verts, inf_verts, Set.union_inter_distrib_left] at *
    · aesop

instance : BoundedOrder (SetGraph V) where
  top := completeGraph V
  bot := ⊥
  le_top _ := ⟨Set.subset_univ _, fun _ _ h => h.ne⟩
  bot_le _ := ⟨Set.empty_subset _, fun _ _ => False.elim⟩


@[simp]
theorem top_adj : (⊤ : SetGraph V).Adj a b ↔ a ≠ b :=
  Iff.rfl

@[simp]
theorem top_verts : (⊤ : SetGraph V).verts = Set.univ :=
  rfl

instance top_verts_nonempty [Nonempty V] : Nonempty (⊤ : SetGraph V).verts :=
  Set.univ.nonempty

@[simp]
theorem completeGraph_eq_top (V : Type*) : completeGraph V = ⊤ :=
  rfl

/-- Note that SetGraphs do not form a Boolean algebra, because of `verts`. -/
def completelyDistribLatticeMinimalAxioms : CompletelyDistribLattice.MinimalAxioms (SetGraph V) :=
  { SetGraph.distribLattice with
    le := (· ≤ ·)
    sup := (· ⊔ ·)
    inf := (· ⊓ ·)
    top := ⊤
    bot := ⊥
    le_top := fun G => ⟨Set.subset_univ _, fun v w h ↦ h.ne⟩
    bot_le := fun _ => ⟨Set.empty_subset _, fun _ _ => False.elim⟩
    sSup := sSup
    le_sSup := fun s G hG => ⟨by apply Set.subset_iUnion₂ G hG, fun _ _ hab => ⟨G, hG, hab⟩⟩
    sSup_le := fun s G hG =>
      ⟨Set.iUnion₂_subset fun _ hH => (hG _ hH).1, by
        rintro a b ⟨H, hH, hab⟩
        exact (hG _ hH).2 hab⟩
    sInf := sInf
    sInf_le := fun _ G hG => ⟨Set.iInter₂_subset G hG, fun _ _ hab => hab.1 hG⟩
    le_sInf := fun _ G hG =>
      ⟨Set.subset_iInter₂ fun _ hH => (hG _ hH).1, fun _ _ hab =>
        ⟨fun _ hH => (hG _ hH).2 hab, hab.ne⟩⟩
    iInf_iSup_eq := fun f => SetGraph.ext (by simpa using iInf_iSup_eq)
      (by ext; simp [Classical.skolem]) }

instance completelyDistribLattice : CompletelyDistribLattice (SetGraph V) :=
  .ofMinimalAxioms completelyDistribLatticeMinimalAxioms

/--
The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed.
The vertices are those of `x`. i.e. it is the graph created from `x` by removing the
edges of `y`
-/
instance sdiff : SDiff (SetGraph V) where
  sdiff x y :=
    { verts := x.verts
      Adj := x.Adj \ y.Adj
      symm := fun v w h => by change x.Adj w v ∧ ¬y.Adj w v; rwa [x.adj_comm, y.adj_comm]
      edge_vert := fun h ↦ x.edge_vert h.1
      loopless := fun v h ↦ x.loopless _ h.1}

@[simp]
theorem sdiff_adj (x y : SetGraph V) (v w : V) : (x \ y).Adj v w ↔ x.Adj v w ∧ ¬y.Adj v w :=
  Iff.rfl

@[simp]
theorem sdiff_verts (x y : SetGraph V) : (x \ y).verts = x.verts :=rfl

@[simp]
theorem sdiff_le_self (x y : SetGraph V) : x \ y ≤ x := by
  constructor
  · simp
  · intro v w h; simp [h.1]

/--
The complement of `G` is the graph with the same vertex set but edges that are not in `G`
between these vertices.
-/
instance hasCompl : HasCompl (SetGraph V) where
  compl G :=
    { verts := G.verts
      Adj := fun v w => v ≠ w ∧ ¬G.Adj v w ∧ v ∈ G.verts ∧ w ∈ G.verts
      edge_vert := fun h ↦ h.2.2.1
      symm := fun v w ⟨hne, h1, h2, h3⟩ => ⟨hne.symm, by rwa [adj_comm], h3, h2⟩
      loopless := fun _ ⟨hne, _⟩ => (hne rfl).elim }


@[simp]
theorem compl_verts (x : SetGraph V) : xᶜ.verts = x.verts := rfl

@[simp]
theorem compl_adj (G : SetGraph V) (v w : V) :
    Gᶜ.Adj v w ↔ v ≠ w ∧ ¬G.Adj v w ∧ v ∈ G.verts ∧ w ∈ G.verts := Iff.rfl

lemma inf_compl_le_sdiff (x y : SetGraph V) : x ⊓ yᶜ ≤ x \ y  := by
  constructor
  · simp
  · simp only [inf_adj, compl_adj, ne_eq, sdiff_adj, and_imp]
    intro v w h h1 h2 h3 h4 ; exact ⟨h, h2⟩

section Decidable

variable (V) (H : SetGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]

instance Bot.adjDecidable : DecidableRel (⊥ : SetGraph V).Adj :=
  inferInstanceAs <| DecidableRel fun _ _ => False

instance Sup.adjDecidable : DecidableRel (G ⊔ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∨ H.Adj v w

instance Inf.adjDecidable : DecidableRel (G ⊓ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ H.Adj v w

instance Sdiff.adjDecidable : DecidableRel (G \ H).Adj :=
  inferInstanceAs <| DecidableRel fun v w => G.Adj v w ∧ ¬H.Adj v w

instance Bot.vertsDecidable : DecidablePred (· ∈ (⊥ : SetGraph V).verts) :=
  inferInstanceAs <| DecidablePred fun _ => False

instance Top.vertsDecidable : DecidablePred (· ∈ (⊤ : SetGraph V).verts) :=
  inferInstanceAs <| DecidablePred fun _ => True

variable [DecidableEq V]

instance Top.adjDecidable : DecidableRel (⊤ : SetGraph V).Adj :=
  inferInstanceAs <| DecidableRel fun v w => v ≠ w

variable [DecidablePred (· ∈ G.verts)] [DecidablePred (· ∈ H.verts)]

instance Sup.vertsDecidable : DecidablePred (· ∈ (G ⊔ H).verts) :=
  inferInstanceAs <| DecidablePred fun v  => v ∈ G.verts ∨ v ∈ H.verts

instance Inf.vertsDecidable : DecidablePred (· ∈ (G ⊓ H).verts) :=
  inferInstanceAs <| DecidablePred fun v  => v ∈ G.verts ∧ v ∈ H.verts

instance Sdiff.vertsDecidable : DecidablePred (· ∈ (G \ H).verts) :=
  inferInstanceAs <| DecidablePred fun v  => v ∈ G.verts

instance Compl.adjDecidable : DecidableRel (Gᶜ.Adj) :=
  inferInstanceAs <| DecidableRel fun v w => v ≠ w ∧ ¬G.Adj v w ∧ v ∈ G.verts ∧ w ∈ G.verts

end Decidable

end Order

theorem adj_iff_exists_edge {v w : V} : G.Adj v w ↔ v ≠ w ∧ ∃ e ∈ G.edgeSet, v ∈ e ∧ w ∈ e := by
  refine ⟨fun _ => ⟨G.ne_of_adj ‹_›, s(v, w), by simpa⟩, ?_⟩
  rintro ⟨hne, e, he, hv⟩
  rw [Sym2.mem_and_mem_iff hne] at hv
  subst e
  rwa [mem_edgeSet] at he

theorem adj_iff_exists_edge_coe : G.Adj a b ↔ ∃ e : G.edgeSet, e.val = s(a, b) := by
  simp only [mem_edgeSet, exists_prop, SetCoe.exists, exists_eq_right]

theorem edge_other_ne {e : Sym2 V} (he : e ∈ G.edgeSet) {v : V} (h : v ∈ e) :
    Sym2.Mem.other h ≠ v := by
  rw [← Sym2.other_spec h, Sym2.eq_swap] at he
  exact G.ne_of_adj he

@[simp]
theorem edgeSet_subset_edgeSet_of_le (h : G₁ ≤ G₂) : edgeSet G₁ ⊆ edgeSet G₂  := by
  intro e he
  cases e
  rw [mem_edgeSet] at *
  exact h.2 he

@[gcongr] lemma verts_mono {H H' : SetGraph V} (h : H ≤ H') : H.verts ⊆ H'.verts := h.1

lemma verts_monotone : Monotone (verts : SetGraph V → Set V) := fun _ _ h ↦ h.1

@[simps]
instance SetGraphInhabited : Inhabited (SetGraph V) := ⟨⊥⟩

@[simp]
theorem neighborSet_sup {H H' : SetGraph V} (v : V) :
    (H ⊔ H').neighborSet v = H.neighborSet v ∪ H'.neighborSet v := rfl

@[simp]
theorem neighborSet_inf {H H' : SetGraph V} (v : V) :
    (H ⊓ H').neighborSet v = H.neighborSet v ∩ H'.neighborSet v := rfl

@[simp]
theorem neighborSet_sSup (s : Set (SetGraph V)) (v : V) :
    (sSup s).neighborSet v = ⋃ G ∈ s, neighborSet G v := by
  ext
  simp

@[simp]
theorem neighborSet_sInf (s : Set (SetGraph V)) (v : V) :
    (sInf s).neighborSet v = (⋂ G ∈ s, neighborSet G v) ∩ {v}ᶜ := by
  ext
  simp
  intro h
  exact ne_comm

@[simp]
theorem neighborSet_iSup (f : ι → SetGraph V) (v : V) :
    (⨆ i, f i).neighborSet v = ⋃ i, (f i).neighborSet v := by ext; simp [iSup]

@[simp]
theorem neighborSet_iInf (f : ι → SetGraph V) (v : V) :
    (⨅ i, f i).neighborSet v = (⋂ i, (f i).neighborSet v) ∩ {v}ᶜ := by ext; simp [iInf]

@[simp]
theorem edgeSet_top : (⊤ : SetGraph V).edgeSet = {e | ¬e.IsDiag}  := Sym2.fromRel_ne

@[simp]
theorem edgeSet_bot : (⊥ : SetGraph V).edgeSet = ∅ :=
  Set.ext <| Sym2.ind (by simp)

@[simp]
theorem edgeSet_subset_setOf_not_isDiag : G.edgeSet ⊆ {e | ¬e.IsDiag} :=
  fun _ h => (Sym2.fromRel_irreflexive (sym := G.symm)).mp G.loopless h

@[simp]
theorem edgeSet_inf {H₁ H₂ : SetGraph V} : (H₁ ⊓ H₂).edgeSet = H₁.edgeSet ∩ H₂.edgeSet :=
  Set.ext <| Sym2.ind (by simp)

@[simp]
theorem edgeSet_sup {H₁ H₂ : SetGraph V} : (H₁ ⊔ H₂).edgeSet = H₁.edgeSet ∪ H₂.edgeSet :=
  Set.ext <| Sym2.ind (by simp)

@[simp]
theorem edgeSet_sSup (s : Set (SetGraph V)) : (sSup s).edgeSet = ⋃ G ∈ s, edgeSet G := by
  ext e
  induction e
  simp

@[simp]
theorem edgeSet_sInf (s : Set (SetGraph V)) :
    (sInf s).edgeSet = (⋂ G ∈ s, edgeSet G) ∩ {e | ¬e.IsDiag} := by
  ext e
  induction e
  simp

@[simp]
theorem edgeSet_iSup (f : ι → SetGraph V) :
    (⨆ i, f i).edgeSet = ⋃ i, (f i).edgeSet := by ext; simp [iSup]

@[simp]
theorem edgeSet_iInf (f : ι → SetGraph V) :
    (⨅ i, f i).edgeSet = (⋂ i, (f i).edgeSet) ∩ {e | ¬e.IsDiag} := by
  ext
  simp [iInf]

theorem support_mono {H H' : SetGraph V} (h : H ≤ H') : H.support ⊆ H'.support :=
  Rel.dom_mono h.2

theorem edgeSet_mono {H₁ H₂ : SetGraph V} (h : H₁ ≤ H₂) : H₁.edgeSet ≤ H₂.edgeSet :=
  Sym2.ind h.2

@[simp]
theorem edgeSet_sdiff : (G₁ \ G₂).edgeSet = G₁.edgeSet \ G₂.edgeSet := by
  ext ⟨x, y⟩
  rfl

theorem _root_.Disjoint.edgeSet {H₁ H₂ : SetGraph V} (h : Disjoint H₁ H₂) :
    Disjoint H₁.edgeSet H₂.edgeSet :=
  disjoint_iff_inf_le.mpr <| by simpa using edgeSet_mono h.le_bot


instance [DecidableEq V] [Fintype V] : Fintype (SetGraph V) := by
  refine .ofBijective
    (α := {H : Finset V × (V → V → Bool) //
     (∀ a b, H.2 a b → a ∈ H.1) ∧ (∀ a b, H.2 a b = H.2 b a) ∧ ∀ a, ¬ H.2 a a})
    (fun H ↦ ⟨H.1.1, fun a b ↦ H.1.2 a b, @H.2.1, fun a b h ↦ (h ▸ H.2.2.1 a b).symm,
      fun a h ↦ (H.2.2.2 _ h)⟩) ⟨?_, fun H ↦ ?_⟩
  · rintro ⟨⟨_, _⟩, -⟩ ⟨⟨_, _⟩, -⟩
    simp [funext_iff]
  · classical
    exact ⟨⟨(H.verts.toFinset, fun a b ↦ H.Adj a b), fun a b ↦
        by simpa using H.edge_vert, by simp [H.adj_comm]⟩, by simp⟩


instance [Finite V] : Finite (SetGraph V) := by classical cases nonempty_fintype V; infer_instance

theorem neighborSet_subset_of_subgraph {x y : SetGraph V} (h : x ≤ y) (v : V) :
    x.neighborSet v ⊆ y.neighborSet v :=
  fun _ h' ↦ h.2 h'

instance neighborSet.decidablePred (G : SetGraph V) [h : DecidableRel G.Adj] (v : V) :
    DecidablePred (· ∈ G.neighborSet v) :=
  h v

instance decidableMemEdgeSet [DecidableRel G.Adj] : DecidablePred (· ∈ G.edgeSet) :=
  Sym2.fromRel.decidablePred G.symm

instance fintypeEdgeSet [Fintype (Sym2 V)] [DecidableRel G.Adj] : Fintype G.edgeSet :=
  Subtype.fintype _

instance fintypeEdgeSetBot : Fintype (⊥ : SetGraph V).edgeSet := by
  rw [edgeSet_bot]
  infer_instance


instance fintypeEdgeSetTop [DecidableEq V] [Fintype (Sym2 V)] :
    Fintype (⊤ : SetGraph V).edgeSet := by
  rw [edgeSet_top]
  infer_instance

instance fintypeEdgeSetSup [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊔ G₂).edgeSet := by
  rw [edgeSet_sup]
  infer_instance

instance fintypeEdgeSetInf [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ ⊓ G₂).edgeSet := by
  rw [edgeSet_inf]
  exact Set.fintypeInter _ _

instance fintypeEdgeSetSdiff [DecidableEq V] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet] :
    Fintype (G₁ \ G₂).edgeSet := by
  rw [edgeSet_sdiff]
  exact Set.fintypeDiff _ _

/-! ### Edge deletion -/

/-- Given a graph `G'` and a set of vertex pairs, remove all of the corresponding edges
from its edge set, if present. Vertices are unchanged. -/
def deleteEdges (G' : SetGraph V) (s : Set (Sym2 V)) : SetGraph V where
  verts := G'.verts
  Adj := G'.Adj \ Sym2.ToRel s
  edge_vert h' := G'.edge_vert h'.1
  symm a b := by simp [G'.adj_comm, Sym2.eq_swap]
  loopless a h := G'.loopless _ h.1

section DeleteEdges

variable {G' : SetGraph V} (s : Set (Sym2 V))

@[simp]
theorem deleteEdges_verts : (G'.deleteEdges s).verts = G'.verts :=
  rfl

variable {s}
@[simp]
theorem deleteEdges_adj {v w : V} : (G'.deleteEdges s).Adj v w ↔ G'.Adj v w ∧ ¬s(v, w) ∈ s :=
  Iff.rfl

instance instDecidableRel_deleteEdges_adj (G : SetGraph V) (s : Set (Sym2 V))
   [DecidableRel G.Adj] [DecidablePred (· ∈ s)] [DecidablePred (· ∈ G.verts)]
   : DecidableRel (G.deleteEdges s).Adj :=
  fun u v => by rw [deleteEdges_adj]; infer_instance

@[simp] lemma deleteEdges_edgeSet (G G' : SetGraph V) : G.deleteEdges G'.edgeSet = G \ G' := by
  ext x y <;> simp

theorem edgeSet_deleteEdges (s : Set (Sym2 V)) : (G.deleteEdges s).edgeSet = G.edgeSet \ s := by
  ext e; cases e; simp

@[simp]
theorem deleteEdges_deleteEdges (s s' : Set (Sym2 V)) :
    (G'.deleteEdges s).deleteEdges s' = G'.deleteEdges (s ∪ s') := by
  ext <;> simp [and_assoc, not_or]

@[simp]
theorem deleteEdges_empty_eq : G'.deleteEdges ∅ = G' := by
  ext <;> simp

@[simp]
theorem deleteEdges_disjoint (h : Disjoint s G'.edgeSet) : G'.deleteEdges s = G' := by
  ext x y
  · simp
  · simp only [deleteEdges_adj, and_iff_left_iff_imp]
    intro h' hf
    apply h.notMem_of_mem_left hf h'


@[simp]
theorem deleteEdges_le (s : Set (Sym2 V)) : G'.deleteEdges s ≤ G' := by
  constructor <;> simp +contextual

@[simp]
theorem deleteEdges_lt {s : Set (Sym2 V)} {u v : V} (h : G.Adj u v) (hs : s(u, v) ∈ s) :
  G.deleteEdges s < G := by
  constructor
  · simp
  · intro h'
    have := h'.2 h
    rw [deleteEdges_adj] at this
    exact this.2 hs

theorem deleteEdges_le_of_le {s s' : Set (Sym2 V)} (h : s ⊆ s') :
    G'.deleteEdges s' ≤ G'.deleteEdges s := by
  constructor <;> simp +contextual only [deleteEdges_verts, deleteEdges_adj,
    true_and, and_imp, subset_rfl]
  exact fun _ _ _ hs' hs ↦ hs' (h hs)

@[simp]
theorem deleteEdges_inter_edgeSet_left_eq :
    G'.deleteEdges (G'.edgeSet ∩ s) = G'.deleteEdges s := by
  ext <;> simp +contextual

@[simp]
theorem deleteEdges_inter_edgeSet_right_eq :
    G'.deleteEdges (s ∩ G'.edgeSet) = G'.deleteEdges s := by
  ext <;> simp +contextual

theorem sdiff_sdiff_adj_eq_self {G H : SetGraph V} (h : H ≤ G) : (G \ (G \ H)).Adj = H.Adj := by
  ext a b
  simp only [sdiff_adj, not_and, not_not]
  constructor
  · intro h'
    exact h'.2 h'.1
  · intro h'
    constructor
    · apply h.2 h'
    · intro; exact h'

theorem sdiff_sdiff_le_self {G H : SetGraph V} (h : H ≤ G) : H ≤ (G \ (G \ H)) :=
  ⟨fun _ h' ↦ h.1 h', (sdiff_sdiff_adj_eq_self h).ge⟩

theorem deleteEdges_sdiff_eq_of_le {H : SetGraph V} (h : H ≤ G) :
    (G.deleteEdges (G.edgeSet \ H.edgeSet)).edgeSet = H.edgeSet := by
  rw [← edgeSet_sdiff, deleteEdges_edgeSet,edgeSet_eq_iff, sdiff_sdiff_adj_eq_self h]

end DeleteEdges

/-! ### Induced subgraphs -/


/-- The induced subgraph of a SetGraph. The expectation is that `s ⊆ G.verts` for the usual
notion of an induced subgraph, but, in general, `s` is taken to be the new vertex set and edges
are induced from `G`. -/
@[simps]
def induce (G : SetGraph V) (s : Set V) : SetGraph V where
  verts := s
  Adj u v := u ∈ s ∧ v ∈ s ∧ G.Adj u v
  edge_vert h := h.1
  symm _ _ h := ⟨h.2.1, h.1, G.symm h.2.2⟩
  loopless _  h := G.loopless _ h.2.2

section Induce

variable {G G' : SetGraph V} {s s' : Set V}

theorem induce_mono (hg : G ≤ G') (hs : s ⊆ s') : G.induce s ≤ G'.induce s' := by
  constructor
  · simp [hs]
  · simp +contextual only [induce_adj, and_imp]
    intro v w hv hw ha
    exact ⟨hs hv, hs hw, hg.2 ha⟩

@[gcongr, mono]
theorem induce_mono_left (hg : G ≤ G') : G.induce s ≤ G'.induce s :=
  induce_mono hg subset_rfl

@[gcongr, mono]
theorem induce_mono_right (hs : s ⊆ s') : G.induce s ≤ G.induce s' :=
  induce_mono le_rfl hs

@[gcongr]
theorem induce_congr_right (hs : s = s') : G.induce s = G.induce s' := by
  rw [hs]

@[simp]
theorem induce_empty : G.induce ∅ = ⊥ := by
  ext <;> simp

@[simp]
theorem induce_self_verts : G.induce G.verts = G := by
  ext
  · simp
  · constructor <;>
      simp +contextual only [induce_adj, imp_true_iff, and_true]
    exact fun ha ↦ ⟨G.edge_vert ha, G.edge_vert ha.symm⟩

lemma le_induce_top_verts : G ≤ (⊤ : SetGraph V).induce G.verts :=
  calc G = G.induce G.verts               := induce_self_verts.symm
       _  ≤ (⊤ : SetGraph V).induce G.verts := induce_mono_left le_top

lemma le_induce_union : G.induce s ⊔ G.induce s' ≤ G.induce (s ∪ s') := by
  constructor
  · simp only [sup_verts, induce_verts, Set.Subset.rfl]
  · simp only [sup_adj, induce_adj, Set.mem_union]
    rintro v w (h | h) <;> simp [h]

lemma le_induce_union_left : G.induce s ≤ G.induce (s ∪ s') := by
  exact (sup_le_iff.mp le_induce_union).1

lemma le_induce_union_right : G.induce s' ≤ G.induce (s ∪ s') := by
  exact (sup_le_iff.mp le_induce_union).2

end Induce

/-- Given a SetGraph and a set of vertices, delete all the vertices from it,
if present. Any edges incident to the deleted vertices are deleted as well. -/
abbrev deleteVerts (G' : SetGraph V) (s : Set V) : SetGraph V :=
  G'.induce (G'.verts \ s)

section DeleteVerts

variable {G' : SetGraph V} {s : Set V}

theorem deleteVerts_verts : (G'.deleteVerts s).verts = G'.verts \ s :=
  rfl

theorem deleteVerts_adj {u v : V} :
    (G'.deleteVerts s).Adj u v ↔ u ∈ G'.verts ∧ ¬u ∈ s ∧ v ∈ G'.verts ∧ ¬v ∈ s ∧ G'.Adj u v := by
  simp [and_assoc]

@[simp]
theorem deleteVerts_deleteVerts (s s' : Set V) :
    (G'.deleteVerts s).deleteVerts s' = G'.deleteVerts (s ∪ s') := by
  ext <;> simp +contextual [not_or, and_assoc]

@[simp]
theorem deleteVerts_empty : G'.deleteVerts ∅ = G' := by
  simp [deleteVerts]

theorem deleteVerts_le : G'.deleteVerts s ≤ G' := by
  constructor <;> simp [Set.diff_subset]

@[gcongr, mono]
theorem deleteVerts_mono {G' G'' : SetGraph V} (h : G' ≤ G'') :
    G'.deleteVerts s ≤ G''.deleteVerts s :=
  induce_mono h (Set.diff_subset_diff_left h.1)

@[gcongr, mono]
theorem deleteVerts_anti {s s' : Set V} (h : s ⊆ s') : G'.deleteVerts s' ≤ G'.deleteVerts s :=
  induce_mono (le_refl _) (Set.diff_subset_diff_right h)

@[simp]
theorem deleteVerts_inter_verts_left_eq : G'.deleteVerts (G'.verts ∩ s) = G'.deleteVerts s := by
  ext <;> simp +contextual

@[simp]
theorem deleteVerts_inter_verts_set_right_eq :
    G'.deleteVerts (s ∩ G'.verts) = G'.deleteVerts s := by
  ext <;> simp +contextual

instance instDecidableRel_deleteVerts_adj (G : SetGraph V) (s : Set V)
   [DecidableRel G.Adj] [DecidablePred (· ∈ s)] [DecidablePred (· ∈ G.verts)]
   : DecidableRel (G.deleteVerts s).Adj :=
  fun u v => by rw [deleteVerts_adj]; infer_instance

end DeleteVerts


section FromEdgeSet

variable (s : Set (Sym2 V)) {v w : V}

/-- `fromEdgeSet` constructs a `SetGraph` from a set of edges, without loops. -/
def fromEdgeSet : SetGraph V where
  verts := Rel.dom (Sym2.ToRel s ⊓ Ne)
  Adj := Sym2.ToRel s ⊓ Ne
  edge_vert h := by
    rename_i v w
    use w, h.1, h.2
  symm _ _ h := ⟨Sym2.toRel_symmetric s h.1, h.2.symm⟩
  loopless _ h' := h'.2.elim rfl

@[simp]
theorem fromEdgeSet_adj : (fromEdgeSet s).Adj v w ↔ s(v, w) ∈ s ∧ v ≠ w :=
  Iff.rfl

@[simp]
theorem fromEdgeSet_verts : v ∈ (fromEdgeSet s).verts ↔ ∃ w, s(v, w) ∈ s ∧ v ≠ w := by
  rw [fromEdgeSet]
  simp only [ne_eq]
  constructor
  · intro ⟨w,hw⟩
    use w, hw.1, hw.2
  · intro ⟨w, h1, h2⟩
    use w, h1, h2

-- Note: we need to make sure `fromEdgeSet_adj` and this lemma are confluent.
-- In particular, both yield `s(u, v) ∈ (fromEdgeSet s).edgeSet` ==> `s(v, w) ∈ s ∧ v ≠ w`.
@[simp]
theorem edgeSet_fromEdgeSet : (fromEdgeSet s).edgeSet = s \ { e | e.IsDiag } := by
  ext e
  exact Sym2.ind (by simp) e

@[simp]
theorem fromEdgeSet_edgeSet : fromEdgeSet G.edgeSet ≤ G := by
  constructor
  · intro v hv
    rw [fromEdgeSet] at hv
    obtain ⟨w, hw⟩ := hv
    apply G.edge_vert hw.1
  · intro v w h
    simpa using h.1

@[simp]
theorem fromEdgeSet_empty : fromEdgeSet (∅ : Set (Sym2 V)) = ⊥ := by
  ext <;> simp

@[simp] -- Need two vertices in V for this to hold
theorem fromEdgeSet_univ [Nontrivial V]: fromEdgeSet (Set.univ : Set (Sym2 V)) = ⊤ := by
  ext v w
  · simp only [top_verts, Set.mem_univ, iff_true]
    obtain ⟨x, y, hy⟩ := exists_pair_ne V
    by_cases h : x = v
    · use y; exact ⟨by trivial, h ▸ hy⟩
    · use x; exact ⟨by trivial, Ne.symm h⟩
  · simp

@[simp]
theorem fromEdgeSet_inter (s t : Set (Sym2 V)) :
    fromEdgeSet (s ∩ t) ≤ fromEdgeSet s ⊓ fromEdgeSet t := by
  constructor
  · intro v hv
    simp
    obtain ⟨w, hw⟩ := hv
    exact ⟨⟨_, hw.1.1, hw.2⟩,⟨_, hw.1.2, hw.2⟩⟩
  · simp only [fromEdgeSet_adj, Set.mem_inter_iff, Ne, inf_adj]
    tauto

@[simp]
theorem fromEdgeSet_union (s t : Set (Sym2 V)) :
    fromEdgeSet (s ∪ t) = fromEdgeSet s ⊔ fromEdgeSet t := by
  ext v w
  · simp only [fromEdgeSet_verts, Set.mem_union, ne_eq, sup_verts]
    aesop
  · simp [Set.mem_union, or_and_right]

@[simp]
theorem fromEdgeSet_sdiff (s t : Set (Sym2 V)) :
    fromEdgeSet (s \ t) ≤ fromEdgeSet s \ fromEdgeSet t   := by
  constructor
  · intro v ⟨w, hw⟩
    use w, hw.1.1, hw.2
  · simp only [fromEdgeSet_adj, Set.mem_diff, ne_eq, sdiff_adj, not_and, not_not, and_imp]
    intro v w hs ht hne
    use ⟨hs, hne⟩
    intro hf; contradiction

@[gcongr, mono]
theorem fromEdgeSet_mono {s t : Set (Sym2 V)} (h : s ⊆ t) : fromEdgeSet s ≤ fromEdgeSet t := by
  constructor
  · intro v
    simp only [fromEdgeSet_verts, ne_eq, forall_exists_index, and_imp]
    intro w  hw h'
    use w, h hw, h'
  · simp only [fromEdgeSet_adj, ne_eq, and_imp]
    intro v w h' hf
    exact ⟨(h h'), hf⟩


theorem deleteEdges_eq_sdiff_fromEdgeSet (s : Set (Sym2 V)) :
  (G.deleteEdges s) = G \ (fromEdgeSet s) := by
  ext v w
  · simp
  · aesop

/-- The one-vertex SetGraph given by a singleton. -/
@[simps]
def ofSingleton (v : V) : SetGraph V where
  verts := {v}
  Adj a b := ⊥
  edge_vert {a b} h := by aesop
  symm := fun _ ↦ by aesop
  loopless := fun _ _ ↦ by simp_all

/-- The one-edge SetGraph given by a pair of non-equal vertices. -/
@[simps]
def ofNe {v w : V} (hne : v ≠ w) : SetGraph V where
  verts := {v, w}
  Adj a b := s(v, w) = s(a, b)
  edge_vert {a b} h := by
    apply_fun fun e ↦ a ∈ e at h
    simp only [Sym2.mem_iff, true_or, eq_iff_iff, iff_true] at h
    exact h
  symm := fun _ ↦ by aesop
  loopless := fun _ _ ↦ by simp_all

/-
TODO: lemmas about SetGraph.ofSingleton and SetGraph.ofNe
-/

@[simp] lemma disjoint_fromEdgeSet (h : Disjoint G (fromEdgeSet s)) : Disjoint G.edgeSet s := by
  rw [Set.disjoint_left]
  intro e he hf
  let H := fromEdgeSet {e}
  have h1 : H ≤ G := (fromEdgeSet_edgeSet G).trans' <| fromEdgeSet_mono (by aesop)
  have h2 : H ≤ fromEdgeSet s := by apply fromEdgeSet_mono (by aesop)
  have := h h1 h2
  rw [le_bot_iff, SetGraph.ext_iff] at this
  cases e
  rename_i x y
  have := this.2
  have : (⊥ : SetGraph V).Adj x y := by
    rw [← this]
    aesop
  exact this

-- @[simp] lemma fromEdgeSet_disjoint : Disjoint (fromEdgeSet s) G ↔ Disjoint s G.edgeSet := by
--   sorry

instance [DecidableEq V] [Fintype s] : Fintype (fromEdgeSet s).edgeSet := by
  rw [edgeSet_fromEdgeSet s]
  infer_instance

end FromEdgeSet
variable {c : V}

theorem mk'_mem_incidenceSet_iff : s(b, c) ∈ G.incidenceSet a ↔ G.Adj b c ∧ (a = b ∨ a = c) :=
  and_congr_right' Sym2.mem_iff

theorem mk'_mem_incidenceSet_left_iff : s(a, b) ∈ G.incidenceSet a ↔ G.Adj a b :=
  and_iff_left <| Sym2.mem_mk_left _ _

theorem mk'_mem_incidenceSet_right_iff : s(a, b) ∈ G.incidenceSet b ↔ G.Adj a b :=
  and_iff_left <| Sym2.mem_mk_right _ _

theorem edge_mem_incidenceSet_iff {e : G.edgeSet} : ↑e ∈ G.incidenceSet a ↔ a ∈ (e : Sym2 V) :=
  and_iff_right e.2

theorem incidenceSet_inter_incidenceSet_subset (h : a ≠ b) :
    G.incidenceSet a ∩ G.incidenceSet b ⊆ {s(a, b)} := fun _e he =>
  (Sym2.mem_and_mem_iff h).1 ⟨he.1.2, he.2.2⟩

theorem incidenceSet_inter_incidenceSet_of_adj (h : G.Adj a b) :
    G.incidenceSet a ∩ G.incidenceSet b = {s(a, b)} := by
  refine (G.incidenceSet_inter_incidenceSet_subset <| h.ne).antisymm ?_
  rintro _ (rfl : _ = s(a, b))
  exact ⟨G.mk'_mem_incidenceSet_left_iff.2 h, G.mk'_mem_incidenceSet_right_iff.2 h⟩

theorem adj_of_mem_incidenceSet (h : a ≠ b) (ha : e ∈ G.incidenceSet a)
    (hb : e ∈ G.incidenceSet b) : G.Adj a b := by
  rwa [← mk'_mem_incidenceSet_left_iff, ←
    Set.mem_singleton_iff.1 <| G.incidenceSet_inter_incidenceSet_subset h ⟨ha, hb⟩]

theorem incidenceSet_inter_incidenceSet_of_not_adj (h : ¬G.Adj a b) (hn : a ≠ b) :
    G.incidenceSet a ∩ G.incidenceSet b = ∅ := by
  simp_rw [Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_and]
  intro u ha hb
  exact h (G.adj_of_mem_incidenceSet hn ha hb)

lemma notMem_neighborSet_self : a ∉ G.neighborSet a := by simp


@[simp]
theorem mem_incidenceSet (v w : V) : s(v, w) ∈ G.incidenceSet v ↔ G.Adj v w := by
  simp [incidenceSet]

theorem mem_incidence_iff_neighbor {v w : V} :
    s(v, w) ∈ G.incidenceSet v ↔ w ∈ G.neighborSet v := by
  simp only [mem_incidenceSet, mem_neighborSet]

theorem adj_incidenceSet_inter {v : V} {e : Sym2 V} (he : e ∈ G.edgeSet) (h : v ∈ e) :
    G.incidenceSet v ∩ G.incidenceSet (Sym2.Mem.other h) = {e} := by
  ext e'
  simp only [incidenceSet, Set.mem_sep_iff, Set.mem_inter_iff, Set.mem_singleton_iff]
  refine ⟨fun h' => ?_, ?_⟩
  · rw [← Sym2.other_spec h]
    exact (Sym2.mem_and_mem_iff (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩
  · rintro rfl
    exact ⟨⟨he, h⟩, he, Sym2.other_mem _⟩



/-- The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`. -/
def commonNeighbors (v w : V) : Set V :=
  G.neighborSet v ∩ G.neighborSet w

theorem commonNeighbors_eq (v w : V) : G.commonNeighbors v w = G.neighborSet v ∩ G.neighborSet w :=
  rfl

theorem mem_commonNeighbors {u v w : V} : u ∈ G.commonNeighbors v w ↔ G.Adj v u ∧ G.Adj w u :=
  Iff.rfl

theorem commonNeighbors_symm (v w : V) : G.commonNeighbors v w = G.commonNeighbors w v :=
  Set.inter_comm _ _

theorem notMem_commonNeighbors_left (v w : V) : v ∉ G.commonNeighbors v w := fun h =>
  ne_of_adj G h.1 rfl

theorem notMem_commonNeighbors_right (v w : V) : w ∉ G.commonNeighbors v w := fun h =>
  ne_of_adj G h.2 rfl

theorem commonNeighbors_subset_neighborSet_left (v w : V) :
    G.commonNeighbors v w ⊆ G.neighborSet v :=
  Set.inter_subset_left

theorem commonNeighbors_subset_neighborSet_right (v w : V) :
    G.commonNeighbors v w ⊆ G.neighborSet w :=
  Set.inter_subset_right

instance decidableMemCommonNeighbors [DecidableRel G.Adj] (v w : V) :
    DecidablePred (· ∈ G.commonNeighbors v w) :=
  inferInstanceAs <| DecidablePred fun u => u ∈ G.neighborSet v ∧ u ∈ G.neighborSet w

theorem commonNeighbors_top_eq {v w : V} :
    (⊤ : SetGraph V).commonNeighbors v w = Set.univ \ {v, w} := by
  ext u
  simp [commonNeighbors, eq_comm, not_or]

section Incidence

variable [DecidableEq V]

/-- Given an edge incident to a particular vertex, get the other vertex on the edge. -/
def otherVertexOfIncident {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) : V :=
  Sym2.Mem.other' h.2

theorem edge_other_incident_set {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) :
    e ∈ G.incidenceSet (G.otherVertexOfIncident h) := by
  use h.1
  simp [otherVertexOfIncident, Sym2.other_mem']

theorem incidence_other_prop {v : V} {e : Sym2 V} (h : e ∈ G.incidenceSet v) :
    G.otherVertexOfIncident h ∈ G.neighborSet v := by
  obtain ⟨he, hv⟩ := h
  rwa [← Sym2.other_spec' hv, mem_edgeSet] at he

-- Porting note: as a simp lemma this does not apply even to itself
theorem incidence_other_neighbor_edge {v w : V} (h : w ∈ G.neighborSet v) :
    G.otherVertexOfIncident (G.mem_incidence_iff_neighbor.mpr h) = w :=
  Sym2.congr_right.mp (Sym2.other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)

/-- There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex. -/
@[simps]
def incidenceSetEquivNeighborSet (v : V) : G.incidenceSet v ≃ G.neighborSet v where
  toFun e := ⟨G.otherVertexOfIncident e.2, G.incidence_other_prop e.2⟩
  invFun w := ⟨s(v, w.1), G.mem_incidence_iff_neighbor.mpr w.2⟩
  left_inv x := by simp [otherVertexOfIncident]
  right_inv := fun ⟨w, hw⟩ => by
    simp only [Subtype.mk.injEq]
    exact incidence_other_neighbor_edge _ hw

end Incidence

variable {s : Set V}
theorem edgeSet_induce :
    (G.induce s).edgeSet = G.edgeSet ∩ {e | ∃ u v, e = s(u,v) ∧ u ∈ s ∧ v ∈ s} := by
  ext e; cases e
  aesop

theorem edgeSet_induce_of_support_subset (h : G.support ⊆ s) :
  (G.induce s).edgeSet = G.edgeSet := by
  rw [edgeSet_induce]
  ext e;
  cases e with
  | h x y =>
    simp only [Set.mem_inter_iff, mem_edgeSet, Set.mem_setOf_eq, Sym2.eq, Sym2.rel_iff',
      Prod.mk.injEq, Prod.swap_prod_mk, and_iff_left_iff_imp]
    intro h'
    use x, y
    simpa using ⟨h <| G.mem_support.2 ⟨_, h'⟩,h <| G.mem_support.2 ⟨_, h'.symm⟩⟩

variable {s : Set V} {v : V}
@[simp]
theorem neighborSet_induce_of_mem (h : v ∈ s) :
    (G.induce s).neighborSet v = s ∩ G.neighborSet v := by
  ext
  simp [h]

theorem neighborSet_induce_of_neighborSet_subset {v : V} (h : v ∈ s) (h2 : G.neighborSet v ⊆ s) :
    ((G.induce s).neighborSet v) = G.neighborSet v := by
  ext x; simp only [mem_neighborSet, induce_adj]
  constructor <;> intro h'
  · exact h'.2.2
  · exact ⟨h, h2 h', h'⟩

@[simp]
theorem neighborSet_induce_of_notMem (h : v ∉ s) :
    (G.induce s).neighborSet v = ∅ := by
  ext
  simp [h]


/-- Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Any bipartite graph may be regarded as a subgraph of one of these. -/
@[simps]
def completeBipartiteGraph (V W : Type*) : SetGraph (V ⊕ W) where
  verts := Set.univ
  Adj v w := v.isLeft ∧ w.isRight ∨ v.isRight ∧ w.isLeft
  symm v w := by cases v <;> cases w <;> simp
  loopless v := by cases v <;> simp
  edge_vert h := by trivial

end SetGraph
