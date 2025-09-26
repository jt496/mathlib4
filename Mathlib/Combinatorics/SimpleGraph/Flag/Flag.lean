/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fintype.Perm
import Mathlib.Combinatorics.SimpleGraph.Flag.Counting
set_option linter.style.header false

/-!
## TODO: --test
  1. Prove that:

    ‖{(e₁, e₂) : (F₁ ↪f F) × (F₁ ↪f F) // ¬ e₁.Compat e₂}‖ ≤
      (‖β‖!)² * #{ (A, B) | A,B ‖β‖-sets in α, with F.θ.image ⊆ A ∩ B ≠ F.θ.image}

    (e₁, e₂) ↦ {(A, B) : A,B ‖β‖-sets in α, with F.θ.image ⊆ A ∩ B ≠ F.θ.image}

      Give C := F.θ.image (so `#C = ‖ι‖` )
      #{(A, B) | #A = #B = ‖β‖ ∧ A ∩ B = C} =
                      ((‖α‖ - ‖ι‖).choose (‖β‖ - ‖ι‖)) * ((‖α‖ - ‖β‖).choose (‖β‖ - ‖ι‖))

  2. Prove that averaging over injections from ι can be done over subgraphs of fixed size.

-/

local notation "‖" x "‖" => Fintype.card x



namespace SimpleGraph

/-- A graph property -/
abbrev GraphProp := {α : Type} → SimpleGraph α → Prop

namespace GraphProp

/-- A graph property `IsInvariant` if it agrees on isomorphic graphs -/
def IsInvariant (P : GraphProp) : Prop := ∀ {α β : Type},
  ∀ {G : SimpleGraph α}, ∀ {H : SimpleGraph β}, Nonempty (G ≃g H) → (P G ↔ P H)

/-- A graph property `IsMonotone` it is closed under taking subgraphs -/
def IsMonotone (P : GraphProp) : Prop :=
  ∀ {α : Type}, ∀ (G : SimpleGraph α), ∀ (H : G.Subgraph), P G → P H.coe

/-- A graph property `IsHereditary` if it is closed under taking induced subgraphs -/
def IsHereditary (P : GraphProp) : Prop := ∀ {α : Type}, ∀ (G : SimpleGraph α),
  ∀ (t : Set α), P G → P (G.induce t)

lemma isMonotone_isHereditary {P : GraphProp} (h : P.IsMonotone) : P.IsHereditary := by
  intro V G t hG
  rw [SimpleGraph.induce_eq_coe_induce_top ]
  apply h _ _ hG

variable {α : Type} {β : Type*}

lemma free_isMonotone (A : SimpleGraph β) : IsMonotone (A.Free ·) :=
  fun _ H hA hf ↦ hA <| hf.trans H.coe_isContained

lemma free_isHereditary (A : SimpleGraph β) : IsHereditary (A.Free ·) :=
   isMonotone_isHereditary <| free_isMonotone A

lemma free_isInvariant (A : SimpleGraph β) : IsInvariant (A.Free ·) :=
  fun ⟨e⟩ ↦ SimpleGraph.free_congr_right e

open Finset Fintype

open Classical in
/--
`exᵢ n H p` is the the maximum number of embeddings of `H` in an `p`-graph on `n`
vertices, e.g. if `H = K₂` this is twice the maximum number of edges in an `p`-graph on `n`
vertices.
-/
noncomputable def extremalPropInduced (n : ℕ) {γ : Type*} (H : SimpleGraph γ) [Fintype γ]
    (p : GraphProp) : ℕ := sup {G : SimpleGraph (Fin n) | p G} (fun G ↦ ‖H ↪g G‖)

local notation "exPᵢ" => extremalPropInduced

variable {n : ℕ} [Fintype α] {γ : Type*} [Fintype γ] {G : SimpleGraph α} {H : SimpleGraph γ}
{p : GraphProp}

open Classical in
theorem extremalPropInduced_of_fintypeCard_eq (hc : card α = n) (hp : p.IsInvariant) :
    exPᵢ n H p = sup {G : SimpleGraph α | p G} (fun G ↦ ‖H ↪g G‖) := by
  let e := Fintype.equivFinOfCardEq hc
  rw [extremalPropInduced, le_antisymm_iff]
  and_intros
  on_goal 1 =>
    replace e := e.symm
  all_goals
  rw [Finset.sup_le_iff]
  intro G h
  let G' := G.map e.toEmbedding
  replace h' : G' ∈ univ.filter (p ·) := by
    rw [mem_filter, ← hp ⟨(SimpleGraph.Iso.map e G)⟩]
    simpa using h
  convert @le_sup _ _ _ _ { G | p G } (fun G ↦ ‖H ↪g G‖) G' h' using 1
  exact Fintype.card_congr (Iso.embeddings_equiv_of_iso (.map e G) (by rfl))

/--
If `p G` holds, then `G` has at most `exPᵢ (card α) H p` induced copies of `H`.
-/
theorem card_embeddings_le_extremalPropInduced (hp : p.IsInvariant) (h : p G) :
    ‖H ↪g G‖ ≤ exPᵢ (card α) H p := by
  rw [extremalPropInduced_of_fintypeCard_eq rfl hp]
  classical
  exact @le_sup _ _ _ _ { G | p G } (fun G ↦ ‖H ↪g G‖) G (by simpa using h)


/-- If `G` has more than `exᵢ (card V) H p` copies of `H`, then `p G` is false. -/
theorem extremalPropInduced_lt_card_embeddings (hp : p.IsInvariant)
    (h : exPᵢ (card α) H p < ‖H ↪g G‖) : ¬ p G := by
  contrapose! h
  exact card_embeddings_le_extremalPropInduced hp h

/-- `exPᵢ (card V) H p` is at most `m` if and only if every simple graph `G` satisfying `p G` has
at most `m` embeddings of `H`. -/
theorem extremalPropInduced_le_iff (hp : p.IsInvariant) (m : ℕ) :
    exPᵢ (card α) H p ≤ m ↔ ∀ ⦃G : SimpleGraph α⦄ [DecidableRel G.Adj], p G →  ‖H ↪g G‖ ≤ m := by
  simp_rw [extremalPropInduced_of_fintypeCard_eq rfl hp, Finset.sup_le_iff, mem_filter, mem_univ,
    true_and]
  classical
  exact ⟨fun h _ _ h' ↦ by convert h _ h', fun h _ h' ↦ h h'⟩

/-- `exᵢ (card V) H p` is greater than `m` if and only if there exists a graph `G` satisfying `p G`
with more than `m` embeddings of `H`. -/
theorem lt_extremalPropInduced_iff (hp : p.IsInvariant) (m : ℕ) : m < exPᵢ (card α) H p ↔
      ∃ G : SimpleGraph α, ∃ _ : DecidableRel G.Adj, p G ∧ m < ‖H ↪g G‖ := by
  simp_rw [extremalPropInduced_of_fintypeCard_eq rfl hp, Finset.lt_sup_iff, mem_filter, mem_univ,
    true_and]
  exact ⟨fun ⟨_, h, h'⟩ ↦ ⟨_, Classical.decRel _, h, h'⟩, fun ⟨_, _, h, h'⟩ ↦ ⟨_, h, by convert h'⟩⟩

variable {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]

theorem extremalPropInduced_le_iff_of_nonneg (hp : p.IsInvariant) {m : R} (h : 0 ≤ m) :
    exPᵢ (card α) H p ≤ m ↔ ∀ ⦃G : SimpleGraph α⦄ [DecidableRel G.Adj], p G → ‖H ↪g G‖ ≤ m := by
  simp_rw [← Nat.le_floor_iff h]
  exact extremalPropInduced_le_iff hp ⌊m⌋₊

theorem lt_extremalPropInduced_iff_of_nonneg (hp : p.IsInvariant) {m : R} (h : 0 ≤ m) :
    m < exPᵢ (card α) H p ↔ ∃ G : SimpleGraph α, ∃ _ : DecidableRel G.Adj, p G ∧ m < ‖H ↪g G‖ := by
  simp_rw [← Nat.floor_lt h]
  exact lt_extremalPropInduced_iff hp ⌊m⌋₊

variable [DecidableRel G.Adj]
/-- `H`-free extremal graphs are `H`-free simple graphs having `exᵢ (card V) H` many
edges. -/
theorem isExtremalPropH_iff (hp : p.IsInvariant) [DecidableRel H.Adj] :
    G.IsExtremalH H p ↔ p G ∧ ‖H ↪g G‖ = exPᵢ (card α) H p := by
  rw [IsExtremalH, and_congr_right_iff, ← extremalPropInduced_le_iff hp]
  exact fun h ↦ ⟨eq_of_le_of_ge (card_embeddings_le_extremalPropInduced hp h), ge_of_eq⟩

lemma card_embeddings_of_isExtremalH (hp : p.IsInvariant) [DecidableRel H.Adj]
    (h : G.IsExtremalH H p) : ‖H ↪g G‖ = exPᵢ (card α) H p := ((isExtremalPropH_iff hp).mp h).2

/--
The maximum proportion of embeddings of `H` into an `n`-vertex `p`-graph, is a monotone
decreasing sequence (if `p` is a hereditary graph property invariant under graph isomorphisms)
-/
lemma antitoneOn_extremalInduced_div_choose (hi : p.IsInvariant) (hh : p.IsHereditary) :
    AntitoneOn (fun n ↦ (exPᵢ n H p / n.descFactorial ‖γ‖ : ℚ)) {x | ‖γ‖ ≤ x} := by
  apply antitoneOn_div_descFactorial _ ‖γ‖
  intro n
  by_cases hn : n < ‖γ‖
  · have : n + 1 - ‖γ‖ = 0 := by cutsat
    simp [this]
  push_neg at hn
  have hp : 0 < (n : ℚ) + 1 - ‖γ‖ := by
    rw [← Nat.cast_add_one, ← Nat.cast_sub (by cutsat)]
    norm_cast; cutsat
  have : exPᵢ (n + 1) H p ≤ ((((n + 1) * exPᵢ n H p) : ℚ)/(n + 1 - ‖γ‖)) := by
    rw [← Fintype.card_fin (n + 1)]
    apply (extremalPropInduced_le_iff_of_nonneg hi (α := (Fin (n + 1))) ?_).2
    · intro G hG hF
      rw [le_div_iff₀ hp]
      rw [← Nat.cast_add_one, ← Nat.cast_sub (by cutsat)]
      norm_cast
      calc
      _ = ∑ t : Finset (Fin (n + 1)) with t.card = n , ‖H ↪g (G.induce t)‖ :=
          (sum_card_embeddings_induce_n G H).symm
      _ ≤ _ := by
        rw [mul_comm]
        apply (sum_le_card_nsmul {t : Finset (Fin (n + 1)) | t.card = n} _ (exPᵢ n H p) ?_).trans
        · simp [mul_comm]
        intro t ht
        simp only [univ_filter_card_eq, mem_powersetCard, subset_univ, true_and] at ht
        have : Fintype.card (t.toSet : Type) = n := by simp [ht]
        simp_rw [← this]
        apply card_embeddings_le_extremalPropInduced hi <| hh _ _ hF
    · apply div_nonneg (by norm_cast; cutsat) hp.le
  rw [← Nat.cast_add_one, ← Nat.cast_sub (by cutsat),
    le_div_iff₀ (mod_cast (by cutsat)), mul_comm] at this
  norm_cast at this

end GraphProp
end SimpleGraph

namespace SimpleGraph
variable {α β δ ι : Type*} {k : ℕ} (e : δ ≃ ι) (f : α ≃ β)



#check e.embeddingCongr f -- (δ ↪ α) ≃ (ι ↪ β) :=
/--
A `Flag α ι` consists of `G : SimpleGraph α` and a labelling of `ι` vertices of `G` by an
injective map `θ : ι ↪ α`. (We call this a `σ`-flag if the labelled subgraph is
`σ : SimpleGraph ι`).
-/
structure Flag (α ι : Type*) where
  G : SimpleGraph α
  θ : ι ↪ α

/--
We say `F ⊆ₗt` (and write `F ⊆ₗ t`) if all the labelled vertices of the flag `F` lie in the
set `t`.
-/
abbrev Flag.labels_in {α ι : Type*} (F : Flag α ι) (t : Set α) : Prop := ∀ i, F.θ i ∈ t

@[inherit_doc] infixl:50 " ⊆ₗ " => Flag.labels_in
/--
Given a flag `F = (G, θ)` and set `t ⊆ V(G)` containing `im(θ)` `F.induce t`
is the flag induced by `t` with the same labels_eq. i,e, `⟨G[t], θ∣ₜ⟩`
-/
def Flag.induce {α ι : Type*} (F : Flag α ι) (t : Set α) (ht : F ⊆ₗ t) : Flag t ι :=
  ⟨F.G.induce t, ⟨fun i ↦ ⟨F.θ i, ht i⟩, fun h ↦ by simp_all⟩⟩

def Flag.induce_copy {α ι : Type*} (F : Flag α ι) {s t : Set α} (h : s = t) (hs : F ⊆ₗ s) :
    Flag t ι := F.induce t (h ▸ hs)

lemma Flag.induce_copy_eq {α ι : Type*} (F : Flag α ι) {s t : Set α} (h : s = t)
    (hs : F ⊆ₗ s) (ht : F ⊆ₗ t) : F.induce t ht = F.induce_copy h hs := by
  subst_vars; rfl

lemma Flag.induce_adj {α ι : Type*} (F : Flag α ι) (t : Set α) (ht : F ⊆ₗ t) :
    (F.induce t ht).G = (F.G.induce t) := rfl

lemma Flag.induce_labels_eq {α ι : Type*} {F : Flag α ι} (t : Set α) (ht : F ⊆ₗ t) {i : ι} :
    (F.induce t ht).θ i = F.θ i := rfl

/-- Added to prove `Fintype` instance later -/
def Flag_equiv_prod (α ι : Type*) : Flag α ι ≃ (SimpleGraph α) × (ι ↪ α) where
  toFun := fun F ↦ (F.G, F.θ)
  invFun := fun p ↦ { G := p.1, θ := p.2 }
  left_inv := fun F ↦ by cases F; rfl
  right_inv := fun p ↦ by cases p; rfl

lemma Flag.card_le_card {α ι : Type*} (F : Flag α ι) [Fintype α] [Fintype ι] : ‖ι‖ ≤ ‖α‖ :=
  Fintype.card_le_of_embedding F.θ


/-- An embedding of flags is an embedding of the underlying graphs that preserves labels. -/
@[ext]
structure FlagEmbedding {α β ι : Type*} (F₁ : Flag α ι) (F₂ : Flag β ι) extends F₁.G ↪g F₂.G where
 labels_eq : F₂.θ = toEmbedding ∘ F₁.θ




/-- An isomorphism of flags is an isomorphism of the underlying graphs that preserves labels. -/
@[ext]
structure FlagIso {α β ι : Type*} (F₁ : Flag α ι) (F₂ : Flag β ι) extends F₁.G ≃g F₂.G where
 labels_eq : F₂.θ = toEquiv ∘ F₁.θ

@[inherit_doc] infixl:50 " ↪f " => FlagEmbedding
@[inherit_doc] infixl:50 " ≃f " => FlagIso

variable {γ : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι} {F₃ : Flag γ ι}

instance : FunLike (F₁ ↪f F₂) α β where
  coe x := x.toFun
  coe_injective' f g h := by
    ext a; simp
    exact congrFun h a

/-- An isomorphism of flags gives rise to an embedding of flags. -/
abbrev FlagIso.toEmbedding (f : F₁ ≃f F₂) : F₁ ↪f F₂ :=
  ⟨f.toRelEmbedding, by ext x ; simp [f.labels_eq]⟩

/-- The identity isomorphism of a flag with itself. -/
abbrev FlagIso.refl : F₁ ≃f F₁ :=
  ⟨RelIso.refl _, rfl⟩

/-- The inverse of a flag isomorphism. -/
abbrev FlagIso.symm (f : F₁ ≃f F₂) : F₂ ≃f F₁ :=
  ⟨RelIso.symm f.toRelIso, by ext; simp [f.labels_eq]⟩

/-- Composition of flag isomorphisms. -/
abbrev FlagIso.trans (f₁₂ : F₁ ≃f F₂) (f₂₃ : F₂ ≃f F₃) : F₁ ≃f F₃ :=
  ⟨f₁₂.toRelIso.trans f₂₃.toRelIso, by ext; simp [f₁₂.labels_eq, f₂₃.labels_eq]⟩

/-- Composition of flag embeddings. -/
abbrev FlagEmbedding.trans (f₁₂ : F₁ ↪f F₂) (f₂₃ : F₂ ↪f F₃) : F₁ ↪f F₃ :=
  ⟨f₁₂.toRelEmbedding.trans f₂₃.toRelEmbedding, by ext i; simp [f₂₃.labels_eq, f₁₂.labels_eq]⟩

@[simp]
lemma FlagEmbedding.labels_subset_range {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι}
    (e : F₁ ↪f F₂) : Set.range F₂.θ ⊆ Set.range e.toFun := by
  intro i hi
  rw [e.labels_eq] at hi
  aesop

theorem FlagEmbedding.toRelEmbedding_injective {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι} :
    Function.Injective (FlagEmbedding.toRelEmbedding : F₁ ↪f F₂ → (F₁.G ↪g F₂.G)) := by
  rintro ⟨f, _⟩ ⟨g, _⟩; simp

variable [Fintype α] [Fintype β] (G : SimpleGraph α) (H : SimpleGraph β)

noncomputable instance FlagEmbedding.instfintypeOfEmbeddings {α β ι : Type*} {F₁ : Flag α ι}
    {F₂ : Flag β ι} [Fintype α] [Fintype β] : Fintype (F₁ ↪f F₂) := by
  exact Fintype.ofInjective _ FlagEmbedding.toRelEmbedding_injective

variable {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι} {e : F₁ ↪f F₂}

lemma FlagIso.symm_eq {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι} (e : F₁ ≃f F₂)
     : F₁.θ = e.symm.toFun ∘ F₂.θ := by
  ext x; simp [e.labels_eq];


/--
Pairs of isomorphic flags have equivalent embedding
-/
def FlagIso.flagEmbeddingCongr {α α' β β' ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι}
    {F₁' : Flag α' ι} {F₂' : Flag β' ι} (e₁ : F₁ ≃f F₁') (e₂ : F₂ ≃f F₂') :
    (F₁ ↪f F₂) ≃ (F₁' ↪f F₂') where
  toFun := fun f ↦ (e₁.symm.toEmbedding.trans f).trans e₂.toEmbedding
  invFun := fun f ↦ (e₁.toEmbedding.trans f).trans e₂.symm.toEmbedding
  left_inv := fun _ ↦ by ext; simp
  right_inv := fun _ ↦ by ext; simp

/--
Given a pair of isomorphic flags `F` and `F'` and a pair of isomorphic graphs `H` and `H'`
and an injective map `θ : ι ↪ β`, the embeddings of `F` in `H` are equivalent to the embeddings
of `F'` in `(H', e ∘ θ)`.
-/
def Iso.flagEmbeddingCongr {α α' β β' ι : Type*} {F : Flag α ι} {F' : Flag α' ι}
    {H : SimpleGraph β} {H' : SimpleGraph β'} {θ : ι ↪ β} (e : H ≃g H') (f : F ≃f F') :
    (F ↪f ⟨H, θ⟩) ≃ (F' ↪f ⟨H', θ.trans (e : β ↪ β')⟩) :=
  f.flagEmbeddingCongr (⟨e, by ext; simp⟩)

open Finset
/-- If `H ≃g H'` as graphs and `F ≃f F'` as flags, then
`∑ θ : ι ↪ β, ‖F ↪f ⟨H, θ⟩‖ = ∑ θ' : ι ↪ β', ‖F' ↪f ⟨H', θ'⟩‖`
where the sum is over all injective maps from `ι` to `β` and `β'` respectively.
-/
lemma Iso.sum_card_flagEmbedding {α α' β β' ι : Type*} [Fintype β] [Fintype β'] [Fintype ι]
    [Fintype α] [Fintype α'] {F : Flag α ι} {F' : Flag α' ι} {H : SimpleGraph β}
    {H' : SimpleGraph β'} (e : H ≃g H') (f : F ≃f F') :
    ∑ (θ : ι ↪ β), ‖F ↪f ⟨H, θ⟩‖ = ∑ (θ' : ι ↪ β'), ‖F' ↪f ⟨H', θ'⟩‖ :=
  Fintype.sum_equiv ((Equiv.refl _).embeddingCongr e) _ _
    (fun _ ↦ Fintype.card_congr <| e.flagEmbeddingCongr f)

abbrev Flag.σ (F : Flag α ι) : SimpleGraph ι := F.G.comap F.θ

/--
`F` is a `σ`-flag iff the labelled subgraph given by `θ` is `σ`
-/
def Flag.IsSigma (F : Flag α ι) (σ : SimpleGraph ι) : Prop :=
  F.σ = σ

abbrev Flag.embeddableIn (F₁ : Flag α ι) (F₂ : Flag β ι) : Prop := Nonempty (F₁ ↪f F₂)

lemma FlagEmbedding.sigma_eq {α β ι : Type*} {F₁ : Flag α ι}
    {F₂ : Flag β ι} (e : F₁ ↪f F₂) : F₂.σ = F₁.σ := by
  ext u v; simp [comap_adj, e.labels_eq]

lemma sigma_eq_of_embeddableIn {α β ι : Type*} {F₁ : Flag α ι}
    {F₂ : Flag β ι} {h : F₁.embeddableIn F₂} : F₂.σ = F₁.σ := by
  obtain ⟨e⟩:= h
  exact e.sigma_eq

lemma Flag.isSigma_self (F : Flag α ι) : F.IsSigma (F.G.comap F.θ) := rfl

variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α]

noncomputable instance : Fintype (Flag α ι) :=  Fintype.ofEquiv _ (Flag_equiv_prod α ι).symm

open Classical in
/--
The Finset of all `σ`-flags with vertex type `α` (where both `α` and `ι` are finite).
-/
noncomputable def SigmaFlags (σ : SimpleGraph ι) : Finset (Flag α ι) := {F | F.IsSigma σ}

/--
Flag embeddings of `F₁` in `F₂[t]` are equivalent to embeddings of `F₁` in `F₂` that map into `t`.
(Note: that `F₂[t]` is only defined if all the labels_eq of `F₂` lie in `t`).
-/
def Flag.induceEquiv (F₁ : Flag α ι) (F₂ : Flag β ι) (t : Set β) (h : ∀ i, F₂.θ i ∈ t) :
    F₁ ↪f (F₂.induce t h) ≃ {e : F₁ ↪f F₂ | Set.range e.toEmbedding ⊆ t}
    where
  toFun := fun e ↦ ⟨⟨Embedding.induce _|>.comp e.toRelEmbedding, by
                ext; rw [← F₂.induce_labels_eq t h, e.labels_eq]; rfl⟩, by rintro x ⟨y , rfl⟩; simp⟩
  invFun := fun e ↦ ⟨⟨⟨fun a : α ↦ ⟨e.1.toRelEmbedding a , by apply e.2; simp⟩, fun _ ↦ by simp⟩,
                by simp [Flag.induce_adj]⟩, by ext i; simp [F₂.induce_labels_eq t h, e.1.labels_eq]⟩
  left_inv := fun e ↦ by ext; simp
  right_inv := fun e ↦ by ext; simp

variable {β : Type*} {F₁ : Flag β ι} {F₂ : Flag β ι} {F : Flag α ι}
    (e₁ : F₁ ↪f F) (e₂ : F₂ ↪f F) (b : β)
#check e₁.toRelEmbedding b
/--
Two flag embeddings `e₁ : F₁ ↪f F` and `e₂ : F₂ ↪f F` are compatible if they are in
`general position`, i.e. the intersection of their images is exactly the set of labelled vertices
of `F`.
-/
@[simp]
def FlagEmbedding.Compat {β : Type*} {F₁ : Flag β ι} {F₂ : Flag β ι} {F : Flag α ι}
    (e₁ : F₁ ↪f F) (e₂ : F₂ ↪f F) : Prop :=
  ∀ b₁ b₂, e₁.toRelEmbedding b₁ = e₂.toRelEmbedding b₂ → ∃ i, F.θ i = e₁.toRelEmbedding b₁

omit [Fintype α] [Fintype ι] [DecidableEq α] in
lemma FlagEmbedding.Compat.symm {β : Type*} {F₁ F₂ : Flag β ι} {F : Flag α ι} {e₁ : F₁ ↪f F}
    {e₂ : F₂ ↪f F} (h : e₁.Compat e₂) : e₂.Compat e₁ := by
  simp only [FlagEmbedding.Compat] at *
  intro b₁ b₂ he
  obtain ⟨i, he'⟩ := h _ _ he.symm
  use i, (he ▸ he')

omit [Fintype α] [Fintype ι] [DecidableEq α] in
lemma FlagEmbedding.compat_iff_inter_eq {β : Type*} {F₁ F₂ : Flag β ι} {F : Flag α ι} {e₁ : F₁ ↪f F}
    {e₂ : F₂ ↪f F} : e₁.Compat e₂ ↔ Set.range e₁.toFun ∩ Set.range e₂.toFun =
        Set.range F.θ := by
  constructor <;> intro h
  · apply subset_antisymm
    · intro a; simp only [Set.mem_inter_iff, Set.mem_range]
      rintro ⟨⟨y,rfl⟩,⟨z, hz⟩⟩;
      obtain ⟨i, hi⟩ := h _ _ hz.symm
      use i, hi
    · rw [Set.subset_inter_iff]
      exact ⟨e₁.labels_subset_range, e₂.labels_subset_range⟩
  · intro b₁ b₂ hb
    simp_rw [← Set.mem_range,← h, Set.mem_inter_iff]
    nth_rw 2 [hb]
    simp

variable {k m n : ℕ}

open Finset

/-- **The principle of counting induced flags by averaging**
If `F` is an  `α, ι`-flag and `F₁` is a `β, ι`-flag, then we can count embeddings of `F₁` in `F`
using `#(F₁ ↪f F) * (choose (‖α‖ - ‖β‖) (k - ‖β‖))` is equal to the sum of the number of embeddings
`F₁ ↪f (F.induce t)` over subsets `t` of `α` of size `k`, that contain the image of `F.θ`, i.e.
`t` contains all the labelled vertices of `F` (otherwise there are no embeddings of `F₁` into
`F.induce t`, since any such embedding preserves the labels).
-/
lemma Flag.sum_card_embeddings_induce_eq (F₁ : Flag β ι) (F : Flag α ι) [Fintype β] {k : ℕ}
  (hk : ‖β‖ ≤ k) : ∑ t : Finset α with ht : #t = k ∧ F ⊆ₗt, ‖F₁ ↪f (F.induce t ht.2)‖
                              = ‖F₁ ↪f F‖ * Nat.choose (‖α‖ - ‖β‖) (k - ‖β‖) := by
  classical
  calc
  _ = ∑ t : Finset α , ∑ e : F₁ ↪f F,
          ite (#t = k ∧ (∀ i, F.θ i ∈ t) ∧ Set.range e.toEmbedding ⊆ t) 1 0 := by
    simp_rw [Fintype.card_congr <| Flag.induceEquiv .., dite_eq_ite,  sum_boole,
              Set.coe_setOf, Fintype.card_subtype]
    congr with t
    split_ifs with h1
    · congr with e
      constructor <;> intro he
      · exact  ⟨h1.1 , h1.2, he⟩
      · exact he.2.2
    · contrapose! h1
      obtain ⟨e, he⟩ := card_ne_zero.1 h1.symm
      simp only [mem_filter, mem_univ, true_and] at he
      exact ⟨he.1, he.2.1⟩
  _ = _ := by
    rw [sum_comm, ← card_univ (α := (F₁ ↪f F)), card_eq_sum_ones, sum_mul, one_mul]
    congr with e
    have : ∀ (i : ι), F.θ i ∈ Set.range e.toEmbedding := fun i ↦ ⟨F₁.θ i, by simp [e.labels_eq]⟩
    calc
    _ =  #{t : Finset α | #t = k  ∧ Set.range e.toEmbedding ⊆ t} := by
      rw [sum_boole]
      congr with t; simp only [and_congr_right_iff, and_iff_right_iff_imp]
      intro hk hs i
      exact hs <| this i
    _ = _ := by
      have hs : #((Set.range e.toEmbedding).toFinset) = ‖β‖ :=
        Set.toFinset_range e.toEmbedding ▸ card_image_of_injective _ e.toEmbedding.injective
      rw [← hs, ← card_supersets (hs ▸ hk)]
      congr with t
      constructor <;> intro ⟨ht1, ht2⟩ <;> exact ⟨ht1, fun x hx ↦ ht2 (by simpa using hx)⟩

lemma Flag.sum_card_embeddings_induce_eq'' (F₁ : Flag β ι) (F : Flag α ι) [Fintype β] {k : ℕ}
  (hk : ‖β‖ ≤ k) : ∑ t : {s : Finset α // #s = k ∧ F ⊆ₗ s} , ‖F₁ ↪f (F.induce t t.prop.2)‖
                              = ‖F₁ ↪f F‖ * Nat.choose (‖α‖ - ‖β‖) (k - ‖β‖) := by
  rw [← sum_card_embeddings_induce_eq F₁ F hk]
  rw [sum_dite, sum_const_zero, add_zero]
  rw [sum_bij]
  · intro t ht
    exact ⟨t, by simpa using ⟨t.2.1, t.2.2⟩⟩
  · simp
  · intro s hs t ht h
    apply Subtype.eq (by simpa using h)
  · intro s t
    simp_all only [ mem_univ, Subtype.exists]
    use s.val
    simp only [Subtype.coe_eta, exists_prop, and_true]
    exact ⟨(mem_filter.1 s.2).2.1, ( mem_filter.1 s.2).2.2⟩
  · intro s hs;
    simp

lemma Flag.sum_card_embeddings_induce_eq' (F : Flag β ι) (G : SimpleGraph α) [Fintype β] {k : ℕ}
  (hk : ‖β‖ ≤ k) (θ : ι ↪ α) : ∑ t : Finset α with ht : #t = k ∧ (⟨G, θ⟩ : Flag α ι) ⊆ₗt,
     ‖F ↪f (⟨G, θ⟩ : Flag α ι).induce t ht.2‖
                              = ‖F ↪f ⟨G, θ⟩‖ * Nat.choose (‖α‖ - ‖β‖) (k - ‖β‖) :=
  sum_card_embeddings_induce_eq F _ hk

lemma Flag.ave_sum_card_embeddings_induce_eq1 [Fintype β] {j k : ℕ} (hk : ‖β‖ ≤ k) (F : Flag β ι)
    (G : SimpleGraph α) {s : {x : Finset α // #x = j}} {θ : ι ↪ s} :
 (Nat.choose (‖α‖ - ‖β‖) (k - ‖β‖)) *  ‖F ↪f ⟨G, θ.intoType⟩‖
    = ∑ t : {t : Finset α // #t = k ∧ ∀ i, (θ i).1 ∈ t},
      ‖F ↪f (⟨G, θ.intoType⟩ : Flag α ι).induce t t.prop.2‖ := by
  rw [mul_comm, ← sum_card_embeddings_induce_eq'' F _ hk]
  congr with t

lemma Flag.ave_sum_card_embeddings_induce_eq (F : Flag β ι) (G : SimpleGraph α) [Fintype β]
    [DecidableEq ι] {j k : ℕ} (hj : ‖ι‖ ≤ j) (hk : ‖β‖ ≤ k) :
  (Nat.choose (‖α‖ - ‖ι‖) (j - ‖ι‖)) * Nat.choose (‖α‖ - ‖β‖) (k - ‖β‖) * ∑ θ : ι ↪ α, ‖F ↪f ⟨G, θ⟩‖
  = ∑ s : {s : Finset α // #s = j} , ∑ θ : ι ↪ s, ∑ t : {t : Finset α // #t = k ∧ ∀ i, (θ i).1 ∈ t},
      ‖F ↪f (⟨G, θ.intoType⟩ : Flag α ι).induce t t.prop.2‖  := by
  rw [mul_assoc, mul_sum, sum_embeddings_eq_sum hj]
  simp_rw  [ave_sum_card_embeddings_induce_eq1 hk]


/--
The subtype of all compatible embeddings of a pair of `(β,ι)`-flags in an `(α,ι)`-flag.
-/
abbrev compat_pairs (F₁₂ : Flag β ι × Flag β ι) (F : Flag α ι) :=
  {e : F₁₂.1 ↪f F × F₁₂.2 ↪f F // e.1.Compat e.2}

@[inherit_doc] infixl:50 " ↪f₂ " => compat_pairs

abbrev compat_pair_to_pair {F₁₂ : Flag β ι × Flag β ι} {F : Flag α ι} :
  F₁₂ ↪f₂ F → (F₁₂.1 ↪f F) × (F₁₂.2 ↪f F) := fun e ↦ e.1

lemma compat_pairs_inj {α β ι : Type*} {F : Flag α ι} {F₁₂ : Flag β ι × Flag β ι} :
  Function.Injective (compat_pair_to_pair : F₁₂ ↪f₂ F → (F₁₂.1 ↪f F) × (F₁₂.2 ↪f F)) := by
  rintro ⟨f, _⟩ ⟨g, _⟩; simp

noncomputable instance FlagEmbedding.instfintypeOfCompatEmbeddings {α β ι : Type*} {F : Flag α ι}
    {F₁₂ : Flag β ι × Flag β ι} [Fintype α] [Fintype β] : Fintype (F₁₂ ↪f₂ F) :=
  Fintype.ofInjective _ compat_pairs_inj

/--
Compatible pairs of flag embeddings of `(F₁, F₂)` into `F[t]` are equivalent to compatible pairs
of flag embeddings of `(F₁,F₂)` into `F` that map into `t`.
(Note: that `F[t]` is only defined if all the labels_eq of `F₂` lie in `t`).
-/
def Flag₂.induceEquiv (F₁ F₂ : Flag β ι) (F : Flag α ι) (t : Set α) (h : F ⊆ₗ t) :
    (F₁, F₂) ↪f₂ (F.induce t h) ≃
      {e : (F₁, F₂) ↪f₂ F // Set.range e.1.1.toFun ⊆ t ∧ Set.range e.1.2.toFun ⊆ t}
    where
  toFun := fun e ↦ by
    let f₁ : F₁ ↪f F:=⟨Embedding.induce _|>.comp e.1.1.toRelEmbedding,
      by ext i; rw [← F.induce_labels_eq t h, e.1.1.labels_eq]; rfl⟩
    let f₂ : F₂ ↪f F:=⟨Embedding.induce _|>.comp e.1.2.toRelEmbedding,
      by ext i; rw [← F.induce_labels_eq t h, e.1.2.labels_eq];rfl⟩
    have he : e.val.1.Compat e.val.2 := e.2
    have he1: ∀ b, e.val.1.toRelEmbedding b = f₁.toRelEmbedding b := by intro b; rfl
    have he2: ∀ b, e.val.2.toRelEmbedding b = f₂.toRelEmbedding b := by intro b; rfl
    have hf : f₁.Compat f₂ := by
      intro x y heq
      have he3 : e.val.1.toRelEmbedding x = e.val.2.toRelEmbedding y := by
        rwa [Subtype.ext_iff, he1, he2]
      obtain ⟨i, heq'⟩ := he x y he3
      have : (F.induce t h).θ i = F.θ i := F.induce_labels_eq t h
      use i, by rw [← he1 x, ← this, ← Subtype.ext_iff,heq']
    refine ⟨⟨(f₁,f₂), hf⟩,?_⟩
    simp; constructor <;> intro a ⟨b,hb⟩
    · rw [← he1] at hb; rw [← hb]; simp
    · rw [← he2] at hb; rw [← hb]; simp
  invFun := fun e ↦ by
    have : ∀ b, e.1.1.1.toRelEmbedding b ∈ t := by intro b; apply e.2.1; simp
    let f₁ : (F₁ ↪f (F.induce t h)) := ⟨⟨⟨fun b : β ↦ ⟨e.1.1.1.toRelEmbedding b, e.2.1 (by simp)⟩,
      fun _ _ hb ↦ by simpa using hb⟩, by simp [Flag.induce_adj]⟩,
      by ext i; simp [F.induce_labels_eq t h, e.1.1.1.labels_eq]⟩
    let f₂ : (F₂ ↪f (F.induce t h)) := ⟨⟨⟨fun b : β ↦ ⟨e.1.1.2.toRelEmbedding b, e.2.2 (by simp)⟩,
      fun _ _ hb ↦ by simpa using hb⟩, by simp [Flag.induce_adj]⟩,
      by ext i; simp [F.induce_labels_eq t h, e.1.1.2.labels_eq]⟩
    refine ⟨(f₁,f₂), ?_⟩
    have : ∀ b₁ b₂, e.1.1.1.toRelEmbedding b₁ = e.1.1.2.toRelEmbedding b₂ →
      ∃ i, F.θ i = e.1.1.1.toRelEmbedding b₁  := e.1.2
    simp only [FlagEmbedding.Compat]
    have he1: ∀ b, e.1.1.1.toRelEmbedding b = f₁.toRelEmbedding b := by intro b; rfl
    have he2: ∀ b, e.1.1.2.toRelEmbedding b = f₂.toRelEmbedding b := by intro b; rfl
    intro b₁ b₂ hb
    have heq : e.1.1.1.toRelEmbedding b₁ = e.1.1.2.toRelEmbedding b₂ := by
      rwa [he1, he2, ← Subtype.ext_iff]
    obtain ⟨i, hi⟩ := this _ _ heq
    use i
    have :=F.induce_labels_eq t h (i := i)
    rwa [← this, he1, ←Subtype.ext_iff] at hi
  left_inv := fun e ↦ by ext <;> dsimp
  right_inv := fun e ↦ by ext <;> dsimp

open Classical in
/-- **The principle of counting induced pairs of compatible flag embeddings by averaging**
If `F : Flag α ι` and `F₁, F₂ : Flag β ι` then
`#((F₁, F₂) ↪f G) * (choose (‖α‖ - (2 * ‖β‖ - ‖ι‖)) (k - (2 * ‖β‖ - ‖ι‖)))` is equal to the sum of
the number of embeddings
`(F₁, F₂) ↪f₂ (F.induce t)` over subsets `t` of `α` of size `k`, for any `2 * ‖β‖ - ‖ι‖ ≤ k`.
(Note: the inequality is required for there to exist any compatible pair of flag embeddings into
a subset of size `k` since the two embeddings meet in the labels only i.e. in a `‖ι‖`-set and each
have image of size `‖β‖`).
-/
lemma Flag.sum_card_embeddings_induce_eq_compat (F₁ F₂ : Flag β ι) (F : Flag α ι) [Fintype β]
  {k : ℕ} (hk : 2 * ‖β‖ - ‖ι‖ ≤ k) :
  ∑ t : Finset α with ht : #t = k ∧ F ⊆ₗt, ‖(F₁, F₂) ↪f₂ (F.induce t ht.2)‖
              = ‖(F₁, F₂) ↪f₂ F‖ * Nat.choose (‖α‖ - (2 * ‖β‖ - ‖ι‖) ) (k - (2 * ‖β‖ - ‖ι‖)) := by
  calc
  _ = ∑ t : Finset α , ∑ e : ((F₁,F₂) ↪f₂ F), ite (#t = k ∧ (∀ i, F.θ i ∈ t) ∧
        Set.range e.1.1.toFun ⊆ t ∧ Set.range e.1.2.toFun ⊆ t) 1 0 := by
    simp_rw [Fintype.card_congr <| Flag₂.induceEquiv .., dite_eq_ite]
    simp only [FlagEmbedding.Compat, sum_boole, Nat.cast_id]
    congr with t
    split_ifs with h1
    · change #t = k ∧ ∀ i, F.θ i ∈ t at h1
      simp_rw [h1, Fintype.card_subtype, implies_true, true_and]
    · by_contra! he
      obtain ⟨e, he⟩ := card_ne_zero.1 he.symm
      simp only [mem_filter, mem_univ, true_and] at he
      exact h1 ⟨he.1, he.2.1⟩
  _ = _ := by
    rw [sum_comm, ← card_univ (α := ((F₁,F₂) ↪f₂ F)), card_eq_sum_ones, sum_mul, one_mul]
    congr with e
    have he1 : ∀ (i : ι), F.θ i ∈ Set.range e.1.1.toFun :=
      fun i ↦ ⟨F₁.θ i, by simp [e.1.1.labels_eq]⟩
    calc
    _ = #{t : Finset α | #t = k ∧ Set.range e.1.1.toFun ⊆ t
              ∧ Set.range e.1.2.toFun ⊆ t} := by
      simp only [sum_boole, FlagEmbedding.Compat]
      congr with t; simp only [and_congr_right_iff, and_iff_right_iff_imp]
      intro hk hs i
      exact hs.1 <| he1 i
    _ =  #{t : Finset α | #t = k ∧
      Set.range e.1.1.toFun ∪ Set.range e.1.2.toFun ⊆ t} := by
      congr with t; simp
    _ = _ := by
      have hint := FlagEmbedding.compat_iff_inter_eq.1 e.2
      have hs1 : #((Set.range e.1.1.toFun).toFinset) = ‖β‖ := Set.toFinset_range
        e.1.1.toFun ▸ card_image_of_injective _ e.1.1.toRelEmbedding.injective
      have hs2 : #((Set.range e.1.2.toFun).toFinset) = ‖β‖ := Set.toFinset_range
        e.1.2.toFun ▸ card_image_of_injective _ e.1.2.toRelEmbedding.injective
      have hl : #(Set.range F.θ).toFinset = ‖ι‖ :=
        Set.toFinset_range F.θ ▸ card_image_of_injective _ F.θ.injective
      have : #((Set.range e.1.1.toFun ∪ Set.range e.1.2.toFun).toFinset)
        = 2* ‖β‖- ‖ι‖ := by
        simp_rw [Set.toFinset_union, card_union, hs1, hs2, ← Set.toFinset_inter, hint, hl, two_mul]
      convert card_supersets (this ▸ hk) with t <;> try exact this.symm
      · constructor <;> intro h <;> intro _ hx
        · exact Finset.mem_coe.1 <| h <| Set.mem_toFinset.1 hx
        · exact h <| Set.mem_toFinset.2 hx

end SimpleGraph
