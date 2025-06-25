/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Flag.Counting
set_option linter.style.header false
local notation "‖" x "‖" => Fintype.card x

variable {k m n : ℕ} {α β ι : Type*}


open Finset SimpleGraph

/-- Given a `G : SimpleGraph α` and a `k`-set `t` this is the canonical `Fin k`-graph of the
subgraph induced by `t`. -/
def SimpleGraph.finGraph (G : SimpleGraph α) {t : Finset α} (ht : #t = k) :
  SimpleGraph (Fin k) := (G.induce t).overFin (by simp [ht])

@[simp]
lemma SimpleGraph.induces_finGraph  (G : SimpleGraph α) {t : Finset α} (ht : #t = k) :
    G.induces t (G.finGraph ht) := by
  apply Nonempty.intro (overFinIso (G.induce t) (by simp [ht.symm])).symm

open Classical in
@[simp]
lemma induce_eq (G : SimpleGraph α) (H : SimpleGraph β) [Fintype α] [Fintype β] :
    #{t : Finset α | #t = ‖β‖ ∧ G.induces t H} = #{t : Finset α | G.induces t H} := by
  congr
  ext; simp only [Set.mem_setOf_eq, and_iff_right_iff_imp, Nonempty.forall]
  intro e
  apply card_induces ⟨e⟩

open Classical in
lemma sum_induce_fin (G : SimpleGraph α) (H : SimpleGraph β) [Fintype α] [Fintype β]
  {k : ℕ} (hk : ‖β‖ ≤ k) : #{t : Finset α | #t = ‖β‖ ∧ G.induces t H} * ‖H.Aut‖ *
    Nat.choose (‖α‖ - ‖β‖) (k - ‖β‖) = ∑ K : SimpleGraph (Fin k),
    #{s : Finset (Fin k) | #s = ‖β‖ ∧ K.induces s H} * ‖H.Aut‖ *
    #{t : {t : Finset α // #t = k} | G.finGraph t.2 = K} := by
    simp_rw [← card_embeddings_eq_card_induces_mul_card_aut, ← sum_card_embeddings_induce_eq _ _ hk]
    calc
  _ = ∑ t : {t : Finset α // #t = k} , ‖H ↪g (G.induce t)‖  := by
    rw [← sum_subtype_eq_sum_filter, subtype_univ]
  _ = _ := by
    let f : {t : Finset α // #t = k} → SimpleGraph (Fin k) :=
    fun t ↦ G.finGraph t.2
    let e := (Equiv.sigmaFiberEquiv f).symm
    let g : (K : SimpleGraph (Fin k)) × { t : {t : Finset α // #t = k} // f t = K } → ℕ :=
    fun ⟨K, t⟩ ↦ ‖H ↪g K‖
    rw [Fintype.sum_equiv e _ g]
    · rw [Fintype.sum_sigma]
      congr! with K hk
      dsimp [g]
      rw [card_eq_sum_ones, mul_sum, mul_one]
      dsimp [f]
      rw [← sum_subtype_eq_sum_filter, sum_const, sum_const]
      congr!
      ext x; simp
    · intro t;
      dsimp [g, e, f]
      apply Fintype.card_congr
      apply Iso.embeddingCongr Iso.refl
      exact (induce t G).overFinIso _


open Classical in
lemma sum_induce_fin' (G : SimpleGraph α) (H : SimpleGraph β) [Fintype α] [Fintype β]
    {k : ℕ} (hk : ‖β‖ ≤ k) :
    #{t : Finset α | G.induces t H} * Nat.choose (‖α‖ - ‖β‖) (k - ‖β‖) =
      ∑ K : SimpleGraph (Fin k), #{s : Finset (Fin k) | K.induces s H} *
        #{t : {t : Finset α // #t = k} | G.finGraph t.2 = K} := by
  have  h := sum_induce_fin G H hk
  simp_rw [mul_comm _ (‖Aut H‖), mul_assoc, ←mul_sum, induce_eq] at h
  exact (mul_right_inj' Fintype.card_ne_zero).1 h

-- TODO: change this to be useful 
open Classical in
lemma card_finGraph_eq (G : SimpleGraph α) (K : SimpleGraph (Fin k)) [Fintype α] :
   ‖{t : {t : Finset α // #t = k} // G.induces t K}‖  =
    ∑ K' : {K' : SimpleGraph (Fin k) // Nonempty (K ≃g K')},
      #{t : {t : Finset α // #t = k} | G.finGraph t.2 = K'} := by
  let f : {t : {t : Finset α // #t = k} // G.induces t K} → SimpleGraph (Fin k) :=
    fun t ↦ G.finGraph t.1.2
  let e := (Equiv.sigmaFiberEquiv f).symm
  rw [← card_univ, card_eq_sum_ones, Fintype.sum_equiv e (g := fun _ ↦ 1)]
  · simp_rw [card_eq_sum_ones, Fintype.sum_sigma]
    simp only [sum_const, card_univ, smul_eq_mul, mul_one]
    have : ∀ K' : SimpleGraph (Fin k), ¬ Nonempty (K ≃g K') → ‖{x // f x = K'}‖ = 0:= by
      intro K' hf
      by_contra!
      have h' : 0 < ‖{ x // f x = K' }‖ := pos_of_ne_zero this
      obtain ⟨t⟩  := Fintype.card_pos_iff.1 h'
      dsimp [f] at t
      apply hf ⟨(t.2 ▸ (G.induces_finGraph t.1.1.2).some).symm.comp t.1.2.some⟩
    calc
    _ = ∑ K' : {K' : SimpleGraph (Fin k) // Nonempty (K ≃g K')}, ‖{x // f x = K'}‖  := by
      rw [← sum_filter_add_sum_filter_not univ (fun K' ↦ Nonempty (K ≃g K'))]
      nth_rw 2 [sum_filter]
      rw  [← add_zero (∑ K' : {K' : SimpleGraph (Fin k) // Nonempty (K ≃g K')}, ‖{x // f x = K'}‖)]
      congr!
      · rw [← sum_subtype_eq_sum_filter, subtype_univ]
      · convert sum_const_zero with  x hx
        split_ifs with h0
        · rfl
        · apply this _ h0
    _ = _ := by
      congr! with K' hK'
      dsimp [f]
      rw [← card_univ]
      apply Finset.card_bij (i := fun x hx ↦ x.1.1)
      · intro a ha
        simpa using a.2
      · intro a1 h1 a2 h2 h12
        aesop
      · intro a ha
        refine ⟨⟨⟨a, ?_⟩, ?_⟩, ?_⟩
        · let e := K'.2.some
          simp at ha
          let f := (ha ▸ G.induces_finGraph a.2).some
          exact ⟨(f.comp e)⟩
        · simpa using ha
        · simp
  · simp

#check Equiv.sigmaPreimageEquiv
#check Equiv.sigmaFiberEquiv
def isIsoTo : SimpleGraph α → SimpleGraph α → Prop := fun G G' ↦ Nonempty (G ≃g G')

instance isIsoToSetoid (α : Type*) : Setoid (SimpleGraph α) where
  r := isIsoTo
  iseqv := ⟨fun _ ↦ ⟨Iso.refl⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩⟩

def UnlabelledGraph (β : Type*) := Quot <| isIsoToSetoid β

noncomputable def UnlabelledGraph.toFinGraph {β : Type*} (G : UnlabelledGraph β) :
  SimpleGraph β := G.out

def SimpleGraph.toUnlabelled {β : Type*} (G : SimpleGraph β) : UnlabelledGraph β :=
   Quot.mk (isIsoToSetoid β) G

noncomputable instance {β : Type*} [Fintype β] : Fintype (UnlabelledGraph β) := by
  rw [UnlabelledGraph]
  classical
  apply Quotient.fintype

open Classical in
lemma sum_induce_unlabelled (G : SimpleGraph α) (H : SimpleGraph β) [Fintype α] [Fintype β]
  {k : ℕ} (hk : ‖β‖ ≤ k) :
    ∑ t : {t : Finset α // #t = k} , ‖H ↪g (G.induce t)‖ =
    ∑ K : UnlabelledGraph (Fin k), #{t : Finset α | #t = k ∧ G.induces t K.out} * ‖H ↪g K.out‖ := by
  let f : {t : Finset α // #t = k} → UnlabelledGraph (Fin k) :=
    fun t ↦ ((G.induce t).overFin (n := k) (by simpa using t.2)).toUnlabelled
  let e := Equiv.sigmaFiberEquiv f
  let g : (K : UnlabelledGraph (Fin k)) × { t : {t : Finset α // #t = k} // f t = K } → ℕ :=
    fun ⟨K, t⟩ ↦ ‖H ↪g K.out‖
  rw [Fintype.sum_equiv e.symm _ g]
  · rw [Fintype.sum_sigma]
    congr! with K hk
    dsimp [g]
    rw [card_eq_sum_ones, sum_mul, one_mul]
    dsimp [f]
    rw [← sum_subtype_eq_sum_filter, sum_const, sum_const]
    congr!
    apply card_equiv (by sorry) (by sorry)
  · intro t;
    dsimp [g]
    apply Fintype.card_congr
    apply Iso.embeddingCongr  Iso.refl
    dsimp [e, f]
--    exact ⟨fun t ↦ t, by sorry, by sorry, by sorry⟩
    sorry
/-
    ∑ K : SimpleGraph (Fin k), (#{s : Finset (Fin k) | #s = ‖β‖ ∧ K.induces s H} / ‖Aut K‖) *
      #{t : Finset α | #t = k ∧ G.induces t K}
-/
#check embeddingsEquivInduceProdAut
open Classical in
lemma sum_induce_unlabelled' (G : SimpleGraph α) (H : SimpleGraph β) [Fintype α] [Fintype β]
  {k : ℕ} (hk : ‖β‖ ≤ k) :
    ∑ t : {t : Finset α // #t = k} , ‖H ↪g (G.induce t)‖   =
    ∑ K : SimpleGraph (Fin k), (#{s : Finset (Fin k) | #s = ‖β‖ ∧ K.induces s H} * ‖Aut H‖) *
      (#{t : Finset α | #t = k ∧ G.induces t K} / ‖Aut K‖) := by
  let f : {t : Finset α // #t = k} → SimpleGraph (Fin k) :=
    fun t ↦ ((G.induce t).overFin (n := k) (by simpa using t.2))
  let e := (Equiv.sigmaFiberEquiv f).symm
  let g : (K : SimpleGraph (Fin k)) × { t : {t : Finset α // #t = k} // f t = K } → ℕ :=
    fun ⟨K, t⟩ ↦ ‖H ↪g K‖
  rw [Fintype.sum_equiv e _ g]
  · rw [Fintype.sum_sigma]
    congr! with K hk
    dsimp [g]
    rw [sum_const, smul_eq_mul, card_univ, card_embeddings_eq_card_induces_mul_card_aut, mul_comm]
    congr!
    dsimp [f]
    symm
    apply Nat.div_eq_of_eq_mul_left (Fintype.card_pos)
    rw [← Fintype.card_prod]
    symm
    rw [← card_univ]
    apply card_bij (i := fun ⟨x, e⟩ hxe ↦ x.1.1)
    · intro ⟨x, e⟩ ha

      simp only [mem_filter, mem_univ, true_and]
      constructor
      · aesop
      · have := x.2
        sorry
    · intro ⟨x1, e1⟩ h1 ⟨x2, e2⟩ h2 h
      rw [Prod.ext_iff]
      dsimp
      constructor
      · aesop
      · sorry
    · intro t ht
      sorry
    -- congr!
    -- apply card_equiv (by sorry) (by sorry)
  · intro t;
    dsimp [g]
    apply Fintype.card_congr
    apply Iso.embeddingCongr  Iso.refl
    dsimp [e, f]
    exact (induce t G).overFinIso _
