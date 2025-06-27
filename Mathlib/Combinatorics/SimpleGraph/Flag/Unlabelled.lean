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

@[reducible]
def equiv_setoid [Fintype α] (r : Setoid α) : α ≃ Σ c : r.classes, c  where
  toFun := fun a ↦ ⟨⟨_, r.mem_classes a⟩, ⟨a, by simp; rfl⟩⟩
  invFun := fun ⟨c, x⟩ ↦ x
  left_inv := by intro a; rfl
  right_inv := by
    intro ⟨c, x⟩
    ext y;
    · simp
      constructor <;> intro h
      · have := x.2;
        obtain ⟨c2, hc1, hc2, hc3⟩:= r.rel_iff_exists_classes.1 h
        have := r.eq_of_mem_classes hc1 hc3  c.2 this
        subst this; exact hc2
      · exact r.rel_iff_exists_classes.2 ⟨_, c.2, h, x.2⟩
    · simp

open Classical in
lemma sum_setoid [Fintype α] (r : Setoid α) (f : α → β) [AddCommMonoid β] :
  ∑ a, f a = ∑ c : r.classes, ∑ a : c, f a := by
  rw [Fintype.sum_equiv (equiv_setoid r) (g := fun ⟨c, x⟩ ↦ f x.val)]
  · rw [Fintype.sum_sigma]
  · intro a; simp

noncomputable def Setoid.out {r : Setoid α} (c : r.classes) : α :=
  (r.quotientEquivClasses.symm c).out

lemma setoid_out_equiv {r : Setoid α} (c : r.classes) (x : ↑c) : r x.val (Setoid.out c) := by
  apply r.rel_iff_exists_classes.2 ⟨_, c.2,x.2, by
    rw [Setoid.out];
    have h1 := r.quotientEquivClasses_mk_eq x.val
    have h2 := Quotient.mk_out (s := r) x.val
    have h3 : ↑(r.quotientEquivClasses ⟦↑x⟧) = c := by
      ext y; rw [h1]
      constructor <;> intro h
      · dsimp at h
        obtain ⟨d,hd1,hd2,hd3 ⟩:= r.rel_iff_exists_classes.1 h
        have := r.eq_of_mem_classes hd1 hd3  c.2 x.2
        subst this; exact hd2
      · dsimp
        apply r.rel_iff_exists_classes.2 ⟨_, c.2, h, x.2⟩
    apply_fun  r.quotientEquivClasses.symm at h3
    simp only [Equiv.symm_apply_apply] at h3
    rw [← h3]
    obtain ⟨d,hd1,hd2,hd3 ⟩:= r.rel_iff_exists_classes.1 h2
    have := r.eq_of_mem_classes hd1 hd3  c.2 x.2
    subst this
    exact hd2⟩

noncomputable instance [r : Setoid α] : Coe r.classes α :=
  ⟨fun c ↦ Setoid.out c⟩

open Classical in
lemma sum_setoid' [Fintype α] (r : Setoid α) (f : α → ℕ) (hf : ∀ a b, a ≈ b → f a = f b) :
  ∑ a, f a = ∑ c : r.classes, ‖c‖ * f c := by
  rw [sum_setoid]
  congr! with c hc
  rw [← card_univ, card_eq_sum_ones, sum_mul, one_mul]
  apply sum_congr rfl
  intro x hx
  apply hf
  exact setoid_out_equiv _ _


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

#check Finpartition
open Classical in
lemma sum_induce_fin' (G : SimpleGraph α) (H : SimpleGraph β) [Fintype α] [Fintype β]
    {k : ℕ} (hk : ‖β‖ ≤ k) :
    #{t : Finset α | G.induces t H} * Nat.choose (‖α‖ - ‖β‖) (k - ‖β‖) =
      ∑ K : SimpleGraph (Fin k), #{s : Finset (Fin k) | K.induces s H} *
        #{t : {t : Finset α // #t = k} | G.finGraph t.2 = K} := by
  have  h := sum_induce_fin G H hk
  simp_rw [mul_comm _ (‖Aut H‖), mul_assoc, ←mul_sum, induce_eq] at h
  exact (mul_right_inj' Fintype.card_ne_zero).1 h

#check SimpleGraph.isIsoToSetoid (Fin k)


variable (c : (isIsoToSetoid (Fin k)).classes)
variable (K : ↑c)


open Classical in
lemma sum_induce_fin'' (G : SimpleGraph α) (H : SimpleGraph β) [Fintype α] [Fintype β]
    {k : ℕ} (hk : ‖β‖ ≤ k) :
    #{t : Finset α | G.induces t H} * Nat.choose (‖α‖ - ‖β‖) (k - ‖β‖) =
     ∑ c : (isIsoToSetoid (Fin k)).classes,
     ∑ K : c, #{s : Finset (Fin k) | (K : SimpleGraph (Fin k)).induces s H} *
        #{t : {t : Finset α // #t = k} | G.finGraph t.2 = K} := by
  rw [sum_induce_fin' _ _ hk, sum_setoid]
  



open Classical in
lemma card_sum_finGraph_eq (G : SimpleGraph α) (K : SimpleGraph (Fin k)) [Fintype α] :
   ‖{t : {t : Finset α // #t = k} // G.induces t K}‖ =
     ∑ K' : {K' : SimpleGraph (Fin k) // K ≈ K'},
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
      apply Finset.card_bij (i := fun x _ ↦ x.1.1)
      · intro a ha
        simpa using a.2
      · intro a1 h1 a2 h2 h12
        aesop
      · intro a ha
        simp only [mem_filter, mem_univ, true_and, f] at ha
        exact ⟨⟨⟨a, ⟨(((ha ▸ G.induces_finGraph a.2).some).comp K'.2.some)⟩⟩, ha⟩, by simp⟩
  · simp

open Classical in
lemma card_sum_finGraph_eq_mul (G : SimpleGraph α) [Fintype α] (f : SimpleGraph (Fin k) → ℕ)
  (hf : ∀ K₁ K₂,  K₁ ≈ K₂ → f K₁ = f K₂) :
  ∑ (K : SimpleGraph (Fin k)), ‖{t : {t : Finset α // #t = k} // G.induces t K}‖ * f K =
     ∑ (K : SimpleGraph (Fin k)), ∑ K' : {K' : SimpleGraph (Fin k) // K ≈ K'},
       #{t : {t : Finset α // #t = k} | G.finGraph t.2 = K'} * f K' := by
    congr!
    rw [card_sum_finGraph_eq, sum_mul]
    congr! 2 with K' hK'
    rw [hf _ _ K'.2]




variable {G H : SimpleGraph α}

def UnlabelledGraph (β : Type*) := Quot <| isIsoToSetoid β

lemma iseqv_iff {G H : SimpleGraph α} : G ≈ H ↔ Nonempty (G ≃g H) := Iff.rfl

noncomputable def UnlabelledGraph.toFinGraph {β : Type*} (G : UnlabelledGraph β) :
  SimpleGraph β := G.out


def SimpleGraph.toUnlabelled {β : Type*} (G : SimpleGraph β) : UnlabelledGraph β :=
   Quot.mk (isIsoToSetoid β) G

noncomputable instance {β : Type*} [Fintype β] : Fintype (UnlabelledGraph β) := by
  rw [UnlabelledGraph]
  classical
  apply Quotient.fintype
