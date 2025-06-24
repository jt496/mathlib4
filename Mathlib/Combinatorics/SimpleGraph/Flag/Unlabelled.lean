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
#check Equiv.sigmaPreimageEquiv
#check Equiv.sigmaFiberEquiv
def isIsoTo : SimpleGraph α → SimpleGraph α → Prop :=fun G G' ↦ Nonempty (G ≃g G')

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
    sorry
