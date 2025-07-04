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
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Flag.Counting
set_option linter.style.header false
local notation "‖" x "‖" => Fintype.card x

variable {k m n : ℕ} {α β ι : Type*}
open Finset SimpleGraph
namespace SimpleGraph

def AdjMatrices (G : SimpleGraph α) : Set (Matrix (Fin k) (Fin k) ℕ) :=
  {M | ∃ h : M.IsAdjMatrix, Nonempty (h.toGraph ≃g G)}

open Classical in
noncomputable instance [Fintype α] (G : SimpleGraph α) (h : ‖α‖ = k) :
    Fintype (G.AdjMatrices (k := k)) := by
  unfold AdjMatrices
  apply Set.fintypeOfFiniteUniv
  apply?



/-- Given a `G : SimpleGraph α` this is a `Fin k`-graph isomorphic to `G`. -/
def finGraph (G : SimpleGraph α) [Fintype α] (ht : ‖α‖ = k) :
  SimpleGraph (Fin k) := G.overFin (by simp [ht])



def isIsoTo : SimpleGraph α → SimpleGraph α → Prop := fun G G' ↦ Nonempty (G ≃g G')

instance isIsoToSetoid (α : Type*) : Setoid (SimpleGraph α) where
  r := isIsoTo
  iseqv := ⟨fun _ ↦ ⟨Iso.refl⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩⟩

abbrev FinGraph (α : Type*) := Quotient <| isIsoToSetoid α


lemma induce_equiv (G : SimpleGraph α) (H : SimpleGraph β) (G' : SimpleGraph α) (H' : SimpleGraph β)
  [Fintype α] [Fintype β] : G ≈ G' → H ≈ H' → ‖H ↪g G‖ = ‖H' ↪g G'‖ := by
  intro ⟨e⟩ ⟨f⟩
  apply Fintype.card_congr
  exact f.embeddingCongr e

/--
The number of embeddings of the unlabelled graph H₁ in the unlabelled graph G₁
-/
noncomputable def card_embedding (G₁ : FinGraph α) (H₁ : FinGraph β) [Fintype α] [Fintype β] :=
  Quotient.lift₂ (fun G H ↦ (‖H ↪g G‖)) (fun _ _ _ _ ↦ induce_equiv _ _ _ _) G₁ H₁

#check card_embedding
