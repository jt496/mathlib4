/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Subwalk

/-!
We extend some of the walk decomposition API : we already have `takeUntil` and `dropUntil`
which satisfy `(w.takeUntil _ hx) ++ (w.dropUntil _ hx) = w`, where `w.takeUntil _ hx` is the part
of `w` from its start to the first occurence of `x` (given `hx : x ∈ w.support`).

We define two new walks `shortCut` and `shortClosed` where `w.shortCut hx` is the walk
that travels along `w` from `u` to `x` and then back to `v` without revisiting `x` and
`w.shortClosed hx` is the closed walk that travels along `w` from the first visit of `x` to the last
 visit.

We also introduce `takeUntilNext` and `dropUntilNext` which, given a closed walk `w : G.Walk u u`,
yield the walks in `w` from start to the next occurence of `u` and then from there to the end
respectively.

We use these to prove that given a closed walk of odd length in `G` there is an odd length cycle.
  `exists_odd_cycle`

We also prove `exists_odd_cycle_subwalk` that given `w` a closed odd walk then there is a subwalk of
`w` that is an odd cycle.
-/

namespace SimpleGraph.Walk
open Walk List
variable {α : Type*} {u v x w : α} {G : SimpleGraph α}

theorem support_eq_concat {u v : α} (p : G.Walk u v) : p.support = p.support.dropLast ++ [v] := by
  cases p with
  | nil => rfl
  | cons h p =>
    obtain ⟨x, q, h',h2⟩ := exists_cons_eq_concat h p
    simp [h2]

lemma mem_support_reverse {u v x : α} (p : G.Walk u v) : x ∈ p.reverse.support ↔ x ∈ p.support := by
  simp [*]

@[simp]
lemma length_takeUntil_add_dropUntil [DecidableEq α] {p : G.Walk u v} (h : w ∈ p.support) :
    (p.takeUntil w h).length + (p.dropUntil w h).length = p.length := by
  rw [← length_append, take_spec]

lemma takeUntil_append_of_mem_left [DecidableEq α] (p : G.Walk u v) (q : G.Walk v w)
    (hx : x ∈ p.support) :
    (p ++ q).takeUntil x (subset_support_append_left _ _ hx) = p.takeUntil _ hx  := by
  induction p with
  | nil => rw [mem_support_nil_iff] at hx; subst_vars; simp
  | @cons u _ _ _ p ih =>
    rw [support_cons] at hx
    by_cases hxu : u = x
    · subst_vars; simp
    · have := List.mem_of_ne_of_mem (fun hf ↦ hxu hf.symm) hx
      simp_rw [takeUntil_cons this hxu, cons_append]
      rw [takeUntil_cons (subset_support_append_left _ _ this) hxu]
      simpa using ih _ this


lemma IsPath.length_one_of_end_start_mem_edges {u v : α} {w : G.Walk u v}
    (hp : w.IsPath) (h1 : s(v, u) ∈ w.edges) : w.length = 1 := by
  cases w with
  | nil => simp at h1
  | cons h p =>
    cases p with
    | nil => simp
    | cons h' p =>
      exfalso
      simp_all only [cons_isPath_iff, edges_cons, mem_cons, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq,
        Prod.swap_prod_mk, and_true, support_cons, not_or, and_false, false_or, or_false]
      obtain ( rfl | ⟨rfl, rfl⟩ | hf) := h1
      · apply hp.1.2 p.end_mem_support
      · apply hp.2.2 p.start_mem_support
      · apply hp.2.2 (p.snd_mem_support_of_mem_edges hf)

/--
If `w : G.Walk u u` is a closed walk and `w.support.tail.Nodup` then it is almost a cycle, in the
sense that is either a cycle or nil or has length 2.
-/
lemma isCycle_or_nil_or_length_two_of_support_tail_nodup {u : α} (w : G.Walk u u)
    (hn : w.support.tail.Nodup) : w.IsCycle ∨ w.Nil ∨ w.length = 2 := by
  by_cases hnc : w.IsCycle
  · exact Or.inl hnc
  right
  contrapose! hnc
  rw [isCycle_def]
  refine ⟨?_, fun hf ↦ hnc.1 <| nil_iff_eq_nil.mpr hf, hn⟩
  apply IsTrail.mk
  cases w with
  | nil => simp
  | @cons _ b _ h w =>
    have : s(u, b) ∉ w.edges := by
      intro hf
      apply hnc.2
      simp only [support_cons, List.tail_cons] at hn
      simpa using (IsPath.mk' hn).length_one_of_end_start_mem_edges hf
    cases w with
    | nil => simp
    | cons h w =>
      rw [support_cons, List.tail_cons] at hn
      apply nodup_cons.2 ⟨by aesop, edges_nodup_of_support_nodup hn⟩

lemma isCycle_odd_support_tail_nodup {u : α} {w : G.Walk u u} (ho : Odd w.length)
    (hn : w.support.tail.Nodup) : w.IsCycle := by
  apply (w.isCycle_or_nil_or_length_two_of_support_tail_nodup hn).resolve_right
  rintro (hf | hf)
  · rw [nil_iff_length_eq.mp hf] at ho
    exact (Nat.not_odd_zero ho).elim
  · rw [hf] at ho
    exact (Nat.not_odd_iff_even.2 (by decide) ho).elim

variable [DecidableEq α]

lemma support_tail_nodup_iff_count_le  {u : α} (w : G.Walk u v) : w.support.tail.Nodup ↔
    w.support.count u ≤ 2 ∧ ∀ x ∈ w.support, x ≠ u → count x w.support ≤ 1 := by
  rw [List.nodup_iff_count_le_one, support_eq_cons]
  simp only [List.tail_cons, count_cons_self, Nat.reduceLeDiff, mem_cons, ne_eq, forall_eq_or_imp,
    not_true_eq_false, add_le_iff_nonpos_left, nonpos_iff_eq_zero, IsEmpty.forall_iff, true_and]
  constructor
  · intro h
    constructor
    · exact h u
    · intro x _ h'
      have := h x
      simpa [Ne.symm h']
  · intro ⟨_, h1⟩ a
    by_cases ha : a ∈ w.support
    · by_cases ha' : a = u
      · subst a
        simpa
      · rw [support_eq_cons] at ha
        simp_all only [mem_cons, false_or]
        have :=  h1 _ ha ha'
        rw [count_cons] at this
        omega
    · rw [count_eq_zero_of_not_mem (fun hf ↦ ha (mem_of_mem_tail hf))]
      omega

/-- Given a vertex `x` in a walk `w` form the walk that travels along `w` from the first visit of
`x` to the last visit of `x` (which may be the same in which case this is `nil' x`) -/
abbrev shortClosed (w : G.Walk u v) (hx : x ∈ w.support) : G.Walk x x :=
  ((w.dropUntil _ hx).reverse.dropUntil _ (by simp)).reverse

@[simp]
lemma shortClosed_start (w : G.Walk u v) : (w.shortClosed (w.start_mem_support)) =
    (w.reverse.dropUntil _ (by simp)).reverse := by
  cases w <;> simp [dropUntil, shortClosed]

@[simp]
lemma shortClosed_of_eq {y: α} (w : G.Walk u v) (hx : x ∈ w.support) (hy : y ∈ w.support)
    (h : y = x) : w.shortClosed hx = (w.shortClosed hy).copy h h := by
  subst h
  rfl

@[simp]
lemma dropUntil_spec (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.shortClosed hx) ++ (w.reverse.takeUntil x (w.mem_support_reverse.2 hx)).reverse =
    w.dropUntil x hx := by
  have hc := congr_arg reverse <| take_spec (w.dropUntil _ hx).reverse (end_mem_support _)
  rw [reverse_reverse, ← hc, reverse_append] at *
  symm
  congr! 2
  conv_rhs =>
    enter [1]
    rw [← take_spec w hx, reverse_append]
  rw [takeUntil_append_of_mem_left]

/-- w.shortCut1 ++ w.shortClosed ++ w.shortCut2 = w -/
lemma take_shortClosed_reverse_spec (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.takeUntil _ hx) ++ ((w.shortClosed hx) ++
      (w.reverse.takeUntil _ (w.mem_support_reverse.2 hx)).reverse) = w := by
  conv_rhs =>
    rw [← take_spec w hx]
  rw [w.dropUntil_spec hx]

lemma shortClosed_infix {u v x : α} {p : G.Walk u v} (hx : x ∈ p.support) :
   Infix (p.shortClosed hx) p := by
  use p.takeUntil _ hx, (p.reverse.takeUntil _ (p.mem_support_reverse.2 hx)).reverse
  have := (take_shortClosed_reverse_spec p hx).symm
  rwa [← append_assoc]

lemma count_reverse {y : α} (w : G.Walk u v) :
    w.reverse.support.count y = w.support.count y := by
  simp

lemma takeUntil_count_le {y : α} (w : G.Walk u v) (hx : x ∈ w.support) :
  (w.takeUntil _ hx).support.count y ≤ w.support.count y := (takeUntil_prefix hx).subwalk.count_le _

@[simp]
lemma dropUntil_count_le {y : α} (w : G.Walk u v) (hx : x ∈ w.support) :
  (w.dropUntil _ hx).support.count y ≤ w.support.count y := (dropUntil_suffix hx).subwalk.count_le _

lemma shortClosed_count_le {y : α} (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.shortClosed hx).support.count y ≤ w.support.count y :=
  (shortClosed_infix hx).subwalk.count_le _

/-- Given a vertex `x` in a walk `w : G.Walk u v` form the walk that travels along `w` from `u`
to `x` and then back to `v` without revisiting `x` -/
abbrev shortCut (w : G.Walk u v) (hx : x ∈ w.support) : G.Walk u v :=
  (w.takeUntil _ hx) ++ (w.reverse.takeUntil _ (w.mem_support_reverse.2 hx)).reverse

lemma shortCut_subwalk {u v x : α} {p : G.Walk u v} (hx : x ∈ p.support) :
   (p.shortCut hx).Subwalk p := by
  have := (take_shortClosed_reverse_spec p hx).symm
  convert Subwalk.of_prefix_append_suffix

@[simp]
lemma shortCut_start (w : G.Walk u v) : w.shortCut w.start_mem_support =
    (w.reverse.takeUntil _ (w.mem_support_reverse.2 (by simp))).reverse := by
  cases w <;> simp [shortCut]

lemma mem_support_shortCut (w : G.Walk u v) (hx : x ∈ w.support) :
    x ∈ (w.shortCut hx).support := by
  simp [shortCut]

lemma shortCut_not_nil (w : G.Walk u v) (hx : x ∈ w.support) (hu : x ≠ u) :
    ¬(w.shortCut hx).Nil := by
  rw [shortCut]
  simp only [nil_append_iff, nil_takeUntil, nil_reverse, not_and]
  rintro rfl; contradiction

lemma shortCut_count_le {y : α} (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.shortCut hx).support.count y ≤ w.support.count y :=
  List.Sublist.count_le _ (w.shortCut_subwalk hx).support_sublist

lemma notMem_support_reverse_tail_takeUntil (w : G.Walk u v) (hx : x ∈ w.support) :
    x ∉ (w.takeUntil x hx).support.reverse.tail := by
  intro hx2
  rw [← count_pos_iff, count_tail, List.count_reverse,
      count_support_takeUntil_eq_one, support_eq_concat] at hx2
  simp at hx2

/-- If `x` is a repeated vertex of the walk `w` then `w.shortClosed hx` is
a non-nil closed walk. -/
lemma shortClosed_not_nil_of_one_lt_count (w : G.Walk u v) (hx : x ∈ w.support)
    (h2 : 1 < w.support.count x) : ¬ (w.shortClosed hx).Nil := by
  intro h
  have : w.dropUntil x hx = (w.reverse.takeUntil x (w.mem_support_reverse.2 hx)).reverse := by
    simp [← dropUntil_spec w hx, h.eq_nil]
  have hw :=  congr_arg (count x) <| congr_arg support <| take_spec w hx
  rw [this, support_append, count_append, count_support_takeUntil_eq_one, support_reverse] at hw
  exact (w.reverse.notMem_support_reverse_tail_takeUntil (by simpa)) <| count_pos_iff.1 (by omega)

lemma length_shortCut_add_shortClosed (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.shortCut hx).length + (w.shortClosed hx).length = w.length := by
  simp_rw [← length_takeUntil_add_dropUntil hx, ← w.dropUntil_spec hx, shortClosed, shortCut,
            length_append, length_reverse]
  omega

lemma length_shortClosed_lt_length {p : G.Walk u u} {x : α} (hx : x ∈ p.support) (hne : x ≠ u) :
    (p.shortClosed hx).length < p.length := by
  rw [ ← p.length_shortCut_add_shortClosed hx]
  rw [lt_add_iff_pos_left, ← not_nil_iff_lt_length]
  exact p.shortCut_not_nil hx hne

lemma length_shortCut_lt_length {p : G.Walk u u} {x : α} (hx : x ∈ p.support)
    (h2 : 1 < p.support.count x) : (p.shortCut hx).length < p.length := by
  rw [ ← p.length_shortCut_add_shortClosed hx]
  rw [lt_add_iff_pos_right, ← not_nil_iff_lt_length]
  exact p.shortClosed_not_nil_of_one_lt_count hx h2

/--
Given a closed walk `w : G.Walk u u` and a vertex `x ∈ w.support` we can form a new closed walk
`w.shorterOdd hx`. If `w.length` is odd then this walk is also odd. Morever if `x` occured more
than once in `w` and `x ≠ u` then `w.shorterOdd hx` is strictly shorter than `w`.
-/
def shorterOdd {u : α} (p : G.Walk u u) {x : α} (hx : x ∈ p.support) : G.Walk x x :=
  if ho : Odd (p.shortClosed hx).length then
    p.shortClosed hx
  else
  -- In this case we rotate this walk to be able to return a `G.Walk x x` in both cases
    (p.shortCut hx).rotate (by simp)

lemma shorterOdd_rotatedSubwalk {u x : α} {p : G.Walk u u} (hx : x ∈ p.support) :
  (p.shorterOdd hx).IsRotatedSubwalk p := by
  rw [shorterOdd]
  split_ifs with h1
  · exact (shortClosed_infix hx).subwalk.isRotated
  · exact ⟨u, (p.shortCut hx), by simp_all [shortCut_subwalk hx]⟩

lemma darts_shorterOdd_subset {u : α} (p : G.Walk u u) {x : α} (hx : x ∈ p.support) :
    (p.shorterOdd hx).darts ⊆ p.darts := (p.shorterOdd_rotatedSubwalk hx).darts_subset

lemma length_shorterOdd_odd {p : G.Walk u u} {x : α} (hx : x ∈ p.support)
    (ho : Odd p.length) : Odd (p.shorterOdd hx).length := by
  rw [← p.length_shortCut_add_shortClosed hx] at ho
  rw [shorterOdd]
  split_ifs with h1
  · exact h1
  · rw [length_rotate]
    exact (Nat.odd_add.1 ho).2 (Nat.not_odd_iff_even.1 h1)

lemma length_shorterOdd_le {u : α} (p : G.Walk u u) {x : α} (hx : x ∈ p.support) :
    (p.shorterOdd hx).length ≤ p.length := (p.shorterOdd_rotatedSubwalk hx).length_le

lemma length_shorterOdd_lt_length {p : G.Walk u u} {x : α} (hx : x ∈ p.support) (hne : x ≠ u)
    (h2 : 1 < p.support.count x) : (p.shorterOdd hx).length < p.length := by
  rw [shorterOdd]
  split_ifs with ho
  · exact p.length_shortClosed_lt_length hx hne
  · rw [length_rotate]; exact p.length_shortCut_lt_length hx h2

def takeUntilNext {u : α} (p : G.Walk u u) : G.Walk u u :=
  match p with
| nil => nil
| cons h p => (p.takeUntil _ p.end_mem_support).cons h

def dropUntilNext {u : α} (p : G.Walk u u) : G.Walk u u :=
  match p with
| nil => nil
| cons _ p => (p.dropUntil _ p.end_mem_support)

lemma takeNext_spec (p : G.Walk u u) :
    p.takeUntilNext ++ p.dropUntilNext = p := by
  cases p with
  | nil => rfl
  | cons h p =>
    rw [takeUntilNext, dropUntilNext, ← take_spec _ p.end_mem_support]
    simp

lemma takeUntilNext_not_nil_of_count {u : α} {p : G.Walk u u} (h : 2 < p.support.count u) :
    ¬ p.takeUntilNext.Nil := by
  cases p with
  | nil => simp at h
  | cons h p => simp [takeUntilNext]

lemma dropUntilNext_not_nil_of_count {u : α} {p : G.Walk u u} (h2 : 2 < p.support.count u) :
    ¬ p.dropUntilNext.Nil := by
  cases p with
  | nil => simp at h2
  | cons h p =>
    have ht := takeNext_spec (p.cons h)
    intro hf
    rw [nil_iff_eq_nil.mp hf] at ht
    apply_fun List.count u ∘ Walk.support at ht
    simp only [append_nil, Function.comp_apply, support_cons, count_cons_self] at ht h2
    simp [← ht, takeUntilNext] at h2

lemma takeUntilNext_isPrefix {u : α} (p : G.Walk u u) : p.takeUntilNext <+: p := by
  use p.dropUntilNext
  rw [takeNext_spec]

lemma dropUntilNext_isSuffix {u : α} (p : G.Walk u u) : p.dropUntilNext <:+ p := by
  use p.takeUntilNext
  rw [takeNext_spec]

def shorterOddStart {u : α} (p : G.Walk u u) : G.Walk u u :=
  if Odd p.takeUntilNext.length then p.takeUntilNext else p.dropUntilNext

lemma shorterOddStart_infix {u : α} (p : G.Walk u u) : p.shorterOddStart <:+: p := by
  rw [shorterOddStart]
  split_ifs with h
  · exact p.takeUntilNext_isPrefix.infix
  · exact p.dropUntilNext_isSuffix.infix

lemma length_shorterOddStart_odd {p : G.Walk u u} (ho : Odd p.length) :
  Odd p.shorterOddStart.length := by
  rw [← p.takeNext_spec] at ho
  rw [shorterOddStart]
  split_ifs with h1
  · exact h1
  · rw [length_append, add_comm] at ho
    exact (Nat.odd_add.1 ho).2 (Nat.not_odd_iff_even.1 h1)

lemma length_shorterOddStart_lt_length {p : G.Walk u u} (h2 : 2 < p.support.count u) :
    p.shorterOddStart.length < p.length := by
  nth_rw 2 [← takeNext_spec p]
  rw [shorterOddStart, length_append]
  split_ifs with ho
  · simp only [lt_add_iff_pos_right, ← not_nil_iff_lt_length]
    exact dropUntilNext_not_nil_of_count h2
  · simp only [lt_add_iff_pos_left, ← not_nil_iff_lt_length]
    exact takeUntilNext_not_nil_of_count h2

theorem exists_odd_cycle {u : α} {w : G.Walk u u} (ho : Odd w.length) :
    ∃ (x : α) (c : G.Walk x x), c.IsCycle ∧ Odd c.length := by
  cases w with
  | nil => simp at ho
  | cons h c =>
    by_cases h2 : 2 < (cons h c).support.count u
    · have := length_shorterOddStart_lt_length h2
      exact exists_odd_cycle <| length_shorterOddStart_odd ho
    · by_cases h1 : ∃ x, (x ∈ (cons h c).support ∧ x ≠ u ∧ 1 < (cons h c).support.count x)
      · obtain ⟨x, hx, hxu, hx1⟩ := h1
        have := length_shorterOdd_lt_length hx hxu hx1
        exact exists_odd_cycle <| length_shorterOdd_odd hx ho
      · push_neg at h1 h2
        have := isCycle_odd_support_tail_nodup ho <| (support_tail_nodup_iff_count_le _).2 ⟨h2, h1⟩
        use u, c.cons h
  termination_by w.length

/-- TODO: work out why the `cases w` and `termination_by w.length` proof fails here. -/
theorem exists_odd_cycle_subwalk {u : α} {w : G.Walk u u} (ho : Odd w.length) :
    ∃ (x : α) (c : G.Walk x x), c.IsCycle ∧ Odd c.length  ∧ c <+ w := by
  induction hn : w.length using Nat.strong_induction_on generalizing w u with
  | h n ih =>
  cases w with
  | nil => simp at ho
  | cons h c =>
    subst hn
    by_cases h2 : 2 < (cons h c).support.count u
    · have := length_shorterOddStart_lt_length h2
      obtain ⟨x, c', hc1, hc2, hc3⟩:= ih _ this (length_shorterOddStart_odd ho) rfl
      exact ⟨x, c', hc1, hc2, hc3.trans (shorterOddStart_infix _).subwalk⟩
    · by_cases h1 : ∃ x, (x ∈ (cons h c).support ∧ x ≠ u ∧ 1 < (cons h c).support.count x)
      · obtain ⟨x, hx, hxu, hx1⟩ := h1
        by_cases ho1 : Odd ((cons h c).shortClosed hx).length
        · obtain ⟨y, c', hc1, hc2, hc3⟩ := ih _ (length_shortClosed_lt_length hx hxu) ho1 rfl
          exact ⟨y, c', hc1, hc2, hc3.trans (shortClosed_infix hx).subwalk⟩
        · have ho' : Odd ((cons h c).shortCut hx).length := by
            rw [← (cons h c).length_shortCut_add_shortClosed hx] at ho
            exact (Nat.odd_add.1 ho).2 (Nat.not_odd_iff_even.1 ho1)
          obtain ⟨y, c', hc1, hc2, hc3⟩ := ih _ (length_shortCut_lt_length hx hx1) ho' rfl
          exact ⟨y, c', hc1, hc2, hc3.trans <| shortCut_subwalk hx⟩
      · push_neg at h1 h2
        have := isCycle_odd_support_tail_nodup ho <| (support_tail_nodup_iff_count_le _).2 ⟨h2, h1⟩
        use u, c.cons h

-- theorem exists_odd_cycle_subwalk' {u : α} {w : G.Walk u u} (ho : Odd w.length) :
--     ∃ (x : α) (c : G.Walk x x), c.IsCycle ∧ Odd c.length  ∧ c <+ w := by
--   cases w with
--   | nil => simp at ho
--   | cons h c =>
--     by_cases h2 : 2 < (cons h c).support.count u
--     · have := length_shorterOddStart_lt_length h2
--       obtain ⟨x, c', hc1, hc2, hc3⟩:= exists_odd_cycle_subwalk' (length_shorterOddStart_odd ho)
--       exact ⟨x, c', hc1, hc2, hc3.trans (shorterOddStart_infix _).subwalk⟩
--     · by_cases h1 : ∃ x, (x ∈ (cons h c).support ∧ x ≠ u ∧ 1 < (cons h c).support.count x)
--       · obtain ⟨x, hx, hxu, hx1⟩ := h1
--         by_cases ho1 : Odd ((cons h c).shortClosed hx).length
--         ·
--           have := length_shortClosed_lt_length hx hxu
--           obtain ⟨y, c', hc1, hc2, hc3⟩ := exists_odd_cycle_subwalk' ho1
--           exact ⟨y, c', hc1, hc2, hc3.trans (shortClosed_infix hx).subwalk⟩
--         · have ho' : Odd ((cons h c).shortCut hx).length := by
--             rw [← (cons h c).length_shortCut_add_shortClosed hx] at ho
--             exact (Nat.odd_add.1 ho).2 (Nat.not_odd_iff_even.1 ho1)
--           have := length_shortCut_lt_length hx hx1
--           obtain ⟨y, c', hc1, hc2, hc3⟩ := exists_odd_cycle_subwalk' ho'
--           exact ⟨y, c', hc1, hc2, hc3.trans ((shortCut_subwalk hx))⟩
--       · push_neg at h1 h2
--         have := isCycle_odd_support_tail_nodup ho <| (support_tail_nodup_iff_count_le _).2 ⟨h2, h1⟩
--         use u, c.cons h
--    termination_by w.length


end SimpleGraph.Walk
