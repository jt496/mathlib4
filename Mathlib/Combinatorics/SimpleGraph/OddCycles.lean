/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Subwalk
/-! # Walk decompositions and odd cycles
We extend the walk decomposition API. Our main aim here is to prove that if `w` is a closed odd
length walk then it contains an odd cycle as a subwalk `exists_odd_cycle_subwalk`.

Given a walk `w : G.Walk u v`: we already have `takeUntil` and `dropUntil`
which satisfy `(w.takeUntil _ hx) ++ (w.dropUntil _ hx) = w`, where `w.takeUntil _ hx` is the part
of `w` from its start to the first occurence of `x` (given `hx : x ∈ w.support`).

For `w : G.Walk u v` and `x ∈ w.support` we define two new walks, `w.shortCut hx` and
  `w.shortClosed`: `w.shortCut hx` is the part of `w` from the start `u` to the first occurence of
  `x` and then from the last occurence of `x` in `w` to `v`, while `w.shortClosed hx` is the closed
  walk that travels along `w` from the first occurence of `x` to the last occurence of `x`.

So `w.shortCut hx : G.Walk u v` is `(w.takeUntil _ hx) ++ (w.reverse.takeUntil _ hx).reverse`
and `w.shortClosed hx : G.Walk x x` is `((w.dropUntil _ hx).reverse.dropUntil _ hx).reverse`.

Note `w.shortClosed` is a closed contiguous (infix) subwalk of `w` while `w.shortCut` is a not
necessarily contiguous subwalk of `w`.

If `w` is a closed walk (i.e. `u = v`) then both `shortCut` and `shortClosed` are closed walks.

We also introduce another way to decompose a closed walk `w : G.Walk u u` into two walks
`takeUntilNext` and `dropUntilNext`, where
`w.takeUntilNext` is the prefix of `w` from its start to the next occurence of `u`.
`w.dropUntilNext` is the suffix of `w` from the second occurence of `u` to its end.

Given a closed walk `w : G.Walk u u` we now have two ways to split `w` into two closed
walks.

If `Odd w.length` then in each case one of the pair of new closed walks will also be odd. Moreover:

(1) If `x ≠ u` and `x` occurs more than once in `w.support` then both `w.shortCut hx` and
    `w.shortClosed hx` are not `Nil` and so whichever of these has odd length is a strictly
    shorter odd closed subwalk of `w`.
(2) If `u` (the starting vertex of `w`) occurs more than twice in `w.support` then both
    `w.takeUntilNext` and `w.dropUntilNext` are not `Nil` and so whichever of these has odd length
    is a strictly shorter odd closed walk.

Hence if `w : G.Walk u u` is an odd closed walk in which either some vertex `x ≠ u` occurs twice
or `u` occurs more than twice then we can find a shorter odd closed walk.

For an odd closed walk `w : G.Walk u u` the condition
  `w.support.count u ≤ 2` and `∀ x, x ≠ u → w.support.count x ≤ 1` is equivalent to being a cycle.

Hence we can use these to prove `exists_odd_cycle_subwalk`: given `w` a closed odd walk there is a
subwalk of `w` that is an odd cycle.

TODO: what should we do for even closed walks? (There is no guarantee of any cycles but perhaps the
walk decomposition API developed here could still be useful.)
-/
namespace SimpleGraph.Walk
open Walk List
variable {α : Type*} {u v x y z : α} {G : SimpleGraph α}

theorem support_eq_concat (p : G.Walk u v) : p.support = p.support.dropLast ++ [v] := by
  cases p with
  | nil => rfl
  | cons h p =>
    obtain ⟨x, q, h',h2⟩ := exists_cons_eq_concat h p
    simp [h2]

lemma mem_support_reverse (p : G.Walk u v) : x ∈ p.reverse.support ↔ x ∈ p.support := by simp [*]

lemma IsPath.length_one_of_end_start_mem_edges {w : G.Walk u v} (hp : w.IsPath)
    (h1 : s(v, u) ∈ w.edges) : w.length = 1 := by
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
lemma isCycle_or_nil_or_length_two_of_support_tail_nodup (w : G.Walk u u)
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
      rw [support_cons, List.tail_cons] at hn
      simpa using (IsPath.mk' hn).length_one_of_end_start_mem_edges hf
    cases w with
    | nil => simp
    | cons h w =>
      rw [support_cons, List.tail_cons] at hn
      apply nodup_cons.2 ⟨by aesop, edges_nodup_of_support_nodup hn⟩

lemma isCycle_odd_support_tail_nodup {w : G.Walk u u} (ho : Odd w.length)
    (hn : w.support.tail.Nodup) : w.IsCycle := by
  apply (w.isCycle_or_nil_or_length_two_of_support_tail_nodup hn).resolve_right
  rintro (hf | hf)
  · rw [nil_iff_length_eq.mp hf] at ho
    exact (Nat.not_odd_zero ho).elim
  · rw [hf] at ho
    exact (Nat.not_odd_iff_even.2 (by decide) ho).elim

variable [DecidableEq α]

lemma not_nil_of_one_lt_count {p : G.Walk u v} (x : α) (h : 1 < p.support.count x) : ¬ p.Nil := by
  contrapose! h
  have := h.eq
  subst this
  rw [h.eq_nil, support_nil]
  convert List.count_le_length

@[simp]
lemma length_takeUntil_add_dropUntil {p : G.Walk u v} (hx : x ∈ p.support) :
    (p.takeUntil x hx).length + (p.dropUntil x hx).length = p.length := by
  rw [← length_append, take_spec]

lemma takeUntil_append_of_mem_left (p : G.Walk u v) (q : G.Walk v z) (hx : x ∈ p.support) :
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

lemma support_tail_nodup_iff_count_le (w : G.Walk u v) : w.support.tail.Nodup ↔
    w.support.count u ≤ 2 ∧ ∀ x ∈ w.support, u ≠ x → count x w.support ≤ 1 := by
  have : w.support.tail.count u + 1 = w.support.count u  := by
    nth_rw 2 [support_eq_cons]
    simp
  simp only [List.nodup_iff_count_le_one, ← this, Nat.reduceLeDiff, ne_eq]
  constructor
  · intro h
    exact ⟨h u, fun x _ h' ↦ by rw [support_eq_cons, count_cons_of_ne h']; exact h x⟩
  · intro ⟨hu, h⟩ a
    by_cases hau : u = a
    · subst hau; trivial
    · by_cases ha : a ∈ u :: w.support.tail
      · have := (w.support_eq_cons ▸ h) a ha hau
        rwa [count_cons_of_ne hau] at this
      · exact (count_eq_zero_of_not_mem <| not_mem_of_not_mem_cons ha).le.trans zero_le_one

/-- Given a vertex `x` in a walk `w` form the walk that travels along `w` from the first visit of
`x` to the last visit of `x` (which may be the same in which case this is `nil' x`) -/
def shortClosed (w : G.Walk u v) (hx : x ∈ w.support) : G.Walk x x :=
  ((w.dropUntil _ hx).reverse.dropUntil _ (by simp)).reverse

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

lemma shortClosed_infix {p : G.Walk u v} (hx : x ∈ p.support) : Infix (p.shortClosed hx) p := by
  use p.takeUntil _ hx, (p.reverse.takeUntil _ (p.mem_support_reverse.2 hx)).reverse
  have := (take_shortClosed_reverse_spec p hx).symm
  rwa [← append_assoc]

lemma shortClosed_count_le (w : G.Walk u v) (hx : x ∈ w.support) :
    (w.shortClosed hx).support.count y ≤ w.support.count y :=
  (shortClosed_infix hx).subwalk.count_le _

/-- Given a vertex `x` in a walk `w : G.Walk u v` form the walk that travels along `w` from `u`
to `x` and then back to `v` without revisiting `x` -/
def shortCut (w : G.Walk u v) (hx : x ∈ w.support) : G.Walk u v :=
  (w.takeUntil _ hx) ++ (w.reverse.takeUntil _ (w.mem_support_reverse.2 hx)).reverse

lemma shortCut_subwalk {p : G.Walk u v} (hx : x ∈ p.support) : (p.shortCut hx) <+ p := by
  have := (take_shortClosed_reverse_spec p hx).symm
  convert Subwalk.of_prefix_append_suffix

lemma shortCut_not_nil (w : G.Walk u v) (hx : x ∈ w.support) (hu : u ≠ x) :
    ¬ (w.shortCut hx).Nil := by
  rw [shortCut]
  simp only [nil_append_iff, nil_takeUntil, nil_reverse, not_and]
  rintro rfl; contradiction

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

lemma length_shortClosed_lt_length {p : G.Walk u u} (hx : x ∈ p.support) (hne : u ≠ x) :
    (p.shortClosed hx).length < p.length := by
  rw [ ← p.length_shortCut_add_shortClosed hx, lt_add_iff_pos_left, ← not_nil_iff_lt_length]
  exact p.shortCut_not_nil hx hne

lemma length_shortCut_lt_length {p : G.Walk u u} (hx : x ∈ p.support)
    (h2 : 1 < p.support.count x) : (p.shortCut hx).length < p.length := by
  rw [ ← p.length_shortCut_add_shortClosed hx, lt_add_iff_pos_right, ← not_nil_iff_lt_length]
  exact p.shortClosed_not_nil_of_one_lt_count hx h2

/-- The walk in `w : G.Walk u u` from the start to the next occurence of `u` -/
def takeUntilNext {u : α} (p : G.Walk u u) : G.Walk u u :=
  match p with
| nil => nil
| cons h p => (p.takeUntil _ p.end_mem_support).cons h

/-- The walk in `w : G.Walk u u` from the second occurence of `u` to the end -/
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

lemma takeUntilNext_not_nil_of_not_nil {p : G.Walk u u} (h : ¬ p.Nil) : ¬ p.takeUntilNext.Nil := by
  cases p with
  | nil => simp at h
  | cons h p => simp [takeUntilNext]

lemma dropUntilNext_not_nil_of_two_lt_count {p : G.Walk u u} (h2 : 2 < p.support.count u) :
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

lemma takeUntilNext_isPrefix (p : G.Walk u u) : p.takeUntilNext <+: p := by
  use p.dropUntilNext
  rw [takeNext_spec]

lemma dropUntilNext_isSuffix (p : G.Walk u u) : p.dropUntilNext <:+ p := by
  use p.takeUntilNext
  rw [takeNext_spec]

def shorterOdd {u : α} (p : G.Walk u u) : G.Walk u u :=
  if Odd p.takeUntilNext.length then p.takeUntilNext else p.dropUntilNext

lemma shorterOdd_infix (p : G.Walk u u) : p.shorterOdd <:+: p := by
  rw [shorterOdd]
  split_ifs with h
  · exact p.takeUntilNext_isPrefix.infix
  · exact p.dropUntilNext_isSuffix.infix

lemma length_shorterOdd_odd {p : G.Walk u u} (ho : Odd p.length) :
    Odd p.shorterOdd.length := by
  rw [← p.takeNext_spec] at ho
  rw [shorterOdd]
  split_ifs with h1
  · exact h1
  · rw [length_append, add_comm] at ho
    exact (Nat.odd_add.1 ho).2 (Nat.not_odd_iff_even.1 h1)

lemma length_shorterOdd_lt_length {p : G.Walk u u} (h2 : 2 < p.support.count u) :
    p.shorterOdd.length < p.length := by
  nth_rw 2 [← takeNext_spec p]
  rw [shorterOdd, length_append]
  split_ifs with ho
  · simp only [lt_add_iff_pos_right, ← not_nil_iff_lt_length]
    exact dropUntilNext_not_nil_of_two_lt_count h2
  · simp only [lt_add_iff_pos_left, ← not_nil_iff_lt_length]
    exact takeUntilNext_not_nil_of_not_nil (not_nil_of_one_lt_count u (by omega) )

/--
If `G` contains a closed odd walk `w` then there is an odd cycle `c` that is a subwalk of `w`
-/
theorem exists_odd_cycle_subwalk {u : α} {w : G.Walk u u} (ho : Odd w.length) :
    ∃ (x : α) (c : G.Walk x x), c.IsCycle ∧ Odd c.length  ∧ c <+ w := by
  by_cases h2 : 2 < w.support.count u
  · have := length_shorterOdd_lt_length h2
    obtain ⟨x, c', hc1, hc2, hc3⟩:= exists_odd_cycle_subwalk (length_shorterOdd_odd ho)
    exact ⟨x, c', hc1, hc2, hc3.trans (shorterOdd_infix _).subwalk⟩
  · by_cases h1 : ∃ x, (x ∈ w.support ∧ u ≠ x ∧ 1 < w.support.count x)
    · obtain ⟨x, hx, hxu, hx1⟩ := h1
      by_cases ho1 : Odd (w.shortClosed hx).length
      · have := length_shortClosed_lt_length hx hxu
        obtain ⟨y, c', hc1, hc2, hc3⟩ := exists_odd_cycle_subwalk ho1
        exact ⟨y, c', hc1, hc2, hc3.trans (shortClosed_infix hx).subwalk⟩
      · have ho' : Odd (w.shortCut hx).length := by
          rw [← w.length_shortCut_add_shortClosed hx] at ho
          exact (Nat.odd_add.1 ho).2 (Nat.not_odd_iff_even.1 ho1)
        have := length_shortCut_lt_length hx hx1
        obtain ⟨y, c', hc1, hc2, hc3⟩ := exists_odd_cycle_subwalk ho'
        exact ⟨y, c', hc1, hc2, hc3.trans (shortCut_subwalk hx)⟩
    · push_neg at h1 h2
      have := isCycle_odd_support_tail_nodup ho <| (support_tail_nodup_iff_count_le _).2 ⟨h2, h1⟩
      use u, w
  termination_by w.length

end SimpleGraph.Walk
