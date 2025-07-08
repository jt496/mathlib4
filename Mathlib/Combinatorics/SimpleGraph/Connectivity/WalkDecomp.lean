/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/

import Mathlib.Combinatorics.SimpleGraph.Walk

/-!
# Decomposing walks
## Main definitions
- `takeUntil`: The path obtained by taking edges of an existing path until a given vertex.
- `dropUntil`: The path obtained by dropping edges of an existing path until a given vertex.
- `rotate`: Rotate a loop walk such that it is centered at the given vertex.
-/

namespace SimpleGraph.Walk

universe u

variable {V : Type u} {G : SimpleGraph V} {v w u : V}

/-! ### Walk decompositions -/

section WalkDecomp

variable [DecidableEq V]

/-- Given a vertex in the support of a path, give the path up until (and including) that vertex. -/
def takeUntil {v w : V} : ∀ (p : G.Walk v w) (u : V), u ∈ p.support → G.Walk v u
  | nil, u, h => by rw [mem_support_nil_iff.mp h]
  | cons r p, u, h =>
    if hx : v = u then
      hx ▸ Walk.nil
    else
      cons r (takeUntil p u <| by
        cases h
        · exact (hx rfl).elim
        · assumption)

@[simp] theorem takeUntil_nil {u : V} {h} : takeUntil (nil : G.Walk u u) u h = nil := rfl

lemma takeUntil_cons {v' : V} {p : G.Walk v' v} (hwp : w ∈ p.support) (h : u ≠ w)
    (hadj : G.Adj u v') :
    (p.cons hadj).takeUntil w (List.mem_of_mem_tail hwp) = (p.takeUntil w hwp).cons hadj := by
  simp [Walk.takeUntil, h]

@[simp]
lemma takeUntil_start (p : G.Walk u v) :
    p.takeUntil u p.start_mem_support = .nil := by cases p <;> simp [Walk.takeUntil]

@[simp]
lemma nil_takeUntil (p : G.Walk u v) (hwp : w ∈ p.support) :
    (p.takeUntil w hwp).Nil ↔ u = w := by
  refine ⟨?_, fun h => by subst h; simp⟩
  intro hnil
  cases p with
  | nil => exact hnil.eq
  | cons h q =>
    simp only [support_cons, List.mem_cons, false_or] at hwp
    obtain hl | hr := hwp
    · exact hl.symm
    · by_contra! hc
      simp [takeUntil_cons hr hc] at hnil

/-- Given a vertex in the support of a path, give the path from (and including) that vertex to
the end. In other words, drop vertices from the front of a path until (and not including)
that vertex. -/
def dropUntil {v w : V} : ∀ (p : G.Walk v w) (u : V), u ∈ p.support → G.Walk u w
  | nil, u, h => by rw [mem_support_nil_iff.mp h]
  | cons r p, u, h =>
    if hx : v = u then by
      subst u
      exact cons r p
    else dropUntil p u <| by
      cases h
      · exact (hx rfl).elim
      · assumption

@[simp] theorem dropUntil_nil {u : V} {h} : dropUntil (nil : G.Walk u u) u h = nil := rfl

@[simp]
lemma dropUntil_start (p : G.Walk v w) :
    p.dropUntil v p.start_mem_support = p := by cases p <;> simp [Walk.dropUntil]

@[simp]
lemma dropUntil_cons_ne_start {x : V} {h : G.Adj v x} {p : G.Walk x w} (hu : u ∈ (p.cons h).support)
    (hn : u ≠ v) : (p.cons h).dropUntil _ hu = p.dropUntil _ (by aesop)  := by
  simp [dropUntil, Ne.symm hn]

@[simp]
lemma not_nil_dropUntil (p : G.Walk u v) (hwp : w ∈ p.support) (hne : w ≠ v) :
    ¬ (p.dropUntil w hwp).Nil := by
  contrapose! hne
  induction p with
  | nil => exact hne.eq
  | @cons u v x h p ih =>
    rw [dropUntil] at hne
    rw [support_cons, List.mem_cons] at hwp
    by_cases h: u = w
    · rw [dif_pos h] at hne
      exact hne.eq
    · rw [dif_neg h] at hne
      obtain hw1 | hw2 := hwp
      · exact absurd hw1.symm h
      · exact ih hw2 hne

/-- The `takeUntil` and `dropUntil` functions split a walk into two pieces.
The lemma `SimpleGraph.Walk.count_support_takeUntil_eq_one` specifies where this split occurs. -/
@[simp]
theorem take_spec {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).append (p.dropUntil u h) = p := by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    rfl
  · cases h
    · simp!
    · simp! only
      split_ifs with h' <;> subst_vars <;> simp [*]

theorem mem_support_iff_exists_append {V : Type u} {G : SimpleGraph V} {u v w : V}
    {p : G.Walk u v} : w ∈ p.support ↔ ∃ (q : G.Walk u w) (r : G.Walk w v), p = q.append r := by
  classical
  constructor
  · exact fun h => ⟨_, _, (p.take_spec h).symm⟩
  · rintro ⟨q, r, rfl⟩
    simp only [mem_support_append_iff, end_mem_support, start_mem_support, or_self_iff]

@[simp]
theorem count_support_takeUntil_eq_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).support.count u = 1 := by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    simp!
  · cases h
    · simp!
    · simp! only
      split_ifs with h' <;> rw [eq_comm] at h' <;> subst_vars <;> simp! [*, List.count_cons]

theorem count_edges_takeUntil_le_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) (x : V) :
    (p.takeUntil u h).edges.count s(u, x) ≤ 1 := by
  induction p with
  | nil =>
    rw [mem_support_nil_iff] at h
    subst u
    simp!
  | cons ha p' ih =>
    cases h
    · simp!
    · simp! only
      split_ifs with h'
      · subst h'
        simp
      · rw [edges_cons, List.count_cons]
        split_ifs with h''
        · simp only [beq_iff_eq, Sym2.eq, Sym2.rel_iff'] at h''
          obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h''
          · exact (h' rfl).elim
          · cases p' <;> simp!
        · apply ih

@[simp]
theorem takeUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u ∈ (p.copy hv hw).support) :
    (p.copy hv hw).takeUntil u h = (p.takeUntil u (by subst_vars; exact h)).copy hv rfl := by
  subst_vars
  rfl

@[simp]
theorem dropUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u ∈ (p.copy hv hw).support) :
    (p.copy hv hw).dropUntil u h = (p.dropUntil u (by subst_vars; exact h)).copy rfl hw := by
  subst_vars
  rfl

theorem support_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).support ⊆ p.support := fun x hx => by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inl hx

theorem support_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).support ⊆ p.support := fun x hx => by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inr hx

theorem darts_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).darts ⊆ p.darts := fun x hx => by
  rw [← take_spec p h, darts_append, List.mem_append]
  exact Or.inl hx

theorem darts_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).darts ⊆ p.darts := fun x hx => by
  rw [← take_spec p h, darts_append, List.mem_append]
  exact Or.inr hx

theorem edges_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).edges ⊆ p.edges :=
  List.map_subset _ (p.darts_takeUntil_subset h)

theorem edges_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).edges ⊆ p.edges :=
  List.map_subset _ (p.darts_dropUntil_subset h)

theorem length_takeUntil_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).length ≤ p.length := by
  have := congr_arg Walk.length (p.take_spec h)
  rw [length_append] at this
  exact Nat.le.intro this

theorem length_dropUntil_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).length ≤ p.length := by
  have := congr_arg Walk.length (p.take_spec h)
  rw [length_append, add_comm] at this
  exact Nat.le.intro this

lemma getVert_dropUntil {u v : V} {p : G.Walk u v} (n : ℕ) (hw : w ∈ p.support) :
    (p.dropUntil w hw).getVert n = p.getVert (n + (p.takeUntil w hw).length) := by
  nth_rw 2 [← take_spec p hw]
  have ha := getVert_append (p.takeUntil w hw) (p.dropUntil w hw) (n + (p.takeUntil w hw).length)
  rwa [if_neg <| not_lt.2 <| Nat.le_add_left _ _, Nat.add_sub_cancel, Eq.comm] at ha

@[simp]
lemma getVert_length_takeUntil_eq_self {u v x} (p : G.Walk u v) (h : x ∈ p.support) :
    p.getVert (p.takeUntil _ h).length = x := by
  have := congr_arg₂ (y := (p.takeUntil _ h).length) getVert (take_spec p h) rfl
  rwa [getVert_append, if_neg <| lt_irrefl _, Nat.sub_self, getVert_zero, Eq.comm] at this

lemma getVert_takeUntil {u v : V} {n : ℕ} {p : G.Walk u v} (hw : w ∈ p.support)
    (hn : n ≤ (p.takeUntil w hw).length) : (p.takeUntil w hw).getVert n = p.getVert n := by
  cases hn.lt_or_eq with
  | inl h =>
    nth_rw 2 [← take_spec p hw]
    rw [getVert_append, if_pos h]
  | inr h => simp [p.getVert_length_takeUntil_eq_self, h]

lemma snd_takeUntil (p : G.Walk u v) (h : w ∈ p.support) (hn : w ≠ u):
    (p.takeUntil w h).snd = p.snd := by
  apply p.getVert_takeUntil h
  by_contra! hc
  simp only [Nat.lt_one_iff, ← nil_iff_length_eq, nil_takeUntil] at hc
  exact hn hc.symm

@[simp]
lemma length_takeUntil_add_dropUntil {p : G.Walk u v} (h : w ∈ p.support) :
    (p.takeUntil w h).length + (p.dropUntil w h).length = p.length := by
  rw [← length_append, take_spec]

lemma penultimate_dropUntil (p : G.Walk u v) (hw : w ∈ p.support) (hn : w ≠ v) :
    (p.dropUntil w hw).penultimate = p.penultimate := by
  rw [penultimate, getVert_dropUntil]
  congr
  rw [← length_takeUntil_add_dropUntil hw, add_comm, Nat.add_sub_assoc]
  exact not_nil_iff_lt_length.1 <| p.not_nil_dropUntil hw hn

lemma length_takeUntil_lt {u v w : V} {p : G.Walk v w} (h : u ∈ p.support) (huw : u ≠ w) :
    (p.takeUntil u h).length < p.length := by
  rw [(p.length_takeUntil_le h).lt_iff_ne]
  exact fun hl ↦ huw (by simpa using (hl ▸ getVert_takeUntil h (by rfl) :
    (p.takeUntil u h).getVert (p.takeUntil u h).length = p.getVert p.length))

variable {x : V}
lemma takeUntil_append_of_mem_left (p : G.Walk u v) (q : G.Walk v w) (hx : x ∈ p.support) :
    (p.append q).takeUntil x (subset_support_append_left _ _ hx) = p.takeUntil _ hx  := by
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

lemma takeUntil_append_of_mem_right (p : G.Walk u v) (q : G.Walk v w) (hxn : x ∉ p.support)
    (hx : x ∈ q.support) :
    (p.append q).takeUntil x (subset_support_append_right _ _ hx) =
    p.append (q.takeUntil _ hx) := by
  induction p with
  | nil => simp
  | cons _ p ih =>
    simp_rw [cons_append]
    rw [support_cons] at hxn
    rw [takeUntil_cons (subset_support_append_right _ _ hx) (List.ne_of_not_mem_cons hxn).symm]
    simpa using ih _ (List.not_mem_of_not_mem_cons hxn) hx

lemma takeUntil_takeUntil (p : G.Walk u v) (hw : w ∈ p.support)
    (hx : x ∈ (p.takeUntil w hw).support) :
    (p.takeUntil w hw).takeUntil x hx = p.takeUntil x (p.support_takeUntil_subset hw hx) := by
  rw [← takeUntil_append_of_mem_left _ (p.dropUntil w hw) hx]
  simp_rw [take_spec]

--@[simp]
lemma dropUntil_append_of_mem_left (p : G.Walk u v) (q : G.Walk v w) (hx : x ∈ p.support) :
    (p.append q).dropUntil x (subset_support_append_left _ _ hx) = (p.dropUntil x hx).append q := by
  induction p with
  | nil => rw [mem_support_nil_iff] at hx; subst_vars; simp
  | @cons u _ _ _ p ih =>
    rw [support_cons] at hx
    simp_rw [cons_append, dropUntil]
    by_cases hxu : u = x
    · subst_vars; simp
    · simp_rw [dif_neg hxu]
      simpa using ih _ (List.mem_of_ne_of_mem (fun hf ↦ hxu hf.symm) hx)

@[simp]
lemma dropUntil_append_of_mem_right  (p : G.Walk u v) (q : G.Walk v w) (hxn : x ∉ p.support)
    (hx : x ∈ q.support) :
    (p.append q).dropUntil x (subset_support_append_right _ _ hx) = q.dropUntil _ hx := by
  induction p with
  | nil => simp
  | @cons u _ _ _ p ih =>
    simp_rw [cons_append]
    rw [support_cons] at hxn
    rw [dropUntil, dif_neg (List.ne_of_not_mem_cons hxn).symm]
    simpa using ih _ (List.not_mem_of_not_mem_cons hxn) hx

lemma dropUntil_dropUntil (p : G.Walk u v) (hw : w ∈ p.support)
    (hx : x ∈ (p.dropUntil w hw).support) (hxn : x ∉ (p.takeUntil w hw).support) :
    (p.dropUntil w hw).dropUntil x hx = p.dropUntil x (p.support_dropUntil_subset hw hx) := by
  rw [← dropUntil_append_of_mem_right _ _ hxn hx]
  simp_rw [take_spec]

lemma not_mem_support_takeUntil_support_takeUntil_subset {p : G.Walk u v} {w x : V} (h : x ≠ w)
    (hw : w ∈ p.support) (hx : x ∈ (p.takeUntil w hw).support) :
    w ∉ (p.takeUntil x (p.support_takeUntil_subset hw hx)).support := by
  rw [← takeUntil_takeUntil p hw hx]
  intro hw'
  have h1 : (((p.takeUntil w hw).takeUntil x hx).takeUntil w hw').length
      < ((p.takeUntil w hw).takeUntil x hx).length := by
    exact length_takeUntil_lt _ h.symm
  have h2 : ((p.takeUntil w hw).takeUntil x hx).length < (p.takeUntil w hw).length := by
    exact length_takeUntil_lt _ h
  simp only [takeUntil_takeUntil] at h1 h2
  omega

/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) : G.Walk u u :=
  (c.dropUntil u h).append (c.takeUntil u h)

@[simp]
theorem rotate_copy {u v v'} (p : G.Walk v v) (hv : v = v') (h : u ∈ (p.copy hv hv).support) :
    (p.copy hv hv).rotate h = (p.rotate (by simpa using h)) := by
  subst_vars
  rfl

@[simp]
theorem rotate_start {v} (p : G.Walk v v)  : p.rotate (start_mem_support ..) = p := by
  cases p <;> simp [rotate]

@[simp]
theorem rotate_not_nil {u v} {p : G.Walk v v} (hn : ¬ p.Nil) (h : u ∈ p.support) :
    ¬ (p.rotate h).Nil := by
  rw [rotate, nil_append_iff]
  intro hf
  exact hn <| (p.take_spec h) ▸ nil_append_iff.2 hf.symm

@[simp]
theorem support_rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).support.tail ~r c.support.tail := by
  simp only [rotate, tail_support_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← tail_support_append, take_spec]

theorem rotate_darts {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).darts ~r c.darts := by
  simp only [rotate, darts_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← darts_append, take_spec]

theorem rotate_edges {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).edges ~r c.edges :=
  (rotate_darts c h).map _

@[simp]
lemma length_rotate {v : V} {c : G.Walk u u} (h : v ∈ c.support) :
    (c.rotate h).length = c.length := by
  rw [rotate, length_append, add_comm, length_takeUntil_add_dropUntil]

lemma getVert_rotate {n : ℕ} {c : G.Walk v v} (h : w ∈ c.support) (hn : n ≤ c.length) :
    (c.rotate h).getVert n = if (n < (c.dropUntil _ h).length) then
      c.getVert ((n + (c.takeUntil _ h).length)) else c.getVert (n - (c.dropUntil _ h).length) := by
  rw [rotate, getVert_append, getVert_dropUntil, getVert_takeUntil]
  simpa

end WalkDecomp

/-- Given a walk `w` and a node in the support, there exists a natural `n`, such that given node
is the `n`-th node (zero-indexed) in the walk. In addition, `n` is at most the length of the path.
Due to the definition of `getVert` it would otherwise be legal to return a larger `n` for the last
node. -/
theorem mem_support_iff_exists_getVert {u v w : V} {p : G.Walk v w} :
    u ∈ p.support ↔ ∃ n, p.getVert n = u ∧ n ≤ p.length := by
  classical
  constructor
  · intro h
    exact ⟨_, p.getVert_length_takeUntil_eq_self h, p.length_takeUntil_le h⟩
  · intro ⟨_, h⟩
    exact h.1 ▸ (getVert_mem_support _ _)

variable {x : V} {p : G.Walk u v} {n : ℕ}

section withDecEq

variable [DecidableEq V]

lemma takeUntil_of_take (hx : x ∈ (p.take n).support) :
    (p.take n).takeUntil _ hx = (p.takeUntil x ((support_take_subset _ _) hx)) := by
  rw [← takeUntil_append_of_mem_left _ (p.drop n) hx]
  simp_rw [take_append_drop]

lemma length_takeUntil_le_of_mem_take (hx : x ∈ (p.take n).support) :
    (p.takeUntil x ((support_take_subset _ _) hx)).length ≤ n := by
  have := length_takeUntil_le _ hx
  rw [takeUntil_of_take hx] at this
  exact this.trans (length_take_le _ _)

lemma dropUntil_of_drop (hx : x ∈ (p.drop n).support) (hxn : x ∉ (p.take n).support) :
    (p.drop n).dropUntil _ hx = (p.dropUntil x ((support_drop_subset _ _) hx)) := by
  rw [← dropUntil_append_of_mem_right (p.take n) _ hxn hx]
  simp_rw [take_append_drop]

lemma mem_support_rotate_iff  {u v x} {c : G.Walk u u} (h : v ∈ c.support) :
    x ∈ (c.rotate h).support ↔ x ∈ c.support := by
  constructor <;> intro h' <;> rw [support_eq_cons] at h'
  · cases h' with
    | head _ => exact h
    | tail _ hb => exact List.mem_of_mem_tail <| (support_rotate c h).mem_iff.1 hb
  · cases h' with
    | head _ =>
      rw [rotate, support_append]
      exact List.mem_append_left _ <| end_mem_support ..
    | tail _ hb => exact List.mem_of_mem_tail <| (support_rotate c h).mem_iff.2 hb

end withDecEq

lemma mem_support_take {m n : ℕ} (p : G.Walk u v) (h : m ≤ n) :
    p.getVert m ∈ (p.take n).support := by
  rw [← getVert_take_of_le p h]
  exact getVert_mem_support ..

lemma mem_support_take_iff (p : G.Walk u v) (n : ℕ) :
    x ∈ (p.take n).support ↔ ∃ m ≤ n, p.getVert m = x := by
  classical
  constructor <;> intro h
  · exact ⟨_, length_takeUntil_le_of_mem_take h,
      getVert_length_takeUntil_eq_self p (support_take_subset p n h)⟩
  · obtain ⟨m, hm , hx⟩ := h
    exact hx.symm ▸ mem_support_take  _ hm

lemma mem_support_drop {m n : ℕ} (p : G.Walk u v) (hn : m ≤ n) :
    p.getVert n ∈ (p.drop m).support := by
  have : (p.drop m).getVert (n - m) = p.getVert n := by
    rw [getVert_drop, Nat.add_sub_of_le hn]
  exact this.symm ▸ getVert_mem_support ..

lemma mem_support_drop_iff (p : G.Walk u v) (n : ℕ) :
    x ∈ (p.drop n).support ↔ ∃ m, n ≤ m ∧ p.getVert m = x := by
  classical
  constructor <;> intro h
  · rw [← getVert_length_takeUntil_eq_self _ h, getVert_drop]
    exact ⟨_, Nat.le_add_right .., rfl⟩
  · obtain ⟨m, hm , hx⟩ := h
    exact hx.symm ▸ mem_support_drop  _ hm

/-- Given a walk that ends in a set S, there is a first vertex of the walk in the set. -/
lemma getVert_find_first {S : Set V} [DecidablePred (· ∈ S)] (w : G.Walk u v) (h : v ∈ S) :
    ∃ n ≤ w.length, w.getVert n ∈ S ∧ ∀ m < n, w.getVert m ∉ S :=
  have h := w.getVert_length.symm ▸ h
  ⟨_, Nat.find_min' _ h, Nat.find_spec ⟨_, h⟩, fun _ h' ↦ Nat.find_min _ h'⟩


/-- Given a walk that contains the nonempty set S, there is a walk containing the set that starts
from a vertex in the set. -/
lemma exists_getVert_first {S : Set V} (p : G.Walk u v) (hw : w ∈ S )
    (h : ∀ x, x ∈ S → x ∈ p.support) :
    ∃ n, p.getVert n ∈ S ∧ ∀ x, x ∈ S → x ∈ (p.drop n).support := by
  classical
  obtain ⟨n, hn1, hn2, hn3⟩ := getVert_find_first (p.takeUntil _ (h w hw)) hw
  simp_rw [getVert_takeUntil (h w hw) hn1] at *
  use n, hn2
  conv at hn3 =>
    enter [2]; intro h'
    rw [getVert_takeUntil (h w hw) (h'.le.trans hn1)]
  intro x hx
  have := h x hx
  rw [← take_append_drop p n, mem_support_append_iff] at this
  cases this with
  | inl h =>
    obtain ⟨m, h, h1⟩ := (mem_support_take_iff p n).1 h
    cases h.lt_or_eq with
    | inl h => exact ((h1 ▸ hn3 _ h) hx).elim
    | inr h => exact (h ▸ h1).symm ▸ (start_mem_support (p.drop n))
  | inr h => exact h

/-! ## SubWalks -/

variable {V : Type} {G : SimpleGraph V} {x : V}
/-- `p.IsInfixWalk q` means that the walk `p` is a contiguous SubWalk of the walk `q`. -/
def IsInfixWalk {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) : Prop :=
  ∃ (ru : G.Walk u₂ u₁) (rv : G.Walk v₁ v₂), q = (ru.append p).append rv


@[simp]
lemma IsInfixWalk_refl {u₁ v₁} (p : G.Walk u₁ v₁) : p.IsInfixWalk p := by
  use nil, nil; simp

/-- `p.IsPrefixWalk q` means that the walk `q` starts with the walk `p`. -/
def IsPrefixWalk {u v₁ v₂} (p : G.Walk u v₁) (q : G.Walk u v₂) : Prop :=
  ∃ (r : G.Walk v₁ v₂), q = p.append r

@[simp]
lemma IsPrefixWalk_nil {u v} (q : G.Walk u v) : (nil' u).IsPrefixWalk q := by
  use q; simp

lemma IsPrefixWalk_cons' {u₁ u₂ x v₁ v₂} (p : G.Walk x v₁) (q : G.Walk u₂ v₂) (h : G.Adj u₁ x)
    (h' : G.Adj u₁ u₂) (hp : (cons h p).IsPrefixWalk (cons h' q)) : u₂ = x := by
  obtain ⟨r, hr⟩ := hp
  rw [cons_append, cons.injEq] at hr
  exact hr.1

lemma IsPrefixWalk_cons {u₁ u₂ v₁ v₂} (p : G.Walk u₂ v₁) (q : G.Walk u₂ v₂) (h : G.Adj u₁ u₂) :
    (cons h p).IsPrefixWalk (cons h q) ↔ p.IsPrefixWalk q := by
  constructor <;> intro ⟨r, hr⟩ <;> exact ⟨r, by aesop⟩

lemma IsPrefix_iff {u v₁ v₂} (p : G.Walk u v₁) (q : G.Walk u v₂) :
    p.IsPrefixWalk q ↔ p.support <+: q.support := by
  induction p with
  | nil =>
    simp_rw [IsPrefixWalk_nil, support_nil, true_iff]
    rw [support_eq_cons]
    simp
  | @cons _ y _ _ r ih =>
    constructor <;> intro h'
    · cases q with
    | nil =>
      obtain ⟨_, hr'⟩ := h'
      simp at hr'
    | cons h'' q =>
      have := IsPrefixWalk_cons' _ _ _ _ h'
      subst this
      simpa using (ih q).1 <| (IsPrefixWalk_cons _ _ _).1 h'
    · cases q with
    | nil => simp at h'
    | @cons _ b _ h'' p =>
      simp only [support_cons, List.cons_prefix_cons, true_and] at h'
      have : y = b := by
        rw [support_eq_cons, support_eq_cons p, List.cons_prefix_cons] at h'
        exact h'.1
      subst this
      apply (IsPrefixWalk_cons ..).2 <| (ih _).2 h'

/-- `p.IsSuffixWalk q` means that the walk `q` ends with the walk `p`. -/
def IsSuffixWalk {u₁ u₂ v} (p : G.Walk u₂ v) (q : G.Walk u₁ v) : Prop :=
  ∃ (r : G.Walk u₁ u₂), q = r.append p

lemma IsSuffixWalk_iff_reverse_isPrefixWalk {u₁ u₂ v} (p : G.Walk u₂ v) (q : G.Walk u₁ v) :
    p.IsSuffixWalk q ↔ p.reverse.IsPrefixWalk q.reverse := by
  constructor <;> intro ⟨r, hr⟩ <;>
  · apply_fun Walk.reverse at hr
    use r.reverse
    simpa using hr

lemma IsSuffix_iff {u₁ u₂ v} (p : G.Walk u₂ v) (q : G.Walk u₁ v) :
    p.IsSuffixWalk q ↔ p.support <:+ q.support := by
  simp [IsSuffixWalk_iff_reverse_isPrefixWalk, IsPrefix_iff]

lemma IsInfixWalk_iff_exists_isPrefix {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) :
  p.IsInfixWalk q ↔ ∃ r : G.Walk u₂ u₁, (r.append p).IsPrefixWalk q := by
  constructor <;> intro ⟨r, ⟨s, hs⟩⟩ <;>
  · use r, s

lemma IsInfixWalk_iff_exists_isSuffix {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) :
  p.IsInfixWalk q ↔ ∃ s : G.Walk v₁ v₂, (p.append s).IsSuffixWalk q := by
  constructor <;> intro ⟨r, ⟨s, hs⟩⟩ <;>
  · use s, r
    rw [hs, append_assoc]

lemma IsInfixWalk_iff {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) :
    p.IsInfixWalk q ↔ p.support <:+: q.support := by
  constructor
  · intro ⟨r, s, hrs⟩
    have hs : (p.append s).IsSuffixWalk q := ⟨r, by rwa [append_assoc]⟩
    have hs := (IsSuffix_iff _ _).1 hs
    rw [support_append] at hs
    obtain ⟨l, hl⟩ := hs
    use l, s.support.tail
    rwa [← List.append_assoc] at hl
  · induction q with
  | nil =>
    intro h
    rw [support_eq_cons, support_nil, List.infix_cons_iff] at h
    cases h with
    | inl h =>
      rw [List.cons_prefix_cons, List.prefix_nil] at h
      have := h.1
      subst this
      cases p with
      | nil => use nil, nil; simp
      | cons h' p => simp at h
    | inr h => simp at h
  | @cons a _ _ h q ih =>
    intro h'
    rw [support_cons, List.infix_cons_iff] at h'
    cases h' with
    | inl h' =>
      have hpre : p.support <+: (cons h q).support := by simpa
      have heq : u₁ = a := by
        rw [support_eq_cons, support_cons, List.cons_prefix_cons] at hpre
        exact hpre.1
      subst heq
      have := (IsPrefix_iff _ _).2 hpre
      rw [IsInfixWalk_iff_exists_isPrefix]
      use nil
      simpa
    | inr h' =>
      obtain ⟨r, s, hr⟩ := ih h'
      use (cons h r), s
      simpa

lemma List.infix_infix_iff {l k : List V} : l <:+: k ∧ k <:+: l ↔ l = k := by
  constructor
  · intro ⟨h1, h2⟩
    exact h1.eq_of_length_le h2.length_le
  · intro h
    subst h
    exact ⟨List.infix_rfl, List.infix_rfl⟩

lemma IsInfixWalk_isSubWalk {u₁ v₁ u₂ v₂} {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} :
    p.IsInfixWalk q ∧ q.IsInfixWalk p ↔ p.support = q.support := by
  simp_rw [← List.infix_infix_iff, IsInfixWalk_iff]

lemma IsInfixWalk_reverse {u₁ v₁ u₂ v₂} {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} :
    p.IsInfixWalk q ↔ p.reverse.IsInfixWalk q.reverse := by
  constructor <;> intro ⟨r, s, h⟩
  · use s.reverse, r.reverse
    rw [h]
    simp [append_assoc]
  · use s.reverse, r.reverse
    apply_fun Walk.reverse at h
    rw [reverse_reverse] at h
    rw [h]
    simp [append_assoc]


lemma append_cons_eq_concat_append {u v w z} {p : G.Walk u v} {q : G.Walk w z} {h : G.Adj v w} :
    p.append (cons h q) = (p.concat h).append q := by
  induction p with
  | nil => simp [concat_nil]
  | cons h' p ih => simp [ih]

lemma IsInfixWalk_antisymm_iff {u₁ v₁ u₂ v₂} {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} :
    p.IsInfixWalk q ∧ q.IsInfixWalk p ↔ ∃ hu hv, p.copy hu hv = q := by
  constructor
  · intro ⟨h1, h2⟩
    obtain ⟨a, b, hpq⟩ := h1
    obtain ⟨c, d, hqp⟩ := h2
    simp_rw [hpq, append_assoc] at hqp
    apply_fun length at hqp
    simp only [length_append] at hqp
    have han : a.Nil := nil_iff_length_eq.mpr (by omega)
    have hbn : b.Nil := nil_iff_length_eq.mpr (by omega)
    have ha' := han.eq
    have hb' := hbn.eq
    subst ha' hb'
    simp [hpq, han.eq_nil, hbn.eq_nil]
  · rintro ⟨rfl, rfl, rfl⟩
    simp

alias ⟨IsInfixWalk_antisymm, _⟩ := IsInfixWalk_antisymm_iff


/--
If `p₁ ++ p₂ = q₁ ++ q₂` and `p₁.length = q₁.length` then `p₁ = q₁` and `p₂ = q₂`.
-/
lemma append_inj {u u₁ v v₁} {p₁ : G.Walk u u₁} {p₂ : G.Walk u₁ v} {q₁ : G.Walk u v₁}
    {q₂ : G.Walk v₁ v} (hp : p₁.append p₂ = q₁.append q₂) (hl : p₁.length = q₁.length) :
    ∃ h, p₁.copy rfl h = q₁ ∧ p₂.copy h rfl = q₂ := by
  have : u₁ = v₁ := by
    have h1 := getVert_append p₁ p₂ p₁.length
    have h2 := getVert_append q₁ q₂ q₁.length
    simp only [lt_self_iff_false, ↓reduceIte, Nat.sub_self, getVert_zero] at h1 h2
    rwa [← hp, ← hl, h1] at h2
  use this
  subst this
  induction p₁ with
  | nil =>
    rw [length_nil] at hl
    have hq1 := (nil_iff_length_eq.mpr hl.symm).eq_nil
    rw [nil_append, copy_rfl_rfl, hp] at *
    exact ⟨hq1.symm, by simp [hq1]⟩
  | cons h p ih =>
    cases q₁ with
    | nil => simp at hl
    | cons h' q₁' =>
      simp only [cons_append, cons.injEq] at *
      have := hp.1
      subst this
      obtain ⟨_, _, _⟩ := ih (by simpa using hp) (by simpa using hl)
      simp_all

/--
If `p₁ ++ p₂ = q₁ ++ q₂` and `p₂.length = q₂.length` then `p₁ = q₁` and `p₂ = q₂`.
-/
lemma append_inj' {u u₁ v v₁} {p₁ : G.Walk u u₁} {p₂ : G.Walk u₁ v} {q₁ : G.Walk u v₁}
    {q₂ : G.Walk v₁ v} (hp : p₁.append p₂ = q₁.append q₂) (hl : p₂.length = q₂.length) :
    ∃ h, p₁.copy rfl h = q₁ ∧ p₂.copy h rfl = q₂ := by
  apply append_inj hp
  apply_fun length at hp
  simp_rw [length_append] at hp
  omega

lemma append_left_inj {u v₁ v₂} {p₁ p₂: G.Walk u v₁} {q : G.Walk v₁ v₂} :
    p₁.append q = p₂.append q ↔ p₁ = p₂ := by
  constructor <;> intro heq
  · obtain ⟨_, h1, h2⟩ := append_inj heq (by apply_fun length at heq; simpa using heq)
    simp [← h1]
  · subst heq; rfl

lemma append_right_inj {u₁ u₂ v} {p : G.Walk u₁ u₂} {q₁ q₂ : G.Walk u₂ v} :
    p.append q₁ = p.append q₂ ↔ q₁ = q₂ := by
  constructor <;> intro heq
  · obtain ⟨_, h1, h2⟩ := append_inj heq (by simp)
    simp [← h2]
  · subst heq; rfl

lemma cons_eq_cons {u v₁ v₂ w} (p₁ : G.Walk v₁ w) (p₂ : G.Walk v₂ w) (h₁ : G.Adj u v₁)
    (h₂ : G.Adj u v₂) : cons h₁ p₁ = cons h₂ p₂ ↔ ∃ h', p₁.copy h' rfl = p₂ := by
  constructor <;> rintro ⟨rfl, hp⟩ <;> simp_all

inductive SubWalk {V : Type} {G : SimpleGraph V} :
    (x : V × V) × G.Walk x.1 x.2 → (x : V × V) × G.Walk x.1 x.2 → Prop
  /-- The nil walk `u` is a SubWalk of any `u-v` walk. -/
  | nil {u v : V} {q : G.Walk u v} : SubWalk ⟨⟨u, u⟩, (Walk.nil' u)⟩ ⟨⟨u, v⟩, q⟩
  /-- If `p` is a SubWalk of `q`, then it is also a SubWalk of `q.cons h`. -/
  | cons {p q x} (h : G.Adj x q.1.1) : SubWalk p q → SubWalk p ⟨⟨x, q.1.2⟩, q.2.cons h⟩
  /-- If `p` is a SubWalk of `q`, then `p.cons hp` is a SubWalk of `q.cons hq`, provided `hp` and
  `hq` are both `G.Adj x *` for some vertex x. -/
  | cons₂ {p q x} (hp : G.Adj x p.1.1) (hq : G.Adj x q.1.1) :
      SubWalk p q → SubWalk ⟨⟨x, p.1.2⟩, p.2.cons hp⟩ ⟨⟨x, q.1.2⟩, q.2.cons hq⟩

@[refl]
lemma SubWalk_refl {u v : V} {p : G.Walk u v} : SubWalk ⟨⟨u,v⟩,p⟩ ⟨⟨u,v⟩,p⟩ := by
  induction p with
  | nil => exact SubWalk.nil
  | cons h _ ih => exact SubWalk.cons₂ h h ih

@[simp]
lemma SubWalk_nil_iff {u v x : V} {q : G.Walk u v} :
    SubWalk ⟨⟨u, v⟩, q⟩ ⟨⟨x, x⟩, nil⟩ ↔ q.Nil ∧ u = x ∧ v = x := by
  constructor
  · intro h
    cases q with
    | nil =>
      simp_all only [nil_nil, and_self, true_and]
      cases h with
      | nil => rfl
    | cons _ _ => cases h
  · rintro ⟨hn, rfl, rfl⟩
    have := nil_iff_eq_nil.1 hn
    subst this
    rfl

@[simp]
lemma nil_subWalk {u v x : V} {q : G.Walk u v} (hx : x ∈ q.support) :
  SubWalk ⟨⟨x, x⟩, nil⟩ ⟨⟨u, v⟩, q⟩ := by
  induction q with
  | nil => simp_all
  | cons _ _ ih =>
    simp_all only [support_cons, List.mem_cons]
    obtain (rfl | hx) := hx
    · exact SubWalk.nil
    · exact SubWalk.cons _ (ih hx)

@[simp]
lemma nil_subWalk_iff {u v x : V} {q : G.Walk u v} :
    SubWalk ⟨⟨x, x⟩, nil⟩ ⟨⟨u, v⟩, q⟩ ↔ x ∈ q.support := by
  constructor <;> intro h
  · induction q <;> cases h <;> simp_all
  · simp [h]

@[simp]
lemma SubWalk_cons {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : SubWalk ⟨(u, v), p⟩ ⟨(x, y), q⟩) (h : G.Adj z x) :
    SubWalk ⟨⟨u, v⟩, p⟩ ⟨⟨z,y⟩, q.cons h⟩ := SubWalk.cons h hs

@[simp]
lemma SubWalk_cons₂ {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : SubWalk ⟨⟨u, v⟩, p⟩ ⟨⟨x,y⟩, q⟩) (hp : G.Adj z u) (hq : G.Adj z x) :
    SubWalk ⟨⟨z, v⟩, p.cons hp⟩ ⟨⟨z, y⟩, q.cons hq⟩ :=
  SubWalk.cons₂ hp hq hs

@[simp]
lemma mem_support_of_subWalk'  {z : V} {p q : (x : V × V) × G.Walk x.1 x.2} (hs : SubWalk p q)
  (hz : z ∈ p.2.support) : z ∈ q.2.support := by
  apply SubWalk.rec
    (motive := fun p q _ ↦ (∀ {z}, z ∈ p.2.support → z ∈ q.2.support)) _ _ _ hs hz
      <;> simp_all

/-- If `p <+ q` then `p.support <+ q.support` -/
@[simp]
lemma support_subList_of_subWalk'  {p q : (x : V × V) × G.Walk x.1 x.2} (hs : SubWalk p q) :
  p.2.support.Sublist q.2.support := SubWalk.rec
    (motive := fun p q hpq ↦ p.2.support.Sublist q.2.support) (by simp) (by simp_all) (by simp) hs

lemma support_subList_of_subWalk {u v x y  : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : SubWalk ⟨(u, v), p⟩ ⟨(x, y), q⟩) : p.support.Sublist q.support :=
  support_subList_of_subWalk' hs 

-- lemma mem_support_of_subWalk  {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
--     (hs : SubWalk ⟨(u, v), p⟩ ⟨(x, y), q⟩) (hz : z ∈ p.support) : z ∈ q.support :=
--   mem_support_of_subWalk' hs (by simpa)

/-- If `p <+ q` then `r ++ p <+ q` -/
@[simp]
lemma SubWalk_append_left {u v x y s : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : SubWalk ⟨⟨u, v⟩, p⟩ ⟨⟨x, y⟩, q⟩) (r : G.Walk s x) :
    SubWalk ⟨⟨u, v⟩, p⟩ ⟨⟨s, y⟩, r.append q⟩ := by
  induction r <;> simp_all

/-- If `z :: p <+ q` then `p <+ q` -/
@[simp]
lemma SubWalk_of_cons {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (h : G.Adj z u) (hs : SubWalk ⟨⟨z, v⟩, p.cons h⟩ ⟨⟨x, y⟩, q⟩) :
    SubWalk ⟨⟨u, v⟩, p⟩ ⟨⟨x, y⟩, q⟩ := by
  induction q <;> cases hs <;> simp_all

/-- If `z :: p <+ t :: q` and `z ≠ t` then `z :: p <+ q` -/
@[simp]
lemma SubWalk_of_cons₂_of_ne {u v x y z t : V} {p : G.Walk u v} {q : G.Walk x y}
    (hp : G.Adj z u) (hq : G.Adj t x) (hs : SubWalk ⟨⟨z, v⟩, p.cons hp⟩ ⟨⟨t, y⟩, q.cons hq⟩)
    (hne : z ≠ t) : SubWalk ⟨⟨z, v⟩, p.cons hp⟩ ⟨⟨x, y⟩, q⟩ := by
  cases hs <;> trivial


/-- If `z :: p <+ t :: q` and `z ≠ t` then `z :: p <+ q` -/
@[simp]
lemma SubWalk_of_cons₂_of_ne' {u v x y z t : V} {p : G.Walk u v} {q : G.Walk x y}
    (hp : G.Adj z u) (hq : G.Adj z x) (hs : SubWalk ⟨⟨z, v⟩, p.cons hp⟩ ⟨⟨z, y⟩, q.cons hq⟩)
    (hne : u ≠ x) : SubWalk ⟨⟨z, v⟩, p.cons hp⟩ ⟨⟨x, y⟩, q⟩ := by
  cases hs with
  | cons h _ => simp_all
  | @cons₂ p q w hp hq hs =>
    simp_all
    cases hs with
    | nil => simp_all
    | @cons _ q s  h' hs =>
      simp_all

      have := SubWalk.cons h' hs
      have := @SubWalk.cons₂ V G p ⟨⟨s,q.1.2⟩, q.2.cons h'⟩ z hp hq this
      dsimp at this
  --    apply SubWalk_of_cons₂_of_ne _ _ _ hq.ne
      sorry
    | cons₂ hp hq _ => simp_all


/-- If `p <+ q` then `p <+ q ++ [z]` -/
@[simp]
lemma SubWalk_concat {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : SubWalk ⟨⟨u, v⟩, p⟩ ⟨⟨x, y⟩, q⟩) (h : G.Adj y z) :
    SubWalk ⟨⟨u, v⟩, p⟩ ⟨⟨x, z⟩, q.concat h⟩ := by
  induction q generalizing u v <;> cases hs <;> simp_all

/-- If `p <+ q` then `p ++ [z] <+ q ++ [z]` -/
@[simp]
lemma SubWalk_concat₂ {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : SubWalk ⟨⟨u, v⟩, p⟩ ⟨⟨x, y⟩, q⟩) (hp : G.Adj v z) (hq : G.Adj y z) :
    SubWalk ⟨⟨u, z⟩, p.concat hp⟩ ⟨⟨x, z⟩, q.concat hq⟩ := by
  induction q generalizing u v <;> cases hs <;> simp_all [concat_eq_append]

/-- If `p ++ [z] <+ q ++ [t]` and `z ≠ t` then `p ++ [z] <+ q` -/
--@[simp]
lemma SubWalk_of_concat₂_of_ne {u v x y z t : V} {p : G.Walk u v} {q : G.Walk x y}
    (hp : G.Adj v z) (hq : G.Adj y t) (h : SubWalk ⟨⟨u, z⟩, p.concat hp⟩ ⟨⟨x, t⟩, q.concat hq⟩)
    (hne : z ≠ t) : SubWalk ⟨⟨u, z⟩, p.concat hp⟩ ⟨⟨x, y⟩, q⟩ :=
  sorry

/-- If `p <+ q` then `p <+ q ++ r` -/
@[simp]
lemma SubWalk_append_right {u v x y s : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : SubWalk ⟨⟨u, v⟩, p⟩ ⟨⟨x, y⟩, q⟩) (r : G.Walk y s) :
    SubWalk ⟨⟨u, v⟩, p⟩ ⟨⟨x, s⟩, q.append r⟩ := by
  induction r <;> simp_all [append_cons_eq_concat_append]

@[simp]
lemma SubWalk_trans {u v x y s t : V} {p : G.Walk u v} {q : G.Walk x y} {r : G.Walk s t}
    (hpq : SubWalk ⟨⟨u, v⟩, p⟩ ⟨⟨x, y⟩, q⟩) (hqr : SubWalk ⟨⟨x, y⟩, q⟩ ⟨⟨s, t⟩, r⟩) :
    SubWalk ⟨⟨u, v⟩, p⟩ ⟨⟨s, t⟩, r⟩ := by
  cases hpq with
  | nil =>
    cases hqr with
    | nil => simp_all
    | @cons a q' h h' hs =>
      simp_all; right; sorry
    | cons₂ hp hq _ => sorry
  | cons h _ => sorry
  | cons₂ hp hq _ => sorry






lemma SubWalk_reverse {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : SubWalk ⟨⟨u, v⟩,p⟩ ⟨⟨x, y⟩,q⟩) : SubWalk ⟨⟨v, u⟩, p.reverse⟩ ⟨⟨y, x⟩, q.reverse⟩ := by
  induction q generalizing p u v with
  | nil => simp_all
  | @cons a b c h q ih =>
    rw [reverse_cons, append_cons_eq_concat_append, append_nil]
    by_cases ha : u = a
    · subst ha
      cases p with
      | nil => simp_all
      | @cons _ w _ h' p =>
      simp_all [reverse_cons, append_cons_eq_concat_append, append_nil]

      sorry
    · have : SubWalk ⟨⟨u, v⟩, p⟩ ⟨⟨b, c⟩, q⟩ := by
        cases p with
        | nil => simp_all
        | cons h' p => exact SubWalk_of_cons₂_of_ne h' h hs ha
      exact SubWalk_concat (ih this) _



end SimpleGraph.Walk
