import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Mathlib.Combinatorics.SimpleGraph.Paths

namespace SimpleGraph.Walk

/-! ## Subwalks -/

/-- `p.Subwalk q` if `p` is a (not necessarily contiguous) subwalk of `q`
(This definition is modelled on `List.Sublist`.) -/
inductive Subwalk {V : Type*} {G : SimpleGraph V} :
    ∀ {u v x y}, G.Walk u v → G.Walk x y → Prop
  /-- The nil walk `u` is a Subwalk of any `u - v` walk. -/
  | nil {u v : V} {q : G.Walk u v} : (Walk.nil' u).Subwalk q
  /-- If `p` is a Subwalk of `q`, then it is also a Subwalk of `q.cons h`. -/
  | cons {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y} (h : G.Adj z x) :
      p.Subwalk q → p.Subwalk (q.cons h)
  /-- If `p` is a Subwalk of `q`, then `p.cons h` is a Subwalk of `q.cons h`. -/
  | cons₂ {u v y z : V} {p : G.Walk u v} {q : G.Walk u y} (h : G.Adj z u) :
      p.Subwalk q → (p.cons h).Subwalk (q.cons h)

variable {V : Type*} {u v w x y z a u₁ u₂ u₃ v₁ v₂ v₃ : V} {G : SimpleGraph V}

attribute [simp] Subwalk.nil Subwalk.cons Subwalk.cons₂

open scoped List

/-- The support of a Subwalk is a Sublist of the support -/
lemma Subwalk.support_sublist {p : G.Walk u v} {q : G.Walk x y} (hs : p.Subwalk q) :
    p.support <+ q.support := by induction hs <;> simp_all

/-- The darts of a Subwalk are a Sublist of the darts -/
lemma Subwalk.darts_sublist {p : G.Walk u v} {q : G.Walk x y} (hs : p.Subwalk q) :
    p.darts <+ q.darts := by induction hs <;> simp_all

/-- The edges of a Subwalk are a Sublist of the edges -/
lemma Subwalk.edges_sublist {p : G.Walk u v} {q : G.Walk x y} (hs : p.Subwalk q) :
    p.edges <+ q.edges := by induction hs <;> simp_all

lemma Subwalk.length_le {p : G.Walk u v} {q : G.Walk x y} (hs : p.Subwalk q) :
    p.length ≤ q.length := Nat.le_of_succ_le_succ <|
  Subwalk.rec (by simp) (by intros; rw [length_cons]; omega) (by simp) hs

lemma Subwalk.count_le [DecidableEq V] {p : G.Walk u v} {q : G.Walk x y} (z : V)
    (hs : p.Subwalk q) : p.support.count z ≤ q.support.count z := hs.support_sublist.count_le _

/-- Any Subwalk of a trail is a trail -/
lemma IsTrail.of_subwalk {p : G.Walk u v} {q : G.Walk x y} (h : p.Subwalk q) (ht : q.IsTrail) :
    p.IsTrail := IsTrail.mk <| h.edges_sublist.nodup ht.edges_nodup

/-- Any non-nil closed Subwalk of a trail is a circuit -/
lemma IsCircuit.of_subwalk {p : G.Walk u u} {q : G.Walk x y} (h : p.Subwalk q) (hn : ¬ p.Nil)
    (ht : q.IsTrail) : p.IsCircuit := IsCircuit.mk (ht.of_subwalk h) (fun _ ↦ hn (by simp_all))

/-- Any Subwalk of a path is a path -/
lemma IsPath.of_subwalk {p : G.Walk u v} {q : G.Walk x y} (h : p.Subwalk q) (ht : q.IsPath) :
    p.IsPath := IsPath.mk' <| h.support_sublist.nodup ht.support_nodup

/-- `p <+ p` -/
@[refl, simp]
lemma Subwalk.refl (p : G.Walk u v) : p.Subwalk p  := by
  induction p with
  | nil => exact .nil
  | cons h _ ih => exact ih.cons₂ h

lemma subwalk_nil_iff {q : G.Walk u v} : q.Subwalk (nil' x) ↔ q.Nil ∧ u = x ∧ v = x := by
  constructor
  · intro h
    cases h; simp
  · rintro ⟨hn, rfl, rfl⟩
    simp_all [nil_iff_eq_nil.1 hn]

@[simp]
lemma not_cons_subwalk_nil {p : G.Walk u v} {h : G.Adj x u} : ¬ (p.cons h).Subwalk (nil' y) := nofun

lemma nil_subwalk {q : G.Walk u v} (hx : x ∈ q.support) : (nil' x).Subwalk q := by
  induction q with
  | nil => simp_all [subwalk_nil_iff]
  | cons _ _ ih =>
    rw [support_cons, List.mem_cons] at *
    obtain (rfl | hx) := hx
    · exact .nil
    · exact (ih hx).cons _

@[simp]
lemma nil_subwalk_iff {q : G.Walk u v} : (nil' x).Subwalk  q ↔ x ∈ q.support := by
  constructor <;> intro h
  · induction q <;> cases h <;> simp_all
  · simp [nil_subwalk, h]

/-- If `p <+ q` then `r ++ p <+ q` -/
lemma Subwalk.append_left {p : G.Walk u v} {q : G.Walk x y} (hs : p.Subwalk q)
    (r : G.Walk z x) : p.Subwalk (r.append q) := by induction r <;> simp_all

/-- If `z :: p <+ q` then `p <+ q` -/
@[simp]
lemma Subwalk.of_cons {p : G.Walk u v} {q : G.Walk x y} (h : G.Adj z u)
    (hs : (p.cons h).Subwalk q) : p.Subwalk q := by induction q <;> cases hs <;> simp_all

/--
If `p <+ q.cons h` where `p : G.Walk u v`, `h : G.Adj a x` and `u ≠ a` then `p <+ q`
-/
@[simp]
lemma Subwalk.of_cons_of_ne {p : G.Walk u v} {q : G.Walk x y} (hq : G.Adj a x)
    (hs : p.Subwalk (q.cons hq)) (hne : u ≠ a) : p.Subwalk q := by
  induction q <;> cases hs <;> simp_all

/--
If `p.cons hp <+ q.cons hq` and `hp, hq` are darts to distinct vertices then `p.cons h <+ q`
-/
@[simp]
lemma Subwalk.of_cons₂_of_ne {p : G.Walk u v} {q : G.Walk x y} (hp : G.Adj z u) (hq : G.Adj z x)
    (hs : (p.cons hp).Subwalk (q.cons hq)) (hne : u ≠ x) : (p.cons hp).Subwalk q := by
  cases hs <;> simp_all

/--
If `p.cons h <+ q.cons h` then `p <+ q`
-/
@[simp]
lemma Subwalk.of_cons₂ {p : G.Walk u v} {q : G.Walk u y} (hz : G.Adj z u)
    (hs : (p.cons hz).Subwalk (q.cons hz)) : p.Subwalk q := by
  cases p with
  | nil => simp
  | cons h p => exact (hs.of_cons _).of_cons_of_ne _ hz.ne.symm

/-- If `r ++ p <+ r ++ q` then `p <+ q` -/
@[simp]
lemma Subwalk.of_append_left {p : G.Walk u v} {q : G.Walk u y} (r : G.Walk x u)
    (hs : (r.append p).Subwalk (r.append q)) : p.Subwalk q := by
  induction r with
  | nil => simpa
  | cons h p ih => exact ih <| hs.of_cons₂ _

/-- If `p <+ q` then `p <+ q.concat h` -/
@[simp]
lemma Subwalk.concat {p : G.Walk u v} {q : G.Walk x y} (hs : p.Subwalk q) (h : G.Adj y z) :
    p.Subwalk (q.concat h) := by
  induction q generalizing u v <;> cases hs <;> simp_all

/-- If `p <+ q` then `p.concat h <+ q.concat h` -/
@[simp]
lemma Subwalk.concat₂ {p : G.Walk u v} {q : G.Walk x v} (hs : p.Subwalk q) (h : G.Adj v z) :
    (p.concat h).Subwalk (q.concat h) := by
  induction q generalizing u with
  | nil => cases hs; simp_all [concat_eq_append]
  | cons h' _ ih =>
    cases hs with
    | nil => exact (ih (by simp) h).cons h'
    | cons _ _ => simp_all [concat_eq_append]
    | cons₂ _ _ => simp_all [concat_eq_append]

/-- If `p <+ q` then `p <+ q ++ r` -/
lemma Subwalk.append_right {p : G.Walk u v} {q : G.Walk x y} (hs : p.Subwalk q) (r : G.Walk y z) :
     p.Subwalk (q.append r) := by induction r <;> simp_all [← concat_append]

/-- If `p <+ q` then `p.reverse <+ q.reverse` -/
lemma Subwalk.reverse {p : G.Walk u v} {q : G.Walk x y} (hs : p.Subwalk q) :
    p.reverse.Subwalk q.reverse := by
  induction q generalizing u with
  | nil => simp_all [subwalk_nil_iff]
  | @cons a b _ h q ih =>
    rw [reverse_cons, ← concat_append, append_nil]
    by_cases ha : u = a
    · subst ha
      cases p with
      | nil => simp
      | @cons _ w _ _ p =>
      rw [reverse_cons, ← concat_append, append_nil]
      by_cases hwb : w = b
      · subst hwb
        exact (ih <| hs.of_cons₂ h).concat₂ _
      · exact (reverse_cons _ _ ▸ ih <| hs.of_cons₂_of_ne _ h hwb).concat _
    · exact (ih (hs.of_cons_of_ne _ ha)).concat _

/-- If `p.concat h <+ q` then `p <+ q` -/
lemma Subwalk.of_concat {p : G.Walk u v} {q : G.Walk x y} (h : G.Adj v z)
    (hs : (p.concat h).Subwalk q) : p.Subwalk q := by
  have := hs.reverse
  rw [reverse_concat] at this
  simpa using (this.of_cons h.symm).reverse

/-- If `p.concat h <+ q.concat h` then `p <+ q` -/
lemma Subwalk.of_concat₂ {p : G.Walk u v} {q : G.Walk x v} (h : G.Adj v y)
    (hs : (p.concat h).Subwalk (q.concat h)) : p.Subwalk q := by
  have := hs.reverse
  simp only [reverse_concat] at this
  simpa using (this.of_cons₂ h.symm).reverse

/--
If `p <+ q.concat hq` and `p : G.Walk u v` and `hq : G.Adj y t` with `v ≠ t` then `p <+ q`
-/
lemma Subwalk.of_concat_of_ne {p : G.Walk u v} {q : G.Walk x y} (hq : G.Adj y z)
     (h : p.Subwalk (q.concat hq)) (hne : v ≠ z) : p.Subwalk q := by
  have := Subwalk.reverse h
  simp only [reverse_concat] at this
  simpa using (this.of_cons_of_ne hq.symm hne).reverse

/--
If `p.concat hp <+ q.concat hq` and the start of the darts `hp` and `hq` differ then
`p.concat hp <+ q`
-/
lemma Subwalk.of_concat₂_of_ne {p : G.Walk u v} {q : G.Walk x y} (hp : G.Adj v z) (hq : G.Adj y z)
    (hs : (p.concat hp).Subwalk (q.concat hq)) (hne : v ≠ y) : (p.concat hp).Subwalk q := by
  have := hs.reverse
  simp only [reverse_concat] at this
  simpa using (this.of_cons₂_of_ne hp.symm hq.symm hne).reverse

/-- If `p ++ r <+ q ++ r` then `p <+ q` -/
lemma Subwalk.of_append_right {p : G.Walk u v} {q : G.Walk x v} (r : G.Walk v y)
    (hs : (p.append r).Subwalk (q.append r)) : p.Subwalk q := by
  have := hs.reverse
  simp only [reverse_append] at this
  simpa using (this.of_append_left r.reverse).reverse

/-- *Transitivity of Subwalks* -/
@[trans]
theorem Subwalk.trans {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂} {p₃ : G.Walk u₃ v₃}
    (h₁ : p₁.Subwalk p₂) (h₂ : p₂.Subwalk p₃) : p₁.Subwalk p₃ := by
  induction h₂ generalizing u₁ with
  | nil =>
    obtain ⟨hp, rfl, rfl⟩ := subwalk_nil_iff.1 h₁
    simp [nil_iff_eq_nil.1 hp]
  | cons h' p₂ ih => simp_all
  | @cons₂ a _ _ d _ _ h' _ ih =>
    by_cases hud : u₁ = d
    · subst hud
      cases p₁ with
      | nil => simp
      | @cons _ e _ h p =>
        by_cases hea : e = a
        · subst hea
          exact (ih <| h₁.of_cons₂ _).cons₂ _
        · exact (ih <| h₁.of_cons₂_of_ne _ _ hea).cons h'
    · exact (ih <| h₁.of_cons_of_ne _ hud).cons _

/--
If `p <+ q` and `q <+ p` then `p.support = q.support`
-/
lemma Subwalk.antisymm_support {p : G.Walk u v} {q : G.Walk x y} (h1 : p.Subwalk q)
    (h2 : q.Subwalk p) : p.support = q.support :=
  List.Sublist.antisymm h1.support_sublist h2.support_sublist

/-- If `p <+ q` then `r ++ p <+ q` -/
lemma Subwalk.append_left_left {p : G.Walk u v} {q : G.Walk u y} (hs : p.Subwalk q)
    (r : G.Walk x u) : (r.append p).Subwalk (r.append q) := by induction r <;> simp_all

/-- If `p <+ q` then `p ++ r <+ q ++ r` -/
lemma Subwalk.append_right_right {p : G.Walk u v} {q : G.Walk x v} (hs : p.Subwalk q)
    (r : G.Walk v y) : (p.append r).Subwalk (q.append r) := by
  have := hs.reverse
  simpa using (this.append_left_left r.reverse).reverse

/--
If `p₁ <+ q₁` and `p₂ <+ q₂` then `p₁ ++ p₂ <+ q₁ ++ q₂` (if these are well-defined)
-/
theorem Subwalk_append {p₁ : G.Walk u₁ x} {p₂ : G.Walk x u₂} {q₁ : G.Walk v₁ y} {q₂ : G.Walk y v₂}
    (h1 : p₁.Subwalk q₁) (h2 : p₂.Subwalk q₂) : (p₁.append p₂).Subwalk (q₁.append q₂) := by
  induction h1 <;> simp_all [Subwalk.append_left]

/-- If `p <+ q` and `q.length ≤ p.length` then `p = q` (mod casting endpoints) -/
theorem Subwalk.eq_of_length_le {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} (h1 : p.Subwalk q)
    (h2 : q.length ≤ p.length) :  ∃ hu hv, p.copy hu hv = q := by
  induction p generalizing u₂ with
  | nil =>
    cases q with
    | nil =>
      obtain ⟨_, rfl, _⟩ := subwalk_nil_iff.1 h1
      simp
    | cons h p => simp at h2
  | @cons a b _ hp _ ih =>
    cases q with
    | nil => simp [subwalk_nil_iff] at h1
    | @cons _ e _ hq _ =>
      by_cases hau : a = u₂
      · subst hau
        by_cases hbe : b = e
        · subst hbe
          obtain ⟨_, rfl, rfl⟩ := ih h1.of_cons₂ (by simpa using h2)
          simp
        · have h1 := (h1.of_cons₂_of_ne _ _ hbe).length_le
          simp only [length_cons, Nat.add_le_add_iff_right] at h1 h2
          omega
      · have h1 := (h1.of_cons_of_ne _ hau).length_le
        simp only [length_cons, Nat.add_le_add_iff_right] at h1 h2
        omega

/-- If `p <+ q` and `q <+ p` then `p = q` (mod casting endpoints) -/
theorem Subwalk.antisymm {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} (h1 : p.Subwalk q)
    (h2 : q.Subwalk p) :  ∃ hu hv, p.copy hu hv = q := h1.eq_of_length_le h2.length_le

/--
If `p <+ q₁ ++ q₂` then either `p <+ q₁` or `p <+ q₂` or `∃ y, r₁, r₂` such that `p = r₁ ++ r₂`
and `r₁ <+ q₁` and `r₂ <+ q₂`
-/
theorem Subwalk.of_append {p : G.Walk u v} {q₁ : G.Walk v₁ x} {q₂ : G.Walk x v₂}
    (hs : p.Subwalk (q₁.append q₂)) : p.Subwalk q₁ ∨ p.Subwalk q₂ ∨ ∃ (y : V) (r₁ : G.Walk u y)
    (r₂ : G.Walk y v), p = r₁.append r₂ ∧ r₁.Subwalk q₁ ∧ r₂.Subwalk q₂ := by
  induction q₁ generalizing p u v with
  | @nil z => right; left; simpa
  | @cons _ b _ h q₁ ih =>
    cases hs with
    | nil => simp
    | cons h hs =>
      obtain (h1 | h2 | ⟨z, s₁, s₂, rfl, h3, h4⟩) := ih hs
      · exact Or.inl <| h1.cons _
      · exact Or.inr <| Or.inl h2
      · exact Or.inr <| Or.inr ⟨z, s₁, s₂, rfl, h3.cons _, h4⟩
    | @cons₂ _ _ _ _ p _ h' hs =>
      obtain (h1 | h2 | ⟨z, s₁, s₂, rfl, h3, h4⟩) := ih hs
      · exact Or.inl <| h1.cons₂ h
      · exact Or.inr <| Or.inr ⟨b, (nil' b).cons h', p, by simp_all⟩
      · exact Or.inr <| Or.inr ⟨z, s₁.cons h', s₂, by simp_all⟩

/--
If `p <+ q₁ ++ q₂` and `p.end ∉ q₂`  then `p <+ q₁` (can weaken this to `p.end ∉ q₂.support.tail`)
-/
theorem Subwalk.of_append_not_mem_right {p : G.Walk u v} {q₁ : G.Walk v₁ x} {q₂ : G.Walk x v₂}
    (hs : p.Subwalk (q₁.append q₂)) (hv : v ∉ q₂.support) : p.Subwalk q₁ := by
  obtain (hs | hs | ⟨_,_,r,_,_, hs⟩) := hs.of_append
  · exact hs
  · exact (hv <| hs.support_sublist.mem p.end_mem_support).elim
  · exact (hv <| hs.support_sublist.mem r.end_mem_support).elim

/--
If `p <+ q₁ ++ q₂` and `p.end ∉ q₂.support.tail`  then `p <+ q₁`
-/
theorem Subwalk.of_append_not_mem_right' {p : G.Walk u v} {q₁ : G.Walk v₁ x} {q₂ : G.Walk x v₂}
    (hs : p.Subwalk (q₁.append q₂)) (hv : v ∉ q₂.support.tail) : p.Subwalk q₁ := by
  by_cases hvx : v = x
  · subst hvx
    obtain (hs | hs | ⟨_,_,r,_,_, hs⟩) := hs.of_append
    · exact hs
    · cases hs with
    | nil => simp
    | cons h hs =>
      simp_all only [cons, append_left, support_cons, List.tail_cons]
      exact (hv (hs.support_sublist.mem p.end_mem_support)).elim
    | cons₂ h hs =>
      simp_all only [support_cons, List.tail_cons, cons₂, append_left]
      exact (hv (hs.support_sublist.mem (end_mem_support _))).elim
    · cases hs with
    | nil => simp_all
    | cons h hs' => exfalso; simp_all [(hs'.support_sublist.mem (end_mem_support _))]
    | cons₂ h hs' => exfalso; simp_all [(hs'.support_sublist.mem (end_mem_support _))]
  · apply hs.of_append_not_mem_right
    intro h
    rw [support_eq_cons] at h
    cases h <;> trivial


/--
If `p <+ q₁ ++ q₂` and `p.start ∉ q₁`  then `p <+ q₂`
  (can weaken this to `p.end ∉ q₁.support.dropLast`)
-/
theorem Subwalk.of_append_not_mem_left {p : G.Walk u v} {q₁ : G.Walk v₁ x} {q₂ : G.Walk x v₂}
    (hs : p.Subwalk (q₁.append q₂)) (hu : u ∉ q₁.support) : p.Subwalk q₂ := by
  have hs := hs.reverse
  rw [reverse_append] at hs
  simpa using (hs.of_append_not_mem_right (by simp_all)).reverse

theorem Subwalk.of_append_not_mem_left' {p : G.Walk u v} {q₁ : G.Walk v₁ x} {q₂ : G.Walk x v₂}
    (hs : p.Subwalk (q₁.append q₂)) (hu : u ∉ q₁.support.dropLast) : p.Subwalk q₂ := by
  have hs := hs.reverse
  rw [reverse_append] at hs
  simpa using (hs.of_append_not_mem_right' (by simp_all)).reverse

/-- If  `q₁ ++ q₂ <+ p` then `∃ y, r₁, r₂` such that `p = r₁ ++ r₂`
and `r₁ <+ q₁` and `r₂ <+ q₂`
-/
theorem append_subwalk {p : G.Walk u v} {q₁ : G.Walk v₁ x} {q₂ : G.Walk x v₂}
    (hs : (q₁.append q₂).Subwalk p) : ∃ (y : V) (r₁ : G.Walk u y) (r₂ : G.Walk y v),
    p = r₁.append r₂ ∧ q₁.Subwalk r₁ ∧ q₂.Subwalk r₂ := by
  induction p generalizing q₁ q₂ v₁ x with
  | nil =>
    rw [subwalk_nil_iff, nil_append_iff] at hs
    obtain ⟨⟨h1, h2⟩, rfl, rfl⟩ := hs
    have := h1.eq
    subst this
    exact ⟨v₂, nil, nil, by simp_all [subwalk_nil_iff]⟩
  | @cons a b c h p ih =>
    by_cases hav₁ : v₁ = a
    · subst hav₁
      cases q₁ with
      | nil => cases hs <;> exact ⟨_, nil, p.cons h, by simp_all⟩
      | @cons d e f hq q₁ =>
        rw [cons_append] at hs
        by_cases hbe : e = b
        · subst hbe
          obtain ⟨y, s₁, s₂, h1, h2, h3⟩ := ih <| hs.of_cons₂
          exact ⟨y, s₁.cons h, s₂, by simp_all⟩
        · have := hs.of_cons₂_of_ne _ _ hbe
          rw [← cons_append] at this
          obtain ⟨y, s₁, s₂, h1, h2, h3⟩ := ih this
          exact ⟨y, s₁.cons h, s₂, by simp_all⟩
    · obtain ⟨y, r₁, r₂, rfl, h2, h3⟩ := ih <| hs.of_cons_of_ne _ hav₁
      exact ⟨y, r₁.cons h, r₂, by simp_all⟩

lemma length_lt_of_subwalk_not_subwalk {p : G.Walk u v} {q : G.Walk x y} (hs : p.Subwalk q)
    (hn : ¬ q.Subwalk p) : p.length < q.length := by
  contrapose! hn
  obtain ⟨rfl, rfl, rfl⟩ := hs.eq_of_length_le hn
  simp

@[simp]
lemma Subwalk.copy_copy {x' y' u' v'} {p : G.Walk u v} {q : G.Walk x y} (h : p.Subwalk q)
    {hu : u = u'} {hv : v = v'} {hx : x = x'} {hy : y = y'} :
    (p.copy hu hv).Subwalk (q.copy hx hy) ↔ p.Subwalk q := by
  subst_vars; simp

variable {W : Type*} {G' : SimpleGraph W}

lemma Subwalk.map {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} (hs : p.Subwalk q) (f : G →g G') :
    (p.map f).Subwalk (q.map f) := by
  induction hs <;> simp_all

variable {H : SimpleGraph V}
lemma Subwalk.transfer  {p : G.Walk u v} {q : G.Walk x y} (h : p.Subwalk q) (hp) (hq) :
    (p.transfer H hp).Subwalk (q.transfer H hq) := by
  induction q generalizing p u v with
  | nil =>
    rw [subwalk_nil_iff] at h
    obtain ⟨hn, rfl, rfl⟩ := h
    have := hn.eq_nil
    subst this
    simp
  | @cons a b c h' q ih =>
    cases p with
    | nil => simp_all
    | @cons d e f h'' p =>
      by_cases hua : u = a
      · subst hua
        by_cases hbe : e = b
        · subst hbe
          have hH : H.Adj u e := by simp_all [edges_cons]
          exact (ih (h.of_cons₂ h') (by simp_all) (by simp_all)).cons₂ hH
        · have := ih (h.of_cons₂_of_ne _ _ hbe) (by simp_all) (by simp_all)
          have hH : H.Adj u b := by
            simp_rw [edges_cons] at hq

            sorry
          exact this.cons hH
      ·
        sorry



---------------- IsInfix / IsPrefix / IsSuffix walks

/-- `p.IsInfix q` means that the walk `p` is a contiguous Subwalk of the walk `q`. -/
def IsInfix (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) : Prop :=
  ∃ (ru : G.Walk u₂ u₁) (rv : G.Walk v₁ v₂), q = (ru.append p).append rv

/-- If `p <:+: q` then `p <+ q` -/
lemma IsInfix.subwalk {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} (h : p.IsInfix q) : p.Subwalk q := by
  obtain ⟨r, s, h⟩ := h
  rw [← append_assoc] at h
  exact h ▸ ((Subwalk.refl p).append_right s).append_left r

@[simp,refl]
lemma IsInfix.refl (p : G.Walk u₁ v₁) : p.IsInfix p := ⟨nil' u₁, nil' v₁, by simp⟩

@[simp]
lemma IsInfix.nil {q : G.Walk u v} (hx : x ∈ q.support) : (nil' x).IsInfix q := by
  classical
  use q.takeUntil _ hx, q.dropUntil _ hx
  simp [(take_spec _ hx)]

lemma IsInfix.of_nil {q : G.Walk u v} (h : q.IsInfix (nil' x)) : q.Nil ∧ u = x ∧ v = x := by
  simpa using subwalk_nil_iff.1 h.subwalk

lemma isInfix_nil_iff {q : G.Walk u v} : q.IsInfix (nil' x) ↔ q.Nil ∧ u = x ∧ v = x := by
  constructor
  · intro h; exact h.of_nil
  · rintro ⟨hq, rfl, rfl⟩
    have := hq.eq_nil
    subst this; rfl

/-- `p.IsPrefix q` means that the walk `q` starts with the walk `p`. -/
def IsPrefix (p : G.Walk u v₁) (q : G.Walk u v₂) : Prop :=
  ∃ (r : G.Walk v₁ v₂), q = p.append r

/-- `p.IsSuffix q` means that the walk `q` ends with the walk `p`. -/
def IsSuffix (p : G.Walk u₂ v) (q : G.Walk u₁ v) : Prop :=
  ∃ (r : G.Walk u₁ u₂), q = r.append p

@[simp,refl]
lemma IsPrefix.refl (p : G.Walk u₁ v₁) : p.IsPrefix p := ⟨nil' v₁, by simp⟩

lemma IsPrefix.infix {p : G.Walk u v₁} {q : G.Walk u v₂} (h : p.IsPrefix q) : p.IsInfix q := by
  obtain ⟨r, hr⟩ := h
  exact ⟨nil' _ ,r , by simpa⟩

lemma IsSuffix.infix {p : G.Walk u₁ v} {q : G.Walk u₂ v} (h : p.IsSuffix q) : p.IsInfix q := by
  obtain ⟨s, hr⟩ := h
  exact ⟨s, nil' _, by simpa⟩

@[simp,refl]
lemma IsSuffix.refl (p : G.Walk u₁ v₁) : p.IsSuffix p := ⟨nil' u₁, by simp⟩

lemma IsPrefix.subwalk {p : G.Walk u v} {q : G.Walk u w} (h : p.IsPrefix q) :
    p.Subwalk q := h.infix.subwalk

lemma IsSuffix.subwalk {p : G.Walk u w} {q : G.Walk v w} (h : p.IsSuffix q) : p.Subwalk q :=
  h.infix.subwalk

lemma IsPrefix.nil (q : G.Walk u v) : (nil' u).IsPrefix q := ⟨q, rfl⟩

lemma IsPrefix.of_nil {q : G.Walk u v} (h : q.IsPrefix (nil' u)) : q.Nil ∧ v = u := by
  simpa using subwalk_nil_iff.1 h.subwalk

lemma IsSuffix.nil (q : G.Walk u v) : (nil' v).IsSuffix q := ⟨q, by simp⟩

lemma IsSuffix.of_nil {q : G.Walk u v} (h : q.IsSuffix (nil' v)) : q.Nil ∧ u = v := by
  simpa using subwalk_nil_iff.1 h.subwalk

/-- `p.cons h <+: q.cons h` iff `p <+: q` -/
lemma isPrefix_cons_iff {p : G.Walk u₂ v₁} {q : G.Walk u₂ v₂} (h : G.Adj u₁ u₂) :
    (cons h p).IsPrefix (cons h q) ↔ p.IsPrefix q := by
  constructor <;> intro ⟨r, hr⟩ <;> exact ⟨r, by simp_all⟩

lemma IsPrefix.support {p : G.Walk u v₁} {q : G.Walk u v₂} (h: p.IsPrefix q) :
    p.support <+: q.support := by
  obtain ⟨r, rfl⟩ := h
  use r.support.tail
  simp [support_append]

lemma isPrefix_of_support {p : G.Walk u v₁} {q : G.Walk u v₂}
    (h : p.support <+: q.support) : p.IsPrefix q := by
  induction p with
  | nil => exact IsPrefix.nil _
  | @cons _ y _ _ _ ih =>
    cases q with
    | nil => simp at h
    | @cons _ b _ _ p =>
      simp only [support_cons, List.cons_prefix_cons, true_and] at h
      have : y = b := by
        rw [support_eq_cons, support_eq_cons p, List.cons_prefix_cons] at h
        exact h.1
      subst this
      apply (isPrefix_cons_iff _).2 (ih h)

lemma isPrefix_iff_support {p : G.Walk u v₁} {q : G.Walk u v₂} :
    p.IsPrefix q ↔ p.support <+: q.support:= Iff.intro IsPrefix.support isPrefix_of_support

lemma isSuffix_iff_reverse_isPrefix (p : G.Walk u₂ v) (q : G.Walk u₁ v) :
    p.IsSuffix q ↔ p.reverse.IsPrefix q.reverse := by
  constructor <;> intro ⟨r, hr⟩ <;>
  · apply_fun Walk.reverse at hr
    use r.reverse
    simpa using hr

lemma isSuffix_iff_support (p : G.Walk u₂ v) (q : G.Walk u₁ v) :
    p.IsSuffix q ↔ p.support <:+ q.support := by
  simp_rw [isSuffix_iff_reverse_isPrefix, isPrefix_iff_support, support_reverse,
            List.reverse_prefix]

lemma isInfix_iff_exists_isPrefix_append (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) :
    p.IsInfix q ↔ ∃ r : G.Walk u₂ u₁, (r.append p).IsPrefix q := by
  constructor <;> intro ⟨r, ⟨s, hs⟩⟩ <;>
  · use r, s

lemma isInfix_iff_exists_isSuffix_append (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) :
  p.IsInfix q ↔ ∃ s : G.Walk v₁ v₂, (p.append s).IsSuffix q := by
  constructor <;> intro ⟨r, ⟨s, hs⟩⟩ <;>
  · exact ⟨s, r, by rw [hs, append_assoc]⟩

lemma support_append' {p : G.Walk u v} {q : G.Walk v w} :
    (p.append q).support = p.support.dropLast ++ q.support := by
  apply_fun List.reverse using List.reverse_injective
  rw [List.reverse_append, ← support_reverse, ← support_reverse, reverse_append, support_append]
  apply (List.append_right_inj _).2
  rw [support_reverse, support_eq_cons, List.tail_reverse]

lemma IsInfix.support {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} (h : p.IsInfix q) :
    p.support <:+: q.support := by
  obtain ⟨r , s, rfl⟩ := h
  use r.support.dropLast, s.support.tail
  rw [support_append, support_append']

/--
Note the analogous result is false for Subwalks : `[x, z] <+ [x, y, z]` as lists of vertices,
but the single edge walk from `x` to `z` is not a subwalk of the two edge walk from
`x` to `z` via `y`.
-/
lemma isInfix_of_support {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} (h : p.support <:+: q.support) :
    p.IsInfix q := by
  induction q with
  | nil =>
    rw [support_eq_cons, support_nil, List.infix_cons_iff] at h
    cases h <;> cases p <;> simp_all
  | @cons a _ _ h' q ih =>
    rw [support_cons, List.infix_cons_iff] at h
    cases h with
    | inl h =>
      have hpre : p.support <+: (cons h' q).support := by simpa
      have heq : u₁ = a := by
        rw [support_eq_cons, support_cons, List.cons_prefix_cons] at hpre
        exact hpre.1
      subst heq
      exact (isPrefix_of_support hpre).infix
    | inr h =>
      obtain ⟨r, s, hr⟩ := ih h
      use (cons h' r), s
      simpa

/--
Sanity check that in a triangle `x y z`, one edge is not a subwalk of the path formed by the other
two edges
-/
lemma not_xz_subwalk_xyz (h1 : G.Adj x y) (h2 : G.Adj y z) (h3 : G.Adj x z):
    ¬ ((nil' z).cons h3).Subwalk (((nil' z).cons h2).cons h1) := by
  intro hs
  cases hs with
  | cons h hs =>
    cases hs <;> simp_all [subwalk_nil_iff]
  | cons₂ h _ => aesop

lemma isInfix_iff_support (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) :
    p.IsInfix q ↔ p.support <:+: q.support := Iff.intro IsInfix.support isInfix_of_support

lemma isInfix_iff_reverse {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} :
    p.IsInfix q ↔ p.reverse.IsInfix q.reverse := by
  constructor <;> intro ⟨r, s, h⟩ <;> use s.reverse, r.reverse
  · rw [h]
    simp [append_assoc]
  · apply_fun Walk.reverse at h
    simpa [append_assoc] using h

alias ⟨IsInfix.reverse, _⟩ := isInfix_iff_reverse

lemma IsInfix.antisymm {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} (h1 : p.IsInfix q)
    (h2 : q.IsInfix p) : ∃ hu hv, p.copy hu hv = q := Subwalk.antisymm h1.subwalk h2.subwalk

/-- Any Subwalk of a path is an IsInfix walk -/
lemma Subwalk.isInfix_of_isPath {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} (hp : q.IsPath)
  (hs : p.Subwalk q) :
    p.IsInfix q := by
  induction q generalizing u₁ with
  | nil =>
    rw [subwalk_nil_iff] at hs
    obtain ⟨h, rfl, rfl⟩ := hs
    rw [h.eq_nil]
  | @cons a b c hq q ih =>
    cases p with
    | nil => simp_all
    | @cons d e f hp' p =>
      rw [cons_isPath_iff] at hp
      by_cases hua : u₁ = a
      · subst hua
        by_cases hbe : e = b
        · subst hbe
          obtain ⟨r, s, hr⟩ := ih hp.1 hs.of_cons₂
          have : q = p.append s := by
            have := (hr ▸ hp.1).of_append_left.of_append_left
            simp at this
            rw [this] at hr
            simpa
          use nil' u₁, s
          simp [this]
        · exact (hp.2 <| (hs.of_cons₂_of_ne _ _ hbe).support_sublist.mem (start_mem_support _)).elim
      · obtain ⟨r, s, rfl⟩ := ih hp.1 (hs.of_cons_of_ne _ hua)
        use r.cons hq, s
        simp

lemma takeUntil_isPrefix [DecidableEq V] {p : G.Walk u v} (hx : x ∈ p.support) :
    (p.takeUntil _ hx).IsPrefix p := ⟨_, (take_spec p hx).symm⟩

lemma dropUntil_isSuffix [DecidableEq V] {p : G.Walk u v} (hx : x ∈ p.support) :
    (p.dropUntil _ hx).IsSuffix p := ⟨_, (take_spec p hx).symm⟩

lemma take_isPrefix {p : G.Walk u v} (n : ℕ) :
    (p.take n).IsPrefix p := ⟨_, (take_append_drop p n).symm⟩

lemma drop_isSuffix {p : G.Walk u v} (n : ℕ) :
    (p.drop n).IsSuffix p := ⟨_, (take_append_drop p n).symm⟩

lemma tail_isSuffix (p : G.Walk u v) : p.tail.IsSuffix p := p.drop_isSuffix _

lemma dropLast_isPrefix (p : G.Walk u v) : p.dropLast.IsPrefix p := p.take_isPrefix _

lemma bypass_subwalk [DecidableEq V] (p : G.Walk u v) : p.bypass.Subwalk p := by
  induction p with
  | nil => rfl
  | cons _ p ih =>
    rw [bypass]
    split_ifs with h1
    · exact (p.bypass.dropUntil_isSuffix h1).subwalk.trans (ih.cons _)
    · exact ih.cons₂ _

/-- `p ++ r <+ p ++ q ++ r` i.e. removing a loop from a walk yields a subwalk. -/
lemma Subwalk.of_isPrefix_append_isSuffix {p : G.Walk u₁ u₂} {q : G.Walk u₂ u₂}
    {r : G.Walk u₂ u₃} : (p.append r).Subwalk (p.append (q.append r)) :=
  ((Subwalk.refl r).append_left  q).append_left_left p

/-! ## Rotated Subwalks -/
section DecEq
variable [DecidableEq V]
/--
`p` is a rotated subwalk of `q` if it is a rotation of a subwalk
-/
def IsRotatedSubwalk (p : G.Walk u u) (q : G.Walk v w) : Prop :=
    ∃ (x : V) (r : G.Walk x x) (hu : u ∈ r.support), r.Subwalk q ∧ p = r.rotate hu

lemma IsRotatedSubwalk.nil (u : V) : (nil' u : G.Walk u u).IsRotatedSubwalk (nil' u) :=
  ⟨u, nil' u, by simp⟩

/-- Any closed subwalk is trivially a rotated subwalk -/
lemma Subwalk.isRotated {p : G.Walk u u} {q : G.Walk v w} (h : p.Subwalk q) :
    p.IsRotatedSubwalk q := by use u; simpa

lemma IsRotatedSubwalk.support_subset {p : G.Walk u u} {q : G.Walk v w} (h : p.IsRotatedSubwalk q) :
    p.support ⊆ q.support := by
  obtain ⟨_, _, _, hr1, rfl⟩ := h
  intro _ hy
  exact hr1.support_sublist.mem (by rwa [← mem_support_rotate_iff] )

lemma IsRotatedSubwalk.darts_subset {p : G.Walk u u} {q : G.Walk v w} (h : p.IsRotatedSubwalk q) :
    p.darts ⊆ q.darts := by
  obtain ⟨_, _, hx, hr1, rfl⟩ := h
  intro _ hy
  exact hr1.darts_sublist.mem <| (rotate_darts _ hx).symm.mem_iff.2 hy

lemma IsRotatedSubwalk.edges_subset {p : G.Walk u u} {q : G.Walk v w} (h : p.IsRotatedSubwalk q) :
    p.edges ⊆ q.edges := by
  obtain ⟨_, _, hx, hr1, rfl⟩ := h
  intro _ hy
  exact hr1.edges_sublist.mem <| (rotate_edges _ hx).symm.mem_iff.2 hy

lemma IsRotatedSubwalk.length_le {u v w : V} {p : G.Walk u u} {q : G.Walk v w}
    (h : p.IsRotatedSubwalk q) : p.length ≤ q.length := by
  obtain ⟨x, r, hx, hr1, rfl⟩ := h
  exact length_rotate hx ▸ hr1.length_le

/- We also sometimes care about rotated subwalks of rotated walks -/
lemma IsRotatedSubwalk.support_subset_rotate {p : G.Walk u u} {q : G.Walk v v} (hy : y ∈ q.support)
    (h : p.IsRotatedSubwalk (q.rotate hy)) : p.support ⊆ q.support :=
  h.support_subset.trans (fun _ hz ↦ (mem_support_rotate_iff hy).mp hz)

lemma IsRotatedSubwalk.darts_subset_rotate {p : G.Walk u u} {q : G.Walk v v} (hy : y ∈ q.support)
    (h : p.IsRotatedSubwalk (q.rotate hy)) : p.darts ⊆ q.darts :=
  h.darts_subset.trans (fun _ hz ↦ (rotate_darts _ hy).symm.mem_iff.2 hz)

lemma IsRotatedSubwalk.edges_subset_rotate {p : G.Walk u u} {q : G.Walk v v} (hy : y ∈ q.support)
    (h : p.IsRotatedSubwalk (q.rotate hy)) : p.edges ⊆ q.edges :=
  h.edges_subset.trans (fun _ hz ↦ (rotate_edges _ hy).symm.mem_iff.2 hz)

lemma IsRotatedSubwalk.length_le_rotate {p : G.Walk u u} {q : G.Walk v v} (hy : y ∈ q.support)
    (h : p.IsRotatedSubwalk (q.rotate hy)): p.length ≤ q.length :=
  length_rotate hy ▸ h.length_le

end DecEq

/-! # Results about injectivity of appending walks -/

/--
If `p₁ ++ p₂ = q₁ ++ q₂` and `p₁.length = q₁.length` then `p₁ = q₁` and `p₂ = q₂`.
-/
lemma append_inj {p₁ : G.Walk u u₁} {p₂ : G.Walk u₁ v} {q₁ : G.Walk u v₁} {q₂ : G.Walk v₁ v}
    (hp : p₁.append p₂ = q₁.append q₂) (hl : p₁.length = q₁.length) :
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
    | cons =>
      simp_rw [cons_append, cons.injEq] at *
      have := hp.1
      subst this
      obtain ⟨rfl, rfl⟩ := ih (by simpa using hp) (by simpa using hl)
      simp

/--
If `p₁ ++ p₂ = q₁ ++ q₂` and `p₂.length = q₂.length` then `p₁ = q₁` and `p₂ = q₂`.
-/
lemma append_inj' {p₁ : G.Walk u u₁} {p₂ : G.Walk u₁ v} {q₁ : G.Walk u v₁} {q₂ : G.Walk v₁ v}
    (hp : p₁.append p₂ = q₁.append q₂) (hl : p₂.length = q₂.length) :
    ∃ h, p₁.copy rfl h = q₁ ∧ p₂.copy h rfl = q₂ := by
  apply append_inj hp
  apply_fun length at hp
  simp_rw [length_append] at hp
  omega

lemma append_left_inj {p₁ p₂: G.Walk u v₁} {q : G.Walk v₁ v₂} :
    p₁.append q = p₂.append q ↔ p₁ = p₂ := by
  constructor <;> intro heq
  · obtain ⟨_, h1, h2⟩ := append_inj heq (by apply_fun length at heq; simpa using heq)
    simp [← h1]
  · subst heq; rfl

lemma append_right_inj {p : G.Walk u₁ u₂} {q₁ q₂ : G.Walk u₂ v} :
    p.append q₁ = p.append q₂ ↔ q₁ = q₂ := by
  constructor <;> intro heq
  · obtain ⟨_, h1, h2⟩ := append_inj heq (by simp)
    simp [← h2]
  · subst heq; rfl

lemma support_reverse_dropLast (p : G.Walk u v) :
    p.reverse.support.dropLast = p.support.tail.reverse := by
  cases p with
  | nil => simp
  | cons h p =>
    rw [support_reverse, support_cons]
    simp

#check PartialOrder
lemma IsCircuit.reverse {c : G.Walk x x} (hc : c.IsCircuit) : c.reverse.IsCircuit := by
  apply IsCircuit.mk hc.toIsTrail.reverse
  intro hf
  rw [← nil_iff_eq_nil, nil_reverse] at hf
  exact hc.not_nil hf

lemma isCycle_support_dropLast_nodup {c : G.Walk x x} (hc : c.IsCircuit)
    (hd : c.support.dropLast.Nodup) : c.IsCycle := by
  rw [← isCycle_reverse]
  have := support_reverse_dropLast c.reverse
  rw [reverse_reverse] at this
  rw [this] at hd
  apply IsCycle.mk hc.reverse <| List.nodup_reverse.1 hd

lemma IsCycle.support_dropLast_nodup {c : G.Walk x x} (hc : c.IsCycle) :
    c.support.dropLast.Nodup := by
  have := hc.reverse.support_nodup
  have := c.reverse.support_reverse_dropLast
  rw [reverse_reverse] at this
  rwa [this, List.nodup_reverse]

lemma IsCircuit.isCycle_iff_support_dropLast {c : G.Walk x x} (hc : c.IsCircuit) :
  c.IsCycle ↔ c.support.dropLast.Nodup := Iff.intro
    (fun h ↦ h.support_dropLast_nodup) (fun h ↦ isCycle_support_dropLast_nodup hc h)


end SimpleGraph.Walk
