import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Mathlib.Combinatorics.SimpleGraph.Path
variable {V : Type*}

namespace List

lemma sublist_rotate_one {l k : List V} (hs : l <+ k) :
  l <+ k.rotate 1 ∨ l.rotate 1 <+ k.rotate 1 := by
  induction k with
  | nil => simp_all
  | cons b =>
    cases l with
    | nil => simp
    | cons a =>
      by_cases hab : a = b
      · simp_all [hab]
      · simp_all [hs.of_cons_of_ne hab]

/--
If `l <+ k` then any rotation of `k` contains a rotation of `l` as a sublist
-/
lemma sublist_rotate {l k : List V} (hs : l <+ k) (n : ℕ) :
    ∃ m ≤ n, (l.rotate m) <+ (k.rotate n) := by
  induction n with
  | zero => simpa
  | succ _ ih =>
    obtain ⟨m, hm, hs⟩ := ih
    cases sublist_rotate_one hs with
    | inl h =>  exact ⟨m, by omega, by simpa [rotate_rotate] using h⟩
    | inr h => exact ⟨m + 1, by omega, by simpa [rotate_rotate] using h⟩


lemma rotate_sublist_rotate_cons_succ {a : V} {l : List V} {n : ℕ} (hn : n ≤ l.length):
    l.rotate n <+ (a :: l).rotate (n + 1) := by
  rw [List.rotate_eq_drop_append_take hn, List.rotate_eq_drop_append_take (by simpa)]
  simp

lemma rotate_sublist_one {l k : List V} (hs : l <+ k) :
    ∃ n, n ≤ k.length ∧ (l.rotate 1) <+ (k.rotate n) := by
    cases l with
    | nil => use 0; simp
    | cons a l =>
      simp only [rotate_cons_succ, rotate_zero]
      induction k with
      | nil => simp_all
      | cons b k ih =>
        by_cases hab : a = b
        · exact ⟨1, by simp_all [hab]⟩
        · obtain ⟨j, hs⟩:= ih <| hs.of_cons_of_ne hab
          cases j with
          | zero => use 0; simp_all
          | succ j =>
            exact ⟨j+2, by simpa using hs.1, hs.2.trans <| rotate_sublist_rotate_cons_succ hs.1⟩

/--
If `l <+ k` then any rotation of `l` is a sublist of some rotation of `k`
-/
lemma Sublist.rotate {l k : List V} (hs : l <+ k) (m : ℕ) : ∃ n, (l.rotate m) <+ (k.rotate n) := by
  induction m with
  | zero => use 0; simpa
  | succ m ih =>
    obtain ⟨j, hs⟩ := ih
    cases l with
    | nil => use 0; simp
    | cons a l =>
      obtain ⟨n, hn⟩ := rotate_sublist_one hs
      simp_rw [rotate_rotate] at hn
      exact ⟨j + n, hn.2⟩

lemma rotate_sublist_subset {l k : List V} (hs : l <+ k) (m : ℕ) : l.rotate m ⊆ k := by
  intro _ hx
  obtain ⟨n, hs⟩ := hs.rotate m
  exact hs.subset.trans (fun _ h ↦ mem_rotate.mp h) hx

end List

namespace SimpleGraph.Walk

/-! # Results about appending walks -/

variable {G : SimpleGraph V}

lemma append_cons_eq_concat_append {u v w z} {p : G.Walk u v} {q : G.Walk w z} {h : G.Adj v w} :
    p.append (cons h q) = (p.concat h).append q := by
  induction p <;> simp_all [concat_nil]

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
    | cons =>
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

/-! ## Subwalks -/

/-- `p.Subwalk q` if `p` is a not necessarily contiguous subwalk of `q`
(This definition is modelled on `List.Sublist`.) -/
inductive Subwalk {V : Type*} {G : SimpleGraph V} : ∀ {u v x y}, G.Walk u v → G.Walk x y → Prop
  /-- The nil walk `u` is a Subwalk of any `u - v` walk. -/
  | nil {u v: V} {q : G.Walk u v} : (Walk.nil' u).Subwalk q
  /-- If `p` is a Subwalk of `q`, then it is also a Subwalk of `q.cons h`. -/
  | cons {u v x y z : V} {p :  G.Walk u v} {q : G.Walk x y} (h : G.Adj z x) :
      p.Subwalk q → p.Subwalk (q.cons h)
  /-- If `p` is a Subwalk of `q`, then `p.cons hp` is a Subwalk of `q.cons hp`. -/
  | cons₂ {u v y z : V} {p :  G.Walk u v} {q : G.Walk u y} (h : G.Adj z u) :
      p.Subwalk q → (p.cons h).Subwalk (q.cons h)

/- ?? How do I open this notation rather than reintroducing it -/
@[inherit_doc] scoped infixl:50 " <+ " => List.Sublist

/-- The support of a Subwalk is a Sublist of the support -/
lemma Subwalk.support_sublist {u v x y : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : p.Subwalk q) : p.support <+ q.support :=
  Subwalk.rec (by simp) (by simp_all) (by simp) hs

/-- The darts of a Subwalk are a Sublist of the darts -/
lemma Subwalk.darts_sublist {u v x y : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : p.Subwalk q) : p.darts <+ q.darts :=
  Subwalk.rec (by simp) (by simp_all) (by simp) hs

/-- The edges of a Subwalk are a Sublist of the edges -/
lemma Subwalk.edges_sublist {u v x y : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : p.Subwalk q) : p.edges <+ q.edges :=
  Subwalk.rec (by simp) (by simp_all) (by simp) hs

lemma Subwalk.length_le  {u v x y : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : p.Subwalk q) : p.length ≤ q.length := by
  apply Nat.add_one_le_add_one_iff.1
  simp_rw [← length_support]
  exact hs.support_sublist.length_le

lemma Subwalk.count_le [DecidableEq V] {u v x y : V} {p : G.Walk u v} {q : G.Walk x y} (z : V)
    (hs : p.Subwalk q) : p.support.count z ≤ q.support.count z :=
  (hs.support_sublist).count_le _

/-- Any Subwalk of a trail is a trail -/
lemma IsTrail.of_subwalk {u v x y : V} {p : G.Walk u v} {q : G.Walk x y} (h : p.Subwalk q)
    (ht : q.IsTrail) : p.IsTrail := IsTrail.mk <| h.edges_sublist.nodup ht.edges_nodup

/-- Any non-nil closed Subwalk of a trail is a circuit -/
lemma IsCircuit.of_subwalk {u x y : V} {p : G.Walk u u} {q : G.Walk x y} (h : p.Subwalk q)
    (hn : ¬ p.Nil) (ht : q.IsTrail) : p.IsCircuit :=
  IsCircuit.mk (ht.of_subwalk h) (fun _ ↦ hn (by simp_all))

/-- Any Subwalk of a path is a path -/
lemma IsPath.of_subwalk {u v x y : V} {p : G.Walk u v} {q : G.Walk x y} (h : p.Subwalk q)
    (ht : q.IsPath) : p.IsPath := IsPath.mk' <| h.support_sublist.nodup ht.support_nodup

/-- `p <+ p` -/
@[refl, simp]
lemma Subwalk.refl {u v : V} (p : G.Walk u v) : p.Subwalk p  := by
  induction p with
  | nil => exact .nil
  | cons h _ ih => exact ih.cons₂ h

@[simp]
lemma subwalk_nil_iff {u v x : V} {q : G.Walk u v} :
    q.Subwalk (nil' x) ↔ q.Nil ∧ u = x ∧ v = x := by
  constructor
  · intro h
    cases h; simp
  · rintro ⟨hn, rfl, rfl⟩
    simp_all [nil_iff_eq_nil.1 hn]

@[simp]
lemma nil_subwalk {u v x : V} {q : G.Walk u v} (hx : x ∈ q.support) :
  (nil' x).Subwalk q := by
  induction q with
  | nil => simp_all
  | cons _ _ ih =>
    rw [support_cons, List.mem_cons] at *
    obtain (rfl | hx) := hx
    · exact .nil
    · exact (ih hx).cons _

@[simp]
lemma nil_subwalk_iff {u v x : V} {q : G.Walk u v} :
    (nil' x).Subwalk  q ↔ x ∈ q.support := by
  constructor <;> intro h
  · induction q <;> cases h <;> simp_all
  · simp [h]

/-- If `p <+ q` then `p <+ q.cons h` -/
@[simp]
lemma Subwalk.cons' {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : p.Subwalk q) (h : G.Adj z x) : p.Subwalk (q.cons h) := hs.cons h

/-- If `p <+ q` then `p.cons h <+ q.cons h` -/
@[simp]
lemma Subwalk.cons₂' {u v y z : V} {p : G.Walk u v} {q : G.Walk u y}
    (hs : p.Subwalk q) (h : G.Adj z u) : (p.cons h).Subwalk (q.cons h) := hs.cons₂ h

/-- If `p <+ q` then `r ++ p <+ q` -/
@[simp]
lemma Subwalk.append_left {u v x y s : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : p.Subwalk q) (r : G.Walk s x) : p.Subwalk (r.append q) := by
  induction r <;> simp_all

/-- If `z :: p <+ q` then `p <+ q` -/
@[simp]
lemma Subwalk.of_cons {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (h : G.Adj z u) (hs :  (p.cons h).Subwalk q) : p.Subwalk q := by
  induction q <;> cases hs <;> simp_all

/--
If `p.cons hp <+ q.cons hq` and `hp , hq` are darts from distinct vertices then `p.cons h <+ q`
-/
@[simp]
lemma Subwalk.of_cons₂_of_ne {u v x y z t : V} {p : G.Walk u v} {q : G.Walk x y}
    (hp : G.Adj z u) (hq : G.Adj t x) (hs : (p.cons hp).Subwalk (q.cons hq))
    (hne : z ≠ t) : (p.cons hp).Subwalk q := by cases hs <;> trivial

/--
If `p.cons hp <+ q.cons hq` and `hp , hq` are darts to distinct vertices then `p.cons h <+ q`
-/
@[simp]
lemma Subwalk.of_cons₂_of_ne_snd {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hp : G.Adj z u) (hq : G.Adj z x) (hs : (p.cons hp).Subwalk (q.cons hq))
    (hne : u ≠ x) : (p.cons hp).Subwalk q := by cases hs <;> simp_all

@[simp]
lemma Subwalk.of_cons₂ {u v y z : V} {p : G.Walk u v} {q : G.Walk u y}
    (hz : G.Adj z u) (hs : (p.cons hz).Subwalk (q.cons hz)) : p.Subwalk q := by
  cases p with
  | nil => simp
  | cons h p => exact (hs.of_cons _).of_cons₂_of_ne _ _  hz.ne.symm

/-- If `r ++ p <+ r ++ q` then `p <+ q` -/
@[simp]
lemma Subwalk.of_append_left {x u v y : V} {p : G.Walk u v}
    {q : G.Walk u y} (r : G.Walk x u) (hs : (r.append p).Subwalk (r.append q)) : p.Subwalk q := by
  induction r with
  | nil => simpa
  | cons h p ih => exact ih <| hs.of_cons₂ _

/-- If `p <+ q` then `p <+ q.concat h` -/
@[simp]
lemma Subwalk.concat {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : p.Subwalk q) (h : G.Adj y z) : p.Subwalk (q.concat h) := by
  induction q generalizing u v <;> cases hs <;> simp_all

/-- If `p <+ q` then `p.concat h <+ q.concat h` -/
@[simp]
lemma Subwalk.concat₂ {u v x z : V} {p : G.Walk u v} {q : G.Walk x v}
    (hs : p.Subwalk q) (h : G.Adj v z) : (p.concat h).Subwalk (q.concat h) := by
  induction q generalizing u with
  | nil => cases hs ; simp_all [concat_eq_append]
  | cons h' _ ih =>
    cases hs with
    | nil => exact (ih (by simp) h).cons h'
    | cons _ _ => simp_all [concat_eq_append]
    | cons₂ _ _ => simp_all [concat_eq_append]


/-- If `p <+ q` then `p <+ q ++ r` -/
@[simp]
lemma Subwalk.append_right {u v x y s : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : p.Subwalk q) (r : G.Walk y s) : p.Subwalk (q.append r) := by
  induction r <;> simp_all [append_cons_eq_concat_append]

/-- If `p <+ q` then `p.reverse <+ q.reverse` -/
lemma Subwalk.reverse {u v x y : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : p.Subwalk q) : p.reverse.Subwalk q.reverse := by
  induction q generalizing u with
  | nil => simp_all
  | @cons a b _ h q ih =>
    rw [reverse_cons, append_cons_eq_concat_append, append_nil]
    by_cases ha : u = a
    · subst ha
      cases p with
      | nil => simp_all
      | @cons _ w _ _ p =>
      rw [reverse_cons, append_cons_eq_concat_append, append_nil]
      by_cases hwb : w = b
      · subst hwb
        apply (ih <| hs.of_cons₂ h).concat₂
      · apply (reverse_cons _ _ ▸ ih <| hs.of_cons₂_of_ne_snd _ h hwb).concat
    · have : p.Subwalk q := by
        cases p with
        | nil => simp_all
        | cons => exact hs.of_cons₂_of_ne _ _ ha
      exact (ih this).concat _

/-- If `p.concat h <+ q` then `p <+ q` -/
@[simp]
lemma Subwalk.of_concat {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (h : G.Adj v z) (hs : (p.concat h).Subwalk q) : p.Subwalk q := by
  have := hs.reverse
  simp only [reverse_concat] at this
  simpa using (this.of_cons h.symm).reverse


/-- If `p.concat h <+ q.concat h` then `p <+ q` -/
@[simp]
lemma Subwalk.of_concat₂ {u v x y  : V} {p : G.Walk u v} {q : G.Walk x v}
    (h : G.Adj v y) (hs : (p.concat h).Subwalk (q.concat h)) : p.Subwalk q := by
  have := hs.reverse
  simp only [reverse_concat] at this
  simpa using (this.of_cons₂ h.symm).reverse

/--
If `p.concat hp <+ q.concat hq` and the end of the darts `hp` and `hq` differ then
`p.concat hp <+ q`
-/
@[simp]
lemma Subwalk.of_concat₂_of_ne {u v x y z t : V} {p : G.Walk u v} {q : G.Walk x y} (hp : G.Adj v z)
    (hq : G.Adj y t) (h : (p.concat hp).Subwalk (q.concat hq)) (hne : z ≠ t) :
    (p.concat hp).Subwalk q := by
  have := Subwalk.reverse h
  simp only [reverse_concat] at this
  simpa using (this.of_cons₂_of_ne hp.symm hq.symm hne).reverse

/--
If `p.concat hp <+ q.concat hq` and the start of the darts `hp` and `hq` differ then
`p.concat hp <+ q`
-/
@[simp]
lemma Subwalk.of_concat₂_of_ne_fst {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hp : G.Adj v z) (hq : G.Adj y z) (hs : (p.concat hp).Subwalk (q.concat hq)) (hne : v ≠ y) :
    (p.concat hp).Subwalk q := by
  have := hs.reverse
  simp only [reverse_concat] at this
  simpa using (this.of_cons₂_of_ne_snd hp.symm hq.symm hne).reverse

/-- If `p ++ r <+ q ++ r` then `p <+ q` -/
@[simp]
lemma Subwalk.of_append_right {x u v y : V} {p : G.Walk u v} {q : G.Walk x v}
    (r : G.Walk v y) (hs : (p.append r).Subwalk (q.append r)) : p.Subwalk q := by
  have := hs.reverse
  simp only [reverse_append] at this
  simpa using (this.of_append_left r.reverse).reverse

/-- *Tranisitivity of Subwalks* -/
@[trans, simp]
theorem Subwalk.trans {u₁ v₁ u₂ v₂ u₃ v₃ : V} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂}
    {p₃ : G.Walk u₃ v₃} (h₁ : p₁.Subwalk p₂) (h₂ : p₂.Subwalk p₃) : p₁.Subwalk p₃ := by
  induction h₂ generalizing u₁ with
  | nil =>
    rw [subwalk_nil_iff] at *
    obtain ⟨hp, rfl, rfl⟩ := h₁
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
        · exact (ih <| h₁.of_cons₂_of_ne_snd _ _ hea).cons h'
    · cases p₁ with
    | nil => simp_all
    | cons h' p => exact (ih <| h₁.of_cons₂_of_ne _ _ hud).cons _

/--
If p <+ q and q <+ p then p = q, but we state this as equality of supports to avoid complications.
-/
lemma Subwalk.antisymm {u v x y : V} {p : G.Walk u v} {q : G.Walk x y} (h1 : p.Subwalk q)
    (h2 : q.Subwalk p) : p.support = q.support :=
  List.Sublist.antisymm h1.support_sublist h2.support_sublist

/-- If `p <+ q` then `r ++ p <+ q` -/
@[simp]
lemma Subwalk.append_left_left {u v x y : V} {p : G.Walk u v} {q : G.Walk u y}
    (hs : p.Subwalk q) (r : G.Walk x u) : (r.append p).Subwalk (r.append q) := by
  induction r <;> simp_all

/-- If `p <+ q` then `p ++ r <+ q ++ r` -/
@[simp]
lemma Subwalk.append_right_right {u v x y : V} {p : G.Walk u v} {q : G.Walk x v}
    (hs : p.Subwalk q) (r : G.Walk v y) : (p.append r).Subwalk (q.append r) := by
  have := hs.reverse
  simp only [reverse_append] at this
  simpa using (this.append_left_left r.reverse).reverse

/--
If `p₁ <+ q₁` and `p₂ <+ q₂` then `p₁ ++ p₂ <+ q₁ ++ q₂` (if these are well-defined and the `++`
in both cases happens at a common vertex `x`.)
-/
theorem SubWalk.append {u₁ u₂ v₁ v₂ x : V} {p₁ : G.Walk u₁ x} {p₂ : G.Walk x u₂}
    {q₁ : G.Walk v₁ x} {q₂ : G.Walk x v₂} (h1 : p₁.Subwalk q₁) (h2 : p₂.Subwalk q₂) :
    (p₁.append p₂).Subwalk (q₁.append q₂) :=
  (h1.append_right_right p₂).trans <| h2.append_left_left q₁

---------------- Infix / Prefix / Suffix walks

/-- `p.Infix q` means that the walk `p` is a contiguous Subwalk of the walk `q`. -/
def Infix {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) : Prop :=
  ∃ (ru : G.Walk u₂ u₁) (rv : G.Walk v₁ v₂), q = (ru.append p).append rv

@[simp]
lemma Infix.refl {u₁ v₁} (p : G.Walk u₁ v₁) : p.Infix p := ⟨nil' u₁, nil' v₁, by simp⟩

/-- `p.Prefix q` means that the walk `q` starts with the walk `p`. -/
def Prefix {u v₁ v₂} (p : G.Walk u v₁) (q : G.Walk u v₂) : Prop :=
  ∃ (r : G.Walk v₁ v₂), q = p.append r

@[simp]
lemma Prefix.nil {u v} (q : G.Walk u v) : (nil' u).Prefix q := ⟨q, rfl⟩

/-- If `p.cons h <+: q.cons h'` then `p` and `q` have equal starts -/
lemma Prefix.eq_of_cons {u₁ u₂ x v₁ v₂} {p : G.Walk x v₁} {q : G.Walk u₂ v₂} (h : G.Adj u₁ x)
    (h' : G.Adj u₁ u₂) (hp : (cons h p).Prefix (cons h' q)) : u₂ = x := by
  obtain ⟨_, hr⟩ := hp
  rw [cons_append, cons.injEq] at hr
  exact hr.1

/-- `p.cons h <+: q.cons h` iff `p <+: q` -/
lemma prefix_cons_iff {u₁ u₂ v₁ v₂} {p : G.Walk u₂ v₁} {q : G.Walk u₂ v₂} (h : G.Adj u₁ u₂) :
    (cons h p).Prefix (cons h q) ↔ p.Prefix q := by
  constructor <;> intro ⟨r, hr⟩ <;> exact ⟨r, by simp_all⟩

lemma prefix_iff_support {u v₁ v₂} (p : G.Walk u v₁) (q : G.Walk u v₂) :
    p.Prefix q ↔ p.support <+: q.support := by
  induction p with
  | nil =>
    simp_rw [Prefix.nil, support_nil, true_iff]
    rw [support_eq_cons]
    simp
  | @cons _ y _ _ r ih =>
    constructor <;> intro h'
    · cases q with
    | nil =>
      obtain ⟨_, hr'⟩ := h'
      simp at hr'
    | cons _ q =>
      have := h'.eq_of_cons _ _
      subst this
      simpa using (ih q).1 <| (prefix_cons_iff _).1 h'
    · cases q with
    | nil => simp at h'
    | @cons _ b _ h'' p =>
      simp only [support_cons, List.cons_prefix_cons, true_and] at h'
      have : y = b := by
        rw [support_eq_cons, support_eq_cons p, List.cons_prefix_cons] at h'
        exact h'.1
      subst this
      apply (prefix_cons_iff _).2 <| (ih _).2 h'

/-- `p.Suffix q` means that the walk `q` ends with the walk `p`. -/
def Suffix {u₁ u₂ v} (p : G.Walk u₂ v) (q : G.Walk u₁ v) : Prop :=
  ∃ (r : G.Walk u₁ u₂), q = r.append p

lemma suffix_iff_reverse_prefix {u₁ u₂ v} (p : G.Walk u₂ v) (q : G.Walk u₁ v) :
    p.Suffix q ↔ p.reverse.Prefix q.reverse := by
  constructor <;> intro ⟨r, hr⟩ <;>
  · apply_fun Walk.reverse at hr
    use r.reverse
    simpa using hr

lemma suffix_iff_support {u₁ u₂ v} (p : G.Walk u₂ v) (q : G.Walk u₁ v) :
    p.Suffix q ↔ p.support <:+ q.support := by
  simp [suffix_iff_reverse_prefix, prefix_iff_support]

lemma infix_iff_exists_prefix_append {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) :
  p.Infix q ↔ ∃ r : G.Walk u₂ u₁, (r.append p).Prefix q := by
  constructor <;> intro ⟨r, ⟨s, hs⟩⟩ <;>
  · use r, s

lemma infix_iff_exists_suffix_append {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) :
  p.Infix q ↔ ∃ s : G.Walk v₁ v₂, (p.append s).Suffix q := by
  constructor <;> intro ⟨r, ⟨s, hs⟩⟩ <;>
  · exact ⟨s, r, by rw [hs, append_assoc]⟩

lemma Prefix.infix {u v₁ v₂} {p : G.Walk u v₁} {q : G.Walk u v₂} (h : p.Prefix q) : p.Infix q := by
  obtain ⟨r, hr⟩ := h
  exact ⟨nil' _ ,r , by simpa⟩

lemma Suffix.infix {u₁ u₂ v} {p : G.Walk u₁ v} {q : G.Walk u₂ v} (h : p.Suffix q) : p.Infix q := by
  obtain ⟨s, hr⟩ := h
  exact ⟨s, nil' _, by simpa⟩

lemma infix_iff_support {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) :
    p.Infix q ↔ p.support <:+: q.support := by
  constructor
  · intro ⟨r, s, hrs⟩
    have hs : (p.append s).Suffix q := ⟨r, by rwa [append_assoc]⟩
    have hs := (suffix_iff_support _ _).1 hs
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
      have := (prefix_iff_support _ _).2 hpre
      rw [infix_iff_exists_prefix_append]
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

lemma infix_infix_iff_support {u₁ v₁ u₂ v₂} {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} :
    p.Infix q ∧ q.Infix p ↔ p.support = q.support := by
  simp_rw [← List.infix_infix_iff, infix_iff_support]

lemma infix_iff_reverse {u₁ v₁ u₂ v₂} {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} :
    p.Infix q ↔ p.reverse.Infix q.reverse := by
  constructor <;> intro ⟨r, s, h⟩
  · use s.reverse, r.reverse
    rw [h]
    simp [append_assoc]
  · use s.reverse, r.reverse
    apply_fun Walk.reverse at h
    rw [reverse_reverse] at h
    rw [h]
    simp [append_assoc]

alias ⟨Infix.reverse, _⟩ := infix_iff_reverse

lemma infix_antisymm_iff {u₁ v₁ u₂ v₂} {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} :
    p.Infix q ∧ q.Infix p ↔ ∃ hu hv, p.copy hu hv = q := by
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

alias ⟨Infix.antisymm, _⟩ := infix_antisymm_iff

lemma cons_eq_cons {u v₁ v₂ w} (p₁ : G.Walk v₁ w) (p₂ : G.Walk v₂ w) (h₁ : G.Adj u v₁)
    (h₂ : G.Adj u v₂) : cons h₁ p₁ = cons h₂ p₂ ↔ ∃ h', p₁.copy h' rfl = p₂ := by
  constructor <;> rintro ⟨rfl, hp⟩ <;> simp_all

lemma Infix.subwalk {u₁ v₁ u₂ v₂} {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂}
    (h : p.Infix q) : p.Subwalk q := by
  obtain ⟨r, s, h⟩ := h
  rw [← append_assoc] at h
  exact h ▸ ((Subwalk.refl p).append_right s).append_left r

/-- `p ++ r <+ p ++ q ++ r` i.e. removing a loop from a walk yields a subwalk. -/
lemma Subwalk.of_prefix_append_suffix {u₁ u₂ u₃} {p : G.Walk u₁ u₂} {q : G.Walk u₂ u₂}
    {r : G.Walk u₂ u₃} : (p.append r).Subwalk (p.append (q.append r)) :=
  ((Subwalk.refl r).append_left  q).append_left_left p

lemma takeUntil_prefix [DecidableEq V] {u v x : V} {p : G.Walk u v} (hx : x ∈ p.support) :
  (p.takeUntil _ hx).Prefix p := ⟨_, (take_spec p hx).symm⟩

lemma dropUntil_suffix [DecidableEq V] {u v x : V} {p : G.Walk u v} (hx : x ∈ p.support) :
  (p.dropUntil _ hx).Suffix p := ⟨_, (take_spec p hx).symm⟩

lemma Prefix.subwalk {u v w : V} {p : G.Walk u v} {q : G.Walk u w} (h : p.Prefix q) :
    p.Subwalk q := h.infix.subwalk

lemma Suffix.subwalk {u v w : V} {p : G.Walk u w} {q : G.Walk v w} (h : p.Suffix q) :
    p.Subwalk q := h.infix.subwalk


/-! ## Rotated Subwalks -/


variable [DecidableEq V]

/--
`p` is a rotated subwalk of `q` if it is a rotation of a subwalk

-/
def RotatedSubwalk {u v w : V} (p : G.Walk u u) (q : G.Walk v w) : Prop :=
    ∃ (x : V) (r : G.Walk x x) (hu : u ∈ r.support), r.Subwalk q ∧ p = r.rotate hu

@[simp]
lemma RotatedSubwalk.nil (u : V) : (nil' u : G.Walk u u).RotatedSubwalk (nil' u) :=
  ⟨u, nil' u, by simp⟩

/-- Any subwalk is trivial a rotated subwalk -/
lemma Subwalk.rotated {u v w : V} {p : G.Walk u u} {q : G.Walk v w} (h : p.Subwalk q) :
    p.RotatedSubwalk q := by use u; simpa

lemma RotatedSubwalk.support_subset {u v w : V} {p : G.Walk u u} {q : G.Walk v w}
    (h : p.RotatedSubwalk q) : p.support ⊆ q.support := by
  obtain ⟨_, _, _, hr1, rfl⟩ := h
  intro _ hy
  exact hr1.support_sublist.mem (by rwa [← mem_support_rotate_iff] )

lemma RotatedSubwalk.darts_subset {u v w : V} {p : G.Walk u u} {q : G.Walk v w}
    (h : p.RotatedSubwalk q) : p.darts ⊆ q.darts := by
  obtain ⟨_, _, hx, hr1, rfl⟩ := h
  intro _ hy
  exact hr1.darts_sublist.mem <| (rotate_darts _ hx).symm.mem_iff.2 hy

lemma RotatedSubwalk.edges_subset {u v w : V} {p : G.Walk u u} {q : G.Walk v w}
    (h : p.RotatedSubwalk q) : p.edges ⊆ q.edges := by
  obtain ⟨_, _, hx, hr1, rfl⟩ := h
  intro _ hy
  exact hr1.edges_sublist.mem <| (rotate_edges _ hx).symm.mem_iff.2 hy

lemma RotatedSubwalk.length_le {u v w : V} {p : G.Walk u u} {q : G.Walk v w}
    (h : p.RotatedSubwalk q) : p.length ≤ q.length := by
  obtain ⟨x, r, hx, hr1, rfl⟩ := h
  exact length_rotate hx ▸ hr1.length_le


/- We also sometimes care about rotated subwalks of rotated walks -/

lemma RotatedSubwalk.support_subset_rotate {u v y : V} {p : G.Walk u u} {q : G.Walk v v}
    (hy : y ∈ q.support ) (h : p.RotatedSubwalk (q.rotate hy)) : p.support ⊆ q.support :=
  h.support_subset.trans (fun _ hz ↦ (mem_support_rotate_iff hy).mp hz)

lemma RotatedSubwalk.darts_subset_rotate {u v y : V} {p : G.Walk u u} {q : G.Walk v v}
    (hy : y ∈ q.support ) (h : p.RotatedSubwalk (q.rotate hy)) : p.darts ⊆ q.darts :=
  h.darts_subset.trans (fun _ hz ↦ (rotate_darts _ hy).symm.mem_iff.2 hz)

lemma RotatedSubwalk.edges_subset_rotate {u v y : V} {p : G.Walk u u} {q : G.Walk v v}
    (hy : y ∈ q.support ) (h : p.RotatedSubwalk (q.rotate hy)) : p.edges ⊆ q.edges :=
  h.edges_subset.trans (fun _ hz ↦ (rotate_edges _ hy).symm.mem_iff.2 hz)

lemma RotatedSubwalk.length_le_rotate {u v y : V} {p : G.Walk u u} {q : G.Walk v v}
    (hy : y ∈ q.support ) (h : p.RotatedSubwalk (q.rotate hy)): p.length ≤ q.length :=
  length_rotate hy ▸ h.length_le





end SimpleGraph.Walk
