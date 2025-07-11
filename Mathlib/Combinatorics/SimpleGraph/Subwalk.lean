import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Mathlib.Combinatorics.SimpleGraph.Paths

variable {V : Type*}

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
      obtain ⟨rfl, rfl⟩ := ih (by simpa using hp) (by simpa using hl)
      simp

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

/-- `p.Subwalk q` if `p` is a (not necessarily contiguous) subwalk of `q`
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
lemma Subwalk.support {u v x y : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : p.Subwalk q) : p.support <+ q.support :=
  Subwalk.rec (by simp) (by simp_all) (by simp) hs

/-- The darts of a Subwalk are a Sublist of the darts -/
lemma Subwalk.darts {u v x y : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : p.Subwalk q) : p.darts <+ q.darts :=
  Subwalk.rec (by simp) (by simp_all) (by simp) hs

/-- The edges of a Subwalk are a Sublist of the edges -/
lemma Subwalk.edges {u v x y : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : p.Subwalk q) : p.edges <+ q.edges :=
  Subwalk.rec (by simp) (by simp_all) (by simp) hs

lemma Subwalk.length_le  {u v x y : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : p.Subwalk q) : p.length ≤ q.length := by
  apply Nat.add_one_le_add_one_iff.1
  simp_rw [← length_support]
  exact hs.support.length_le

lemma Subwalk.count_le [DecidableEq V] {u v x y : V} {p : G.Walk u v} {q : G.Walk x y} (z : V)
    (hs : p.Subwalk q) : p.support.count z ≤ q.support.count z :=
  (hs.support).count_le _

/-- Any Subwalk of a trail is a trail -/
lemma IsTrail.of_subwalk {u v x y : V} {p : G.Walk u v} {q : G.Walk x y} (h : p.Subwalk q)
    (ht : q.IsTrail) : p.IsTrail := IsTrail.mk <| h.edges.nodup ht.edges_nodup

/-- Any non-nil closed Subwalk of a trail is a circuit -/
lemma IsCircuit.of_subwalk {u x y : V} {p : G.Walk u u} {q : G.Walk x y} (h : p.Subwalk q)
    (hn : ¬ p.Nil) (ht : q.IsTrail) : p.IsCircuit :=
  IsCircuit.mk (ht.of_subwalk h) (fun _ ↦ hn (by simp_all))

/-- Any Subwalk of a path is a path -/
lemma IsPath.of_subwalk {u v x y : V} {p : G.Walk u v} {q : G.Walk x y} (h : p.Subwalk q)
    (ht : q.IsPath) : p.IsPath := IsPath.mk' <| h.support.nodup ht.support_nodup

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
  · simp [nil_subwalk, h]

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
If `p <+ q.cons h` where `p: G.Walk u v`, `h : G.Adj a x` and `u ≠ a` then `p <+ q`
-/
@[simp]
lemma Subwalk.of_cons_of_ne {u v x y a : V} {p : G.Walk u v} {q : G.Walk x y} (hq : G.Adj a x)
    (hs : p.Subwalk (q.cons hq)) (hne : u ≠ a) : p.Subwalk q := by
  induction q <;> cases hs <;> simp_all
/--
If `p.cons hp <+ q.cons hq` and `hp, hq` are darts to distinct vertices then `p.cons h <+ q`
-/
@[simp]
lemma Subwalk.of_cons₂_of_ne {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hp : G.Adj z u) (hq : G.Adj z x) (hs : (p.cons hp).Subwalk (q.cons hq))
    (hne : u ≠ x) : (p.cons hp).Subwalk q := by cases hs <;> simp_all

/--
If `p.cons h <+ q.cons h` then `p <+ q`
-/
@[simp]
lemma Subwalk.of_cons₂ {u v y z : V} {p : G.Walk u v} {q : G.Walk u y}
    (hz : G.Adj z u) (hs : (p.cons hz).Subwalk (q.cons hz)) : p.Subwalk q := by
  cases p with
  | nil => simp
  | cons h p => exact (hs.of_cons _).of_cons_of_ne _ hz.ne.symm

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
  | nil => cases hs; simp_all [concat_eq_append]
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
      | nil => simp
      | @cons _ w _ _ p =>
      rw [reverse_cons, append_cons_eq_concat_append, append_nil]
      by_cases hwb : w = b
      · subst hwb
        exact (ih <| hs.of_cons₂ h).concat₂ _
      · exact (reverse_cons _ _ ▸ ih <| hs.of_cons₂_of_ne _ h hwb).concat _
    · have : p.Subwalk q := by
        cases p with
        | nil => simp_all
        | cons => exact hs.of_cons_of_ne _ ha
      exact (ih this).concat _

/-- If `p.concat h <+ q` then `p <+ q` -/
@[simp]
lemma Subwalk.of_concat {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (h : G.Adj v z) (hs : (p.concat h).Subwalk q) : p.Subwalk q := by
  have := hs.reverse
  rw [reverse_concat] at this
  simpa using (this.of_cons h.symm).reverse

/-- If `p.concat h <+ q.concat h` then `p <+ q` -/
@[simp]
lemma Subwalk.of_concat₂ {u v x y  : V} {p : G.Walk u v} {q : G.Walk x v}
    (h : G.Adj v y) (hs : (p.concat h).Subwalk (q.concat h)) : p.Subwalk q := by
  have := hs.reverse
  simp only [reverse_concat] at this
  simpa using (this.of_cons₂ h.symm).reverse

/--
If `p <+ q.concat hq` and `p : G.Walk u v` and `hq : G.Adj y t` with `v ≠ t` differ then `p <+ q`
-/
@[simp]
lemma Subwalk.of_concat_of_ne {u v x y t : V} {p : G.Walk u v} {q : G.Walk x y} (hq : G.Adj y t)
     (h : p.Subwalk (q.concat hq)) (hne : v ≠ t) :
    p.Subwalk q := by
  have := Subwalk.reverse h
  simp only [reverse_concat] at this
  simpa using (this.of_cons_of_ne hq.symm hne).reverse

/--
If `p.concat hp <+ q.concat hq` and the start of the darts `hp` and `hq` differ then
`p.concat hp <+ q`
-/
@[simp]
lemma Subwalk.of_concat₂_of_ne {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hp : G.Adj v z) (hq : G.Adj y z) (hs : (p.concat hp).Subwalk (q.concat hq)) (hne : v ≠ y) :
    (p.concat hp).Subwalk q := by
  have := hs.reverse
  simp only [reverse_concat] at this
  simpa using (this.of_cons₂_of_ne hp.symm hq.symm hne).reverse

/-- If `p ++ r <+ q ++ r` then `p <+ q` -/
@[simp]
lemma Subwalk.of_append_right {x u v y : V} {p : G.Walk u v} {q : G.Walk x v}
    (r : G.Walk v y) (hs : (p.append r).Subwalk (q.append r)) : p.Subwalk q := by
  have := hs.reverse
  simp only [reverse_append] at this
  simpa using (this.of_append_left r.reverse).reverse

/-- *Transitivity of Subwalks* -/
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
        · exact (ih <| h₁.of_cons₂_of_ne _ _ hea).cons h'
    · cases p₁ with
    | nil => simp_all
    | cons h' p => exact (ih <| h₁.of_cons_of_ne _ hud).cons _

/--
If `p <+ q` and `q <+ p` then `p.support = q.support`
-/
lemma Subwalk.antisymm_support {u v x y : V} {p : G.Walk u v} {q : G.Walk x y} (h1 : p.Subwalk q)
    (h2 : q.Subwalk p) : p.support = q.support :=
  List.Sublist.antisymm h1.support h2.support

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

/-- If `p <+ q` and `q <+ p` then `p = q` (mod casting endpoints) -/
theorem Subwalk.antisymm {u₁ u₂ v₁ v₂} {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} (h1 : p.Subwalk q)
    (h2 : q.Subwalk p) :  ∃ hu hv, p = q.copy hu hv := by
  induction p generalizing u₂ with
  | nil =>
    rw [nil_subwalk_iff] at h1
    rw [subwalk_nil_iff] at h2;
    obtain ⟨h2, rfl, rfl⟩ := h2
    simp [h2.eq_nil]
  | @cons a b _ hp _ ih =>
    cases q with
    | nil => simp at h1
    | @cons _ e _ hq _ =>
      by_cases hau : a = u₂
      · subst hau
        by_cases hbe : b = e
        · subst hbe
          obtain ⟨_, rfl, rfl⟩ := ih h1.of_cons₂ h2.of_cons₂
          simp
        · have h1 := (h1.of_cons₂_of_ne _ _ hbe).length_le
          have h2 := h2.length_le
          simp only [length_cons, Nat.add_le_add_iff_right] at h1 h2
          omega
      · have h1 := (h1.of_cons_of_ne _ hau).length_le
        have h2 := h2.length_le
        simp only [length_cons, Nat.add_le_add_iff_right] at h1 h2
        omega


---------------- Infix / Prefix / Suffix walks

/-- `p.Infix q` means that the walk `p` is a contiguous Subwalk of the walk `q`. -/
def Infix {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) : Prop :=
  ∃ (ru : G.Walk u₂ u₁) (rv : G.Walk v₁ v₂), q = (ru.append p).append rv

/-- If `p <:+: q` then `p <+ q` -/
lemma Infix.subwalk {u₁ v₁ u₂ v₂} {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂}
    (h : p.Infix q) : p.Subwalk q := by
  obtain ⟨r, s, h⟩ := h
  rw [← append_assoc] at h
  exact h ▸ ((Subwalk.refl p).append_right s).append_left r

@[simp,refl]
lemma Infix.refl {u₁ v₁} (p : G.Walk u₁ v₁) : p.Infix p := ⟨nil' u₁, nil' v₁, by simp⟩

@[simp]
lemma Infix.nil {u v x} {q : G.Walk u v} (hx : x ∈ q.support) : (nil' x).Infix q := by
  classical
  use q.takeUntil _ hx, q.dropUntil _ hx
  simp [(take_spec _ hx)]

lemma Infix.of_nil {u v x} {q : G.Walk u v} (h : q.Infix (nil' x)) : q.Nil ∧ u = x ∧ v = x := by
  simpa using subwalk_nil_iff.1 h.subwalk

/-- `p.Prefix q` means that the walk `q` starts with the walk `p`. -/
def Prefix {u v₁ v₂} (p : G.Walk u v₁) (q : G.Walk u v₂) : Prop :=
  ∃ (r : G.Walk v₁ v₂), q = p.append r

/-- `p.Suffix q` means that the walk `q` ends with the walk `p`. -/
def Suffix {u₁ u₂ v} (p : G.Walk u₂ v) (q : G.Walk u₁ v) : Prop :=
  ∃ (r : G.Walk u₁ u₂), q = r.append p

@[simp,refl]
lemma Prefix.refl {u₁ v₁} (p : G.Walk u₁ v₁) : p.Prefix p := ⟨nil' v₁, by simp⟩

lemma Prefix.infix {u v₁ v₂} {p : G.Walk u v₁} {q : G.Walk u v₂} (h : p.Prefix q) : p.Infix q := by
  obtain ⟨r, hr⟩ := h
  exact ⟨nil' _ ,r , by simpa⟩

lemma Suffix.infix {u₁ u₂ v} {p : G.Walk u₁ v} {q : G.Walk u₂ v} (h : p.Suffix q) : p.Infix q := by
  obtain ⟨s, hr⟩ := h
  exact ⟨s, nil' _, by simpa⟩

@[simp,refl]
lemma Suffix.refl {u₁ v₁} (p : G.Walk u₁ v₁) : p.Suffix p := ⟨nil' u₁, by simp⟩

lemma Prefix.subwalk {u v w : V} {p : G.Walk u v} {q : G.Walk u w} (h : p.Prefix q) :
    p.Subwalk q := h.infix.subwalk

lemma Suffix.subwalk {u v w : V} {p : G.Walk u w} {q : G.Walk v w} (h : p.Suffix q) :
    p.Subwalk q := h.infix.subwalk

lemma Prefix.nil {u v} (q : G.Walk u v) : (nil' u).Prefix q := ⟨q, rfl⟩

lemma Prefix.of_nil {u v} {q : G.Walk u v} (h : q.Prefix (nil' u)) : q.Nil ∧ v = u := by
  simpa using subwalk_nil_iff.1 h.subwalk

lemma Suffix.nil {u v} (q : G.Walk u v) : (nil' v).Suffix q := ⟨q, by simp⟩

lemma Suffix.of_nil {u v} {q : G.Walk u v} (h : q.Suffix (nil' v)) : q.Nil ∧ u = v := by
  simpa using subwalk_nil_iff.1 h.subwalk

/-- `p.cons h <+: q.cons h` iff `p <+: q` -/
lemma prefix_cons_iff {u₁ u₂ v₁ v₂} {p : G.Walk u₂ v₁} {q : G.Walk u₂ v₂} (h : G.Adj u₁ u₂) :
    (cons h p).Prefix (cons h q) ↔ p.Prefix q := by
  constructor <;> intro ⟨r, hr⟩ <;> exact ⟨r, by simp_all⟩

lemma Prefix.support {u v₁ v₂} {p : G.Walk u v₁} {q : G.Walk u v₂} (h: p.Prefix q) :
  p.support <+: q.support := by
  obtain ⟨r, rfl⟩ := h
  use r.support.tail
  simp [support_append]

lemma prefix_of_support {u v₁ v₂} {p : G.Walk u v₁} {q : G.Walk u v₂}
    (h : p.support <+: q.support) : p.Prefix q := by
  induction p with
  | nil => exact Prefix.nil _
  | @cons _ y _ _ _ ih =>
    cases q with
    | nil => simp at h
    | @cons _ b _ _ p =>
      simp only [support_cons, List.cons_prefix_cons, true_and] at h
      have : y = b := by
        rw [support_eq_cons, support_eq_cons p, List.cons_prefix_cons] at h
        exact h.1
      subst this
      apply (prefix_cons_iff _).2 (ih h)

lemma prefix_iff_support {u v₁ v₂} {p : G.Walk u v₁} {q : G.Walk u v₂} :
    p.Prefix q ↔ p.support <+: q.support:= Iff.intro Prefix.support prefix_of_support

lemma suffix_iff_reverse_prefix {u₁ u₂ v} (p : G.Walk u₂ v) (q : G.Walk u₁ v) :
    p.Suffix q ↔ p.reverse.Prefix q.reverse := by
  constructor <;> intro ⟨r, hr⟩ <;>
  · apply_fun Walk.reverse at hr
    use r.reverse
    simpa using hr

lemma suffix_iff_support {u₁ u₂ v} (p : G.Walk u₂ v) (q : G.Walk u₁ v) :
    p.Suffix q ↔ p.support <:+ q.support := by
  simp_rw [suffix_iff_reverse_prefix, prefix_iff_support, support_reverse, List.reverse_prefix]

lemma infix_iff_exists_prefix_append {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) :
  p.Infix q ↔ ∃ r : G.Walk u₂ u₁, (r.append p).Prefix q := by
  constructor <;> intro ⟨r, ⟨s, hs⟩⟩ <;>
  · use r, s

lemma infix_iff_exists_suffix_append {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) :
  p.Infix q ↔ ∃ s : G.Walk v₁ v₂, (p.append s).Suffix q := by
  constructor <;> intro ⟨r, ⟨s, hs⟩⟩ <;>
  · exact ⟨s, r, by rw [hs, append_assoc]⟩

lemma support_append' {u v w} {p : G.Walk u v} {q : G.Walk v w} :
    (p.append q).support = p.support.dropLast ++ q.support := by
  apply_fun List.reverse using List.reverse_injective
  rw [List.reverse_append, ← support_reverse, ← support_reverse, reverse_append, support_append]
  apply (List.append_right_inj _).2
  rw [support_reverse, support_eq_cons, List.tail_reverse]

lemma Infix.support {u₁ v₁ u₂ v₂} {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} (h : p.Infix q) :
    p.support <:+: q.support := by
  obtain ⟨r , s, rfl⟩ := h
  use r.support.dropLast, s.support.tail
  rw [support_append, support_append']

/--
Note the analogous result is false for Subwalks : `[a, b] <+ [a, x, b]` as lists of vertices,
but the single edge walk from `a` to `b` is not a subwalk of the two edge walk from
`a` to `b` via `x`.
-/
lemma infix_of_support {u₁ v₁ u₂ v₂} {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂}
    (h : p.support <:+: q.support) : p.Infix q := by
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
      exact (prefix_of_support hpre).infix
    | inr h =>
      obtain ⟨r, s, hr⟩ := ih h
      use (cons h' r), s
      simpa

lemma infix_iff_support {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) :
    p.Infix q ↔ p.support <:+: q.support := Iff.intro Infix.support infix_of_support

lemma infix_iff_reverse {u₁ v₁ u₂ v₂} {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} :
    p.Infix q ↔ p.reverse.Infix q.reverse := by
  constructor <;> intro ⟨r, s, h⟩ <;> use s.reverse, r.reverse
  · rw [h]
    simp [append_assoc]
  · apply_fun Walk.reverse at h
    simpa [append_assoc] using h

alias ⟨Infix.reverse, _⟩ := infix_iff_reverse

lemma Infix.antisymm {u₁ v₁ u₂ v₂} {p : G.Walk u₁ v₁} {q : G.Walk u₂ v₂} (h1 : p.Infix q)
    (h2 : q.Infix p) : ∃ hu hv, p = q.copy hu hv := Subwalk.antisymm h1.subwalk h2.subwalk

lemma takeUntil_prefix [DecidableEq V] {u v x : V} {p : G.Walk u v} (hx : x ∈ p.support) :
  (p.takeUntil _ hx).Prefix p := ⟨_, (take_spec p hx).symm⟩

lemma dropUntil_suffix [DecidableEq V] {u v x : V} {p : G.Walk u v} (hx : x ∈ p.support) :
  (p.dropUntil _ hx).Suffix p := ⟨_, (take_spec p hx).symm⟩

lemma take_prefix {u v : V} {p : G.Walk u v} (n : ℕ) : (p.take n).Prefix p :=
  ⟨_, (take_append_drop p n).symm⟩

lemma drop_suffix {u v : V} {p : G.Walk u v} (n : ℕ) : (p.drop n).Suffix p :=
  ⟨_, (take_append_drop p n).symm⟩

lemma tail_suffix {u v : V} (p : G.Walk u v) : p.tail.Suffix p := p.drop_suffix _

lemma dropLast_prefix {u v : V} (p : G.Walk u v) : p.dropLast.Prefix p := p.take_prefix _

lemma bypass_subwalk [DecidableEq V] {u v : V} (p : G.Walk u v) : p.bypass.Subwalk p := by
  induction p with
  | nil => rfl
  | cons _ p ih =>
    rw [bypass]
    split_ifs with h1
    · exact (p.bypass.dropUntil_suffix h1).subwalk.trans (ih.cons _)
    · exact ih.cons₂ _

/-- `p ++ r <+ p ++ q ++ r` i.e. removing a loop from a walk yields a subwalk. -/
lemma Subwalk.of_prefix_append_suffix {u₁ u₂ u₃} {p : G.Walk u₁ u₂} {q : G.Walk u₂ u₂}
    {r : G.Walk u₂ u₃} : (p.append r).Subwalk (p.append (q.append r)) :=
  ((Subwalk.refl r).append_left  q).append_left_left p

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

/-- Any closed subwalk is trivially a rotated subwalk -/
lemma Subwalk.rotated {u v w : V} {p : G.Walk u u} {q : G.Walk v w} (h : p.Subwalk q) :
    p.RotatedSubwalk q := by use u; simpa

lemma RotatedSubwalk.support_subset {u v w : V} {p : G.Walk u u} {q : G.Walk v w}
    (h : p.RotatedSubwalk q) : p.support ⊆ q.support := by
  obtain ⟨_, _, _, hr1, rfl⟩ := h
  intro _ hy
  exact hr1.support.mem (by rwa [← mem_support_rotate_iff] )

lemma RotatedSubwalk.darts_subset {u v w : V} {p : G.Walk u u} {q : G.Walk v w}
    (h : p.RotatedSubwalk q) : p.darts ⊆ q.darts := by
  obtain ⟨_, _, hx, hr1, rfl⟩ := h
  intro _ hy
  exact hr1.darts.mem <| (rotate_darts _ hx).symm.mem_iff.2 hy

lemma RotatedSubwalk.edges_subset {u v w : V} {p : G.Walk u u} {q : G.Walk v w}
    (h : p.RotatedSubwalk q) : p.edges ⊆ q.edges := by
  obtain ⟨_, _, hx, hr1, rfl⟩ := h
  intro _ hy
  exact hr1.edges.mem <| (rotate_edges _ hx).symm.mem_iff.2 hy

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
