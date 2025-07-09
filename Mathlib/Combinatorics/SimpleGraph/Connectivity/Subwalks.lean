import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp

namespace SimpleGraph.Walk

#check List.sublist_append_iff

/-! # Results about appending walks -/

variable {V : Type*} {G : SimpleGraph V}

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
  | nil {u v: V} {q : G.Walk u v} : Subwalk (Walk.nil' u) q
  /-- If `p` is a Subwalk of `q`, then it is also a Subwalk of `q.cons h`. -/
  | cons {u v x y z : V} {p :  G.Walk u v} {q : G.Walk x y} (h : G.Adj z x) :
      Subwalk p q → Subwalk p (q.cons h)
  /-- If `p` is a Subwalk of `q`, then `p.cons hp` is a Subwalk of `q.cons hp`. -/
  | cons₂ {u v y z : V} {p :  G.Walk u v} {q : G.Walk u y} (h : G.Adj z u) :
      Subwalk p q → Subwalk (p.cons h) (q.cons h)

/- ?? How do I open this notation rather than reintroducing it -/
@[inherit_doc] scoped infixl:50 " <+ " => List.Sublist

/-- The support of a Subwalk is a Sublist of the support -/
lemma Subwalk.support_sublist {u v x y : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : Subwalk p q) : p.support <+ q.support :=
  Subwalk.rec (by simp) (by simp_all) (by simp) hs

/-- The darts of a Subwalk are a Sublist of the darts -/
lemma Subwalk.darts_sublist {u v x y : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : Subwalk p q) : p.darts <+ q.darts :=
  Subwalk.rec (by simp) (by simp_all) (by simp) hs

/-- The edges of a Subwalk are a Sublist of the edges -/
lemma Subwalk.edges_sublist {u v x y : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : Subwalk p q) : p.edges <+ q.edges :=
  Subwalk.rec (by simp) (by simp_all) (by simp) hs

/-- `p <+ p` -/
@[refl, simp]
lemma Subwalk.refl {u v : V} (p : G.Walk u v) : Subwalk p p := by
  induction p with
  | nil => exact Subwalk.nil
  | cons h _ ih => exact Subwalk.cons₂ h ih

@[simp]
lemma subwalk_nil_iff {u v x : V} {q : G.Walk u v} :
    Subwalk q (nil' x) ↔ q.Nil ∧ u = x ∧ v = x := by
  constructor
  · intro h
    cases h; simp
  · rintro ⟨hn, rfl, rfl⟩
    simp_all [nil_iff_eq_nil.1 hn]

@[simp]
lemma nil_subwalk {u v x : V} {q : G.Walk u v} (hx : x ∈ q.support) :
  Subwalk (nil' x) q := by
  induction q with
  | nil => simp_all
  | cons _ _ ih =>
    rw [support_cons, List.mem_cons] at *
    obtain (rfl | hx) := hx
    · exact Subwalk.nil
    · exact Subwalk.cons _ (ih hx)

@[simp]
lemma nil_subwalk_iff {u v x : V} {q : G.Walk u v} :
    Subwalk (nil' x) q ↔ x ∈ q.support := by
  constructor <;> intro h
  · induction q <;> cases h <;> simp_all
  · simp [h]

/-- If `p <+ q` then `p <+ q.cons h` -/
@[simp]
lemma Subwalk.cons' {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : Subwalk p q) (h : G.Adj z x) :
    Subwalk p (q.cons h) := Subwalk.cons h hs

/-- If `p <+ q` then `p.cons h <+ q.cons h` -/
@[simp]
lemma Subwalk.cons₂' {u v y z : V} {p : G.Walk u v} {q : G.Walk u y}
    (hs : Subwalk p q) (h : G.Adj z u) :
    Subwalk (p.cons h) (q.cons h) := Subwalk.cons₂ h hs

/-- If `p <+ q` then `r ++ p <+ q` -/
@[simp]
lemma Subwalk.append_left {u v x y s : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : Subwalk p q) (r : G.Walk s x) :
    Subwalk p (r.append q) := by
  induction r <;> simp_all

/-- If `z :: p <+ q` then `p <+ q` -/
@[simp]
lemma Subwalk.of_cons {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (h : G.Adj z u) (hs : Subwalk (p.cons h) q) : Subwalk p q := by
  induction q <;> cases hs <;> simp_all

/--
If `p.cons hp <+ q.cons hq` and `hp , hq` are darts from distinct vertices then `p.cons h <+ q`
-/
@[simp]
lemma Subwalk.of_cons₂_of_ne {u v x y z t : V} {p : G.Walk u v} {q : G.Walk x y}
    (hp : G.Adj z u) (hq : G.Adj t x) (hs : Subwalk (p.cons hp) (q.cons hq))
    (hne : z ≠ t) : Subwalk (p.cons hp) q := by
  cases hs <;> trivial

/--
If `p.cons hp <+ q.cons hq` and `hp , hq` are darts to distinct vertices then `p.cons h <+ q`
-/
@[simp]
lemma Subwalk.of_cons₂_of_ne_snd {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hp : G.Adj z u) (hq : G.Adj z x) (hs : Subwalk (p.cons hp) (q.cons hq))
    (hne : u ≠ x) : Subwalk (p.cons hp) q := by
  cases hs <;> simp_all

@[simp]
lemma Subwalk.of_cons₂ {u v y z : V} {p : G.Walk u v} {q : G.Walk u y}
    (hz : G.Adj z u) (hs : Subwalk (p.cons hz) (q.cons hz)) :
    Subwalk p q := by
  cases p with
  | nil => simp
  | cons h p => exact (hs.of_cons _).of_cons₂_of_ne _ _  hz.ne.symm

/-- If `r ++ p <+ r ++ q` then `p <+ q` -/
@[simp]
lemma Subwalk.of_append_left {x u v y : V} {p : G.Walk u v}
    {q : G.Walk u y} (r : G.Walk x u) (hs : Subwalk (r.append p) (r.append q)) :
    Subwalk p q := by
  induction r with
  | nil => simpa
  | cons h p ih => exact ih <| hs.of_cons₂ _

/-- If `p <+ q` then `p <+ q.concat h` -/
@[simp]
lemma Subwalk.concat {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : Subwalk p q) (h : G.Adj y z) :
    Subwalk p (q.concat h) := by
  induction q generalizing u v <;> cases hs <;> simp_all

/-- If `p <+ q` then `p.concat h <+ q.concat h` -/
@[simp]
lemma Subwalk.concat₂ {u v x z : V} {p : G.Walk u v} {q : G.Walk x v}
    (hs : Subwalk p q) (h : G.Adj v z) :
    Subwalk (p.concat h) (q.concat h) := by
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
    (hs : Subwalk p q) (r : G.Walk y s) : Subwalk p (q.append r) := by
  induction r <;> simp_all [append_cons_eq_concat_append]

/-- If `p <+ q` then `p.reverse <+ q.reverse` -/
lemma Subwalk.reverse {u v x y : V} {p : G.Walk u v} {q : G.Walk x y}
    (hs : Subwalk p q) : Subwalk p.reverse q.reverse := by
  induction q generalizing p u v with
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
    · have : Subwalk p q := by
        cases p with
        | nil => simp_all
        | cons => exact hs.of_cons₂_of_ne _ _ ha
      exact (ih this).concat _

/-- If `p.concat h <+ q` then `p <+ q` -/
@[simp]
lemma Subwalk.of_concat {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (h : G.Adj v z) (hs : Subwalk (p.concat h) q) : Subwalk p q := by
  have := hs.reverse
  simp only [reverse_concat] at this
  simpa using (this.of_cons h.symm).reverse


/-- If `p.concat h <+ q.concat h` then `p <+ q` -/
@[simp]
lemma Subwalk.of_concat₂ {u v x y  : V} {p : G.Walk u v} {q : G.Walk x v}
    (h : G.Adj v y) (hs : Subwalk (p.concat h) (q.concat h)) : Subwalk p q := by
  have := hs.reverse
  simp only [reverse_concat] at this
  simpa using (this.of_cons₂ h.symm).reverse

/--
If `p.concat hp <+ q.concat hq` and the end of the darts `hp` and `hq` differ then
`p.concat hp <+ q`
-/
@[simp]
lemma Subwalk.of_concat₂_of_ne {u v x y z t : V} {p : G.Walk u v} {q : G.Walk x y} (hp : G.Adj v z)
    (hq : G.Adj y t) (h : Subwalk (p.concat hp) (q.concat hq)) (hne : z ≠ t) :
    Subwalk (p.concat hp) q := by
  have := Subwalk.reverse h
  simp only [reverse_concat] at this
  simpa using (this.of_cons₂_of_ne hp.symm hq.symm hne).reverse

/--
If `p.concat hp <+ q.concat hq` and the start of the darts `hp` and `hq` differ then
`p.concat hp <+ q`
-/
@[simp]
lemma Subwalk.of_concat₂_of_ne_fst {u v x y z : V} {p : G.Walk u v} {q : G.Walk x y}
    (hp : G.Adj v z) (hq : G.Adj y z) (hs : Subwalk (p.concat hp) (q.concat hq))
    (hne : v ≠ y) : Subwalk (p.concat hp) q := by
  have := hs.reverse
  simp only [reverse_concat] at this
  simpa using (this.of_cons₂_of_ne_snd hp.symm hq.symm hne).reverse

/-- If `p ++ r <+ q ++ r` then `p <+ q` -/
@[simp]
lemma Subwalk.of_append_right {x u v y : V} {p : G.Walk u v} {q : G.Walk x v}
    (r : G.Walk v y) (hs : Subwalk (p.append r) (q.append r)) : Subwalk p q := by
  have := hs.reverse
  simp only [reverse_append] at this
  simpa using (this.of_append_left r.reverse).reverse

/-- *Tranisitivity of Subwalks* -/
@[trans, simp]
theorem Subwalk.trans {u₁ v₁ u₂ v₂ u₃ v₃ : V} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂}
    {p₃ : G.Walk u₃ v₃} (h₁ : Subwalk p₁ p₂) (h₂ : Subwalk p₂ p₃) : Subwalk p₁ p₃ := by
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
    (hs : Subwalk p q) (r : G.Walk x u) : Subwalk (r.append p) (r.append q) := by
  induction r <;> simp_all

/-- If `p <+ q` then `p ++ r <+ q ++ r` -/
@[simp]
lemma Subwalk.append_right_right {u v x y : V} {p : G.Walk u v} {q : G.Walk x v}
    (hs : Subwalk p q) (r : G.Walk v y) : Subwalk (p.append r) (q.append r) := by
  have := hs.reverse
  simp only [reverse_append] at this
  simpa using (this.append_left_left r.reverse).reverse

---------------- Infix / Prefix / Suffix walks

/-- `p.Infix q` means that the walk `p` is a contiguous Subwalk of the walk `q`. -/
def Infix {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) : Prop :=
  ∃ (ru : G.Walk u₂ u₁) (rv : G.Walk v₁ v₂), q = (ru.append p).append rv

@[simp]
lemma Infix.refl {u₁ v₁} (p : G.Walk u₁ v₁) : p.Infix p := by
  use nil, nil; simp

/-- `p.Prefix q` means that the walk `q` starts with the walk `p`. -/
def Prefix {u v₁ v₂} (p : G.Walk u v₁) (q : G.Walk u v₂) : Prop :=
  ∃ (r : G.Walk v₁ v₂), q = p.append r

@[simp]
lemma Prefix.nil {u v} (q : G.Walk u v) : (nil' u).Prefix q := by
  use q; simp

/-- If `p.cons h <+: q.cons h'` then `p` and `q` have equal starts -/
lemma Prefix.eq_of_cons {u₁ u₂ x v₁ v₂} {p : G.Walk x v₁} {q : G.Walk u₂ v₂} (h : G.Adj u₁ x)
    (h' : G.Adj u₁ u₂) (hp : (cons h p).Prefix (cons h' q)) : u₂ = x := by
  obtain ⟨_, hr⟩ := hp
  rw [cons_append, cons.injEq] at hr
  exact hr.1

/-- `p.cons h <+: q.cons h` iff `p <+: q` -/
lemma prefix_cons_iff {u₁ u₂ v₁ v₂} {p : G.Walk u₂ v₁} {q : G.Walk u₂ v₂} (h : G.Adj u₁ u₂) :
    (cons h p).Prefix (cons h q) ↔ p.Prefix q := by
  constructor <;> intro ⟨r, hr⟩ <;> exact ⟨r, by aesop⟩

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

lemma takeUntil_isPrefix [DecidableEq V] {u v x : V} {p : G.Walk u v} (hx : x ∈ p.support) :
  (p.takeUntil _ hx).Prefix p := ⟨_, (take_spec p hx).symm⟩

lemma dropUntil_isSuffix [DecidableEq V] {u v x : V} {p : G.Walk u v} (hx : x ∈ p.support) :
  (p.dropUntil _ hx).Suffix p := ⟨_, (take_spec p hx).symm⟩

lemma Prefix.subwalk {u v w : V} {p : G.Walk u v} {q : G.Walk u w} (h : p.Prefix q) :
    p.Subwalk q := h.infix.subwalk

lemma Suffix.subwalk {u v w : V} {p : G.Walk u w} {q : G.Walk v w} (h : p.Suffix q) :
    p.Subwalk q := h.infix.subwalk

end SimpleGraph.Walk
