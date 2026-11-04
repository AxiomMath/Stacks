module

public import Mathlib.Topology.Sheaves.SheafOfFunctions


public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Stacks 007D — the stalk of a product sheaf is in general not the corresponding factor

Fix a topological space `X` and a family of sets `A x` indexed by the points of `X`, and let
`F : U ↦ ∏ x ∈ U, A x` be the product sheaf of Stacks 006X, with restriction along `V ⊆ U` given
by `s ↦ s|_V`; in Mathlib this is `TopCat.sheafToTypes`, with underlying presheaf
`TopCat.presheafToTypes`. Stacks 007D observes that the stalk `F_x` is in general *not* `A x`:
there is a canonical map `F_x → A x`, and in general nothing better can be said.

Three parts are formalized. `statement1_exists_evalMap` produces the canonical evaluation map
`π_x : F_x → A x` with `π_x (germ s) = s x`; it is witnessed by `evalStalk`, whose
well-definedness is `evalStalk_welldef` and whose characterising equation is `evalStalk_germ`.
`statement2_empty_stalk` shows `F_x` is empty as soon as every open neighbourhood of `x` contains
a point `y` with `A y` empty. `statement3_surjects_onto_tails` treats the case `A y = {0,1}` for
all `y`, with a sequence of pairwise distinct points `x n` converging to `x` in the sense that
every open neighbourhood of `x` contains `x n` for all but finitely many `n`: it produces a
well-defined surjection `τ : F_x → T` onto the set `T = Tails` of tails of `{0,1}`-valued
sequences, that is `{0,1}^ℕ` modulo the equivalence `tailSetoid` of differing in only finitely
many places, and `T` is infinite by `infinite_tails`.
-/

@[expose] public section

open TopCat TopologicalSpace CategoryTheory Opposite Filter

noncomputable section

/-! ## The product sheaf and its stalks

The product sheaf is `TopCat.sheafToTypes X A`, with underlying presheaf
`TopCat.presheafToTypes X A`. For an open set `U`, the sections are the dependent
functions `∀ y : U, A y`, and restriction is precomposition with the inclusion.
The stalk at `x` is `(TopCat.presheafToTypes X A).stalk x` and the germ map is
`(TopCat.presheafToTypes X A).germ U x hx`.

These are recorded as definitional facts. -/

/-- Sections of the product (pre)sheaf over an open set `U` are dependent functions. -/
example (X : TopCat) (A : X → Type) (U : Opens X) :
    (presheafToTypes X A).obj (op U) = (∀ y : U, A y) := rfl

/-- `sheafToTypes` has `presheafToTypes` as its underlying presheaf. -/
example (X : TopCat) (A : X → Type) :
    (sheafToTypes X A).presheaf = presheafToTypes X A := rfl

/-! ## The canonical evaluation map `π_x : F_x → A x` -/

variable {X : TopCat} {A : X → Type}

/-- The canonical evaluation map `π_x : F_x → A x`. The germ at `x` of a section `s`
defined on a neighbourhood `U` of `x` is sent to its value `s x ∈ A x`. It is defined by
choosing a representative; `evalStalk_germ` shows it sends `germ s` to `s x`, and
`evalStalk_welldef` records the underlying well-definedness. -/
def evalStalk (x : X) (g : (presheafToTypes X A).stalk x) : A x :=
  letI h := (presheafToTypes X A).exists_germ_eq g
  h.choose_spec.choose_spec.choose ⟨x, h.choose_spec.choose⟩

/-- Well-definedness underlying the evaluation map: two sections whose germs at `x`
agree have equal values at `x`. -/
theorem evalStalk_welldef (U V : Opens X) (x : X) (hx : x ∈ U) (hxV : x ∈ V)
    (s : ∀ y : U, A y) (t : ∀ y : V, A y)
    (heq : (presheafToTypes X A).germ U x hx s = (presheafToTypes X A).germ V x hxV t) :
    s ⟨x, hx⟩ = t ⟨x, hxV⟩ := by
  obtain ⟨W, hxW, iU, iV, hres⟩ := (presheafToTypes X A).germ_eq x hx hxV s t heq
  exact congrFun hres ⟨x, hxW⟩

/-- Correctness of the evaluation map: `π_x (germ s) = s x`, i.e. `evalStalk` agrees with
the projection `∏_{y ∈ U} A y → A x` on each `F(U)`. -/
theorem evalStalk_germ (U : Opens X) (x : X) (hx : x ∈ U) (s : ∀ y : U, A y) :
    evalStalk x ((presheafToTypes X A).germ U x hx s) = s ⟨x, hx⟩ := by
  unfold evalStalk
  set g := (presheafToTypes X A).germ U x hx s with hg
  exact evalStalk_welldef _ U x _ hx _ s
    ((presheafToTypes X A).exists_germ_eq g).choose_spec.choose_spec.choose_spec

/-! ## Part (1): `π_x` is a well-defined function

That the map `π_x : F_x → A x` is well defined is formalised directly as the *existence* of a
function `π_x : F_x → A x` satisfying the characterising germ-evaluation equation
`π_x (germ s) = s x`. It is witnessed by `evalStalk x`, which packages the well-definedness
established in `evalStalk_welldef`, with the equation proved by `evalStalk_germ`. -/

/-- **Stacks 007D (1).** For every `x ∈ X` there is a well-defined function
`π_x : F_x → A x` with `π_x (germ s) = s x` for every section `s` of the product sheaf over a
neighbourhood of `x`. -/
@[stacks 007D "(1)"]
theorem statement1_exists_evalMap (x : X) :
    ∃ π : (presheafToTypes X A).stalk x → A x,
      ∀ (U : Opens X) (hx : x ∈ U) (s : ∀ y : U, A y),
        π ((presheafToTypes X A).germ U x hx s) = s ⟨x, hx⟩ :=
  ⟨evalStalk x, fun U hx s => evalStalk_germ U x hx s⟩

/-! ## Tails of `{0,1}`-valued sequences -/

/-- The tail equivalence on `{0,1}^ℕ` (modelled as `ℕ → Fin 2`): two sequences are
equivalent iff they differ in only finitely many places. -/
def tailSetoid : Setoid (ℕ → Fin 2) where
  r := fun b b' => {n | b n ≠ b' n}.Finite
  iseqv :=
    { refl := fun b => by simp
      symm := fun {b b'} h => by
        have : {n | b' n ≠ b n} = {n | b n ≠ b' n} := by ext n; simp [ne_comm]
        rw [this]; exact h
      trans := fun {a b c} hab hbc => by
        apply Set.Finite.subset (hab.union hbc)
        intro n hn
        simp only [Set.mem_ofPred_eq, Set.mem_union]
        by_contra h
        rw [not_or, not_not, not_not] at h
        exact hn (h.1.trans h.2) }

/-- The set of tails `T = {0,1}^ℕ / ~tail`. -/
abbrev Tails : Type := Quotient tailSetoid

/-! ## Part (2): the stalk can be empty -/

/-- **Stacks 007D (2).** Fix `x`. If every open neighbourhood `U` of `x` contains a point
`y ∈ U` with `A y` empty, then the stalk `F_x` is empty. -/
@[stacks 007D "(2)"]
theorem statement2_empty_stalk (x : X)
    (h : ∀ U : Opens X, x ∈ U → ∃ y : X, ∃ _ : y ∈ U, IsEmpty (A y)) :
    IsEmpty ((presheafToTypes X A).stalk x) := by
  -- Every stalk element is the germ of some section `s` over a nbhd `U`; pick the empty
  -- point `y ∈ U` with `IsEmpty (A y)`, then `s ⟨y, hyU⟩ : A y` is an element of an empty
  -- type, contradiction (`IsEmpty.elim`).
  constructor
  intro g
  obtain ⟨U, hxU, s, hgerm⟩ := (presheafToTypes X A).exists_germ_eq g
  obtain ⟨y, hyU, hAy⟩ := h U hxU
  exact hAy.elim (s ⟨y, hyU⟩)

/-! ## Part (3): surjection onto tails

We specialise to the constant family `A = fun _ => Fin 2` (i.e. `A y = {0,1}` for all `y`).
The convergence hypothesis `x n → x` is spelled out as: every open neighbourhood `U` of `x`
contains `x n` for all but finitely many `n` (equivalently, `Tendsto xseq cofinite (𝓝 x)`). -/

open scoped Classical in
/-- The total `{0,1}`-valued sequence `b^{(U,s)}` attached to a section `s` over `U`:
its `n`-th entry is `s (x n)` if `x n ∈ U`, and `0` otherwise. -/
def tauSeq (xseq : ℕ → X) (U : Opens X) (s : ∀ _y : U, Fin 2) : ℕ → Fin 2 :=
  fun n => if h : xseq n ∈ U then s ⟨xseq n, h⟩ else 0

/-- `T` is infinite: the classes of the "bit-`m`" sequences `n ↦ testBit n m` are pairwise
distinct, giving an injection `ℕ → T`. -/
theorem infinite_tails : Infinite Tails := by
  -- Inject ℕ → Tails by m ↦ ⟦n ↦ testBit n m⟧. Distinctness: for m < m', the positions
  -- n = 2^m + k·2^(m'+1) (k ∈ ℕ) all have testBit n m = true, testBit n m' = false, so
  -- the two bit-sequences disagree there. That set is infinite (injective image of ℕ),
  -- so the classes differ.
  set e : ℕ → Tails :=
    fun m => Quotient.mk tailSetoid (fun n => if Nat.testBit n m then 1 else 0) with he
  apply Infinite.of_injective e
  have key : ∀ m m' : ℕ, m < m' → e m ≠ e m' := by
    intro m m' hlt heq
    rw [he] at heq
    simp only [Quotient.eq] at heq
    have hfin : {n | (if Nat.testBit n m then (1:Fin 2) else 0)
        ≠ (if Nat.testBit n m' then 1 else 0)}.Finite := heq
    set g : ℕ → ℕ := fun k => 2^m + k * 2^(m'+1) with hg
    have hginj : Function.Injective g := by
      intro a b hab
      simp only [hg] at hab
      have hpos : 0 < 2^(m'+1) := by positivity
      have : a * 2^(m'+1) = b * 2^(m'+1) := by omega
      exact Nat.eq_of_mul_eq_mul_right hpos this
    have hsub : Set.range g ⊆ {n | (if Nat.testBit n m then (1:Fin 2) else 0)
        ≠ (if Nat.testBit n m' then 1 else 0)} := by
      rintro n ⟨k, rfl⟩
      have hb : 2^m < 2^(m'+1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have heq2 : (2:ℕ)^m + k * 2^(m'+1) = 2^(m'+1) * k + 2^m := by ring
      have t1 : Nat.testBit (g k) m = true := by
        simp only [hg, heq2]
        rw [Nat.testBit_two_pow_mul_add k hb m, ite_eq_left (by omega)]
        exact Nat.testBit_two_pow_self
      have t2 : Nat.testBit (g k) m' = false := by
        simp only [hg, heq2]
        rw [Nat.testBit_two_pow_mul_add k hb m', ite_eq_left (by omega), Nat.testBit_two_pow]
        simp; omega
      simp only [Set.mem_ofPred_eq, t1, t2]
      decide
    have : (Set.range g).Finite := hfin.subset hsub
    exact (Set.infinite_range_of_injective hginj) this
  intro m m' hmm
  rcases lt_trichotomy m m' with h | h | h
  · exact absurd hmm (key m m' h)
  · exact h
  · exact absurd hmm.symm (key m' m h)

/-- Well-definedness for `τ`: if two sections have the same germ at `x`, their associated
total sequences `tauSeq` differ in only finitely many positions, i.e. are tail-equivalent. -/
theorem tauSeq_welldef (xseq : ℕ → X) (x : X)
    (hconv : ∀ U : Opens X, x ∈ U → {n | xseq n ∉ U}.Finite)
    (U V : Opens X) (hx : x ∈ U) (hxV : x ∈ V)
    (s : ∀ _ : U, Fin 2) (t : ∀ _ : V, Fin 2)
    (heq : (presheafToTypes X (fun _ : X => Fin 2)).germ U x hx s
         = (presheafToTypes X (fun _ : X => Fin 2)).germ V x hxV t) :
    {n | tauSeq xseq U s n ≠ tauSeq xseq V t n}.Finite := by
  -- Same germ ⇒ s, t agree on a common nbhd `W` (`germ_eq`). For `xseq n ∈ W` (all but
  -- finitely many n, by `hconv W`), both tauSeq entries equal s/t at `xseq n`, which agree;
  -- so the disagreement set is contained in the finite set `{n | xseq n ∉ W}`.
  obtain ⟨W, hxW, iU, iV, hres⟩ :=
    (presheafToTypes X (fun _ : X => Fin 2)).germ_eq x hx hxV s t heq
  have key : ∀ p : W, s (iU p) = t (iV p) := by
    intro p
    have h2 := congrFun hres p
    dsimp [presheafToTypes] at h2
    exact h2
  apply Set.Finite.subset (hconv W hxW)
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn ⊢
  by_contra hnW
  -- xseq n ∈ W
  apply hn
  have hU : xseq n ∈ U := (iU ⟨xseq n, hnW⟩).2
  have hVm : xseq n ∈ V := (iV ⟨xseq n, hnW⟩).2
  have hsval : s ⟨xseq n, hU⟩ = t ⟨xseq n, hVm⟩ := by
    have := key ⟨xseq n, hnW⟩
    -- iU ⟨xseq n, hnW⟩ has underlying point xseq n
    have e1 : (iU ⟨xseq n, hnW⟩ : U) = ⟨xseq n, hU⟩ := Subtype.ext rfl
    have e2 : (iV ⟨xseq n, hnW⟩ : V) = ⟨xseq n, hVm⟩ := Subtype.ext rfl
    rw [e1, e2] at this
    exact this
  simp [tauSeq, hU, hVm, hsval]

open scoped Classical in
/-- **Stacks 007D (3).** Suppose `A y = {0,1}` for all `y` (here `A = fun _ => Fin 2`), the
points `x n` are pairwise distinct, and `x n → x` in the sense that every open neighbourhood
of `x` contains `x n` for all but finitely many `n`. Then there is a well-defined map
`τ : F_x → T` sending the germ of a section `s` over `U` to the tail class of `b^{(U,s)}`,
and `τ` is surjective; moreover `T` is infinite. -/
@[stacks 007D "(3)"]
theorem statement3_surjects_onto_tails
    (xseq : ℕ → X) (x : X)
    (hdist : Function.Injective xseq)
    (hconv : ∀ U : Opens X, x ∈ U → {n | xseq n ∉ U}.Finite) :
    (∃ τ : (presheafToTypes X (fun _ : X => Fin 2)).stalk x → Tails,
      (∀ (U : Opens X) (hx : x ∈ U) (s : ∀ _ : U, Fin 2),
        τ ((presheafToTypes X (fun _ : X => Fin 2)).germ U x hx s)
          = Quotient.mk tailSetoid (tauSeq xseq U s)) ∧
      Function.Surjective τ)
    ∧ Infinite Tails := by
  -- Define τ(g) = ⟦tauSeq of a chosen representative of g⟧. Well-defined by tauSeq_welldef.
  -- Surjective: given a tail ⟦b⟧, build the section s over ⊤ with s(y) = b k when y = xseq k
  -- (well-defined since xseq injective), else 0; then tauSeq ⊤ s = b exactly, so
  -- τ(germ s) = ⟦b⟧. Infinitude of Tails is `infinite_tails`.
  classical
  refine ⟨?_, infinite_tails⟩
  -- Define τ by choosing a representative section for each germ.
  set P := presheafToTypes X (fun _ : X => Fin 2) with hP
  -- choice data for each germ
  let τ : P.stalk x → Tails := fun g =>
    let h := P.exists_germ_eq g
    Quotient.mk tailSetoid (tauSeq xseq h.choose h.choose_spec.choose_spec.choose)
  have hτ : ∀ (U : Opens X) (hx : x ∈ U) (s : ∀ y : U, Fin 2),
      τ (P.germ U x hx s) = Quotient.mk tailSetoid (tauSeq xseq U s) := by
    intro U hx s
    -- the chosen representative of the germ `P.germ U x hx s`
    set g := P.germ U x hx s with hg
    have hch := P.exists_germ_eq g
    have hspec : P.germ hch.choose x hch.choose_spec.choose hch.choose_spec.choose_spec.choose
        = g := hch.choose_spec.choose_spec.choose_spec
    -- now apply well-definedness
    dsimp only [τ]
    apply Quotient.sound
    -- need: tauSeq of chosen rep ~ tauSeq of (U, s)
    apply tauSeq_welldef xseq x hconv hch.choose U hch.choose_spec.choose hx
    rw [hspec, hg]
  refine ⟨τ, hτ, ?_⟩
  -- surjectivity
  intro c
  refine Quotient.inductionOn c ?_
  intro b
  -- build a section over ⊤ whose tauSeq equals b exactly
  let s : ∀ _y : (⊤ : Opens X), Fin 2 :=
    fun y => if h : ∃ k, xseq k = (y : X) then b h.choose else 0
  have hxtop : x ∈ (⊤ : Opens X) := trivial
  refine ⟨P.germ (⊤ : Opens X) x hxtop s, ?_⟩
  rw [hτ]
  apply Quotient.sound
  -- tauSeq xseq ⊤ s = b, hence tail-equivalent (in fact equal)
  have heqseq : tauSeq xseq (⊤ : Opens X) s = b := by
    funext n
    simp only [tauSeq]
    rw [dite_eq_left (show xseq n ∈ (⊤ : Opens X) from trivial)]
    have hex : ∃ k, xseq k = ((⟨xseq n, trivial⟩ : (⊤ : Opens X)) : X) := ⟨n, rfl⟩
    simp only [s, dite_eq_left hex]
    have : xseq hex.choose = xseq n := hex.choose_spec
    rw [hdist this]
  rw [heqseq]

end
