module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Analysis.Normed.Ring.Lemmas
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

-- The degree-transport maps `CplxCplx.cast` are degree casts whose `change`/`rfl`
-- steps below need to be checked at default transparency; verified load-bearing (removing it
-- breaks `smul_d_add_f_eq_zero_of_totalD_eq_zero` and `total_H0_eq_zero`).
set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

We follow Stacks Tag 0H0Q (Lemma 15.105.1), Tag 0EYW (Section 15.105), and the
conventions of Stacks Section 12.18 (Tags 0FNB, 012Y, 012Z).

All objects are abelian groups and all complexes are cochain complexes
(differential raises degree by `1`).

## Main Definitions (informal)

* A *cochain complex of abelian groups* `B^•` is a family `(B^q)_{q ∈ ℤ}` with
  differentials `d_B^q : B^q → B^{q+1}` satisfying `d^{q+1} ∘ d^q = 0`.  Its
  cohomology is `H^q(B^•) = ker(d_B^q) / im(d_B^{q-1})`.

* A *double complex* has terms `A^{p,q}` with a horizontal differential
  `d_1^{p,q} : A^{p,q} → A^{p+1,q}` and a vertical differential
  `d_2^{p,q} : A^{p,q} → A^{p,q+1}` such that `d_1 ∘ d_1 = 0`, `d_2 ∘ d_2 = 0`
  and the squares commute: `d_1^{p,q+1} ∘ d_2^{p,q} = d_2^{p+1,q} ∘ d_1^{p,q}`.

* The *product total complex* `Tot_π(A^{•,•})` has terms
  `Tot_π^n = ∏_{p+q=n} A^{p,q}` with differential whose component in `A^{p,q}`
  (with `p+q = n+1`) is `d_1^{p-1,q}(x_{p-1,q}) + (-1)^p d_2^{p,q-1}(x_{p,q-1})`.
  Note the *direct product* (not direct sum): infinitely many summands may be
  nonzero in a single total degree.

* A *complex of complexes* indexed by `p ≥ 0`
    `A_0^• --f_0--> A_1^• --f_1--> A_2^• --f_2--> ⋯`
  is a sequence of cochain complexes `A_p^•` with chain maps `f_p` such that
  `f_{p+1} ∘ f_p = 0`.  It yields a double complex by `A^{p,q} = A_p^q` for
  `p ≥ 0` (and `0` for `p < 0`), with `d_1 = f_p` and `d_2 = d_{A_p^•}`.

## Main Statement (Stacks Tag 0H0Q, Lemma 15.105.1)

Let `A_0^• → A_1^• → A_2^• → ⋯` be a complex of complexes of abelian groups
with `H^{-p}(A_p^•) = 0` for all `p ≥ 0`.  Then `H^0(Tot_π(A^{•,•})) = 0`.
-/

/-
## Modelling choices

We model the *complex of complexes* (Definition 4) directly, since this is the
shape in which the lemma is used and it carries all the data of the associated
double complex.  We index the "complex-of-complexes" direction by `p : ℕ`
(matching `p ≥ 0`; for `p < 0` all groups are `0`, contributing nothing to a
product over `p + q = n` once `p ≥ 0` is imposed), and the internal direction by
`q : ℤ`.

The groups are an arbitrary family `A : ℕ → ℤ → Type u` of abelian groups,
`d` is the internal (vertical) differential `d_2 = d_{A_p^•}`, and `f` is the
horizontal differential `d_1 = f_p`.  The three double-complex axioms are
recorded as `d_d` (`d_2 ∘ d_2 = 0`), `f_f` (`f_{p+1} ∘ f_p = 0`) and `f_d`
(the chain-map / commuting-square condition `d ∘ f = f ∘ d`).

The *product* total complex in total degree `n` is `(p : ℕ) → A_p^{n-p}`, the
direct product over `p ≥ 0` of `A^{p,n-p} = A_p^{n-p}` (the constraint
`p + q = n` with `p ≥ 0` becomes `q = n - p`).

Mathlib's vocabulary for the data of `CplxCplx` is `HomologicalComplex₂` (with
`A`, `d`, `f` the terms and the two differentials, `d_d`/`f_f` the complex
conditions and `f_d` the chain-map condition); the total complex it provides,
`HomologicalComplex₂.total`, is the *coproduct* one, so the product total complex
studied here has no Mathlib counterpart.
-/

universe u

/-- A complex of cochain complexes of abelian groups, indexed by `p : ℕ`:
`A_0^• --f_0--> A_1^• --f_1--> ⋯`.  Here `A p q = A_p^q`, `d` is the internal
(vertical) differential, and `f` is the horizontal map `f_p`. -/
structure CplxCplx where
  /-- The abelian group `A_p^q`. -/
  A : ℕ → ℤ → Type u
  /-- The abelian group structure on `A p q`. -/
  instAb : ∀ p q, AddCommGroup (A p q)
  /-- Internal (vertical) differential `d_2 = d_{A_p^•} : A_p^q → A_p^{q+1}`. -/
  d : ∀ p q, A p q →+ A p (q + 1)
  /-- Horizontal differential `d_1 = f_p : A_p^q → A_{p+1}^q`. -/
  f : ∀ p q, A p q →+ A (p + 1) q
  /-- `A_p^•` is a complex: `d_2 ∘ d_2 = 0`. -/
  d_d : ∀ p q (x : A p q), d p (q + 1) (d p q x) = 0
  /-- The horizontal differentials compose to zero: `f_{p+1} ∘ f_p = 0`. -/
  f_f : ∀ p q (x : A p q), f (p + 1) q (f p q x) = 0
  /-- Each `f_p` is a chain map (commuting squares): `d ∘ f = f ∘ d`. -/
  f_d : ∀ p q (x : A p q), d (p + 1) q (f p q x) = f p (q + 1) (d p q x)

attribute [instance] CplxCplx.instAb

private theorem neg_one_pow_mul_self (n : ℕ) : ((-1 : ℤ) ^ n) * ((-1 : ℤ) ^ n) = 1 := by
  rw [← pow_add]; simp


@[deprecated (since := "2026-09-27")]
alias ComplexOfComplexes := CplxCplx

namespace CplxCplx

/-- Transport an element along an equality of internal degree, as an additive
equivalence `A_p^q ≃+ A_p^{q'}`. -/
def cast (c : CplxCplx) (p : ℕ) {q q' : ℤ} (h : q = q') : c.A p q ≃+ c.A p q' :=
  AddEquiv.cast (M := fun q => c.A p q) h

/-- Transport along `rfl` is the identity. -/
@[simp] theorem cast_rfl (c : CplxCplx) (p : ℕ) {q : ℤ} (x : c.A p q) :
    c.cast p (rfl : q = q) x = x := rfl

/-- Transporting along `h : q = q'` and then `h' : q' = q''` is transport along
`h.trans h'`. -/
@[simp] theorem cast_cast (c : CplxCplx) (p : ℕ) {q q' q'' : ℤ} (h : q = q')
    (h' : q' = q'') (x : c.A p q) : c.cast p h' (c.cast p h x) = c.cast p (h.trans h') x := by
  cases h; cases h'; rfl

/-- `d` commutes with `cast` (transport of the source degree). -/
@[simp] theorem d_cast (c : CplxCplx) (p : ℕ) {q q' : ℤ} (h : q = q') (x : c.A p q) :
    c.d p q' (c.cast p h x) = c.cast p (by rw [h]) (c.d p q x) := by
  cases h; rfl

/-- Transporting the source degree, applying `d`, then transporting the target
degree is a single transport of `d`. -/
theorem cast_d_cast (c : CplxCplx) (p : ℕ) {q q' r : ℤ} (h : q = q') (h' : q' + 1 = r)
    (x : c.A p q) :
    c.cast p h' (c.d p q' (c.cast p h x)) = c.cast p (by omega) (c.d p q x) := by
  cases h; cases h'; rfl

/-- `f` commutes with `cast`. -/
@[simp] theorem f_cast (c : CplxCplx) (p : ℕ) {q q' : ℤ} (h : q = q') (x : c.A p q) :
    c.f p q' (c.cast p h x) = c.cast (p + 1) h (c.f p q x) := by
  cases h; rfl

/-- Term of the *product total complex* `Tot_π` in total degree `n`:
the direct product `∏_{p ≥ 0} A_p^{n-p}` (over `p + q = n`, `p ≥ 0`). -/
@[sga "4 XVII 1.1.4" "partial"]
def Tot (c : CplxCplx.{u}) (n : ℤ) : Type u := (p : ℕ) → c.A p (n - p)

/-- The abelian group structure on `Tot_π^n`, given componentwise. -/
instance instAddCommGroupTot (c : CplxCplx) (n : ℤ) : AddCommGroup (c.Tot n) :=
  inferInstanceAs (AddCommGroup ((p : ℕ) → c.A p (n - p)))

/-- The vertical (internal) contribution to the `p`-th component of the total
differential: `(-1)^p d_2^{p,n-p}(x_p)`, landing in `A_p^{n+1-p}`. -/
def dPartHom (c : CplxCplx) (n : ℤ) (p : ℕ) : c.Tot n →+ c.A p (n + 1 - p) :=
  (c.cast p (show n - (p : ℤ) + 1 = n + 1 - p by ring)).toAddMonoidHom.comp
    (((zsmulAddGroupHom ((-1 : ℤ) ^ p)).comp (c.d p (n - p))).comp
      (Pi.evalAddMonoidHom (fun p => c.A p (n - p)) p))

/-- The horizontal contribution to the `(p+1)`-st component of the total
differential: `f_p^{n-p}(x_p)`, landing in `A_{p+1}^{n+1-(p+1)}`. -/
def fPartHom (c : CplxCplx) (n : ℤ) (p : ℕ) :
    c.Tot n →+ c.A (p + 1) (n + 1 - ((p + 1 : ℕ) : ℤ)) :=
  (c.cast (p + 1)
      (show n - (p : ℤ) = n + 1 - ((p + 1 : ℕ) : ℤ) by push_cast; ring)).toAddMonoidHom.comp
    ((c.f p (n - p)).comp (Pi.evalAddMonoidHom (fun p => c.A p (n - p)) p))

/-- The `p`-th component of `D^n x ∈ Tot_π^{n+1}`.  For `p = 0` only the
vertical term occurs (the horizontal term would use `x_{-1} = 0`); for `p+1` it
is `(-1)^{p+1} d_2(x_{p+1}) + f_p^{n-p}(x_p)`, i.e. the vertical contribution of
the `(p+1)`-st factor plus the horizontal contribution of the `p`-th factor. -/
def dComp (c : CplxCplx) (n : ℤ) (x : c.Tot n) (p : ℕ) : c.A p (n + 1 - p) :=
  match p with
  | 0 => c.dPartHom n 0 x
  | (p' + 1) => c.dPartHom n (p' + 1) x + c.fPartHom n p' x

/-- The differential `D^n : Tot_π^n → Tot_π^{n+1}` of the product total complex. -/
def totalD (c : CplxCplx) (n : ℤ) : c.Tot n →+ c.Tot (n + 1) where
  toFun x := c.dComp n x
  map_zero' := by
    funext p
    change c.dComp n 0 p = (0 : c.A p (n + 1 - p))
    cases p with
    | zero => simp only [dComp, map_zero]
    | succ p' => simp only [dComp, map_zero, add_zero]
  map_add' x y := by
    funext p
    change c.dComp n (x + y) p = c.dComp n x p + c.dComp n y p
    cases p with
    | zero => simp only [dComp, map_add]
    | succ p' => simp only [dComp, map_add]; abel

/-- `H^{-p}(A_p^•) = 0`: every internal `(-p)`-cocycle of the complex `A_p^•` is
a coboundary, i.e. lies in the image of `d_2^{-p-1}`.  In Mathlib's vocabulary
this is exactness of `A_p^•` at degree `-p` (`HomologicalComplex.ExactAt`). -/
def InternalCohomologyVanishes (c : CplxCplx) (p : ℕ) : Prop :=
  ∀ z : c.A p (-(p : ℤ)), c.d p (-(p : ℤ)) z = 0 →
    ∃ w : c.A p (-(p : ℤ) - 1),
      c.cast p (show -(p : ℤ) - 1 + 1 = -(p : ℤ) by ring) (c.d p (-(p : ℤ) - 1) w) = z

/-- Eliminator for `InternalCohomologyVanishes`: an internal `(-p)`-cocycle of `A_p^•` is the
coboundary of some `w : A_p^{-p-1}`. -/
theorem InternalCohomologyVanishes.exists_cast_d_eq {c : CplxCplx} {p : ℕ}
    (h : c.InternalCohomologyVanishes p) {z : c.A p (-(p : ℤ))} (hz : c.d p (-(p : ℤ)) z = 0) :
    ∃ w : c.A p (-(p : ℤ) - 1),
      c.cast p (show -(p : ℤ) - 1 + 1 = -(p : ℤ) by ring) (c.d p (-(p : ℤ) - 1) w) = z :=
  h z hz

/-- The vertical contribution evaluated at `x` is `(-1)^p d_2(x_p)`, transported to degree
`n + 1 - p`. -/
theorem dPartHom_apply (c : CplxCplx) {n : ℤ} (p : ℕ) (x : c.Tot n) :
    c.dPartHom n p x =
      c.cast p (show n - (p : ℤ) + 1 = n + 1 - p by ring)
        (((-1 : ℤ) ^ p) • c.d p (n - p) (x p)) := rfl

/-- The horizontal contribution evaluated at `x` is `f_p(x_p)`, transported to degree
`n + 1 - (p + 1)`. -/
theorem fPartHom_apply (c : CplxCplx) {n : ℤ} (p : ℕ) (x : c.Tot n) :
    c.fPartHom n p x =
      c.cast (p + 1) (show n - (p : ℤ) = n + 1 - ((p + 1 : ℕ) : ℤ) by push_cast; ring)
        (c.f p (n - p) (x p)) := rfl

/-- The `0`-th component of `D^n x` is the vertical contribution of `x_0`. -/
theorem totalD_apply_zero (c : CplxCplx) {n : ℤ} (x : c.Tot n) :
    c.totalD n x 0 = c.dPartHom n 0 x := rfl

/-- The `(p + 1)`-st component of `D^n x` is the vertical contribution of `x_{p+1}` plus the
horizontal contribution of `x_p`. -/
theorem totalD_apply_succ (c : CplxCplx) {n : ℤ} (x : c.Tot n) (p : ℕ) :
    c.totalD n x (p + 1) = c.dPartHom n (p + 1) x + c.fPartHom n p x := rfl

-- Main Statement(s)

/-
## Proof of `total_H0_eq_zero` (Stacks Tag 0H0Q), decomposition

Informal proof.  Given a degree-`0` cocycle
`x = (x_p)_{p≥0}` (`x_p ∈ A_p^{-p}`) with `D^0 x = 0`, we build a witness
`y = (y_p)_{p≥0}` (`y_p ∈ A_p^{-1-p}`) with `D^{-1} y = x`, by recursion on `p`.

The cocycle condition `D^0 x = 0` unpacks componentwise (this is what
`d_eq_zero_of_totalD_eq_zero` / `smul_d_add_f_eq_zero_of_totalD_eq_zero` extract) into:
* `p = 0`:   `d_2^0(x_0) = 0`;                              (so `x_0` is a cocycle)
* `p ≥ 1`:   `f_{p-1}^{-p+1}(x_{p-1}) + (-1)^p d_2^{-p}(x_p) = 0`.

The `p`-component of `D^{-1} y` is `(-1)^p d_2(y_p)` for `p = 0` and
`(-1)^{p+1} d_2(y_{p+1}) + f_p(y_p)` for `p+1`.  So `D^{-1} y = x` means exactly
* `p = 0`:   `d_2(y_0) = x_0`;
* `p+1`:     `(-1)^{p+1} d_2(y_{p+1}) = x_{p+1} - f_p(y_p)`, i.e.
             `d_2(y_{p+1}) = (-1)^{p+1}(x_{p+1} - f_p(y_p))`.

We solve these in turn:
* **Base.**  `x_0` is a cocycle (`d_eq_zero_of_totalD_eq_zero`), so `H^0(A_0^•) = 0`
  (`hH 0`) yields `y_0` with `d_2(y_0) = x_0`.
* **Step.**  Assume `y_p` solved.  The residual `r_{p+1} = x_{p+1} - f_p(y_p)`
  is a `(-(p+1))`-cocycle (`d_sub_eq_zero_of_stageInvariant`): using the chain-map axiom
  `f_d` (`d∘f = f∘d`), the invariant `StageInvariant` (`f_p(d_2 y_p) = (-1)^p f_p(x_p)`),
  and the cocycle relation `smul_d_add_f_eq_zero_of_totalD_eq_zero`, one computes
  `d_2(r_{p+1}) = 0`.
  Hence `H^{-(p+1)}(A_{p+1}^•) = 0` (`hH (p+1)`) yields `y_{p+1}` with
  `d_2(y_{p+1}) = (-1)^{p+1} r_{p+1}`, which is the required `p+1` equation.
  The invariant `StageInvariant (p+1) y_{p+1}` is then automatic from `f_{p+1}∘f_p = 0`.

The whole construction is a single dependent recursion on `p` (each stage uses
the previous `y_p` and its `StageInvariant`), and `total_H0_eq_zero` packages it.
The argument is rigorous and not circular: stage `p+1` depends only on stage `p`
(a strictly smaller index), and the only external inputs are the hypotheses `hH`,
the structure axioms, and the two cocycle-extraction lemmas. -/

/-- The internal cocycle relation extracted from the total cocycle condition
`D^n x = 0`, base component (`p = 0`): `d_{A_0}^{n}(x_0) = 0`, i.e. `x_0` is an
internal cocycle. -/
theorem d_eq_zero_of_totalD_eq_zero (c : CplxCplx) {n : ℤ} {x : c.Tot n}
    (hx : c.totalD n x = 0) : c.d 0 (n - ((0:ℕ):ℤ)) (x 0) = 0 := by
  have h := congrFun hx 0
  rw [totalD_apply_zero, dPartHom_apply, Pi.zero_apply] at h
  simp only [pow_zero, one_smul] at h
  rwa [AddEquivClass.map_eq_zero_iff] at h

/-- The internal cocycle relation extracted from `D^n x = 0`, component `p+1`:
`(-1)^{p+1} d_2^{n-(p+1)}(x_{p+1}) + f_p^{n-p}(x_p) = 0` (the degree cast aligns
`f_p^{n-p}(x_p) : A_{p+1}^{n-p}` with `d_2^{n-(p+1)}(x_{p+1}) : A_{p+1}^{n-p}`). -/
theorem smul_d_add_f_eq_zero_of_totalD_eq_zero (c : CplxCplx) {n : ℤ} {x : c.Tot n}
    (hx : c.totalD n x = 0) (p : ℕ) :
    ((-1:ℤ)^(p+1)) • c.d (p+1) (n - (p+1:ℕ)) (x (p+1))
      + c.cast (p+1) (by push_cast; ring) (c.f p (n - (p:ℕ)) (x p)) = 0 := by
  have h := congrFun hx (p+1)
  rw [totalD_apply_succ, dPartHom_apply, fPartHom_apply] at h
  rw [map_zsmul, Pi.zero_apply] at h
  apply (c.cast (p+1)
    (show n - (p+1:ℕ) + 1 = n + 1 - (p+1:ℕ) by push_cast; ring)).injective
  rw [map_add, map_zsmul, map_zero, cast_cast]
  convert h using 2

/-- The stage-`p` invariant `StageInvariant p y_p` carried through the inductive
construction of the coboundary `y`.  It records that, after applying the
horizontal map `f_p`, the internal differential of `y_p` agrees with
`(-1)^p f_p(x_p)`.  This is precisely the fact needed to show the next-stage
residual is a cocycle, and it holds automatically of any `y_p` produced from the
construction equation `d_2(y_p) = (-1)^p(x_p - f_{p-1}(y_{p-1}))` because
`f_p ∘ f_{p-1} = 0`. -/
def StageInvariant (c : CplxCplx) (x : c.Tot 0) (p : ℕ)
    (yp : c.A p (-1 - (p : ℤ))) : Prop :=
  c.f p (-(p:ℤ)) (c.cast p (by ring) (c.d p (-1 - (p:ℤ)) yp))
    = ((-1:ℤ)^p) • c.f p (-(p:ℤ)) (c.cast p (by ring) (x p))

/-- The stage invariant unfolded: `c.StageInvariant x p yp` is the equation
`f_p(d_2 y_p) = (-1)^p f_p(x_p)`, with the internal-degree transports made
explicit.  Use this instead of unfolding `StageInvariant`. -/
theorem stageInvariant_iff (c : CplxCplx) (x : c.Tot 0) {p : ℕ}
    (yp : c.A p (-1 - (p : ℤ))) :
    c.StageInvariant x p yp ↔
      c.f p (-(p:ℤ)) (c.cast p (by ring) (c.d p (-1 - (p:ℤ)) yp))
        = ((-1:ℤ)^p) • c.f p (-(p:ℤ)) (c.cast p (by ring) (x p)) := Iff.rfl

/-- **Key sub-lemma (the residual is a cocycle).**  At stage `p+1` of the
construction, the residual `r_{p+1} = x_{p+1} - f_p(y_p) ∈ A_{p+1}^{-(p+1)}` is an
internal `(-(p+1))`-cocycle, i.e. `d_2(r_{p+1}) = 0`.  This is the hypothesis that
licenses applying `H^{-(p+1)}(A_{p+1}^•) = 0` to `r_{p+1}`.

Rigorous proof.  Write `d := c.d (p+1) (-(p+1))`.  By additivity,
`d(r_{p+1}) = d(x_{p+1}) - d(f_p y_p)`.
1. By the chain-map axiom `c.f_d`, `d(f_p y_p) = f_p(d_2 y_p)` (`d∘f = f∘d`);
   pushing `f_p` through and applying the invariant `hinv : StageInvariant p y_p` gives
   `f_p(d_2 y_p) = (-1)^p f_p(x_p)`.  (Degrees: `d_2 y_p ∈ A_p^{-p}`, so
   `f_p(d_2 y_p) ∈ A_{p+1}^{-p}`, matching `d(x_{p+1}) ∈ A_{p+1}^{-p}`.)
2. From `smul_d_add_f_eq_zero_of_totalD_eq_zero` at `p`:
   `(-1)^{p+1} d_2(x_{p+1}) + f_p(x_p) = 0`, i.e.
   `(-1)^{p+1} d_2(x_{p+1}) = - f_p(x_p)`.  Multiply by `(-1)^{p+1}` (and use
   `(-1)^{2(p+1)} = 1`, `(-1)^{p+1}·(-1) = (-1)^{p+2} = (-1)^p`):
   `d_2(x_{p+1}) = (-1)^p f_p(x_p)`.
3. Subtracting, `d(r_{p+1}) = (-1)^p f_p(x_p) - (-1)^p f_p(x_p) = 0`. -/
theorem d_sub_eq_zero_of_stageInvariant (c : CplxCplx) {x : c.Tot 0}
    (hx : c.totalD 0 x = 0) {p : ℕ} {yp : c.A p (-1 - (p : ℤ))}
    (hinv : c.StageInvariant x p yp) :
    c.d (p+1) (-((p:ℤ)+1))
      (c.cast (p+1) (by push_cast; ring) (x (p+1))
        - c.cast (p+1) (by ring) (c.f p (-1 - (p:ℤ)) yp)) = 0 := by
  rw [map_sub, d_cast, d_cast, c.f_d p (-1 - (p:ℤ)) yp]
  have hcoc := smul_d_add_f_eq_zero_of_totalD_eq_zero c hx p
  rw [c.stageInvariant_iff] at hinv
  have hpow := neg_one_pow_mul_self (p+1)
  have hT1 : c.d (p+1) (0 - (p+1:ℕ)) (x (p+1))
      = - (((-1:ℤ)^(p+1)) • c.cast (p+1) (by push_cast; ring) (c.f p (0 - (p:ℕ)) (x p))) := by
    rw [← smul_neg, ← eq_neg_iff_add_eq_zero.mpr hcoc, smul_smul, hpow, one_smul]
  rw [f_cast] at hinv
  rw [hT1, map_neg, map_zsmul, cast_cast]
  rw [show c.cast (p+1) (show (-1 - (p:ℤ) + 1) = -((p:ℤ)+1)+1 by ring)
        (c.f p (-1 - (p:ℤ) + 1) (c.d p (-1 - (p:ℤ)) yp))
      = c.cast (p+1) (show (-(p:ℤ)) = -((p:ℤ)+1)+1 by ring)
          (c.cast (p+1) (show (-1 - (p:ℤ) + 1) = -(p:ℤ) by ring)
            (c.f p (-1 - (p:ℤ) + 1) (c.d p (-1 - (p:ℤ)) yp)))
      from by rw [cast_cast]]
  rw [hinv, map_zsmul, f_cast, cast_cast]
  rw [← neg_smul, show -((-1:ℤ)^(p+1)) = (-1:ℤ)^p from by rw [pow_succ]; ring, sub_self]

/-- **Stacks Tag 0H0Q (Lemma 15.105.1).**
Let `A_0^• → A_1^• → ⋯` be a complex of complexes of abelian groups such that
`H^{-p}(A_p^•) = 0` for all `p ≥ 0`.  Then `H^0(Tot_π(A^{•,•})) = 0`, i.e. every
degree-`0` cocycle of the product total complex is a coboundary: every
`x ∈ Tot_π^0` with `D^0 x = 0` is `D^{-1} y` for some `y ∈ Tot_π^{-1}`.
(Together with `D ∘ D = 0`, recorded in `totalD_totalD_eq_zero` below, this says
exactly that `ker(D^0) = im(D^{-1})`, i.e. `H^0(Tot_π) = 0`.)

Rigorous proof (recursion on `p`; see the block comment above for the math).
Build, by `Nat.rec`, a dependent stream
`Y : (p : ℕ) → Σ' (yp : c.A p (-1 - (p:ℤ))), c.StageInvariant x p yp` such that the
component equation of `D^{-1} (fun p => (Y p).fst) = x` holds at every `p`; set
`y p := (Y p).fst`.
* **Base (`Y 0`).**  `d_eq_zero_of_totalD_eq_zero` says `x 0` is a `0`-cocycle, so `hH 0`
  (after reconciling `0 - ↑0 = -↑0`) yields `w` with
  `d_2(w) = x_0`; take `(Y 0).fst := w`.  `StageInvariant x 0 w` reduces (`(-1)^0 = 1`) to
  `f_0(d_2 w) = f_0(x_0)`, immediate from `d_2 w = x_0`.
* **Step (`Y (p+1)` from `Y p`).**  Let `yp := (Y p).fst`, `hinv := (Y p).snd`.
  `d_sub_eq_zero_of_stageInvariant c hx hinv` shows `r_{p+1} = x_{p+1} - f_p(yp)` is a
  `(-(p+1))`-cocycle, so `hH (p+1)` yields `w'` with
  `d_2(w') = (-1)^{p+1} r_{p+1}` (scale the witness by `(-1)^{p+1}`, valid since
  `(-1)^{p+1}` is a unit; or equivalently apply `hH` to `(-1)^{p+1} r_{p+1}`,
  which is also a cocycle).  Take `(Y (p+1)).fst := w'`.  Then `StageInvariant x (p+1) w'`
  follows because `f_{p+1}(d_2 w') = (-1)^{p+1} f_{p+1}(r_{p+1}) =
  (-1)^{p+1}(f_{p+1}(x_{p+1}) - f_{p+1}(f_p yp)) = (-1)^{p+1} f_{p+1}(x_{p+1})`
  using `c.f_f p` (`f_{p+1}∘f_p = 0`).
Finally `c.totalD (-1) y = x` by `funext p`, `cases p`, reading off the recorded
construction equations (the `p=0` and `p+1` cases of `totalD_apply_zero` /
`totalD_apply_succ`, `dPartHom_apply`, `fPartHom_apply`). -/
@[stacks 0H0Q]
theorem total_H0_eq_zero (c : CplxCplx)
    (hH : ∀ p : ℕ, c.InternalCohomologyVanishes p)
    (x : c.Tot 0) (hx : c.totalD 0 x = 0) :
    ∃ y : c.Tot (-1), c.totalD (-1) y = x := by
  classical
  -- Base witness: `x 0`, cast to the degree `-0` in which `hH 0` consumes it, is a cocycle.
  have hbase : c.d 0 (-(0:ℤ))
      (c.cast 0 (show (0:ℤ) - ((0:ℕ):ℤ) = -(0:ℤ) by simp) (x 0)) = 0 := by
    rw [d_cast, AddEquivClass.map_eq_zero_iff]
    exact d_eq_zero_of_totalD_eq_zero c hx
  -- The cocycle fed to `hH (p+1)` at the inductive step: `(-1)^{p+1} • r_{p+1}`.
  let zc : (p : ℕ) → c.A p (-1 - (p:ℤ)) → c.A (p+1) (-(((p+1:ℕ)):ℤ)) :=
    fun p yp => ((-1:ℤ)^(p+1)) • c.cast (p+1)
      (show -((p:ℤ)+1) = -(((p+1:ℕ)):ℤ) by push_cast; ring)
        (c.cast (p+1) (show (0:ℤ) - ((p+1:ℕ):ℤ) = -((p:ℤ)+1) by push_cast; ring) (x (p+1))
          - c.cast (p+1) (show (-1 - (p:ℤ)) = -((p:ℤ)+1) by ring) (c.f p (-1 - (p:ℤ)) yp))
  have hzc : ∀ (p : ℕ) (yp : c.A p (-1 - (p:ℤ))), c.StageInvariant x p yp →
      c.d (p+1) (-(((p+1:ℕ)):ℤ)) (zc p yp) = 0 := by
    intro p yp hinv
    show c.d (p+1) (-(((p+1:ℕ)):ℤ)) (((-1:ℤ)^(p+1)) • c.cast (p+1) _ _) = 0
    rw [map_zsmul, d_cast, d_sub_eq_zero_of_stageInvariant c hx hinv, map_zero, smul_zero]
  -- `StageInvariant` for a base witness produced from `hH 0`.
  have stageInvariant_base : ∀ (w : c.A 0 (-(0:ℤ) - 1)),
      c.cast 0 (show -(0:ℤ) - 1 + 1 = -(0:ℤ) by ring) (c.d 0 (-(0:ℤ) - 1) w)
        = c.cast 0 (show (0:ℤ) - ((0:ℕ):ℤ) = -(0:ℤ) by simp) (x 0) →
      c.StageInvariant x 0 (c.cast 0 (show (-(0:ℤ)) - 1 = -1 - (0:ℤ) by ring) w) := by
    intro w hw
    rw [c.stageInvariant_iff]
    rw [pow_zero, one_smul]
    exact congrArg (c.f 0 _) ((c.cast_d_cast 0 _ _ w).trans hw)
  -- `StageInvariant` for a successor witness produced from `hH (p+1)`.
  have stageInvariant_succ : ∀ (p : ℕ) (yp : c.A p (-1 - (p:ℤ)))
      (w : c.A (p+1) (-(((p+1:ℕ)):ℤ) - 1)),
      c.cast (p+1) (show -(((p+1:ℕ)):ℤ) - 1 + 1 = -(((p+1:ℕ)):ℤ) by ring)
          (c.d (p+1) (-(((p+1:ℕ)):ℤ) - 1) w) = zc p yp →
      c.StageInvariant x (p+1)
        (c.cast (p+1) (show (-(((p+1:ℕ)):ℤ)) - 1 = -1 - ((p+1:ℕ):ℤ) by push_cast; ring) w) := by
    intro p yp w hw
    -- `hw : cast (d w) = (-1)^{p+1} • cast (cast (x (p+1)) - cast (f_p yp))`
    rw [c.stageInvariant_iff]
    -- LHS: f_{p+1} (cast (d (cast w)))
    rw [show c.d (p+1) (-1 - ((p+1:ℕ):ℤ))
            (c.cast (p+1) (show (-(((p+1:ℕ)):ℤ)) - 1 = -1 - ((p+1:ℕ):ℤ) by push_cast; ring) w)
          = c.cast (p+1) (show (-(((p+1:ℕ)):ℤ)) - 1 + 1 = -1 - ((p+1:ℕ):ℤ) + 1 by push_cast; ring)
              (c.d (p+1) (-(((p+1:ℕ)):ℤ) - 1) w) from c.d_cast (p+1) _ w]
    rw [cast_cast]
    -- Now LHS arg is `cast (d w)`; use hw.
    rw [show c.cast (p+1) (show (-(((p+1:ℕ)):ℤ)) - 1 + 1 = -((p+1:ℕ):ℤ) by push_cast; ring)
              (c.d (p+1) (-(((p+1:ℕ)):ℤ) - 1) w)
          = ((-1:ℤ)^(p+1)) • c.cast (p+1) (show -((p:ℤ)+1) = -((p+1:ℕ):ℤ) by push_cast; ring)
              (c.cast (p+1) (show (0:ℤ) - ((p+1:ℕ):ℤ) = -((p:ℤ)+1) by push_cast; ring) (x (p+1))
                - c.cast (p+1) (show (-1 - (p:ℤ)) = -((p:ℤ)+1) by ring) (c.f p (-1 - (p:ℤ)) yp))
        from hw]
    rw [map_zsmul, map_sub, cast_cast, map_sub]
    -- `f_{p+1} (cast (f_p yp)) = 0` by `f_f`.
    rw [show c.f (p+1) (-((p+1:ℕ):ℤ)) (c.cast (p+1) (by push_cast; ring)
            (c.cast (p+1) (show (-1 - (p:ℤ)) = -((p:ℤ)+1) by ring) (c.f p (-1 - (p:ℤ)) yp)))
              = 0 from by
      rw [cast_cast, f_cast]
      rw [c.f_f p (-1 - (p:ℤ)) yp]
      simp]
    rw [sub_zero, f_cast]
  let Y : (p : ℕ) → Σ' (yp : c.A p (-1 - (p:ℤ))), c.StageInvariant x p yp := fun p => Nat.rec
    (motive := fun p => Σ' (yp : c.A p (-1 - (p:ℤ))), c.StageInvariant x p yp)
    ⟨c.cast 0 (show (-(0:ℤ)) - 1 = -1 - (0:ℤ) by ring) (Classical.choose (hH 0 _ hbase)),
      stageInvariant_base _ (Classical.choose_spec (hH 0 _ hbase))⟩
    (fun p ih =>
      let h := hH (p+1) (zc p ih.fst) (hzc p ih.fst ih.snd)
      ⟨c.cast (p+1) (show (-(((p+1:ℕ)):ℤ)) - 1 = -1 - ((p+1:ℕ):ℤ) by push_cast; ring)
        (Classical.choose h), stageInvariant_succ p ih.fst _ (Classical.choose_spec h)⟩)
    p
  -- The coboundary witness.
  refine ⟨fun p => (Y p).fst, ?_⟩
  funext p
  cases p with
  | zero =>
    -- `(Y 0).fst = cast (choose ...)`; its `d` is `cast (x 0)` by `choose_spec`.
    have hd0 : c.cast 0 (show -(0:ℤ) - 1 + 1 = -(0:ℤ) by ring)
          (c.d 0 (-(0:ℤ) - 1) (Classical.choose (hH 0 _ hbase)))
        = c.cast 0 (show (0:ℤ) - ((0:ℕ):ℤ) = -(0:ℤ) by simp) (x 0) :=
      Classical.choose_spec (hH 0 _ hbase)
    rw [totalD_apply_zero, dPartHom_apply]
    show c.cast 0 _ (((-1:ℤ)^(0:ℕ)) • c.d 0 ((-1) - ((0:ℕ):ℤ))
        (c.cast 0 (show (-(0:ℤ)) - 1 = -1 - (0:ℤ) by ring) (Classical.choose (hH 0 _ hbase)))) = x 0
    rw [pow_zero, one_smul]
    exact (c.cast_d_cast 0 _ _ _).trans hd0
  | succ p =>
    rw [totalD_apply_succ, dPartHom_apply, fPartHom_apply]
    set zz : c.A (p+1) (-(((p+1:ℕ)):ℤ)) := zc p (Y p).fst with hzz
    set ww : c.A (p+1) (-(((p+1:ℕ)):ℤ) - 1) :=
      Classical.choose (hH (p+1) zz (hzc p (Y p).fst (Y p).snd)) with hww
    have hdS : c.cast (p+1) (show -(((p+1:ℕ)):ℤ) - 1 + 1 = -(((p+1:ℕ)):ℤ) by ring)
          (c.d (p+1) (-(((p+1:ℕ)):ℤ) - 1) ww) = zz :=
      Classical.choose_spec (hH (p+1) zz (hzc p (Y p).fst (Y p).snd))
    -- `(Y (p+1)).fst = cast ww`.
    show c.cast (p+1) _ (((-1:ℤ)^(p+1)) • c.d (p+1) ((-1) - ((p+1:ℕ):ℤ))
          (c.cast (p+1) (show (-(((p+1:ℕ)):ℤ)) - 1 = -1 - ((p+1:ℕ):ℤ) by push_cast; ring) ww))
        + c.cast (p+1) _ (c.f p ((-1) - (p:ℕ)) (Y p).fst) = x (p+1)
    rw [show c.d (p+1) ((-1) - ((p+1:ℕ):ℤ))
            (c.cast (p+1) (show (-(((p+1:ℕ)):ℤ)) - 1 = -1 - ((p+1:ℕ):ℤ) by push_cast; ring) ww)
          = c.cast (p+1) (show (-(((p+1:ℕ)):ℤ)) - 1 + 1 = -1 - ((p+1:ℕ):ℤ) + 1 by push_cast; ring)
              (c.d (p+1) (-(((p+1:ℕ)):ℤ) - 1) ww) from c.d_cast (p+1) _ ww]
    rw [map_zsmul]
    rw [show c.cast (p+1) (show (-(((p+1:ℕ)):ℤ)) - 1 + 1 = -1 - ((p+1:ℕ):ℤ) + 1 by push_cast; ring)
            (c.d (p+1) (-(((p+1:ℕ)):ℤ) - 1) ww)
          = c.cast (p+1) (show (-(((p+1:ℕ)):ℤ)) = -1 - ((p+1:ℕ):ℤ) + 1 by push_cast; ring) zz
        from by rw [← hdS, cast_cast]]
    -- LHS now `(-1)^{p+1} • cast (cast zz) + cast (f (Y p).fst)`; unfold `zz` and simplify.
    rw [cast_cast, hzz]
    show ((-1:ℤ)^(p+1)) • c.cast (p+1)
          (show (-(((p+1:ℕ)):ℤ)) = (0:ℤ) - ((p+1:ℕ):ℤ) by push_cast; ring)
          (((-1:ℤ)^(p+1)) • c.cast (p+1)
            (show -((p:ℤ)+1) = -(((p+1:ℕ)):ℤ) by push_cast; ring)
            (c.cast (p+1) (show (0:ℤ) - ((p+1:ℕ):ℤ) = -((p:ℤ)+1) by push_cast; ring) (x (p+1))
              - c.cast (p+1) (show (-1 - (p:ℤ)) = -((p:ℤ)+1) by ring)
                  (c.f p (-1 - (p:ℤ)) (Y p).fst)))
        + c.cast (p+1) (show ((-1:ℤ)) - (p:ℕ) = (0:ℤ) - ((p+1:ℕ):ℤ) by push_cast; ring)
            (c.f p ((-1) - (p:ℕ)) (Y p).fst) = x (p+1)
    rw [map_zsmul, cast_cast, smul_smul, neg_one_pow_mul_self, one_smul]
    rw [map_sub, cast_cast, cast_cast]
    rw [show c.cast (p+1) (show (-1 - (p:ℤ)) = (0:ℤ) - ((p+1:ℕ):ℤ) by push_cast; ring)
            (c.f p (-1 - (p:ℤ)) (Y p).fst)
          = c.cast (p+1) (show ((-1:ℤ)) - (p:ℕ) = (0:ℤ) - ((p+1:ℕ):ℤ) by push_cast; ring)
              (c.f p ((-1) - (p:ℕ)) (Y p).fst) from by congr 1]
    rw [sub_add_cancel]
    exact c.cast_rfl (p+1) (x (p+1))

/-- The total differential squares to zero: `D^{n+1} ∘ D^n = 0`.  This certifies
that `Tot_π` together with `D` is a genuine cochain complex (one half of
`H^0 = 0` is then automatic; the content of `total_H0_eq_zero` is the reverse
inclusion `ker(D^0) ⊆ im(D^{-1})`). -/
theorem totalD_totalD_eq_zero (c : CplxCplx) {n : ℤ} (x : c.Tot n) :
    c.totalD (n + 1) (c.totalD n x) = 0 := by
  funext p
  show c.totalD (n + 1) (c.totalD n x) p = (0 : c.A p (n + 1 + 1 - p))
  match p with
  | 0 =>
    rw [totalD_apply_zero, dPartHom_apply, totalD_apply_zero, dPartHom_apply]
    simp only [pow_zero, one_smul, d_cast]
    rw [cast_cast]
    rw [c.d_d 0 _]
    simp
  | (p' + 1) =>
    rw [totalD_apply_succ, dPartHom_apply, fPartHom_apply, totalD_apply_succ]
    rw [dPartHom_apply, fPartHom_apply]
    simp only [map_add, map_zsmul, smul_add, d_cast]
    rw [cast_cast, c.d_d (p' + 1) _]
    simp only [map_zero, smul_zero, zero_add]
    rw [c.f_d p' (n - p')]
    match p' with
    | 0 =>
      rw [totalD_apply_zero, dPartHom_apply]
      simp only [f_cast, pow_zero, one_smul, cast_cast]
      rw [pow_succ, pow_zero, one_mul]
      simp [neg_smul]
    | (p'' + 1) =>
      rw [totalD_apply_succ, dPartHom_apply, fPartHom_apply]
      simp only [map_add, map_zsmul, f_cast, cast_cast]
      rw [c.f_f p'' (n - p'')]
      simp only [map_zero, add_zero]
      rw [pow_succ ((-1:ℤ)) (p'' + 1)]
      simp [neg_smul]

/-- The total differential composed with itself is the zero homomorphism, the
hom-level form of `totalD_totalD_eq_zero`: `(Tot_π, D)` is a cochain complex. -/
theorem totalD_comp_totalD (c : CplxCplx) (n : ℤ) :
    (c.totalD (n + 1)).comp (c.totalD n) = 0 :=
  AddMonoidHom.ext fun x => c.totalD_totalD_eq_zero x

end CplxCplx
