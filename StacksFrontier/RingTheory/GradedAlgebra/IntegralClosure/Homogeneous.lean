module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.GradedAlgebra.Basic
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.GradedAlgebra.IntegralClosure.GradedTwist
public import StacksFrontier.RingTheory.GradedAlgebra.IntegralClosure.TwoVariableDescent

/-!
# Homogeneous components of integral elements

The monic-quotient descent (`monic_quotient_descent`), the diameter induction showing that
the homogeneous components of an integral Laurent polynomial are integral
(`graded_component_isIntegral`, `coeff_isIntegral`), and the main results
`integralClosure_isHomogeneous` and `integralClosure_carrier_eq` (Stacks Tag 077G).
-/

@[expose] public section

universe u_1 u_2
variable {R : Type u_1} {S : Type u_2} [CommRing R] [CommRing S] [Algebra R S]
variable (ℛ : ℕ → AddSubgroup R) (𝒮 : ℕ → AddSubgroup S)
variable [GradedRing ℛ] [GradedRing 𝒮]

open LaurentPolynomial in
/-- **(Helper for L3a-C-outer) The split-finite-free descent data for the monic-quotient
construction.**

This packages the genuine HEAVY content of `monic_quotient_outer_descent` as an existential
bundle of exactly the data consumed by the already-proved `isIntegralElem_of_split_finite_free`.

Concretely: from `hint` (the multiplier `(t^n − t^m)·(C(C z)·Tⁿ)` integral over the 2-variable
base `(LaurentPolynomial R)[T;T⁻¹]` along `Ψ`), there is a finite-free monic-quotient extension
`B' := B̃[T;T⁻¹]` (where `B̃ := AdjoinRoot (g.map Φ₁)` for the Selmer polynomial
`g := X^d − X − 1` of degree `d := (m − n).natAbs ≥ 1`), with:
* base maps `e : (LaurentPolynomial R)[T;T⁻¹] →+* Ã[T;T⁻¹]` and `f' : Ã[T;T⁻¹] →+* B̃[T;T⁻¹]`
  lifted from `AdjoinRoot.of`, intertwining `Ψ` (`f'.comp e = ι.comp Ψ`);
* the clean inner base-change inclusion `ι : (LaurentPolynomial S)[T;T⁻¹] →+* B̃[T;T⁻¹]`
  (injective, no forced `ι(t) = Ū`);
* the `Ū⁰`-coordinate projection `π : B̃[T;T⁻¹] →+ (LaurentPolynomial S)[T;T⁻¹]` retracting `ι`
  and right-`ι B`-linear;
* the `Ū⁰`-coordinate pull-back of base coefficients (`hcoeff`);
* AND the key integrality fact `f'.IsIntegralElem (ι (C(C z)·Tⁿ))`, obtained by transporting
  `hint` along the ring hom `q` (inner `t ↦ Ū`, outer `T` preserved), where `q(C(t^n−t^m))` is a
  unit (`= −Ū^{n+1}`) stripped via `isIntegralElem_of_unit_mul`, followed by
  `RingHom.IsIntegral.trans` (Stacks 00GN) to descend `Ã → LaurentPolynomial R`.

Stated separately so as to isolate the AdjoinRoot, freeness, unit-strip and descent content,
leaving `monic_quotient_outer_descent` a clean application of
`isIntegralElem_of_split_finite_free`. -/
theorem monic_quotient_outer_descent_data
    (z : S) (n m : ℤ) (hnm : n ≠ m)
    (hint : (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))).IsIntegralElem
        (C ((LaurentPolynomial.T n - LaurentPolynomial.T m : LaurentPolynomial S)) *
          (C (LaurentPolynomial.C z) * T n))) :
    ∃ (A' B' : Type (max u_1 u_2)) (_ : CommRing A') (_ : CommRing B')
      (e : (LaurentPolynomial R)[T;T⁻¹] →+* A') (f' : A' →+* B')
      (ι : (LaurentPolynomial S)[T;T⁻¹] →+* B')
      (π : B' →+ (LaurentPolynomial S)[T;T⁻¹]),
      f'.comp e = ι.comp (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S)))
        ∧ Function.Injective ι
        ∧ (∀ b : (LaurentPolynomial S)[T;T⁻¹], π (ι b) = b)
        ∧ (∀ (cc : B') (b : (LaurentPolynomial S)[T;T⁻¹]), π (cc * ι b) = π cc * b)
        ∧ (∀ ct : A', ∃ c₀ : (LaurentPolynomial R)[T;T⁻¹],
            (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))) c₀ = π (f' ct))
        ∧ f'.IsIntegralElem (ι (C (LaurentPolynomial.C z) * T n)) :=
  mqod_inner z n m hnm hint

open LaurentPolynomial in
/-- **(L3a-C-outer) Outer-variable monic-quotient descent (the HEAVY construction, REPAIRED).**

Replaces the FLAWED `monic_quotient_image_isIntegral` bundle (branch-8, FALSE: it conflated the
twist/inner `t` and original/outer `T` variables — see
the construction below).  Here we keep the surviving monomial in the
**OUTER** `T` throughout, quotienting only on the INNER `t`.

From `hint` — `(t^n − t^m)·(C(C z)·Tⁿ)` integral over `(LaurentPolynomial R)[T;T⁻¹]` along
`Ψ := AddMonoidAlgebra.mapRingHom ℤ Φ₁` — conclude that the **pure outer-`T` monomial**
`C(C z)·Tⁿ` (NO inner-`t` power on the coefficient `C z`) is integral over the SAME 2-variable
base `(LaurentPolynomial R)[T;T⁻¹]` along `Ψ`.

Mechanism (descent done correctly):
* WLOG `n < m`; `d := (m−n).toNat ≥ 1`.  `g : (LaurentPolynomial R)[X]` monic of degree `d`
  with `Ū := AdjoinRoot.root` a UNIT and `Ū^m − Ū^n = 1` (so the multiplier `t^n − t^m ↦ −1`).
  `Ã := AdjoinRoot g` finite FREE over `LaurentPolynomial R` (`AdjoinRoot.powerBasis'`), `B̃`
  likewise over `LaurentPolynomial S`.
* `q : (LaurentPolynomial S)[T;T⁻¹] →+* B̃[T;T⁻¹]` sends the inner `t ↦ Ū`
(`LaurentPolynomial.eval₂`,
  `Ū` a unit) and PRESERVES the outer `T`.  Then `q(C(t^n − t^m)) = Ū^n − Ū^m = −1` and the
  outer `Tⁿ` survives.  `RingHom.IsIntegralElem.map` on `hint`, then strip `−1`
  (`isIntegralElem_of_unit_mul`), descend `Ã → LaurentPolynomial R` (`RingHom.IsIntegral.trans`,
  00GN), and project onto the `Ū⁰`-summand (`isIntegralElem_of_split_finite_free`, REUSED with
  `B := (LaurentPolynomial S)[T;T⁻¹]`, `x := C(C z)·Tⁿ`, `ι` the clean inner base-change
  inclusion — `x` carries NO inner-`t` power, so the retraction picture is CONSISTENT, no forced
  `ι(t)=Ū`).
* This sub-lemma LIKELY needs its own AND sub-decomposition; take it FIRST per AND-node policy. -/
theorem monic_quotient_outer_descent
    (z : S) (n m : ℤ) (hnm : n ≠ m)
    (hint : (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))).IsIntegralElem
        (C ((LaurentPolynomial.T n - LaurentPolynomial.T m : LaurentPolynomial S)) *
          (C (LaurentPolynomial.C z) * T n))) :
    (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))).IsIntegralElem
      (C (LaurentPolynomial.C z) * T n) := by
  -- the docstring's target `Ū^m − Ū^n = 1` (with Ū a unit) is NOT realizable when `0 ∈ {n,m}`
  -- (e.g. n=0 forces Ū^m=2, needs 2 a unit, fails over R=ℤ).  CORRECT framing: make the
  -- multiplier `t^n − t^m` become *a* unit (not exactly −1).  Use the SELMER polynomial
  -- `g_d := U^d − U − 1 ∈ (LaurentPolynomial R)[X]` (monic, deg d = (max−min of {m,n} diff)≥1):
  -- its root `ū` satisfies `ū^d − 1 = ū`, and `g_d(0) = −1` makes `ū` a UNIT; then
  -- `t^n − t^m = t^n(1 − t^d) ↦ ū^n(1 − ū^d) = ū^n(−ū) = −ū^{n+1}`, manifestly a unit
  -- (`Res(U^d−1, g_d) = ∏ α = ±1`).  Strip via `isIntegralElem_of_unit_mul` (PROVED).
  -- HEAVY.  Build `g_d`/`Ã`/`B̃`/`q` (inner `t↦ū` unit, outer `T` preserved), strip the unit,
  -- descend (`RingHom.IsIntegral.trans`), project onto the `Ū⁰`-summand
  -- (`isIntegralElem_of_split_finite_free`).  See docstring + v3 177–209.
  -- The monomial stays in the OUTER `T` throughout (avoids the branch-8 variable conflation).
  -- The heavy AdjoinRoot/freeness/unit-strip/descent content is isolated in
  -- `monic_quotient_outer_descent_data`; here we just apply the proved generic descent lemma.
  obtain ⟨A', B', _, _, _, f', ι, π, _, _, hπι, hπmul, hcoeff, hint'⟩ :=
    monic_quotient_outer_descent_data z n m hnm hint
  exact isIntegralElem_of_split_finite_free
    (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))) f' ι π hπι hπmul hcoeff
    (C (LaurentPolynomial.C z) * T n) hint'

/-- Mapping the coefficients along `f` sends `C a` to `C (f a)`. -/
private theorem mapRingHom_C {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) := by
  rw [LP_C_eq_single, AddMonoidAlgebra.mapRingHom_single, LP_C_eq_single]

/-- Mapping the coefficients along `f` fixes the monomials `T n`. -/
private theorem mapRingHom_T {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (n : ℤ) :
    AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  rw [LaurentPolynomial.T, AddMonoidAlgebra.mapRingHom_single, map_one]; rfl

/-- Evaluating `T ↦ 1` commutes with mapping the coefficients along `f`. -/
private theorem eval_one_comp_mapRingHom {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    (LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ)).comp (AddMonoidAlgebra.mapRingHom ℤ f)
      = f.comp (LaurentPolynomial.eval₂ (RingHom.id A) (1 : Aˣ)) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    rw [← LP_C_eq_single, RingHom.comp_apply, RingHom.comp_apply, mapRingHom_C,
      LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_C]
    simp
  · intro m
    change LaurentPolynomial.eval₂ (RingHom.id B) (1 : Bˣ)
        (AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.T m))
      = f (LaurentPolynomial.eval₂ (RingHom.id A) (1 : Aˣ) (LaurentPolynomial.T m))
    rw [mapRingHom_T, LaurentPolynomial.eval₂_T, LaurentPolynomial.eval₂_T]
    simp

open LaurentPolynomial in
/-- **(L3a-C-inner) Inner-variable specialization `t ↦ 1` (mechanical).**

From `Ψ`-integrality of the pure outer-`T` monomial `C(C z)·Tⁿ` over
`(LaurentPolynomial R)[T;T⁻¹]`,
specialize the INNER twist variable `t ↦ 1` to land `Φ`-integrality of `C z · Tⁿ` over the
ORIGINAL `S[T;T⁻¹]` along `Φ := AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)`.

The inner `t ↦ 1` evaluation is the ring hom
`ε := AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.eval₂ (RingHom.id S) 1)` lifted over the
outer `T` (it fixes the outer `T`, evaluates the inner `t ↦ 1` coefficientwise).  It intertwines
`Ψ` over `Φ` (`ε ∘ Ψ = Φ ∘ ε_R`), and `ε (C(C z)·Tⁿ) = C z · Tⁿ` (since `eval₂ … 1 (C z) = z`).
Transport the monic relation along `ε` (`RingHom.IsIntegralElem.map`) and identify the base
image with `R[T;T⁻¹]` via `ε_R ∘ (algebraMap R[T;T⁻¹] (LaurentPolynomial R)[T;T⁻¹]) = id`.
Same flavor as L3b's `T↦1` specialization; SHORT, try `lean-closer` directly. -/
theorem inner_specialize
    (z : S) (n : ℤ)
    (hint : (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))).IsIntegralElem
      (C (LaurentPolynomial.C z) * T n)) :
    (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)).IsIntegralElem
      (LaurentPolynomial.C z * LaurentPolynomial.T n) := by
  --   `eval₂(id_S,1) ∘ Φ₁ = algebraMap R S ∘ eval₂(id_R,1)` was machine-verified.)
  -- Specialize inner `t ↦ 1` (`LaurentPolynomial.eval₂ (RingHom.id S) 1`, lifted over outer T);
  -- transport with `RingHom.IsIntegralElem.map`; identify base image with `R[T;T⁻¹]`.
  set εS : LaurentPolynomial S →+* S := LaurentPolynomial.eval₂ (RingHom.id S) (1 : Sˣ) with hεS
  set εR : LaurentPolynomial R →+* R := LaurentPolynomial.eval₂ (RingHom.id R) (1 : Rˣ) with hεR
  set ε : (LaurentPolynomial S)[T;T⁻¹] →+* S[T;T⁻¹] := AddMonoidAlgebra.mapRingHom ℤ εS with hε
  -- crux: inner identity εS ∘ Φ₁ = (algebraMap R S) ∘ εR
  have hinner : εS.comp (Φ₁ (R := R) (S := S)) = (algebraMap R S).comp εR :=
    eval_one_comp_mapRingHom (algebraMap R S)
  -- crux at outer level
  have hcrux : ε.comp (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S)))
      = (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)).comp
          (AddMonoidAlgebra.mapRingHom ℤ εR) := by
    rw [hε, ← AddMonoidAlgebra.mapRingHom_comp, ← AddMonoidAlgebra.mapRingHom_comp, hinner]
  -- compute ε on the target element
  have htgt :
      ε (C (LaurentPolynomial.C z) * T n) = LaurentPolynomial.C z * LaurentPolynomial.T n := by
    rw [show (C (LaurentPolynomial.C z) * T n : (LaurentPolynomial S)[T;T⁻¹])
          = AddMonoidAlgebra.single n (LaurentPolynomial.C z) from by
          rw [← LaurentPolynomial.single_eq_C_mul_T], hε, AddMonoidAlgebra.mapRingHom_single]
    rw [hεS, LaurentPolynomial.eval₂_C, RingHom.id_apply]
    rw [← LaurentPolynomial.single_eq_C_mul_T]
  -- transport hint along ε
  have hmap := hint.map ε
  rw [htgt, hcrux] at hmap
  exact isIntegralElem_precomp _ _ _ hmap

open LaurentPolynomial in
/-- **(L3a-C) Monic-quotient descent (the `(t^m − t^n) = 1` specialization + transitivity
+ split-finite-extension projection).**

Given `n ≠ m` and `(t^n − t^m)·(C z · Tⁿ)` integral over `(LaurentPolynomial R)[T;T⁻¹]`
along `Ψ` (output of L3a-B with `z = w n`), conclude `C z · Tⁿ` is integral over
`R[T;T⁻¹]` along the ORIGINAL `Φ := AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)`.

Mechanism:
* WLOG `n < m` (swap roles otherwise; `t^n − t^m = −(t^m − t^n)`).  Let
  `g := X^b − X^a − 1 ∈ R[X]` (monic of degree `b = m`) realizing `t^m − t^n`:
  pass to the finite-free monic quotient `R̃ := (LaurentPolynomial R)[U]/(g)` (and `S̃`).
  There `t^m − t^n ↦ 1`, so the multiplier `(t^n − t^m) ↦ −1`, a unit.
* `R̃` is module-finite FREE over `LaurentPolynomial R` (monic deg-`b` relation;
  `AdjoinRoot.powerBasis'`).  Strip the unit `−1` (`isIntegralElem_of_unit_mul`), get
  `image of (C z·Tⁿ)` integral over `R̃`; by `RingHom.IsIntegral.trans` (00GN) integral
  over `LaurentPolynomial R`.
* Project the monic relation onto the `Ū⁰`-summand of the free module `S̃`
  (`isIntegralElem_of_split_finite_free`) to get a monic relation for `C z · Tⁿ` over
  `LaurentPolynomial R = R[T;T⁻¹]` along `Φ`.

The unit being stripped is `−1`, so the proved `isIntegralElem_of_unit_mul` applies; NO
`t^s−1` unit claim is used. -/
theorem monic_quotient_descent
    (z : S) (n m : ℤ) (hnm : n ≠ m)
    (hint : (AddMonoidAlgebra.mapRingHom ℤ (Φ₁ (R := R) (S := S))).IsIntegralElem
        (C ((LaurentPolynomial.T n - LaurentPolynomial.T m : LaurentPolynomial S)) *
          (C (LaurentPolynomial.C z) * T n))) :
    (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)).IsIntegralElem
      (LaurentPolynomial.C z * LaurentPolynomial.T n) := by
  -- genuine nonzero difference, NOT the refuted `∀ Δ` shape; finite-free monic quotient
  -- makes `Ū` auto-invertible so `t^m−t^n↦1` literally, no `t^s−1`-unit/resultant claim.)
  -- Assembled from the two sub-lemmas of the (repaired) AND node, keeping the surviving
  -- monomial in the OUTER `T` throughout (avoids the branch-8 variable-conflation flaw):
  --   `monic_quotient_outer_descent`: outer-`T` monomial `C(C z)·Tⁿ` integral over the 2-var
  --       base along `Ψ` (AdjoinRoot-on-inner-`t` quotient, unit strip, trans, Ū⁰-projection).
  --   `inner_specialize`: inner `t ↦ 1` specialization ⇒ `C z·Tⁿ` integral over `S[T;T⁻¹]`/`Φ`.
  exact inner_specialize z n (monic_quotient_outer_descent z n m hnm hint)

/-! ============================================================================
    L3a (v5) — diameter/tower induction replacing the unsound `two_term_isolate`.

    Three generic
    lemmas over an arbitrary ring hom `ψ : A →+* B` (replacing the specific
    `algebraMap R S`), assembled by `single_monomial_isIntegral` at the `j = 0`
    instance `A = R`, `B = S`, `ψ = algebraMap R S`.
    ============================================================================ -/

open LaurentPolynomial in
/-- **(L3a-Cgen) Generic single-factor strip with a CONSTANT coefficient.**

This is the `ψ`-generic version of `monic_quotient_descent`: replacing the
specific `(R, S, algebraMap R S)` with an arbitrary `(A, B, ψ : A →+* B)`.  Its
proof transfers verbatim from `monic_quotient_descent` (whose only ingredients —
`monic_quotient_outer_descent` and `inner_specialize` — go through for any base
ring hom, since the finite-free monic-quotient mechanism and the `t ↦ 1`
specialization are insensitive to which base hom is used).

Given `n ≠ m` and `(t^n − t^m)·(C (C z)·Tⁿ)` integral over the two-variable base
`(LaurentPolynomial A)[T;T⁻¹]` along
`Lψ' := AddMonoidAlgebra.mapRingHom ℤ (AddMonoidAlgebra.mapRingHom ℤ ψ)`, with the
inner constant coefficient `z : B`, conclude `C z · Tⁿ` is integral over
`LaurentPolynomial A` along `Lψ := AddMonoidAlgebra.mapRingHom ℤ ψ`. -/
theorem monic_quotient_descent_step {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (z : B) (n m : ℤ) (hnm : n ≠ m)
    (hint : (AddMonoidAlgebra.mapRingHom ℤ (AddMonoidAlgebra.mapRingHom ℤ ψ)).IsIntegralElem
        (LaurentPolynomial.C ((LaurentPolynomial.T n - LaurentPolynomial.T m : LaurentPolynomial
            B)) *
          (LaurentPolynomial.C (LaurentPolynomial.C z) * LaurentPolynomial.T n))) :
    (AddMonoidAlgebra.mapRingHom ℤ ψ).IsIntegralElem
      (LaurentPolynomial.C z * LaurentPolynomial.T n) := by
  -- via `ψ.toAlgebra`: `algebraMap A B = ψ` defeq, so the doubly/singly mapped ring homs
  -- match; the `n ≠ m` multiplier `T^n − T^m` is provably nonzero, ruling out the
  -- refuted zero-multiplier pattern).
  let : Algebra A B := ψ.toAlgebra
  exact monic_quotient_descent (R := A) (S := B) z n m hnm hint

open LaurentPolynomial in
/-- Power of the degree-twist unit `C(T 1)·T` is `C(T n)·T^n`. -/
theorem hpow_unit_twist {K : Type*} [CommRing K]
    (v : (LaurentPolynomial (LaurentPolynomial K))ˣ)
    (hv : (v : LaurentPolynomial (LaurentPolynomial K))
      = LaurentPolynomial.C (LaurentPolynomial.T 1) * LaurentPolynomial.T 1) (n : ℤ) :
    ((v^n : (LaurentPolynomial (LaurentPolynomial K))ˣ) :
      LaurentPolynomial (LaurentPolynomial K))
      = LaurentPolynomial.C (LaurentPolynomial.T n) * LaurentPolynomial.T n := by
  have hvinv : ((v⁻¹ : (LaurentPolynomial (LaurentPolynomial K))ˣ) :
      LaurentPolynomial (LaurentPolynomial K))
      = LaurentPolynomial.C (LaurentPolynomial.T (-1)) * LaurentPolynomial.T (-1) := by
    rw [← Units.mul_eq_one_iff_inv_eq, hv]
    rw [mul_mul_mul_comm, ← map_mul, ← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
    norm_num
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [zpow_add_one, Units.val_mul, ih, hv, mul_mul_mul_comm, ← map_mul,
      ← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
  | pred k ih =>
    rw [zpow_sub_one, Units.val_mul, ih, hvinv, mul_mul_mul_comm, ← map_mul,
      ← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
    congr 2

/-- The degree twist `T n ↦ C (T n) * T n`, fixing the constants, as a ring hom. -/
private theorem exists_degree_twist {K : Type*} [CommRing K] :
    ∃ σ : LaurentPolynomial (LaurentPolynomial K) →+* LaurentPolynomial (LaurentPolynomial K),
      (∀ n : ℤ, σ (LaurentPolynomial.T n)
        = LaurentPolynomial.C (LaurentPolynomial.T n) * LaurentPolynomial.T n) ∧
      ∀ a, σ (LaurentPolynomial.C a) = LaurentPolynomial.C a := by
  have hU : IsUnit (LaurentPolynomial.C (LaurentPolynomial.T 1) * LaurentPolynomial.T 1 :
      LaurentPolynomial (LaurentPolynomial K)) :=
    IsUnit.mul ((LaurentPolynomial.isUnit_T 1).map LaurentPolynomial.C)
      (LaurentPolynomial.isUnit_T 1)
  refine ⟨LaurentPolynomial.eval₂ LaurentPolynomial.C hU.unit, fun n => ?_,
    fun a => LaurentPolynomial.eval₂_C _ _ _⟩
  rw [LaurentPolynomial.eval₂_T, hpow_unit_twist _ hU.unit_spec n]

open LaurentPolynomial in
/-- **(L3a-B v5) Formal extraction lowering the diameter by one.**

Working ring is the two-variable Laurent ring `(LaurentPolynomial B)[T;T⁻¹]`
(outer variable `T`, inner fresh variable `t`), with base map
`Ψ := AddMonoidAlgebra.mapRingHom ℤ (AddMonoidAlgebra.mapRingHom ℤ ψ)`.

Given `x` integral over the two-variable base along `Ψ`, and a peeled degree `p`,
there exists `x' := σ(x) − C(t^p)·x` (σ the degree-twist of
`laurent_twist_preserves_integral`) which is `Ψ`-integral, has zero degree-`p`
component, and whose degree-`k` component (`k ≠ p`) is `(t^k − t^p)·(x k)`.  Thus
`x'` has strictly fewer nonzero `T`-components than `x`.  (See v5 §2 Sub-lemma B.) -/
theorem extract_lower_diameter {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (x : LaurentPolynomial (LaurentPolynomial B))
    (hx : (AddMonoidAlgebra.mapRingHom ℤ (AddMonoidAlgebra.mapRingHom ℤ ψ)).IsIntegralElem x)
    (p : ℤ) :
    ∃ x' : LaurentPolynomial (LaurentPolynomial B),
      (AddMonoidAlgebra.mapRingHom ℤ (AddMonoidAlgebra.mapRingHom ℤ ψ)).IsIntegralElem x' ∧
        x'.coeff p = 0 ∧
        ∀ k, k ≠ p → x'.coeff k
          = (LaurentPolynomial.T k - LaurentPolynomial.T p) * x.coeff k := by
  -- identities (C c·y) k = c·(y k) and (σ x) k = (T k)·(x k) machine-verified; no counterexample)
  classical
  set Φ : LaurentPolynomial A →+* LaurentPolynomial B := AddMonoidAlgebra.mapRingHom ℤ ψ with hΦ
  set Ψ := AddMonoidAlgebra.mapRingHom ℤ (AddMonoidAlgebra.mapRingHom ℤ ψ) with hΨ
  -- Ψ on generators
  obtain ⟨σ, hσT, hσC⟩ := exists_degree_twist (K := B)
  obtain ⟨σA, hσAT, hσAC⟩ := exists_degree_twist (K := A)
  have hΨC : ∀ a : LaurentPolynomial A,
      Ψ (LaurentPolynomial.C a) = LaurentPolynomial.C (Φ a) := mapRingHom_C _
  have hΨT : ∀ n : ℤ, Ψ (LaurentPolynomial.T n) = LaurentPolynomial.T n := mapRingHom_T _
  have hΦT : ∀ n : ℤ, Φ (LaurentPolynomial.T n) = LaurentPolynomial.T n := mapRingHom_T _
  -- coefficient of monomial
  have hcoeffMon : ∀ (a : LaurentPolynomial B) (j k : ℤ),
      ((LaurentPolynomial.C a * LaurentPolynomial.T j :
          LaurentPolynomial (LaurentPolynomial B))).coeff k
        = if k = j then a else 0 := by
    intro a j k
    rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply]; simp [eq_comm]
  -- coefficient identity for σ
  have hσcoeff : ∀ (y : LaurentPolynomial (LaurentPolynomial B)) (k : ℤ),
      (σ y).coeff k = LaurentPolynomial.T k * y.coeff k := by
    intro y k
    induction y using LaurentPolynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq,
        AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]
    | C_mul_T n a =>
      rw [map_mul, hσC, hσT n, ← mul_assoc, ← map_mul]
      rw [hcoeffMon (a * LaurentPolynomial.T n) n k, hcoeffMon a n k]
      split_ifs with h <;> simp [mul_comm, h]
  -- commuting square σ ∘ Ψ = Ψ ∘ σA
  have hsquare : σ.comp Ψ = Ψ.comp σA := by
    apply RingHom.ext; intro y
    simp only [RingHom.comp_apply]
    induction y using LaurentPolynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
    | C_mul_T n a =>
      -- LHS: σ (Ψ (C a * T n))
      rw [map_mul, hΨC, hΨT, map_mul, hσC, hσT]
      -- RHS: Ψ (σA (C a * T n))
      rw [map_mul, hσAC, hσAT, map_mul, map_mul, hΨC, hΨT, hΨC, hΦT]
  -- integrality of σ x
  have hσint : Ψ.IsIntegralElem (σ x) := by
    have h1 : (σ.comp Ψ).IsIntegralElem (σ x) := hx.map σ
    rw [hsquare] at h1
    exact isIntegralElem_precomp Ψ σA (σ x) h1
  -- integrality of C(T p) * x
  have hCTpx : Ψ.IsIntegralElem (LaurentPolynomial.C (LaurentPolynomial.T p) * x) := by
    have := (RingHom.isIntegralElem_map (f := Ψ) (x := LaurentPolynomial.C (LaurentPolynomial.T p))
      ).mul Ψ hx
    rwa [hΨC, hΦT] at this
  -- coefficient of C(T p) * x
  have hCmul : ∀ k, ((LaurentPolynomial.C (LaurentPolynomial.T p) * x :
      LaurentPolynomial (LaurentPolynomial B))).coeff k
        = LaurentPolynomial.T p * x.coeff k := by
    intro k
    rw [LP_C_eq_single, AddMonoidAlgebra.coeff_single_zero_mul]
  -- coefficient of the witness
  have hcoeff : ∀ k,
      ((σ x - LaurentPolynomial.C (LaurentPolynomial.T p) * x :
          LaurentPolynomial (LaurentPolynomial B))).coeff k
        = (LaurentPolynomial.T k - LaurentPolynomial.T p) * x.coeff k := by
    intro k
    rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hσcoeff x k, hCmul k, sub_mul]
  -- the witness
  refine ⟨σ x - LaurentPolynomial.C (LaurentPolynomial.T p) * x, ?_, ?_, ?_⟩
  · exact hσint.sub Ψ hCTpx
  · rw [hcoeff p]; simp
  · intro k _; rw [hcoeff k]

open LaurentPolynomial in
/-- **(L3a v5 — Proposition IND) Graded-component integrality, generic base.**

For any `x : LaurentPolynomial B` integral over `LaurentPolynomial A` along
`Lψ := AddMonoidAlgebra.mapRingHom ℤ ψ`, every `T`-homogeneous component
`C (x k) · T^k` is itself `Lψ`-integral.

Proof is by strong induction on the diameter `r = x.support.card` (v5 §3): the
step adjoins a fresh degree-0 variable (enlarging the base to
`ψ' := AddMonoidAlgebra.mapRingHom ℤ ψ : LaurentPolynomial A →+* LaurentPolynomial B`),
uses `extract_lower_diameter` to produce `x'` of strictly smaller diameter over
the enlarged base, applies the induction hypothesis to `x'` (the tower recursion,
over the strictly larger coefficient ring `LaurentPolynomial B`), and finally
strips the single twist factor with `monic_quotient_descent_step`.  The goal
`single_monomial_isIntegral` is the `j = 0` instance. -/
theorem graded_component_isIntegral {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (x : LaurentPolynomial B)
    (hx : (AddMonoidAlgebra.mapRingHom ℤ ψ).IsIntegralElem x) (k : ℤ) :
    (AddMonoidAlgebra.mapRingHom ℤ ψ).IsIntegralElem
      (LaurentPolynomial.C (x.coeff k) * LaurentPolynomial.T k) := by
  -- v5 diameter/tower induction; recursion measure `x.coeff.support.card`.
  classical
  rcases le_or_gt x.coeff.support.card 1 with hcard | hcard
  · -- Base case: diameter ≤ 1.
    by_cases hxk : x.coeff k = 0
    · -- target component is zero, hence integral
      have hzero : LaurentPolynomial.C (x.coeff k) * LaurentPolynomial.T k = 0 := by rw [hxk]; simp
      rw [hzero]
      exact ⟨Polynomial.X, Polynomial.monic_X, by simp⟩
    · -- k ∈ support, support = {k}, so x = C(x k)·T^k is integral by hx
      have hk_mem : k ∈ x.coeff.support := by rw [Finsupp.mem_support_iff]; exact hxk
      have hsupp : x.coeff.support = {k} := by
        have h1 : ({k} : Finset ℤ) ⊆ x.coeff.support := by simp [hk_mem]
        have h2 : x.coeff.support.card ≤ ({k} : Finset ℤ).card := by simpa using hcard
        exact (Finset.eq_of_subset_of_card_le h1 h2).symm
      have hxeq : x = LaurentPolynomial.C (x.coeff k) * LaurentPolynomial.T k := by
        ext j
        rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
          Finsupp.single_apply]
        by_cases hj : j = k
        · subst hj; simp
        · have : j ∉ x.coeff.support := by rw [hsupp]; simp [hj]
          rw [Finsupp.notMem_support_iff] at this
          rw [this]; simp [Ne.symm hj]
      rw [← hxeq]; exact hx
  · -- Step case: diameter ≥ 2.
    have hcard2 : 2 ≤ x.coeff.support.card := hcard
    -- pick a peeled degree p ∈ support with p ≠ k
    obtain ⟨p, hp_mem, hpk⟩ : ∃ p ∈ x.coeff.support, p ≠ k := by
      by_contra h
      push Not at h
      have hsub : x.coeff.support ⊆ {k} := by intro q hq; simp [h q hq]
      have := Finset.card_le_card hsub
      simp at this; omega
    -- base-change x to the enlarged coefficient ring
    set Cmap : B →+* LaurentPolynomial B := LaurentPolynomial.C with hCmap
    set X : LaurentPolynomial (LaurentPolynomial B) :=
      (AddMonoidAlgebra.mapRingHom ℤ Cmap) x with hXdef
    have hXk : ∀ j, X.coeff j = LaurentPolynomial.C (x.coeff j) := by
      intro j; rw [hXdef, AddMonoidAlgebra.coeff_mapRingHom]
    -- X is integral over the enlarged base
    have hXint :
        (AddMonoidAlgebra.mapRingHom ℤ (AddMonoidAlgebra.mapRingHom ℤ ψ)).IsIntegralElem X := by
      have hmap := hx.map (AddMonoidAlgebra.mapRingHom ℤ Cmap)
      rw [← AddMonoidAlgebra.mapRingHom_comp] at hmap
      apply isIntegralElem_precomp (AddMonoidAlgebra.mapRingHom ℤ (AddMonoidAlgebra.mapRingHom ℤ ψ))
        (AddMonoidAlgebra.mapRingHom ℤ (LaurentPolynomial.C : A →+* LaurentPolynomial A))
      rw [← AddMonoidAlgebra.mapRingHom_comp]
      have hcomp : ((AddMonoidAlgebra.mapRingHom ℤ ψ).comp
            (LaurentPolynomial.C : A →+* LaurentPolynomial A))
          = Cmap.comp ψ := by
        apply RingHom.ext; intro a
        simp only [RingHom.comp_apply]
        ext j
        rw [AddMonoidAlgebra.coeff_mapRingHom]
        simp only [LaurentPolynomial.C_apply, hCmap]
        split <;> simp
      rw [hcomp]
      exact hmap
    -- extract an element of strictly smaller diameter over the enlarged base
    obtain ⟨x', hx'int, hx'p, hx'k⟩ := extract_lower_diameter ψ X hXint p
    -- diameter strictly decreases
    have hdecr : x'.coeff.support.card < x.coeff.support.card := by
      have hsub : x'.coeff.support ⊆ x.coeff.support.erase p := by
        intro j hj
        rw [Finsupp.mem_support_iff] at hj
        have hjp : j ≠ p := by rintro rfl; exact hj hx'p
        rw [Finset.mem_erase]
        refine ⟨hjp, ?_⟩
        rw [Finsupp.mem_support_iff]
        intro hxj
        apply hj
        rw [hx'k j hjp, hXk j, hxj]
        simp
      calc x'.coeff.support.card ≤ (x.coeff.support.erase p).card := Finset.card_le_card hsub
        _ < x.coeff.support.card := Finset.card_erase_lt_of_mem hp_mem
    -- apply the induction hypothesis at the enlarged base and strictly smaller diameter
    have hIH := graded_component_isIntegral (AddMonoidAlgebra.mapRingHom ℤ ψ) x' hx'int k
    -- rewrite x' k = (T k - T p) * C (x k)
    have hx'kval :
        x'.coeff k
          = (LaurentPolynomial.T k - LaurentPolynomial.T p) * LaurentPolynomial.C (x.coeff k) := by
      rw [hx'k k (Ne.symm hpk), hXk k]
    rw [hx'kval] at hIH
    -- reshape into the hypothesis of monic_quotient_descent_step
    have hreshape :
        LaurentPolynomial.C ((LaurentPolynomial.T k - LaurentPolynomial.T p) *
            LaurentPolynomial.C (x.coeff k)) * LaurentPolynomial.T k
          = LaurentPolynomial.C (LaurentPolynomial.T k - LaurentPolynomial.T p) *
              (LaurentPolynomial.C (LaurentPolynomial.C (x.coeff k)) * LaurentPolynomial.T k) := by
      rw [map_mul]; ring
    rw [hreshape] at hIH
    -- strip the single twist factor
    exact monic_quotient_descent_step ψ (x.coeff k) k p (Ne.symm hpk) hIH
  termination_by x.coeff.support.card
  decreasing_by exact hdecr

open LaurentPolynomial in
/-- **(L3a) Monomial isolation — the analytic kernel of Stacks 077G.**

Let `Φ := AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S) : R[T;T⁻¹] →+* S[T;T⁻¹]`.
If `w ∈ S[T;T⁻¹]` is integral over `R[T;T⁻¹]` along `Φ`, then for every `n : ℤ` the
single monomial `C (w n) · T^n` is *itself* integral over `R[T;T⁻¹]` along `Φ`.

Assembled by diameter and tower induction: this is the
`j = 0` instance of the generic graded-component induction
`graded_component_isIntegral` with `A = R`, `B = S`, `ψ = algebraMap R S`, `x = w`. -/
theorem single_monomial_isIntegral
    (w : S[T;T⁻¹])
    (hw : (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)).IsIntegralElem w)
    (n : ℤ) :
    (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)).IsIntegralElem
      (LaurentPolynomial.C (w.coeff n) * LaurentPolynomial.T n) := by
  -- The `j = 0` instance of the diameter/tower induction `graded_component_isIntegral`, with
  -- `A = R`, `B = S`, `ψ = algebraMap R S`, `x = w` and component `n`.
  exact graded_component_isIntegral (algebraMap R S) w hw n

open LaurentPolynomial in
/-- **(L3b) Coefficient of an integral monomial is integral (specialization `T ↦ 1`).**

Let `Φ := AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)`.  If the single monomial
`C s · T^n ∈ S[T;T⁻¹]` is integral over `R[T;T⁻¹]` along `Φ`, then `s` is integral
over `R`.

Apply the `T ↦ 1`
evaluation ring homs
`evₛ := LaurentPolynomial.eval₂ (RingHom.id S) (1 : Sˣ) : S[T;T⁻¹] →+* S` and
`evᵣ := LaurentPolynomial.eval₂ (RingHom.id R) (1 : Rˣ) : R[T;T⁻¹] →+* R`.  They satisfy
the commuting square `evₛ ∘ Φ = (algebraMap R S) ∘ evᵣ` (both fix coefficients via
`algebraMap` and send `T ↦ 1`), and `evₛ (C s · T^n) = s · 1^n = s`
(`LaurentPolynomial.eval₂_C`, `eval₂_T`, `Units.val_one`, `one_zpow`).  Transporting the
integral relation along `evₛ` (`RingHom.IsIntegralElem.map`) shows
`((algebraMap R S).comp evᵣ).IsIntegralElem s`, i.e. `s` is integral over the image of
`R[T;T⁻¹]` under `evᵣ`, which is all of `R` (`evᵣ` is onto `R`, splitting
`algebraMap R R[T;T⁻¹]`).  Concretely: `evᵣ.comp (algebraMap R R[T;T⁻¹]) = RingHom.id R`,
so the monic relation has coefficients literally `algebraMap R S (evᵣ bᵢ)`, exhibiting
`IsIntegral R s` directly. -/
theorem coeff_monomial_isIntegral
    (s : S) (n : ℤ)
    (hmon : (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)).IsIntegralElem
      (LaurentPolynomial.C s * LaurentPolynomial.T n)) :
    IsIntegral R s := by
  -- verified sound, no counterexample; core identities evₛ(C s·T^n)=s, evᵣ(C r)=r checked).
  -- Specialize T ↦ 1 (`eval₂ _ 1`); transport integrality with `RingHom.IsIntegralElem.map`;
  -- identify the base image with R via `evᵣ.comp (algebraMap R R[T;T⁻¹]) = id`.
  set Φ := AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S) with hΦ
  set evₛ : S[T;T⁻¹] →+* S := LaurentPolynomial.eval₂ (RingHom.id S) (1 : Sˣ) with hevₛ
  set evᵣ : R[T;T⁻¹] →+* R := LaurentPolynomial.eval₂ (RingHom.id R) (1 : Rˣ) with hevᵣ
  -- Transport `hmon` along `evₛ`.
  have htrans := hmon.map evₛ
  -- Compute `evₛ (C s * T n) = s`.
  have hval : evₛ (LaurentPolynomial.C s * LaurentPolynomial.T n) = s := by
    rw [map_mul, hevₛ, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T]
    simp
  rw [hval] at htrans
  -- The commuting square: evₛ.comp Φ = (algebraMap R S).comp evᵣ.
  have hsquare : evₛ.comp Φ = (algebraMap R S).comp evᵣ :=
    eval_one_comp_mapRingHom (algebraMap R S)
  rw [hsquare] at htrans
  -- Now `htrans : ((algebraMap R S).comp evᵣ).IsIntegralElem s`.  Descend to R.
  obtain ⟨p, hpmon, hpeval⟩ := htrans
  refine ⟨p.map evᵣ, hpmon.map evᵣ, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hpeval

open LaurentPolynomial in
/-- **(L3) Componentwise integrality.**  Assembles L3a (monomial isolation) and L3b
(`T ↦ 1` specialization): every `T`-coefficient `w n` of an element `w ∈ S[T;T⁻¹]`
integral over `R[T;T⁻¹]` (along `Φ`) is integral over `R`. -/
theorem coeff_isIntegral
    (w : S[T;T⁻¹])
    (hw : (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)).IsIntegralElem w)
    (n : ℤ) :
    IsIntegral R (w.coeff n) := by
  -- The monomial `C (w n) · T^n` is integral over R[T;T⁻¹] (L3a) ...
  have hmon := single_monomial_isIntegral w hw n
  -- ... hence its coefficient `w n` is integral over R (L3b, T ↦ 1 specialization).
  exact coeff_monomial_isIntegral (w.coeff n) n hmon

open LaurentPolynomial in
/-- If the structure map respects the gradings, the integral closure of `R` in `S` is a
homogeneous subring: every homogeneous component of an integral element is integral. -/
theorem integralClosure_isHomogeneous
    (hφ : RespectsGrading ℛ 𝒮)
    (s : S) (hs : s ∈ integralClosure R S) (d : ℕ) :
    GradedRing.proj 𝒮 d s ∈ integralClosure R S := by
  -- `s ∈ integralClosure R S ↔ IsIntegral R s`.
  rw [mem_integralClosure_iff] at hs ⊢
  -- Take the graded twist ring hom Ψ (L1).
  obtain ⟨Ψ, hΨcoeff, hΨsupp⟩ := exists_gradedTwist 𝒮
  -- Ψ s is integral over R[T;T⁻¹] (L2).
  have hint : (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S)).IsIntegralElem (Ψ s) :=
    gradedTwist_isIntegral ℛ 𝒮 hφ Ψ hΨcoeff hΨsupp s hs
  -- Its degree-d coefficient is integral over R (L3).
  have hcoeff : IsIntegral R ((Ψ s).coeff (d : ℤ)) := coeff_isIntegral (Ψ s) hint (d : ℤ)
  -- And that coefficient is exactly proj_d s.
  rwa [hΨcoeff s d] at hcoeff

-- Equivalent reformulation as the carrier-set characterization of the graded
-- subalgebra: the integral closure `S'` equals the set of elements all of whose
-- homogeneous components are integral, which is the explicit form of the internal
-- direct-sum equality `S' = ⨁_{d ≥ 0} (S' ∩ S_d)`.
/-- If the structure map respects the gradings, an element of `S` is integral over `R` exactly
when all of its homogeneous components are. -/
@[stacks 077G]
theorem integralClosure_carrier_eq
    (hφ : RespectsGrading ℛ 𝒮) :
    (integralClosure R S : Set S)
      = {s : S | ∀ d : ℕ, GradedRing.proj 𝒮 d s ∈ integralClosure R S} := by
  ext s
  simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
  refine ⟨fun hs d => integralClosure_isHomogeneous ℛ 𝒮 hφ s hs d, fun hs => ?_⟩
  -- s is the finite sum of its homogeneous components, each of which is integral
  classical
  have hsum : s = ∑ d ∈ (DirectSum.decompose 𝒮 s).support, GradedRing.proj 𝒮 d s := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒮 s]
    rfl
  rw [hsum]
  exact Subalgebra.sum_mem _ fun d _ => hs d
