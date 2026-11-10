module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityInvertibleKernel
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensorUnconditional
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialEvalDualityProof

/-!
# Upper shriek along a localization at one element

[Stacks, Tag 0C0H] computes the algebraic upper shriek functor of a map `φ : R → R'` in two
clauses: for `R` Noetherian and `f ∈ R` the map `φ : R → R_f` has `φ^!` isomorphic to
`- ⊗_R^L R_f`, and more generally so does any `φ : R → R'` with `Spec(R') → Spec(R)` an open
immersion.  This file proves the first clause, with nothing carried; the general clause is
`Dualizing.nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_isOpenImmersion`, in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatEpimorphism`, where the two are assembled into
the tag, `Dualizing.upperShriekFunctor_iso_derivedTensorProduct_away_and_of_isOpenImmersion`.

The route is the source's own.  Present `R_f` by the polynomial algebra in one variable,
`R → R[x] → R[x]/(fx - 1) = R_f`; the element `fx - 1` is a nonzerodivisor of `R[x]`, so the
kernel of that surjection is an invertible module and [Stacks, Tag 0BZH] computes
`RHom_{R[x]}(R_f, R[x])` as `N[-1]` with `N` the inverse of the conormal module.  The kernel
being free of rank one, `N` is `R_f`, and the shift by the one variable in the definition of
`φ^!` cancels the shift of Tag 0BZH — "note that the shift in the definition of `φ^!` and in the
lemma add up to zero", as the source puts it.  That computes `ω_{R_f/R} = φ^!(R)` as `R_f`, and
[Stacks, Tag 0BZU] then turns it into the statement about the functor: `φ` is flat, so `R_f` is a
perfect module over the polynomial algebra and `φ^!(K) = K ⊗_R^L φ^!(R)` unconditionally.

## Main definitions

* `Dualizing.mvPolynomialFinOneAlgEquivPolynomial` — the identification
  `MvPolynomial (Fin 1) R ≃ₐ[R] R[X]` used to read `fx - 1` in the polynomial algebra of a
  presentation.
* `Dualizing.awayGenerator` — the element `f · x₀ - 1` of `MvPolynomial (Fin 1) R`.
* `Dualizing.awayPresentation` — the polynomial presentation of `R → R_f` in one variable.

## Main results

* `Dualizing.awayGenerator_eq_zero_of_mul_eq_zero` — `f · x₀ - 1` is a nonzerodivisor.
* `Dualizing.ker_awayPresentationHom` — the kernel of the presentation's surjection is the
  principal ideal on `f · x₀ - 1`.
* `Dualizing.PolynomialPresentation.upperShriekUnitIsoOfInvertibleKernel` — for a presentation in
  one variable whose surjection has invertible kernel with conormal inverse the target,
  `φ^!(R) = A`.  This is where Tag 0BZH is read.
* `Dualizing.upperShriekFunctor_unitObject_iso_away` — **`ω_{R_f/R} = R_f`**: for `R_f` a
  localization of `R` away from `f`, the relative dualizing complex `φ^!(R)` is `R_f` in degree
  zero.
* `Dualizing.nonempty_upperShriekFunctor_iso_derivedTensorProduct_away` — **the clause of
  [Stacks, Tag 0C0H] for a localization at one element**: `φ^!` is `- ⊗_R^L R_f`, at an arbitrary
  polynomial presentation of `φ` and an arbitrary module universe, with nothing carried.
* `Dualizing.nonempty_upperShriekFunctor_iso_derivedTensorProduct_localizationAway` — the same
  read at `Localization.Away f`, which is the source's `R_f`.

## Implementation notes

The target is a ring `S` with `IsLocalization.Away f S` rather than `Localization.Away f`
itself, which is the more general reading and the one Mathlib states localization results in;
the named corollary at `Localization.Away f` is immediate from it.

`- ⊗_R^L R_f` is written `Dualizing.derivedTensorProductOver (algebraMap R S) R'₀` with `R'₀` the
free module of rank one in degree zero, which is the shape in which the library's
[Stacks, Tag 0BZU] and [Stacks, Tag 0E4B] state `φ^!(K) = K ⊗_R^L ω`.  It is not the shape
`Dualizing.upperShriekFunctor_iso_derivedExtensionScalars_of_bijective` uses for the case of a
bijective `φ`, which is a total left derived functor of extension of scalars; the two are models
of the same functor but the library has no comparison between them, so neither statement
subsumes the other.

Everything is stated at an arbitrary module universe: the computation of `RHom` for an
invertible kernel ([Stacks, Tag 0BZH]), Tag 0BZU and Tag 0BZJ all hold there.  The statement is at
an arbitrary polynomial presentation, [Stacks, Tag 0BZJ] being unconditional
(`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso`); the proof works at the
one-variable presentation built here.

The Noetherian hypothesis of the source is not needed and is omitted: finite presentation of
`R → R_f` is the only finiteness the argument uses.

## References

* [Stacks Project, Tag 0C0H](https://stacks.math.columbia.edu/tag/0C0H)
* [Stacks Project, Tag 0BZH](https://stacks.math.columbia.edu/tag/0BZH)
* [Stacks Project, Tag 0BZU](https://stacks.math.columbia.edu/tag/0BZU)
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial

attribute [local instance 10000] HasDerivedCategory.standard

universe u v

namespace Dualizing

variable {R S : Type u} [CommRing R] [CommRing S]

/-! ### The presentation `R → R[x] → R_f` -/

/-- The polynomial algebra in one variable indexed by `Fin 1`, identified with `R[X]`. -/
def mvPolynomialFinOneAlgEquivPolynomial (R : Type u) [CommRing R] :
    MvPolynomial (Fin 1) R ≃ₐ[R] Polynomial R :=
  (MvPolynomial.renameEquiv R (Equiv.equivPUnit (Fin 1) : Fin 1 ≃ PUnit.{1})).trans
    (MvPolynomial.uniqueAlgEquiv R PUnit.{1})

/-- The element `f · x₀ - 1` of the polynomial algebra in one variable: the generator of the
kernel of the presentation of `R_f`. -/
def awayGenerator (f : R) : MvPolynomial (Fin 1) R :=
  MvPolynomial.C f * MvPolynomial.X 0 - 1

/-- The identification `MvPolynomial (Fin 1) R ≃ₐ[R] R[X]` sends the constant `C r` to `C r`. -/
theorem mvPolynomialFinOneAlgEquivPolynomial_C (r : R) :
    mvPolynomialFinOneAlgEquivPolynomial R (MvPolynomial.C r) = Polynomial.C r := by
  simp [mvPolynomialFinOneAlgEquivPolynomial]

/-- The identification `MvPolynomial (Fin 1) R ≃ₐ[R] R[X]` sends `f · x₀ - 1` to `f X - 1`. -/
theorem mvPolynomialFinOneAlgEquivPolynomial_awayGenerator (f : R) :
    mvPolynomialFinOneAlgEquivPolynomial R (awayGenerator f) = C f * X - 1 := by
  have hX : mvPolynomialFinOneAlgEquivPolynomial R (MvPolynomial.X 0) = X := by
    simp [mvPolynomialFinOneAlgEquivPolynomial]
  rw [awayGenerator, map_sub, map_mul, map_one, mvPolynomialFinOneAlgEquivPolynomial_C, hX]

/-- **`f · x₀ - 1` is a nonzerodivisor.**  If `q · (fx - 1) = 0` then the coefficients of `q`
satisfy `q_0 = 0` and `q_{n+1} = f q_n`, so all of them vanish. -/
theorem awayGenerator_eq_zero_of_mul_eq_zero (f : R) (r : MvPolynomial (Fin 1) R)
    (h : r * awayGenerator f = 0) : r = 0 := by
  set e := mvPolynomialFinOneAlgEquivPolynomial R with he
  have h1 : e r * (C f * X - 1) = 0 := by
    rw [he, ← mvPolynomialFinOneAlgEquivPolynomial_awayGenerator, ← map_mul, h, map_zero]
  have h2 : e r = 0 := by
    rw [mul_sub, mul_one, sub_eq_zero] at h1
    have h3 : C f * (e r * X) = e r := by linear_combination h1
    have hq : ∀ n, (e r).coeff n = 0 := by
      intro n
      induction n with
      | zero =>
        rw [← h3]
        simp
      | succ m ih =>
        rw [← h3]
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_mul_X, ih]
    exact Polynomial.ext fun n => by simp [hq n]
  simpa using e.injective (by rw [h2, map_zero])

variable [Algebra R S]

/-- `R[x]/(fx - 1)` is a localization of `R` away from `f`, so it is identified with any other
one; this is [Stacks, Tag 00I2] in the form Mathlib's `IsLocalization.adjoin_inv` gives it. -/
def adjoinRootAlgEquivAway (f : R) [IsLocalization.Away f S] :
    AdjoinRoot (C f * X - 1 : Polynomial R) ≃ₐ[R] S :=
  letI : IsLocalization.Away f (AdjoinRoot (C f * X - 1 : Polynomial R)) :=
    IsLocalization.adjoin_inv f
  IsLocalization.algEquiv (Submonoid.powers f) _ S

/-- The surjection `MvPolynomial (Fin 1) R → R_f` of the presentation: evaluate the variable at
the inverse of `f`. -/
def awayPresentationHom (f : R) [IsLocalization.Away f S] : MvPolynomial (Fin 1) R →+* S :=
  ((adjoinRootAlgEquivAway f (S := S)).toRingHom.comp
    (AdjoinRoot.mk (C f * X - 1 : Polynomial R))).comp
      (mvPolynomialFinOneAlgEquivPolynomial R).toRingHom

/-- The map `MvPolynomial (Fin 1) R → S` of the presentation of `R_f` is surjective. -/
theorem awayPresentationHom_surjective (f : R) [IsLocalization.Away f S] :
    Function.Surjective (awayPresentationHom f (S := S)) :=
  ((adjoinRootAlgEquivAway f (S := S)).surjective.comp Ideal.Quotient.mk_surjective).comp
    (mvPolynomialFinOneAlgEquivPolynomial R).surjective

/-- The map of the presentation of `R_f` factors through the identification with `R[X]` and
`R[X]/(fx - 1)`. -/
private theorem awayPresentationHom_apply (f : R) [IsLocalization.Away f S]
    (x : MvPolynomial (Fin 1) R) :
    awayPresentationHom f (S := S) x = adjoinRootAlgEquivAway f (S := S)
      (AdjoinRoot.mk _ (mvPolynomialFinOneAlgEquivPolynomial R x)) := rfl

/-- The map of the presentation of `R_f`, restricted to the constants, is `algebraMap R S`. -/
theorem awayPresentationHom_comp_C (f : R) [IsLocalization.Away f S] :
    (awayPresentationHom f (S := S)).comp MvPolynomial.C = algebraMap R S := by
  refine RingHom.ext fun r => ?_
  have h2 : (AdjoinRoot.mk (C f * X - 1 : Polynomial R)) (Polynomial.C r)
      = algebraMap R (AdjoinRoot (C f * X - 1 : Polynomial R)) r :=
    (RingHom.congr_fun (AdjoinRoot.algebraMap_eq (C f * X - 1 : Polynomial R)) r).symm
  rw [RingHom.comp_apply, awayPresentationHom_apply, mvPolynomialFinOneAlgEquivPolynomial_C, h2]
  exact (adjoinRootAlgEquivAway f (S := S)).commutes r

/-- **The kernel of the presentation is the principal ideal on `f · x₀ - 1`.** -/
theorem ker_awayPresentationHom (f : R) [IsLocalization.Away f S] :
    RingHom.ker (awayPresentationHom f (S := S)) = Ideal.span {awayGenerator f} := by
  set e := mvPolynomialFinOneAlgEquivPolynomial R with he
  have hg : e (awayGenerator f) = C f * X - 1 :=
    mvPolynomialFinOneAlgEquivPolynomial_awayGenerator f
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton', awayPresentationHom_apply,
    map_eq_zero_iff _ (adjoinRootAlgEquivAway f (S := S)).injective, AdjoinRoot.mk_eq_zero]
  refine ⟨fun ⟨c, hc⟩ => ⟨e.symm c, e.injective ?_⟩, fun ⟨c, hc⟩ => ⟨e c, ?_⟩⟩
  · rw [map_mul, hg, e.apply_symm_apply, hc]
    ring
  · rw [← hc, map_mul, hg]
    ring

/-- **The presentation of `R → R_f` in one variable**, `R → R[x] → R[x]/(fx - 1) = R_f`. -/
def awayPresentation (f : R) [IsLocalization.Away f S] :
    PolynomialPresentation (algebraMap R S) where
  variableCount := 1
  toRingHom := awayPresentationHom f
  commutes := awayPresentationHom_comp_C f
  surjective := awayPresentationHom_surjective f

/-! ### The hypotheses of Stacks 0BZH at that presentation -/

namespace AwayPresentation

open Dualizing.InvertibleKernel

/-- The algebra structure on `R_f` over the polynomial algebra of the presentation. -/
abbrev algebra (f : R) [IsLocalization.Away f S] : Algebra (MvPolynomial (Fin 1) R) S :=
  (awayPresentationHom f (S := S)).toAlgebra

/-- For the algebra structure `AwayPresentation.algebra`, the map
`MvPolynomial (Fin 1) R → S` is surjective. -/
theorem surjective_algebraMap (f : R) [IsLocalization.Away f S] :
    letI := algebra f (S := S)
    Function.Surjective (algebraMap (MvPolynomial (Fin 1) R) S) :=
  awayPresentationHom_surjective f

/-- **The kernel of the presentation is an invertible module**, being principal on a
nonzerodivisor.  This is the hypothesis of [Stacks, Tag 0BZH]. -/
theorem invertible_ker (f : R) [IsLocalization.Away f S] :
    letI := algebra f (S := S)
    Module.Invertible (MvPolynomial (Fin 1) R)
      (RingHom.ker (algebraMap (MvPolynomial (Fin 1) R) S)) := by
  let := algebra f (S := S)
  have hker : RingHom.ker (algebraMap (MvPolynomial (Fin 1) R) S)
      = Ideal.span {awayGenerator f} := ker_awayPresentationHom f
  let := invertible_span_singleton (awayGenerator f) (awayGenerator_eq_zero_of_mul_eq_zero f)
  exact Module.Invertible.congr (LinearEquiv.ofEq _ _ hker.symm)

/-- **The conormal inverse of the presentation is `R_f` itself.**  The kernel is free of rank one
on `f · x₀ - 1`, so the conormal module `I ⊗_{R[x]} R_f` is free of rank one over `R_f` and so is
its inverse `N = Hom_{R_f}(I ⊗_{R[x]} R_f, R_f)`. -/
def conormalInverseLinearEquiv (f : R) [IsLocalization.Away f S] :
    letI := algebra f (S := S)
    conormalInverse.{u, v} (MvPolynomial (Fin 1) R) S ≃ₗ[S] ULift.{max v u} S := by
  letI := algebra f (S := S)
  have hker : RingHom.ker (algebraMap (MvPolynomial (Fin 1) R) S)
      = Ideal.span {awayGenerator f} := ker_awayPresentationHom f
  let eKer : kernelModule.{u, v} (MvPolynomial (Fin 1) R) S ≃ₗ[MvPolynomial (Fin 1) R]
      MvPolynomial (Fin 1) R :=
    ULift.moduleEquiv.trans ((LinearEquiv.ofEq _ _ hker).trans
      (spanSingletonEquiv (awayGenerator f)
        (awayGenerator_eq_zero_of_mul_eq_zero f)).symm)
  let eCon : conormal.{u, v} (MvPolynomial (Fin 1) R) S ≃ₗ[S] S :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) eKer).trans
      (TensorProduct.AlgebraTensorModule.rid (MvPolynomial (Fin 1) R) S S)
  exact (eCon.symm.dualMap.trans (LinearMap.ringLmapEquivSelf S S S)).trans
    ULift.moduleEquiv.symm

end AwayPresentation

/-! ### `ω_{R_f/R} = R_f` -/

/-- Extension of scalars along `φ : R →+* P` carries the free module of rank one to the free
module of rank one. -/
def extendScalarsULiftIso {R P : Type u} [CommRing R] [CommRing P] (φ : R →+* P) :
    (ModuleCat.extendScalars.{u, u, max v u} φ).obj (ModuleCat.of R (ULift.{max v u} R)) ≅
      ModuleCat.of P (ULift.{max v u} P) := by
  letI := φ.toAlgebra
  exact ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl P P)
      (ULift.moduleEquiv : ULift.{max v u} R ≃ₗ[R] R)).trans
    ((TensorProduct.AlgebraTensorModule.rid R P P).trans
      (ULift.moduleEquiv : ULift.{max v u} P ≃ₗ[P] P).symm)).toModuleIso

namespace PolynomialPresentation

/-- **Derived base change along the polynomial algebra of a presentation carries `R` to `P`**,
read at the free module of rank one: the identification `R ⊗_R^L P = P` in degree zero.  This is
where `φ^!(R) = RHom_P(A, R ⊗_R^L P)[n]` becomes `RHom_P(A, P)[n]`. -/
def derivedExtensionUnitObjectIso {R A : Type u} [CommRing R] [CommRing A] {g : R →+* A}
    (p : PolynomialPresentation g) :
    p.derivedExtension.{u, v}.obj (Stacks0BZE.unitObject.{u, v} R) ≅
      Stacks0BZE.unitObject.{u, v} p.Poly := by
  let F := ModuleCat.extendScalars.{u, u, max v u} (MvPolynomial.C : R →+* p.Poly)
  letI : Limits.PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _ p.flat_C
  change F.mapDerivedCategory.obj _ ≅ _
  exact (F.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of R (ULift.{max v u} R)) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{max v u} p.Poly) 0).mapIso
      (extendScalarsULiftIso (MvPolynomial.C : R →+* p.Poly))

/-- **`φ^!(R) = A` from [Stacks, Tag 0BZH].**  Let `p` be a polynomial presentation of
`g : R →+* A` in one variable whose surjection `P → A` has invertible kernel and whose conormal
inverse is `A` itself.  Then the relative dualizing complex `φ^!(R)` of `p` is `A` in degree
zero.

The three steps are `R ⊗_R^L P = P`, then Tag 0BZH in the shape
`Dualizing.InvertibleKernel.derivedHomUnitObjectIsoSingle`, which puts `RHom_P(A, P)` in degree
one, and then the shift by the one variable, which brings it back to degree zero. -/
def upperShriekUnitIsoOfInvertibleKernel {R A : Type u} [CommRing R] [CommRing A] {g : R →+* A}
    (p : PolynomialPresentation g) (hvar : ((p.variableCount : ℕ) : ℤ) = 1)
    (hsurj : letI := p.toRingHom.toAlgebra
      Function.Surjective (algebraMap p.Poly A))
    (hinv : letI := p.toRingHom.toAlgebra
      Module.Invertible p.Poly (RingHom.ker (algebraMap p.Poly A)))
    (e : letI := p.toRingHom.toAlgebra
      InvertibleKernel.conormalInverse.{u, v} p.Poly A ≃ₗ[A] ULift.{max v u} A) :
    p.upperShriekFunctor.{u, v}.obj (Stacks0BZE.unitObject.{u, v} R) ≅
      Stacks0BZE.unitObject.{u, v} A := by
  letI := p.toRingHom.toAlgebra
  let M := ModuleCat.of A (InvertibleKernel.conormalInverse.{u, v} p.Poly A)
  have e2 : (derivedHom.{u, v} p.toRingHom).obj (Stacks0BZE.unitObject.{u, v} p.Poly) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 1).obj M :=
    InvertibleKernel.derivedHomUnitObjectIsoSingle.{u, v} hsurj hinv
  refine (shiftFunctor (DerivedCategory (ModuleCat.{max v u} A)) ((p.variableCount : ℕ) : ℤ)).mapIso
      ((derivedHom.{u, v} p.toRingHom).mapIso p.derivedExtensionUnitObjectIso ≪≫ e2) ≪≫ ?_
  refine ((DerivedCategory.singleFunctors (ModuleCat.{max v u} A)).shiftIso
      (((p.variableCount : ℕ) : ℤ)) 0 1 (by simp [hvar])).app M ≪≫ ?_
  exact (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).mapIso e.toModuleIso

end PolynomialPresentation

/-- **`ω_{R_f/R} = R_f`.**  For `S` a localization of `R` away from `f`, the relative dualizing
complex `φ^!(R)` of the one-variable presentation of `φ : R → S` is `S` in degree zero. -/
def upperShriekFunctor_unitObject_iso_away (f : R) [IsLocalization.Away f S] :
    (awayPresentation f (S := S)).upperShriekFunctor.{u, v}.obj
        (Stacks0BZE.unitObject.{u, v} R) ≅ Stacks0BZE.unitObject.{u, v} S :=
  PolynomialPresentation.upperShriekUnitIsoOfInvertibleKernel (awayPresentation f (S := S))
    (by norm_num [awayPresentation]) (AwayPresentation.surjective_algebraMap f)
    (AwayPresentation.invertible_ker f) (AwayPresentation.conormalInverseLinearEquiv f)

/-- Derived tensor product over `R` with an object of `D(A)` depends on that object only up to
isomorphism; this is [Stacks, Tag 0BYK] in the form
`Dualizing.InvertibleKernel.derivedTensorIsoOfDerivedIso` gives it. -/
def derivedTensorProductOverIsoCongr {R A : Type u} [CommRing R] [CommRing A] (g : R →+* A)
    {L N : DerivedCategory (ModuleCat.{max v u} A)} (e : L ≅ N) :
    derivedTensorProductOver.{u, v} g L ≅ derivedTensorProductOver.{u, v} g N := by
  let Qh := DerivedCategory.Qh (C := ModuleCat.{max v u} A)
  let Lc := (Qh.objPreimage L).as
  let Nc := (Qh.objPreimage N).as
  let eL : DerivedCategory.Q.obj Lc ≅ L :=
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).app Lc).symm ≪≫
      Qh.objObjPreimageIso L
  let eN : DerivedCategory.Q.obj Nc ≅ N :=
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{max v u} A)).app Nc).symm ≪≫
      Qh.objObjPreimageIso N
  exact InvertibleKernel.derivedTensorIsoOfDerivedIso g (eL ≪≫ e ≪≫ eN.symm)
    (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, v} g Lc)
    (CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, v} g Nc)

/-- **The first clause of [Stacks, Tag 0C0H], a localization at one element.**  The tag as a whole
is `Dualizing.upperShriekFunctor_iso_derivedTensorProduct_away_and_of_isOpenImmersion`.  Let `R`
be a commutative ring, let `f ∈ R` and let `S` be a localization of `R` away from `f`.  Then the
algebraic upper shriek
functor of `φ : R → S`, read at any polynomial presentation of `φ`, is derived base change
`- ⊗_R^L S`.

Nothing is carried and nothing is assumed of `R`.  `φ^!(K) = K ⊗_R^L φ^!(R)` is
[Stacks, Tag 0BZU], unconditional here because `φ` is flat of finite presentation, so `S` is a
perfect module over the polynomial algebra of the presentation; and
`φ^!(R) = S` is `Dualizing.upperShriekFunctor_unitObject_iso_away`, which is [Stacks, Tag 0BZH]
at the surjection `R[x] → R[x]/(fx - 1)`.  The passage from the one-variable presentation to an
arbitrary one is [Stacks, Tag 0BZJ], also unconditional.

The source states the clause for a Noetherian `R`; no Noetherian hypothesis is needed, finite
presentation of `R → R_f` being the only finiteness the argument uses. -/
theorem nonempty_upperShriekFunctor_iso_derivedTensorProduct_away
    (f : R) [IsLocalization.Away f S]
    (p : PolynomialPresentation (algebraMap R S)) :
    Nonempty (p.upperShriekFunctor.{u, v} ≅
      derivedTensorProductOver.{u, v} (algebraMap R S) (Stacks0BZE.unitObject.{u, v} S)) := by
  have hflat : (algebraMap R S).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S (Submonoid.powers f))
  have hfp : (algebraMap R S).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr (IsLocalization.Away.finitePresentation f)
  obtain ⟨e0⟩ := PolynomialPresentation.nonempty_upperShriekFunctor_iso.{u, v}
    (algebraMap R S) p (awayPresentation f (S := S))
  obtain ⟨e1⟩ := (awayPresentation f (S := S)).upperShriekFunctor_iso_derivedTensorProduct.{u, v}
    ((awayPresentation f (S := S)).isPerfectModule_of_flat_of_finitePresentation hflat hfp)
  exact ⟨e0 ≪≫ e1 ≪≫
    derivedTensorProductOverIsoCongr _ (upperShriekFunctor_unitObject_iso_away f)⟩

/-- **[Stacks, Tag 0C0H] for a localization at one element**, read at `Localization.Away f`,
which is the source's `R_f`. -/
theorem nonempty_upperShriekFunctor_iso_derivedTensorProduct_localizationAway
    {R : Type u} [CommRing R] (f : R)
    (p : PolynomialPresentation (algebraMap R (Localization.Away f))) :
    Nonempty (p.upperShriekFunctor.{u, v} ≅
      derivedTensorProductOver.{u, v} (algebraMap R (Localization.Away f))
        (Stacks0BZE.unitObject.{u, v} (Localization.Away f))) :=
  nonempty_upperShriekFunctor_iso_derivedTensorProduct_away f p

end Dualizing

end
