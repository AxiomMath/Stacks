module

public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.CurvesFunctionFields.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.FlatMorphism
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFactorizationChain
public import StacksFrontier.AlgebraicGeometry.Curves.ModelGlobalSections
public import StacksFrontier.AlgebraicGeometry.Curves.PinchedProjectiveLine.CoordinateRing
public import StacksFrontier.AlgebraicGeometry.Curves.RationalMapExtension
public import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModel
public import StacksFrontier.AlgebraicGeometry.Curves.SmoothModelOverPerfectField
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.Extension
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.FormallySmooth.Retract
public import StacksFrontier.RingTheory.NodalChart.Regularity

/-!
# The nonsingular projective model is unique up to unique isomorphism

Section 0BXX of the Stacks project ([Stacks, Tag 0BXX]) observes, right after Definition 0BY2
(`AlgebraicGeometry.NonsingularProjectiveModel`), that a nonsingular projective model `(Y, φ)` of
a curve `X` over a field `k` is determined up to unique isomorphism by Theorem 0BY1: for two models
`(Y₁, φ₁)` and `(Y₂, φ₂)` there is exactly one isomorphism `Y₁ ≅ Y₂` over `k` whose map of function
fields `k(Y₂) ⟶ k(Y₁)` carries `φ₂` to `φ₁`.

## Main results

* `AlgebraicGeometry.NonsingularProjectiveModel.existsUnique_iso` — the uniqueness statement.
* `AlgebraicGeometry.exists_forall_not_smooth_nonsingularProjectiveModel` — a curve none of whose
  nonsingular projective models is smooth over the base field.

The file also registers for the section its main theorem, Theorem 0BY1, Definition 0BY2, its
Lemmas 0BXY, 0BXZ, 0CCK, 0CCL and 0BY4 (3), Lemma 0BY3 for the second half of the warning
following that definition, and proves the first half of that warning: the nonsingular projective
model need not be smooth over `k`
(`AlgebraicGeometry.exists_forall_not_smooth_nonsingularProjectiveModel`). The example is the
regular projective compactification, over `k = 𝔽₂(t)`, of the affine line over `𝔽₂(√t)`; it
contains that affine line as an open subscheme, which is not smooth over `k` because
`𝔽₂(√t)[x]` is not formally smooth over `𝔽₂(t)`: `𝔽₂(√t)` is a retract of it, and a formally
smooth field extension is separable (Stacks 031Y).

## Implementation notes

A nonsingular projective curve is normal (`AlgebraicGeometry.isNormal_of_isRegular`) and proper
(`AlgebraicGeometry.isProper_of_isProjectiveMorphism`), so the part of Theorem 0BY1 that is used is
the correspondence between morphisms over `k` of normal proper curves and `k`-algebra maps of
their function fields: `AlgebraicGeometry.exists_isIso_of_algEquiv` produces the isomorphism and
`AlgebraicGeometry.over_hom_ext_of_functionFieldMap` gives its uniqueness. Those are stated for
the `k`-algebra structure of the function field of a `AlgebraicGeometry.Variety`, which agrees
with the one of `AlgebraicGeometry.functionFieldAlgebra` used by the model
(`AlgebraicGeometry.functionFieldAlgebraMap_eq_germToFunctionField`).

## References

* [Stacks Project, Section 0BXX](https://stacks.math.columbia.edu/tag/0BXX)
* [Stacks Project, Tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1)
* [Stacks Project, Tag 0BY2](https://stacks.math.columbia.edu/tag/0BY2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsCurve k sX]

/-- The comparison of function fields of a nonsingular projective model, as a ring isomorphism. -/
def NonsingularProjectiveModel.functionFieldRingEquiv (M : NonsingularProjectiveModel k X sX) :
    letI : IsCurve k M.structureMap := M.isCurve
    X.functionField ≃+* M.Y.functionField :=
  let _ : IsCurve k M.structureMap := M.isCurve
  let _ : Algebra k X.functionField := functionFieldAlgebra k sX
  let _ : Algebra k M.Y.functionField := functionFieldAlgebra k M.structureMap
  M.functionFieldEquiv.toRingEquiv

/-- The ring isomorphism `functionFieldRingEquiv` agrees pointwise with `functionFieldEquiv`. -/
theorem NonsingularProjectiveModel.functionFieldRingEquiv_apply
    (M : NonsingularProjectiveModel k X sX) (a : X.functionField) :
    letI : IsCurve k M.structureMap := M.isCurve
    M.functionFieldRingEquiv a = M.functionFieldEquiv a :=
  rfl

/-- The comparison of function fields of a nonsingular projective model fixes the constants. -/
theorem NonsingularProjectiveModel.functionFieldRingEquiv_germ
    (M : NonsingularProjectiveModel k X sX) (a : k) :
    letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
    letI : IsCurve k M.structureMap := M.isCurve
    letI : Nonempty (⊤ : M.Y.Opens) := ⟨⟨genericPoint M.Y, trivial⟩⟩
    M.functionFieldRingEquiv
        (((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.germToFunctionField ⊤).hom a) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ M.structureMap.appTop ≫
        M.Y.germToFunctionField ⊤).hom a :=
  M.functionFieldEquiv_algebraMap a

add_to_stacks 0BXX "Lemma 0BXY of the section: a morphism from a nonempty open of a curve to a \
  proper variety extends across a closed point whose local ring is a discrete valuation ring"
  AlgebraicGeometry.exists_open_extension_of_valuationRing_stalk

add_to_stacks 0BXX "Lemma 0BXZ of the section: rational maps from a normal curve to a proper \
  variety are morphisms" AlgebraicGeometry.toRationalMap_bijective

add_to_stacks 0BXX "Lemma 0CCK of the section: a nonconstant morphism of curves with normal \
  target is flat" AlgebraicGeometry.isFlat_of_nonconstant_of_isNormal

add_to_stacks 0BXX "Lemma 0CCL of the section: a morphism from a proper scheme of dimension at \
  most one which is nonconstant on every one-dimensional component is finite"
  AlgebraicGeometry.isFinite_of_isProper_dimension_le_one_of_nontrivial_image_components

add_to_stacks 0BXX "Lemma 0BY4 of the section, part (3): a smooth nonsingular projective model \
  of a reduced base change has the base field as global regular functions"
  AlgebraicGeometry.isIso_globalSections_of_smooth_model_reducedBaseChange

add_to_stacks 0BXX "the main theorem of the section, Theorem 0BY1: the category of curves and \
  dominant rational maps is anti-equivalent to that of finitely generated field extensions of \
  transcendence degree one"
  AlgebraicGeometry.curveEquivalenceFinitelyGeneratedFieldExtensionTrdegOneOpposite

add_to_stacks 0BXX "the main theorem of the section, Theorem 0BY1: normal projective curves and \
  nonconstant morphisms are equivalent to curves and dominant rational maps"
  AlgebraicGeometry.normalProjectiveCurveEquivalenceCurve

add_to_stacks 0BXX "Definition 0BY2 of the section: a nonsingular projective model of a curve"
  AlgebraicGeometry.NonsingularProjectiveModel

add_to_stacks 0BXX "the warning after Definition 0BY2, its second half: a nonsingular projective \
  model fails to be smooth only over an imperfect field, hence only in positive characteristic \
  (Lemma 0BY3)" AlgebraicGeometry.NonsingularProjectiveModel.isSmoothProjectiveCurve

/-- **The nonsingular projective model is unique up to unique isomorphism** (Section 0BXX). For two
nonsingular projective models `(Y₁, φ₁)` and `(Y₂, φ₂)` of a curve `X` over `k`, there is exactly
one isomorphism `e : Y₁ ≅ Y₂` over `k` whose map of function fields `k(Y₂) ⟶ k(Y₁)` carries
`φ₂` to `φ₁`. -/
@[stacks 0BXX "a nonsingular projective model is determined up to unique isomorphism, by \
Theorem 0BY1"]
theorem NonsingularProjectiveModel.existsUnique_iso (M₁ M₂ : NonsingularProjectiveModel k X sX) :
    letI : IsCurve k M₁.structureMap := M₁.isCurve
    letI : IsCurve k M₂.structureMap := M₂.isCurve
    ∃! e : M₁.Y ≅ M₂.Y, e.hom ≫ M₂.structureMap = M₁.structureMap ∧
      ∀ a : X.functionField,
        functionFieldMap e.hom (M₂.functionFieldRingEquiv a) = M₁.functionFieldRingEquiv a := by
  let _ : IsCurve k M₁.structureMap := M₁.isCurve
  let _ : IsCurve k M₂.structureMap := M₂.isCurve
  let V₁ : Variety k := ⟨M₁.Y, M₁.structureMap⟩
  let V₂ : Variety k := ⟨M₂.Y, M₂.structureMap⟩
  have : IsCurve k V₁.structureMap := M₁.isCurve
  have : IsCurve k V₂.structureMap := M₂.isCurve
  have : IsNormal V₁.toScheme := isNormal_of_isRegular _ M₁.isRegular
  have : IsNormal V₂.toScheme := isNormal_of_isRegular _ M₂.isRegular
  have : IsProper V₁.structureMap :=
    isProper_of_isProjectiveMorphism _ M₁.isProjectiveVariety.isProjective
  have : IsProper V₂.structureMap :=
    isProper_of_isProjectiveMorphism _ M₂.isProjectiveVariety.isProjective
  let : Algebra k V₁.toScheme.functionField := varietyFunctionFieldAlgebra V₁
  let : Algebra k V₂.toScheme.functionField := varietyFunctionFieldAlgebra V₂
  let ρ : M₂.Y.functionField ≃+* M₁.Y.functionField :=
    M₂.functionFieldRingEquiv.symm.trans M₁.functionFieldRingEquiv
  have hρ : ∀ b, ρ (M₂.functionFieldRingEquiv b) = M₁.functionFieldRingEquiv b := fun b => by
    simp [ρ]
  have hcomm : ∀ a : k, ρ (algebraMap k V₂.toScheme.functionField a) =
      algebraMap k V₁.toScheme.functionField a := by
    intro a
    show ρ (functionFieldAlgebraMap V₂ a) = functionFieldAlgebraMap V₁ a
    rw [DFunLike.congr_fun (functionFieldAlgebraMap_eq_germToFunctionField V₁) a,
      DFunLike.congr_fun (functionFieldAlgebraMap_eq_germToFunctionField V₂) a,
      ← M₂.functionFieldRingEquiv_germ a, hρ, M₁.functionFieldRingEquiv_germ a]
  obtain ⟨g, hg, hdom, hgφ⟩ :=
    exists_isIso_of_algEquiv V₁ V₂ (AlgEquiv.ofRingEquiv (f := ρ) hcomm)
  have : IsIso g := hg
  have : IsIso g.left := inferInstanceAs (IsIso ((Over.forget _).map g))
  have hfun : ∀ a : X.functionField,
      functionFieldMap g.left (M₂.functionFieldRingEquiv a) = M₁.functionFieldRingEquiv a :=
    fun a => (DFunLike.congr_fun hgφ _).trans (hρ a)
  refine ⟨asIso g.left, ⟨Over.w g, hfun⟩, ?_⟩
  rintro e ⟨he, hefun⟩
  apply Iso.ext
  let g' : Over.mk V₁.structureMap ⟶ Over.mk V₂.structureMap := Over.homMk e.hom he
  have : IsDominant g'.left := inferInstanceAs (IsDominant e.hom)
  have hgg' : g' = g := by
    refine over_hom_ext_of_functionFieldMap V₁ V₂ g' g ?_
    ext b
    obtain ⟨a, rfl⟩ := M₂.functionFieldRingEquiv.surjective b
    exact (hefun a).trans (hfun a).symm
  exact congrArg CommaMorphism.left hgg'

/-! ### The warning: a nonsingular projective model need not be smooth -/

section NotSmooth

/-- The field `𝔽₂(t)` of rational functions over `𝔽₂`, in universe `u`: an imperfect field. -/
abbrev imperfectRatFunc : Type u := RatFunc (ULift.{u} (ZMod 2))

/-- `2 = 0` in `𝔽₂(t)`. -/
theorem two_eq_zero_imperfectRatFunc : (2 : imperfectRatFunc.{u}) = 0 := by
  have h : (2 : ULift.{u} (ZMod 2)) = 0 := ULift.ext (by decide)
  have := congrArg (algebraMap (ULift.{u} (ZMod 2)) imperfectRatFunc.{u}) h
  rwa [map_ofNat, map_zero] at this

/-- The variable `t` is not a square in `𝔽₂(t)`: a square has even degree, `t` has degree one. -/
theorem sq_ne_X_imperfectRatFunc (b : imperfectRatFunc.{u}) : b ^ 2 ≠ RatFunc.X := by
  intro hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact RatFunc.X_ne_zero (by simpa using hb.symm)
  have h := congrArg RatFunc.intDegree hb
  rw [pow_two, RatFunc.intDegree_mul hb0 hb0, RatFunc.intDegree_X] at h
  omega

/-- The polynomial `T² - t` over `𝔽₂(t)`. -/
abbrev sqrtPolynomial : Polynomial imperfectRatFunc.{u} := Polynomial.X ^ 2 - Polynomial.C RatFunc.X

/-- The polynomial `T² - t` is irreducible over `𝔽₂(t)`. -/
theorem irreducible_sqrtPolynomial : Irreducible sqrtPolynomial.{u} :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two sq_ne_X_imperfectRatFunc

/-- The irreducibility of `T² - t` over `𝔽₂(t)`, as a `Fact`. -/
instance fact_irreducible_sqrtPolynomial : Fact (Irreducible sqrtPolynomial.{u}) :=
  ⟨irreducible_sqrtPolynomial⟩

/-- The purely inseparable quadratic extension `𝔽₂(√t)` of `𝔽₂(t)`. -/
abbrev sqrtExtension : Type u := AdjoinRoot sqrtPolynomial.{u}

/-- `𝔽₂(√t)` is a finite extension of `𝔽₂(t)`. -/
instance finite_sqrtExtension : Module.Finite imperfectRatFunc.{u} sqrtExtension.{u} :=
  (AdjoinRoot.powerBasis irreducible_sqrtPolynomial.ne_zero).finite

/-- `𝔽₂(√t)` is not separable over `𝔽₂(t)`: the minimal polynomial `T² - t` of `√t` has
derivative `2T = 0`. -/
theorem not_isSeparable_sqrtExtension :
    ¬ Algebra.IsSeparable imperfectRatFunc.{u} sqrtExtension.{u} := by
  intro h
  have hsep := h.isSeparable' (AdjoinRoot.root sqrtPolynomial.{u})
  have hmonic : sqrtPolynomial.{u}.Monic := Polynomial.monic_X_pow_sub_C _ two_ne_zero
  rw [IsSeparable, AdjoinRoot.minpoly_root irreducible_sqrtPolynomial.ne_zero, hmonic.leadingCoeff,
    inv_one, Polynomial.C_1, mul_one,
    Polynomial.separable_iff_derivative_ne_zero irreducible_sqrtPolynomial] at hsep
  apply hsep
  rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero, Polynomial.derivative_X_pow]
  simp [two_eq_zero_imperfectRatFunc]

/-- The polynomial ring `𝔽₂(√t)[x]` is not formally smooth over `𝔽₂(t)`: `𝔽₂(√t)` is a retract
of it (by the constants and evaluation at `0`), so it would be formally smooth, hence separable
(Stacks 031Y) and, being algebraic, separable algebraic. -/
theorem not_formallySmooth_polynomial_sqrtExtension :
    ¬ Algebra.FormallySmooth imperfectRatFunc.{u} (Polynomial sqrtExtension.{u}) := by
  intro h
  have : Algebra.FormallySmooth imperfectRatFunc.{u} sqrtExtension.{u} :=
    Algebra.FormallySmooth.of_retract (B := Polynomial sqrtExtension.{u})
      ((Algebra.ofId sqrtExtension.{u} (Polynomial sqrtExtension.{u})).restrictScalars
        imperfectRatFunc.{u})
      ((Polynomial.aeval (R := sqrtExtension.{u}) (0 : sqrtExtension.{u})).restrictScalars
        imperfectRatFunc.{u})
      (AlgHom.ext fun x ↦ by simp)
  have : Algebra.IsSeparableExtension imperfectRatFunc.{u} sqrtExtension.{u} :=
    (Algebra.FormallySmooth.iff_isSeparableExtension _ _).1 this
  have : Algebra.IsAlgebraic imperfectRatFunc.{u} sqrtExtension.{u} :=
    Algebra.IsIntegral.isAlgebraic
  exact not_isSeparable_sqrtExtension
    (Stacks.AlgebraicGeometry.ProperSectionsGeom.isSeparable_of_isSeparableExtension_of_isAlgebraic
      _ _)

/-- The affine line over `𝔽₂(√t)`, as a scheme over `𝔽₂(t)`. -/
abbrev sqrtAffineLine : Scheme.{u} := Spec (.of (Polynomial sqrtExtension.{u}))

/-- The structure morphism of the affine line over `𝔽₂(√t)` to `Spec 𝔽₂(t)`. -/
abbrev sqrtAffineLineStructureMap : sqrtAffineLine.{u} ⟶ Spec (.of imperfectRatFunc.{u}) :=
  Spec.map (CommRingCat.ofHom (algebraMap imperfectRatFunc.{u} (Polynomial sqrtExtension.{u})))

/-- The affine line over `𝔽₂(√t)` is not smooth over `𝔽₂(t)`. -/
theorem not_smooth_sqrtAffineLineStructureMap : ¬ Smooth sqrtAffineLineStructureMap.{u} := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  show ¬ (algebraMap imperfectRatFunc.{u} (Polynomial sqrtExtension.{u})).Smooth
  rw [RingHom.smooth_algebraMap]
  exact fun h ↦ not_formallySmooth_polynomial_sqrtExtension h.formallySmooth

/-- The affine line over `𝔽₂(√t)` is a curve over `𝔽₂(t)`. -/
instance isCurve_sqrtAffineLineStructureMap :
    IsCurve imperfectRatFunc.{u} sqrtAffineLineStructureMap.{u} where
  toIsVariety :=
    { toIsIntegral :=
        have : IsDomain (Polynomial sqrtExtension.{u}) := inferInstance
        inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := by
        rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
        change (algebraMap imperfectRatFunc.{u} (Polynomial sqrtExtension.{u})).FiniteType
        rw [RingHom.finiteType_algebraMap]
        exact Algebra.FiniteType.trans (S := sqrtExtension.{u}) inferInstance inferInstance
      toQuasiCompact := inferInstance }
  topologicalKrullDim_eq_one := topologicalKrullDim_spec_polynomial sqrtExtension.{u}

/-- The affine line over `𝔽₂(√t)` is a regular scheme. -/
theorem isRegular_sqrtAffineLine : IsRegular sqrtAffineLine.{u} :=
  Stacks.isRegular_spec_of_isRegularRing _

/-- **The nonsingular projective model need not be smooth** (the warning after Definition 0BY2,
Section 0BXX). There is a curve `X` over a field `k` which has a nonsingular projective model, and
no nonsingular projective model of `X` is smooth over `k`.

Here `k = 𝔽₂(t)` and `X` is the nonsingular projective model `Y` of the affine line over
`𝔽₂(√t)`, which is its own model. The affine line is an open subscheme of `Y`, and it is not smooth
over `k`, because `𝔽₂(√t)/𝔽₂(t)` is not separable; so `Y` is not smooth over `k`, and neither is
any other model, all models being isomorphic over `k`. -/
@[stacks 0BXX "the warning after Definition 0BY2, its first half: the nonsingular projective \
model of a curve need not be smooth over k"]
theorem exists_forall_not_smooth_nonsingularProjectiveModel :
    ∃ (k : Type u) (_ : Field k) (X : Scheme.{u}) (sX : X ⟶ Spec (.of k)) (_ : IsCurve k sX),
      Nonempty (NonsingularProjectiveModel k X sX) ∧
        ∀ M : NonsingularProjectiveModel k X sX, ¬ Smooth M.structureMap := by
  obtain ⟨Y, q, j, hj, hjq, hcurve, hproj, hreg, -, -⟩ :=
    exists_isRegular_isProjectiveMorphism_compactification imperfectRatFunc.{u}
      sqrtAffineLineStructureMap.{u} isRegular_sqrtAffineLine
  have : IsOpenImmersion j := hj
  have : IsCurve imperfectRatFunc.{u} q := hcurve
  have hq : ¬ Smooth q := fun h ↦ not_smooth_sqrtAffineLineStructureMap (hjq ▸ inferInstance)
  let M₀ : NonsingularProjectiveModel imperfectRatFunc.{u} Y q :=
    { Y := Y
      structureMap := q
      isCurve := hcurve
      isProjectiveVariety := (isProjectiveVariety_iff _ q).2 ⟨inferInstance, hproj⟩
      isRegular := hreg
      functionFieldEquiv :=
        let := functionFieldAlgebra imperfectRatFunc.{u} q
        AlgEquiv.refl }
  refine ⟨imperfectRatFunc.{u}, inferInstance, Y, q, hcurve, ⟨M₀⟩, fun M hM ↦ ?_⟩
  obtain ⟨e, ⟨he, -⟩, -⟩ := NonsingularProjectiveModel.existsUnique_iso M₀ M
  have : Smooth (e.hom ≫ M.structureMap) := inferInstance
  have he' : e.hom ≫ M.structureMap = q := he
  exact hq (he' ▸ this)

end NotSmooth

end AlgebraicGeometry

end
