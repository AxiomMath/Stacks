module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverPointVanishing
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange

/-!
# The base change of a family of curves, and the cohomology of its fibres over fields

Let `f : X → S` be a family of curves (Stacks 0D4Z) and `g : S' → S` a morphism of schemes. The
base change `X' = X ×_S S' → S'` is again a family of curves: flatness, properness and finite
presentation are stable under base change (Stacks 03MO, 04WP, 03XP), and the relative dimension
at a point of `X'` is that of `f` at its image (Stacks 04NS). Here the total space is *the*
fibre product `AlgebraicGeometry.AlgebraicSpaces.fiberProduct` of `f` and `g`, the one in which
the hypotheses of Stacks 0E1J and 0E6B are written, so statements about the base change apply to
those fibres with no comparison isomorphism.

Over the spectrum `Spec k` of a field, the base change is a family over an affine Noetherian
one-point base, so the cohomology of a quasi-coherent module on the fibre `X_k` vanishes in
degrees `≥ 2` (`CurveFamily.isZero_rightDerived_globalSectionsFunctor_of_subsingleton`). This is
the vanishing `H^i(X_s, 𝒪_{X_s}) = 0` for `i ≥ 2` used in the proof of Stacks 0E1J.

## Main definitions

* `CurveFamily.baseChange`: the base change of a family of curves along a morphism of base
  schemes, with total space the fibre product.
* `CurveFamily.baseChangeHom`: the cartesian morphism from the base change to the family.

## Main results

* `CurveFamily.isZero_rightDerived_globalSectionsFunctor_fiberProduct_fieldValuedPoint`:
  `H^q(X ×_S Spec k, 𝓜) = 0` for `q ≥ 2`, every field-valued point `Spec k → S` and every
  quasi-coherent `𝓜`.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry

universe u

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **The base change of a family of curves.** For a family `f : X → S` and a morphism
`g : S' → S` of base schemes, the family `X ×_S S' → S'`, whose total space is the fibre product
of `f` and `g`. -/
def baseChange (X : CurveFamily B hZ) {V : BigFppfOver B integerBase hZ} (g : V ⟶ X.base) :
    CurveFamily B hZ where
  base := V
  total := AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap g)
  toBase := ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap g).hom)
  flat := (Space.isFlat_isStableUnderBaseChange B integerBase hZ).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase (schemeSpaceMap g))
    X.flat
  proper := (Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase (schemeSpaceMap g))
    X.proper
  finitePresentation :=
    (Space.isFinitePresentation_isStableUnderBaseChange (B := B) (S := integerBase)
      (hS := hZ)).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase (schemeSpaceMap g))
    X.finitePresentation
  relativeDimensionLE := by
    intro x'
    obtain ⟨e, he, hrel⟩ := X.relativeDimensionLE (Space.pointsMap B integerBase hZ _
      (pullback.fst X.toBase.hom (schemeSpaceMap g).hom) x')
    have hfinite : Space.IsLocallyOfFiniteType B integerBase hZ X.toBase.hom :=
      Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
        X.finitePresentation.1
    exact ⟨e, he, (Space.hasRelativeDimensionAt_iff_of_isPullback B integerBase hZ
      (IsPullback.of_hasPullback X.toBase.hom (schemeSpaceMap g).hom) X.total.property
      (schemeSpace V).property (schemeSpace X.base).property hfinite x' (e : ℕ∞)).mp hrel⟩

/-- **The cartesian morphism from the base change of a family of curves to the family.** -/
def baseChangeHom (X : CurveFamily B hZ) {V : BigFppfOver B integerBase hZ} (g : V ⟶ X.base) :
    X.baseChange g ⟶ X where
  baseMap := g
  totalMap := ObjectProperty.homMk (pullback.fst X.toBase.hom (schemeSpaceMap g).hom)
  cartesian := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase (schemeSpaceMap g)

attribute [local instance 5000] SheafOfModules.instAbelian in
attribute [local instance] Space.hasInjectiveResolutions_modules Space.enoughInjectives_modules in
/-- **The cohomology of a fibre of a family of curves over a field stops in degree one.** For a
family `f : X → S`, a field-valued point `Spec k → S` and a quasi-coherent module `𝓜` on the fibre
`X ×_S Spec k`, `H^q(X ×_S Spec k, 𝓜) = 0` for every `q ≥ 2`: the fibre is the total space of the
base change of `X` to the affine Noetherian one-point scheme `Spec k`. -/
theorem isZero_rightDerived_globalSectionsFunctor_fiberProduct_fieldValuedPoint
    (X : CurveFamily B hZ) (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (M : Space.Modules.{u, u} B integerBase hZ
      (AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap p.value)).1
      (AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap p.value)).2)
    (hM : M.IsQuasicoherentOnSite) {q : ℕ} (hq : 2 ≤ q) :
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ
          (AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap p.value)).1
          (AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase
            (schemeSpaceMap p.value)).2).O)).rightDerived q).obj M) :=
  have : Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj
      (X.baseChange p.value).base) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  have : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj (X.baseChange p.value).base) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of p.carrier)))
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B integerBase hZ).obj
      (X.baseChange p.value).base) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of p.carrier)))
  (X.baseChange p.value).isZero_rightDerived_globalSectionsFunctor_of_subsingleton M hM hq

end CurveFamily

end AlgebraicGeometry

end
