module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardUpperBound
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedQuasicoherentSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedAcyclicPushforward

/-!
# Derived direct image along an affine morphism of algebraic spaces on quasi-coherent modules

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Direct image preserves quasi-coherence (the quasi-coherence assertion of
[Stacks, Tag 07U8]) so it restricts to `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`, and *that* restriction is
exact: left exactness is free, direct image of all modules being a right adjoint, and right
exactness comes from the vanishing of the higher direct images on quasi-coherent modules
([Stacks, Tag 073H]).  An exact functor induces a functor of unbounded derived categories with no
derivation, so `f_*` defines `D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))`, which is the first assertion of
[Stacks, Tag 08GY]; and the comparison functor of [Stacks, Tag 08F1] carries that functor to the
derived direct image `Rf_*`, which is the second.  **Both assertions of the tag are registered
here, with no hypothesis beyond the source's.**

## Main results

* `AlgebraicGeometry.Space.isRightDerivedFunctor_quasicoherentPushforwardMapDerivedCategory`:
  **the first assertion of [Stacks, Tag 08GY]** — the functor induced on unbounded derived
  categories by the exact functor `AlgebraicGeometry.Space.quasicoherentPushforward` is a total
  right derived functor of it, so the derived functor is computed by applying `f_*` to a
  representative complex.
* `AlgebraicGeometry.Space.derivedQuasicoherentComparisonSquareOfIsAffineHom`:
  **the commuting square of [Stacks, Tag 08GY]**, with no hypothesis.
* `AlgebraicGeometry.Space.preservesFiniteColimitsQuasicoherentPushforwardOfIsAffineHom`:
  right exactness of the quasi-coherent direct image, with no hypothesis.
* `AlgebraicGeometry.Space.isIso_derivedModulePushforwardUnit_app_of_isQuasicoherentOnSite`:
  a complex of quasi-coherent `𝒪_X`-modules computes its own derived direct image, which is
  [Stacks, Tag 0G9N] for an affine morphism of algebraic spaces and the one input the square
  needs.

## Implementation notes

This file is where the inputs that the three preceding files carry are discharged, so that both
assertions of the tag hold under the source's hypotheses alone:

* preservation of quasi-coherence is
  `AlgebraicGeometry.Space.pushforwardPreservesQuasicoherence_of_isAffineHom`, the
  quasi-coherence assertion of [Stacks, Tag 07U8];
* the acyclicity input `hac` of
  `StacksFrontier/AlgebraicGeometry/Spaces/AffineQuasicoherentPushforwardExact.lean` is
  `AlgebraicGeometry.Space.rightAcyclic_modulePushforward_of_isQuasicoherentOnSite`,
  [Stacks, Tag 073H] read through the acyclicity criterion of [Stacks, Tag 015C];
* the input `hG9N` of
  `StacksFrontier/AlgebraicGeometry/Spaces/AffineDerivedQuasicoherentSquare.lean` is
  `AlgebraicGeometry.Space.isIso_derivedModulePushforwardUnit_app_of_isQuasicoherentOnSite`
  below, which is `AlgebraicGeometry.Space.isIso_to_rightDerived_of_termwise_acyclic` at `N = 1`
  with its two hypotheses supplied by [Stacks, Tag 073H] and by the upper cohomological bound
  `AlgebraicGeometry.Space.isLE_derivedModulePushforward_obj_of_isAffineHom`.

So the statements below assume exactly what the source assumes: an affine morphism of algebraic
spaces over `S`.

**Where the square lives.**  The square is stated inside `D(𝒪_Y)`, i.e. after the fully faithful
inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)` on both corners of its right-hand column, which is where the
tagged statement states it and which is an equivalent assertion; the reason is that the
right edge *inside* `D_QCoh` is the restriction of `Rf_*`, whose existence is part (1) of
[Stacks, Tag 08D5] and is not an assertion of [Stacks, Tag 08GY].  The full discussion is in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineDerivedQuasicoherentSquare.lean`.

**`Rf_*` is a binder.**  The square is stated for an arbitrary total right derived functor of the
direct image of all modules together with its derivation unit, as the neighbouring
[Stacks, Tag 08GZ] is; such a pair exists for every morphism of algebraic spaces, by
`AlgebraicGeometry.Space.hasRightDerivedFunctor_modulePushforward`, and the source's `Rf_*` is one
of them.

`HasDerivedCategory` is supplied by `CategoryTheory.HasDerivedCategory.standard` as a local
instance, which is the model
`AlgebraicGeometry.Space.quasicoherentDerivedComparisonSchemeUniverse` — the comparison functor
of [Stacks, Tag 08F1] that the square of [Stacks, Tag 08GY] has for its rows — is read at.

## References

* [Stacks Project, Tag 08GY](https://stacks.math.columbia.edu/tag/08GY)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 015F](https://stacks.math.columbia.edu/tag/015F)
* [Stacks Project, Tag 08F1](https://stacks.math.columbia.edu/tag/08F1)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_modules
attribute [local instance] enoughInjectives_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **Direct image along an affine morphism of algebraic spaces is right exact on quasi-coherent
modules**, with no hypothesis.

This is
`AlgebraicGeometry.Space.preservesFiniteColimits_quasicoherentPushforward_of_isAffineHom` with
its acyclicity input discharged by
`AlgebraicGeometry.Space.rightAcyclic_modulePushforward_of_isQuasicoherentOnSite`, the vanishing
of the higher direct images of [Stacks, Tag 073H]. -/
theorem preservesFiniteColimitsQuasicoherentPushforwardOfIsAffineHom (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) :
    PreservesFiniteColimits (quasicoherentPushforward B S hS f
      (pushforwardPreservesQuasicoherence_of_isAffineHom B S hS f hf)) :=
  preservesFiniteColimits_quasicoherentPushforward_of_isAffineHom B S hS f hf
    fun M hM ↦ rightAcyclic_modulePushforward_of_isQuasicoherentOnSite B S hS f hf M hM

/-- **[Stacks, Tag 08GY], the derived functor.**  Let `f : X ⟶ Y` be an affine morphism of
algebraic spaces over a scheme `S`.  Then direct image defines a derived functor
`f_* : D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))`: the functor induced on the unbounded derived categories by
the exact functor `AlgebraicGeometry.Space.quasicoherentPushforward` is a total right derived
functor of it.  No resolutions are involved, and the derived functor is computed by applying
`f_*` to a representative complex, which is how the source states it.

The structure map is `CategoryTheory.Functor.mapDerivedCategoryFactorsh.inv`, which exhibits the
induced functor as a lift through the localization `DerivedCategory.Qh`; a lift of a functor that
inverts the quasi-isomorphisms is a right derived functor for the inverse of the lifting
isomorphism. -/
@[stacks 08GY "the derived functor"]
theorem isRightDerivedFunctor_quasicoherentPushforwardMapDerivedCategory (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) :
    letI := preservesFiniteColimitsQuasicoherentPushforwardOfIsAffineHom B S hS f hf
    Functor.IsRightDerivedFunctor
      (quasicoherentPushforward B S hS f
        (pushforwardPreservesQuasicoherence_of_isAffineHom B S hS f hf)).mapDerivedCategory
      (quasicoherentPushforward B S hS f
          (pushforwardPreservesQuasicoherence_of_isAffineHom B S hS f
            hf)).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
        (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_quasicoherentPushforward_mapDerivedCategory_of_isAffineHom B S hS f hf
    fun M hM ↦ rightAcyclic_modulePushforward_of_isQuasicoherentOnSite B S hS f hf M hM

/-! ### The commuting square -/

section Square

variable (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
  (Rf : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
  (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rf)
  [Rf.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]

include hf in
/-- **[Stacks, Tag 0G9N] for an affine morphism of algebraic spaces.**  A cochain complex of
quasi-coherent `𝒪_X`-modules computes its own derived direct image: the derivation unit `α` of
`Rf_*` is invertible at the homotopy class of such a complex.

This is `AlgebraicGeometry.Space.isIso_to_rightDerived_of_termwise_acyclic` at `N = 1` with both
of its hypotheses supplied — termwise acyclicity by
`AlgebraicGeometry.Space.rightAcyclic_modulePushforward_of_isQuasicoherentOnSite`, which is
[Stacks, Tag 073H], and the upper cohomological bound by
`AlgebraicGeometry.Space.isLE_derivedModulePushforward_obj_of_isAffineHom`, which is part (2) of
[Stacks, Tag 08D5] for an affine morphism, where `N = 1`. -/
theorem isIso_derivedModulePushforwardUnit_app_of_isQuasicoherentOnSite
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hqc : ∀ n, (K.X n).IsQuasicoherentOnSite) :
    IsIso (α.app ((HomotopyCategory.quotient (Modules.{u, u} B S hS X.1 X.2)
      (ComplexShape.up ℤ)).obj K)) :=
  isIso_to_rightDerived_of_termwise_acyclic B S hS f K hqc
    (fun n ↦ rightAcyclic_modulePushforward_of_isQuasicoherentOnSite B S hS f hf _ (hqc n))
    Rf α 1 fun E d hcoh hE ↦ by
      have h := isLE_derivedModulePushforward_obj_of_isAffineHom B S hS f hf Rf α E hcoh d hE
      simpa using h

/-- **[Stacks, Tag 08GY], the commuting square.**  Let `f : X ⟶ Y` be an affine morphism of
algebraic spaces over a scheme `S`, and let `Rf_*` be a total right derived functor of the direct
image of all `𝒪_X`-modules, with derivation unit `α`.  Then the square

`D(QCoh(𝒪_X)) ⟶ D_QCoh(𝒪_X) ⟶^{Rf_*} D_QCoh(𝒪_Y)`,
`D(QCoh(𝒪_X)) ⟶^{f_*} D(QCoh(𝒪_Y)) ⟶ D_QCoh(𝒪_Y)`

commutes, its rows being the comparison functor of [Stacks, Tag 08F1] and its left edge the
derived functor of
`AlgebraicGeometry.Space.isRightDerivedFunctor_quasicoherentPushforwardMapDerivedCategory`.

This is `AlgebraicGeometry.Space.derivedQuasicoherentComparisonSquare` with both of its inputs
supplied: right exactness of the quasi-coherent direct image by
`AlgebraicGeometry.Space.preservesFiniteColimitsQuasicoherentPushforwardOfIsAffineHom`, and that
a complex of quasi-coherent modules computes its derived direct image by
`AlgebraicGeometry.Space.isIso_derivedModulePushforwardUnit_app_of_isQuasicoherentOnSite`. -/
@[stacks 08GY "the commuting square"]
noncomputable def derivedQuasicoherentComparisonSquareOfIsAffineHom :
    letI := preservesFiniteColimitsQuasicoherentPushforwardOfIsAffineHom B S hS f hf
    (quasicoherentPushforward B S hS f
          (pushforwardPreservesQuasicoherence_of_isAffineHom B S hS f hf)).mapDerivedCategory ⋙
        quasicoherentDerivedComparisonSchemeUniverse B S hS Y.1 Y.2 ⋙
          (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).ι ≅
      quasicoherentDerivedComparisonSchemeUniverse B S hS X.1 X.2 ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⋙
        Rf :=
  letI := preservesFiniteColimitsQuasicoherentPushforwardOfIsAffineHom B S hS f hf
  derivedQuasicoherentComparisonSquare B S hS f Rf α
    (fun K hqc ↦ isIso_derivedModulePushforwardUnit_app_of_isQuasicoherentOnSite
      B S hS f hf Rf α K hqc)
    (pushforwardPreservesQuasicoherence_of_isAffineHom B S hS f hf)
    (preservesFiniteColimitsQuasicoherentPushforwardOfIsAffineHom B S hS f hf)

end Square

end AlgebraicGeometry.Space

end
