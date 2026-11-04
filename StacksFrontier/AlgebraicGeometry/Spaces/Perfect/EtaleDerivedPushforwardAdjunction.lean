module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.CoheratorQuasiInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.Homology.Injectives.DerivedCategory.ArbitraryModel
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

/-!
# Derived restriction along an étale morphism is left adjoint to the derived direct image

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`.  Restriction of
modules `f^* = (-)|_X` is exact and left adjoint to the direct image `f_*`
(`AlgebraicGeometry.Space.etaleModulePullbackAdjunction`).  Hence the functor it induces on
unbounded derived categories is left adjoint to every total right derived functor `Rf_*` of
`f_*` (Stacks 09T5), and such a total right derived functor exists, the modules being a
Grothendieck abelian category.

## Main definitions

* `AlgebraicGeometry.Space.etaleModulePullbackDerivedPushforwardAdjunction`: the adjunction
  `(-)|_X ⊣ Rf_*` on `D(𝒪_Y)` and `D(𝒪_X)`, for an arbitrary total right derived functor of the
  direct image relative to `CategoryTheory.DerivedCategory.Q`.

## Main results

* `AlgebraicGeometry.Space.exists_derivedModulePushforward`: a total right derived functor of the
  direct image exists.
* `AlgebraicGeometry.Space.nonempty_etaleModulePullback_mapDerivedCategory_adjunction`: derived
  restriction along an étale morphism has a right adjoint.

## References

* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

-- The universe-polymorphic `Abelian` instance of `Stacks.Cohomology.SiteModules`, imported with
-- `Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory`, leaves the module universe of
-- `AlgebraicGeometry.Space.Modules` undetermined; the instance of Mathlib is the one used here.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

/-- **A total right derived functor of the direct image exists**: the modules on the small
étale ringed site of `X` are Grothendieck abelian, so every complex has a K-injective
resolution (Stacks 079P) and the degreewise direct image followed by `DerivedCategory.Q` has a
total right derived functor. -/
theorem exists_derivedModulePushforward :
    ∃ (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
        DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
      (α : (modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R),
      R.IsRightDerivedFunctor α
        (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
  let := isGrothendieckAbelian_modules B S hS X.1 X.2
  have :=
    Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (A := Modules.{u, u} B S hS Y.1 Y.2) (modulePushforward B S hS f)
  ⟨((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)),
    ((modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)),
    inferInstance⟩

/-- **Derived restriction along an étale morphism is left adjoint to the derived direct
image** (Stacks 09T5): for an étale `f : X ⟶ Y` and any total right derived functor `Rf_*` of
the direct image, `(-)|_X ⊣ Rf_*` on unbounded derived categories.

It is `Stacks.DerivedModel.adjunctionOfExact` at the exact left adjoint `f^*`, read through
`Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory`. -/
def etaleModulePullbackDerivedPushforwardAdjunction
    (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (α : (modulePushforward B S hS f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    [R.IsRightDerivedFunctor α
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] :
    (etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory ⊣ R :=
  letI := isGrothendieckAbelian_modules B S hS X.1 X.2
  (Stacks.DerivedModel.adjunctionOfExact (etaleModulePullback.{u, u} B S hS f hf)
    DerivedCategory.Q DerivedCategory.Q (etaleModulePullbackAdjunction B S hS f hf) R
    α).ofNatIsoLeft
    (Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory
      (etaleModulePullback.{u, u} B S hS f hf))

/-- **Derived restriction along an étale morphism has a right adjoint**, the derived direct
image. -/
theorem nonempty_etaleModulePullback_mapDerivedCategory_adjunction :
    ∃ R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
        DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2),
      Nonempty ((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory ⊣ R) := by
  obtain ⟨R, α, hR⟩ := exists_derivedModulePushforward B S hS f
  exact ⟨R, ⟨etaleModulePullbackDerivedPushforwardAdjunction B S hS f hf R α⟩⟩

end AlgebraicGeometry.Space

end
