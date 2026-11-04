module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoheratorQuasiInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSeparator

/-!
# The coherator and the derived coherator of an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  By
Stacks 077V (2) the inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` has a right adjoint, the *coherator*
`Q_X`; its total right derived functor on the whole unbounded derived category is the *derived
coherator* `RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))` of Stacks 08GZ / 09TG / 08H0.  This file names both, so
that every statement about `Q_X` and `RQ_X` is about one and the same functor.

## Main definitions

* `AlgebraicGeometry.Space.coherator`: the coherator `Q_X`, the right adjoint of `ι` supplied by
  Stacks 077V (2), `AlgebraicGeometry.Space.isLeftAdjoint_ι_quasicoherentSheaves`.
* `AlgebraicGeometry.Space.coheratorAdjunction`: the adjunction `ι ⊣ Q_X`.
* `AlgebraicGeometry.Space.derivedCoherator`: `RQ_X`, the total right derived functor of `Q_X`
  relative to `CategoryTheory.DerivedCategory.Q`.
* `AlgebraicGeometry.Space.derivedCoheratorUnit`: its derivation unit; the instance
  `AlgebraicGeometry.Space.derivedCoherator_isRightDerivedFunctor` says it is a right derived
  functor.

## Implementation notes

The module universe is the universe `u` of the schemes: there `QCoh(𝒪_X)` is Grothendieck
abelian (Stacks 077V (1)) and `Mod(𝒪_X)` is Grothendieck abelian, which supplies the right adjoint
and the K-injective resolutions making `RQ_X` exist on the whole unbounded derived category.

The derived categories are the standard models `CategoryTheory.HasDerivedCategory.standard`, and
the localization is `CategoryTheory.DerivedCategory.Q`, as for the comparison functor
`AlgebraicGeometry.Space.quasicoherentDerivedComparison` of Stacks 08F1.  So `coherator`,
`coheratorAdjunction`, `derivedCoherator` and `derivedCoheratorUnit` instantiate the binders
`CF`, `adjF`, `RQ` and `RQUnit` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/DerivedCoheratorQuasiInverse.lean`.

The coherator is *a* right adjoint, chosen by `CategoryTheory.Functor.rightAdjoint`; any other
right adjoint is canonically isomorphic to it (`CategoryTheory.Adjunction.rightAdjointUniq`), and
the source's "the right adjoint" means exactly this.

## References

* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 08GZ](https://stacks.math.columbia.edu/tag/08GZ)
* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
* [Stacks Project, Tag 09TG](https://stacks.math.columbia.edu/tag/09TG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
  isClosedUnderKernels_quasicoherentSheaves_schemeUniverse
  isClosedUnderCokernels_quasicoherentSheaves quasicoherentSheaves_abelian_of_closure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The inclusion `QCoh(𝒪_X) ⥤ Mod(𝒪_X)` is a left adjoint, at the module universe of the
schemes: Stacks 077V (2), `AlgebraicGeometry.Space.isLeftAdjoint_ι_quasicoherentSheaves`, with
its two closure hypotheses discharged. -/
instance isLeftAdjoint_ι_quasicoherentSheaves_schemeUniverse :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).ι.IsLeftAdjoint :=
  isLeftAdjoint_ι_quasicoherentSheaves B S hS F hF

/-- **The coherator** `Q_X : Mod(𝒪_X) ⥤ QCoh(𝒪_X)` of an algebraic space, the right adjoint of
the inclusion of the quasi-coherent modules (Stacks 077V (2)). -/
def coherator : Modules.{u, u} B S hS F hF ⥤ QuasicoherentSheaves.{u, u} B S hS F hF :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι.rightAdjoint

/-- The adjunction `ι ⊣ Q_X` between the inclusion of the quasi-coherent modules and the
coherator. -/
def coheratorAdjunction :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι ⊣
        coherator B S hS F hF :=
  Adjunction.ofIsLeftAdjoint _

/-- The coherator is additive, being a right adjoint of the additive inclusion. -/
instance coherator_additive : (coherator B S hS F hF).Additive :=
  (coheratorAdjunction B S hS F hF).right_adjoint_additive

/-- The counit `Q_X(𝓕) ⟶ 𝓕` of the coherator adjunction is an isomorphism at every quasi-coherent
`𝒪_X`-module (Stacks 077V (2)). -/
instance isIso_coheratorAdjunction_counit_app (M : QuasicoherentSheaves.{u, u} B S hS F hF) :
    IsIso ((coheratorAdjunction B S hS F hF).counit.app
      ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O))).ι.obj M)) :=
  have : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι.Full :=
    inferInstance
  (Adjunction.isIso_counit_app_iff_mem_essImage _).mpr ⟨M, ⟨Iso.refl _⟩⟩

open Stacks.Injectives.KInjectiveResolution in
/-- The coherator, applied termwise and followed by the localization, has a total right derived
functor on the whole homotopy category of `𝒪_X`-modules: the `𝒪_X`-modules are Grothendieck
abelian at the universe of the schemes, so every cochain complex has a K-injective
resolution. -/
instance coherator_hasRightDerivedFunctor :
    ((coherator B S hS F hF).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS F hF)).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)) :=
  letI := isGrothendieckAbelian_modules B S hS F hF
  hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (A := QuasicoherentSheaves.{u, u} B S hS F hF) (coherator B S hS F hF)

/-- **The derived coherator** `RQ_X : D(𝒪_X) ⥤ D(QCoh(𝒪_X))` of an algebraic space: the total
right derived functor of the coherator on the whole unbounded derived category. -/
def derivedCoherator :
    DerivedCategory (Modules.{u, u} B S hS F hF) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS F hF) :=
  ((coherator B S hS F hF).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q).totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ))

/-- The derivation unit of the derived coherator: the comparison from the termwise coherator to
`RQ_X`. -/
def derivedCoheratorUnit :
    (coherator B S hS F hF).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS F hF) ⟶
      DerivedCategory.Q (C := Modules.{u, u} B S hS F hF) ⋙ derivedCoherator B S hS F hF :=
  ((coherator B S hS F hF).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ))

/-- The derivation unit exhibits `RQ_X` as a right derived functor of the coherator. -/
instance derivedCoherator_isRightDerivedFunctor :
    (derivedCoherator B S hS F hF).IsRightDerivedFunctor (derivedCoheratorUnit B S hS F hF)
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)) :=
  inferInstanceAs ((((coherator B S hS F hF).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q).totalRightDerived DerivedCategory.Q
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF)
        (ComplexShape.up ℤ))).IsRightDerivedFunctor
    (((coherator B S hS F hF).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q).totalRightDerivedUnit DerivedCategory.Q
        (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ))) _)

/-- The derived coherator restricted to `D_QCoh(𝒪_X)` is right adjoint to the comparison functor
`D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1:
`AlgebraicGeometry.Space.comparisonDerivedCoheratorAdjunction` at the coherator of this file. -/
def comparisonDerivedCoheratorAdjunctionOfCoherator :
    quasicoherentDerivedComparison B S hS F hF ⊣
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)))).ι ⋙ derivedCoherator B S hS F hF :=
  comparisonDerivedCoheratorAdjunction B S hS F hF (coherator B S hS F hF)
    (coheratorAdjunction B S hS F hF) (derivedCoherator B S hS F hF)
    (derivedCoheratorUnit B S hS F hF)

end AlgebraicGeometry.Space

end
