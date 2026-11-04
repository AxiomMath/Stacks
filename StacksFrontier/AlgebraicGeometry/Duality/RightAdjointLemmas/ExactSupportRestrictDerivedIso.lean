module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImageLocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherentAnyModel
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportRestrictComparisonIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationIsomorphisms

/-!
# Derived sheaf Hom with exact support and restriction to an open subspace

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces and let `U ⊆ X` be open, with
restricted situation `i|_{i⁻¹U} : Z|_{i⁻¹U} ⟶ X|_U`. This file proves that the right derived
functor of sheaf Hom with exact support commutes with restriction to `U`:

`(R ℰom(𝒪_Z, K))|_{i⁻¹U} ≅ R ℰom(𝒪_{Z|_{i⁻¹U}}, K|_U)`,

at any chosen models of the four derived categories involved (the functors of
`Stacks.Duality.AnyModel`).

## Main results

* `ClosedQuotientMorphismOfRingedSpaces.isKInjective_moduleRestriction_mapHomologicalComplex`:
  restriction to an open subspace carries K-injective complexes to K-injective complexes
  ([Stacks, Tag 08BJ]), extension by zero being an exact left adjoint.
* `ClosedQuotientMorphismOfRingedSpaces.nonempty_derivedSheafHomExactSupport_restrict_iso`:
  **the derived restriction isomorphism.**
* `Stacks.Duality.LocallySmall.nonempty_restrict_derivedSheafHomExactSupport_iso`: the same for a
  closed immersion of schemes and an open `U` of the target, at the locally small derived
  categories, with Mathlib's restriction functors and the restricted morphism `i ∣_ U`.

## Implementation notes

Both sides are computed on a K-injective resolution `K ⟶ J`
(`Stacks.Duality.AnyModel.derivedSheafHomExactSupportObjIso`), and the termwise isomorphism
`ℰom(𝒪_Z, J)|_{i⁻¹U} ≅ ℰom(𝒪_{Z|_{i⁻¹U}}, J|_U)` is the underived comparison, an isomorphism by
`ClosedQuotientMorphismOfRingedSpaces.isIso_sheafHomExactSupportRestrictComparison`. The
statement is an existence statement: the isomorphism is not compared with
`ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportRestrictComparison`.

## References

* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage Stacks.AlgebraicGeometry.SchemeHigherDirectImage

universe w u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u}) (U : Opens S.X)



/-- **Restriction to an open subspace preserves K-injective complexes** ([Stacks, Tag 08BJ]):
it is right adjoint to extension by zero, which is exact. -/
theorem isKInjective_moduleRestriction_mapHomologicalComplex (X : RingedSpace.{u, u})
    (V : Opens X)
    (J : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) [J.IsKInjective] :
    CochainComplex.IsKInjective
      (((moduleRestriction X V).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
  @CochainComplex.isKInjective_mapHomologicalComplex_of_exact _ _ _ _ _ _ (moduleRestriction X V)
    (ExtensionByZeroModules.jShriek V (structureSheafRing X)) _
    (ExtensionByZeroModules.jShriek_additive V (structureSheafRing X))
    (ExtensionByZeroModules.jShriekAdjunction V (structureSheafRing X))
    (ExtensionByZeroModules.jShriek_preservesFiniteLimits V (structureSheafRing X))
    (@PreservesColimitsOfSize.preservesFiniteColimits _ _ _ _ _
      (ExtensionByZeroModules.jShriek_preservesColimitsOfSizeZero V (structureSheafRing X)))
    J _

variable [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing S.X))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing S.Z))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing (S.restrict U).X))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing (S.restrict U).Z))]

/-- **Derived sheaf Hom with exact support commutes with restriction to an open subspace**, at
any chosen models of the four derived categories:
`(R ℰom(𝒪_Z, K))|_{i⁻¹U} ≅ R ℰom(𝒪_{Z|_{i⁻¹U}}, K|_U)`. For a K-injective resolution
`K ⟶ J`, both sides are represented by `ℰom(𝒪_Z, J)|_{i⁻¹U} ≅ ℰom(𝒪_{Z|_{i⁻¹U}}, J|_U)`, the
termwise underived isomorphism: restriction to an open is exact and carries K-injective
complexes to K-injective complexes (`isKInjective_moduleRestriction_mapHomologicalComplex`). -/
theorem nonempty_derivedSheafHomExactSupport_restrict_iso
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    Nonempty ((moduleRestriction S.Z (preimageOpen S.i U)).mapDerivedCategory.obj
        ((Stacks.Duality.AnyModel.derivedSheafHomExactSupport.{w} S).obj K) ≅
      (Stacks.Duality.AnyModel.derivedSheafHomExactSupport.{w} (S.restrict U)).obj
        ((moduleRestriction S.X U).mapDerivedCategory.obj K)) := by
  obtain ⟨K', ⟨eK⟩⟩ : ∃ K', Nonempty (DerivedCategory.Q.obj K' ≅ K) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  obtain ⟨J, s, hJ, hs⟩ := Stacks.DerivedFunctor.exists_quasiIso_isKInjective K'
  let resX := moduleRestriction S.X U
  let resZ := moduleRestriction S.Z (preimageOpen S.i U)
  have hJ' := isKInjective_moduleRestriction_mapHomologicalComplex S.X U J
  have hs' : QuasiIso ((resX.mapHomologicalComplex (ComplexShape.up ℤ)).map s) := inferInstance
  let e := asIso (S.sheafHomExactSupportRestrictComparison U).natTrans
  have : (S.restrict U).sheafHomExactSupport.Additive :=
    (S.restrict U).modulePushforwardSheafHomExactSupportAdjunction.right_adjoint_additive
  refine ⟨resZ.mapDerivedCategory.mapIso
      ((Stacks.Duality.AnyModel.derivedSheafHomExactSupport.{w} S).mapIso
          (eK.symm ≪≫ ((DerivedCategory.quotientCompQhIso _).app K').symm) ≪≫
        Stacks.Duality.AnyModel.derivedSheafHomExactSupportObjIso.{w} S s hJ hs) ≪≫
    resZ.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app J) ≪≫
    (Stacks.Duality.AnyModel.derivedSheafHomExactSupportObjIso.{w} (S.restrict U) _ hJ'
      hs').symm ≪≫
    (Stacks.Duality.AnyModel.derivedSheafHomExactSupport.{w} (S.restrict U)).mapIso
      ((DerivedCategory.quotientCompQhIso _).app _ ≪≫
        (resX.mapDerivedCategoryFactors.app K').symm) ≪≫
    (Stacks.Duality.AnyModel.derivedSheafHomExactSupport.{w} (S.restrict U)).mapIso
      (resX.mapDerivedCategory.mapIso eK)⟩


end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

/-- `R ℰom(𝒪_Z, -)` depends on a closed quotient morphism only through its underlying morphism of
ringed spaces: replacing the morphism by an equal one does not change the functor up to
isomorphism. -/
theorem nonempty_derivedSheafHomExactSupport_congr_i (S : ClosedQuotientMorphismOfRingedSpaces.{u})
    (g : S.Z ⟶ S.X) (hg : S.i = g) (h₁ h₂)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing S.X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing S.Z))]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    Nonempty ((Stacks.Duality.AnyModel.derivedSheafHomExactSupport.{w} S).obj K ≅
      (Stacks.Duality.AnyModel.derivedSheafHomExactSupport.{w}
        ⟨S.X, S.Z, g, h₁, h₂⟩).obj K) := by
  subst hg
  exact ⟨Iso.refl _⟩

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

namespace Stacks.Duality.LocallySmall

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (U : X.Opens)

/-- **`R ℰom(𝒪_Y, -)` along a closed immersion of schemes commutes with restriction to an open of
the target**, at the locally small derived categories: for `i : Y ⟶ X` and `U ⊆ X` open,
`(R ℰom(𝒪_Y, K))|_{i⁻¹U} ≅ R ℰom(𝒪_{i⁻¹U}, K|_U)` for the restricted closed immersion
`i ∣_ U`. This is `nonempty_derivedSheafHomExactSupport_restrict_iso` read through the
identifications of Mathlib's restriction of modules and of `i ∣_ U` with their ringed-space
counterparts. -/
theorem nonempty_restrict_derivedSheafHomExactSupport_iso (K : DerivedCategory X.Modules) :
    Nonempty ((Scheme.Modules.restrictFunctor (i ⁻¹ᵁ U).ι).mapDerivedCategory.obj
        ((derivedSheafHomExactSupport i).obj K) ≅
      (derivedSheafHomExactSupport (i ∣_ U)).obj
        ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K)) := by
  simp only [restrictFunctor_eq_moduleRestriction]
  obtain ⟨e₂⟩ := (closedQuotient i).nonempty_derivedSheafHomExactSupport_restrict_iso U K
  obtain ⟨e₃⟩ := ((closedQuotient i).restrict U).nonempty_derivedSheafHomExactSupport_congr_i
    (i ∣_ U).toLRSHom.toShHom (toShHom_morphismRestrict i U).symm
    (closedQuotient (i ∣_ U)).isClosedEmbedding (closedQuotient (i ∣_ U)).isLocallySurjective
    ((moduleRestriction X.toRingedSpace U).mapDerivedCategory.obj K)
  exact ⟨e₂ ≪≫ e₃⟩

end Stacks.Duality.LocallySmall

end
