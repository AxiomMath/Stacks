module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRelativeDualizingSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedRightAdjointDuality
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsLocallyProjective
public import StacksFrontier.AlgebraicGeometry.Duality.C1590Private.RelativeDualizingSheaf
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic

/-!
# The relative dualizing complex of a represented morphism over an affine base

Let `φ : V ⟶ T` be a morphism of the big fppf site over `S` with `T` affine, whose underlying
morphism of schemes `q : V_0 ⟶ T_0` is proper, and whose represented morphism of algebraic spaces
is of finite presentation. The relative dualizing complex `a(𝒪_T)` of the represented morphism
(`AlgebraicGeometry.Space.affineRelativeDualizingComplex`) corresponds, under the equivalence
`D_QCoh(𝒪_{V_0}) ≌ D_QCoh(𝒪_V)` of Stacks 071Q, to the relative dualizing complex
`ω^•_{V_0/T_0} = q^×(𝒪_{T_0})` of `q` (`AlgebraicGeometry.C1590Private.relativeDualizingComplex`).
This is Stacks 0E6E at the structure sheaf: the equivalence carries `𝒪_{T_0}` to `𝒪_T`. Since
cohomology sheaves commute with the equivalence, `a(𝒪_T)` has the amplitude of `ω^•_{V_0/T_0}`
above, and the restriction of `ω_{V/T} = H^{-1}(a(𝒪_T))` to the scheme `V_0` is
`ω_{V_0/T_0} = H^{-1}(ω^•_{V_0/T_0})`.

## Main definitions

* `AlgebraicGeometry.Space.homologyRepresentedDualityEquivalenceIso`: `H^n` of the image of `K`
  under Stacks 071Q is `ε^* H^n(K)`.
* `AlgebraicGeometry.Space.restrictToChartSchemeHomologyRepresentedDualityEquivalenceIso`: its
  restriction to the identity chart is `H^n(K)`.
* `AlgebraicGeometry.Space.representedDualityEquivalenceDerivedStructureSheafIso`: Stacks 071Q
  carries `𝒪_{T_0}` to `𝒪_T`.
* `AlgebraicGeometry.Space.affineRelativeDualizingComplexRepresentedIso`: `a(𝒪_T)` is the image
  of `ω^•_{V_0/T_0}`.
* `AlgebraicGeometry.Space.restrictToChartSchemeAffineRelativeDualizingSheafIso`: `ω_{V/T}` read
  on `V_0` is `ω_{V_0/T_0}`.

## Main results

* `AlgebraicGeometry.Space.isLE_representedDualityEquivalence_functor_obj`: Stacks 071Q
  preserves amplitude above.
* `AlgebraicGeometry.Space.isLE_affineRelativeDualizingComplex_of_isLE`: `a(𝒪_T)` has no
  cohomology above degree `d` when `ω^•_{V_0/T_0}` has none.

## Implementation notes

The derived categories of modules on the algebraic spaces are read at
`HasDerivedCategory.standard`, the model of `AlgebraicGeometry.Space.QuasicoherentDerivedCategory`;
those of the schemes at the locally small model, the model of
`AlgebraicGeometry.C1590Private.relativeDualizingComplex`.

## References

* [Stacks Project, Tag 0E6E](https://stacks.math.columbia.edu/tag/0E6E)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace StacksDraft.DerivedModel

/-- **The comparison of models carries objects placed in degree zero to objects placed in degree
zero**: the inverse of the comparison `Stacks.Injectives.grothendieckModelEquiv` of the standard
model with the model of Stacks 079Q carries `N[0]` to `N[0]`. -/
def grothendieckModelEquivInverseSingleIso {C : Type (u + 1)} [Category.{u} C] [Abelian C]
    [IsGrothendieckAbelian.{u} C] (N : C) :
    (Stacks.Injectives.grothendieckModelEquiv.{u} C).inverse.obj
        ((@DerivedCategory.singleFunctor C _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} C) 0).obj N) ≅
      (@DerivedCategory.singleFunctor C _ _ (HasDerivedCategory.standard C) 0).obj N :=
  (Stacks.Injectives.grothendieckModelEquiv.{u} C).inverse.mapIso
      ((StacksDraft.DerivedModel.grothendieckModelEquivFunctorIso C).app _ ≪≫
        (StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard C)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} C)).functor.mapIso
          ((@DerivedCategory.singleFunctorIsoCompQ C _ _ (HasDerivedCategory.standard C) 0).app
            N) ≪≫
        (StacksDraft.DerivedModel.modelCompQIso (HasDerivedCategory.standard C)
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} C)).app _ ≪≫
        ((@DerivedCategory.singleFunctorIsoCompQ C _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} C) 0).app
            N).symm).symm ≪≫
    ((Stacks.Injectives.grothendieckModelEquiv.{u} C).unitIso.app _).symm

/-- A functor isomorphic to the functor `D(F)` induced by an exact functor `F` carries an object
isomorphic to `N[0]` to `M[0]` for `F(N) ≅ M`. The models of the derived categories are implicit
arguments, read off the isomorphism `e`. -/
def mapDerivedCategorySingleObjIso {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] {_ : Abelian C₁}
    {_ : Abelian C₂} {_ : HasDerivedCategory C₁} {_ : HasDerivedCategory C₂} (F : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {L : DerivedCategory C₁ ⥤ DerivedCategory C₂} (e : L ≅ F.mapDerivedCategory)
    {K : DerivedCategory C₁} {N : C₁} {M : C₂} (a : K ≅ (DerivedCategory.singleFunctor C₁ 0).obj N)
    (b : F.obj N ≅ M) :
    L.obj K ≅ (DerivedCategory.singleFunctor C₂ 0).obj M :=
  L.mapIso a ≪≫ e.app _ ≪≫ (F.mapDerivedCategorySingleFunctor 0).app N ≪≫
    (DerivedCategory.singleFunctor C₂ 0).mapIso b

end StacksDraft.DerivedModel

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Homology

variable (T : BigFppfOver B S hS)

/-- **Cohomology commutes with the equivalence of Stacks 071Q.** -/
def homologyRepresentedDualityEquivalenceIso
    (K : Stacks.Duality.quasiCoherentDerivedCategory
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T)) (n : ℤ) :
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS (representedSpace T).1 (representedSpace T).2)
    (DerivedCategory.homologyFunctor _ n).obj
        ((representedDualityQuasicoherentDerivedEquivalence B S hS T).functor.obj K).obj ≅
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).obj
        ((DerivedCategory.homologyFunctor
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules n).obj K.obj) :=
  letI := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (representedSpace T).1 (representedSpace T).2)
  (representedZariskiDerivedPullbackHomologyIso B S hS T n).app
      ((Stacks.Duality.quasiCoherentDerivedCategoryModelEquiv
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T)).inverse.obj K).obj ≪≫
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T).mapIso
      (((StacksDraft.DerivedModel.grothendieckModelEquivHomologyIso
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules n).app
          ((Stacks.Duality.quasiCoherentDerivedCategoryModelEquiv
            (representedSchemeRepresentedZariskiRingedToposHom B S hS T)).inverse.obj
              K).obj).symm ≪≫
        (DerivedCategory.homologyFunctor
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules n).mapIso
          ((ObjectProperty.ι _).mapIso
          ((Stacks.Duality.quasiCoherentDerivedCategoryModelEquiv
            (representedSchemeRepresentedZariskiRingedToposHom B S hS T)).counitIso.app K)))

/-- **The equivalence of Stacks 071Q preserves amplitude above.** If `K ∈ D_QCoh(𝒪_{X_0})` has no
cohomology above degree `d`, neither has its image in `D_QCoh(𝒪_X)`. -/
theorem isLE_representedDualityEquivalence_functor_obj
    (K : Stacks.Duality.quasiCoherentDerivedCategory
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T)) (d : ℤ) (hK : K.obj.IsLE d) :
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS (representedSpace T).1 (representedSpace T).2)
    ((representedDualityQuasicoherentDerivedEquivalence B S hS T).functor.obj K).obj.IsLE d := by
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (representedSpace T).1 (representedSpace T).2)
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact IsZero.of_iso (Functor.map_isZero _ ((DerivedCategory.isLE_iff K.obj d).1 hK i hi))
    (homologyRepresentedDualityEquivalenceIso T K i ≪≫
      (representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
        B S hS T).app _)

/-- **Restricting to the scheme undoes the equivalence of Stacks 071Q on cohomology.** For
`K ∈ D_QCoh(𝒪_{X_0})`, the restriction of `H^n` of its image in `D_QCoh(𝒪_X)` to the identity
chart of `X` is `H^n(K)`. -/
def restrictToChartSchemeHomologyRepresentedDualityEquivalenceIso
    (K : Stacks.Duality.quasiCoherentDerivedCategory
      (representedSchemeRepresentedZariskiRingedToposHom B S hS T)) (n : ℤ) :
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS (representedSpace T).1 (representedSpace T).2)
    restrictToChartScheme B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
        ((DerivedCategory.homologyFunctor _ n).obj
          ((representedDualityQuasicoherentDerivedEquivalence B S hS T).functor.obj K).obj)
        (idEtaleChart B S hS T) ≅
      (DerivedCategory.homologyFunctor
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules n).obj K.obj :=
  letI := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (representedSpace T).1 (representedSpace T).2)
  restrictToChartSchemeMapIso B S hS (isAlgebraicSpace_yoneda B S hS T)
      (homologyRepresentedDualityEquivalenceIso T K n ≪≫
        (representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
          B S hS T).app _)
      (idEtaleChart B S hS T) ≪≫
    restrictToChartSchemeRepresentedAssociatedModuleIso B S hS T _ (K.property n)

/-- **The equivalence of Stacks 071Q carries the structure sheaf to the structure sheaf.** -/
def representedDualityEquivalenceDerivedStructureSheafIso :
    (representedDualityQuasicoherentDerivedEquivalence B S hS T).functor.obj
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T)) ≅
      derivedStructureSheaf B S hS (schemeSpace T).1 (schemeSpace T).2 :=
  ObjectProperty.isoMk _
    (StacksDraft.DerivedModel.mapDerivedCategorySingleObjIso
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS T)
      (representedZariskiDerivedPullbackIso B S hS T)
      (StacksDraft.DerivedModel.grothendieckModelEquivInverseSingleIso _)
      ((representedZariskiModulePullbackAssociatedModuleIsoRepresentedZariskiModuleAdjunction
          B S hS T).app _ ≪≫
        representedAssociatedModuleObjUnitIso B S hS T (isAlgebraicSpace_yoneda B S hS T)))

end Homology

section Represented

variable (hZ : B.Contains (⊤_ Scheme.{u})) {V T : BigFppfOver B S hS} (φ : V ⟶ T)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map φ)]
  (hfp : IsFinitePresentation B S hS (schemeSpaceMap φ).hom)

/-- **Stacks 0E6E at the structure sheaf.** For a morphism `φ : V ⟶ T` of the big fppf site with
`T` affine and underlying morphism of schemes `q` proper, the relative dualizing complex
`a(𝒪_T)` of the represented morphism of algebraic spaces is the image, under the equivalence of
Stacks 071Q, of the relative dualizing complex `ω^•_{V_0/T_0} = q^×(𝒪_{T_0})` of `q`. -/
def affineRelativeDualizingComplexRepresentedIso :
    affineRelativeDualizingComplex hZ (schemeSpaceMap φ) hfp
        (isAffineSpace_yoneda B S hS T inferInstance) ≅
      (representedDualityQuasicoherentDerivedEquivalence B S hS V).functor.obj
        (C1590Private.relativeDualizingComplex ((BigFppfOver.toScheme B S hS).map φ)) :=
  (quasicoherentDerivedRightAdjoint hZ (schemeSpaceMap φ)
      (isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS (schemeSpaceMap φ).hom
        (isAffineSpace_yoneda B S hS T inferInstance) hfp.2.1)
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS hZ
        (schemeSpaceMap φ).hom (schemeSpace V).2 (isAffineSpace_yoneda B S hS T inferInstance)
        hfp.2.2)
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ
        (isAffineSpace_yoneda B S hS T inferInstance))).mapIso
      (representedDualityEquivalenceDerivedStructureSheafIso T).symm ≪≫
    ((representedRightAdjointIso hZ φ
      (isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS (schemeSpaceMap φ).hom
        (isAffineSpace_yoneda B S hS T inferInstance) hfp.2.1)
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS hZ
        (schemeSpaceMap φ).hom (schemeSpace V).2 (isAffineSpace_yoneda B S hS T inferInstance)
        hfp.2.2)
      (isAffineSpace_yoneda B S hS T inferInstance).isQuasiCompactSpace
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ
        (isAffineSpace_yoneda B S hS T inferInstance))).app
      (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
        (representedSchemeRepresentedZariskiRingedToposHom B S hS T))).symm

/-- **The relative dualizing complex of the represented morphism has the amplitude of `ω^•` of
the scheme morphism**: if `ω^•_{V_0/T_0}` has no cohomology above degree `d`, neither has
`a(𝒪_T)`. -/
theorem isLE_affineRelativeDualizingComplex_of_isLE (d : ℤ)
    (hd : (C1590Private.relativeDualizingComplex ((BigFppfOver.toScheme B S hS).map φ)).obj.IsLE
      d) :
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS (schemeSpace V).1 (schemeSpace V).2)
    (affineRelativeDualizingComplex hZ (schemeSpaceMap φ) hfp
      (isAffineSpace_yoneda B S hS T inferInstance)).obj.IsLE d := by
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (schemeSpace V).1 (schemeSpace V).2)
  let := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (representedSpace V).1 (representedSpace V).2)
  have := isLE_representedDualityEquivalence_functor_obj V _ d hd
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (X := ((representedDualityQuasicoherentDerivedEquivalence B S hS V).functor.obj
      (C1590Private.relativeDualizingComplex ((BigFppfOver.toScheme B S hS).map φ))).obj)
    ((ObjectProperty.ι _).mapIso (affineRelativeDualizingComplexRepresentedIso hZ φ hfp)).symm d

/-- **The relative dualizing sheaf of the represented morphism, read on the scheme, is the
relative dualizing sheaf of the scheme morphism**: the restriction of `ω_{V/T} = H^{-1}(a(𝒪_T))`
to the identity chart of `V` is `ω_{V_0/T_0} = H^{-1}(ω^•_{V_0/T_0})`. -/
def restrictToChartSchemeAffineRelativeDualizingSheafIso :
    restrictToChartScheme B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
        (affineRelativeDualizingSheaf hZ (schemeSpaceMap φ) hfp
          (isAffineSpace_yoneda B S hS T inferInstance))
        (idEtaleChart B S hS V) ≅
      (C1590Private.relativeDualizingSheaf ((BigFppfOver.toScheme B S hS).map φ) :
        ((BigFppfOver.toScheme B S hS).obj V).Modules) :=
  letI := HasDerivedCategory.standard
    (Modules.{u, u} B S hS (representedSpace V).1 (representedSpace V).2)
  restrictToChartSchemeMapIso B S hS (isAlgebraicSpace_yoneda B S hS V)
      ((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS (representedSpace V).1 (representedSpace V).2) (-1)).mapIso
        ((ObjectProperty.ι _).mapIso (affineRelativeDualizingComplexRepresentedIso hZ φ hfp)))
      (idEtaleChart B S hS V) ≪≫
    restrictToChartSchemeHomologyRepresentedDualityEquivalenceIso V _ (-1)

end Represented

end AlgebraicGeometry.Space

end
