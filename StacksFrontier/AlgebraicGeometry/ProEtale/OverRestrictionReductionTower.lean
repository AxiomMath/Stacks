module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstantComplexAdicTower
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedReductionTower
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ReductionTowerSlice

/-!
# Towers of reductions on a slice of the pro-étale site, read over the coefficient ring sheaf

Let `X` be a scheme, `Λ` a ring, `I ⊆ Λ` an ideal and `V` an object of `X_proét`. An object `K`
of `D(X_proét, Λ)` is a complex of sheaves of modules over the constant coefficient ring sheaf
`\underline{Λ}`; through `AlgebraicGeometry.ProEtale.derivedModuleEquiv` it is a complex `K'` of
sheaves of `Λ`-modules. This file compares two ways of restricting the towers attached to `K`
and to a complex `N` of `Λ`-modules to `V`:

* on the slice site `X_proét/V`, with values in sheaves of `Λ`-modules: the tower of derived
  reductions of `K'|_V` and the tower `n ↦ \underline{N/IⁿN}` of constant complexes;
* through `AlgebraicGeometry.ProEtale.overRestrictionDerived`, with values in sheaves of modules
  over `\underline{Λ}|_V`: the towers `n ↦ (K' ⊗_Λ^L \underline{Λ/Iⁿ})|_V` and
  `n ↦ \underline{N/IⁿN}|_V`.

An isomorphism of towers of the first kind gives one of the second kind
(`AlgebraicGeometry.ProEtale.nonempty_reductionTower_iso_of_overPullback_iso`), which is the form
consumed by `AlgebraicGeometry.ProEtale.nonempty_overRestrictionDerived_iso_of_reductionTower_iso`
in the proof of Stacks 09C6.

The comparison is assembled from three identifications, each compatible with the transition
maps: restriction to `V` commutes with the identification of sheaves of `Λ`-modules with
sheaves of `\underline{Λ}`-modules
(`AlgebraicGeometry.ProEtale.constantCoefficientModuleEquivOverIso`); it commutes with the
derived reductions of a K-flat complex
(`Stacks.ModuleSheaf.derivedReductionTowerOverPullbackIso`); and it carries constant sheaves to
constant sheaves.

## Main definitions

* `AlgebraicGeometry.ProEtale.constantAdicQuotientFunctorTowerOverIso`: the tower of functors
  `M ↦ \underline{M/IⁿM}` on `X_proét/V`, read over `\underline{Λ}|_V`, is the tower on
  `X_proét` read over `\underline{Λ}` and restricted to `V`.

## Main results

* `AlgebraicGeometry.ProEtale.nonempty_reductionTower_iso_of_overPullback_iso`: the transport of
  an isomorphism of towers from the slice site to `overRestrictionDerived`.

## References

* [Stacks Project, Tag 09C6](https://stacks.math.columbia.edu/tag/09C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.KFlatBifunctor
  Stacks.DerivedCategoryComparisons

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Sheaf.symmetricCategory Stacks.ModuleSheaf.derivedMonoidal
  CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable (X : Scheme.{u}) (Λ : Type (max (u + 1) w)) [CommRing Λ] (I : Ideal Λ)

/-- **The constant sheaves of the adic quotients, restricted to an object of `X_proét`.** The tower
of functors `M ↦ \underline{M/IⁿM}` on the slice site `X_proét/V`, read over `\underline{Λ}|_V`,
is the tower `M ↦ \underline{M/IⁿM}` on `X_proét`, read over `\underline{Λ}` and restricted to
`V`: the constant sheaf commutes with restriction, and so does reading sheaves of `Λ`-modules
over `\underline{Λ}`. -/
def constantAdicQuotientFunctorTowerOverIso (V : X.ProEt) :
    Stacks.ModuleSheaf.constantAdicQuotientFunctorTower ((Scheme.ProEt.topology X).over V) Λ I ⋙
        (Functor.whiskeringRight _ _ _).obj
          (overCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ V).functor ≅
      adicQuotientConstantTower.{u, w} X Λ I ⋙
        (Functor.whiskeringRight _ _ _).obj (SheafOfModules.overFunctor.{max (u + 1) w}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O)) V) :=
  let J := Scheme.ProEt.topology X
  let A := ModuleCat.{max (u + 1) w} Λ
  let EV := (overCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ V).functor
  let O := SheafOfModules.overFunctor.{max (u + 1) w}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O)) V
  let c : constantSheaf (J.over V) A ⋙ EV ≅
      (constantSheaf J A ⋙ moduleSheafOverConstantCoefficientsFunctor.{u, max (u + 1) w, w} X Λ) ⋙
        O :=
    Functor.isoWhiskerRight (Stacks.ConstantSheaf.overPullbackConstantSheafIso J A V) EV ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (constantSheaf J A)
        ((constantCoefficientModuleEquivOverIso.{u, max (u + 1) w, w} X Λ V).symm ≪≫
          Functor.isoWhiskerRight (constantCoefficientModuleEquivFunctorIso.{u, max (u + 1) w, w}
            X Λ) O) ≪≫
      (Functor.associator _ _ _).symm
  Functor.isoWhiskerLeft (adicQuotientModuleFunctor.{max (u + 1) w, max (u + 1) w} Λ I).flip
    ((Functor.whiskeringRight _ _ _).mapIso c)

/-- **Transport of an isomorphism of towers from a slice site to the coefficient modules.** Let
`K` be an object of `D(X_proét, Λ)`, `P` a K-flat complex of sheaves of `Λ`-modules representing
`K' = (derivedModuleEquiv X Λ).inverse.obj K`, `V` an object of `X_proét` and `M` a complex of
`Λ^∧`-modules, with underlying complex `N` of `Λ`-modules. An isomorphism of towers on the slice
site `X_proét/V` between the derived reductions of `P|_V` and the constant complexes
`\underline{N/IⁿN}` gives an isomorphism of towers between `\underline{N/IⁿN}|_V` and
`(K' ⊗_Λ^L \underline{Λ/Iⁿ})|_V`, read over `\underline{Λ}|_V`. -/
theorem nonempty_reductionTower_iso_of_overPullback_iso
    (K : DerivedSheaves.{u, max (u + 1) w, w} X Λ)
    {P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) ℤ}
    (eP : DerivedCategory.Q.obj P ≅ (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K)
    (hP : KFlat (MonoidalCategory.curriedTensor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) P)
    (V : X.ProEt) (M : CochainComplex (ModuleCat.{max (u + 1) w} (AdicCompletion I Λ)) ℤ)
    (φ : Stacks.ModuleSheaf.derivedReductionTower ((Scheme.ProEt.topology X).over V) Λ I
        (DerivedCategory.Q.obj ((((Scheme.ProEt.topology X).overPullback
          (ModuleCat.{max (u + 1) w} Λ) V).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≅
      Stacks.ModuleSheaf.constantAdicQuotientComplexTower ((Scheme.ProEt.topology X).over V) Λ I
        (((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).mapHomologicalComplex
          _).obj M) ⋙ DerivedCategory.Q) :
    Nonempty (adicQuotientConstantComplexTower.{u, w} X Λ I
        (((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).mapHomologicalComplex
          _).obj M) ⋙ DerivedCategory.Q ⋙ overRestrictionDerived.{u, max (u + 1) w, w} X Λ V ≅
      derivedReductionTower.{u, w} X Λ I
          ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K) ⋙
        (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).functor ⋙
          overRestrictionDerived.{u, max (u + 1) w, w} X Λ V) := by
  let J := Scheme.ProEt.topology X
  let A := ModuleCat.{max (u + 1) w} Λ
  let N := ((restrictToCoefficients.{max (u + 1) w, max (u + 1) w} Λ I).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj M
  let E := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ
  let EV := overCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ V
  let O := SheafOfModules.overFunctor.{max (u + 1) w}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ).O)) V
  let jV := J.overPullback A V
  let : PreservesFiniteLimits O := SheafOfModules.preservesFiniteLimits_pushforward _
  let : PreservesFiniteColimits O :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits.{u + 1, u,
      max (u + 1) w} V
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : EV.functor.Additive := Functor.additive_of_preserves_binary_products _
  let := Stacks.ModuleSheaf.preservesFiniteLimits_overPullback J Λ V
  let := Stacks.ModuleSheaf.preservesFiniteColimits_overPullback J Λ V
  let : jV.Additive := ⟨fun {_ _ _ _} => rfl⟩
  let r₁ : derivedReductionTower.{u, w} X Λ I
        ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K) ⋙
        E.functor.mapDerivedCategory ⋙ O.mapDerivedCategory ≅
      derivedReductionTower.{u, w} X Λ I (DerivedCategory.Q.obj P) ⋙
        E.functor.mapDerivedCategory ⋙ O.mapDerivedCategory :=
    Functor.isoWhiskerRight ((Stacks.ModuleSheaf.derivedReductionTowerFunctor J Λ I).mapIso
      eP.symm) _
  let r₂ : E.functor.mapDerivedCategory ⋙ O.mapDerivedCategory ≅
      jV.mapDerivedCategory ⋙ EV.functor.mapDerivedCategory :=
    (mapDerivedCategoryCompIso E.functor O).symm ≪≫
      mapDerivedCategoryIsoOfNatIso _ _
        (constantCoefficientModuleEquivOverIso.{u, max (u + 1) w, w} X Λ V) ≪≫
      mapDerivedCategoryCompIso jV EV.functor
  let r₃ := Stacks.ModuleSheaf.derivedReductionTowerOverPullbackIso J Λ V I hP
  let r₆ := Functor.mapHomologicalComplexDiagramCompIso
    (constantAdicQuotientFunctorTowerOverIso X Λ I V) N
  let TV := Stacks.ModuleSheaf.constantAdicQuotientComplexTower (J.over V) Λ I N
  let TX := adicQuotientConstantComplexTower.{u, w} X Λ I N
  let DV := Stacks.ModuleSheaf.derivedReductionTower (J.over V) Λ I
    (DerivedCategory.Q.obj ((jV.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
  let DX := derivedReductionTower.{u, w} X Λ I (DerivedCategory.Q.obj P)
  let s₁ : TX ⋙ DerivedCategory.Q ⋙ O.mapDerivedCategory ≅
      TX ⋙ O.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft TX O.mapDerivedCategoryFactors
  let s₂ : TX ⋙ O.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
      TV ⋙ EV.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight r₆.symm DerivedCategory.Q
  let s₃ : TV ⋙ EV.functor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
      (TV ⋙ DerivedCategory.Q) ⋙ EV.functor.mapDerivedCategory :=
    Functor.isoWhiskerLeft TV EV.functor.mapDerivedCategoryFactors.symm
  let s₄ : (TV ⋙ DerivedCategory.Q) ⋙ EV.functor.mapDerivedCategory ≅
      DV ⋙ EV.functor.mapDerivedCategory :=
    Functor.isoWhiskerRight φ.symm EV.functor.mapDerivedCategory
  let s₅ : DV ⋙ EV.functor.mapDerivedCategory ≅
      (DX ⋙ jV.mapDerivedCategory) ⋙ EV.functor.mapDerivedCategory :=
    Functor.isoWhiskerRight r₃.symm EV.functor.mapDerivedCategory
  let s₆ : (DX ⋙ jV.mapDerivedCategory) ⋙ EV.functor.mapDerivedCategory ≅
      DX ⋙ E.functor.mapDerivedCategory ⋙ O.mapDerivedCategory :=
    Functor.isoWhiskerLeft DX r₂.symm
  exact ⟨s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄ ≪≫ s₅ ≪≫ s₆ ≪≫ r₁.symm⟩

end AlgebraicGeometry.ProEtale

end
