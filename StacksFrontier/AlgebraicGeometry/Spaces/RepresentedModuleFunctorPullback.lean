module

public import StacksFrontier.AlgebraicGeometry.Modules.AffinePullbackCentral
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChangeEquivalence

/-!
# Inverse images of quasi-coherent modules on represented algebraic spaces

For an object `U` of the big fppf site, quasi-coherent modules on the scheme underlying `U` and on
the algebraic space `h_U` correspond
(`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`). This file shows that the
correspondence intertwines the inverse images along a morphism `g : U' ⟶ U`, as an isomorphism of
functors.

## Main definitions

* `AlgebraicGeometry.Space.representedModuleFunctor`: the comparison `𝓕 ↦ 𝓕^a` from
  quasi-coherent Zariski modules on `U` to modules on `h_U`.
* `AlgebraicGeometry.Space.representedModuleFunctorPullbackIso`: `g^*(𝓕^a) ≅ (g^*𝓕)^a`,
  naturally in `𝓕`.
* `AlgebraicGeometry.Space.representedModuleFunctorFullyFaithful`: the comparison is fully
  faithful.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison `𝓕 ↦ 𝓕^a` from quasi-coherent Zariski modules on the scheme underlying `U`
to modules on the algebraic space `h_U`. -/
noncomputable abbrev representedModuleFunctor (U : BigFppfOver B S hS) :
    (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory ⥤
      Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2 :=
  ObjectProperty.ι _ ⋙
    _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
    (representedSmallEtaleModuleEquivalence B S hS U).functor

/-- The comparison intertwines inverse images: `g^*(𝓕^a) ≅ (g^*𝓕)^a`, naturally in the
quasi-coherent module `𝓕`. -/
noncomputable def representedModuleFunctorPullbackIso {U' U : BigFppfOver B S hS} (g : U' ⟶ U) :
    representedModuleFunctor B S hS U ⋙ modulePullback B S hS (schemeSpaceMap g) ≅
      Stacks.Modules.pullbackQcoh ((BigFppfOver.toScheme B S hS).map g) ⋙
        representedModuleFunctor B S hS U' :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (representedSmallEtaleModuleEquivalencePullbackIso B S hS g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
      (associatedBigEtaleSite B) g.left).symm _ ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm

/-- The comparison is fully faithful. -/
noncomputable def representedModuleFunctorFullyFaithful (U : BigFppfOver B S hS) :
    (representedModuleFunctor B S hS U).FullyFaithful :=
  ((representedQuasicoherentSchemeEquivalence B S hS U).fullyFaithfulFunctor.comp
    (ObjectProperty.fullyFaithfulι _))

/-- Every quasi-coherent module on `h_U` is in the essential image of the comparison. -/
theorem exists_representedModuleFunctor_iso (U : BigFppfOver B S hS)
    (M : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2) (hM : M.IsQuasicoherentOnSite) :
    ∃ N, Nonempty ((representedModuleFunctor B S hS U).obj N ≅ M) :=
  ⟨(representedQuasicoherentSchemeEquivalence B S hS U).inverse.obj ⟨M, hM⟩,
    ⟨(ObjectProperty.ι _).mapIso
      ((representedQuasicoherentSchemeEquivalence B S hS U).counitIso.app ⟨M, hM⟩)⟩⟩

/-- The inverse image of the comparison of a quasi-coherent module, along a morphism of affine
schemes of the site, has central natural endomorphisms. -/
theorem natEndCentral_representedModuleFunctor_comp_modulePullback {U' U : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] (g : U' ⟶ U) :
    (representedModuleFunctor B S hS U ⋙
      modulePullback B S hS (schemeSpaceMap g)).NatEndCentral := by
  refine Functor.NatEndCentral.of_iso (representedModuleFunctorPullbackIso B S hS g) ?_
  refine Functor.NatEndCentral.comp (representedModuleFunctorFullyFaithful B S hS U') ?_
  exact Functor.NatEndCentral.of_comp_faithful (d := ObjectProperty.ι _)
    (Scheme.Modules.natEndCentral_pullback_of_isAffine ((BigFppfOver.toScheme B S hS).map g))

/-- The inverse image along a morphism of affine represented algebraic spaces has central
natural endomorphisms on quasi-coherent modules: every natural endomorphism of `g^*` commutes
with every morphism `g^*M ⟶ g^*N`. -/
theorem natEndCentral_modulePullback_schemeSpaceMap {U' U : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] (g : U' ⟶ U) :
    ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS U)).ι ⋙
        modulePullback B S hS (schemeSpaceMap g)).NatEndCentral := by
  let P := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (representedStructureRingSheaf B S hS U)
  let e : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory ⥤ P.FullSubcategory :=
    (representedQuasicoherentSchemeEquivalence B S hS U).functor
  have : e.EssSurj := inferInstanceAs
    (representedQuasicoherentSchemeEquivalence B S hS U).functor.EssSurj
  exact Functor.NatEndCentral.of_comp (e := e)
    (natEndCentral_representedModuleFunctor_comp_modulePullback B S hS g)

end AlgebraicGeometry.Space

end
