module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.UnitAndCounitIsomorphisms

/-!
# Restriction to the small Zariski site is conservative on the quasi-coherent modules of a big site

Let `S` be a scheme of the big fppf site `B` and `τ` one of the five topologies.  The
associated-module functor `𝓕 ↦ 𝓕^a` of Definition 03DU is the pullback along the morphism of
ringed sites `id_{τ,Zar} : ((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)` (Remark 03FH), and its right adjoint
`AlgebraicGeometry.BigFppfOver.baseRestrictModule` is restriction along the inclusion of the
small Zariski site of `S`.  This file proves that **that restriction reflects isomorphisms
between modules quasi-coherent on `(Sch/S)_τ`**, with no hypothesis, and reads the criterion off
the components:

> a morphism of modules quasi-coherent on `(Sch/S)_τ` is invertible as soon as it is invertible
> on sections over the objects `U^{big}` attached to the opens `U` of `S`.

Nothing of Descent, Proposition 03DX has to be re-proved for it.  Both inputs are
theorems of this library, and the argument joining them is formal:

* the unit `𝓕 ⟶ (𝓕^a)|_{S_Zar}` is an isomorphism at every quasi-coherent `𝒪_S`-module,
  `AlgebraicGeometry.BigFppfOver.isIso_baseUnit_app`, so the counit of the adjunction is
  invertible at every `𝓕^a` by the left triangle identity
  (`CategoryTheory.Adjunction.isIso_counit_app_obj_of_isIso_unit_app`);
* every module quasi-coherent on `(Sch/S)_τ` *is* an `𝓕^a` up to isomorphism, which is the
  essential-surjectivity half of Descent, Proposition 03DX (1),
  `AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`; and the objects at
  which a counit is invertible are closed under isomorphism
  (`CategoryTheory.Adjunction.isClosedUnderIsomorphisms_counitIsIso`).

So the quasi-coherent modules of `(Sch/S)_τ` are contained in
`CategoryTheory.Adjunction.counitIsIso` of the associated-module adjunction, and a right adjoint
is **fully faithful** on that subcategory
(`CategoryTheory.Adjunction.fullyFaithfulιCompRightAdjointOfLE`); a fully faithful functor
reflects isomorphisms.

## Why the component form is the usable one

A consumer of this file never holds the hypothesis in the shape "the restriction of `φ` to the
small Zariski site is invertible": what it holds is that the components of `φ` are invertible at
certain objects of the big site.  `AlgebraicGeometry.BigFppfOver.baseRestrictModule` is a
`CategoryTheory.SheafOfModules.pushforward` along `AlgebraicGeometry.BigFppfOver.opensToBig`, so
its components are the components of `φ` at the images of that functor, up to restriction of
scalars — which reflects invertibility.  That is
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_pushforward_map`, and it turns the
hypothesis into one about the opens of `S` alone.

## Main results

* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_le_counitIsIso`: the modules
  quasi-coherent on `(Sch/S)_τ` are objects at which the counit of the associated-module
  adjunction is invertible — Descent, Proposition 03DX (1) read on the counit.
* `AlgebraicGeometry.BigFppfOver.fullyFaithfulιCompBaseRestrictModule`: restriction to the small
  Zariski site is fully faithful on them.
* `AlgebraicGeometry.BigFppfOver.isIso_of_isIso_baseRestrictModule_map`: **it reflects
  isomorphisms** between them.
* `AlgebraicGeometry.BigFppfOver.isIso_of_isIso_val_app_opensToBig`: the same criterion read on
  components — invertibility over the opens of `S` suffices.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent, Proposition 03DX (1) read on the counit**: at a module quasi-coherent on the big
`τ`-site of `S` the counit `(𝒢|_{S_Zar})^a ⟶ 𝒢` of the associated-module adjunction is
invertible, with no hypothesis.

Such a `𝒢` is `𝓕^a` for a quasi-coherent `𝒪_S`-module `𝓕`
(`AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`); there the counit
is invertible because the unit at `𝓕` is
(`AlgebraicGeometry.BigFppfOver.isIso_baseUnit_app`) and the left triangle identity exhibits the
one as an inverse of the image of the other; and the objects at which a counit is invertible are
closed under isomorphism. -/
public theorem isQuasicoherentOnSite_le_counitIsIso (τ : SiteKind) :
    SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf B S hS τ) ≤
      (baseAssociatedModuleAdjunction B S hS τ).counitIsIso := by
  let := Adjunction.isClosedUnderIsomorphisms_counitIsIso
    (baseAssociatedModuleAdjunction B S hS τ)
  intro G hG
  obtain ⟨𝓕, ⟨i⟩⟩ := baseQuasicoherentIsEssImageAssociatedModule B S hS τ G hG
  have : 𝓕.obj.IsQuasicoherent := 𝓕.property
  exact ObjectProperty.prop_of_iso _ i
    ((baseAssociatedModuleAdjunction B S hS τ).isIso_counit_app_obj_of_isIso_unit_app 𝓕.obj
      (isIso_baseUnit_app B S hS τ 𝓕.obj))

/-- **Restriction to the small Zariski site of `S` is fully faithful on the modules
quasi-coherent on the big `τ`-site**, with no hypothesis: a right adjoint is fully faithful on
the objects at which the counit is invertible, and
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_le_counitIsIso` says the quasi-coherent
modules are among them. -/
public noncomputable def fullyFaithfulιCompBaseRestrictModule (τ : SiteKind) :
    ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (FibredSite.baseRingStructureSheaf B S hS τ)).ι ⋙
        baseRestrictModule B S hS τ).FullyFaithful :=
  (baseAssociatedModuleAdjunction B S hS τ).fullyFaithfulιCompRightAdjointOfLE
    (isQuasicoherentOnSite_le_counitIsIso B S hS τ)

/-- **Restriction to the small Zariski site of `S` reflects isomorphisms between modules
quasi-coherent on the big `τ`-site**, with no hypothesis: it is fully faithful there, and a fully
faithful functor reflects isomorphisms. -/
public theorem isIso_of_isIso_baseRestrictModule_map (τ : SiteKind)
    {M N : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N)
    (h : IsIso ((baseRestrictModule B S hS τ).map φ)) : IsIso φ := by
  let ψ := ObjectProperty.homMk (X := ⟨M, hM⟩) (Y := ⟨N, hN⟩) φ
  have : IsIso (((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.baseRingStructureSheaf B S hS τ)).ι ⋙ baseRestrictModule B S hS τ).map ψ) := h
  exact (ObjectProperty.isIso_hom_iff _).2
    ((fullyFaithfulιCompBaseRestrictModule B S hS τ).isIso_of_isIso_map ψ)

/-- The restriction of a morphism to the small Zariski site of `S` is invertible as soon as the
morphism is invertible on sections over the objects of the big site attached to the opens of `S`.

`AlgebraicGeometry.BigFppfOver.baseRestrictModule` is a
`CategoryTheory.SheafOfModules.pushforward` along `AlgebraicGeometry.BigFppfOver.opensToBig`, so
each of its components is a restriction of scalars of such a component, and restriction of
scalars reflects invertibility. -/
public theorem isIso_baseRestrictModule_map_of_isIso_val_app (τ : SiteKind)
    {M N : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)} (φ : M ⟶ N)
    (h : ∀ U : S.Opens, IsIso (φ.val.app (op ((opensToBig B S hS).obj U)))) :
    IsIso ((baseRestrictModule B S hS τ).map φ) :=
  Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app _ fun U =>
    Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_pushforward_map
      (baseStructureMap B S hS τ) φ U (h U.unop)

/-- **A morphism of modules quasi-coherent on the big `τ`-site of `S` is invertible as soon as it
is invertible on sections over the opens of `S`**, with no hypothesis.

This is the form in which Descent, Proposition 03DX (1) is used to compare a quasi-coherent
module on a big site with its restriction to the small sites: the opens of `S` are a vanishingly
small part of the objects of `(Sch/S)_τ`, and the components there already determine the
morphism, because both modules are pulled back from the small Zariski site. -/
public theorem isIso_of_isIso_val_app_opensToBig (τ : SiteKind)
    {M N : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N)
    (h : ∀ U : S.Opens, IsIso (φ.val.app (op ((opensToBig B S hS).obj U)))) :
    IsIso φ :=
  isIso_of_isIso_baseRestrictModule_map B S hS τ hM hN φ
    (isIso_baseRestrictModule_map_of_isIso_val_app B S hS τ φ h)

end AlgebraicGeometry.BigFppfOver

end
