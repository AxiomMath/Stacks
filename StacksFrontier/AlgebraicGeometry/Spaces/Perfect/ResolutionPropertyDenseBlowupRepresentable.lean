module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteTypeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRepresentable

/-!
# The resolution property of a scheme is that of the algebraic space it represents

Let `U` be an object of the big fppf site over a scheme `S`, with underlying scheme `T`.  The
algebraic space `yoneda.obj U` has the resolution property of Stacks 0GUS exactly when the
scheme `T` has the resolution property of Stacks 0F86.  The implication from the space to the
scheme is
`AlgebraicGeometry.Space.hasResolutionProperty_scheme_of_hasResolutionProperty_yoneda`; this
file proves the implication from the scheme to the space, so the two predicates now agree.

The two statements are about different sites — the small étale site of the space and the Zariski
site of the scheme — and the passage is in two steps, each the mirror image of a step of the
converse.

* A finite-type quasi-coherent `𝒪`-module on the small étale site of `yoneda.obj U` is read as a
  quasi-coherent `𝒪_T`-module by the comparison of Descent, Proposition 03DX (2) at
  `τ = étale`, proved for a representable space as
  `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`, and it is of *finite
  type* in Mathlib's sense there.  That is the content of
  `AlgebraicGeometry.Space.isFiniteType_of_isFiniteTypeOnSite_`
  `representedQuasicoherentSchemeEquivalence` below: finite type on a site is reflected by the
  equivalence of ringed sites
  (`Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_reindex`, the clause 03DL (5)
  half of Stacks 03DM in its reflecting direction) and then by the associated-module functor of
  the small étale site of `T`
  (`AlgebraicGeometry.SmallEtale.isFiniteType_of_isFiniteTypeOnSite_associatedModule`, the
  converse of Stacks 08HD for a quasi-coherent module).  So the resolution property of `T`
  applies and produces a finite locally free quotient on the Zariski site of `T`.
* That quotient has to go back up.  Its source is carried to a module which is finite locally
  free on the site by the *forward* half of Stacks 05VG for the clause 03DL (2),
  `AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule`, and then by
  `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff`, the
  clause 03DM comparison of the two small étale sites.  The *morphism* goes up through the two
  left adjoints, which preserve epimorphisms
  (`CategoryTheory.Functor.preservesEpimorphisms_of_adjunction` at
  `AlgebraicGeometry.SmallEtale.associatedModuleAdjunction` and at the adjunction of the
  equivalence `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`), and lands on
  the given module up to the counit isomorphism of the comparison equivalence.

## Main results

* `AlgebraicGeometry.Space.isFiniteType_of_isFiniteTypeOnSite_`
  `representedQuasicoherentSchemeEquivalence`: **the finite-type reflection**, the mirror of
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence`.
* `AlgebraicGeometry.Space.hasResolutionProperty_yoneda_of_hasResolutionProperty_scheme`:
  **the algebraic space `yoneda.obj U` has the resolution property as soon as the scheme
  underlying `U` does.**
* `AlgebraicGeometry.Space.hasResolutionProperty_representedAlgebraicSpace_of_`
  `hasResolutionProperty`: the same, stated for
  `AlgebraicGeometry.Space.representedAlgebraicSpace`, the algebraic space of the big fppf site
  read as an object of `AlgebraicGeometry.AlgebraicSpaces`.

## Implementation notes

Nothing here carries a `stacks` attribute, for the reason given in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ResolutionPropertyRepresentable.lean`: the change
of site between Stacks 0GUS for a representable algebraic space and Stacks 0F86 for its scheme
is a clause of neither tag.

The module universe is pinned to the universe of the schemes, as it is throughout
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedQuasicoherent.lean`: the conclusion is the
resolution property of the space at that one module universe, and the hypothesis is the scheme
statement in full, the latter having no free module universe.

Two epimorphisms are produced from the preservation fields of
`CategoryTheory.Functor.PreservesEpimorphisms` by name rather than by instance search.  Searching
for `CategoryTheory.Epi` of a functor image here reaches
`CategoryTheory.Functor.PreservesEpimorphisms` through the homology-preservation instance of an
abelian category, whose universe arguments are free, and the search ends in an unsolved universe
constraint.  Likewise `CategoryTheory.Iso.isIso_hom` is applied by name.

## References

* [Stacks Project, Tag 0GUS](https://stacks.math.columbia.edu/tag/0GUS)
* [Stacks Project, Tag 0F86](https://stacks.math.columbia.edu/tag/0F86)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **Finite type is reflected by the comparison of a representable algebraic space with its
scheme.**  A quasi-coherent module on the scheme underlying `U` whose reading on the small étale
site of `yoneda.obj U` is of finite type there is of finite type.

This is the mirror of
`AlgebraicGeometry.Space.isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence`, proved
from the same two steps run backwards: the reflecting half of clause 03DL (5) along an
equivalence of ringed sites
(`Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_reindex`) and the converse of
Stacks 08HD for a quasi-coherent module
(`AlgebraicGeometry.SmallEtale.isFiniteType_of_isFiniteTypeOnSite_associatedModule`). -/
theorem isFiniteType_of_isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence
    (M : SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf)
    (hM : SheafOfModules.IsQuasicoherent M)
    (hft : SheafOfModules.IsFiniteTypeOnSite
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj ⟨M, hM⟩).obj) :
    SheafOfModules.IsFiniteType M := by
  have := hM
  exact AlgebraicGeometry.SmallEtale.isFiniteType_of_isFiniteTypeOnSite_associatedModule
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property M
    (Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_reindex
      (J' := SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeStructureSheaf B S hS U) _ hft)

/-- **The algebraic space `yoneda.obj U` has the resolution property as soon as the scheme
underlying `U` does.**

A finite-type quasi-coherent `𝒪`-module on the small étale site of `yoneda.obj U` is read as a
quasi-coherent `𝒪_T`-module by the comparison of Descent, Proposition 03DX (2) at `τ = étale`,
and is of finite type there by
`AlgebraicGeometry.Space.isFiniteType_of_isFiniteTypeOnSite_`
`representedQuasicoherentSchemeEquivalence`; the resolution property of `T` produces a finite
locally free quotient on the Zariski site of `T`; and that quotient is carried up by the forward
half of Stacks 05VG for clause 03DL (2) together with the comparison of the two small étale
sites, both of whose functors are left adjoints and so preserve the epimorphism. -/
theorem hasResolutionProperty_yoneda_of_hasResolutionProperty_scheme
    (h : _root_.AlgebraicGeometry.HasResolutionProperty
      ((BigFppfOver.toScheme B S hS).obj U)) :
    HasResolutionProperty.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) := by
  let A := AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property
  let e := representedQuasicoherentSchemeEquivalence B S hS U
  let G := representedSmallEtaleModuleEquivalence B S hS U
  have hpres1 : A.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property)
  have hpres2 : G.functor.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction G.toAdjunction
  constructor
  intro M hMft
  have hMft' : SheafOfModules.IsFiniteTypeOnSite M.obj := hMft
  -- The counit of the comparison equivalence, read on the underlying modules.
  have iso := (ObjectProperty.ι _).mapIso (e.counitIso.app M)
  have hft1 : SheafOfModules.IsFiniteTypeOnSite (e.functor.obj (e.inverse.obj M)).obj :=
    Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso iso.symm hMft'
  have hNft : SheafOfModules.IsFiniteType (e.inverse.obj M).obj :=
    isFiniteType_of_isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence B S hS U _
      (e.inverse.obj M).property hft1
  obtain ⟨E', hE', φ, hφ⟩ := h.exists_finiteLocallyFree_quotient (e.inverse.obj M).obj
  have := hφ
  refine ⟨G.functor.obj (A.obj E'), ?_, G.functor.map (A.map φ) ≫ iso.hom, ?_⟩
  · exact (isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff B S hS U _).mpr
      (AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property E' hE')
  · have h1 : Epi (A.map φ) := hpres1.preserves φ
    have h2 : Epi (G.functor.map (A.map φ)) := hpres2.preserves _
    have h3 : Epi iso.hom := @IsIso.epi_of_iso _ _ _ _ iso.hom (Iso.isIso_hom iso)
    exact epi_comp' h2 h3

/-- **The algebraic space of an object of the big fppf site has the resolution property as soon
as the scheme underlying that object does**, stated at
`AlgebraicGeometry.Space.representedAlgebraicSpace`, the form in which the algebraic space
appears as an object of `AlgebraicGeometry.AlgebraicSpaces`. -/
theorem hasResolutionProperty_representedAlgebraicSpace_of_hasResolutionProperty
    (h : _root_.AlgebraicGeometry.HasResolutionProperty
      ((BigFppfOver.toScheme B S hS).obj U)) :
    HasResolutionProperty.{u, u} B S hS (representedAlgebraicSpace B S hS U).1
      (representedAlgebraicSpace B S hS U).2 :=
  hasResolutionProperty_yoneda_of_hasResolutionProperty_scheme B S hS U h

end AlgebraicGeometry.Space

end
