module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeViaEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteTypeOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent

/-!
# The resolution property of a representable algebraic space is that of its scheme

Let `U` be an object of the big fppf site over a scheme `S`, with underlying scheme `T`.  If the
algebraic space `yoneda.obj U` has the resolution property of Stacks 0GUS, then the scheme `T` has
the resolution property of Stacks 0F86.  The two properties are about different sites, the small
étale site of the space and the Zariski site of the scheme.

The proof is in two steps, and the second is the one with mathematical content.

* A finite-type quasi-coherent `𝒪_T`-module is carried to a finite-type quasi-coherent
  `𝒪`-module on the small étale site of `yoneda.obj U` by the comparison of Descent,
  Proposition 03DX (2) at `τ = étale`, which for a representable space is
  `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`; the finite-type half of
  that transport is `Stacks.SheafOfModules.FiniteTypeTransport`'s clause 03DL (5), available as
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence`.  So
  the resolution property of the space applies and produces a finite locally free quotient
  *on the site*.
* That quotient comes back down to the Zariski site of `T`.  Its source is finite locally
  free on the site, hence of finite presentation on it and so quasi-coherent on it, so the
  counit of the associated-module adjunction is an isomorphism there by
  `AlgebraicGeometry.SmallEtale.isIso_counit` and exhibits the source as the associated module
  of its own Zariski restriction, which is finite locally free by the reflection half of
  Stacks 05VG for the clause 03DL (2).  The *morphism* comes down through the right adjoint:
  the unit is an isomorphism at the quasi-coherent target (Stacks 0GN7 at `τ = étale`,
  `AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent`), so the restriction of the quotient map
  is a map onto the target itself, and it is an epimorphism because the associated-module
  functor reflects epimorphisms
  (`AlgebraicGeometry.SmallEtale.reflectsEpimorphisms_associatedModule`) and carries it, by
  naturality of the counit, to the original epimorphism up to two isomorphisms.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_isFiniteLocallyFree_epi_of_isFiniteLocallyFreeOnSite_epi`:
  **a finite locally free quotient of `𝓕^a` on the small étale site of a scheme descends to a
  finite locally free quotient of `𝓕` on its Zariski site**, for `𝓕` quasi-coherent.
* `AlgebraicGeometry.Space.hasResolutionProperty_scheme_of_hasResolutionProperty_yoneda`:
  **the scheme underlying `U` has the resolution property as soon as the algebraic space
  `yoneda.obj U` does.**

## Implementation notes

`AlgebraicGeometry.Space.hasResolutionProperty_of_isAffineHom` reduces Stacks 0GUU — that the
source of an affine or quasi-affine morphism onto a quasi-compact, quasi-separated algebraic space
with the resolution property has the resolution property — to Stacks 0GUT.  Both are about the
resolution property of an algebraic space, while Stacks 0F8C is about the resolution property of
a scheme; these are two different predicates even when the space is representable, and
`AlgebraicGeometry.Space.hasResolutionProperty_scheme_of_hasResolutionProperty_yoneda` passes
from the first to the second.

The module universe of the hypothesis is the universe of the schemes, at which the representable
comparison `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence` is stated, while
`AlgebraicGeometry.Space.HasResolutionProperty` leaves it free.  The conclusion, the resolution
property of a scheme, has no free module universe.

## References

* [Stacks Project, Tag 0GUS](https://stacks.math.columbia.edu/tag/0GUS)
* [Stacks Project, Tag 0F86](https://stacks.math.columbia.edu/tag/0F86)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- **A finite locally free quotient on the small étale site descends to the Zariski site.**
Let `𝓕` be a quasi-coherent `𝒪_X`-module and let `E` be a module on the small étale site of `X`
which is finite locally free on that site and admits an epimorphism onto `𝓕^a`.  Then `𝓕` is
itself the target of an epimorphism from a finite locally free `𝒪_X`-module, namely from the
Zariski restriction of `E`.

Finite local freeness of the restriction is
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFree_restrictModule_of_isFiniteLocallyFreeOnSite`.
The map is the restriction of the given one, composed with the inverse of the unit at `𝓕`, which
is an isomorphism by Stacks 0GN7 at `τ = étale`; it is an epimorphism because `ε^*` reflects
epimorphisms and, by naturality of the counit, carries it to the given epimorphism between two
objects at which the counit is invertible. -/
theorem exists_isFiniteLocallyFree_epi_of_isFiniteLocallyFreeOnSite_epi
    (𝓕 : X.Modules) (h𝓕 : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝓕)
    (E : _root_.SheafOfModules.{u} (structureSheaf B X hX))
    (hE : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite E)
    (f : E ⟶ (associatedModule B X hX).obj 𝓕) (hf : Epi f) :
    ∃ (E' : X.Modules) (_ : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E')
      (φ : E' ⟶ 𝓕), Epi φ := by
  have := _root_.SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hE
  have hEqc : E.IsQuasicoherentOnSite := inferInstance
  have hAqc : ((associatedModule B X hX).obj 𝓕).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B X hX 𝓕 h𝓕
  have := isIso_counit B X hX E hEqc (isQuasicoherent_restrictModule B X hX E hEqc)
  have := isIso_counit B X hX ((associatedModule B X hX).obj 𝓕) hAqc
    (isQuasicoherent_restrictModule B X hX _ hAqc)
  have : IsIso ((associatedModuleAdjunction B X hX).unit.app 𝓕) :=
    unitIsoOnQuasicoherent B X hX ⟨𝓕, h𝓕⟩
  refine ⟨(restrictModule B X hX).obj E,
    isFiniteLocallyFree_restrictModule_of_isFiniteLocallyFreeOnSite B X hX E hE,
    (restrictModule B X hX).map f ≫ inv ((associatedModuleAdjunction B X hX).unit.app 𝓕), ?_⟩
  have hmid : Epi ((associatedModule B X hX).map ((restrictModule B X hX).map f)) := by
    have hfac : (associatedModule B X hX).map ((restrictModule B X hX).map f) =
        ((associatedModuleAdjunction B X hX).counit.app E ≫ f) ≫
          inv ((associatedModuleAdjunction B X hX).counit.app
            ((associatedModule B X hX).obj 𝓕)) := by
      rw [← (associatedModuleAdjunction B X hX).counit_naturality f, Category.assoc,
        IsIso.hom_inv_id, Category.comp_id]
    rw [hfac]
    exact epi_comp' (epi_comp' (IsIso.epi_of_iso _) hf) (IsIso.epi_of_iso _)
  refine (reflectsEpimorphisms_associatedModule B X hX).reflects _ ?_
  rw [Functor.map_comp]
  exact epi_comp' hmid (IsIso.epi_of_iso _)

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The scheme underlying `U` has the resolution property as soon as the algebraic space
`yoneda.obj U` does.**

A finite-type quasi-coherent `𝒪_T`-module is read on the small étale site of `yoneda.obj U` by
the comparison of Descent, Proposition 03DX (2) at `τ = étale`, staying quasi-coherent and of
finite type; the resolution property of the space produces a finite locally free quotient there;
and that quotient is carried back to the Zariski site of `T` by
`AlgebraicGeometry.SmallEtale.exists_isFiniteLocallyFree_epi_of_isFiniteLocallyFreeOnSite_epi`,
the comparison having left it a quotient of the associated module of the original. -/
theorem hasResolutionProperty_scheme_of_hasResolutionProperty_yoneda
    (h : HasResolutionProperty.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)) :
    _root_.AlgebraicGeometry.HasResolutionProperty
      ((BigFppfOver.toScheme B S hS).obj U) := by
  refine ⟨fun 𝓕 h𝓕qc h𝓕ft => ?_⟩
  obtain ⟨E, hE, f, hf⟩ :=
    @HasResolutionProperty.exists_finiteLocallyFree_quotient.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) h _
      (isFiniteTypeOnSite_representedQuasicoherentSchemeEquivalence B S hS U 𝓕 h𝓕qc h𝓕ft)
  refine
    AlgebraicGeometry.SmallEtale.exists_isFiniteLocallyFree_epi_of_isFiniteLocallyFreeOnSite_epi
      (AlgebraicGeometry.associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
      U.left.property 𝓕 h𝓕qc
      ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj E) ?_
      ((representedSmallEtaleModuleEquivalence B S hS U).functor.preimage
        (((representedSmallEtaleModuleEquivalence B S hS U).counitIso.app E).hom ≫ f)) ?_
  · exact (isFiniteLocallyFreeOnSite_representedSmallEtaleModule_iff B S hS U _).mp <|
        _root_.SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
        ((representedSmallEtaleModuleEquivalence B S hS U).counitIso.app E).symm hE
  · refine (Functor.reflectsEpimorphisms_of_faithful
      (representedSmallEtaleModuleEquivalence B S hS U).functor).reflects _ ?_
    rw [Functor.map_preimage]
    exact epi_comp' (IsIso.epi_of_iso _) hf

end AlgebraicGeometry.Space

end
