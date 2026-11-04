module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreePushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningEtaleLocalization

/-!
# Finite local freeness of a conormal module on the small étale site

Let `Z` be a closed subspace of an algebraic space `X'` over a scheme `S`.  Finite local
freeness of the conormal module `𝒞_{Z/X'}` is insensitive to étale localization: it holds
exactly when it holds for the conormal module of the inverse image of `Z` in an algebraic space
étale and surjective on points over `X'`.  For a formally unramified morphism it is likewise the
same condition on the conormal sheaf of Stacks 0607 and on the conormal module of the closed
subspace of the universal first-order thickening that the conormal sheaf is transported from.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_modulePullback_iff`: finite local freeness
  of a module on the small étale site is unchanged by the inverse image along a morphism which
  is étale and surjective on points.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalSheaf_iff`: the conormal sheaf of a
  formally unramified morphism is finite locally free exactly when the conormal module of the
  closed subspace of its universal first-order thickening is.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_conormalModule_preimage_iff`: finite local
  freeness of the conormal module of a closed subspace may be tested after an étale localization
  surjective on points.

## Implementation notes

The first statement is the clause of Stacks 03DN for finite local freeness, read along a
morphism of algebraic spaces by
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_etaleModulePullback_iff`, composed with
Equation 03LW, `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, which identifies
the inverse image of modules along an étale morphism with étale restriction.  Both the conormal
sheaf of Stacks 0607 and the identification of Stacks 060D (3) are stated in terms of the
inverse image of modules, so the first statement is what makes them usable for a locality
argument.

The second statement is the first one for the identification of the source with the smaller
space of the thickening, which is an isomorphism, hence étale and surjective on points.  The
third is the first one for the projection of the inverse image, which is étale and surjective on
points because it is a base change of the given chart, composed with Stacks 060D (3),
`AlgebraicGeometry.Space.conormalModuleEtaleLocalizationIso`.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 0607](https://stacks.math.columbia.edu/tag/0607)
* [Stacks Project, Tag 060D](https://stacks.math.columbia.edu/tag/060D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Finite local freeness and the inverse image of modules -/

/-- Finite local freeness on the site is invariant under isomorphism of modules. -/
private theorem isFiniteLocallyFreeOnSite_iff_of_iso {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X : AlgebraicSpaces B S hS} {M N : Modules.{u, u} B S hS X.1 X.2}
    (e : M ≅ N) :
    SheafOfModules.IsFiniteLocallyFreeOnSite M ↔ SheafOfModules.IsFiniteLocallyFreeOnSite N :=
  ⟨SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso e,
    SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso e.symm⟩

/-- **Finite local freeness is unchanged by the inverse image of modules along a morphism which
is étale and surjective on points.**  This is the clause of Stacks 03DN for finite local
freeness read along such a morphism, transported across Equation 03LW from étale restriction to
the inverse image of modules of Stacks 03LU. -/
public theorem isFiniteLocallyFreeOnSite_modulePullback_iff {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) (hsurj : IsSurjective B S hS f.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    SheafOfModules.IsFiniteLocallyFreeOnSite M ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite ((modulePullback B S hS f).obj M) :=
  (isFiniteLocallyFreeOnSite_etaleModulePullback_iff B S hS f hf hsurj M).trans
    (isFiniteLocallyFreeOnSite_iff_of_iso
      ((modulePullbackIsoEtaleModulePullback B S hS f hf).app M)).symm

/-! ### The conormal sheaf and the conormal module of the thickening -/

/-- The conormal sheaf of Stacks 0607 of a formally unramified morphism of algebraic spaces,
relative to a universal first-order thickening, is finite locally free exactly when the conormal
module of the smaller space of that thickening is.

The two differ by the inverse image along the identification of the source with the smaller
space of the thickening, which is an isomorphism. -/
public theorem isFiniteLocallyFreeOnSite_conormalSheaf_iff {Z X : AlgebraicSpaces B S hS}
    {h : Z ⟶ X} (t : UniversalFirstOrderThickening B S hS h) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (conormalSheaf B S hS t) ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite
        (conormalModule B S hS t.ambient t.closedSub) := by
  have hiso : IsIso t.sourceInclusion.hom :=
    ⟨t.sourceIso.inv, t.sourceIso.hom_inv_id, t.sourceIso.inv_hom_id⟩
  exact (isFiniteLocallyFreeOnSite_modulePullback_iff B S hS t.sourceInclusion
    (isEtale_of_isIso B S hS _) (isSurjective_of_isIso B S hS _)
    (conormalModule B S hS t.ambient t.closedSub)).symm

/-! ### Étale localization of the conormal module of a closed subspace -/

/-- **Finite local freeness of a conormal module is étale local.**  For a closed subspace `Z` of
an algebraic space `X'` over `S` and a morphism `g : V' ⟶ X'` which is étale and surjective on
points, the conormal module of `Z` in `X'` is finite locally free exactly when the conormal
module of the inverse image of `Z` in `V'` is.

The projection of the inverse image is a base change of `g`, hence étale and surjective on
points, and Stacks 060D (3) identifies the inverse image of `𝒞_{Z/X'}` along it with the
conormal module of the inverse image. -/
public theorem isFiniteLocallyFreeOnSite_conormalModule_preimage_iff
    {X' V' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X'.1)
    (g : V' ⟶ X') (hg : IsEtale B S hS g.hom) (hgsurj : IsSurjective B S hS g.hom) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (conormalModule B S hS X' Z) ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite (conormalModule B S hS V'
        ⟨Z.1.preimage g.hom,
          isClosedSubspace_preimage B S hS g.hom Z.1 X'.2 V'.2 Z.2⟩) := by
  have hW : IsClosedSubspace B S hS (Z.1.preimage g.hom) :=
    isClosedSubspace_preimage B S hS g.hom Z.1 X'.2 V'.2 Z.2
  have hsq : IsPullback (Z.1.fromPreimage g.hom) (Z.1.preimage g.hom).ι Z.1.ι g.hom :=
    Subfunctor.isPullback_preimage g.hom Z.1
  have hsqS : IsPullback
      (ObjectProperty.homMk (Z.1.fromPreimage g.hom) :
        (⟨(Z.1.preimage g.hom).toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (Z.1.preimage g.hom).ι)
      (ObjectProperty.homMk Z.1.ι) g :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι (IsAlgebraicSpace B S hS)) hsq
  have hc : IsEtale B S hS
      (ObjectProperty.homMk (Z.1.fromPreimage g.hom) :
        (⟨(Z.1.preimage g.hom).toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).hom :=
    isEtale_of_isPullback B S hS _ _ g _ hsqS.flip hg
  have hcsurj : IsSurjective B S hS
      (ObjectProperty.homMk (Z.1.fromPreimage g.hom) :
        (⟨(Z.1.preimage g.hom).toFunctor, hW.1⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)).hom :=
    isSurjective_of_isPullback B S hS hsqS.flip hgsurj
  refine (isFiniteLocallyFreeOnSite_modulePullback_iff B S hS _ hc hcsurj
    (conormalModule B S hS X' Z)).trans ?_
  exact isFiniteLocallyFreeOnSite_iff_of_iso
    (conormalModuleEtaleLocalizationIso B S hS Z g hg (Z.1.preimage g.hom) hW
      (Z.1.fromPreimage g.hom) hsq)

end AlgebraicGeometry.Space

end
