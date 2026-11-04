module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Affine
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.ImmersionIntoSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.SmoothTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.RingTheory.Dualizing.GorensteinLocalCompleteIntersection
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport

/-!
# The source of a local complete intersection morphism over a Gorenstein scheme

A local complete intersection morphism whose target is a Gorenstein scheme has Gorenstein
source.

## Main results

* `AlgebraicGeometry.isGorenstein_of_isOpenImmersion` — Gorensteinness passes to the source of
  an open immersion.
* `AlgebraicGeometry.isGorenstein_of_isLocalCompleteIntersectionMorphism` — a local complete
  intersection morphism whose target is a Gorenstein scheme has Gorenstein source.

## Implementation notes

The statement is the globalization of the ring-theoretic
`Dualizing.isGorensteinRing_of_isLocalCompleteIntersection`, Stacks 0DWA, along the affine
criterion `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_iff_appTop`, Stacks 07DB. No
affineness, Noetherian or finiteness hypothesis is added: local Noetherianity of the source comes
from local Noetherianity of the target, a local complete intersection morphism being locally of
finite type.

Around a point `y` of the source the finite-type clause of Stacks 069F already supplies an affine
open `V` of the target and an affine open `U` of the source with `y ∈ U` and `U ≤ f ⁻¹ᵁ V`. The
restriction `f.resLE V U` is again a local complete intersection morphism, because the inclusion
of an open is an open immersion and hence both a Koszul-regular immersion and smooth, so Stacks
069J and 069M apply.

Both Gorenstein predicates quantify over the *canonical* localization
`Localization.AtPrime p`, while the geometric objects at hand are the stalks of the structure
sheaf, which are only isomorphic to those localizations. The two are matched by
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk` together with
`Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff`.

## References

* [Stacks Project, Tag 0BVA](https://stacks.math.columbia.edu/tag/0BVA)
* [Stacks Project, Tag 0AWW](https://stacks.math.columbia.edu/tag/0AWW)
* [Stacks Project, Tag 069F](https://stacks.math.columbia.edu/tag/069F)
* [Stacks Project, Tag 069J](https://stacks.math.columbia.edu/tag/069J)
* [Stacks Project, Tag 069L](https://stacks.math.columbia.edu/tag/069L)
* [Stacks Project, Tag 069M](https://stacks.math.columbia.edu/tag/069M)
* [Stacks Project, Tag 07DB](https://stacks.math.columbia.edu/tag/07DB)
* [Stacks Project, Tag 0DWA](https://stacks.math.columbia.edu/tag/0DWA)
-/

@[expose] public section

open CategoryTheory Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry

/-- At a point of an affine open, Gorensteinness of the local ring of a scheme is Gorensteinness
of the localization of the sections at the corresponding prime. -/
private theorem isGorensteinLocalRing_stalk_iff_atPrime {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) [IsLocallyNoetherian X] [IsNoetherianRing Γ(X, U)] (x : U) :
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x.1) ↔
      Dualizing.IsGorensteinLocalRing
        (Localization.AtPrime (hU.primeIdealOf x).asIdeal) := by
  let p := (hU.primeIdealOf x).asIdeal
  let : Algebra Γ(X, U) (X.presheaf.stalk x.1) := X.presheaf.algebra_section_stalk x
  let : IsLocalization.AtPrime (X.presheaf.stalk x.1) p := hU.isLocalization_stalk x
  exact Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff
    (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk x.1)
      (Localization.AtPrime p)).toRingEquiv

/-- The sections of a Gorenstein scheme over an affine open form a Gorenstein ring. -/
private theorem isGorensteinRing_sections_of_isGorenstein {X : Scheme.{u}} [IsGorenstein X]
    {U : X.Opens} (hU : IsAffineOpen U) [IsNoetherianRing Γ(X, U)] :
    Dualizing.IsGorensteinRing Γ(X, U) := by
  intro p hp
  obtain ⟨x, hx⟩ : ∃ x : U, (hU.primeIdealOf x).asIdeal = p := by
    refine ⟨hU.isoSpec.inv.base ⟨p, hp⟩, ?_⟩
    have : (hU.isoSpec.inv ≫ hU.isoSpec.hom).base ⟨p, hp⟩ = (⟨p, hp⟩ : PrimeSpectrum Γ(X, U)) := by
      rw [hU.isoSpec.inv_hom_id]; rfl
    exact congrArg PrimeSpectrum.asIdeal this
  subst hx
  exact (isGorensteinLocalRing_stalk_iff_atPrime hU x).mp
    (IsGorenstein.isGorensteinLocalRing x.1)

/-- The local ring of the source of an open immersion at `x` is Gorenstein iff the local ring of
the target at `j x` is. -/
private theorem isGorensteinLocalRing_stalk_iff_of_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (x : X) :
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) ↔
      Dualizing.IsGorensteinLocalRing (Y.presheaf.stalk (j.base x)) :=
  Stacks.Duality.isGorensteinLocalRing_ringEquiv_iff
    (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv.symm

/-- Gorensteinness passes to the source of an open immersion, the stalks of the source being the
stalks of the target at the image points. -/
public theorem isGorenstein_of_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] [IsGorenstein Y] : IsGorenstein X := by
  let : IsLocallyNoetherian Y := IsGorenstein.toIsLocallyNoetherian
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion j
  refine { toIsLocallyNoetherian := ‹_›, isGorensteinLocalRing := fun x => ?_ }
  exact (isGorensteinLocalRing_stalk_iff_of_isOpenImmersion j x).mpr
    (IsGorenstein.isGorensteinLocalRing (j.base x))

/-- A local complete intersection morphism whose target is a Gorenstein scheme has Gorenstein
source. -/
@[stacks 0BVA]
public theorem isGorenstein_of_isLocalCompleteIntersectionMorphism {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : IsLocalCompleteIntersectionMorphism f) (hX : IsGorenstein X) : IsGorenstein Y := by
  let : IsGorenstein X := hX
  let : IsLocallyNoetherian X := IsGorenstein.toIsLocallyNoetherian
  let : LocallyOfFiniteType f :=
    (HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType)
      (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        RingHom.finiteType_holdsForLocalizationAway).left).mpr fun y => (hf y).1
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  refine { toIsLocallyNoetherian := ‹_›, isGorensteinLocalRing := ?_ }
  intro y
  -- an affine open `V` of the target around the image of `y`, and an affine open `U ≤ f ⁻¹ᵁ V`
  obtain ⟨V, U, hyU, hUV, -⟩ := (hf y).1
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine V.1.toScheme := V.2
  -- the restriction of `f` is a local complete intersection morphism of affine schemes
  let g : U.1.toScheme ⟶ V.1.toScheme := f.resLE V.1 U.1 hUV
  have hgRing : g.appTop.hom.IsLocalCompleteIntersection :=
    (isLocalCompleteIntersectionMorphism_iff_appTop g).mp
      (isLocalCompleteIntersectionMorphism_resLE f hf V.1 U.1 hUV)
  -- the sections over `V` are a Gorenstein ring, hence so are the sections over `U`
  let : IsGorenstein V.1.toScheme := isGorenstein_of_isOpenImmersion V.1.ι
  let : IsNoetherianRing Γ(V.1.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V.1.toScheme⟩
  have hVring : Dualizing.IsGorensteinRing Γ(V.1.toScheme, ⊤) :=
    isGorensteinRing_sections_of_isGorenstein (isAffineOpen_top V.1.toScheme)
  have hUring := Dualizing.isGorensteinRing_of_isLocalCompleteIntersection g.appTop.hom hgRing
    hVring
  -- which is Gorensteinness of the local ring of `Y` at `y`
  let : IsNoetherianRing Γ(U.1.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.1.toScheme⟩
  exact (isGorensteinLocalRing_stalk_iff_of_isOpenImmersion U.1.ι ⟨y, hyU⟩).mp
    ((isGorensteinLocalRing_stalk_iff_atPrime (X := U.1.toScheme)
      (isAffineOpen_top U.1.toScheme) ⟨⟨y, hyU⟩, trivial⟩).mpr (hUring _))

end AlgebraicGeometry

end
