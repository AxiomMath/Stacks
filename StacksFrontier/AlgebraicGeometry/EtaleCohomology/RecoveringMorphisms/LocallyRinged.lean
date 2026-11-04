module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import
    StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.GeometricStalkReflectsUnits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedSiteHom
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.IsLocallyRingedCriterion

/-!
# Towards Stacks 04I5: the small étale ringed-site morphism of a morphism of schemes

Stacks 04I5 says that the morphism of ringed sites
`(a_small, a_small^♯) : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` attached to a morphism of schemes
`a : X ⟶ Y` is a morphism of *locally* ringed sites, that is — Stacks 04HA — that its square

```
  a⁻¹(𝒪_Y^*) ---> 𝒪_X^*
      |             |
      v             v
  a⁻¹(𝒪_Y)  ---> 𝒪_X
```

of units subsheaves is cartesian.  The morphism of ringed sites is
`AlgebraicGeometry.smallEtaleRingedSiteHom` and the assertion is
`(smallEtaleRingedSiteHom B a).IsLocallyRinged`.

This file reduces that assertion to a statement about one geometric stalk at a time.  The
reduction has no remaining sheaf-theoretic content: by Stacks 04KR the units square of
`a_small` is the units square of the morphism `a⁻¹𝒪_Y ⟶ 𝒪_X` of sheaves of commutative rings on
the small étale site of `X`
(`AlgebraicGeometry.RingedSite.HomGeneral.forgetRing_map_fSharpRingMap`), by Stacks 021B the
geometric points of `X` are a conservative family of points of that site at the universe of the
sections (`AlgebraicGeometry.isConservativeFamilyOfPoints_geometricSitePoints`), and a square of
sheaves of sets which is cartesian at every member of a conservative family is cartesian
(`AlgebraicGeometry.RingedTopos.isPullback_unitsSquare_of_family`).

What is left is exactly the one step of the source's proof with mathematical content, condition
(3) of Stacks 04H9: at each geometric point the induced map of étale local rings
`(𝒪_Y)_ȳ ⟶ (𝒪_X)_x̄` reflects units.  That is
`AlgebraicGeometry.reflectsUnitsObj_fSharpRingMap`, and feeding it to the reduction gives
Stacks 04I5.

## Main results

* `AlgebraicGeometry.smallEtaleRingedSiteHom_isLocallyRinged_of_reflectsUnitsStalk`: the
  reduction of Stacks 04I5 to reflection of units at every geometric stalk.
* `AlgebraicGeometry.smallEtaleRingedSiteHom_isLocallyRinged`: **Stacks 04I5.**

## Implementation notes

The hypothesis of the reduction is phrased as
`AlgebraicGeometry.RingedTopos.ReflectsUnitsObj` for the stalk functor at a geometric point,
which mentions no ring structure: it asks that a germ of `a⁻¹𝒪_Y` at a geometric point lift
through the stalk of the units subsheaf of `a⁻¹𝒪_Y` as soon as its image in `(𝒪_X)_x̄` lifts
through the stalk of `𝒪_X^*`.  By `AlgebraicGeometry.RingedTopos.isUnit_stalk_iff` that is
reflection of units for the ring structures transported along the stalk functor, so it is
condition (3) of Stacks 04H9 — stated for the *transported* stalk rings rather than for the
étale local rings of Stacks 03PS, the two being identified by
`AlgebraicGeometry.etaleStalkMulEquiv`.

The reduction is stated at the family indexed by
`AlgebraicGeometry.geometricSitePoints`, the conservative family of Stacks 021B, rather than at
all geometric points of `X`: that family is the one whose conservativity is proved, and it is
indexed by the points of the underlying space of `X` with the algebraic closures of their
residue fields.

## References

* [Stacks Project, Tag 04I5](https://stacks.math.columbia.edu/tag/04I5)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
* [Stacks Project, Tag 04KR](https://stacks.math.columbia.edu/tag/04KR)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- The stalk functor of sheaves of sets at a member of the conservative family of geometric
points of the small étale site of `X`. -/
public abbrev geometricSitePointStalk
    (Φ : (geometricSitePoints B X.obj X.property).FullSubcategory) :
    Sheaf (SmallEtale.topology B X.obj X.property) (Type u) ⥤ Type u :=
  Φ.obj.sheafFiber

/-- The stalk functor at a geometric point is left exact. -/
public instance preservesFiniteLimits_geometricSitePointStalk
    (Φ : (geometricSitePoints B X.obj X.property).FullSubcategory) :
    PreservesFiniteLimits (geometricSitePointStalk B (X := X) Φ) :=
  inferInstance

/-- **Stacks 04I5, conditional on condition (3) of Stacks 04H9.** The morphism of ringed sites
`(a_small, a_small^♯)` of a morphism of schemes `a : X ⟶ Y` is a morphism of locally ringed
sites, provided that at every geometric point of `X` the stalk of the structure map
`a⁻¹𝒪_Y ⟶ 𝒪_X` reflects units.

The hypothesis is the only remaining content: the reduction of the cartesian units square of
Stacks 04HA to it uses Stacks 04KR, the conservativity of the geometric points of Stacks 021B,
and nothing else. -/
public theorem smallEtaleRingedSiteHom_isLocallyRinged_of_reflectsUnitsStalk
    (h : ∀ Φ : (geometricSitePoints B X.obj X.property).FullSubcategory,
      RingedTopos.ReflectsUnitsObj (geometricSitePointStalk B (X := X) Φ)
        (smallEtaleRingedSiteHom B a).fSharpRingMap) :
    (smallEtaleRingedSiteHom B a).IsLocallyRinged :=
  RingedSite.HomGeneral.isLocallyRinged_of_reflectsUnitsObj (smallEtaleRingedSiteHom B a)
    (geometricSitePointStalk B (X := X))
    (preservesFiniteLimits_geometricSitePointStalk B (X := X))
    (fun {F G} ψ hψ ↦ by
      have : ∀ Φ : (geometricSitePoints B X.obj X.property).FullSubcategory,
          IsIso ((geometricSitePointStalk B (X := X) Φ).map ψ) := hψ
      exact (isConservativeFamilyOfPoints_geometricSitePoints B X.obj X.property)
        |>.jointlyReflectIsomorphisms_type.isIso ψ)
    h

/-- **Stacks 04I5.** The morphism of ringed sites `(a_small, a_small^♯)` associated to a
morphism of schemes `a : X ⟶ Y` is a morphism of locally ringed sites: its square of units
subsheaves is cartesian.

The geometric points of `X` are a conservative family of points of its small étale site, and at
each of them the stalk of `a⁻¹𝒪_Y ⟶ 𝒪_X` is the map of étale local rings
`(𝒪_Y)_ȳ ⟶ (𝒪_X)_x̄`, which is a local ring map. -/
@[stacks 04I5]
public theorem smallEtaleRingedSiteHom_isLocallyRinged :
    (smallEtaleRingedSiteHom B a).IsLocallyRinged :=
  smallEtaleRingedSiteHom_isLocallyRinged_of_reflectsUnitsStalk B a fun Φ ↦ by
    obtain ⟨P, hP⟩ := Φ
    obtain ⟨pt, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hP
    exact reflectsUnitsObj_fSharpRingMap B a (GeometricPoint.ofPoint X.obj pt)

end AlgebraicGeometry

end
