module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.StalkReflectsUnits
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.ToposHomUnitsSquare

/-!
# The small étale ringed topos morphism of a morphism of algebraic spaces is locally ringed

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  Stacks 04KJ says that the
morphism of small étale ringed topoi `(f_small, f♯) : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` of
Stacks 03G8 is a morphism of *locally* ringed topoi in the sense of Stacks 04HA: its square

```
  f⁻¹(𝒪_Y^*) ---> 𝒪_X^*
      |             |
      v             v
  f⁻¹(𝒪_Y)  ---> 𝒪_X
```

of units subsheaves is cartesian.

The proof is the source's.  Both small étale sites are locally ringed (Stacks 04KH,
`AlgebraicGeometry.Space.smallEtaleRingedSite_isLocallyRinged`) and the small étale site of `X`
has enough points: the geometric points of `X` are a conservative family of points of it.  So
by condition (3) of Stacks 04H9 it suffices that at every geometric point `x̄` of `X` the
induced map of étale local rings `𝒪_{Y, f(x̄)} ⟶ 𝒪_{X, x̄}` be a local ring map.  That map is
`AlgebraicGeometry.Space.etaleLocalRingMap`, which is local by
`AlgebraicGeometry.Space.isLocalHom_etaleLocalRingMap` — itself deduced from the corresponding
statement for schemes along a commutative square of étale scheme charts over `f`, exactly as
the source does.

## Main results

* `AlgebraicGeometry.Space.isLocalHom_stalkStructureMap`: the fibre at a geometric point of the
  inverse-image structure map is a local ring homomorphism.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_isLocallyRinged`: **Stacks 04KJ.**

## Implementation notes

That the fibre of the inverse-image structure map *is* the canonical map of étale local rings
of Stacks 04NG is not reproved here: it is
`AlgebraicGeometry.Space.etaleLocalRingMapAsStalkMap_eq`, and all that is done with it is to
transport locality along the two ring isomorphisms of Stacks 05VQ,
`AlgebraicGeometry.Space.pointStalkRingEquiv`.  This is the same reduction that
`AlgebraicGeometry.Space.isFlat_iff_smallEtaleRingedToposHom_isFlat` makes for flatness.

The passage from locality of that fibre to the cartesian units square is in two general steps:
`AlgebraicGeometry.RingedTopos.reflectsUnitsObj_sheafFiber_of_isLocalHom` turns it into
reflection of units by the stalk functor of the point on sheaves of *sets*, which is the
universe in which the units square is read, and
`AlgebraicGeometry.RingedToposHom.isLocallyRinged_of_reflectsUnitsObj` assembles the square
from a conservative family of such functors.  Neither step mentions algebraic spaces.

## References

* [Stacks Project, Tag 04KJ](https://stacks.math.columbia.edu/tag/04KJ)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04H9](https://stacks.math.columbia.edu/tag/04H9)
* [Stacks Project, Tag 04KH](https://stacks.math.columbia.edu/tag/04KH)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)

/-- **The fibre of the structure map at a geometric point is a local ring homomorphism.** It is
the canonical map of étale local rings `𝒪_{Y, f(x̄)} ⟶ 𝒪_{X, x̄}` of Stacks 04NG read through
the comparison of Stacks 05VQ, and that map is local. -/
theorem isLocalHom_stalkStructureMap :
    IsLocalHom (stalkStructureMap B S hS f x).hom := by
  have hY : IsLocalHom
      (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).toRingHom :=
    isLocalHom_toRingHom (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x))
  have hX : IsLocalHom (pointStalkRingEquiv B S hS X x).symm.toRingHom :=
    isLocalHom_toRingHom (pointStalkRingEquiv B S hS X x).symm
  have hmap : IsLocalHom (etaleLocalRingMap X.2 f.hom x) :=
    isLocalHom_etaleLocalRingMap B S hS X.2 Y.2 f.hom x
  have h1 : IsLocalHom ((etaleLocalRingMap X.2 f.hom x).comp
      (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).toRingHom) :=
    RingHom.isLocalHom_comp _ _
  have h2 : IsLocalHom ((pointStalkRingEquiv B S hS X x).symm.toRingHom.comp
      ((etaleLocalRingMap X.2 f.hom x).comp
        (pointStalkRingEquiv B S hS Y (geometricPointMap f.hom x)).toRingHom)) :=
    RingHom.isLocalHom_comp _ _
  rw [← etaleLocalRingMapAsStalkMap_eq (B := B) (S := S) (hS := hS) (f := f) (x := x)]
  exact h2

/-- The fibre at a geometric point of the inverse-image structure map, read without the
comparison of Stacks 04K2, is a local ring homomorphism: it differs from
`AlgebraicGeometry.Space.stalkStructureMap` by that comparison, which is an isomorphism. -/
theorem isLocalHom_sheafFiber_map_fSharpInverseImage :
    IsLocalHom ((((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := CommRingCat.{u})).map
      (smallEtaleRingedToposHom B S hS f).fSharpInverseImage).hom) := by
  set e := (smallEtaleInverseImageFiberRingIso B S hS f x).app
    (smallEtaleRingedTopos B S hS Y).O with he
  have hsplit : ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := CommRingCat.{u})).map
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage =
      e.inv ≫ stalkStructureMap B S hS f x :=
    (e.inv_hom_id_assoc _).symm
  have hst : IsLocalHom (stalkStructureMap B S hS f x).hom :=
    isLocalHom_stalkStructureMap B S hS f x
  refine ⟨fun a ha ↦ ?_⟩
  have hc : (stalkStructureMap B S hS f x).hom (e.inv.hom a) =
      (((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := CommRingCat.{u})).map
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage).hom a :=
    (ConcreteCategory.congr_hom hsplit a).symm
  have h2 : IsUnit (e.inv.hom a) := hst.map_nonunit _ (hc ▸ ha)
  have h4 : e.hom.hom (e.inv.hom a) = a := ConcreteCategory.congr_hom e.inv_hom_id a
  exact h4 ▸ h2.map e.hom.hom

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, the morphism of small
étale ringed topoi `(f_small, f♯)` attached to `f` is a morphism of locally ringed topoi: its
square of units subsheaves is cartesian.

The geometric points of `X` are a conservative family of points of its small étale site, and at
each of them the fibre of `f⁻¹𝒪_Y ⟶ 𝒪_X` is the map of étale local rings
`𝒪_{Y, f(x̄)} ⟶ 𝒪_{X, x̄}`, which is a local ring map. -/
@[stacks 04KJ]
theorem smallEtaleRingedToposHom_isLocallyRinged :
    (smallEtaleRingedToposHom B S hS f).IsLocallyRinged := by
  haveI : HasLimitsOfShape WalkingCospan (Sheaf (smallEtaleRingedTopos B S hS X).J (Type u)) :=
    HasFiniteLimits.out _
  haveI : HasPullback (RingedTopos.unitsιOf (smallEtaleRingedTopos B S hS X).O)
      (RingedTopos.forgetRingMap (smallEtaleRingedToposHom B S hS f).fSharpInverseImage) :=
    HasLimitsOfShape.has_limit _
  have hP : ∀ Φ : (ObjectProperty.ofObj
      (fun z : GeometricPoint B S hS X.1 => etaleSitePoint B S hS X.1 z X.2)).FullSubcategory,
      PreservesFiniteLimits (Φ.obj.sheafFiber (A := Type u)) := fun _ => inferInstance
  refine RingedToposHom.isLocallyRinged_of_reflectsUnitsObj
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (smallEtaleRingedToposHom B S hS f)
    (ι := (ObjectProperty.ofObj
      (fun z : GeometricPoint B S hS X.1 => etaleSitePoint B S hS X.1 z X.2)).FullSubcategory)
    (fun Φ => Φ.obj.sheafFiber (A := Type u)) hP
    (fun {F G} ψ hψ => by
      have : ∀ Φ : (ObjectProperty.ofObj (fun z : GeometricPoint B S hS X.1 =>
          etaleSitePoint B S hS X.1 z X.2)).FullSubcategory,
          IsIso ((Φ.obj.sheafFiber (A := Type u)).map ψ) := hψ
      exact (isConservativeFamilyOfPoints_etaleSitePoint B S hS X.1
        X.2).jointlyReflectIsomorphisms_type.isIso ψ) ?_
  rintro ⟨p, hp⟩
  obtain ⟨z, rfl⟩ := (ObjectProperty.ofObj_iff _ _).1 hp
  exact RingedTopos.reflectsUnitsObj_sheafFiber_of_isLocalHom _ _
    (isLocalHom_sheafFiber_map_fSharpInverseImage B S hS f z)

end AlgebraicGeometry.Space

end
