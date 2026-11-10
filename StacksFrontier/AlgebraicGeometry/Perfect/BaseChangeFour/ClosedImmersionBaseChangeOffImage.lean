module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived base change along a closed immersion, away from the closed subscheme

Consider a cartesian diagram of schemes

```
Z' --i'--> X'
|g          |f
Z --i-----> X
```

with `i` a closed immersion.  Stacks 0E23 asserts that the canonical derived base change map
`Lf^*(Ri_* K) ⟶ Ri'_*(Lg^* K)` of Stacks 08HY is an isomorphism for every `K` in `D(𝒪_Z)` when
`Z` and `X'` are tor independent over `X`.  Invertibility in the derived category is detected on
derived stalks, and the source's own proof computes that stalk at a point of `Z'`.  This file
settles the *other* points: at a point of `X'` outside `Z'` both sides of the comparison have
vanishing derived stalk, so the comparison is invertible there — with no tor independence
needed, and with none of the identifications the on-image half requires.

The underlying geometric input is that `Z'` is, as a subset of `X'`, exactly the preimage of
`Z`: that is `range_eq_preimage_range_of_isPullback`, and it is what converts "off `Z'`" into
"off `Z`" so that the vanishing of `Ri_* K` off the image can be used.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.Cohomology.ClosedImmersionBaseChange.range_eq_preimage_range_of_isPullback`: the image
  of `i'` in `X'` is the preimage under `f` of the image of `i` in `X`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isZero_derivedStalkFunctor_of_isZero`: the two
  spellings of the derived stalk of a complex of `𝒪_X`-modules vanish together.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isZero_derivedStalk_derivedPullback_of_isZero`:
  the derived stalk of `Lf^* M` at `x'` vanishes when the derived stalk of `M` at `f x'` does.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isZero_derivedStalk_pullbackPushforward`: the
  derived stalk of `Lf^*(Ri_* K)` — the source of the base change map — vanishes off `Z'`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isZero_derivedStalk_pushforwardPullback`: the
  derived stalk of `Ri'_*(Lg^* K)` — its target — vanishes off `Z'`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedStalk_derivedBaseChangeMap`: the
  derived base change map of Stacks 08HY has invertible derived stalk at every point of `X'`
  outside `Z'`.

## Implementation notes

*Two spellings of the derived stalk.*  `AlgebraicGeometry.SheafOfModules.derivedStalkFunctor`
takes modules over the `RingCat`-valued stalk of the ring sheaf, and is the spelling the
vanishing of `Ri_* K` off the image is stated in;
`AlgebraicGeometry.derivedStalkFunctor` takes modules over the local ring `𝒪_{X,x}`, and is the
spelling the derived stalk of a derived pullback is computed in.  Both are
`Functor.mapDerivedCategory` of an exact stalk functor on the *same* category of sheaves of
modules, so an object of either derived category is an object of the other; only the target
categories differ, by restriction of scalars along
`AlgebraicGeometry.ringCatStalkRingEquiv`.  `isZero_derivedStalkFunctor_of_isZero` crosses
between them, degree by degree through `AlgebraicGeometry.restrictScalarsStalkObjIso`, and is
the only bridge the file needs.  It is stated in the one direction used; the converse would
need restriction of scalars to reflect zero objects, which nothing here wants.

*Why vanishing of all homology is turned into vanishing of the object by hand.*  There is no
`DerivedCategory.isZero_iff` in the library, so the argument of
`Stacks.ClosedImmersion.isZero_derivedStalk_mapDerivedCategory_of_notMemRange` is repeated:
`DerivedCategory.isIso_iff` applied to the zero endomorphism makes it invertible when every
homology vanishes, and an object with an invertible zero endomorphism is zero.

*The on-image half.*  Nothing in this file is tagged.  The invertibility of the derived stalk
of the base change map at the points of `Z'`, and with it Stacks 0E23, is proved in
the file `ClosedImmersionBaseChangeTorIndependent.lean` of the directory
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/`
(`Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareAsIso`).  The off-image half
does not use Tor independence.

## References

* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

noncomputable section

namespace Stacks.Cohomology.ClosedImmersionBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The closed subscheme of the base change is the preimage -/

/-- **The image of a base change of a closed immersion is the preimage of the image.**  For a
cartesian square of schemes the subset `i' (Z')` of `X'` is exactly `f⁻¹(i (Z))`.

The square is cartesian, so `Z'` is isomorphic to the fibre product over `X` of `X'` and `Z` in
a way carrying `i'` to the first projection, and the underlying set of a fibre product of
schemes does have the two projections' images given by preimages
(`AlgebraicGeometry.Scheme.Pullback.range_fst`).  No hypothesis on `i` is used. -/
@[ega "I 4.3.1" "partial", ega "IV 9.2.2" "(iv), special case"]
theorem range_eq_preimage_range_of_isPullback {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'}
    {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X} (sq : IsPullback i' g f i) :
    Set.range (⇑i') = (⇑f) ⁻¹' Set.range (⇑i) := by
  rw [← AlgebraicGeometry.Scheme.Pullback.range_fst f i, ← sq.isoPullback_hom_fst,
    Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (Scheme.Hom.surjective _), Set.image_univ]

/-! ### The two spellings of the derived stalk -/

/-- **The two derived stalks vanish together.**  If the derived stalk of `E` at `x` taken over
the `RingCat`-valued stalk of the ring sheaf is a zero object, then so is the derived stalk
taken over the local ring `𝒪_{X,x}`.

Both functors are `Functor.mapDerivedCategory` of a stalk functor on the same category of
sheaves of modules, so `E` is an object of either derived category.  The comparison is degreewise:
the `n`-th homology of each derived stalk is the stalk of the `n`-th cohomology sheaf of `E` in
the corresponding spelling, and the two sheaf-level stalks differ by restriction of scalars
along `AlgebraicGeometry.ringCatStalkRingEquiv`, which is additive and so carries a zero object
to a zero object. -/
theorem isZero_derivedStalkFunctor_of_isZero {X : Scheme.{u}} (x : X)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (h : IsZero ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor
      (structureSheafRing X.toRingedSpace) x).obj E)) :
    IsZero ((AlgebraicGeometry.derivedStalkFunctor x).obj E) := by
  set Y := (AlgebraicGeometry.derivedStalkFunctor x).obj E with hY
  have hz : ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor _ n).obj Y) := by
    intro n
    have h0 := Functor.map_isZero
      (DerivedCategory.homologyFunctor (ModuleCat.{u}
        (TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafRing X.toRingedSpace).obj x)) n) h
    have h1 : IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafRing X.toRingedSpace) x).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj E)) :=
      IsZero.of_iso h0
        (((AlgebraicGeometry.SheafOfModules.derivedStalkHomologyIso
          (structureSheafRing X.toRingedSpace) x n).app E).symm)
    have h2 := Functor.map_isZero (ModuleCat.restrictScalars.{u, u, u}
      (AlgebraicGeometry.ringCatStalkRingEquiv x).symm.toRingHom) h1
    have h3 : IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj E)) :=
      IsZero.of_iso h2 (AlgebraicGeometry.restrictScalarsStalkObjIso x _).symm
    exact IsZero.of_iso h3
      (((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryHomologyIso n).app E)
  have hiso : IsIso (0 : Y ⟶ Y) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    rw [(hz n).eq_of_src ((DerivedCategory.homologyFunctor _ n).map (0 : Y ⟶ Y)) (𝟙 _)]
    infer_instance
  rw [IsZero.iff_id_eq_zero]
  calc (𝟙 Y) = CategoryTheory.inv (0 : Y ⟶ Y) ≫ (0 : Y ⟶ Y) := (IsIso.inv_hom_id _).symm
    _ = 0 := Limits.comp_zero

/-! ### The derived stalk of a derived pullback vanishes where the stalk upstairs does -/

/-- **A derived pullback has vanishing derived stalk where its argument does.**  If the derived
stalk of `M` at `f x'` is a zero object then so is the derived stalk of `Lf^* M` at `x'`.

This is `AlgebraicGeometry.derivedPullbackStalkIso`, which computes the derived stalk of a
derived pullback as derived extension of scalars along the germ map `𝒪_{X, f x'} ⟶ 𝒪_{X', x'}`
applied to the derived stalk upstairs, together with additivity of that derived extension of
scalars. -/
theorem isZero_derivedStalk_derivedPullback_of_isZero {X' X : Scheme.{u}} (f : X' ⟶ X)
    (x' : X') (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (hM : IsZero ((AlgebraicGeometry.derivedStalkFunctor (f x')).obj M)) :
    IsZero ((AlgebraicGeometry.derivedStalkFunctor x').obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        f.toLRSHom.toShHom).obj M)) :=
  IsZero.of_iso
    (Functor.map_isZero
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (f.stalkMap x').hom).functor hM)
    ((AlgebraicGeometry.derivedPullbackStalkIso f x').app M)

/-! ### Both sides of the base change map vanish off the closed subscheme -/

section Square

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

/-- **The source of the base change map has vanishing derived stalk off `Z'`.**  At a point `x'`
of `X'` outside the image of `i'`, the derived stalk of `Lf^*(Ri_* K)` is a zero object.

The point `f x'` lies outside the image of `i` by
`range_eq_preimage_range_of_isPullback`, so the derived stalk of `Ri_* K` there vanishes by
`Stacks.ClosedImmersion.isZero_derivedStalk_derivedPushforward_of_notMemRange`; the derived
pullback then has vanishing derived stalk at `x'` by
`isZero_derivedStalk_derivedPullback_of_isZero`.  Only the closed immersion `i` and
cartesianness are used; there is no tor independence here. -/
theorem isZero_derivedStalk_pullbackPushforward (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (x' : X') (hx' : x' ∉ Set.range (⇑i')) :
    IsZero ((AlgebraicGeometry.derivedStalkFunctor x').obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          i.toLRSHom.toShHom).obj K))) := by
  have hbase : f x' ∉ Set.range (⇑i) := by
    rw [range_eq_preimage_range_of_isPullback sq] at hx'
    exact hx'
  exact isZero_derivedStalk_derivedPullback_of_isZero f x' _
    (isZero_derivedStalkFunctor_of_isZero _ _
      (Stacks.ClosedImmersion.isZero_derivedStalk_derivedPushforward_of_notMemRange i K
        (f x') hbase))

/-- **The target of the base change map has vanishing derived stalk off `Z'`.**  At a point `x'`
of `X'` outside the image of `i'`, the derived stalk of `Ri'_*(Lg^* K)` is a zero object.

`i'` is a closed immersion, being a base change of one, so this is
`Stacks.ClosedImmersion.isZero_derivedStalk_derivedPushforward_of_notMemRange` for `i'` applied
to `Lg^* K`, crossed to the local-ring spelling of the derived stalk. -/
theorem isZero_derivedStalk_pushforwardPullback (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (x' : X') (hx' : x' ∉ Set.range (⇑i')) :
    IsZero ((AlgebraicGeometry.derivedStalkFunctor x').obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          i'.toLRSHom.toShHom).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          g.toLRSHom.toShHom).obj K))) := by
  have hi' : AlgebraicGeometry.IsClosedImmersion i' :=
    MorphismProperty.of_isPullback sq.flip inferInstance
  exact isZero_derivedStalkFunctor_of_isZero _ _
    (Stacks.ClosedImmersion.isZero_derivedStalk_derivedPushforward_of_notMemRange i' _ x' hx')

/-- **Stacks 0E23 away from the closed subscheme.**  In a cartesian square of schemes with `i` a
closed immersion, the canonical derived base change map
`Lf^*(Ri_* K) ⟶ Ri'_*(Lg^* K)` of Stacks 08HY has invertible derived stalk at every point of
`X'` outside the image of `i'`.

Both the source and the target are zero objects there, by
`isZero_derivedStalk_pullbackPushforward` and `isZero_derivedStalk_pushforwardPullback`, and a
morphism between zero objects agrees with the canonical isomorphism between them.

This is *not* a clause of Stacks 0E23, which asserts invertibility of the comparison itself; it
is the half of the stalkwise criterion that the source's proof passes over in silence, and it
needs neither tor independence nor any identification of the comparison. -/
theorem isIso_derivedStalk_derivedBaseChangeMap (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (x' : X') (hx' : x' ∉ Set.range (⇑i')) :
    IsIso ((AlgebraicGeometry.derivedStalkFunctor x').map
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
        g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom f.toLRSHom.toShHom
        (by
          simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
            congrArg (fun h : Z' ⟶ X => h.toLRSHom.toShHom) sq.w.symm) K)) := by
  have hsrc := isZero_derivedStalk_pullbackPushforward sq K x' hx'
  have htgt := isZero_derivedStalk_pushforwardPullback sq K x' hx'
  exact ⟨⟨(hsrc.iso htgt).inv, hsrc.eq_of_src _ _, htgt.eq_of_src _ _⟩⟩

end Square

end Stacks.Cohomology.ClosedImmersionBaseChange

end

end
