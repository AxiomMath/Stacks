module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleEtaleRestrictionCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleSchemeAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure

/-!
# The conormal module of a closed subspace, restricted to a presented étale chart

Let `X'` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`Z ⊆ X'` be a closed subspace, let `U'` be an étale scheme chart of `X'` and let

```
T --incl--> U'
|           |
c           |
v           v
Z --------> X'
```

be a cartesian square of presheaves presenting `Z ×_{X'} U'` by a morphism `incl` of the big
fppf site which is a closed immersion of schemes.  Then `c` is an étale chart of `Z`, and this
file identifies the inverse image of the conormal module `𝒞_{Z/X'}` to the small étale site of
the chart space of that chart with the module `Mᵃ` of [Stacks Project, Tag 03DU] (4) of the
*Zariski* conormal sheaf of `incl`:

`c^*𝒞_{Z/X'} ≅ (𝒞_{T/U'})ᵃ`.

Three known isomorphisms compose to give it:

* `AlgebraicGeometry.Space.modulePullbackCompIso`, [Stacks Project, Tag 03LU], splits the chart
  morphism as the comparison of `T` with the range of `incl` followed by the projection of the
  base-changed subspace;
* `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso`,
  [Stacks Project, Tag 04CO], identifies the inverse image of `𝒞_{Z/X'}` along that projection
  with the conormal module of the base-changed subspace of the chart space — the base-changed
  subspace being taken as the *range* of `incl`, which is the spelling the represented case
  needs;
* `AlgebraicGeometry.Space.conormalModuleClosedSubspaceRangeIso`, [Stacks Project, Tag 04G2] (1),
  identifies that with the associated module of the Zariski conormal sheaf of `incl`.

## Why this is wanted

It is the *target* half of the comparison of the two descriptions of the acting sheaf of
[Stacks Project, Tag 061D] on an étale chart, which step (II) of [Stacks Project, Tag 04AM]
needs.  The acting group at a chart,
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection`, lands in the conormal data
`RingHom.ker incl^♯` of the chart thickening, whose identification with the global sections of
the Zariski conormal sheaf is
`Stacks.Thickenings.conormalTopSectionsLinearEquivKer`; what is proved here is the half of the
comparison which lives on the small étale site.

## Main definitions

* `AlgebraicGeometry.Space.presentedSubspaceChart`: the étale chart of `Z` cut out by the
  presentation — the object `T` with the chart morphism `c`.  Its étaleness is base change of
  the étaleness of `U'`, [Stacks Project, Tag 03FU].
* `AlgebraicGeometry.Space.presentedSubspaceRangeMap`: the morphism from the range of `incl`,
  as a closed subspace of the chart space, to `Z`.
* `AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso`: **the inverse image of
  `𝒞_{Z/X'}` to the small étale site of the chart space is the associated module of the Zariski
  conormal sheaf of `incl`.**

## Main results

* `AlgebraicGeometry.Space.presentedSubspaceRangeMap_square` and
  `AlgebraicGeometry.Space.isPullback_presentedSubspaceRangeMap`: the square of inclusions
  commutes and is cartesian, which are the two hypotheses of
  `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso`.  Both come from the
  presenting square transported along the comparison of `T` with the range of `incl`.
* `AlgebraicGeometry.Space.chartToSpace_presentedSubspaceChart`: the structure morphism of the
  presented chart factors as that comparison followed by the projection of the base-changed
  subspace, which is what lets the composition comparison of Tag 03LU split the inverse image.
* `AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso_eq`: the identification
  **is** the chain of its four factors, stated between the isomorphisms.
* `AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso_eq_represented`: the same
  equation with the chain written first, which is what puts it at the represented reading of
  both chart spaces.
* `AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso_hom_represented`: **the
  factorization of the identification on `hom`**, at that reading.  It is the form a naturality
  square for the identification is assembled from.

## Implementation notes

**`AlgebraicGeometry.Space.modulePullback` and
`AlgebraicGeometry.Space.modulePullbackCompIso` are made file-locally irreducible**, exactly as
`StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleSchemeAgreement` does.  Without that the
composite below exhausts the 200,000-heartbeat budget at `whnf` — the composition comparison of
Tag 03LU is a `CategoryTheory.Adjunction.leftAdjointUniq`, and unfolding it drives the
conversion check into the construction of the inverse image by sheafification.  With it the file
checks in a couple of seconds.  Nothing below needs any value of either.

The base-changed subspace is taken to be `AlgebraicGeometry.Space.closedSubspaceRange` of
`incl`, not `CategoryTheory.Subfunctor.preimage` of `Z` along the chart: the represented
comparison of Tag 04G2 (1) is stated for the range, and
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso` takes the base-changed
subspace and the cartesian square as data rather than forming the preimage, so no equality of
subfunctors has to be proved.  The cartesian square is the presenting one transported along
`AlgebraicGeometry.Space.rangeIsoPresheaf` by `CategoryTheory.IsPullback.of_iso`.

### Why the factorization is stated at the represented reading, and in that spelling

The chain crosses two readings of a chart space.  Its first two factors meet at the chart space
of the presented chart, which `AlgebraicGeometry.Space.chartToSpace` reads as
`AlgebraicGeometry.Space.chartSpace` of that chart and
`AlgebraicGeometry.Space.modulePullbackCompIso` — through
`AlgebraicGeometry.Space.rangeSpaceIso` — reads as the algebraic space represented by `T`; its
last two meet at the chart space of `U'`, which
`AlgebraicGeometry.Space.conormalModuleEtaleRestrictionCanonicalIso` infers from
`AlgebraicGeometry.Space.chartToSpace` of `U'` and
`AlgebraicGeometry.Space.conormalModuleClosedSubspaceRangeIso` writes as the algebraic space
represented by the object of the site underlying `U'`.

Both crossings are affordable **between isomorphisms** and neither is affordable at a composite
of morphisms, which is what
`AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso_eq_represented` is for: it
makes both crossings once, at the isomorphisms, by naming the reading in the motive of the
leading transport and in the étale source of the Tag 04CO factor, and
`.conormalModulePresentedChartAssociatedIso_hom_represented` then only projects.  Stating that
factorization at the inferred reading instead, or proving it by `rfl`, is a kernel timeout; so is
writing its leading transport as `CategoryTheory.eqToHom` of the motive rather than as `hom` of
`CategoryTheory.eqToIso` of it, even though the two are `rfl`-equal in isolation by
`CategoryTheory.eqToIso.hom`.

No `@[stacks]` attribute is claimed: Tags 03LU, 04CO and 04G2 (1) are registered at the
isomorphisms composed here, and Tag 03FU at the base change of étaleness.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local irreducible] modulePullback modulePullbackCompIso

variable {X' : AlgebraicSpaces B S hS}

variable (Z : ClosedSubspaces B S hS X'.1) (U' : SmallEtale B S hS X'.1)
    {T : BigFppfOver B S hS} (incl : T ⟶ (SmallEtale.toOver B S hS X'.1).obj U')
    (hincl : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map incl))
    (c : yoneda.obj T ⟶ Z.1.toFunctor)
    (hpb : IsPullback (yoneda.map incl) c U'.1.hom Z.1.ι)

/-- **The étale chart of a closed subspace cut out by a presentation of a chart thickening.**
The object `T` of the big fppf site, with the chart morphism `c : yoneda.obj T ⟶ Z`, is an étale
chart of `Z`: `c` is the base change of the étale structure morphism of `U'` along the inclusion
of `Z`, and étaleness of a morphism with representable source is stable under base change,
[Stacks Project, Tag 03FU]. -/
abbrev presentedSubspaceChart : SmallEtale B S hS Z.1.toFunctor :=
  ⟨CostructuredArrow.mk c,
    (isEtale_iff_presheaf_of_yoneda B S hS c).1
      (isEtale_of_isPullback_yoneda B S hS hpb
        ((isEtale_iff_presheaf_of_yoneda B S hS U'.1.hom).2 U'.property))⟩

/-- **The projection of the base-changed subspace of the chart space to `Z`.**  The range of
`incl` is a closed subspace of the chart space; the presenting square sends it to `Z`, the
morphism being the chart morphism `c` read through the comparison of `T` with that range. -/
noncomputable def presentedSubspaceRangeMap :
    closedSubspaceRangeSpace B S hS incl hincl ⟶
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) :=
  ObjectProperty.homMk ((rangeIsoPresheaf B S hS incl hincl).inv ≫ c)

include hpb in
/-- The square of inclusions commutes: the inclusion of the base-changed subspace followed by
the chart of `X'` is the projection to `Z` followed by the inclusion of `Z`.  This is the
presenting square read through the comparison of `T` with the range of `incl`. -/
theorem presentedSubspaceRangeMap_square :
    subspaceInclusion B S hS (chartSpace B S hS X' U') (closedSubspaceRange B S hS incl hincl) ≫
        chartToSpace B S hS X' U' =
      presentedSubspaceRangeMap B S hS Z U' incl hincl c ≫ subspaceInclusion B S hS X' Z := by
  apply ObjectProperty.hom_ext
  change (Subfunctor.range (yoneda.map incl)).ι ≫ U'.1.hom =
    ((rangeIsoPresheaf B S hS incl hincl).inv ≫ c) ≫ Z.1.ι
  have h1 : (rangeIsoPresheaf B S hS incl hincl).hom ≫
      (Subfunctor.range (yoneda.map incl)).ι = yoneda.map incl :=
    Subfunctor.toRange_ι (yoneda.map incl)
  have h2 : (rangeIsoPresheaf B S hS incl hincl).inv ≫ yoneda.map incl =
      (Subfunctor.range (yoneda.map incl)).ι :=
    (Iso.inv_comp_eq _).2 h1.symm
  rw [Category.assoc, ← hpb.w, ← Category.assoc, h2]

include hpb in
/-- The square of inclusions is cartesian.  It is the presenting square with its apex replaced
by the range of `incl`, along the comparison `AlgebraicGeometry.Space.rangeIsoPresheaf`. -/
theorem isPullback_presentedSubspaceRangeMap :
    IsPullback (closedSubspaceRange B S hS incl hincl).1.ι
      (presentedSubspaceRangeMap B S hS Z U' incl hincl c).hom
      (chartToSpace B S hS X' U').hom Z.1.ι :=
  hpb.of_iso (rangeIsoPresheaf B S hS incl hincl) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change yoneda.map incl ≫ 𝟙 _ =
        Subfunctor.toRange (yoneda.map incl) ≫ (Subfunctor.range (yoneda.map incl)).ι
      rw [Category.comp_id, Subfunctor.toRange_ι])
    (by
      change c ≫ 𝟙 _ = (rangeIsoPresheaf B S hS incl hincl).hom ≫
        ((rangeIsoPresheaf B S hS incl hincl).inv ≫ c)
      rw [Iso.hom_inv_id_assoc, Category.comp_id])
    (Category.comp_id _ |>.trans (Category.id_comp _).symm)
    (Category.comp_id _ |>.trans (Category.id_comp _).symm)

include hpb in
/-- The structure morphism of the presented chart of `Z` is the comparison of `T` with the range
of `incl` followed by the projection of the base-changed subspace.  This is what lets the
composition comparison of [Stacks Project, Tag 03LU] split its inverse image. -/
theorem chartToSpace_presentedSubspaceChart :
    chartToSpace B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)
        (presentedSubspaceChart B S hS Z U' incl c hpb) =
      (rangeSpaceIso B S hS incl hincl).hom ≫
        presentedSubspaceRangeMap B S hS Z U' incl hincl c := by
  apply ObjectProperty.hom_ext
  exact (Iso.hom_inv_id_assoc _ _).symm

include hpb in
/-- **The conormal module of a closed subspace, restricted to a presented étale chart, is the
associated module of the Zariski conormal sheaf of the presenting closed immersion.**  For a
cartesian square presenting `Z ×_{X'} U'` by a closed immersion `incl : T ⟶ U'` of schemes of
the site,

`c^*𝒞_{Z/X'} ≅ (𝒞_{T/U'})ᵃ`

on the small étale site of the algebraic space represented by `T`.

This is [Stacks Project, Tag 03LU] splitting the chart morphism, [Stacks Project, Tag 04CO] at
the étale chart of `X'`, and [Stacks Project, Tag 04G2] (1) at the closed immersion `incl`. -/
noncomputable def conormalModulePresentedChartAssociatedIso :
    (modulePullback B S hS (chartToSpace B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)
          (presentedSubspaceChart B S hS Z U' incl c hpb))).obj
        (conormalModule B S hS X' Z) ≅
      (representedAssociatedModule B S hS T (schemeSpace T).property).obj
        (Stacks.Conormal.conormalSheaf ((BigFppfOver.toScheme B S hS).map incl)) :=
  eqToIso (congrArg (fun m => (modulePullback B S hS m).obj (conormalModule B S hS X' Z))
      (chartToSpace_presentedSubspaceChart B S hS Z U' incl hincl c hpb)) ≪≫
    ((modulePullbackCompIso B S hS (rangeSpaceIso B S hS incl hincl).hom
        (presentedSubspaceRangeMap B S hS Z U' incl hincl c)).app
          (conormalModule B S hS X' Z)).symm ≪≫
    (modulePullback B S hS (rangeSpaceIso B S hS incl hincl).hom).mapIso
        (conormalModuleEtaleRestrictionCanonicalIso B S hS
          (closedSubspaceRange B S hS incl hincl) Z (chartToSpace B S hS X' U')
          (presentedSubspaceRangeMap B S hS Z U' incl hincl c)
          (presentedSubspaceRangeMap_square B S hS Z U' incl hincl c hpb)
          (isPullback_presentedSubspaceRangeMap B S hS Z U' incl hincl c hpb)
          (isEtale_chartToSpace B S hS X' U')) ≪≫
      conormalModuleClosedSubspaceRangeIso B S hS incl

/-! ### The defining chain, and its factorization at the represented chart space -/

/-- **The presented-chart comparison is the transport of the factorization of the chart morphism,
the inverse of [Stacks Project, Tag 03LU], the inverse image of [Stacks Project, Tag 04CO] and
[Stacks Project, Tag 04G2] (1).**  The defining chain of
`AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso`, stated between the
isomorphisms, which is the level at which the chain is cheap. -/
theorem conormalModulePresentedChartAssociatedIso_eq :
    conormalModulePresentedChartAssociatedIso B S hS Z U' incl hincl c hpb =
      eqToIso (congrArg (fun m : chartSpace B S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)
            (presentedSubspaceChart B S hS Z U' incl c hpb) ⟶
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) =>
          (modulePullback B S hS m).obj (conormalModule B S hS X' Z))
          (chartToSpace_presentedSubspaceChart B S hS Z U' incl hincl c hpb)) ≪≫
        ((modulePullbackCompIso B S hS (rangeSpaceIso B S hS incl hincl).hom
            (presentedSubspaceRangeMap B S hS Z U' incl hincl c)).app
              (conormalModule B S hS X' Z)).symm ≪≫
        (modulePullback B S hS (rangeSpaceIso B S hS incl hincl).hom).mapIso
            (conormalModuleEtaleRestrictionCanonicalIso B S hS
              (closedSubspaceRange B S hS incl hincl) Z (chartToSpace B S hS X' U')
              (presentedSubspaceRangeMap B S hS Z U' incl hincl c)
              (presentedSubspaceRangeMap_square B S hS Z U' incl hincl c hpb)
              (isPullback_presentedSubspaceRangeMap B S hS Z U' incl hincl c hpb)
              (isEtale_chartToSpace B S hS X' U')) ≪≫
          conormalModuleClosedSubspaceRangeIso B S hS incl :=
  rfl

/-- **The defining chain of the presented-chart comparison, read at the represented chart
spaces.**  `AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso_eq` with the chart
space of the presented chart read as the algebraic space *represented* by `T`, and the étale
source of the [Stacks Project, Tag 04CO] factor read as the algebraic space represented by the
object of the site underlying `U'`.  Those are the two readings in which the composition
comparison of [Stacks Project, Tag 03LU] and the comparison of [Stacks Project, Tag 04G2] (1)
are stated, and so the readings every square of the chain reads them at.

The factored side is stated **first** on purpose: an equation takes the reading of whichever side
elaborates first, so writing the chain on the left is what puts the whole equation at the
represented reading.  Both crossings happen here, between two isomorphisms and with no
composition of morphisms formed — the one level at which they are affordable; see the
implementation notes. -/
theorem conormalModulePresentedChartAssociatedIso_eq_represented :
    eqToIso (congrArg
          (fun m : (schemeSpace T :
                AlgebraicSpaces B S hS) ⟶
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) =>
            (modulePullback B S hS m).obj (conormalModule B S hS X' Z))
          (chartToSpace_presentedSubspaceChart B S hS Z U' incl hincl c hpb)) ≪≫
        ((modulePullbackCompIso B S hS (rangeSpaceIso B S hS incl hincl).hom
              (presentedSubspaceRangeMap B S hS Z U' incl hincl c)).app
            (conormalModule B S hS X' Z)).symm ≪≫
        (modulePullback B S hS (rangeSpaceIso B S hS incl hincl).hom).mapIso
            (conormalModuleEtaleRestrictionCanonicalIso B S hS
              (X := (schemeSpace ((SmallEtale.toOver B S hS X'.1).obj U') :
                  AlgebraicSpaces B S hS))
              (closedSubspaceRange B S hS incl hincl) Z (chartToSpace B S hS X' U')
              (presentedSubspaceRangeMap B S hS Z U' incl hincl c)
              (presentedSubspaceRangeMap_square B S hS Z U' incl hincl c hpb)
              (isPullback_presentedSubspaceRangeMap B S hS Z U' incl hincl c hpb)
              (isEtale_chartToSpace B S hS X' U')) ≪≫
          conormalModuleClosedSubspaceRangeIso B S hS incl =
      conormalModulePresentedChartAssociatedIso B S hS Z U' incl hincl c hpb :=
  (conormalModulePresentedChartAssociatedIso_eq B S hS Z U' incl hincl c hpb).symm

/-- **The factorization of the presented-chart comparison**, at the represented chart spaces:
`AlgebraicGeometry.Space.conormalModulePresentedChartAssociatedIso_eq_represented` on `hom`, by
`congrArg`, which is where the four factors appear and where the three
`CategoryTheory.Iso.trans` are projected away.

This is the form an assembler of a naturality square takes as a factorization of one of its two
sides: each factor is the term the corresponding square writes — the transport of the
factorization of the chart morphism, the inverted composition comparison of
[Stacks Project, Tag 03LU] that `AlgebraicGeometry.Space.headSquareInv` moves, the inverse image
of the identification of [Stacks Project, Tag 04CO] and the comparison of
[Stacks Project, Tag 04G2] (1).

The leading transport is written as `hom` of `CategoryTheory.eqToIso` rather than as
`CategoryTheory.eqToHom`.  The two are interchangeable by `CategoryTheory.eqToIso.hom`, which is
`rfl` and cheap, but only the first can stand as the left factor of this composite; see the
implementation notes. -/
theorem conormalModulePresentedChartAssociatedIso_hom_represented :
    (eqToIso (congrArg
          (fun m : (schemeSpace T :
                AlgebraicSpaces B S hS) ⟶
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) =>
            (modulePullback B S hS m).obj (conormalModule B S hS X' Z))
          (chartToSpace_presentedSubspaceChart B S hS Z U' incl hincl c hpb))).hom ≫
        ((modulePullbackCompIso B S hS (rangeSpaceIso B S hS incl hincl).hom
              (presentedSubspaceRangeMap B S hS Z U' incl hincl c)).app
            (conormalModule B S hS X' Z)).inv ≫
          (modulePullback B S hS (rangeSpaceIso B S hS incl hincl).hom).map
              (conormalModuleEtaleRestrictionCanonicalIso B S hS
                (X := (schemeSpace ((SmallEtale.toOver B S hS X'.1).obj U') :
                    AlgebraicSpaces B S hS))
                (closedSubspaceRange B S hS incl hincl) Z (chartToSpace B S hS X' U')
                (presentedSubspaceRangeMap B S hS Z U' incl hincl c)
                (presentedSubspaceRangeMap_square B S hS Z U' incl hincl c hpb)
                (isPullback_presentedSubspaceRangeMap B S hS Z U' incl hincl c hpb)
                (isEtale_chartToSpace B S hS X' U')).hom ≫
            (conormalModuleClosedSubspaceRangeIso B S hS incl).hom =
      (conormalModulePresentedChartAssociatedIso B S hS Z U' incl hincl c hpb).hom :=
  congrArg Iso.hom
    (conormalModulePresentedChartAssociatedIso_eq_represented B S hS Z U' incl hincl c hpb)

end AlgebraicGeometry.Space

end
