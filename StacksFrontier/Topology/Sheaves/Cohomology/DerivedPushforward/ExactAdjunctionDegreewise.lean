module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryAdjunctionUnit
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.Homology.DerivedCategory.MateDerivedCategory
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional

/-!
# An exact pullback–pushforward adjunction derives degreewise

Let `i : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces along which **both** functors of the
adjunction `i^* ⊣ i_*` of [Stacks, Tag 0096] are exact — `i^*` preserves finite limits and finite
colimits, and so does `i_*`.  Then nothing on either side is derived.  The derived pullback `Li^*`
of [Stacks, Tag 06YJ] is the functor `D(i^*)` induced degreewise, by
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory`; the derived
pushforward `Ri_*` of [Stacks, Tag 079W] is the functor `D(i_*)` induced degreewise, by
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`.  This file shows that the
*adjunction* goes the same way: under those two comparisons the derived adjunction
`Li^* ⊣ Ri_*` of [Stacks, Tag 079W] **is** the adjunction `D(i^*) ⊣ D(i_*)` that `i^* ⊣ i_*`
induces degreewise, namely `CategoryTheory.Adjunction.mapDerivedCategory`.

This is what makes the derived base change of [Stacks, Tag 08HY] accessible to the degreewise
mates calculus.  `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap` is a mate for the two
*derived* adjunctions, while `CategoryTheory.mateEquiv_mapDerivedCategory` — that
`CategoryTheory.Adjunction.mapDerivedCategory` carries mates to mates — speaks about the two
*degreewise* adjunctions.  The identification below is the bridge between those two statements.

## Main results

All three are in the namespace `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces`.

* `derivedPushforwardComparisonIso`: the comparison `D(i_*) ≅ Ri_*` for an exact `i_*`.
* `derivedAdjunction_eq_ofNatIso_mapDerivedCategory`: the derived adjunction of
  [Stacks, Tag 079W] is the degreewise one, transported along the comparisons of the two derived
  functors with the degreewise functors.
* `ofNatIso_derivedAdjunction_eq_mapDerivedCategory`: **the same statement with the transport on
  the other side**, which is the form the mates calculus consumes: the derived adjunction, read
  through the two comparisons, equals `CategoryTheory.Adjunction.mapDerivedCategory` of the
  underived adjunction.
* `mateEquiv_derivedAdjunction_eq_mapDerivedCategory`: the consequence the derived base change of
  [Stacks, Tag 08HY] is after — the mate, under two derived adjunctions, of the derived image of a
  2-square of degreewise pullbacks is the derived image of its mate under the two underived
  adjunctions.  This is the previous statement composed with
  `CategoryTheory.mateEquiv_mapDerivedCategory`.

## Implementation notes

*Why an equality of adjunctions, and how it is proved.*  An adjunction is determined by its unit,
and the unit of the derived adjunction of [Stacks, Tag 079W] is determined by
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_fac`: it is the unique
transformation into the left derived functor `Li^* ⋙ Ri_*` whose composite with the comparison
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison` is the degreewise
unit followed by the comparison
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit`.  That uniqueness is
`CategoryTheory.Adjunction.eq_of_unit_comp_eq`, and the absoluteness of the derived pullback that
it consumes is `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.comp_isLeftDerivedFunctor` at
the resolving datum of all objects, which an exact `i^*` admits.  So all that has to be checked is
that the transported degreewise adjunction satisfies the same factorization, and that is
`CategoryTheory.mapDerivedCategoryAdjunction_unit_app_Qh` — the unit of the degreewise derived
adjunction read on the homotopy category — together with the universal properties of the two
comparisons, `Stacks.Homology.leftDerivedIsoMapDerivedCategory_hom_app` and
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived_fac_app`.  What is left is the
chase `CategoryTheory.Adjunction.comparisonChase`.

*The two universal properties are read at spellings that differ definitionally.*  The comparison
of the derived pullback is `Stacks.Homology.leftDerivedIsoMapDerivedCategory` at `i^*` and the
comparison of the derived pushforward is
`Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived` at `i_*`, while the adjunction is
stated in terms of `Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory`,
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison` and
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit`.  Both crossings are
paid once, in a `have` whose type is written out in the second spelling and whose proof is the
universal property in the first; afterwards only one spelling occurs and the rewrites fire.

*Only three exactness hypotheses appear.*  Left exactness of `i_*` is unconditional, `i_*` being a
right adjoint (`Stacks.ClosedImmersion.preservesFiniteLimits_modulePushforward`), so it is found by
instance search rather than assumed.

## References

* [Stacks Project, Lemma 20.28.6 (Tag 079W)](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Lemma 20.28.2 (Tag 06YJ)](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Section 17.6 (Tag 0096)](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Remark 20.28.3 (Tag 08HY)](https://stacks.math.columbia.edu/tag/08HY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (i : X ⟶ Y)
  [PreservesFiniteLimits (modulePullback i)] [PreservesFiniteColimits (modulePullback i)]
  [PreservesFiniteColimits (modulePushforward i)]

/-- The comparison `Ri_* ≅ D(i_*)` for a morphism of ringed spaces along which `i_*` is exact:
the inverse of `Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`, which exhibits
the degreewise functor as the chosen total right derived functor. -/
abbrev derivedPushforwardComparisonIso :
    (modulePushforward i).mapDerivedCategory ≅ derivedPushforward i :=
  Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived (modulePushforward i)

/-- The degreewise derived adjunction `D(i^*) ⊣ D(i_*)`, transported along the comparisons of the
two derived functors, satisfies the factorization of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_fac`.

This is `CategoryTheory.mapDerivedCategoryAdjunction_unit_app_Qh` read through the universal
properties of the two comparisons. -/
private theorem ofNatIso_mapDerivedCategory_unit_fac
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ)) :
    ((((modulePullbackPushforwardAdjunction i).mapDerivedCategory.ofNatIsoLeft
            (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i).symm).ofNatIsoRight
          (derivedPushforwardComparisonIso i)).unit.app (DerivedCategory.Qh.obj M)) ≫
        (derivedPushforward i).map ((derivedPullbackComparison i).app M) =
      DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction i).unit.app M) ≫
        (derivedPushforwardUnit i).app
          (((modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) := by
  have hα : (derivedPullbackComparison i).app M =
      (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i).hom.app
          (DerivedCategory.Qh.obj M) ≫
        (modulePullback i).mapDerivedCategoryFactorsh.hom.app M :=
    (Stacks.Homology.leftDerivedIsoMapDerivedCategory_hom_app (modulePullback i)
      (derivedPullback i) (derivedPullbackComparison i) M).symm
  have hβ : (derivedPushforwardUnit i).app
        (((modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) =
      (modulePushforward i).mapDerivedCategoryFactorsh.inv.app
          (((modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        (derivedPushforwardComparisonIso i).hom.app
          (DerivedCategory.Qh.obj
            (((modulePullback i).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) :=
    (Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived_fac_app
      (modulePushforward i) _).symm
  have hl : (modulePushforward i).mapDerivedCategory.map
          ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i).inv.app
            (DerivedCategory.Qh.obj M)) ≫
        (modulePushforward i).mapDerivedCategory.map
          ((DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i).hom.app
            (DerivedCategory.Qh.obj M)) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have hu := CategoryTheory.mapDerivedCategoryAdjunction_unit_app_Qh
    (modulePullbackPushforwardAdjunction i) M
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc]
  rw [hα, hβ]
  exact Adjunction.comparisonChase (derivedPushforwardComparisonIso i).hom _ _ _ _ _ _ hl hu

/-- **The derived adjunction of an exact pullback–pushforward pair is the degreewise one.**
For a morphism `i` of ringed spaces along which both `i^*` and `i_*` are exact, the adjunction
`Li^* ⊣ Ri_*` of [Stacks, Tag 079W] is the adjunction `D(i^*) ⊣ D(i_*)` induced degreewise by
`i^* ⊣ i_*`, transported along the comparison `Li^* ≅ D(i^*)` of
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory` and the comparison
`D(i_*) ≅ Ri_*` of `Stacks.ClosedImmersion.mapDerivedCategoryIsoTotalRightDerived`.

Both adjunctions have the same left and right functor, so they agree as soon as their units do,
and both units satisfy the factorization that pins down a transformation into the left derived
functor `Li^* ⋙ Ri_*`. -/
theorem derivedAdjunction_eq_ofNatIso_mapDerivedCategory :
    derivedAdjunction i =
      ((modulePullbackPushforwardAdjunction i).mapDerivedCategory.ofNatIsoLeft
          (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i).symm).ofNatIsoRight
        (derivedPushforwardComparisonIso i) := by
  have := comp_isLeftDerivedFunctor i
    (⊤ : ObjectProperty (HomotopyCategory (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ))) (hasResolutions_top Y) (pullbackInvertsQuasiIso_top i)
  refine Adjunction.eq_of_unit_comp_eq
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (derivedPullbackComparison i) _ _ fun M => ?_
  exact (derivedAdjunction_unit_fac i M).trans
    (ofNatIso_mapDerivedCategory_unit_fac i M).symm

/-- **The derived adjunction of an exact pullback–pushforward pair is the degreewise one**, with
the transport on the other side: reading `Li^* ⊣ Ri_*` through the comparisons `Li^* ≅ D(i^*)`
and `Ri_* ≅ D(i_*)` of the two derived functors with the degreewise ones gives exactly
`CategoryTheory.Adjunction.mapDerivedCategory` of the underived adjunction `i^* ⊣ i_*`.

This is the form the mates calculus consumes, `CategoryTheory.mateEquiv_mapDerivedCategory` being
stated for `CategoryTheory.Adjunction.mapDerivedCategory`. -/
theorem ofNatIso_derivedAdjunction_eq_mapDerivedCategory :
    ((derivedAdjunction i).ofNatIsoLeft
          (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i)).ofNatIsoRight
        (derivedPushforwardComparisonIso i).symm =
      (modulePullbackPushforwardAdjunction i).mapDerivedCategory :=
  Adjunction.ofNatIsoLeft_ofNatIsoRight_symm _ _ _ _
    (derivedAdjunction_eq_ofNatIso_mapDerivedCategory i)

/-- **The mate under two derived adjunctions of the derived image of a 2-square is the derived
image of its mate under the two underived adjunctions.**

The two horizontal edges of the square are the adjunctions `Lh^* ⊣ Rh_*` and `Li^* ⊣ Ri_*` of
[Stacks, Tag 079W], read through the comparisons of their four functors with the degreewise ones;
the two vertical edges are the degreewise pullbacks along `p` and `q`.

This is `ofNatIso_derivedAdjunction_eq_mapDerivedCategory` composed with
`CategoryTheory.mateEquiv_mapDerivedCategory`, and it is what the derived base change of
[Stacks, Tag 08HY] needs: that map is a mate for the derived adjunctions of [Stacks, Tag 079W],
while the mates calculus on derived categories is available only for the degreewise ones. -/
theorem mateEquiv_derivedAdjunction_eq_mapDerivedCategory {Z W : RingedSpace.{u, u}}
    (h : Z ⟶ W) (p : Y ⟶ W) (q : X ⟶ Z)
    [PreservesFiniteLimits (modulePullback h)] [PreservesFiniteColimits (modulePullback h)]
    [PreservesFiniteColimits (modulePushforward h)]
    [PreservesFiniteLimits (modulePullback p)] [PreservesFiniteColimits (modulePullback p)]
    [PreservesFiniteLimits (modulePullback q)] [PreservesFiniteColimits (modulePullback q)]
    (β : TwoSquare (modulePullback p) (modulePullback h) (modulePullback i)
      (modulePullback q)) :
    mateEquiv
        (((derivedAdjunction h).ofNatIsoLeft
              (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory h)).ofNatIsoRight
            (derivedPushforwardComparisonIso h).symm)
        (((derivedAdjunction i).ofNatIsoLeft
              (DerivedOpenImmersion.derivedPullbackIsoMapDerivedCategory i)).ofNatIsoRight
            (derivedPushforwardComparisonIso i).symm)
        β.mapDerivedCategory =
      (mateEquiv (modulePullbackPushforwardAdjunction h)
        (modulePullbackPushforwardAdjunction i) β).mapDerivedCategory := by
  rw [ofNatIso_derivedAdjunction_eq_mapDerivedCategory,
    ofNatIso_derivedAdjunction_eq_mapDerivedCategory]
  exact mateEquiv_mapDerivedCategory _ _ _

end

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
