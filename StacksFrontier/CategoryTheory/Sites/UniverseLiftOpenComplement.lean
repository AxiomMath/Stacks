module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportLongExact
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived

/-!
# The universe lift on the size-bounded small étale site, and the open complement

Let `B` be a big étale site and `X` a scheme of `B`. On the size-bounded small étale site
`SmallEtale.topology B X.obj X.property`, the universe lift
`L : Sheaf _ AddCommGrpCat.{u} ⥤ Sheaf _ AddCommGrpCat.{u + 1}` of abelian sheaves is exact and
carries injective sheaves to injective sheaves. For the inclusion `j : U ⟶ X` of the open
complement of a closed immersion `i : Z ⟶ X`, this file records how `L` interacts with the
functors `j^{-1}`, `j_*` and `Rᵖ j_*` through which [Stacks, Tag 0A45] is stated on that site.

* `j^{-1}` commutes with the lift. In the larger universe `j^{-1}` is the inverse image
  `AlgebraicGeometry.complementPullback`; in the smaller universe it is the direct image along
  post-composition with `j`, which is restriction of sections to objects over `U`. The two are
  identified by `AlgebraicGeometry.SmallEtale.openRestrictionIso`.
* `Rᵖ j_*` commutes with the lift in every degree, the direct image being along a continuous
  functor of sites.
* The unit `𝟭 ⟶ j_*j^{-1}` of the smaller universe, lifted, is the unit
  `AlgebraicGeometry.complementRestriction` of the larger one.

## Main results

* The lift is exact on the size-bounded small étale site: the general instances
  `Stacks.Sheaves.UniverseLift.uliftSheafFunctor_preservesFiniteLimits` and
  `Stacks.Sheaves.UniverseLift.uliftSheafFunctor_preservesFiniteColimits` apply there.
* `Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor_smallEtaleBounded` —
  the lift preserves injective abelian sheaves there, and
  `Stacks.Sheaves.UniverseLift.hasInjectiveResolutions_smallEtaleBounded` supplies injective
  resolutions in the smaller universe.
* `Stacks.Sheaves.UniverseLift.complementPullbackULiftIso` — `j^{-1}` commutes with the lift.
* `Stacks.Sheaves.UniverseLift.rightDerivedComplementPushforwardULiftIso` — `Rᵖ j_*` commutes
  with the lift.
* `Stacks.Sheaves.UniverseLift.whiskerRight_complementAdjunctionULift_unit_comp` — the lifted
  unit of `j^{-1} ⊣ j_*` is `AlgebraicGeometry.complementRestriction`.

## Implementation notes

The Grothendieck property of abelian sheaves in the smaller universe has to be supplied by name,
`AlgebraicGeometry.SmallEtale.isGrothendieckAbelian_sheaf`, rather than left to instance search.
Once `StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors` is in
scope, its global instance `Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale` (at
the coefficient universe `max (u + 1) v`) is tried for the universe `u` as well, and instance
search then stops at the unsolvable universe constraint `u =?= max (u + 1) ?v` instead of moving
on. The same applies on Mathlib's small étale site, which is why
`Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor_smallEtale` names
Mathlib's instance.

## References

* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Sheaves.UniverseLift

variable (B : BigEtaleSite.{u})

section Site

variable (X : B.Scheme)

/-- **On the size-bounded small étale site, the universe lift of abelian sheaves from `u` to
`u + 1` preserves injective objects.** -/
instance preservesInjectiveObjects_uliftSheafFunctor_smallEtaleBounded :
    (uliftSheafFunctor.{u + 1, u}
      (SmallEtale.topology B X.obj X.property)).PreservesInjectiveObjects :=
  have : HasSeparator (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u}) :=
    @IsGrothendieckAbelian.hasSeparator.{u} _ _ _
      (SmallEtale.isGrothendieckAbelian_sheaf B X.obj X.property)
  preservesInjectiveObjects_uliftSheafFunctor_of_hasSeparator.{u + 1, u + 1, u} _

/-- Abelian sheaves on the size-bounded small étale site in the smaller universe have injective
resolutions, being a Grothendieck abelian category. -/
instance hasInjectiveResolutions_smallEtaleBounded :
    HasInjectiveResolutions (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u}) :=
  have := SmallEtale.isGrothendieckAbelian_sheaf B X.obj X.property
  inferInstance

end Site

section Complement

variable {Z X : B.Scheme} (i : Z ⟶ X) [IsClosedImmersion (B.inclusion.map i)]

/-- Restriction of abelian sheaves in the smaller universe to the open complement of a closed
immersion: the direct image along post-composition with its inclusion `j`, so that sections
over an object `W` of the complement are sections over `W`, viewed over `X`. -/
abbrev complementRestrictionULift :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u} ⥤
      Sheaf (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property)
        AddCommGrpCat.{u} :=
  (SmallEtale.openPostcompose B (closedComplementInclusion B i)).sheafPushforwardContinuous
    AddCommGrpCat.{u}
    (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property)
    (SmallEtale.topology B X.obj X.property)

/-- Direct image of abelian sheaves in the smaller universe along the inclusion `j` of the open
complement of a closed immersion. -/
abbrev complementPushforwardULift :
    Sheaf (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property)
        AddCommGrpCat.{u} ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u} :=
  (smallEtaleBaseChange B (closedComplementInclusion B i)).sheafPushforwardContinuous
    AddCommGrpCat.{u} (SmallEtale.topology B X.obj X.property)
    (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property)

/-- The adjunction `j^{-1} ⊣ j_*` in the smaller universe, induced by the adjunction between
post-composition with `j` and base change along `j` on the sites. -/
abbrev complementAdjunctionULift :
    complementRestrictionULift B i ⊣ complementPushforwardULift B i :=
  Adjunction.sheafPushforwardContinuous
    (SmallEtale.openPostcomposeAdjunction B (closedComplementInclusion B i))
    (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property)
    (SmallEtale.topology B X.obj X.property)

/-- **Restriction to the open complement commutes with the universe lift**: `j^{-1}` of the lift
of an abelian sheaf is the lift of its restriction. -/
def complementPullbackULiftIso :
    complementRestrictionULift B i ⋙
        uliftSheafFunctor.{u + 1, u}
          (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property) ≅
      uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B X.obj X.property) ⋙
        complementPullback B i :=
  Functor.isoWhiskerLeft (uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B X.obj X.property))
    (SmallEtale.openRestrictionIso.{u, 0} B (closedComplementInclusion B i))

/-- **Direct image to the ambient scheme commutes with the universe lift.** -/
def complementPushforwardULiftIso :
    complementPushforwardULift B i ⋙
        uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B X.obj X.property) ≅
      uliftSheafFunctor.{u + 1, u}
          (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property) ⋙
        complementPushforward B i :=
  sheafPushforwardContinuousULiftIso _ _ _

/-- **The higher direct images along the inclusion of the open complement commute with the
universe lift**: `Rᵖ j_*` of the lift of an abelian sheaf is the lift of `Rᵖ j_*`, in every
degree `p`. -/
def rightDerivedComplementPushforwardULiftIso (p : ℕ) :
    (complementPushforwardULift B i).rightDerived p ⋙
        uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B X.obj X.property) ≅
      uliftSheafFunctor.{u + 1, u}
          (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property) ⋙
        (complementPushforward B i).rightDerived p :=
  rightDerivedSheafPushforwardContinuousULiftIso _ _ _ p

/-- **The unit of `j^{-1} ⊣ j_*` commutes with the universe lift**: the lift of the unit
`𝟭 ⟶ j_*j^{-1}` of the smaller universe, followed by the identifications of
`complementPullbackULiftIso` and `complementPushforwardULiftIso`, is the unit
`AlgebraicGeometry.complementRestriction` of the larger universe. -/
theorem whiskerRight_complementAdjunctionULift_unit_comp :
    Functor.whiskerRight (complementAdjunctionULift B i).unit
        (uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B X.obj X.property)) ≫
      Functor.whiskerRight (complementPullbackULiftIso B i).hom (complementPushforward B i) =
    Functor.whiskerLeft (uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B X.obj X.property))
      (complementRestriction B i) := by
  ext F : 2
  have h := congrArg
    (fun t ↦ t.app ((uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B X.obj X.property)).obj F))
    (Adjunction.unit_leftAdjointUniq_hom
      (Adjunction.sheafPushforwardContinuous (E := AddCommGrpCat.{u + 1})
        (SmallEtale.openPostcomposeAdjunction B (closedComplementInclusion B i))
        (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property)
        (SmallEtale.topology B X.obj X.property))
      ((smallEtaleBaseChange B (closedComplementInclusion B i)).sheafAdjunctionContinuous
        AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property)))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h ⊢
  rw [complementRestriction, ← h]
  rfl

end Complement

end Stacks.Sheaves.UniverseLift
