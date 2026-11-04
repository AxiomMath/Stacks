module

public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportLongExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportSequence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite
public import StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact

/-!
# Injective abelian sheaves and the open complement of a closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes and let `j : U ⟶ X` be the inclusion of the
open complement. The sequence `0 ⟶ i_*ℋ_Z(ℐ) ⟶ ℐ ⟶ j_*(ℐ|_U) ⟶ 0` is short exact at an
injective abelian sheaf `ℐ` on `X_étale`: that is
`AlgebraicGeometry.supportedSectionsShortComplex_shortExact_of_injective`. This file supplies
what the long exact sequence of cohomology with support further needs of the open complement:
restriction to it preserves injective abelian sheaves, and `F ↦ j_*(F|_U)` is left exact and
additive.

## Main results

* `AlgebraicGeometry.preservesInjectiveObjects_smallEtaleSheafPullback` — inverse image of
  abelian sheaves along the structure morphism of an object of the small étale site preserves
  injective objects; at the open complement this is the base's instance
  `AlgebraicGeometry.preservesInjectiveObjects_complementPullback`.
* `AlgebraicGeometry.complementRestrictPush_preservesFiniteLimits` — the functor
  `F ↦ j_*(F|_U)` is left exact.

## Implementation notes

That restriction to the open complement preserves injectives is read off the slice equivalence
of [Stacks, Tag 03S3]: the inverse image along the structure morphism of an object `V` of the
small étale site of `X` is restriction to the localization of that site at `V`, transported
along the equivalence of the localized site with the small étale site of the scheme `V`
(`AlgebraicGeometry.smallEtaleSheafPullbackIsoPostcompose` together with the equality
`AlgebraicGeometry.overPullback_comp_sheafCongr_inverse`).  Restriction to a localized site
preserves injective abelian sheaves because its left adjoint, extension by zero, is left exact;
that is `Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback`, whose universe
hypothesis holds unconditionally at the small étale site.


## References

* [Stacks Project, Tag 0A45](https://stacks.math.columbia.edu/tag/0A45)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Inverse image along an étale morphism preserves injectives -/

section Injectives

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (V : SmallEtale B X hX)

/-- **Restriction to the localized site at an object `V` of the small étale site preserves
injective abelian sheaves.** This is
`Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback`, whose universe
hypothesis `UnivLE.{max u v, w}` is satisfied unconditionally here: the site has objects in
`Type (u + 1)` and morphisms in `Type u`, and the coefficients are `AddCommGrpCat.{u + 1}`. -/
public theorem preservesInjectiveObjects_overPullback_smallEtale :
    ((SmallEtale.topology B X hX).overPullback AddCommGrpCat.{u + 1} V
      ).PreservesInjectiveObjects :=
  Stacks.Cohomology.LocalizedSite.preservesInjectiveObjects_overPullback.{u, u + 1, u + 1}
    (SmallEtale.topology B X hX) V

/-- **Inverse image of abelian sheaves along the structure morphism of an object `V` of the
small étale site preserves injective objects.** That inverse image is restriction to the
localized site at `V`, read through the slice equivalence of Stacks 03S3; restriction to a
localized site preserves injectives because its left adjoint, extension by zero, is left
exact. -/
public theorem preservesInjectiveObjects_smallEtaleSheafPullback :
    ((smallEtaleBaseChange B V.obj.hom).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X hX)
      (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
      ).PreservesInjectiveObjects := by
  have := preservesInjectiveObjects_overPullback_smallEtale B X hX V
  have : (((smallEtaleEquivalenceOver B X hX V).sheafCongr
      (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
      ((SmallEtale.topology B X hX).over V) AddCommGrpCat.{u + 1}).inverse
      ).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      ((smallEtaleEquivalenceOver B X hX V).sheafCongr
        (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
        ((SmallEtale.topology B X hX).over V) AddCommGrpCat.{u + 1}).toAdjunction
  have key := smallEtaleSheafPullbackIsoPostcompose B X hX V AddCommGrpCat.{u + 1} ≪≫
    eqToIso (overPullback_comp_sheafCongr_inverse B X hX V AddCommGrpCat.{u + 1}).symm
  refine ⟨fun {I} hI => ?_⟩
  exact Injective.of_iso (key.app I).symm
    (inferInstanceAs (Injective
      (((SmallEtale.topology B X hX).overPullback AddCommGrpCat.{u + 1} V ⋙
        ((smallEtaleEquivalenceOver B X hX V).sheafCongr
          (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
          ((SmallEtale.topology B X hX).over V) AddCommGrpCat.{u + 1}).inverse).obj I)))

end Injectives

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)]

/-- The open complement of a closed immersion, as an object of the small étale site of the
ambient scheme: its structure morphism is the inclusion, which is étale because it is an open
immersion. -/
public def complementEtaleObj : SmallEtale B X.obj X.property :=
  ⟨Over.mk (closedComplementInclusion B i), by
    change Etale (closedComplementOpen B i).ι
    infer_instance⟩

/-- The functor `F ↦ j_*(F|_U)` of restriction to the open complement followed by direct
image, which is the target of `AlgebraicGeometry.complementRestriction`. -/
public abbrev complementRestrictPush :
    SmallEtaleAbelianSheaf B X ⥤ SmallEtaleAbelianSheaf B X :=
  (smallEtaleBaseChange B (closedComplementInclusion B i)).sheafPullback
      AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property) ⋙
    (smallEtaleBaseChange B (closedComplementInclusion B i)).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (closedComplement B i).obj (closedComplement B i).property)

/-- `F ↦ j_*(F|_U)` is left exact: restriction to the open complement is exact and direct
image is a right adjoint. -/
public instance complementRestrictPush_preservesFiniteLimits :
    PreservesFiniteLimits (complementRestrictPush B i) := by
  have : PreservesLimitsOfSize.{0, 0}
      ((smallEtaleBaseChange B (closedComplementInclusion B i)).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (closedComplement B i).obj
          (closedComplement B i).property)) :=
    ((smallEtaleBaseChange B (closedComplementInclusion B i)).sheafAdjunctionContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (closedComplement B i).obj
        (closedComplement B i).property)).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits
      ((smallEtaleBaseChange B (closedComplementInclusion B i)).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (closedComplement B i).obj
          (closedComplement B i).property)) :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  exact comp_preservesFiniteLimits _ _

/-- `F ↦ j_*(F|_U)` is additive. -/
public instance complementRestrictPush_additive :
    (complementRestrictPush B i).Additive :=
  inferInstance

end AlgebraicGeometry

end
