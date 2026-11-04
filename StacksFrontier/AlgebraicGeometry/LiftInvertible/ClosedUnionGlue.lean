module

public import StacksFrontier.AlgebraicGeometry.LiftInvertible.KerCover
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.ReducedTarget
public import StacksFrontier.AlgebraicGeometry.ClosedLift.Basic

/-!
# Tag 09NY

[Stacks, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY): an invertible module on a closed
subscheme of a scheme with Noetherian underlying space of dimension at most one is the pullback
of an invertible module on the ambient scheme — for an **arbitrary** ambient scheme, with no
reducedness and no condition on how the subscheme meets the irreducible components.

## The proof

`Stacks.LiftInvertible.closedUnionIdeal` is the ideal sheaf `i.ker ⊓ vanishingIdeal Y`, where
`Y` is the union of the irreducible components of `X` not contained in the image of `i`; its
closed subscheme is the scheme-theoretic union of `Z` with the reduced induced subscheme on `Y`.
Two facts about it are already proved:

* its closed immersion into `X` is **onto**
  (`Stacks.LiftInvertible.surjective_subschemeι_closedUnionIdeal`), so by
  `Stacks.LiftInvertible.picPullbackSurjective_of_closedUnionLift` Tag 09NY for `i` follows from
  Tag 09NY for the factorization `Stacks.LiftInvertible.closedUnionLift` of `i` through it;
* the overlap of `Z` with `Y` is a finite discrete set of closed points
  (`Stacks.LiftInvertible.discreteTopology_range_inter_complementaryClosed`).

So the two members of `Stacks.LiftInvertible.coverScheme`, lifted to the union, are a
two-member closed cover of it with discrete overlap, and the intersection of their kernel ideal
sheaves is `⊥` **by construction**: pushing forward along `subschemeι` takes it to
`closedUnionIdeal i` itself, which is that inclusion's kernel, and pushforward along
`subschemeι` is injective (`Stacks.IdealSheafData.eq_of_map_subschemeι_eq`). That is exactly the
hypothesis of
`Stacks.ClosedCoverKer.exists_invertible_of_closed_cover_discrete_intersections_of_iInf_ker`,
Tag 09NE with reducedness replaced by the cover being scheme-theoretic.

Reducedness is therefore never assumed anywhere: where
`Stacks.LiftInvertible.exists_modulePullback_iso_of_isReduced` needed `X` reduced so that the
set-theoretic two-member cover was a cover scheme-theoretically, here the ambient scheme is
*replaced* by the union, on which the same thing holds for free.

## Main results

* `Stacks.LiftInvertible.picPullbackSurjective_closedUnionLift`: the residue that
  `Stacks.LiftInvertible.picPullbackSurjective_of_closedUnionLift` left open.
* `Stacks.LiftInvertible.picPullbackSurjective_of_dimension_le_one`: **Tag 09NY**, in predicate
  form.
* `Stacks.LiftInvertible.exists_modulePullback_iso_of_isClosedImmersion_of_dimension_le_one`:
  **Tag 09NY** in its own `∃`-form.

## References

* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
* [Stacks Project, Tag 09NE](https://stacks.math.columbia.edu/tag/09NE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Set TopologicalSpace Topology
open CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

open Stacks.AlgebraicGeometry.Tag09NY (LiftsInvertibleModules)

namespace Stacks.LiftInvertible

variable {X Z : Scheme.{u}}

/-- The ideal sheaf of the scheme-theoretic union is below the kernel of **both** members of the
two-member cover: at `true` by `Stacks.LiftInvertible.closedUnionIdeal_le_ker`, at `false`
because the `false` member is the subscheme of `vanishingIdeal (complementaryClosed i)`, whose
kernel is that very ideal sheaf. -/
theorem closedUnionIdeal_le_ker_coverMap (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X]
    (b : Bool) : closedUnionIdeal i ≤ Scheme.Hom.ker (coverMap i b) := by
  cases b with
  | true => exact closedUnionIdeal_le_ker i
  | false =>
    show closedUnionIdeal i ≤
      Scheme.Hom.ker (vanishingIdeal (complementaryClosed i)).subschemeι
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact closedUnionIdeal_le_vanishingIdeal i

/-- **The two-member cover, lifted to the scheme-theoretic union.** At `true` this is
`Stacks.LiftInvertible.closedUnionLift`; the definition is uniform in the index because both
members' kernels contain the union's ideal sheaf. -/
noncomputable def coverLift (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X] (b : Bool) :
    coverScheme i b ⟶ (closedUnionIdeal i).subscheme :=
  IsClosedImmersion.lift (closedUnionIdeal i).subschemeι (coverMap i b)
    (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact closedUnionIdeal_le_ker_coverMap i b)

/-- Composing `coverLift i b` with the inclusion of the scheme-theoretic union gives
`coverMap i b`. -/
@[simp]
theorem coverLift_subschemeι (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X] (b : Bool) :
    coverLift i b ≫ (closedUnionIdeal i).subschemeι = coverMap i b :=
  IsClosedImmersion.lift_fac _ _ _

/-- At `true`, `coverLift i` is `Stacks.LiftInvertible.closedUnionLift i`. -/
theorem coverLift_true (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X] :
    coverLift i true = closedUnionLift i := rfl

/-- Each lifted member `coverLift i b` is a closed immersion into the scheme-theoretic union. -/
instance isClosedImmersion_coverLift (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X]
    (b : Bool) : IsClosedImmersion (coverLift i b) := by
  have h : IsClosedImmersion (coverLift i b ≫ (closedUnionIdeal i).subschemeι) := by
    rw [coverLift_subschemeι]
    infer_instance
  exact IsClosedImmersion.of_comp (coverLift i b) (closedUnionIdeal i).subschemeι

/-- **The intersection of the two members' kernels on `X` is the union's ideal sheaf**, which is
how `Stacks.LiftInvertible.closedUnionIdeal` was defined. -/
theorem iInf_ker_coverMap (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X] :
    (⨅ b, Scheme.Hom.ker (coverMap i b)) = closedUnionIdeal i := by
  rw [iInf_bool_eq]
  show Scheme.Hom.ker i ⊓
    Scheme.Hom.ker (vanishingIdeal (complementaryClosed i)).subschemeι = _
  rw [Scheme.IdealSheafData.ker_subschemeι]
  rfl

/-- **The cover of the union is a cover scheme-theoretically.** This is the hypothesis of
`Stacks.ClosedCoverKer.exists_invertible_of_closed_cover_discrete_intersections_of_iInf_ker`,
and on the scheme-theoretic union it holds **by construction**: pushing the intersection forward
along `subschemeι` gives `⨅ b, (coverMap i b).ker`, which is `closedUnionIdeal i`, which is the
kernel of `subschemeι`, i.e. the pushforward of `⊥`. Pushforward along `subschemeι` is injective
on ideal sheaves (`Stacks.IdealSheafData.eq_of_map_subschemeι_eq`), so the two agree. -/
theorem iInf_ker_coverLift (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X] :
    (⨅ b, Scheme.Hom.ker (coverLift i b)) = ⊥ := by
  refine Stacks.IdealSheafData.eq_of_map_subschemeι_eq (closedUnionIdeal i) ?_
  rw [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι,
    (Scheme.IdealSheafData.map_gc (closedUnionIdeal i).subschemeι).u_iInf]
  simp only [Scheme.IdealSheafData.map_ker, coverLift_subschemeι]
  exact iInf_ker_coverMap i

/-- The inclusion of the scheme-theoretic union sends `coverLift i b z` to `coverMap i b z`. -/
private theorem subschemeι_coverLift_apply (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X]
    (b : Bool) (z : coverScheme i b) :
    (closedUnionIdeal i).subschemeι ((coverLift i b) z) = (coverMap i b) z :=
  congrArg (fun q ↦ q.base z) (coverLift_subschemeι i b)

/-- **The lifted members cover the union**: the union has the same underlying space as `X`
(`Stacks.LiftInvertible.coe_support_closedUnionIdeal`), the members cover `X` by
`Stacks.LiftInvertible.exists_coverMap_eq`, and `subschemeι` is injective. -/
theorem exists_coverLift_eq (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X]
    (x : (closedUnionIdeal i).subscheme) : ∃ (b : Bool) (z : coverScheme i b),
      (coverLift i b) z = x := by
  obtain ⟨b, z, hz⟩ := exists_coverMap_eq i ((closedUnionIdeal i).subschemeι x)
  refine ⟨b, z, ?_⟩
  apply (IsClosedImmersion.isClosedEmbedding (closedUnionIdeal i).subschemeι).injective
  exact (subschemeι_coverLift_apply i b z).trans hz

/-- The lifted members still meet in a discrete space: `subschemeι` is a closed embedding
carrying their intersection into the intersection of the images in `X`, which is discrete by
`Stacks.LiftInvertible.discreteTopology_range_coverMap_inter`. -/
theorem discreteTopology_range_coverLift_inter (i : Z ⟶ X) [IsClosedImmersion i]
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1) (b b' : Bool) (hbb' : b ≠ b') :
    DiscreteTopology
      ((Set.range (coverLift i b).base ∩ Set.range (coverLift i b').base :
        Set ((closedUnionIdeal i).subscheme : Type u))) := by
  have _ : DiscreteTopology
      ((Set.range (coverMap i b).base ∩ Set.range (coverMap i b').base : Set (X : Type u))) :=
    discreteTopology_range_coverMap_inter i hdim b b' hbb'
  have hemb : Topology.IsEmbedding (closedUnionIdeal i).subschemeι.base :=
    (IsClosedImmersion.isClosedEmbedding (closedUnionIdeal i).subschemeι).isEmbedding
  have hmaps : Set.MapsTo (closedUnionIdeal i).subschemeι.base
      (Set.range (coverLift i b).base ∩ Set.range (coverLift i b').base)
      (Set.range (coverMap i b).base ∩ Set.range (coverMap i b').base) := by
    rintro x ⟨⟨z, hz⟩, ⟨z', hz'⟩⟩
    exact ⟨⟨z, (subschemeι_coverLift_apply i b z).symm.trans (congrArg _ hz)⟩,
      ⟨z', (subschemeι_coverLift_apply i b' z').symm.trans (congrArg _ hz')⟩⟩
  exact (Topology.IsEmbedding.restrict hemb hmaps).discreteTopology

/-- **The residue of Tag 09NY, proved.** Every invertible module on `Z` is the pullback of an
invertible module on the scheme-theoretic union of `Z` with the components of `X` it misses.

This is exactly the hypothesis that
`Stacks.LiftInvertible.picPullbackSurjective_of_closedUnionLift` carried, and it is Tag 09NE
on the two-member cover of the union — legitimate there, and not on `X`, because the cover of
the union is a cover scheme-theoretically (`Stacks.LiftInvertible.iInf_ker_coverLift`) while the
cover of `X` is only a cover set-theoretically. -/
theorem picPullbackSurjective_closedUnionLift (i : Z ⟶ X) [IsClosedImmersion i]
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1) :
    LiftsInvertibleModules (closedUnionLift i) := by
  intro L hL
  have hinv : ∀ b, AlgebraicGeometry.SheafOfModules.IsInvertible (coverScheme i b).presheaf
      (coverScheme i b).ringCatSheaf.2 (coverModule i L b) := by
    intro b
    cases b with
    | true => exact hL
    | false =>
      exact (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
        (Stacks.SheafOfModules.isInvertible_unit _ _)
  obtain ⟨M, hM, hMpull⟩ :=
    Stacks.ClosedCoverKer.exists_invertible_of_closed_cover_discrete_intersections_of_iInf_ker
      (closedUnionIdeal i).subscheme (coverScheme i) (coverLift i) (exists_coverLift_eq i)
      (discreteTopology_range_coverLift_inter i hdim) (iInf_ker_coverLift i) (coverModule i L)
  exact ⟨M, hM, hMpull true⟩

/-- **Tag 09NY**, in predicate form: for a closed immersion into a scheme with Noetherian
underlying space of dimension at most one, every invertible module on the source is the pullback
of an invertible module on the target. No reducedness, and no hypothesis on how the image meets
the irreducible components. -/
theorem picPullbackSurjective_of_dimension_le_one (i : Z ⟶ X) [IsClosedImmersion i]
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1) : LiftsInvertibleModules i :=
  picPullbackSurjective_of_closedUnionLift i hdim (picPullbackSurjective_closedUnionLift i hdim)

/-- An invertible module on a closed subscheme of a scheme whose underlying space is Noetherian
and has dimension at most one is the pullback of an invertible module on the ambient scheme. -/
@[stacks 09NY]
theorem exists_modulePullback_iso_of_isClosedImmersion_of_dimension_le_one
    (X Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Z.IsSheaf) L] :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) :=
  let ⟨M, hM, hiso⟩ := picPullbackSurjective_of_dimension_le_one i hdim L ‹_›
  ⟨M, hM, hiso⟩

end Stacks.LiftInvertible

end
