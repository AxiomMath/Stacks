module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjFinitePresentation.GradedBaseChange
public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayFlatOverBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite presentation of the structure morphism of a relative homogeneous spectrum

Let `S` be a scheme carrying a quasi-coherent, commutative, nonnegatively graded `𝒪_S`-algebra
`A` of finite presentation, in the sense that the canonical map `Γ(S, U) → A(U)` is a ring
homomorphism of finite presentation for every affine open `U` of `S`. Then the structure
morphism `p : Proj_S(A) ⟶ S` of the relative homogeneous spectrum is of finite presentation:
locally of finite presentation, quasi-compact and quasi-separated. This is the first of the two
assertions of Stacks tag 0D4D.

Being locally of finite presentation is Zariski-local on the target, and over an affine open `U`
of the base the chart square identifies the restriction of `p` with the chart's own structure
morphism `Proj A(U) ⟶ Spec Γ(S, U) ≅ U`, which is locally of finite presentation by
`Stacks.AlgebraicGeometry.Proj.locallyOfFinitePresentation_projToSpec`. Quasi-compactness is the
finite-type statement of tag 07ZY, applied to the finite type homomorphisms underlying the
finitely presented ones, and quasi-separatedness follows from separatedness of `p`, which holds
for every quasi-coherent graded algebra.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjFinitePresentation.locallyOfFinitePresentation_toBase`:
  the structure morphism of the relative homogeneous spectrum of a finitely presented
  quasi-coherent graded algebra is locally of finite presentation.
* `Stacks.AlgebraicGeometry.RelativeProjFinitePresentation.finitePresentation_toBase`: that
  structure morphism is of finite presentation. This is the first assertion of Stacks tag 0D4D.

## The other assertion of the tag, and where the registrations are

Stacks tag 0D4D asserts two things: that `p` is of finite presentation, and that every twist
`𝒪_X(d)` on the relative homogeneous spectrum is an `𝒪_X`-module of finite presentation. The
first is proved here; the second is
`Stacks.AlgebraicGeometry.RelativeProjFinitePresentation.isFinitePresentation_relativeProjTwist`
in `StacksFrontier.AlgebraicGeometry.RelativeProjFinitePresentation.GluedTwists`, which states it
for the twists `𝒪_X(d)` of `A` itself — the homogeneous pieces of Tag 01NR's twist datum
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`. That is the whole covering
set, so each half carries the tag: that declaration carries
`@[stacks 0D4D "twists_finite_presentation"]` directly, while the registration for this half is
an `add_to_stacks` command in
`StacksFrontier.AlgebraicGeometry.RelativeProjFinitePresentation.TwistFinitePresentation`,
`@[stacks ...]` being unavailable here for want of the import.

## Implementation notes

`Stacks.AlgebraicGeometry.Proj.locallyOfFinitePresentation_projToSpec` is stated for a grading by
`Γ(S, U)`-submodules, while the graded ring of sections is graded by additive subgroups. The two
gradings have the same members, by `GradedRing.toSubmodules`, and the resulting identification of
projective spectra is `Stacks.GradedRegrading.projIso`; its degree-zero edge turns the structure
map of the submodule grading into the degree-zero projection of the structure map of the graded
algebra, which is
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.toGradeZero_eq`.

The graded ring of sections is a direct sum, so besides the `Γ(S, U)`-algebra structure defined
by its structure map it carries a summandwise `Γ(S, U)`-module structure, and the two agree only
propositionally. The algebra structure used is therefore always
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionRingAlgebra`, installed by
`let`, rather than left to instance search.

`AlgebraicGeometry.LocallyOfFinitePresentation` carries neither a
`AlgebraicGeometry.IsZariskiLocalAtTarget` nor a `CategoryTheory.MorphismProperty` `RespectsIso`
instance; both are produced by hand from its `AlgebraicGeometry.HasRingHomProperty` structure.

## References

* [Stacks Project, Tag 0D4D](https://stacks.math.columbia.edu/tag/0D4D)
* [Stacks Project, Tag 07ZY](https://stacks.math.columbia.edu/tag/07ZY)
* [Stacks Project, Tag 01TP](https://stacks.math.columbia.edu/tag/01TP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjFinitePresentation

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

include A in
/-- The chart of the relative homogeneous spectrum over an affine open on which the graded ring
of sections is a finitely presented algebra is locally of finite presentation over that open.
This is the affine case of the first assertion of Stacks tag 0D4D, read through the chart. -/
private theorem locallyOfFinitePresentation_projInclusionToOpen (U : S.Opens)
    (hU : IsAffineOpen U) (hfp : (A.strHom U).FinitePresentation) :
    LocallyOfFinitePresentation (projInclusionToOpen A U hU) := by
  let _ := A.sectionRingAlgebra U
  let _ : Algebra.FinitePresentation Γ(S, U) (A.sectionRing U) :=
    RingHom.finitePresentation_algebraMap.mp hfp
  have hcar : ∀ i, (A.grading U i : Set (A.sectionRing U)) =
      GradedRing.toSubmodules (A.grading U) (A.strHom_mem U) i := fun _ => rfl
  have hcoe : ∀ r : Γ(S, U),
      ((((GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U)) r :
        A.grading U 0) : A.sectionRing U) = algebraMap Γ(S, U) (A.sectionRing U) r := by
    intro r
    rw [← A.toGradeZero_eq U]
    exact GradedRing.coe_toGradeZero_apply (A.grading U) (A.strHom_mem U) r
  have hzero : (Stacks.GradedRegrading.regrade hcar).gradedZeroRingHom.comp
      ((GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U)) =
      algebraMap Γ(S, U) (GradedRing.toSubmodules (A.grading U) (A.strHom_mem U) 0) :=
    RingHom.ext fun r => Subtype.ext (hcoe r)
  have hspec : Spec.map (CommRingCat.ofHom
        (Stacks.GradedRegrading.regrade hcar).gradedZeroRingHom) ≫
      Spec.map (CommRingCat.ofHom
        ((GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U))) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U)
        (GradedRing.toSubmodules (A.grading U) (A.strHom_mem U) 0))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hzero]
  have hdef : projInclusionToOpen A U hU =
      AlgebraicGeometry.Proj.toSpecZero (A.grading U) ≫
        Spec.map (CommRingCat.ofHom
          ((GradedRing.projZeroRingHom' (A.grading U)).comp (A.strHom U))) ≫
            hU.isoSpec.inv := rfl
  have hcomp : (Stacks.GradedRegrading.projIso hcar).hom ≫ projInclusionToOpen A U hU =
      (AlgebraicGeometry.Proj.toSpecZero
          (GradedRing.toSubmodules (A.grading U) (A.strHom_mem U)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U)
          (GradedRing.toSubmodules (A.grading U) (A.strHom_mem U) 0)))) ≫ hU.isoSpec.inv := by
    rw [hdef, ← Category.assoc, Stacks.GradedRegrading.projIso_hom_comp_toSpecZero hcar,
      ← hspec]
    simp only [Category.assoc]
  have hrio : MorphismProperty.RespectsIso @LocallyOfFinitePresentation := by
    rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation]
    exact affineLocally_respectsIso _ RingHom.finitePresentation_respectsIso
  refine (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFinitePresentation
    (Stacks.GradedRegrading.projIso hcar).hom _).1 ?_
  rw [hcomp]
  exact (MorphismProperty.cancel_right_of_respectsIso @LocallyOfFinitePresentation _
    hU.isoSpec.inv).2 (Stacks.AlgebraicGeometry.Proj.locallyOfFinitePresentation_projToSpec
      (GradedRing.toSubmodules (A.grading U) (A.strHom_mem U)))

include A in
/-- **Stacks 0D4D, first assertion.** The structure morphism of the relative homogeneous
spectrum of a finitely presented quasi-coherent graded algebra is locally of finite
presentation. -/
@[ega "II 3.1.3" "special case", ega "II 4.6.18" "partial"]
public theorem locallyOfFinitePresentation_toBase
    (hA : ∀ U : S.Opens, IsAffineOpen U → (A.strHom U).FinitePresentation) :
    LocallyOfFinitePresentation (relativeProj A).toBase := by
  have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation)
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation)
    (fun V : S.affineOpens => (V : S.Opens)) (iSup_affineOpens_eq_top S)]
  intro V
  have hchart := (relativeProj A).chart_isPullback (V : S.Opens) V.2
  have hrestrict := (isPullback_morphismRestrict (relativeProj A).toBase (V : S.Opens)).flip
  have he : (hchart.isoIsPullback _ _ hrestrict).inv ≫
      projInclusionToOpen A (V : S.Opens) V.2 = (relativeProj A).toBase ∣_ (V : S.Opens) :=
    hchart.isoIsPullback_inv_snd _ _ hrestrict
  have : LocallyOfFinitePresentation (projInclusionToOpen A (V : S.Opens) V.2) :=
    locallyOfFinitePresentation_projInclusionToOpen A (V : S.Opens) V.2 (hA _ V.2)
  rw [← he]
  infer_instance

include A in
/-- The structure morphism of the relative homogeneous spectrum of a finitely presented
quasi-coherent graded algebra is of finite presentation: locally of finite presentation,
quasi-compact and quasi-separated.

This is the first of the two assertions of Stacks tag 0D4D, and it carries
`@[stacks 0D4D "relative_proj_finite_presentation"]`: the attribute is attached by an
`add_to_stacks` command in
`StacksFrontier.AlgebraicGeometry.RelativeProjFinitePresentation.TwistFinitePresentation`. The
second assertion — that every twist `𝒪_X(d)` on the relative homogeneous spectrum is of finite
presentation — reduced to one absolute statement in commutative algebra, finite presentation of
the degree-zero part of the twisted localization, which is proved as
`Stacks.ProjTwistFinitePresentation.isFinitePresentation_twistingSheaf`; it is registered on
`Stacks.AlgebraicGeometry.RelativeProjFinitePresentation.isFinitePresentation_relativeProjTwist`
in `StacksFrontier.AlgebraicGeometry.RelativeProjFinitePresentation.GluedTwists`, so the covering
set is complete. -/
@[ega "II 3.1.3" "special case",
  ega "II 3.4.1" "special case",
  ega "II 4.6.18" "f is of finite type"]
public theorem finitePresentation_toBase
    (hA : ∀ U : S.Opens, IsAffineOpen U → (A.strHom U).FinitePresentation) :
    AlgebraicGeometry.FinitePresentation (relativeProj A).toBase := by
  have hsft : RelativeProjFiniteType.IsFiniteType A := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU, RingHom.FiniteType.of_finitePresentation (hA U hU)⟩
  have : IsSeparated (relativeProj A).toBase :=
    RelativeProjSeparated.isSeparated_toBase A (relativeProj A)
  exact AlgebraicGeometry.FinitePresentation.mk
    (locallyOfFinitePresentation_toBase A hA)
    (RelativeProjFiniteType.quasiCompact_toBase A hsft) inferInstance

end Stacks.AlgebraicGeometry.RelativeProjFinitePresentation

end
