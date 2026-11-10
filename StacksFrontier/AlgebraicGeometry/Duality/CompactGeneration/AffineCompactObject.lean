module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentPushforwardAdjoint
public import StacksFrontier.Homology.Perfect.Characterizing

/-!
# The structure sheaf is a compact object of `D_QCoh(𝒪_{Spec R})`

Let `R` be a commutative ring.
`AlgebraicGeometry.preservesColimitsOfShape_coyoneda_derivedTildeUnit` and
`AlgebraicGeometry.isZero_of_rightOrthogonal_shiftClosure_derivedTildeUnit` already say that
`𝒪_{Spec R}[0] = derivedTilde R (R[0])` is a compact generator of `D_QCoh(𝒪_{Spec R})` — the
affine case of [Stacks, Tag 09IS] — the first in the shape "`Hom(𝒪_{Spec R}[0], -)` commutes with
direct sums", the second in the shape "the family indexed by `PUnit` is a weak generator".

The duality machinery of `StacksFrontier/AlgebraicGeometry/Duality/RightAdjointPushforward/` does
not consume either shape. It asks for `CategoryTheory.IsCompactObject`, the *class* of
[Stacks, Tag 07LS], and for generation as
`CategoryTheory.ObjectProperty.IsWeakTriangulatedGenerator` of a `singleton` rather than of an
`ObjectProperty.ofObj` family. This file supplies both, so that a consumer over an affine base can
discharge the triple `E`, `hEc`, `hE` that
`Stacks.Duality.preservesCoproducts_rightAdjoint_of_isCompactObject_pushforward`
([Stacks, Tag 0A9R]) and
`Stacks.Duality.isIso_compareWithPullbackTensor_of_isIso_generators` ([Stacks, Tag 0A9U]) carry.

## The argument

Both statements are transports across the affine derived Spec–Γ equivalence of
[Stacks, Tag 06Z0], which this repository has unconditionally as the instance
`AlgebraicGeometry.derivedTilde_isEquivalence`.

For compactness: `R` is a compact projective object of `ModuleCat R`
(`StacksDraft.Perfect.isCompactObject_regularModule`), so `R[0]` is a compact object of `D(R)`
(`StacksDraft.Perfect.isCompactObject_derived_single`), and compactness is invariant under an
additive equivalence of categories
(`CategoryTheory.isCompactObject_iff_isCompactObject_obj`).

For generation: `ObjectProperty.ofObj` of a constant family indexed by a nonempty type has the
same objects as `ObjectProperty.singleton` of its single member, so the library's statement is the
one wanted after that identification. The identification is spelled out in the proof rather than
extracted, because
`StacksFrontier/CategoryTheory/Triangulated/CompactObjects/CompactGenerators.lean` already has it
as the private `ofObj_const_eq_singleton` and a second copy would be a duplicate.

## Main results

* `AlgebraicGeometry.isCompactObject_derivedTildeUnit` — `𝒪_{Spec R}[0]` is a compact object of
  `D_QCoh(𝒪_{Spec R})`, as the class `CategoryTheory.IsCompactObject`.
* `AlgebraicGeometry.isWeakTriangulatedGenerator_derivedTildeUnit` — the one-object family
  `{𝒪_{Spec R}[0]}` is a weak generator of `D_QCoh(𝒪_{Spec R})`, in the `singleton` spelling.
* `AlgebraicGeometry.exists_isCompactObject_isWeakTriangulatedGenerator` — the two together, as
  the existence of a compact weak generator of `D_QCoh(𝒪_{Spec R})`.

## Implementation notes

**No `@[stacks 09IS]` attribute is attached here, and none is possible here.** Tag 09IS is a
statement about a quasi-compact quasi-separated scheme and asserts in addition that the generator
is a *perfect* object; what is below is its affine case, and only the
compactness-and-generation half of it. The tag itself is registered in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/PerfectGeneratorInduction.lean`, on
`Stacks.DerivedQCoh.AnyModel.hasPerfectGenerator_of_qcqs` and on
`Stacks.DerivedQCoh.AnyModel.exists_isPerfect_isZero_iff_forall_hom_eq_zero`. That file runs the
induction principle [Stacks, Tag 08DR] with the inductive step
`Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_detection_of_prop`
(`…/DerivedQCoh/AnyModel/GenerationStepOnASubcategory.lean`), whose hypothesis `hret` is the
extension of a perfect object from a quasi-compact open, [Stacks, Tag 09IQ].

The inputs of that step are available beyond the affine case. 09IQ is **not** available only
for an affine scheme: it is proved unconditionally at a quasi-compact open of a quasi-compact
quasi-separated scheme, at the locally
small model, as `Stacks.DerivedQCoh.AnyModel.exists_isPerfect_retract_derivedRestrict` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AnyModel/PerfectSummandOfRestriction.lean`.
[Stacks, Tag 09IM] is **not** available only for a closed subset contained in the open:
`Stacks.Perfect.LiftingComplexes.exists_isPerfect_lift` of
`StacksFrontier/AlgebraicGeometry/Perfect/LiftingComplexes/General.lean` carries a general
`T : Set X`, closed with retrocompact complement. And [Stacks, Tag 08EK] **is** registered, on
`Spec A`, in `StacksFrontier/AlgebraicGeometry/DerivedQCoh/OpenLift/SupportedPerfectLift.lean`.

Nothing further is owed for 09IS. The induction is
`Stacks.DerivedQCoh.AnyModel.hasPerfectGenerator_of_qcqs`, run on the property of an open of `X`
that every open subscheme with that image has a perfect generator; its step is
`Stacks.DerivedQCoh.AnyModel.hasPerfectGenerator_of_two_opens`, and both summands of the
generator that step produces are perfect — `Q` by [Stacks, Tag 09IQ], and the Koszul summand
`K = Rj_{V*}K_V` by `Stacks.Koszul.TwoOpens.isPerfect_derivedPushforward_koszulObjectOn` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/KoszulSummandPerfect.lean`, which is
[Stacks, Tag 08DP]. Its two geometric hypotheses are
`isZero_derivedRestrict_derivedPushforward_koszulObjectOn` and
`isZero_of_rightOrthogonal_derivedPushforward_koszulObjectOn` of
`…/DerivedQCoh/KoszulDetectionTwoOpens.lean`. The passage from right orthogonality to the shifts
of the Koszul object to the invertibility of the unit is [Stacks, Tag 09IR], whose `(2) ⇒ (1)`
implication is proved and
tagged as `Stacks.Koszul.Truncation.isIso_unit_of_hom_koszulObject_eq_zero`
(`…/Duality/KoszulOrthogonality/AffineSituation.lean`), for `E` in `D_QCoh(𝒪_{Spec A})`. See also
the coverage note of
`StacksFrontier/AlgebraicGeometry/Duality/QuasiCoherentPushforwardAdjoint.lean`.

**The route does not go through
`Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_detection`**. Its hypothesis
`hdet` is quantified over *all* of `D(𝒪_Y)`, and the
docstring of `Stacks.Koszul.Truncation.isIso_unit_iff_hom_koszulObject_eq_zero` in
`…/Duality/KoszulOrthogonality/AffineSituation.lean` records in its own words that "`hdet` as
stated here is false, and this statement is therefore vacuous", with a discrete-valuation-ring
counterexample. The form the induction uses is
`isWeakTriangulatedGenerator_biprod_of_detection_of_prop`, which confines `hdet` to a class `A`
closed under cones and so, at `A = D_QCoh(𝒪_Y)`, asks exactly the quasi-coherence the source
assumes; `isWeakTriangulatedGenerator_biprod_of_openImmersion` fed from
`Stacks.Koszul.Truncation.isIso_unit_of_hom_koszulObject_eq_zero` is the equivalent route.

*Relation to `CompactGeneration/AffineGenerator.lean`.* That file proves the generation half of
the affine case by a different route — Koszul detection for the empty sequence — at the spelling
`(tilde.functor R).obj (ModuleCat.of R R)` placed in degree zero, and records the equivalence of
[Stacks, Tag 06Z0] as unavailable. The equivalence is in fact available, so the route below is
open to it; the two spellings of the structure sheaf are not identified here, and nothing below
depends on that file.

*The model of the derived categories.* The locally small one, as everywhere in this cluster: the
affine Spec–Γ equivalence is available at
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `ModuleCat.hasDerivedCategory` and at no
other, and compactness is therefore tested at `Type u`.

## References

* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 07LS](https://stacks.math.columbia.edu/tag/07LS)
* [Stacks Project, Tag 07LT](https://stacks.math.columbia.edu/tag/07LT)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty Opposite

universe u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u})

/-! ### Compactness -/

/-- **`𝒪_{Spec R}[0]` is a compact object of `D_QCoh(𝒪_{Spec R})`**, as the class
`CategoryTheory.IsCompactObject` of [Stacks, Tag 07LS] rather than as the commutation of
`Hom(𝒪_{Spec R}[0], -)` with direct sums that
`AlgebraicGeometry.preservesColimitsOfShape_coyoneda_derivedTildeUnit` supplies.

The regular module `R` is a compact projective object of `ModuleCat R`, so `R[0]` is a compact
object of `D(R)`; derived sheafification is an additive equivalence by [Stacks, Tag 06Z0], and
compactness is invariant under one. -/
theorem isCompactObject_derivedTildeUnit :
    IsCompactObject.{u} ((derivedTilde R).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) := by
  have hreg : IsCompactObject.{u} (ModuleCat.of R R) :=
    StacksDraft.Perfect.isCompactObject_regularModule
  have hsingle : IsCompactObject.{u}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) :=
    StacksDraft.Perfect.isCompactObject_derived_single _ 0
  exact (isCompactObject_iff_isCompactObject_obj (derivedTilde R) _).1 hsingle

/-! ### Generation in the `singleton` spelling -/

/-- **The one-object family `{𝒪_{Spec R}[0]}` is a weak generator of `D_QCoh(𝒪_{Spec R})`.** This
is `AlgebraicGeometry.isZero_of_rightOrthogonal_shiftClosure_derivedTildeUnit` with its
`ObjectProperty.ofObj` family, indexed by `PUnit`, replaced by the `ObjectProperty.singleton` of
its single member: the two properties hold of the same objects. -/
theorem isWeakTriangulatedGenerator_derivedTildeUnit :
    (ObjectProperty.singleton ((derivedTilde R).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R)))).IsWeakTriangulatedGenerator := by
  have he : ObjectProperty.ofObj (fun _ : PUnit.{u + 1} => (derivedTilde R).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) =
      ObjectProperty.singleton ((derivedTilde R).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) := by
    ext Y
    rw [ObjectProperty.ofObj_iff, ObjectProperty.singleton_iff]
    exact ⟨fun ⟨_, hi⟩ => hi, fun hE => ⟨PUnit.unit, hE⟩⟩
  intro K hK
  rw [← he] at hK
  exact isZero_of_rightOrthogonal_shiftClosure_derivedTildeUnit R K hK

/-! ### The two together -/

/-- **`D_QCoh(𝒪_{Spec R})` has a compact weak generator**, namely `𝒪_{Spec R}[0]`. This is the
affine case of [Stacks, Tag 09IS] in exactly the shape the duality machinery consumes it: it
supplies the triple `E`, `hEc`, `hE` of
`Stacks.Duality.preservesCoproducts_rightAdjoint_of_isCompactObject_pushforward`,
[Stacks, Tag 0A9R]. The perfectness of the generator, which 09IS also asserts, is not claimed. -/
theorem exists_isCompactObject_isWeakTriangulatedGenerator :
    ∃ E : Stacks.Duality.quasiCoherentDerivedCategory (Spec R),
      IsCompactObject.{u} E ∧ (ObjectProperty.singleton E).IsWeakTriangulatedGenerator :=
  ⟨_, isCompactObject_derivedTildeUnit R, isWeakTriangulatedGenerator_derivedTildeUnit R⟩

end AlgebraicGeometry

end
