module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpPointTransport
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CompletionSituation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpCompletedLocalRings
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.StalkBaseChangePullback
public import StacksFrontier.RingTheory.Rig.AdicCompletionMap

/-!
# Points of the blowup of a local ring and of its completion

Let `A` be a Noetherian local ring with completion `A^`. The blowup of `Spec A^` in its maximal
ideal is the base change of the blowup of `Spec A` in its maximal ideal along the flat morphism
`Spec A^ ⟶ Spec A` ([Stacks, Tag 0805]); at a point lying over the closed point the completed
local rings of the two blowups agree ([Stacks, Tag 0BG5]). So the points of the two blowups over
the closed points correspond, with isomorphic completed local rings, hence with the same
regularity ([Stacks, Tag 07NY]).

The same is recorded for an isomorphism of local rings, which carries the blowup of one to the
blowup of the other.

## Main results

* `AlgebraicGeometry.exists_blowUp_adicCompletion_point_of_blowUp`: a point of the blowup of
  `Spec A` over the closed point has a point of the blowup of `Spec A^` over it with isomorphic
  completed local ring.
* `AlgebraicGeometry.exists_blowUp_point_of_blowUp_adicCompletion`: conversely.
* `AlgebraicGeometry.exists_blowUp_point_of_ringEquiv`: a point of the blowup of `Spec C` over
  the closed point gives a point of the blowup of `Spec D` for an isomorphism `C ≃+* D`, with
  isomorphic local rings.

## References

* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 0BG5](https://stacks.math.columbia.edu/tag/0BG5)
* [Stacks Project, Tag 07NY](https://stacks.math.columbia.edu/tag/07NY)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

section Completion

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The blowup of `Spec A^` in the maximal ideal is the base change of the blowup of `Spec A` in
the maximal ideal along `Spec A^ ⟶ Spec A`. -/
theorem exists_isPullback_blowUp_adicCompletion :
    ∃ k : blowUp (maximalIdealSheaf (AdicCompletion (maximalIdeal A) A)) ⟶
        blowUp (maximalIdealSheaf A),
      IsPullback (blowUpToBase (maximalIdealSheaf (AdicCompletion (maximalIdeal A) A))) k
        (specMapAdicCompletion A) (blowUpToBase (maximalIdealSheaf A)) := by
  have : Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson _
      (by rw [← Ideal.jacobson_bot]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have : Flat (specMapAdicCompletion A) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have key := exists_isPullback_blowUpToBase_comap (specMapAdicCompletion A)
    (maximalIdealSheaf A)
  rwa [comap_maximalIdealSheaf_specMapAdicCompletion] at key

/-- The completion morphism sends the closed point to the closed point. -/
theorem specMapAdicCompletion_closedPoint :
    specMapAdicCompletion A (closedPoint (AdicCompletion (maximalIdeal A) A)) = closedPoint A := by
  have : IsLocalHom (CommRingCat.ofHom
      (algebraMap A (AdicCompletion (maximalIdeal A) A))).hom :=
    inferInstanceAs (IsLocalHom (algebraMap A (AdicCompletion (maximalIdeal A) A)))
  exact AlgebraicGeometry.Spec_closedPoint

/-- **A point of the blowup of `Spec A` over the closed point lifts to the blowup of `Spec A^`,
with isomorphic completed local ring** ([Stacks, Tag 0805], [Stacks, Tag 0BG5]). -/
theorem exists_blowUp_adicCompletion_point_of_blowUp (z : blowUp (maximalIdealSheaf A))
    (hz : blowUpToBase (maximalIdealSheaf A) z = closedPoint A) :
    ∃ y : blowUp (maximalIdealSheaf (AdicCompletion (maximalIdeal A) A)),
      blowUpToBase (maximalIdealSheaf (AdicCompletion (maximalIdeal A) A)) y =
        closedPoint (AdicCompletion (maximalIdeal A) A) ∧
      Nonempty (AdicCompletion (maximalIdeal ((blowUp (maximalIdealSheaf A)).presheaf.stalk z))
          ((blowUp (maximalIdealSheaf A)).presheaf.stalk z) ≃+*
        AdicCompletion (maximalIdeal ((blowUp (maximalIdealSheaf
            (AdicCompletion (maximalIdeal A) A))).presheaf.stalk y))
          ((blowUp (maximalIdealSheaf (AdicCompletion (maximalIdeal A) A))).presheaf.stalk y)) := by
  obtain ⟨k, hsq⟩ := exists_isPullback_blowUp_adicCompletion A
  obtain ⟨y, hy1, hy2⟩ := Scheme.exists_preimage_of_isPullback hsq
    (closedPoint (AdicCompletion (maximalIdeal A) A)) z
    (by rw [hz]; exact specMapAdicCompletion_closedPoint A)
  obtain ⟨e, -⟩ := exists_adicCompletion_ringEquiv_stalkMap_of_isPullback A
    (maximalIdeal A).fg_of_isNoetherianRing (blowUpToBase (maximalIdealSheaf A)) k
    (blowUpToBase (maximalIdealSheaf (AdicCompletion (maximalIdeal A) A))) hsq.flip y z hy2
    (by rw [hz]; rfl)
  exact ⟨y, hy1, ⟨e⟩⟩

/-- **A point of the blowup of `Spec A^` over the closed point lies over a point of the blowup of
`Spec A` over the closed point, with isomorphic completed local ring.** -/
theorem exists_blowUp_point_of_blowUp_adicCompletion
    (y : blowUp (maximalIdealSheaf (AdicCompletion (maximalIdeal A) A)))
    (hy : blowUpToBase (maximalIdealSheaf (AdicCompletion (maximalIdeal A) A)) y =
      closedPoint (AdicCompletion (maximalIdeal A) A)) :
    ∃ z : blowUp (maximalIdealSheaf A),
      blowUpToBase (maximalIdealSheaf A) z = closedPoint A ∧
      Nonempty (AdicCompletion (maximalIdeal ((blowUp (maximalIdealSheaf A)).presheaf.stalk z))
          ((blowUp (maximalIdealSheaf A)).presheaf.stalk z) ≃+*
        AdicCompletion (maximalIdeal ((blowUp (maximalIdealSheaf
            (AdicCompletion (maximalIdeal A) A))).presheaf.stalk y))
          ((blowUp (maximalIdealSheaf (AdicCompletion (maximalIdeal A) A))).presheaf.stalk y)) := by
  obtain ⟨k, hsq⟩ := exists_isPullback_blowUp_adicCompletion A
  have hz : blowUpToBase (maximalIdealSheaf A) (k y) = closedPoint A := by
    have hw := congrArg (fun m => m.base y) hsq.w
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at hw
    rw [← hw, hy]
    exact specMapAdicCompletion_closedPoint A
  obtain ⟨e, -⟩ := exists_adicCompletion_ringEquiv_stalkMap_of_isPullback A
    (maximalIdeal A).fg_of_isNoetherianRing (blowUpToBase (maximalIdealSheaf A)) k
    (blowUpToBase (maximalIdealSheaf (AdicCompletion (maximalIdeal A) A))) hsq.flip y (k y) rfl
    (by rw [hz]; rfl)
  exact ⟨k y, hz, ⟨e⟩⟩

end Completion

/-- **A point of the blowup of `Spec C` over the closed point gives a point of the blowup of
`Spec D` over the closed point**, for an isomorphism `C ≃+* D`, with isomorphic local rings. -/
theorem exists_blowUp_point_of_ringEquiv {C D : Type u} [CommRing C] [IsLocalRing C]
    [CommRing D] [IsLocalRing D] (ε : C ≃+* D) (z : blowUp (maximalIdealSheaf C))
    (hz : blowUpToBase (maximalIdealSheaf C) z = closedPoint C) :
    ∃ w : blowUp (maximalIdealSheaf D), blowUpToBase (maximalIdealSheaf D) w = closedPoint D ∧
      Nonempty ((blowUp (maximalIdealSheaf D)).presheaf.stalk w ≃+*
        (blowUp (maximalIdealSheaf C)).presheaf.stalk z) := by
  have hcl : IsClosed ({closedPoint D} : Set (Spec (.of D))) :=
    IsLocalRing.isClosed_singleton_closedPoint D
  let e : C ≃+* (Spec (.of D)).presheaf.stalk (closedPoint D) :=
    ε.trans (stalkClosedPointIso (.of D)).commRingCatIsoToRingEquiv.symm
  obtain ⟨q, hq, ε', -, -⟩ := exists_blowUp_point_of_maximalIdealSheaf C
    (X := Spec (.of D)) (closedPoint D) hcl e z hz
  rw [← vanishingIdeal_closedPoint_eq_maximalIdealSheaf D hcl]
  exact ⟨q, hq, ⟨ε'⟩⟩

end AlgebraicGeometry

end
