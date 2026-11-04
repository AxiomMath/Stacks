module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CompletionSituation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpSingularPoints
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.StageSituation

/-!
# Comparing the blowups of rational double points with isomorphic completions

The local rings at the closed points of the blowup of `Spec(A)` in the maximal ideal have the
completions of the local rings of the blowup of `Spec(A^)` ([Stacks, Tag 0BG5]), the latter being
the base change of the former ([Stacks, Tag 0805]). So for two rational double points with
isomorphic completions, the singular points of their blowups correspond, with isomorphic
completed local rings.

## Main results

* `AlgebraicGeometry.exists_iso_blowUp_maximalIdealSheaf_of_ringEquiv`: a ring isomorphism of local
  rings induces an isomorphism of the blowups in the maximal ideals.
* `RationalDoublePointSituation.exists_hom_blowUp_completion`: the blowup of `Spec(A^)` maps to
  the blowup of `Spec(A)`, onto the points over the closed point, with isomorphic completed local
  rings.
* `RationalDoublePointSituation.exists_mem_singularLocus_of_completion_ringEquiv`: for rational
  double points with isomorphic completions, every singular point of the one blowup has a singular
  point of the other with an isomorphic completed local ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A ring isomorphism of local rings induces an isomorphism of the blowups in the maximal
ideals**, over `Spec` of the isomorphism. -/
theorem exists_iso_blowUp_maximalIdealSheaf_of_ringEquiv {A B : Type u} [CommRing A]
    [IsLocalRing A] [CommRing B] [IsLocalRing B] (e : A ≃+* B) :
    ∃ k : blowUp (maximalIdealSheaf B) ≅ blowUp (maximalIdealSheaf A),
      k.hom ≫ blowUpToBase (maximalIdealSheaf A) =
        blowUpToBase (maximalIdealSheaf B) ≫ Spec.map (CommRingCat.ofHom (e : A →+* B)) := by
  have : IsIso (CommRingCat.ofHom (e : A →+* B)) := e.toCommRingCatIso.isIso_hom
  rw [← comap_maximalIdealSheaf_specMap_ringEquiv e]
  obtain ⟨k, hsq⟩ := exists_isPullback_blowUpToBase_comap
    (Spec.map (CommRingCat.ofHom (e : A →+* B))) (maximalIdealSheaf A)
  have : IsIso k := hsq.isIso_snd_of_isIso
  exact ⟨asIso k, hsq.w.symm⟩

/-- The spectrum of a local homomorphism of local rings maps the closed point to the closed
point. -/
private theorem base_spec_map_closedPoint {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    (Spec.map (CommRingCat.ofHom f)).base (IsLocalRing.closedPoint B) =
      IsLocalRing.closedPoint A :=
  Spec_closedPoint (f := CommRingCat.ofHom f)

namespace RationalDoublePointSituation

variable (S : RationalDoublePointSituation.{u})

/-- **The blowup of the completion over the blowup.** There is a morphism from the blowup of
`Spec(A^)` in its maximal ideal to the blowup of `Spec(A)` in its maximal ideal, which maps the
points over the closed point onto the points over the closed point, with isomorphic completed
local rings ([Stacks, Tags 0805 and 0BG5]). -/
theorem exists_hom_blowUp_completion (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] :
    ∃ pr : blowUp (maximalIdealSheaf (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ⟶
        blowUp (maximalIdealSheaf A),
      (∀ y, blowUpToBase _ y =
          IsLocalRing.closedPoint (AdicCompletion (IsLocalRing.maximalIdeal A) A) →
        blowUpToBase (maximalIdealSheaf A) (pr y) = IsLocalRing.closedPoint A ∧
        Nonempty (AdicCompletion (IsLocalRing.maximalIdeal
            ((blowUp (maximalIdealSheaf A)).presheaf.stalk (pr y)))
            ((blowUp (maximalIdealSheaf A)).presheaf.stalk (pr y)) ≃+*
          AdicCompletion (IsLocalRing.maximalIdeal ((blowUp (maximalIdealSheaf
            (AdicCompletion (IsLocalRing.maximalIdeal A) A))).presheaf.stalk y))
            ((blowUp (maximalIdealSheaf
              (AdicCompletion (IsLocalRing.maximalIdeal A) A))).presheaf.stalk y))) ∧
      (∀ x, blowUpToBase (maximalIdealSheaf A) x = IsLocalRing.closedPoint A →
        ∃ y, pr y = x ∧ blowUpToBase _ y =
          IsLocalRing.closedPoint (AdicCompletion (IsLocalRing.maximalIdeal A) A)) := by
  have : Module.FaithfullyFlat A (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson _
      (by rw [← Ideal.jacobson_bot]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥)
  have : Flat (specMapAdicCompletion A) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  rw [← comap_maximalIdealSheaf_specMapAdicCompletion]
  obtain ⟨pr, hsq⟩ := exists_isPullback_blowUpToBase_comap
    (specMapAdicCompletion A) (maximalIdealSheaf A)
  have hcp : (specMapAdicCompletion A).base
      (IsLocalRing.closedPoint (AdicCompletion (IsLocalRing.maximalIdeal A) A)) =
      IsLocalRing.closedPoint A :=
    base_spec_map_closedPoint (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
  have hcomm : ∀ y, blowUpToBase (maximalIdealSheaf A) (pr y) =
      (specMapAdicCompletion A).base
        (blowUpToBase ((maximalIdealSheaf A).comap (specMapAdicCompletion A)) y) := by
    intro y
    simpa [Scheme.Hom.comp_apply] using (congrArg (fun t => t.base y) hsq.w).symm
  refine ⟨pr, fun y hy => ?_, fun x hx => ?_⟩
  · have hxo : blowUpToBase (maximalIdealSheaf A) (pr y) = IsLocalRing.closedPoint A := by
      rw [hcomm, hy, hcp]
    obtain ⟨e, -⟩ := exists_adicCompletion_ringEquiv_stalkMap_of_isPullback A
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing (blowUpToBase (maximalIdealSheaf A)) pr
      (blowUpToBase ((maximalIdealSheaf A).comap (specMapAdicCompletion A)))
      hsq.flip y (pr y) rfl (by rw [hxo]; rfl)
    exact ⟨hxo, ⟨e⟩⟩
  · obtain ⟨y, hy, hyx⟩ := Scheme.exists_preimage_of_isPullback hsq
      (IsLocalRing.closedPoint (AdicCompletion (IsLocalRing.maximalIdeal A) A)) x
      (by rw [hcp, hx])
    exact ⟨y, hyx, hy⟩

/-- **Rational double points with isomorphic completions have blowups with corresponding singular
points.** If the completions of the rings of `S` and `S'` are isomorphic, every singular point of
the blowup of `Spec(S'.A)` in its maximal ideal has a singular point of the blowup of `Spec(S.A)`
with an isomorphic completed local ring. -/
theorem exists_mem_singularLocus_of_completion_ringEquiv (S S' : RationalDoublePointSituation.{u})
    (E : AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A ≃+*
      AdicCompletion (IsLocalRing.maximalIdeal S'.A) S'.A)
    (x' : blowUp (maximalIdealSheaf S'.A))
    (hx' : x' ∈ singularLocus (blowUp (maximalIdealSheaf S'.A))) :
    ∃ x : blowUp (maximalIdealSheaf S.A), x ∈ singularLocus (blowUp (maximalIdealSheaf S.A)) ∧
      Nonempty (AdicCompletion (IsLocalRing.maximalIdeal
          ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x))
          ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal
          ((blowUp (maximalIdealSheaf S'.A)).presheaf.stalk x'))
          ((blowUp (maximalIdealSheaf S'.A)).presheaf.stalk x')) := by
  have hx'o := S'.blowUpToBase_eq_closedPoint_of_mem_singularLocus x' hx'
  obtain ⟨pr', hpr'1, hpr'2⟩ := exists_hom_blowUp_completion S'.A
  obtain ⟨pr, hpr1, -⟩ := exists_hom_blowUp_completion S.A
  obtain ⟨y', rfl, hy'o⟩ := hpr'2 x' hx'o
  obtain ⟨-, ⟨c1⟩⟩ := hpr'1 y' hy'o
  obtain ⟨k, hk⟩ := exists_iso_blowUp_maximalIdealSheaf_of_ringEquiv E
  have : IsLocalHom (E : AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A →+*
      AdicCompletion (IsLocalRing.maximalIdeal S'.A) S'.A) :=
    IsLocalHom.of_surjective _ E.surjective
  have hyo : blowUpToBase _ (k.hom y') =
      IsLocalRing.closedPoint (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A) := by
    have h := congrArg (fun t => t.base y') hk
    simp only [Scheme.Hom.comp_apply] at h
    rw [h, hy'o]
    exact base_spec_map_closedPoint _
  obtain ⟨hxo, ⟨c2⟩⟩ := hpr1 (k.hom y') hyo
  have c3 : (blowUp (maximalIdealSheaf
        (AdicCompletion (IsLocalRing.maximalIdeal S'.A) S'.A))).presheaf.stalk y' ≃+*
      (blowUp (maximalIdealSheaf
        (AdicCompletion (IsLocalRing.maximalIdeal S.A) S.A))).presheaf.stalk (k.hom y') :=
    (asIso (k.hom.stalkMap y')).commRingCatIsoToRingEquiv.symm
  obtain ⟨C3, -⟩ := StacksDraft.exists_adicCompletion_ringEquiv_of_ringEquiv c3
  have hiso : Nonempty (AdicCompletion (IsLocalRing.maximalIdeal
          ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk (pr (k.hom y'))))
          ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk (pr (k.hom y'))) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal
          ((blowUp (maximalIdealSheaf S'.A)).presheaf.stalk (pr' y')))
          ((blowUp (maximalIdealSheaf S'.A)).presheaf.stalk (pr' y'))) :=
    ⟨(c2.trans C3.symm).trans c1.symm⟩
  refine ⟨pr (k.hom y'), fun hreg => hx' ?_, hiso⟩
  obtain ⟨c⟩ := hiso
  have hN (T : RationalDoublePointSituation.{u}) :
      IsLocallyNoetherian (blowUp (maximalIdealSheaf T.A)) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase _)
  have := hN S
  have := hN S'
  change IsRegularLocalRing _ at hreg ⊢
  rw [isRegularLocalRing_iff_adicCompletion_maximalIdeal] at hreg ⊢
  exact IsRegularLocalRing.of_ringEquiv c

end RationalDoublePointSituation

end AlgebraicGeometry

end
