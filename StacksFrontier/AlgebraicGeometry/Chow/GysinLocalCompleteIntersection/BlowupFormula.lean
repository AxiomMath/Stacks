module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFlat
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.BlowupExcessConormal
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.BaseChangeExcessFormula

/-!
# The blow up formula

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, `i : Z ⟶ X` a regular
closed immersion of schemes locally of finite type over `S`, `b : X' ⟶ X` the blowing up of `X`
with centre `Z` and `π : E ⟶ Z` the exceptional divisor `E = X' ×_X Z` over the centre, with
`j : E ⟶ X'`. The blow up formula (Stacks 0FVA) asserts that, if the Gysin map exists for `b`,

  `res(b^!) = c_top(𝓕^∨) ∘ π^*`   in `A^*(E ⟶ Z)^∧`,

where `𝓕` is the kernel of the canonical map `π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'}`
(`Stacks.Chow.blowupExcessConormal`).

## Main results

* `Stacks.Chow.gysinMapExists_pullbackSnd_blowUpToBase`: the Gysin map exists for `π`.
* `Stacks.Chow.lciGysinMap_pullbackSnd_blowUpToBase`: `π^! = π^*` in `A^*(E ⟶ Z)^∧`.
* `Stacks.Chow.completedBivariantRestriction_lciGysinMap_blowUpToBase`: the blow up formula
  `res(b^!) = c_top(𝓕^∨) ∘ π^*`.

## References

* [Stacks Project, Tag 0FVA](https://stacks.math.columbia.edu/tag/0FVA)
* [Stacks Project, Tag 0FF4](https://stacks.math.columbia.edu/tag/0FF4)
* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The Gysin map of Stacks 0FF3 exists for the projection `π : E ⟶ Z` of the exceptional
divisor of the blowing up along a regular closed immersion. -/
theorem gysinMapExists_pullbackSnd_blowUpToBase (hi : IsRegularImmersion i) :
    GysinMapExists (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i) := by
  have := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
  simpa using GysinMapExists.of_comp (𝟙 _) (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i)

/-- For the projection `π : E ⟶ Z` of the exceptional divisor of the blowing up along a regular
closed immersion, the Gysin map `π^!` of Stacks 0FF3 is the flat pullback `π^*` of the smooth
morphism `π`, in the completed bivariant group `A^*(E ⟶ Z)^∧`. -/
theorem lciGysinMap_pullbackSnd_blowUpToBase (hi : IsRegularImmersion i)
    (sE : pullback (Stacks.Blowup.blowUpToBase i.ker) i ⟶ C.S) [LocallyOfFiniteType sE]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    [LocallyOfFiniteType (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i)]
    (hπ : pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i ≫ sZ = sE) :
    letI : IsLocallyNoetherian (pullback (Stacks.Blowup.blowUpToBase i.ker) i) :=
      LocallyOfFiniteType.isLocallyNoetherian sE
    letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
    haveI := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
    lciGysinMap C sE sZ hπ (isLocalCompleteIntersectionMorphism_pullbackSnd_blowUpToBase i hi)
        (gysinMapExists_pullbackSnd_blowUpToBase i hi) =
      completedFlatPullbackOfSmooth C sE sZ (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i)
        hπ := by
  have : IsLocallyNoetherian (pullback (Stacks.Blowup.blowUpToBase i.ker) i) :=
    LocallyOfFiniteType.isLocallyNoetherian sE
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
  rw [lciGysinMap_eq_completedFlatPullbackOfFlatLCI, completedFlatPullbackOfFlatLCI,
    completedFlatPullbackOfSmooth_eq_completedFlatPullback]

/-- **The blow up formula.** Let `i : Z ⟶ X` be a regular closed immersion of schemes locally of
finite type over the base, `b : X' ⟶ X` the blowing up of `X` with centre `Z`, and `E = X' ×_X Z`
with `j : E ⟶ X'` and `π : E ⟶ Z`. Assume that the Gysin map of Stacks 0FF3 exists for `b` (a local
complete intersection morphism, Stacks 0BIQ). Then

  `res(b^!) = c_top(𝓕^∨) ∘ π^*`   in `A^*(E ⟶ Z)^∧`,

where `𝓕` is the kernel of the canonical map `π^*𝒞_{Z/X} ⟶ 𝒞_{E/X'}` (finite locally free,
`Stacks.Chow.isFiniteLocallyFree_blowupExcessConormal`), `res` is the restriction of Stacks 0F9Z
along `i`, `c_top` the top Chern class of Stacks 0FA4, `π^*` the flat pullback of the smooth
morphism `π` and the composition that of Stacks 0FE0 (a class for `𝟙 ≫ π`). -/
@[stacks 0FVA "the whole lemma: for a regular closed immersion i : Z → X of schemes locally of \
finite type over S, the blowing up b : X' → X with centre Z, E = X' ×_X Z with π : E → Z, and the \
Gysin map existing for b, res(b^!) = c_top(F^∨) ∘ π^* in A^*(E → Z)^∧, F the kernel of \
π^*C_{Z/X} → C_{E/X'}"]
theorem completedBivariantRestriction_lciGysinMap_blowUpToBase (hi : IsRegularImmersion i)
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (hG : GysinMapExists (Stacks.Blowup.blowUpToBase i.ker)) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
    haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
    haveI : IsLocallyNoetherian (Stacks.Blowup.blowUp i.ker) :=
      LocallyOfFiniteType.isLocallyNoetherian (Stacks.Blowup.blowUpToBase i.ker ≫ sX)
    haveI : IsLocallyNoetherian (pullback (Stacks.Blowup.blowUpToBase i.ker) i) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i ≫
        Stacks.Blowup.blowUpToBase i.ker ≫ sX)
    haveI : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (blowupExcessConormal i) :=
      isFiniteLocallyFree_blowupExcessConormal i hi hG
    haveI : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf (blowupExcessConormal i)) :=
      isFiniteLocallyFree_dualSheaf_of_schemeOpens _ inferInstance
    completedBivariantRestrictionViaSequence C (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX
        (Stacks.Blowup.blowUpToBase i.ker) rfl i
        (lciGysinMap C (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX rfl
          (Stacks.Blowup.isLocalCompleteIntersectionMorphism_blowUpToBase i hi) hG) =
      completedBivariantGroup.copy C (Category.id_comp (pullback.snd _ i)) _
        (pullbackSnd_comp_structureMorphism_eq C _ sX _ rfl i)
        (completedBivariantCompositeOfInvertible C
          (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i ≫
            Stacks.Blowup.blowUpToBase i.ker ≫ sX)
          (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i ≫
            Stacks.Blowup.blowUpToBase i.ker ≫ sX)
          (i ≫ sX) (𝟙 _) (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i) (Category.id_comp _)
          (pullbackSnd_comp_structureMorphism_eq C _ sX _ rfl i)
          (topChernClassOfInvertible C _ (dualSheaf (blowupExcessConormal i)))
          (completedFlatPullbackOfSmooth C _ (i ≫ sX)
            (pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i)
            (pullbackSnd_comp_structureMorphism_eq C _ sX _ rfl i))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := Stacks.Blowup.smooth_pullbackSnd_blowUpToBase i hi
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ sX)
  have : IsLocallyNoetherian (Stacks.Blowup.blowUp i.ker) :=
    LocallyOfFiniteType.isLocallyNoetherian (Stacks.Blowup.blowUpToBase i.ker ≫ sX)
  have : IsLocallyNoetherian (pullback (Stacks.Blowup.blowUpToBase i.ker) i) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i ≫
      Stacks.Blowup.blowUpToBase i.ker ≫ sX)
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (blowupExcessConormal i) :=
    isFiniteLocallyFree_blowupExcessConormal i hi hG
  obtain ⟨Fb⟩ := (gysinMapExists_iff_nonempty _).1 hG
  have hsq := IsPullback.of_hasPullback (Stacks.Blowup.blowUpToBase i.ker) i
  have hlb := Stacks.Blowup.isLocalCompleteIntersectionMorphism_blowUpToBase i hi
  have hlπ := isLocalCompleteIntersectionMorphism_pullbackSnd_blowUpToBase i hi
  have hf' : pullback.snd (Stacks.Blowup.blowUpToBase i.ker) i ≫ (i ≫ sX) =
      pullback.fst (Stacks.Blowup.blowUpToBase i.ker) i ≫ Stacks.Blowup.blowUpToBase i.ker ≫ sX :=
    (pullback.condition_assoc sX).symm
  have key := Fb.completedBivariantTransport_completedBivariantRestriction_gysinMap C
    (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX _ rfl hf' hsq hlb hlπ (blowupExcessConormal i)
    (baseChangeExcessConormalIsoBlowupExcessConormal i hi Fb).symm
  rw [completedBivariantTransport_of_hom_eq_id C _ _ _ _ _ _
    (pullback.hom_ext (by rw [Iso.symm_hom, IsPullback.isoPullback_inv_fst, Category.id_comp])
      (by rw [Iso.symm_hom, IsPullback.isoPullback_inv_snd, Category.id_comp]))] at key
  rw [← Fb.gysinMap_eq_lciGysinMap C (Stacks.Blowup.blowUpToBase i.ker ≫ sX) sX rfl hlb hG, key,
    (Fb.baseChange hsq).gysinMap_eq_lciGysinMap C _ (i ≫ sX) hf' hlπ
      (gysinMapExists_pullbackSnd_blowUpToBase i hi),
    lciGysinMap_pullbackSnd_blowUpToBase C i hi _ (i ≫ sX) hf']

end Stacks.Chow

end
