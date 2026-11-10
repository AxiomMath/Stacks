module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveStrictTransform
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CurveStrictTransform
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.InverseImageComponents

/-!
# The support of a strict transform

Let `X` be a Noetherian scheme, `p` a closed point of `X` and `Z ⊆ X` a closed subscheme. The
strict transform `AlgebraicGeometry.transformIdeal` of `Z` under the blowup `b` of `X` at `p` has
support the closure of `b⁻¹(Supp Z) \ b⁻¹{p}`, the part of the inverse image of `Z` lying off the
fibre over `p`. Consequently, when it is reduced, it coincides with
`Stacks.ResolutionOfSurfaces.reducedStrictTransform`, the reduced structure on that set.

## Main results

* `Stacks.ResolutionOfSurfaces.coe_support_transformIdeal`: the support of the strict transform
  is `closure (b⁻¹(Supp Z) \ b⁻¹{p})`.
* `Stacks.ResolutionOfSurfaces.reducedStrictTransform_eq_transformIdeal`: if the strict transform
  is reduced, it is `Stacks.ResolutionOfSurfaces.reducedStrictTransform`.

## References

* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 0BIC](https://stacks.math.columbia.edu/tag/0BIC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-- The support of the strict transform of a closed subscheme under the blowup at a closed point
is the closure of the part of the inverse image of that subscheme lying off the exceptional
fibre. -/
public theorem coe_support_transformIdeal {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (p : X) (hp : IsClosed ({p} : Set X)) :
    ((AlgebraicGeometry.transformIdeal I p hp).support :
        Set (blowUp (AlgebraicGeometry.centerIdeal p hp))) =
      closure ((blowUpToBase (AlgebraicGeometry.centerIdeal p hp)).base ⁻¹' (I.support : Set X) \
        (blowUpToBase (AlgebraicGeometry.centerIdeal p hp)).base ⁻¹' {p}) := by
  have hci : ((AlgebraicGeometry.centerIdeal p hp).support : Set X) = {p} :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  set b := blowUpToBase (AlgebraicGeometry.centerIdeal p hp) with hb
  set P : Scheme.{u} := pullback I.subschemeι b with hP
  set pr₁ : P ⟶ I.subscheme := pullback.fst I.subschemeι b with hpr₁
  set pr₂ : P ⟶ blowUp (AlgebraicGeometry.centerIdeal p hp) := pullback.snd I.subschemeι b
    with hpr₂
  have : IsClosedImmersion pr₂ := by rw [hpr₂]; infer_instance
  have : IsClosedImmersion (AlgebraicGeometry.transformToBlowUp I p hp) :=
    AlgebraicGeometry.isClosedImmersion_transformToBlowUp I p hp
  have : IsNoetherian (blowUp (AlgebraicGeometry.centerIdeal p hp)) := isNoetherian_blowUp _
  have : IsLocallyNoetherian (blowUp (AlgebraicGeometry.centerIdeal p hp)) :=
    IsNoetherian.toIsLocallyNoetherian
  have : IsLocallyNoetherian P :=
    AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion pr₂
  set W : P.Opens :=
    (pr₁ ≫ I.subschemeι) ⁻¹ᵁ (AlgebraicGeometry.centerIdeal p hp).support.compl with hW
  have hpt : ∀ q : P, I.subschemeι (pr₁ q) = b (pr₂ q) := fun q =>
    congrArg (fun k : P ⟶ X => k.base q)
      (pullback.condition (f := I.subschemeι) (g := b))
  have hran : Set.range pr₂.base = b.base ⁻¹' (I.support : Set X) := by
    rw [hpr₂, Scheme.Pullback.range_snd, I.range_subschemeι]
  have hST : ((AlgebraicGeometry.strictTransformCenterIdeal I p hp).support : Set P) =
      closure (W : Set P) := by
    rw [AlgebraicGeometry.strictTransformCenterIdeal_eq_ker, Scheme.Hom.support_ker,
      Scheme.Opens.range_ι]
  have hmem : ∀ q : P, q ∈ W ↔ b (pr₂ q) ≠ p := fun q => by
    change I.subschemeι (pr₁ q) ∉ ((AlgebraicGeometry.centerIdeal p hp).support : Set X) ↔ _
    rw [hci, Set.mem_singleton_iff, hpt q]
  have himg : pr₂.base '' (W : Set P) =
      b.base ⁻¹' (I.support : Set X) \ b.base ⁻¹' {p} := by
    refine Set.eq_of_subset_of_subset (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨q, hqW, rfl⟩ := hz
      exact ⟨hran ▸ Set.mem_range_self q, (hmem q).1 hqW⟩
    · obtain ⟨z', rfl⟩ : z ∈ Set.range pr₂.base := hran ▸ hz.1
      exact ⟨z', (hmem z').2 (by simpa using hz.2), rfl⟩
  have hcomp : ∀ x, (AlgebraicGeometry.transformToBlowUp I p hp) x =
      pr₂ ((AlgebraicGeometry.strictTransformCenterIdeal I p hp).subschemeι x) := fun _ => rfl
  have hrange : Set.range (AlgebraicGeometry.transformToBlowUp I p hp).base =
      pr₂.base '' ((AlgebraicGeometry.strictTransformCenterIdeal I p hp).support : Set P) := by
    rw [← (AlgebraicGeometry.strictTransformCenterIdeal I p hp).range_subschemeι]
    refine Set.eq_of_subset_of_subset ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, (hcomp x).symm⟩
    · rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, hcomp x⟩
  rw [show AlgebraicGeometry.transformIdeal I p hp =
      (AlgebraicGeometry.transformToBlowUp I p hp).ker from rfl, Scheme.Hom.support_ker,
    hrange, hST, ← pr₂.isClosedEmbedding.closure_image_eq, himg, closure_closure]

/-- If the strict transform `AlgebraicGeometry.transformIdeal I p hp` is reduced, it is equal to
`Stacks.ResolutionOfSurfaces.reducedStrictTransform p hp I`, the reduced structure on the closure
of the part of the inverse image of `I` lying off the exceptional fibre. -/
public theorem reducedStrictTransform_eq_transformIdeal {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (p : X) (hp : IsClosed ({p} : Set X))
    [IsReduced (AlgebraicGeometry.transformIdeal I p hp).subscheme] :
    reducedStrictTransform p hp I = AlgebraicGeometry.transformIdeal I p hp :=
  (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme
    (AlgebraicGeometry.transformIdeal I p hp) _
    (Closeds.ext (coe_support_transformIdeal I p hp))).symm

end Stacks.ResolutionOfSurfaces

end
