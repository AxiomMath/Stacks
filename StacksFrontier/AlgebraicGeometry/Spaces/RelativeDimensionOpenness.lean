module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart

/-!
# The locus of bounded relative dimension of a morphism of algebraic spaces is open

For a morphism `f : X ⟶ Y` of algebraic spaces which is locally of finite type and an integer
`n ≥ 0`, the set of points of `|X|` at which the relative dimension of `f` is at most `n` is
open.

## Main results

* `AlgebraicGeometry.Space.isOpen_setOf_hasRelativeDimensionAt_le`: the set of points of the
  source at which the relative dimension is at most `n` is open.

## References

* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04NT](https://stacks.math.columbia.edu/tag/04NT)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- For a value of `WithBot ℕ∞` which is at least `0`, being the image of some `d : ℕ∞` with
`d ≤ m` is the inequality `≤ m`. -/
private theorem exists_coe_le_iff_le {v : WithBot ℕ∞} (hv : 0 ≤ v) (m : ℕ∞) :
    (∃ d : ℕ∞, d ≤ m ∧ v = (d : WithBot ℕ∞)) ↔ v ≤ (m : WithBot ℕ∞) := by
  refine ⟨fun ⟨d, hdm, h⟩ ↦ h ▸ WithBot.coe_le_coe.mpr hdm, fun hvm ↦ ?_⟩
  obtain ⟨d, rfl⟩ := WithBot.ne_bot_iff_exists.mp (show v ≠ ⊥ by rintro rfl; simp at hv)
  exact ⟨d, WithBot.coe_le_coe.mp hvm, rfl⟩

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- For a morphism of algebraic spaces over `S` which is locally of finite type, the set of
points of the source at which the relative dimension is at most `n` is open. -/
@[stacks 04NT]
theorem isOpen_setOf_hasRelativeDimensionAt_le (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsLocallyOfFiniteType B S hS f)
    (n : ℕ) :
    IsOpen {x : points B S hS F |
      ∃ d : ℕ∞, d ≤ (n : ℕ∞) ∧ HasRelativeDimensionAt d B S hS f x} := by
  obtain ⟨V, b, hbSurjective, hbEtale⟩ := hG.exists_atlas
  obtain ⟨U, a, α, hcomm, haSurjective, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hF hG f V b hbSurjective hbEtale
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS F hF U a).mp haSurjective
  have hquot := isQuotientMap_pointsMap_of_presheafEtale B S hS a haEtale hsurj
  rw [← hquot.isOpen_preimage]
  have hft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α) :=
    hf U V a b α haEtale hbEtale hcomm.symm
  have hcast : ((n : ℕ∞) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by simp
  have hpre : pointsMap B S hS (yoneda.obj U) a ⁻¹'
        {x : points B S hS F |
          ∃ d : ℕ∞, d ≤ (n : ℕ∞) ∧ HasRelativeDimensionAt d B S hS f x} =
      pointsToScheme B S hS U ⁻¹'
        {u : (BigFppfOver.toScheme B S hS).obj U |
          topologicalKrullDimAt (((BigFppfOver.toScheme B S hS).map α).fiber
              (((BigFppfOver.toScheme B S hS).map α) u))
            (((BigFppfOver.toScheme B S hS).map α).asFiber u) ≤ (n : WithBot ℕ∞)} := by
    ext w
    have hw : (pointsEquivScheme B S hS U).symm (pointsToScheme B S hS U w) = w :=
      (pointsEquivScheme B S hS U).symm_apply_apply w
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [← hcast, ← exists_coe_le_iff_le (topologicalKrullDimAt_nonneg _) (n : ℕ∞)]
    refine exists_congr fun d ↦ and_congr_right fun _ ↦ ?_
    have hiff := hasRelativeDimensionAt_pointsMap_iff B S hS d f U V a b α haEtale hbEtale
      hcomm.symm (pointsToScheme B S hS U w)
    rwa [hw] at hiff
  rw [hpre, isOpen_pointTopology_yoneda_iff_isOpen_image,
    Set.image_preimage_eq _ (surjective_pointsToScheme B S hS U)]
  exact isOpen_setOf_fiberDimensionAt_le ((BigFppfOver.toScheme B S hS).map α) n

end Space

end AlgebraicGeometry

end
