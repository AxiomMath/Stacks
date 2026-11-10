module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionOpenness
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionSmoothSpaces

/-!
# The fibre dimension of a smooth morphism is locally constant

For a morphism `g : T ⟶ G` of algebraic spaces locally of finite type, the fibre dimension
`t ↦ dim_t(T_{g(t)})`, the relative dimension of Stacks 0DRG, is upper semi-continuous on `|T|`,
and it is locally constant when `g` is smooth (Stacks 0DRQ).

## Main results

* `AlgebraicGeometry.Space.eq_of_hasRelativeDimensionAt`: the relative dimension of Stacks 04NM
  at a point takes at most one value.
* `AlgebraicGeometry.Space.exists_isOpen_forall_hasRelativeDimensionAt_of_isSmooth`: a smooth
  morphism of algebraic spaces has, at every point of its source, an open neighbourhood on
  which its relative dimension of Stacks 04NM is constant.
* `AlgebraicGeometry.Stack.isOpen_setOf_relativeDimensionAt_le`: the fibre dimension of a
  morphism of algebraic spaces locally of finite type is upper semi-continuous.
* `AlgebraicGeometry.Stack.isLocallyConstant_relativeDimensionAt_of_isSmooth`: the fibre
  dimension of a smooth morphism of algebraic spaces is locally constant.

## References

* [Stacks Project, Tag 01VD](https://stacks.math.columbia.edu/tag/01VD)
* [Stacks Project, Tag 02K1](https://stacks.math.columbia.edu/tag/02K1)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04NT](https://stacks.math.columbia.edu/tag/04NT)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRH](https://stacks.math.columbia.edu/tag/0DRH)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRN](https://stacks.math.columbia.edu/tag/0DRN)
* [Stacks Project, Tag 0DRQ](https://stacks.math.columbia.edu/tag/0DRQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The relative dimension (Stacks 04NM) of a morphism of algebraic spaces at a point takes at
most one value. -/
theorem eq_of_hasRelativeDimensionAt {d e : ℕ∞}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (x : points B S hS F)
    (hd : HasRelativeDimensionAt d B S hS f x)
    (he : HasRelativeDimensionAt e B S hS f x) :
    d = e := by
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hF hG f x
  rw [hasRelativeDimensionAt_iff_of_chart B S hS d f x c] at hd
  rw [hasRelativeDimensionAt_iff_of_chart B S hS e f x c] at he
  exact WithBot.coe_injective (hd.symm.trans he)

/-- A smooth morphism of algebraic spaces over `S` has locally constant relative dimension: at
every point of the source there is an open neighbourhood and a single value `d` which is the
relative dimension of Stacks 04NM at every point of it. -/
@[ega "IV 17.10.2" "more general"]
theorem exists_isOpen_forall_hasRelativeDimensionAt_of_isSmooth
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (hf : IsSmooth B S hS f) (x : points B S hS F) :
    ∃ (W : Set (points B S hS F)) (d : ℕ∞), IsOpen W ∧ x ∈ W ∧
      ∀ y ∈ W, HasRelativeDimensionAt d B S hS f y := by
  classical
  obtain ⟨V, b, hbSurjective, hbEtale⟩ := hG.exists_atlas
  obtain ⟨U, a, α, hcomm, haSurjective, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hF hG f V b hbSurjective hbEtale
  have _ : _root_.AlgebraicGeometry.Smooth ((BigFppfOver.toScheme B S hS).map α) :=
    hf U V a b α haEtale hbEtale hcomm.symm
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
    (surjective_iff_surjective_pointsMap B S hS F hF U a).mp haSurjective
  obtain ⟨w, hw⟩ := hsurj x
  obtain ⟨O, hO, hwO, hconst⟩ :=
    (isLocallyConstant_fiberDimensionAt ((BigFppfOver.toScheme B S hS).map α)
      (syntomic_of_smooth ((BigFppfOver.toScheme B S hS).map α))).exists_open
      (pointsToScheme B S hS U w)
  obtain ⟨d, hd⟩ : ∃ d : ℕ∞,
      topologicalKrullDimAt
          (((BigFppfOver.toScheme B S hS).map α).fiber
            ((BigFppfOver.toScheme B S hS).map α (pointsToScheme B S hS U w)))
          (((BigFppfOver.toScheme B S hS).map α).asFiber (pointsToScheme B S hS U w)) =
        (d : WithBot ℕ∞) := by
    have hpos := topologicalKrullDimAt_nonneg
      (((BigFppfOver.toScheme B S hS).map α).asFiber (pointsToScheme B S hS U w))
    have hne : topologicalKrullDimAt
        (((BigFppfOver.toScheme B S hS).map α).fiber
          ((BigFppfOver.toScheme B S hS).map α (pointsToScheme B S hS U w)))
        (((BigFppfOver.toScheme B S hS).map α).asFiber
          (pointsToScheme B S hS U w)) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hpos
      simp at hpos
    obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hne
    exact ⟨e, he.symm⟩
  refine ⟨pointsMap B S hS (yoneda.obj U) a '' (pointsToScheme B S hS U ⁻¹' O), d, ?_,
    ⟨w, hwO, hw⟩, ?_⟩
  · refine isOpenMap_pointsMap_of_presheafEtale B S hS a haEtale _ ?_
    rw [isOpen_pointTopology_yoneda_iff_isOpen_image,
      Set.image_preimage_eq _ (surjective_pointsToScheme B S hS U)]
    exact hO
  · rintro y ⟨w', hw'O, rfl⟩
    have hiff := hasRelativeDimensionAt_pointsMap_iff B S hS d f U V a b α haEtale hbEtale
      hcomm.symm (pointsToScheme B S hS U w')
    have he : (pointsEquivScheme B S hS U).symm (pointsToScheme B S hS U w') = w' := by
      apply (pointsEquivScheme B S hS U).injective
      rw [Equiv.apply_symm_apply]
      rfl
    rw [he] at hiff
    exact hiff.mpr ((hconst _ hw'O).trans hd)

end Space

namespace Stack

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a morphism `g : T ⟶ G` of algebraic spaces over `S` which is locally of finite type, the
locus of points of `|T|` at which the fibre dimension `dim_t(T_{g(t)})` of Stacks 0DRG is at most
`n` is open. -/
@[stacks 0DRQ "part (1) for a morphism of algebraic spaces"]
theorem isOpen_setOf_relativeDimensionAt_le
    {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) (g : T ⟶ G)
    (hg : Space.IsLocallyOfFiniteType B S hS g)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hT hG g))
    (n : ℕ) :
    IsOpen {t : Space.points B S hS T |
      relativeDimensionAt.{u, w} B S hS T hT (algebraicSpaceStack.{u, w} B S hS G hG)
        (algebraicSpaceStackMap.{u, w} B S hS hT hG g) hf t ≤ (n : WithBot ℕ∞)} := by
  have hset : {t : Space.points B S hS T |
        relativeDimensionAt.{u, w} B S hS T hT (algebraicSpaceStack.{u, w} B S hS G hG)
          (algebraicSpaceStackMap.{u, w} B S hS hT hG g) hf t ≤ (n : WithBot ℕ∞)} =
      {t : Space.points B S hS T | ∃ d : ℕ∞, d ≤ (n : ℕ∞) ∧
        Space.HasRelativeDimensionAt d B S hS g t} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    refine ⟨fun ht => ?_, fun ⟨d, hdn, hd⟩ => ?_⟩
    · obtain ⟨d, hd⟩ := Space.exists_hasRelativeDimensionAt B S hS hT hG g t
      rw [(relativeDimensionAt_eq_iff_hasRelativeDimensionAt.{u, w} B S hS hT hG g hf t d).mpr
        hd] at ht
      exact ⟨d, by exact_mod_cast ht, hd⟩
    · rw [(relativeDimensionAt_eq_iff_hasRelativeDimensionAt.{u, w} B S hS hT hG g hf t d).mpr hd]
      exact_mod_cast hdn
  rw [hset]
  exact Space.isOpen_setOf_hasRelativeDimensionAt_le B S hS hT hG g hg n

/-- For a smooth morphism `g : T ⟶ G` of algebraic spaces over `S`, the fibre dimension
`t ↦ dim_t(T_{g(t)})` of Stacks 0DRG is locally constant on `|T|`. -/
@[stacks 0DRQ "part (2) for a morphism of algebraic spaces", ega "IV 17.10.2" "more general"]
theorem isLocallyConstant_relativeDimensionAt_of_isSmooth
    {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) (g : T ⟶ G)
    (hg : Space.IsSmooth B S hS g) :
    IsLocallyConstant
      (relativeDimensionAt.{u, w} B S hS T hT (algebraicSpaceStack.{u, w} B S hS G hG)
        (algebraicSpaceStackMap.{u, w} B S hS hT hG g)
        (isLocallyOfFiniteType_algebraicSpaceStackMap_of_isSmooth.{u, w} B S hS hT hG g hg)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro t
  obtain ⟨W, d, hWopen, htW, hWd⟩ :=
    Space.exists_isOpen_forall_hasRelativeDimensionAt_of_isSmooth B S hS hT hG g hg t
  have key := fun s (hs : s ∈ W) =>
    (relativeDimensionAt_eq_iff_hasRelativeDimensionAt.{u, w} B S hS hT hG g
      (isLocallyOfFiniteType_algebraicSpaceStackMap_of_isSmooth.{u, w} B S hS hT hG g hg)
      s d).mpr (hWd s hs)
  exact ⟨W, hWopen, htW, fun t' ht' => (key t' ht').trans (key t htW).symm⟩

end Stack

end AlgebraicGeometry

end
