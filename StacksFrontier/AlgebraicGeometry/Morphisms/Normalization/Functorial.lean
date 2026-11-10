module

public import Mathlib.AlgebraicGeometry.Normalization
public import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of relative normalization

A commutative square of quasi-compact and quasi-separated morphisms of schemes induces a
canonical morphism between their relative normalizations. This morphism makes both resulting
squares commute, and it is the unique morphism that does so.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.normalizationMap` is the canonical morphism between the
  relative normalizations.

## Main results

* `AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationMap` gives commutativity with the
  morphisms from the source schemes.
* `AlgebraicGeometry.Scheme.Hom.normalizationMap_fromNormalization` gives commutativity with
  the morphisms to the target schemes.
* `AlgebraicGeometry.Scheme.Hom.normalizationMap_unique` characterizes the canonical morphism
  uniquely by these two commutative squares.

## Implementation notes

The canonical morphism is constructed by first mapping into the pullback of the first
normalization along the map of target schemes, applying the universal property of the second
normalization, and then projecting to the first normalization.

## References

* [Stacks Project, Tag 035J](https://stacks.math.columbia.edu/tag/035J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {Y₁ Y₂ X₁ X₂ : Scheme.{u}}
  (f₁ : Y₁ ⟶ X₁) (f₂ : Y₂ ⟶ X₂)
  (gY : Y₂ ⟶ Y₁) (gX : X₂ ⟶ X₁)
  [QuasiCompact f₁] [QuasiSeparated f₁]
  [QuasiCompact f₂] [QuasiSeparated f₂]
  (sq : gY ≫ f₁ = f₂ ≫ gX)

/-- The canonical morphism between relative normalizations induced by a commutative square. -/
@[stacks 035J "canonical morphism"]
noncomputable def normalizationMap : f₂.normalization ⟶ f₁.normalization :=
  f₂.normalizationDesc
      (pullback.lift f₂ (gY ≫ f₁.toNormalization) (by
        rw [Category.assoc, f₁.toNormalization_fromNormalization, sq]))
      (pullback.fst gX f₁.fromNormalization) (by rw [pullback.lift_fst]) ≫
    pullback.snd gX f₁.fromNormalization

/-- The canonical morphism between normalizations commutes with the maps from the source
schemes. -/
@[stacks 035J "upper square"]
lemma toNormalization_normalizationMap :
    f₂.toNormalization ≫ normalizationMap f₁ f₂ gY gX sq =
      gY ≫ f₁.toNormalization := by
  unfold normalizationMap
  rw [← Category.assoc, f₂.toNormalization_normalizationDesc, pullback.lift_snd]

/-- The canonical morphism between normalizations commutes with the maps to the target
schemes. -/
@[stacks 035J "lower square"]
lemma normalizationMap_fromNormalization :
    normalizationMap f₁ f₂ gY gX sq ≫ f₁.fromNormalization =
      f₂.fromNormalization ≫ gX := by
  unfold normalizationMap
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    f₂.normalizationDesc_comp]

/-- A morphism between the relative normalizations that makes both squares commute is the
canonical morphism. -/
@[stacks 035J "uniqueness"]
lemma normalizationMap_unique (h : f₂.normalization ⟶ f₁.normalization)
    (h_source : f₂.toNormalization ≫ h = gY ≫ f₁.toNormalization)
    (h_target : h ≫ f₁.fromNormalization = f₂.fromNormalization ≫ gX) :
    h = normalizationMap f₁ f₂ gY gX sq := by
  let k : f₂.normalization ⟶ pullback gX f₁.fromNormalization :=
    pullback.lift f₂.fromNormalization h h_target.symm
  have hk : k = f₂.normalizationDesc
      (pullback.lift f₂ (gY ≫ f₁.toNormalization) (by
        rw [Category.assoc, f₁.toNormalization_fromNormalization, sq]))
      (pullback.fst gX f₁.fromNormalization) (by rw [pullback.lift_fst]) := by
    apply normalization.hom_ext (f := f₂) k _ (pullback.fst gX f₁.fromNormalization)
    · apply pullback.hom_ext
      · rw [Category.assoc, show k ≫ pullback.fst gX f₁.fromNormalization =
          f₂.fromNormalization from pullback.lift_fst _ _ _,
          f₂.toNormalization_normalizationDesc, pullback.lift_fst,
          f₂.toNormalization_fromNormalization]
      · rw [Category.assoc, show k ≫ pullback.snd gX f₁.fromNormalization = h from
          pullback.lift_snd _ _ _, h_source,
          f₂.toNormalization_normalizationDesc, pullback.lift_snd]
    · exact pullback.lift_fst _ _ _
    · exact f₂.normalizationDesc_comp _ _ _
  calc
    h = k ≫ pullback.snd gX f₁.fromNormalization := by simp [k]
    _ = normalizationMap f₁ f₂ gY gX sq := by rw [hk]; rfl

end AlgebraicGeometry.Scheme.Hom
