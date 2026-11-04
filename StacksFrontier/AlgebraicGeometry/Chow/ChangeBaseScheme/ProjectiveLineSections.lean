module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ProjectiveLineFamily

/-!
# The constant sections under a change of the base scheme

`StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.ProjectiveLineFamily` builds the morphism
`Stacks.Chow.projectiveLineProductBaseChange` exhibiting the family `X' ×_{S'} 𝐏¹_{S'}` as the
base change of `X ×_S 𝐏¹_S` along `g : S' ⟶ S`, for `X' = X ×_S S'`. It deliberately stops short
of the compatibility of that morphism with the distinguished constant sections. This file
supplies it, and the consequence a cycle-level argument wants: the zero and infinity fibres of a
base-changed closed subscheme are the base changes of the zero and infinity fibres.

## Main results

* `Stacks.Chow.constantSection_comp_projectiveLineProductBaseChange` — the square

  ```
  X' ---- constantSection ----> X' ×_{S'} 𝐏¹_{S'}
  |                                     |
  v                                     v
  X  ---- constantSection ----> X ×_S 𝐏¹_S
  ```

  commutes, the vertical maps being the projection `X' ⟶ X` and
  `Stacks.Chow.projectiveLineProductBaseChange`.
* `Stacks.Chow.zeroFiber_baseChangedFamily`, `Stacks.Chow.infinityFiber_baseChangedFamily` —
  the two fibres of `Stacks.Chow.baseChangedFamily` are the inverse images along `X' ⟶ X` of the
  two fibres.
* `Stacks.Chow.constantSection_comp_projectiveLineProductMap`,
  `Stacks.Chow.zeroFiber_baseChangedFamilyOfSquare`,
  `Stacks.Chow.infinityFiber_baseChangedFamilyOfSquare` — the same statements for the morphism
  of families attached to an arbitrary commuting square.

## Implementation notes

The structure morphism `relativeProjectiveLine S ↘ S` is the first projection of the pullback
defining `𝐏¹_S` only through the `CategoryTheory.Over` instance, so `pullback.lift_fst` does not
fire at it directly; `Stacks.Chow.relativeProjectiveLine_over_hom` crosses that spelling and is
rewritten with explicitly, rather than left to `simp`, which would otherwise unfold the limit
cone of `𝐏¹_S`.

Everything below is a chase of the two universal properties — that of `X ×_S 𝐏¹_S` over `X` and
that of `𝐏¹_S` over `S` — against the three characterizing equations
`Stacks.Chow.projectiveLineProductBaseChange_comp_fst`,
`Stacks.Chow.projectiveLineProductBaseChange_comp_snd` and
`Stacks.Chow.projectiveLineBaseChange_comp_snd`. The fibre statements are then pure `comap`
functoriality.

## References

* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

/-- The base-change morphism of families is compatible with the projection to `𝐏¹_ℤ`: both
families project to the same `𝐏¹_ℤ`-coordinate. -/
@[reassoc (attr := simp)]
theorem projectiveLineProductBaseChange_comp_projection :
    projectiveLineProductBaseChange f g ≫ projectiveLineProjection f =
      projectiveLineProjection (pullback.snd f g) := by
  rw [projectiveLineProjection, projectiveLineProjection, ← Category.assoc,
    projectiveLineProductBaseChange_comp_snd, Category.assoc, projectiveLineBaseChange_comp_snd]

/-- **The constant sections are compatible with a change of the base scheme.** For
`X' = X ×_S S'`, the constant section of `X' ×_{S'} 𝐏¹_{S'} ⟶ X'` at an integral point `e` of
`𝐏¹_ℤ`, followed by `Stacks.Chow.projectiveLineProductBaseChange`, is the projection `X' ⟶ X`
followed by the constant section of `X ×_S 𝐏¹_S ⟶ X` at `e`.

Both sides are compared through `Stacks.Chow.isPullback_projectiveLineProjection`, which presents
`X ×_S 𝐏¹_S` as the product of `X` and `𝐏¹_ℤ` over the terminal scheme: a morphism into it is
determined by its projection to `X` and its `𝐏¹_ℤ`-coordinate, and both are computed by the
characterizing equations of the two base-change morphisms. -/
theorem constantSection_comp_projectiveLineProductBaseChange
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    constantSection (pullback.snd f g) e ≫ projectiveLineProductBaseChange f g =
      pullback.fst f g ≫ constantSection f e := by
  refine (isPullback_projectiveLineProjection f).hom_ext ?_ ?_
  · rw [Category.assoc, projectiveLineProductBaseChange_comp_fst, ← Category.assoc,
      constantSection_comp_fst, Category.id_comp, Category.assoc, constantSection_comp_fst,
      Category.comp_id]
  · simp only [Category.assoc, projectiveLineProductBaseChange_comp_projection,
      constantSection_comp_projection, terminal.comp_from_assoc]

/-- The zero section is compatible with a change of the base scheme. -/
theorem zeroSection_comp_projectiveLineProductBaseChange :
    zeroSection (pullback.snd f g) ≫ projectiveLineProductBaseChange f g =
      pullback.fst f g ≫ zeroSection f :=
  constantSection_comp_projectiveLineProductBaseChange f g integralZeroSection

/-- The infinity section is compatible with a change of the base scheme. -/
theorem infinitySection_comp_projectiveLineProductBaseChange :
    infinitySection (pullback.snd f g) ≫ projectiveLineProductBaseChange f g =
      pullback.fst f g ≫ infinitySection f :=
  constantSection_comp_projectiveLineProductBaseChange f g integralInfinitySection

/-- **The zero fibre of a base-changed family is the base change of the zero fibre.** -/
theorem zeroFiber_baseChangedFamily (W : (projectiveLineProduct f).IdealSheafData) :
    zeroFiber (pullback.snd f g) (baseChangedFamily f g W) =
      (zeroFiber f W).comap (pullback.fst f g) := by
  rw [baseChangedFamily, zeroFiber, zeroFiber, ← Scheme.IdealSheafData.comap_comp,
    zeroSection_comp_projectiveLineProductBaseChange, Scheme.IdealSheafData.comap_comp]

/-- **The infinity fibre of a base-changed family is the base change of the infinity fibre.** -/
theorem infinityFiber_baseChangedFamily (W : (projectiveLineProduct f).IdealSheafData) :
    infinityFiber (pullback.snd f g) (baseChangedFamily f g W) =
      (infinityFiber f W).comap (pullback.fst f g) := by
  rw [baseChangedFamily, infinityFiber, infinityFiber, ← Scheme.IdealSheafData.comap_comp,
    infinitySection_comp_projectiveLineProductBaseChange, Scheme.IdealSheafData.comap_comp]

section Square

variable {Y : Scheme.{u}} {p : Y ⟶ X} {q : Y ⟶ S'} (w : p ≫ f = q ≫ g)

/-- The morphism of families attached to a commuting square is compatible with the projection to
`𝐏¹_ℤ`: both families project to the same `𝐏¹_ℤ`-coordinate. -/
@[reassoc (attr := simp)]
theorem projectiveLineProductMap_comp_projection :
    projectiveLineProductMap f g w ≫ projectiveLineProjection f = projectiveLineProjection q := by
  rw [projectiveLineProjection, projectiveLineProjection, ← Category.assoc,
    projectiveLineProductMap_comp_snd, Category.assoc, projectiveLineBaseChange_comp_snd]

/-- **The constant sections are compatible with the morphism of families attached to a commuting
square.** For `p ≫ f = q ≫ g`, the constant section of `Y ×_{S'} 𝐏¹_{S'} ⟶ Y` at an integral
point `e` of `𝐏¹_ℤ`, followed by `Stacks.Chow.projectiveLineProductMap`, is `p` followed by the
constant section of `X ×_S 𝐏¹_S ⟶ X` at `e`. -/
theorem constantSection_comp_projectiveLineProductMap
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    constantSection q e ≫ projectiveLineProductMap f g w = p ≫ constantSection f e := by
  refine (isPullback_projectiveLineProjection f).hom_ext ?_ ?_
  · rw [Category.assoc, projectiveLineProductMap_comp_fst, ← Category.assoc,
      constantSection_comp_fst, Category.id_comp, Category.assoc, constantSection_comp_fst,
      Category.comp_id]
  · simp only [Category.assoc, projectiveLineProductMap_comp_projection,
      constantSection_comp_projection, terminal.comp_from_assoc]

/-- The zero section is compatible with the morphism of families attached to a commuting
square. -/
theorem zeroSection_comp_projectiveLineProductMap :
    zeroSection q ≫ projectiveLineProductMap f g w = p ≫ zeroSection f :=
  constantSection_comp_projectiveLineProductMap f g w integralZeroSection

/-- The infinity section is compatible with the morphism of families attached to a commuting
square. -/
theorem infinitySection_comp_projectiveLineProductMap :
    infinitySection q ≫ projectiveLineProductMap f g w = p ≫ infinitySection f :=
  constantSection_comp_projectiveLineProductMap f g w integralInfinitySection

/-- **The zero fibre of a family pulled back along a commuting square is the inverse image of
the zero fibre.** -/
theorem zeroFiber_baseChangedFamilyOfSquare (W : (projectiveLineProduct f).IdealSheafData) :
    zeroFiber q (baseChangedFamilyOfSquare f g w W) = (zeroFiber f W).comap p := by
  rw [baseChangedFamilyOfSquare, zeroFiber, zeroFiber, ← Scheme.IdealSheafData.comap_comp,
    zeroSection_comp_projectiveLineProductMap, Scheme.IdealSheafData.comap_comp]

/-- **The infinity fibre of a family pulled back along a commuting square is the inverse image
of the infinity fibre.** -/
theorem infinityFiber_baseChangedFamilyOfSquare (W : (projectiveLineProduct f).IdealSheafData) :
    infinityFiber q (baseChangedFamilyOfSquare f g w W) = (infinityFiber f W).comap p := by
  rw [baseChangedFamilyOfSquare, infinityFiber, infinityFiber, ← Scheme.IdealSheafData.comap_comp,
    infinitySection_comp_projectiveLineProductMap, Scheme.IdealSheafData.comap_comp]

end Square

end Stacks.Chow

end
