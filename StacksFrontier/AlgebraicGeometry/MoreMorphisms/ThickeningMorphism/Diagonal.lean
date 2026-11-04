module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability

/-!
# Relative diagonals of a morphism of thickenings

Let `i : X ⟶ X'` and `j : S ⟶ S'` be thickenings and let `f : X ⟶ S`, `f' : X' ⟶ S'` be
morphisms with `i ≫ f' = f ≫ j`. The relative diagonal of `f` lands in `X ×_S X` and that of
`f'` in `X' ×_{S'} X'`, and the two are compared by a canonical morphism

`X ×_S X ⟶ X ×_{S'} X ⟶ X ×_{S'} X' ⟶ X' ×_{S'} X'`,

whose first arrow is an isomorphism because `j` is a monomorphism and whose remaining two
arrows are base changes of `i`. The composite is therefore a thickening, and the two relative
diagonals form a morphism of thickenings over it. This is what reduces a separation property of
`f` and `f'` to the corresponding property of their diagonals.

## Main definitions

* `Stacks.Thickenings.diagonalBaseComparison`: the comparison `X ×_S X ⟶ X ×_{S'} X`.
* `Stacks.Thickenings.diagonalTargetFst` and `Stacks.Thickenings.diagonalTargetSnd`: the two
  base changes of `i` relating `X ×_{S'} X`, `X ×_{S'} X'` and `X' ×_{S'} X'`.
* `Stacks.Thickenings.diagonalTargetMap`: their composite with the comparison morphism, the
  map on the targets of the two relative diagonals.

## Main results

* `Stacks.Thickenings.isIso_diagonalBaseComparison`: enlarging the base along a closed
  immersion does not change the self-fibre product of `X`.
* `Stacks.Thickenings.isThickening_diagonalTargetFst`,
  `Stacks.Thickenings.isThickening_diagonalTargetSnd` and
  `Stacks.Thickenings.isThickening_diagonalTargetMap`: the three arrows, and hence the
  composite, are thickenings.
* `Stacks.Thickenings.diagonal_comp_diagonalTargetMap`: the two relative diagonals commute
  with `i` and with the map on their targets.

## Implementation notes

The identification of the two self-fibre products of `X` is recorded as `IsIso` of the
canonical comparison morphism rather than as an equality of chosen pullback objects, and all
four morphisms are built with `CategoryTheory.Limits.pullback.map`, so no choice beyond
Mathlib's displayed fibre product enters.

## References

* [Stacks Project, Tag 09ZV](https://stacks.math.columbia.edu/tag/09ZV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Thickenings

universe u

/-- The canonical comparison `X ×_S X ⟶ X ×_{S'} X` along a morphism `j : S ⟶ S'`. -/
noncomputable def diagonalBaseComparison {X S S' : Scheme.{u}}
    (f : X ⟶ S) (j : S ⟶ S') :
    pullback f f ⟶ pullback (f ≫ j) (f ≫ j) :=
  pullback.map f f (f ≫ j) (f ≫ j) (𝟙 X) (𝟙 X) j (by simp) (by simp)

/-- The first base change of `i : X ⟶ X'`, from `X ×_{S'} X` to `X ×_{S'} X'`. -/
noncomputable def diagonalTargetFst {X X' S S' : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ S) (f' : X' ⟶ S') (j : S ⟶ S')
    (h : i ≫ f' = f ≫ j) :
    pullback (f ≫ j) (f ≫ j) ⟶ pullback (f ≫ j) f' :=
  pullback.map (f ≫ j) (f ≫ j) (f ≫ j) f' (𝟙 X) i (𝟙 S')
    (by simp) (by simpa using h.symm)

/-- The second base change of `i : X ⟶ X'`, from `X ×_{S'} X'` to `X' ×_{S'} X'`. -/
noncomputable def diagonalTargetSnd {X X' S S' : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ S) (f' : X' ⟶ S') (j : S ⟶ S')
    (h : i ≫ f' = f ≫ j) :
    pullback (f ≫ j) f' ⟶ pullback f' f' :=
  pullback.map (f ≫ j) f' f' f' i (𝟙 X') (𝟙 S')
    (by simpa using h.symm) (by simp)

/-- The map on the targets of the two relative diagonals of `f` and `f'`. -/
noncomputable def diagonalTargetMap {X X' S S' : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ S) (f' : X' ⟶ S') (j : S ⟶ S')
    (h : i ≫ f' = f ≫ j) :
    pullback f f ⟶ pullback f' f' :=
  diagonalBaseComparison f j ≫ diagonalTargetFst i f f' j h ≫
    diagonalTargetSnd i f f' j h

/-- Enlarging the base along a closed immersion does not change the self-fibre product
of `X`. -/
theorem isIso_diagonalBaseComparison {X S S' : Scheme.{u}}
    (f : X ⟶ S) (j : S ⟶ S') [IsClosedImmersion j] :
    IsIso (diagonalBaseComparison f j) := by
  let inv : pullback (f ≫ j) (f ≫ j) ⟶ pullback f f :=
    pullback.lift (pullback.fst (f ≫ j) (f ≫ j))
      (pullback.snd (f ≫ j) (f ≫ j)) (by
        apply (cancel_mono j).mp
        simpa only [Category.assoc] using pullback.condition (f := f ≫ j) (g := f ≫ j))
  have hf : diagonalBaseComparison f j ≫ pullback.fst (f ≫ j) (f ≫ j) =
      pullback.fst f f := by
    simp [diagonalBaseComparison, pullback.map, pullback.lift_fst]
  have hs : diagonalBaseComparison f j ≫ pullback.snd (f ≫ j) (f ≫ j) =
      pullback.snd f f := by
    simp [diagonalBaseComparison, pullback.map, pullback.lift_snd]
  have h₁ : diagonalBaseComparison f j ≫ inv = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hf]
      simp
    · rw [Category.assoc, pullback.lift_snd, hs]
      simp
  have h₂ : inv ≫ diagonalBaseComparison f j = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hf, pullback.lift_fst]
      simp
    · rw [Category.assoc, hs, pullback.lift_snd]
      simp
  exact ⟨⟨inv, h₁, h₂⟩⟩

/-- Replacing the first factor `X` of `X ×_{S'} T` by a thickening `X ⟶ X'` over `S'` is a
thickening. -/
private theorem isThickening_pullback_lift_fst_comp {X X' S' T : Scheme.{u}}
    (i : X ⟶ X') (f' : X' ⟶ S') (a : X ⟶ S') (b : T ⟶ S') (h : i ≫ f' = a)
    (hi : IsThickening i) :
    IsThickening (pullback.lift (f := f') (g := b) (pullback.fst a b ≫ i) (pullback.snd a b)
      (by simpa only [Category.assoc, h] using pullback.condition (f := a) (g := b))) :=
  MorphismProperty.pullbackLift_fst_snd (f := b) (v₁₂ := a) (v₂₂ := f') (g := i)
    (hv₁₂ := h.symm) hi

/-- The first arrow in the factorization of the map on diagonal targets is a thickening,
being a base change of `i`. -/
theorem isThickening_diagonalTargetFst {X X' S S' : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ S) (f' : X' ⟶ S') (j : S ⟶ S')
    (h : i ≫ f' = f ≫ j) (hi : IsThickening i) :
    IsThickening (diagonalTargetFst i f f' j h) := by
  have heq : diagonalTargetFst i f f' j h =
      (pullbackSymmetry (f ≫ j) (f ≫ j)).hom ≫
      pullback.lift (f := f') (g := f ≫ j) (pullback.fst (f ≫ j) (f ≫ j) ≫ i)
        (pullback.snd (f ≫ j) (f ≫ j)) (by
          simpa only [Category.assoc, h] using
            (pullback.condition (f := f ≫ j) (g := f ≫ j))) ≫
      (pullbackSymmetry f' (f ≫ j)).hom := by
    apply pullback.hom_ext <;>
      simp [diagonalTargetFst, pullback.map, pullback.lift_fst, pullback.lift_snd]
  rw [heq]
  exact isThickening_comp (isThickening_of_isIso _)
    (isThickening_comp (isThickening_pullback_lift_fst_comp i f' _ _ h hi)
      (isThickening_of_isIso _))

/-- The second arrow in the factorization of the map on diagonal targets is a thickening,
being a base change of `i`. -/
theorem isThickening_diagonalTargetSnd {X X' S S' : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ S) (f' : X' ⟶ S') (j : S ⟶ S')
    (h : i ≫ f' = f ≫ j) (hi : IsThickening i) :
    IsThickening (diagonalTargetSnd i f f' j h) := by
  have heq : diagonalTargetSnd i f f' j h =
      pullback.lift (f := f') (g := f') (pullback.fst (f ≫ j) f' ≫ i)
        (pullback.snd (f ≫ j) f') (by
          simpa only [Category.assoc, h] using
            (pullback.condition (f := f ≫ j) (g := f'))) := by
    apply pullback.hom_ext <;>
      simp [diagonalTargetSnd, pullback.map]
  rw [heq]
  exact isThickening_pullback_lift_fst_comp i f' _ _ h hi

/-- The map on the targets of the two relative diagonals is a thickening. -/
theorem isThickening_diagonalTargetMap {X X' S S' : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ S) (f' : X' ⟶ S') (j : S ⟶ S')
    (h : i ≫ f' = f ≫ j) (hi : IsThickening i) (hj : IsThickening j) :
    IsThickening (diagonalTargetMap i f f' j h) := by
  have _ : IsClosedImmersion j := hj.1
  have _ : IsIso (diagonalBaseComparison f j) := isIso_diagonalBaseComparison f j
  exact isThickening_comp (isThickening_of_isIso _)
    (isThickening_comp (isThickening_diagonalTargetFst i f f' j h hi)
      (isThickening_diagonalTargetSnd i f f' j h hi))

/-- The two relative diagonals commute with `i` and with the map on their targets. -/
theorem diagonal_comp_diagonalTargetMap {X X' S S' : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ S) (f' : X' ⟶ S') (j : S ⟶ S')
    (h : i ≫ f' = f ≫ j) :
    pullback.diagonal f ≫ diagonalTargetMap i f f' j h = i ≫ pullback.diagonal f' := by
  apply pullback.hom_ext <;>
    simp [diagonalTargetMap, diagonalBaseComparison, diagonalTargetFst,
      diagonalTargetSnd, pullback.map, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]

end Stacks.Thickenings

end
