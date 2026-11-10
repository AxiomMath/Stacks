module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGluing
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditional
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditionalSupplement
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningAffineGluing
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningAffineGluingSquare

/-!
# The last assertion of Tag 07RV, on prescribed squares

Let `i : X ⟶ X'` be a thickening of schemes and `f : X ⟶ Y` an affine morphism, and let
`w : Q' ⟶ Q` be a morphism between two cocartesian squares on thickenings and affine morphisms,
lying over them along the two cartesian squares of a triple.  This module proves that the two
remaining lateral squares are cartesian as well: the pieces of the triple are recovered from the
glued scheme by base change.  The five clauses of [Stacks Project, Tag 07RX] on such prescribed
squares are `AlgebraicGeometry.ThickeningAffineGluing.etale_induced_iff_of_isPushout` and its
siblings.

This is the form in which the construction of [Stacks Project, Tag 07VX] consumes Tag 07RV: the
two projections of the relation `R' ⨿_{R₀} T ⇉ U' ⨿_U V` are morphisms between prescribed
pushouts, induced by the two projections of the kernel pairs.

## Main results

* `AlgebraicGeometry.ThickeningAffinePushoutSituation.isPullback_of_isPushout_of_isPullback`: the
  last assertion of Tag 07RV on prescribed squares.

## References

* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Thickenings

universe u

namespace AlgebraicGeometry

namespace ThickeningAffinePushoutSituation

variable {X X' Y Q : Scheme.{u}} {i : X ⟶ X'} {f : X ⟶ Y} {A : X' ⟶ Q} {B : Y ⟶ Q}

variable {Z Z' W Q' : Scheme.{u}} {k : Z ⟶ Z'} {g : Z ⟶ W} {A' : Z' ⟶ Q'} {B' : W ⟶ Q'}

section clauses

variable (hpo : IsPushout i f A B) (hi : IsThickening i) [IsAffineHom f]
  (hpo' : IsPushout k g A' B')
  {toX' : Z' ⟶ X'} {toY : W ⟶ Y} {toX : Z ⟶ X}
  (hpi : IsPullback k toX toX' i) (hpf : IsPullback g toX toY f) {w : Q' ⟶ Q}
  (hwA : A' ≫ w = toX' ≫ A) (hwB : B' ≫ w = toY ≫ B)
include hpo hi hpo' hpi hpf hwA hwB

/-- **The last assertion of [Stacks Project, Tag 07RV], on prescribed squares.**  For a
morphism `w : Q' ⟶ Q` between two cocartesian squares on thickenings and affine morphisms,
lying over them along the two cartesian squares `Z = Z' ×_{X'} X` and `Z = W ×_Y X`, the two
remaining lateral squares are cartesian too: `W = Q' ×_Q Y` and `Z' = Q' ×_Q X'`. -/
theorem isPullback_of_isPushout_of_isPullback :
    IsPullback B' toY w B ∧ IsPullback A' toX' w A := by
  have : HasPushout i f := hpo.hasPushout
  -- the triple as a compatible pair over the canonical pushout
  let φ : (Over.pullback f).obj (Over.mk toY) ⟶ (Over.pullback i).obj (Over.mk toX') :=
    Over.homMk (hpf.isoPullback.inv ≫ hpi.isoPullback.hom) (by simp)
  let ψ : (Over.pullback i).obj (Over.mk toX') ⟶ (Over.pullback f).obj (Over.mk toY) :=
    Over.homMk (hpi.isoPullback.inv ≫ hpf.isoPullback.hom) (by simp)
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    ext
    simp [φ, ψ]
  have hiso : IsIso φ := ⟨ψ, hφψ, by ext; simp [φ, ψ]⟩
  let T : Stacks.Pushout.gluingData i f := ⟨⟨Over.mk toY, Over.mk toX', φ⟩, hiso⟩
  have := Stacks.Pushout.gluingHasPushout i f hi T
  have hinv : inv T.obj.hom = ψ := IsIso.inv_eq_of_hom_inv_id hφψ
  have hsrc : hpi.isoPullback.hom ≫ Stacks.Pushout.gluingSourceMap i f T = g := by
    change hpi.isoPullback.hom ≫ (inv T.obj.hom).left ≫ pullback.fst toY f = g
    rw [hinv]
    simp [ψ]
  -- the prescribed square on the triple is a pushout of the span of the compatible pair
  have hpo'' : IsPushout (pullback.fst T.obj.right.hom i)
      (Stacks.Pushout.gluingSourceMap i f T) A' B' :=
    hpo'.of_iso hpi.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id]; exact hpi.isoPullback_hom_fst.symm)
      (by simpa using hsrc.symm) (by simp) (by simp)
  let e' := (IsPushout.of_hasPushout (pullback.fst T.obj.right.hom i)
    (Stacks.Pushout.gluingSourceMap i f T)).isoIsPushout _ _ hpo''
  have he'l : pushout.inl _ _ ≫ e'.hom = A' := IsPushout.inl_isoIsPushout_hom _ _ _ hpo''
  have he'r : pushout.inr _ _ ≫ e'.hom = B' := IsPushout.inr_isoIsPushout_hom _ _ _ hpo''
  let e₀ := (IsPushout.of_hasPushout i f).isoIsPushout _ _ hpo
  have he₀l : pushout.inl i f ≫ e₀.hom = A := IsPushout.inl_isoIsPushout_hom _ _ _ hpo
  have he₀r : pushout.inr i f ≫ e₀.hom = B := IsPushout.inr_isoIsPushout_hom _ _ _ hpo
  have hG : (Stacks.Pushout.gluingPushoutData i f T).hom ≫ e₀.hom = e'.hom ≫ w := by
    refine (IsPushout.of_hasPushout (pullback.fst T.obj.right.hom i)
      (Stacks.Pushout.gluingSourceMap i f T)).hom_ext ?_ ?_
    · rw [← Category.assoc, Stacks.Pushout.gluingPushoutData_inl i f T, Category.assoc, he₀l,
        ← Category.assoc, he'l, hwA]
      rfl
    · rw [← Category.assoc, Stacks.Pushout.gluingPushoutData_inr i f T, Category.assoc, he₀r,
        ← Category.assoc, he'r, hwB]
      rfl
  obtain ⟨h₁, h₂⟩ := Stacks.Pushout.gluing_components_isPullback i f hi T
  refine ⟨h₁.of_iso (Iso.refl _) e' (Iso.refl _) e₀ ?_ ?_ hG ?_,
    h₂.of_iso (Iso.refl _) e' (Iso.refl _) e₀ ?_ ?_ hG ?_⟩ <;>
    simp [he'l, he'r, he₀l, he₀r] <;> rfl

end clauses

end ThickeningAffinePushoutSituation

end AlgebraicGeometry

end
