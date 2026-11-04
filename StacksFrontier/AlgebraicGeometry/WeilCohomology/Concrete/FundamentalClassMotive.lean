module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.FundamentalClassTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveMonoidDuality
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTateTensorHom
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiUnitTwistTraceMonObj
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The fundamental class as a morphism of motives

Let `X` be a smooth projective scheme over a field `k`, equidimensional of dimension `d`. By
Stacks 0FG0 the fundamental class `[X] ∈ CH_d(X) ⊗ ℚ = Corr^{-d}(X, Spec k)` is a morphism of
motives `h(X)(d) = h(X) ⊗ 𝟏(d) ⟶ 𝟏` (proof of Stacks 0FHK, datum (D3)). Applying a realization
`G` and taking degree `0` parts, it gives the trace map `∫_X : H^{2d}(X)(d) → F`.

The fundamental classes are multiplicative: `[X × Y]`, precomposed with
`h(X) ⊗ h(Y) ⟶ h(X × Y)` and `𝟏(d) ⊗ 𝟏(e) ⟶ 𝟏(d + e)`, is `[X] ⊗ [Y]` after the interchange
(`Stacks.WeilCohomology.ChowMotiveCat.fundamentalClassMot_tensor`). This gives axiom (B)(b) for a
realization.

## Main definitions

* `Stacks.WeilCohomology.ChowMotiveCat.fundamentalClassMot`: `[X] : h(X) ⊗ 𝟏(d) ⟶ 𝟏`.

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.fundamentalClassMot_tensor`: multiplicativity.

## Implementation notes

As in `StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveMonoid`, the motive `h(X)` is
spelled `TwistedKaroubi.ofObj (𝐎 X)`, the twisted units `TwistedKaroubi.tateTriple`, and only the
generic monoidal structure `TwistedKaroubi.monoidalCategory` of the twisted Karoubi envelope is
used: comparing morphisms built over different instance paths unfolds correspondences down to
cycles.

## References

* [Stacks Project, Tag 0FHK](https://stacks.math.columbia.edu/tag/0FHK)
* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CategoryTheory.GradedCategory

universe u

namespace Stacks.WeilCohomology.ChowMotiveCat

attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

local notation "𝐎" => (GradedCompositionData.Obj.mk :
  CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
    CorrespondenceCategory _)

variable {k : Type u} [Field k] {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}

/-- **The fundamental class `[X] : h(X) ⊗ 𝟏(d) ⟶ 𝟏`** of `X` equidimensional of dimension `d`:
the class `[X] ∈ Corr^{-d}(X, Spec k)` (`Stacks.WeilCohomology.fundamentalClassHom`), through
`X × Spec k ≅ X` (`CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistTrace`). It is the
morphism through which the counit of the duality of Stacks 0FGI factors
(`Stacks.WeilCohomology.ChowMotiveCat.evaluation_exactPairingMotive`). -/
def fundamentalClassMot (hX : RelativeDimension X.obj.hom d) :=
  TwistedKaroubi.unitTwistTrace (R := ℚ) (d : ℤ) (fundamentalClassHom hX)
    (fundamentalClassHom_mem_grade hX)

/-- **`([X] ⊗ [Y]) ≫ λ = (([Γ_{pr₁}] ⊗ [Γ_{pr₂}]) ≫ [Γ_Δ]) ≫ [X × Y]`** in the category of
correspondences, for `X`, `Y` equidimensional of dimensions `d`, `e`: the multiplicativity of
fundamental classes, through the comparison `h(X) ⊗ h(Y) ⟶ h(X × Y)` given by the multiplication
of `h(X × Y)`. -/
theorem fundamentalClassHom_tensorHom_comp_leftUnitor_eq_mul_comp
    {Y : (SmoothProjectiveScheme k).FullSubcategory} {e : ℕ} (hX : RelativeDimension X.obj.hom d)
    (hY : RelativeDimension Y.obj.hom e)
    (hXY : RelativeDimension (X ⊗ Y).obj.hom (d + e)) :
    (fundamentalClassHom hX ⊗ₘ fundamentalClassHom hY) ≫
        (λ_ (𝟙_ (CorrespondenceCategory k))).hom =
      (((graphHom (CorrespondenceCategory.tensorFst X Y) : 𝐎 X ⟶ 𝐎 (X ⊗ Y)) ⊗ₘ
        (graphHom (CorrespondenceCategory.tensorSnd X Y) : 𝐎 Y ⟶ 𝐎 (X ⊗ Y))) ≫
          MonObj.mul (X := 𝐎 (X ⊗ Y))) ≫ fundamentalClassHom hXY := by
  rw [CorrespondenceCategory.tensorHom_graphHom_tensorFst_tensorSnd_mul, Category.id_comp]
  exact fundamentalClassHom_tensorHom_comp_leftUnitor hX hY hXY

/-- `h(f)` is the morphism of `TwistedKaroubi.ofObjHom` on the graph of `f`. -/
private theorem motMap_eq_ofObjHom {Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : Z ⟶ Y) :
    motMap f = TwistedKaroubi.ofObjHom (X := 𝐎 Y) (Y := 𝐎 Z) (motMap f).val
      (CorrespondenceCategory.graphHom_mem_grade' f) :=
  rfl

/-- **The fundamental classes are multiplicative** (Stacks 0FHK, proof of (B)(b)): `[X × Y]`,
precomposed with `h(X) ⊗ h(Y) ⟶ h(X × Y)` (the multiplication of `h(X × Y)` after
`h(pr₁) ⊗ h(pr₂)`) and `𝟏(d) ⊗ 𝟏(e) ⟶ 𝟏(d + e)`, is `[X] ⊗ [Y]` after the interchange. -/
theorem fundamentalClassMot_tensor {Y : (SmoothProjectiveScheme k).FullSubcategory} {e : ℕ}
    (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e)
    (hXY : RelativeDimension (X ⊗ Y).obj.hom (d + e)) :
    (((motMap (CorrespondenceCategory.tensorFst X Y) ⊗ₘ
        motMap (CorrespondenceCategory.tensorSnd X Y)) ≫ MonObj.mul) ⊗ₘ
      TwistedKaroubi.tateTensorHom (R := ℚ)
        (C := (canonicalCorrespondenceCompositionData k).Obj) d e ((d + e : ℕ) : ℤ)
        (by push_cast; ring)) ≫ fundamentalClassMot hXY =
      tensorμ _ _ _ _ ≫ (fundamentalClassMot hX ⊗ₘ fundamentalClassMot hY) ≫ (λ_ _).hom := by
  have h := fundamentalClassHom_tensorHom_comp_leftUnitor_eq_mul_comp hX hY hXY
  have key := TwistedKaroubi.unitTwistTrace_tensor_ofObjHom_mul (R := ℚ)
    (C := (canonicalCorrespondenceCompositionData k).Obj) (A := 𝐎 X) (B := 𝐎 Y) (P := 𝐎 (X ⊗ Y))
    (CorrespondenceCategory.graphHom_mem_grade' _) (CorrespondenceCategory.graphHom_mem_grade' _)
    (motMap (CorrespondenceCategory.tensorFst X Y)).val
    (CorrespondenceCategory.graphHom_mem_grade' (CorrespondenceCategory.tensorFst X Y))
    (motMap (CorrespondenceCategory.tensorSnd X Y)).val
    (CorrespondenceCategory.graphHom_mem_grade' (CorrespondenceCategory.tensorSnd X Y))
    (fundamentalClassHom hX) (fundamentalClassHom hY) (fundamentalClassHom hXY)
    (fundamentalClassHom_mem_grade hX) (fundamentalClassHom_mem_grade hY)
    (fundamentalClassHom_mem_grade hXY) (by
      rw [motMap_val, motMap_val]
      generalize (graphHom (CorrespondenceCategory.tensorFst X Y) : 𝐎 X ⟶ 𝐎 (X ⊗ Y)) = f at h ⊢
      generalize (graphHom (CorrespondenceCategory.tensorSnd X Y) : 𝐎 Y ⟶ 𝐎 (X ⊗ Y)) = g at h ⊢
      generalize fundamentalClassHom hX = a at h ⊢
      generalize fundamentalClassHom hY = b at h ⊢
      generalize fundamentalClassHom hXY = c at h ⊢
      exact h)
    (TwistedKaroubi.tateTensorHom (R := ℚ)
        (C := (canonicalCorrespondenceCompositionData k).Obj) d e ((d + e : ℕ) : ℤ)
        (by push_cast; ring)) (TwistedKaroubi.tateTensorHom_val _ _ _ _)
  refine Eq.trans ?_ (key.trans ?_)
  · have e3 : fundamentalClassMot hXY = TwistedKaroubi.unitTwistTrace (R := ℚ) ((d + e : ℕ) : ℤ)
        (fundamentalClassHom hXY) (fundamentalClassHom_mem_grade hXY) := rfl
    conv_lhs =>
      rw [motMap_eq_ofObjHom (CorrespondenceCategory.tensorFst X Y),
        motMap_eq_ofObjHom (CorrespondenceCategory.tensorSnd X Y), e3]
  · rfl

end Stacks.WeilCohomology.ChowMotiveCat

end
