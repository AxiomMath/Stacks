module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassExteriorProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveCycleClassAxioms
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.PointCorrTensor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Axiom (C)(c) for the cycle class map of a realization: the motive identity

Let `X` be a smooth projective scheme over `k` and `α ∈ CH^i(X)`, `β ∈ CH^j(X)`, with
correspondences `a_α : 𝟏(-i) ⟶ h(X)` and `a_β : 𝟏(-j) ⟶ h(X)` (Stacks 0FG0). The proof
of the axiom (C)(c) in Stacks 0FH1 uses Remark 0FGU: the intersection product is
`α · β = Δ^!(α × β)`, and `α × β` corresponds to `a_α ⊗ a_β`. This file proves the resulting
identity of morphisms of motives

  `(a_α ⊗ a_β) ≫ [Γ_Δ] = (𝟏(-i) ⊗ 𝟏(-j) ≅ 𝟏(-(i + j))) ≫ a_{α · β}`,

from which `γ(α · β) = γ(α) ∪ γ(β)` follows for every realization (Stacks 0FHK,
`Stacks.WeilCohomology.WeilRealization.cycleClassMul_of_pointMotiveHom`).

## Main results

* `Stacks.WeilCohomology.pointCorrHom_codimensionExteriorProduct_comp_graphHom_tensorDiag`:
  `a_{α × β} ∘ [Γ_Δ] = a_{α · β}`.
* `Stacks.WeilCohomology.pointCorrHom_tensorHom_pointCorrHom_mul`:
  `(a_α ⊗ a_β) ≫ [Γ_Δ] = ρ ≫ a_{α · β}` in the category of correspondences.
* `Stacks.WeilCohomology.ChowMotiveCat.pointMotiveHom_tensorHom_comp_mul`: the same on motives.

## References

* [Stacks Project, Tag 0FH1](https://stacks.math.columbia.edu/tag/0FH1)
* [Stacks Project, Tag 0FGU](https://stacks.math.columbia.edu/tag/0FGU)
* [Stacks Project, Tag 0FHD](https://stacks.math.columbia.edu/tag/0FHD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

open CorrespondenceCategory ChowMotiveCat SmoothProjectiveScheme

variable {k : Type u} [Field k]

local notation "𝐎" =>
  (GradedCompositionData.Obj.mk :
    CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
      CorrespondenceCategory _)

/-- `Δ^!(α × β) = α · β`, with the diagonal `X ⟶ X ⊗ X` of smooth projective schemes. -/
theorem codimensionGysin_tensorDiag_codimensionExteriorProduct
    (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) (β : codimensionChowGroup k X.obj.hom j) :
    codimensionGysin X.obj.hom (X ⊗ X).obj.hom (Over.w (tensorDiag X).hom) (i + j)
        (codimensionExteriorProduct k X.obj.hom X.obj.hom i j α β) =
      codimensionIntersectionProduct k X.obj.hom i j α β :=
  (codimensionIntersectionProduct_eq_codimensionGysin_diag X.obj.hom i j α β).symm

/-- **`a_{α × β} ∘ [Γ_Δ] = a_{α · β}`** (Remark 0FHD and Stacks 0FG5 (1)): pulling the exterior
product back along the diagonal is the intersection product. -/
theorem pointCorrHom_codimensionExteriorProduct_comp_graphHom_tensorDiag
    (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) (β : codimensionChowGroup k X.obj.hom j) :
    pointCorrHom (X ⊗ X) (i + j) (codimensionExteriorProduct k X.obj.hom X.obj.hom i j α β) ≫
        (graphHom (tensorDiag X) : 𝐎 (X ⊗ X) ⟶ 𝐎 X) =
      pointCorrHom X (i + j) (codimensionIntersectionProduct k X.obj.hom i j α β) := by
  rw [pointCorrHom_comp_graphHom, codimensionGysin_tensorDiag_codimensionExteriorProduct]

section Monoidal

attribute [-instance] CorrespondenceCategory.monoidalCategoryStruct

/-- **`(a_α ⊗ a_β) ≫ μ_X = ρ ≫ a_{α · β}`** in the category of correspondences: `a_α ⊗ a_β` is
`ρ ≫ a_{α × β}` (`Stacks.WeilCohomology.tensorHom_pointCorrHom`), and `a_{α × β} ∘ [Γ_Δ]` is
`a_{Δ^!(α × β)} = a_{α · β}`. -/
theorem pointCorrHom_tensorHom_pointCorrHom_mul (X : (SmoothProjectiveScheme k).FullSubcategory)
    (i j : ℤ) (α : codimensionChowGroup k X.obj.hom i) (β : codimensionChowGroup k X.obj.hom j) :
    (pointCorrHom X i α ⊗ₘ pointCorrHom X j β) ≫ MonObj.mul (X := 𝐎 X) =
      (CorrespondenceCategory.rightUnitorIso
          (𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)))).hom ≫
        pointCorrHom X (i + j) (codimensionIntersectionProduct k X.obj.hom i j α β) := by
  have h₁ := tensorHom_pointCorrHom X X i j α β
  have h₂ := pointCorrHom_codimensionExteriorProduct_comp_graphHom_tensorDiag X i j α β
  have h₃ : CorrespondenceCategory.tensorHom (pointCorrHom X i α) (pointCorrHom X j β) ≫
      (graphHom (tensorDiag X) : 𝐎 (X ⊗ X) ⟶ 𝐎 X) =
      (CorrespondenceCategory.rightUnitorIso
          (𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)))).hom ≫
        pointCorrHom X (i + j) (codimensionIntersectionProduct k X.obj.hom i j α β) := by
    rw [← Iso.inv_comp_eq, ← Category.assoc, h₁]
    convert h₂ using 0
  rw [CorrespondenceCategory.mul_eq_graphHom]
  simp only [CorrespondenceCategory.tensorHom_eq, CorrespondenceCategory.tensorObj_eq]
  convert h₃ using 0

end Monoidal

namespace ChowMotiveCat

open CategoryTheory.GradedCategory

attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct
  CorrespondenceCategory.monoidalCategoryStruct TwistedKaroubi.symmetricCategory

/-- **Stacks 0FH1, proof of (C)(c), on motives**: `(a_α ⊗ a_β) ≫ μ = (𝟏(-i) ⊗ 𝟏(-j) ⟶ 𝟏(-(i+j)))
≫ a_{α · β}` for `α ∈ CH^i(X)` and `β ∈ CH^j(X)`, with `μ = [Γ_Δ]` the multiplication of
`h(X)`. -/
theorem pointMotiveHom_tensorHom_comp_mul (X : (SmoothProjectiveScheme k).FullSubcategory) (i j : ℤ)
    (α : codimensionChowGroup k X.obj.hom i) (β : codimensionChowGroup k X.obj.hom j) :
    (pointMotiveHom X i α ⊗ₘ pointMotiveHom X j β) ≫
        MonObj.mul (X := TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) =
      TwistedKaroubi.tateTensorHomOfEq (R := ℚ)
          (C := (canonicalCorrespondenceCompositionData k).Obj) (M := tate k (-i))
          (N := tate k (-j)) (P := tate k (-(i + j))) (-i) (-j) (-(i + j))
          (by ring) rfl rfl rfl ≫
        pointMotiveHom X (i + j) (codimensionIntersectionProduct k X.obj.hom i j α β) := by
  have key := TwistedKaroubi.tensorHom_comp_eq_tateTensorHomOfEq_comp (A := 𝐎 X)
    (U := 𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory))) (M := tate k (-i)) (N := tate k (-j))
    (P := tate k (-(i + j))) (n := -i) (m := -j) (p := -(i + j)) (by ring) rfl rfl rfl rfl
    (pointMotiveHom X i α) (pointMotiveHom X j β)
    (MonObj.mul (X := TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)))
    (pointMotiveHom X (i + j) (codimensionIntersectionProduct k X.obj.hom i j α β))
    (pointCorrHom X i α) (pointCorrHom X j β)
    (pointCorrHom X (i + j) (codimensionIntersectionProduct k X.obj.hom i j α β))
    (MonObj.mul (X := 𝐎 X))
    (CorrespondenceCategory.rightUnitorIso
      (𝐎 (𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)))).hom
    HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl (by
      have h := pointCorrHom_tensorHom_pointCorrHom_mul X i j α β
      convert h using 0)
  convert key using 3

end ChowMotiveCat

end Stacks.WeilCohomology

end
