module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotiveAlgebra
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonObj
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The motive of a smooth projective scheme is a commutative monoid

Let `X` be a smooth projective scheme over a field `k`. The diagonal `Δ : X ⟶ X × X` and the
structure morphism `X ⟶ Spec k` make `X` a cocommutative comonoid for the product, so their
graphs make `X` a commutative monoid in the category of correspondences, with multiplication
`[Γ_Δ] : X ⊗ X ⟶ X` and unit `[Γ_{X → Spec k}] : 𝟏 ⟶ X`; the graph `[Γ_f]` of a morphism `f` is
a morphism of monoids. Hence the motive `h(X) = (X, 1, 0)` is a commutative monoid in `M_k` and
`h(f)` is a morphism of monoids. This is the source of the cup product in Stacks 0FH1: applying a
symmetric monoidal functor `G` gives the graded commutative algebra `H^*(X) = G(h(X))`.

## Main definitions

* `Stacks.WeilCohomology.CorrespondenceCategory.monObj`: the monoid `X` of correspondences.
* `Stacks.WeilCohomology.ChowMotiveCat.monObjMotive`: the monoid `h(X) = (X, 1, 0)`.
* `Stacks.WeilCohomology.ChowMotiveCat.motMap`: `h(f) = [Γ_f] : h(X) ⟶ h(Y)` for `f : Y ⟶ X`.

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.isCommMonObj_motive`: `h(X)` is commutative.
* `Stacks.WeilCohomology.ChowMotiveCat.isMonHom_motMap`: `h(f)` is a morphism of monoids;
  `motMap_comp`, `motMap_id`: `h` is a contravariant functor.
* `Stacks.WeilCohomology.ChowMotiveCat.isIso_motMap_fst_snd_mul`: `h(pr₁) ⊗ h(pr₂)` followed by
  the multiplication of `h(X × Y)` is an isomorphism `h(X) ⊗ h(Y) ≅ h(X × Y)`.

## Implementation notes

The monoids `h(X)` are spelled `TwistedKaroubi.ofObj (𝐎 X)` and the morphisms `h(f)` are
`TwistedKaroubi.ofObjHom [Γ_f]`, so that the generic results of
`StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonObj` apply on the nose; in the motive section
the monoidal structure is taken through the generic instances (see the comment there).

## References

* [Stacks Project, Tag 0FH1](https://stacks.math.columbia.edu/tag/0FH1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj Opposite

universe u

namespace Stacks.WeilCohomology

local notation "𝐎" => (GradedCompositionData.Obj.mk :
  CategoryTheory.ObjectProperty.FullSubcategory (SmoothProjectiveScheme _) →
    CorrespondenceCategory _)

namespace CorrespondenceCategory

variable {k : Type u} [Field k]

open SmoothProjectiveScheme

/-- `[Γ_f]` has degree `0`, for the grading of the category of correspondences. -/
theorem graphHom_mem_grade' {P Q : (SmoothProjectiveScheme k).FullSubcategory} (f : Q ⟶ P) :
    (graphHom f : 𝐎 P ⟶ 𝐎 Q) ∈ GradedCategory.grade (R := ℚ) (𝐎 P) (𝐎 Q) 0 :=
  graphHom_mem_grade f

/-- The diagonal `X ⟶ X ⊗ X` followed by `(X ⟶ Spec k) ▷ X` is the inverse left unitor. -/
theorem diag_toUnit_whiskerRight_eq (X : (SmoothProjectiveScheme k).FullSubcategory) :
    tensorDiag X ≫ (toUnit X ▷ X) = (λ_ X).inv :=
  (Iso.comp_hom_eq_id _).1 (by rw [Category.assoc]; exact diag_toUnit_whiskerRight X)

/-- The diagonal `X ⟶ X ⊗ X` followed by `X ◁ (X ⟶ Spec k)` is the inverse right unitor. -/
theorem diag_whiskerLeft_toUnit_eq (X : (SmoothProjectiveScheme k).FullSubcategory) :
    tensorDiag X ≫ (X ◁ toUnit X) = (ρ_ X).inv :=
  (Iso.comp_hom_eq_id _).1 (by rw [Category.assoc]; exact diag_whiskerLeft_toUnit X)

/-- Coassociativity of the diagonal: `Δ ≫ (Δ ▷ X) = Δ ≫ (X ◁ Δ) ≫ α⁻¹`. -/
theorem diag_whiskerRight_eq (X : (SmoothProjectiveScheme k).FullSubcategory) :
    tensorDiag X ≫ (tensorDiag X ▷ X) = tensorDiag X ≫ (X ◁ tensorDiag X) ≫ (α_ X X X).inv := by
  rw [← Category.assoc (tensorDiag X), ← diag_whiskerRight_associator, Category.assoc,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The first projection `X × Y ⟶ X`, with its source written as a tensor product. -/
abbrev tensorFst (X Y : (SmoothProjectiveScheme k).FullSubcategory) : X ⊗ Y ⟶ X := fst X Y

/-- The second projection `X × Y ⟶ Y`, with its source written as a tensor product. -/
abbrev tensorSnd (X Y : (SmoothProjectiveScheme k).FullSubcategory) : X ⊗ Y ⟶ Y := snd X Y

/-- The diagonal of `X ⊗ Y` followed by `pr₁ ⊗ pr₂` is the identity of `X ⊗ Y`. -/
theorem diag_tensorHom_tensorFst_tensorSnd (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    tensorDiag (X ⊗ Y) ≫ (tensorFst X Y ⊗ₘ tensorSnd X Y) = 𝟙 (X ⊗ Y) :=
  diag_tensorHom_fst_snd X Y

/-- Cocommutativity of the diagonal: `Δ ≫ β⁻¹ = Δ`. -/
theorem diag_braiding_inv (X : (SmoothProjectiveScheme k).FullSubcategory) :
    tensorDiag X ≫ (β_ X X).inv = tensorDiag X := by
  rw [← diag_braiding X, Category.assoc, Iso.hom_inv_id, Category.comp_id, diag_braiding]

/-- **The monoid of correspondences of a smooth projective scheme**: `X` with multiplication the
graph `[Γ_Δ] : X ⊗ X ⟶ X` of the diagonal and unit the graph `[Γ_{X → Spec k}] : 𝟏 ⟶ X` of the
structure morphism. -/
instance monObj (X : (SmoothProjectiveScheme k).FullSubcategory) : MonObj (𝐎 X) where
  one := graphHom (toUnit X)
  mul := graphHom (tensorDiag X)
  one_mul := by
    rw [graphHom_whiskerRight, graphHom_comp', diag_toUnit_whiskerRight_eq, leftUnitor_eq,
      graphIso_hom]
  mul_one := by
    rw [whiskerLeft_graphHom, graphHom_comp', diag_whiskerLeft_toUnit_eq, rightUnitor_eq,
      graphIso_hom]
  mul_assoc := by
    rw [graphHom_whiskerRight, whiskerLeft_graphHom, graphHom_comp', graphHom_comp',
      associator_eq, graphIso_hom, graphHom_comp', diag_whiskerRight_eq, Category.assoc]

/-- The unit of the monoid `X` is the graph `[Γ_{X → Spec k}]` of the structure morphism. -/
theorem one_eq_graphHom (X : (SmoothProjectiveScheme k).FullSubcategory) :
    η[𝐎 X] = graphHom (toUnit X) :=
  rfl

/-- The multiplication of the monoid `X` is the graph `[Γ_Δ]` of the diagonal. -/
theorem mul_eq_graphHom (X : (SmoothProjectiveScheme k).FullSubcategory) :
    μ[𝐎 X] = graphHom (tensorDiag X) :=
  rfl

/-- The monoid of correspondences of `X` is commutative. -/
instance isCommMonObj (X : (SmoothProjectiveScheme k).FullSubcategory) : IsCommMonObj (𝐎 X) where
  mul_comm := by
    rw [mul_eq_graphHom, braiding_eq, graphIso_hom, graphHom_comp', diag_braiding_inv]

/-- The graph `[Γ_f] : X ⟶ Y` of `f : Y ⟶ X` is a morphism of monoids. -/
instance isMonHom_graphHom {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : Y ⟶ X) :
    IsMonHom (M := 𝐎 X) (N := 𝐎 Y) (graphHom f) where
  one_hom := by
    rw [one_eq_graphHom, one_eq_graphHom, graphHom_comp', toUnit_unique (f ≫ toUnit X) (toUnit Y)]
  mul_hom := by
    rw [mul_eq_graphHom, mul_eq_graphHom, graphHom_comp', tensorHom_eq, tensorHom_graphHom_of_hom,
      graphHom_comp', diag_naturality]

section Kunneth

/- The tensor product is taken through `MonoidalCategory.toMonoidalCategoryStruct`, as in the
monoid-object API. -/
attribute [-instance] CorrespondenceCategory.monoidalCategoryStruct

/-- `[Γ_{pr₁}] ⊗ [Γ_{pr₂}]` followed by the multiplication `[Γ_Δ]` of `X × Y` is the identity of
`X × Y` in the category of correspondences. -/
theorem tensorHom_graphHom_tensorFst_tensorSnd_mul
    (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    ((graphHom (tensorFst X Y) : 𝐎 X ⟶ 𝐎 (X ⊗ Y)) ⊗ₘ
      (graphHom (tensorSnd X Y) : 𝐎 Y ⟶ 𝐎 (X ⊗ Y))) ≫ μ[𝐎 (X ⊗ Y)] = 𝟙 _ := by
  rw [mul_eq_graphHom, tensorHom_eq, tensorHom_graphHom_of_hom, graphHom_comp',
    diag_tensorHom_tensorFst_tensorSnd]
  exact graphHom_id _

end Kunneth

end CorrespondenceCategory

namespace ChowMotiveCat

variable {k : Type u} [Field k]

open CategoryTheory.GradedCategory SmoothProjectiveScheme

/- The monoidal structure of `M_k` is used here through the generic instances
`CategoryTheory.GradedCategory.TwistedKaroubi.monoidalCategory` and `braidedCategory` and through
`MonoidalCategory.toMonoidalCategoryStruct`, as in the generic results of
`StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonObj` that are specialised below. The instances
`ChowMotiveCat.monoidalCategory` (equal to the generic one by definition) and the direct
`TwistedKaroubi.monoidalCategoryStruct` are set aside in this section: comparing morphisms built
over the two instance paths makes `isDefEq` unfold correspondences down to cycles on fibre
products. -/
attribute [-instance] ChowMotiveCat.monoidalCategory ChowMotiveCat.braidedCategory
  ChowMotiveCat.symmetricCategory TwistedKaroubi.monoidalCategoryStruct

/-- **The motive `h(X)` is a monoid**: multiplication `[Γ_Δ] : h(X) ⊗ h(X) ⟶ h(X)` and unit
`[Γ_{X → Spec k}] : 𝟏 ⟶ h(X)`. -/
instance monObjMotive (X : (SmoothProjectiveScheme k).FullSubcategory) :
    MonObj (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) :=
  TwistedKaroubi.monObjOfObj (𝐎 X) (CorrespondenceCategory.graphHom_mem_grade' _)
    (CorrespondenceCategory.graphHom_mem_grade' _)

/-- The underlying correspondence of the multiplication of `h(X)` is that of `X`. -/
theorem mul_motive_val (X : (SmoothProjectiveScheme k).FullSubcategory) :
    μ[TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)].val = μ[𝐎 X] :=
  rfl

/-- The underlying correspondence of the unit of `h(X)` is that of `X`. -/
theorem one_motive_val (X : (SmoothProjectiveScheme k).FullSubcategory) :
    η[TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)].val = η[𝐎 X] :=
  rfl

/-- The monoid `h(X)` is commutative. -/
instance isCommMonObj_motive (X : (SmoothProjectiveScheme k).FullSubcategory) :
    IsCommMonObj (TwistedKaroubi.ofObj (R := ℚ) (𝐎 X)) :=
  TwistedKaroubi.isCommMonObj_ofObj (𝐎 X) (CorrespondenceCategory.graphHom_mem_grade' _)
    (CorrespondenceCategory.graphHom_mem_grade' _)

/-- The morphism `h(f) = [Γ_f] : h(X) ⟶ h(Y)` of `f : Y ⟶ X`, between untwisted triples; its
underlying correspondence is that of `Stacks.WeilCohomology.ChowMotiveCat.gmap`. -/
def motMap {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : Y ⟶ X) :=
  TwistedKaroubi.ofObjHom (R := ℚ) (X := 𝐎 X) (Y := 𝐎 Y) (graphHom f)
    (CorrespondenceCategory.graphHom_mem_grade' f)

/-- The underlying correspondence of `h(f)` is the graph `[Γ_f]`. -/
theorem motMap_val {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : Y ⟶ X) :
    (motMap f).val = (graphHom f : 𝐎 X ⟶ 𝐎 Y) :=
  rfl

/-- `h(f) ≫ h(g) = h(g ≫ f)`. -/
theorem motMap_comp {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : Y ⟶ X) (g : Z ⟶ Y) :
    motMap f ≫ motMap g = motMap (g ≫ f) := by
  apply TwistedKaroubi.hom_ext
  rw [TwistedKaroubi.comp_val, motMap_val, motMap_val, motMap_val]
  exact graphHom_comp f g

/-- `h(𝟙 X)` is the identity of `h(X)`. -/
theorem motMap_id (X : (SmoothProjectiveScheme k).FullSubcategory) : motMap (𝟙 X) = 𝟙 _ := by
  apply TwistedKaroubi.hom_ext
  rw [motMap_val, TwistedKaroubi.id_val, TwistedKaroubi.ofObj_p]
  exact graphHom_id X

/-- `h(f) = [Γ_f] : h(X) ⟶ h(Y)` is a morphism of monoids. -/
instance isMonHom_motMap {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : Y ⟶ X) :
    IsMonHom (motMap f) :=
  TwistedKaroubi.isMonHom_ofObjHom _ _ _ _ (graphHom f)
    (CorrespondenceCategory.graphHom_mem_grade' f)

/-- **`h(X) ⊗ h(Y) = h(X × Y)` through the multiplication of `h(X × Y)`**: the composite
`h(X) ⊗ h(Y) ⟶ h(X × Y) ⊗ h(X × Y) ⟶ h(X × Y)` of `h(pr₁) ⊗ h(pr₂)` and the multiplication is an
isomorphism; its underlying correspondence is the identity of `X × Y`. -/
theorem isIso_motMap_fst_snd_mul (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    IsIso ((motMap (CorrespondenceCategory.tensorFst X Y) ⊗ₘ
      motMap (CorrespondenceCategory.tensorSnd X Y)) ≫ MonObj.mul) := by
  refine TwistedKaroubi.isIso_tensorHom_ofObjHom_mul (R := ℚ)
    (X := 𝐎 X) (Y := 𝐎 Y) (P := 𝐎 (X ⊗ Y)) (CorrespondenceCategory.graphHom_mem_grade' _)
    (CorrespondenceCategory.graphHom_mem_grade' _) (graphHom (CorrespondenceCategory.tensorFst X Y))
    (CorrespondenceCategory.graphHom_mem_grade' _) (graphHom (CorrespondenceCategory.tensorSnd X Y))
    (CorrespondenceCategory.graphHom_mem_grade' _) (𝟙 _) (GradedCategory.id_mem _) ?_ ?_
  · rw [Category.comp_id, CorrespondenceCategory.tensorHom_graphHom_tensorFst_tensorSnd_mul]
  · rw [Category.id_comp, CorrespondenceCategory.tensorHom_graphHom_tensorFst_tensorSnd_mul]
    rfl

end ChowMotiveCat

end Stacks.WeilCohomology

end
