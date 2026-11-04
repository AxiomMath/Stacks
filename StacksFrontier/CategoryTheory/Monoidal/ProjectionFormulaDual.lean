module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.Currying
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# The projection formula for a dual is the mate of the inverse projection formula

Let `F : C ⥤ D` be a strong monoidal functor with a right adjoint `G`, `adj : F ⊣ G`. For `K` in
`C` the *projection formula map* `K ⊗ G E ⟶ G (F K ⊗ E)` is the mate, for `adj` on both sides,
of the oplax structure map `δ : F (K ⊗ X) ⟶ F K ⊗ F X`. If `K'` is a right dual of `K`
(`ExactPairing K K'`), then `F K'` is a right dual of `F K` (`CategoryTheory.ExactPairing.map`),
tensoring with `K'` is left adjoint to tensoring with `K` on both sides
(`CategoryTheory.tensorLeftAdjunction`), and the mate of the projection formula map for `K'` for
these two adjunctions is the inverse of the projection formula map for `K`. In particular the
projection formula map of a dualizable object is invertible.

## Main definitions

* `CategoryTheory.ProjectionFormula.tensorLeftδ`, `CategoryTheory.ProjectionFormula.tensorLeftμ`:
  the structure maps of `F` with a fixed left factor, as 2-squares.
* `CategoryTheory.ProjectionFormula.projection`: the projection formula map as a 2-square.

## Main results

* `CategoryTheory.ProjectionFormula.adjunctionTensorMap_eq_projection_app`: the projection formula
  map is `CategoryTheory.adjunctionTensorMap` for the comparison `δ`.
* `CategoryTheory.ProjectionFormula.mateEquiv_tensorLeftμ`: for a pairing `(K, K')`, the mate of
  `μ` with left factor `K'` is `δ` with left factor `K`.
* `CategoryTheory.ProjectionFormula.mateEquiv_projection_comp_projection` and
  `CategoryTheory.ProjectionFormula.projection_comp_mateEquiv_projection`: the mate of the
  projection formula map for `K'` is inverse to the projection formula map for `K`.
* `CategoryTheory.ProjectionFormula.mateEquiv_projection_eq_inv`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Prod

namespace CategoryTheory.ProjectionFormula

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]

/-- The oplax structure map `δ : F (K ⊗ X) ⟶ F K ⊗ F X` with fixed left factor `K`, as a
2-square `tensorLeft K ⋙ F ⟶ F ⋙ tensorLeft (F K)`. -/
def tensorLeftδ (K : C) : TwoSquare (tensorLeft K) F F (tensorLeft (F.obj K)) :=
  TwoSquare.mk _ _ _ _
    { app := fun X => δ F K X
      naturality := fun _ _ f => (δ_natural_right F K f).symm }

/-- The component of `tensorLeftδ F K` at `X` is `δ F K X`. -/
@[simp]
theorem tensorLeftδ_app (K X : C) : (tensorLeftδ F K).app X = δ F K X := rfl

/-- The lax structure map `μ : F K ⊗ F X ⟶ F (K ⊗ X)` with fixed left factor `K`, as a
2-square `F ⋙ tensorLeft (F K) ⟶ tensorLeft K ⋙ F`. -/
def tensorLeftμ (K : C) : TwoSquare F (tensorLeft K) (tensorLeft (F.obj K)) F :=
  TwoSquare.mk _ _ _ _
    { app := fun X => μ F K X
      naturality := fun _ _ f => μ_natural_right F K f }

/-- The component of `tensorLeftμ F K` at `X` is `μ F K X`. -/
@[simp]
theorem tensorLeftμ_app (K X : C) : (tensorLeftμ F K).app X = μ F K X := rfl

/-- The image under `F` of the right triangle identity of `(K' ⊗ -) ⊣ (K ⊗ -)`, written through
the structure maps of `F` and the image pairing. -/
private theorem map_right_triangle (K K' X : C) [ExactPairing K K'] :
    letI := ExactPairing.map F K K'
    (tensorLeftAdjunction (F.obj K) (F.obj K')).unit.app (F.obj (K ⊗ X)) ≫
      F.obj K ◁ μ F K' (K ⊗ X) ≫ F.obj K ◁ F.map ((tensorLeftAdjunction K K').counit.app X)
      ≫ μ F K X =
    F.map ((tensorLeftAdjunction K K').unit.app (K ⊗ X) ≫
        K ◁ ((tensorLeftAdjunction K K').counit.app X)) := by
  let := ExactPairing.map F K K'
  simp only [tensorLeftAdjunction, Adjunction.mkOfHomEquiv_unit_app,
    Adjunction.mkOfHomEquiv_counit_app, tensorLeftHomEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
    MonoidalCategory.whiskerLeft_id, Category.id_comp, ExactPairing.map_coevaluation]
  dsimp only [MonoidalCategory.curriedTensor_obj_obj]
  simp only [Functor.map_comp, Category.assoc, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [Functor.Monoidal.map_leftUnitor_inv F (K ⊗ X),
    Functor.Monoidal.map_whiskerRight F (η_ K K') (K ⊗ X),
    Functor.Monoidal.map_associator F K K' (K ⊗ X),
    Functor.Monoidal.map_whiskerLeft F K ((α_ K' K X).inv ≫ ε_ K K' ▷ X ≫ (λ_ X).hom)]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc, comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Functor.map_comp]

/-- For a pairing `(K, K')`, the mate of `μ` with left factor `K'`, for the adjunctions
`(K' ⊗ -) ⊣ (K ⊗ -)` and `(F K' ⊗ -) ⊣ (F K ⊗ -)`, is `δ` with left factor `K`. -/
theorem mateEquiv_tensorLeftμ (K K' : C) [ExactPairing K K'] :
    letI := ExactPairing.map F K K'
    mateEquiv (tensorLeftAdjunction K K') (tensorLeftAdjunction (F.obj K) (F.obj K'))
      (tensorLeftμ F K') = tensorLeftδ F K := by
  let := ExactPairing.map F K K'
  ext X
  have ht : (tensorLeftAdjunction K K').unit.app (K ⊗ X) ≫
      K ◁ ((tensorLeftAdjunction K K').counit.app X) = 𝟙 _ :=
    (tensorLeftAdjunction K K').right_triangle_components X
  have key := map_right_triangle F K K' X
  rw [ht, F.map_id] at key
  have e : (mateEquiv (tensorLeftAdjunction K K') (tensorLeftAdjunction (F.obj K) (F.obj K'))
      (tensorLeftμ F K')).app X =
      (tensorLeftAdjunction (F.obj K) (F.obj K')).unit.app (F.obj (K ⊗ X)) ≫
        F.obj K ◁ μ F K' (K ⊗ X) ≫
          F.obj K ◁ F.map ((tensorLeftAdjunction K K').counit.app X) := by
    simp [mateEquiv_apply]
  show _ = δ F K X
  rw [e, ← cancel_mono (μ F K X), Functor.Monoidal.δ_μ]
  simpa only [Category.assoc, Functor.id_obj] using key

variable {G : D ⥤ C} (adj : F ⊣ G)

/-- **The projection formula map** `K ⊗ G E ⟶ G (F K ⊗ E)`, natural in `E`, as a 2-square
`G ⋙ tensorLeft K ⟶ tensorLeft (F K) ⋙ G`: the mate of `tensorLeftδ F K` for `adj` on both
sides. -/
def projection (K : C) : TwoSquare G (tensorLeft (F.obj K)) (tensorLeft K) G :=
  mateEquiv adj adj (tensorLeftδ F K)

/-- The component of the projection formula map: the unit at `K ⊗ G E`, followed by `G` of
`δ` and of `F K` tensored with the counit at `E`. -/
theorem projection_app (K : C) (E : D) :
    (projection F adj K).app E =
      adj.unit.app (K ⊗ G.obj E) ≫ G.map (δ F K (G.obj E)) ≫
        G.map (F.obj K ◁ adj.counit.app E) := by
  simp [projection]

/-- **The projection formula map is `CategoryTheory.adjunctionTensorMap`** for the tensor
products with their factors exchanged, `(X, K) ↦ K ⊗ X`, and a comparison whose component at
`(X, K)` is `δ F K X`. -/
theorem adjunctionTensorMap_eq_projection_app
    (α : (Prod.swap C C ⋙ Functor.uncurry.obj (curriedTensor C)) ⋙ F ⟶
      F.prod F ⋙ (Prod.swap D D ⋙ Functor.uncurry.obj (curriedTensor D)))
    (hα : ∀ X K : C, α.app (X, K) = δ F K X) (E : D) (K : C) :
    adjunctionTensorMap adj _ _ α E K = (projection F adj K).app E := by
  rw [adjunctionTensorMap_eq_unit_comp, projection_app, hα, Functor.map_comp]
  simp

/-- The projection formula map is the conjugate of `μ`, for the composite adjunctions
`(K' ⊗ -) ⋙ F ⊣ G ⋙ (K ⊗ -)` and `F ⋙ (F K' ⊗ -) ⊣ (F K ⊗ -) ⋙ G`. -/
theorem projection_natTrans_eq_conjugateEquiv (K K' : C) [ExactPairing K K'] :
    letI := ExactPairing.map F K K'
    (projection F adj K).natTrans =
      conjugateEquiv ((tensorLeftAdjunction K K').comp adj)
        (adj.comp (tensorLeftAdjunction (F.obj K) (F.obj K'))) (tensorLeftμ F K').natTrans := by
  let := ExactPairing.map F K K'
  rw [← iterated_mateEquiv_conjugateEquiv, mateEquiv_tensorLeftμ]
  rfl

/-- The mate of the projection formula map for `K'` is the conjugate of `δ`, for the composite
adjunctions `F ⋙ (F K' ⊗ -) ⊣ (F K ⊗ -) ⋙ G` and `(K' ⊗ -) ⋙ F ⊣ G ⋙ (K ⊗ -)`. -/
theorem mateEquiv_projection_natTrans_eq_conjugateEquiv (K K' : C) [ExactPairing K K'] :
    letI := ExactPairing.map F K K'
    (mateEquiv (tensorLeftAdjunction (F.obj K) (F.obj K')) (tensorLeftAdjunction K K')
        (projection F adj K')).natTrans =
      conjugateEquiv (adj.comp (tensorLeftAdjunction (F.obj K) (F.obj K')))
        ((tensorLeftAdjunction K K').comp adj) (tensorLeftδ F K').natTrans := by
  let := ExactPairing.map F K K'
  exact iterated_mateEquiv_conjugateEquiv adj adj (tensorLeftAdjunction K K')
    (tensorLeftAdjunction (F.obj K) (F.obj K')) (tensorLeftδ F K')

/-- `tensorLeftμ F K` followed by `tensorLeftδ F K` is the identity. -/
theorem tensorLeftμ_comp_tensorLeftδ (K : C) :
    (tensorLeftμ F K).natTrans ≫ (tensorLeftδ F K).natTrans = 𝟙 _ := by
  ext X
  simp

/-- `tensorLeftδ F K` followed by `tensorLeftμ F K` is the identity. -/
theorem tensorLeftδ_comp_tensorLeftμ (K : C) :
    (tensorLeftδ F K).natTrans ≫ (tensorLeftμ F K).natTrans = 𝟙 _ := by
  ext X
  simp

/-- **The mate of the projection formula map for `K'` inverts the projection formula map for
`K`**, on the side of `G (F K ⊗ -)`. -/
theorem mateEquiv_projection_comp_projection (K K' : C) [ExactPairing K K'] :
    letI := ExactPairing.map F K K'
    (mateEquiv (tensorLeftAdjunction (F.obj K) (F.obj K')) (tensorLeftAdjunction K K')
        (projection F adj K')).natTrans ≫ (projection F adj K).natTrans = 𝟙 _ := by
  let := ExactPairing.map F K K'
  rw [mateEquiv_projection_natTrans_eq_conjugateEquiv F adj K K',
    projection_natTrans_eq_conjugateEquiv F adj K K',
    conjugateEquiv_comp, tensorLeftμ_comp_tensorLeftδ, conjugateEquiv_id]

/-- **The mate of the projection formula map for `K'` inverts the projection formula map for
`K`**, on the side of `K ⊗ G -`. -/
theorem projection_comp_mateEquiv_projection (K K' : C) [ExactPairing K K'] :
    letI := ExactPairing.map F K K'
    (projection F adj K).natTrans ≫
      (mateEquiv (tensorLeftAdjunction (F.obj K) (F.obj K')) (tensorLeftAdjunction K K')
        (projection F adj K')).natTrans = 𝟙 _ := by
  let := ExactPairing.map F K K'
  rw [mateEquiv_projection_natTrans_eq_conjugateEquiv F adj K K',
    projection_natTrans_eq_conjugateEquiv F adj K K',
    conjugateEquiv_comp, tensorLeftδ_comp_tensorLeftμ, conjugateEquiv_id]

/-- The projection formula map of a dualizable object is invertible. -/
theorem isIso_projection (K : C) (K' : C) [ExactPairing K K'] :
    IsIso (projection F adj K).natTrans := by
  let := ExactPairing.map F K K'
  exact ⟨_, projection_comp_mateEquiv_projection F adj K K',
    mateEquiv_projection_comp_projection F adj K K'⟩

/-- **The mate of the projection formula map for `K'` is the inverse of the projection formula
map for `K`.** -/
theorem mateEquiv_projection_eq_inv (K K' : C) [ExactPairing K K'] :
    letI := ExactPairing.map F K K'
    haveI := isIso_projection F adj K K'
    (mateEquiv (tensorLeftAdjunction (F.obj K) (F.obj K')) (tensorLeftAdjunction K K')
        (projection F adj K')).natTrans = inv (projection F adj K).natTrans := by
  let := ExactPairing.map F K K'
  have := isIso_projection F adj K K'
  rw [← Category.id_comp (inv _), ← mateEquiv_projection_comp_projection F adj K K',
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end CategoryTheory.ProjectionFormula
