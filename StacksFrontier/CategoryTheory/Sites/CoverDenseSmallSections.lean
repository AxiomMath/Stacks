module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Sections of a sheaf are small if they are small on a cover-dense subcategory

Let `G : C ⥤ D` be cover-dense for a topology `K` on `D`, with `C` essentially small and `D`
locally small in a universe `w`. A sheaf of types on `(D, K)` whose sections over the objects
`G X` are `w`-small has `w`-small sections everywhere: a section over `U` is determined by its
restrictions along the morphisms `G X ⟶ U`, and up to isomorphism those form a `w`-small family.

## Main results

* `CategoryTheory.Functor.IsCoverDense.small_obj_of_small_obj_map`: sections are small if they
  are small on the image of a cover-dense functor.
-/

@[expose] public section

open CategoryTheory Opposite

universe w w' v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.IsCoverDense

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {K : GrothendieckTopology D} (G : C ⥤ D) [G.IsCoverDense K]
  [EssentiallySmall.{w} C] [LocallySmall.{w} D]

/-- **Sections of a sheaf are small when they are small on a cover-dense subcategory.** -/
theorem small_obj_of_small_obj_map (P : Sheaf K (Type w'))
    (h : ∀ X : C, Small.{w} (P.obj.obj (op (G.obj X)))) (U : D) :
    Small.{w} (P.obj.obj (op U)) := by
  let ι : SmallModel.{w} C → C := fun Y => (equivSmallModel.{w} C).inverse.obj Y
  let Φ : P.obj.obj (op U) → ∀ i : Σ Y : SmallModel.{w} C, (G.obj (ι Y) ⟶ U),
      P.obj.obj (op (G.obj (ι i.1))) := fun s i => P.obj.map i.2.op s
  refine small_of_injective (f := Φ) fun s t hst => ?_
  refine Functor.IsCoverDense.ext G P U fun Y f => ?_
  let e : Y ≅ ι ((equivSmallModel.{w} C).functor.obj Y) := (equivSmallModel.{w} C).unitIso.app Y
  have hf : f = G.map e.hom ≫ (G.map e.inv ≫ f) := by
    rw [← Category.assoc, ← G.map_comp, e.hom_inv_id, G.map_id, Category.id_comp]
  have h1 := congrFun hst ⟨(equivSmallModel.{w} C).functor.obj Y, G.map e.inv ≫ f⟩
  change P.obj.map (G.map e.inv ≫ f).op s = P.obj.map (G.map e.inv ≫ f).op t at h1
  rw [hf, op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply, h1]

end CategoryTheory.Functor.IsCoverDense
