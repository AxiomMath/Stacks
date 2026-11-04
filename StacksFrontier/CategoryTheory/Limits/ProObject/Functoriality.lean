module

public import Mathlib.CategoryTheory.Limits.Indization.Category

/-!
# Functoriality of pro-objects presented as colimits of representables

A pro-object of a category `C` indexed by `J` is presented by the colimit of representables
`colim_j yoneda (A j)` in the presheaf category `Cᵒᵖ ⥤ Type v`. A functor `K : C ⥤ D` carries the
pro-object presented by `A` to the one presented by `A ⋙ K`: there is a bijection
```
  (colim_j yoneda (K (A j)) ⟶ T) ≃ (colim_j yoneda (A j) ⟶ K.op ⋙ T),
```
natural in the presheaf `T` on `D`, and consequently `K` carries an isomorphism of pro-objects to
an isomorphism of pro-objects. The index category `J` is arbitrary.

## Main definitions

* `Stacks.ProObject.presheafRestriction`: restriction of presheaves along `K.op`.
* `Stacks.ProObject.comparison`: the canonical morphism
  `colim_j yoneda (A j) ⟶ K.op ⋙ colim_j yoneda (K (A j))`.
* `Stacks.ProObject.homEquiv`: the bijection displayed above.

## Main results

* `Stacks.ProObject.transportIso`: an isomorphism of the colimits of representables on diagrams
  `A` and `B` in `C` gives an isomorphism of those on `A ⋙ K` and `B ⋙ K` in `D`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v uC uD

namespace Stacks.ProObject

variable {C : Type uC} [Category.{v} C] {D : Type uD} [Category.{v} D]

/-- Restriction of presheaves along `K.op`. -/
public abbrev presheafRestriction (K : C ⥤ D) : (Dᵒᵖ ⥤ Type v) ⥤ (Cᵒᵖ ⥤ Type v) :=
  (Functor.whiskeringLeft _ _ _).obj K.op

/-- The natural transformation `yoneda ⟶ K ⋙ yoneda ⋙ K.op ⋙ -` whose component at `X` sends a
morphism `Y ⟶ X` to its image `K Y ⟶ K X`. -/
public def yonedaCompRestriction (K : C ⥤ D) :
    (yoneda : C ⥤ _) ⟶ K ⋙ yoneda ⋙ presheafRestriction K where
  app X := yonedaMap K X
  naturality := by intros; ext Y f; simp

/-- The component of `Stacks.ProObject.yonedaCompRestriction K` at `X` is `yonedaMap K X`. -/
@[simp]
public theorem yonedaCompRestriction_app (K : C ⥤ D) (X : C) :
    (yonedaCompRestriction K).app X = yonedaMap K X :=
  rfl

variable {J : Type w} [Category.{w'} J] (K : C ⥤ D) (A : J ⥤ C)
  [HasColimit (A ⋙ yoneda)] [HasColimit (A ⋙ K ⋙ yoneda)]

/-- The cocone on `A ⋙ yoneda` with vertex the restriction along `K.op` of the colimit of
`A ⋙ K ⋙ yoneda`, whose leg at `j` is the image under `K` of a morphism into `A j`. -/
public def comparisonCocone : Cocone (A ⋙ yoneda) where
  pt := (presheafRestriction K).obj (colimit (A ⋙ K ⋙ yoneda))
  ι :=
    { app := fun j =>
        yonedaMap K (A.obj j) ≫ (presheafRestriction K).map (colimit.ι (A ⋙ K ⋙ yoneda) j)
      naturality := by
        intro j j' u
        have h := (yonedaCompRestriction K).naturality (A.map u)
        simp only [yonedaCompRestriction_app, Functor.comp_obj, Functor.const_obj_obj,
          Functor.comp_map, Functor.const_obj_map, Category.comp_id] at *
        rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp,
          show (yoneda.map (K.map (A.map u)) ≫ colimit.ι (A ⋙ K ⋙ yoneda) j') =
            colimit.ι (A ⋙ K ⋙ yoneda) j from colimit.w (A ⋙ K ⋙ yoneda) u] }

/-- The canonical morphism `colim_j yoneda (A j) ⟶ K.op ⋙ colim_j yoneda (K (A j))`, the image of
the identity under the hom bijection `Stacks.ProObject.homEquiv`. -/
public def comparison :
    colimit (A ⋙ yoneda) ⟶ (presheafRestriction K).obj (colimit (A ⋙ K ⋙ yoneda)) :=
  colimit.desc (A ⋙ yoneda) (comparisonCocone K A)

/-- The comparison morphism restricted to the stage `j` is the image under `K` of a morphism into
`A j`, followed by the restricted colimit coprojection at `j`. -/
@[simp]
public theorem ι_comparison (j : J) :
    colimit.ι (A ⋙ yoneda) j ≫ comparison K A =
      yonedaMap K (A.obj j) ≫ (presheafRestriction K).map (colimit.ι (A ⋙ K ⋙ yoneda) j) :=
  colimit.ι_desc _ _

/-- The comparison morphism does not change the element of `T (K (A j))` that a morphism out of
the colimit determines at the stage `j`. -/
public theorem yonedaEquiv_ι_comparison_comp {T : Dᵒᵖ ⥤ Type v} (j : J)
    (h : colimit (A ⋙ K ⋙ yoneda) ⟶ T) :
    yonedaEquiv (colimit.ι (A ⋙ yoneda) j ≫ comparison K A ≫ (presheafRestriction K).map h) =
      yonedaEquiv (colimit.ι (A ⋙ K ⋙ yoneda) j ≫ h) := by
  rw [← Category.assoc, ι_comparison, Category.assoc, ← Functor.map_comp]
  simp only [yonedaEquiv_apply, Functor.comp_obj, NatTrans.comp_app_apply,
    Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app]
  congr 2
  exact K.map_id _

/-- The stage `j` of the cocone transposing a morphism out of `colim_j yoneda (A j)` into a
presheaf restricted along `K.op`: the same element of `T (K (A j))`, read through
`CategoryTheory.yonedaEquiv` on the other side. -/
public def transposeStage {T : Dᵒᵖ ⥤ Type v}
    (w : colimit (A ⋙ yoneda) ⟶ (presheafRestriction K).obj T) (j : J) :
    (A ⋙ K ⋙ yoneda).obj j ⟶ T :=
  yonedaEquiv.symm
    (yonedaEquiv (X := A.obj j) (F := (presheafRestriction K).obj T)
      (colimit.ι (A ⋙ yoneda) j ≫ w))

omit [HasColimit (A ⋙ K ⋙ yoneda)] in
/-- The element of `T (K (A j))` determined by the stage `j` of the transposed cocone is the one
determined by the original morphism at the stage `j`. -/
public theorem yonedaEquiv_transposeStage {T : Dᵒᵖ ⥤ Type v}
    (w : colimit (A ⋙ yoneda) ⟶ (presheafRestriction K).obj T) (j : J) :
    yonedaEquiv (X := K.obj (A.obj j)) (F := T) (transposeStage K A w j) =
      yonedaEquiv (X := A.obj j) (F := (presheafRestriction K).obj T)
        (colimit.ι (A ⋙ yoneda) j ≫ w) :=
  Equiv.apply_symm_apply _ _

omit [HasColimit (A ⋙ K ⋙ yoneda)] in
/-- A stage of the transposed cocone is characterized by the element it determines. -/
public theorem transposeStage_eq {T : Dᵒᵖ ⥤ Type v}
    (w : colimit (A ⋙ yoneda) ⟶ (presheafRestriction K).obj T) (j : J)
    (y : (A ⋙ K ⋙ yoneda).obj j ⟶ T)
    (hy : yonedaEquiv (X := A.obj j) (F := (presheafRestriction K).obj T)
        (colimit.ι (A ⋙ yoneda) j ≫ w) = yonedaEquiv (X := K.obj (A.obj j)) (F := T) y) :
    transposeStage K A w j = y :=
  yonedaEquiv.injective ((yonedaEquiv_transposeStage K A w j).trans hy)

/-- The cocone on `A ⋙ K ⋙ yoneda` built from a morphism out of `colim_j yoneda (A j)` into a
presheaf restricted along `K.op`, stage by stage through `CategoryTheory.yonedaEquiv`. -/
public def transposeCocone {T : Dᵒᵖ ⥤ Type v}
    (w : colimit (A ⋙ yoneda) ⟶ (presheafRestriction K).obj T) :
    Cocone (A ⋙ K ⋙ yoneda) where
  pt := T
  ι :=
    { app := transposeStage K A w
      naturality := by
        intro j j' u
        apply yonedaEquiv.injective
        simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map,
          Functor.const_obj_map, Category.comp_id]
        rw [← yonedaEquiv_naturality, yonedaEquiv_transposeStage, yonedaEquiv_transposeStage]
        change ((presheafRestriction K).obj T).map (A.map u).op
            (yonedaEquiv (colimit.ι (A ⋙ yoneda) j' ≫ w)) = _
        rw [yonedaEquiv_naturality, ← Category.assoc,
          show (yoneda.map (A.map u) ≫ colimit.ι (A ⋙ yoneda) j') =
            colimit.ι (A ⋙ yoneda) j from colimit.w (A ⋙ yoneda) u] }

/-- The morphism out of `colim_j yoneda (K (A j))` transposing a morphism out of
`colim_j yoneda (A j)` into a presheaf restricted along `K.op`. -/
public def transpose {T : Dᵒᵖ ⥤ Type v}
    (w : colimit (A ⋙ yoneda) ⟶ (presheafRestriction K).obj T) :
    colimit (A ⋙ K ⋙ yoneda) ⟶ T :=
  colimit.desc (A ⋙ K ⋙ yoneda) (transposeCocone K A w)

/-- The transpose restricted to the stage `j` is `Stacks.ProObject.transposeStage`. -/
@[simp]
public theorem ι_transpose {T : Dᵒᵖ ⥤ Type v}
    (w : colimit (A ⋙ yoneda) ⟶ (presheafRestriction K).obj T) (j : J) :
    colimit.ι (A ⋙ K ⋙ yoneda) j ≫ transpose K A w = transposeStage K A w j :=
  colimit.ι_desc _ _

/-- A morphism from the pro-object presented by `A ⋙ K` to a presheaf `T`
is the same thing as a morphism from the pro-object presented by `A` to the restriction of `T`
along `K.op`. Both are a compatible family of elements of `T (K (A j))`, and the bijection is the
identity on that data. -/
public def homEquiv (T : Dᵒᵖ ⥤ Type v) :
    (colimit (A ⋙ K ⋙ yoneda) ⟶ T) ≃
      (colimit (A ⋙ yoneda) ⟶ (presheafRestriction K).obj T) where
  toFun h := comparison K A ≫ (presheafRestriction K).map h
  invFun w := transpose K A w
  left_inv h := by
    change transpose K A (comparison K A ≫ (presheafRestriction K).map h) = h
    refine colimit.hom_ext fun j => ?_
    exact (ι_transpose K A _ j).trans
      (transposeStage_eq K A _ j _ (yonedaEquiv_ι_comparison_comp K A j h))
  right_inv w := by
    change comparison K A ≫ (presheafRestriction K).map (transpose K A w) = w
    refine colimit.hom_ext fun j => ?_
    apply yonedaEquiv.injective
    rw [yonedaEquiv_ι_comparison_comp, ι_transpose, yonedaEquiv_transposeStage]

/-- The hom bijection sends `h` to the comparison morphism followed by the restriction of `h`. -/
@[simp]
public theorem homEquiv_apply (T : Dᵒᵖ ⥤ Type v) (h : colimit (A ⋙ K ⋙ yoneda) ⟶ T) :
    homEquiv K A T h = comparison K A ≫ (presheafRestriction K).map h :=
  rfl

/-- The hom bijection turns postcomposition into restriction. -/
public theorem homEquiv_comp {T T' : Dᵒᵖ ⥤ Type v} (h : colimit (A ⋙ K ⋙ yoneda) ⟶ T)
    (s : T ⟶ T') :
    homEquiv K A T' (h ≫ s) = homEquiv K A T h ≫ (presheafRestriction K).map s := by
  rw [homEquiv_apply, homEquiv_apply, Functor.map_comp, Category.assoc]

/-- The hom bijection sends the identity to the comparison morphism. -/
public theorem homEquiv_id :
    homEquiv K A (colimit (A ⋙ K ⋙ yoneda)) (𝟙 _) = comparison K A := by
  rw [homEquiv_apply, (presheafRestriction K).map_id, Category.comp_id]

variable (B : J ⥤ C) [HasColimit (B ⋙ yoneda)] [HasColimit (B ⋙ K ⋙ yoneda)]

/-- A functor carries an isomorphism of pro-objects to an isomorphism of pro-objects: if the
colimits of representables on the diagrams `A` and `B` in `C` are isomorphic, then so are those on
`A ⋙ K` and `B ⋙ K` in `D`. -/
public def transportIso (h : colimit (A ⋙ yoneda) ≅ colimit (B ⋙ yoneda)) :
    colimit (A ⋙ K ⋙ yoneda) ≅ colimit (B ⋙ K ⋙ yoneda) where
  hom := (homEquiv K A (colimit (B ⋙ K ⋙ yoneda))).symm (h.hom ≫ comparison K B)
  inv := (homEquiv K B (colimit (A ⋙ K ⋙ yoneda))).symm (h.inv ≫ comparison K A)
  hom_inv_id := by
    apply (homEquiv K A (colimit (A ⋙ K ⋙ yoneda))).injective
    rw [homEquiv_comp, Equiv.apply_symm_apply, homEquiv_id, Category.assoc,
      ← homEquiv_apply K B _ _, Equiv.apply_symm_apply, Iso.hom_inv_id_assoc]
  inv_hom_id := by
    apply (homEquiv K B (colimit (B ⋙ K ⋙ yoneda))).injective
    rw [homEquiv_comp, Equiv.apply_symm_apply, homEquiv_id, Category.assoc,
      ← homEquiv_apply K A _ _, Equiv.apply_symm_apply, Iso.inv_hom_id_assoc]

end Stacks.ProObject

end
