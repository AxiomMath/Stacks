module

public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsModelIsoRestrictedEvaluation

/-!
# The chain-level projection formula is the lax tensor of restriction after the unit

Let `φ : A →+* B`, let `P` be a complex of `A`-modules and `L` a complex of `B`-modules.
`CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso` is the chain-level projection
formula of [stacks 06Y6], identifying `(L ⊗_B (B ⊗_A P))|_A` with `L|_A ⊗_A P`, and
`CochainComplex.ExtendScalars.restrictScalarsLaxTensor` is the lax monoidal structure map
`ρ : X|_A ⊗_A Y|_A ⟶ (X ⊗_B Y)|_A` of restriction of scalars. This file proves

`(baseChange_tensor_iso φ P L).inv = (𝟙_{L|_A} ⊗ₘ η_P) ≫ ρ_{L, B ⊗_A P}`,

with `η` the unit of degreewise extension--restriction of scalars on cochain complexes.

## Main results

* `CochainComplex.ExtendScalars.projectionFormulaIso_inv_eq_homEquiv` and
  `CochainComplex.ExtendScalars.projectionFormulaIso_inv_eq_unit_comp`: the inverse of the
  projection formula at a pair of modules is the transpose of the oplax structure map of
  extension of scalars followed by the counit.
* `CochainComplex.ExtendScalars.tensorHom_unit_comp_restrictScalarsLaxTensor`:
  `(𝟙 ⊗ₘ η_P) ≫ ρ` as a transpose.
* `CochainComplex.ExtendScalars.baseChange_tensor_iso_inv_eq_homEquiv`: the inverse of the
  chain-level projection formula as the same transpose.
* `CochainComplex.ExtendScalars.baseChange_tensor_iso_inv_eq`: the identity above.

## Universes

`CochainComplex.ExtendScalars.restrictScalarsLaxTensor` is stated at the equal-universe
`ModuleCat.{u}` with both rings in `Type u`, so this file is too: the lifted monoidal structure
`ModuleCat.liftedModuleMonoidal` that `baseChange_tensor_iso` is stated with and Mathlib's
monoidal structure that `restrictScalarsLaxTensor` is stated with unify there with no bridging
isomorphism, and at unequal universes they do not.

## References

* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars

universe u

namespace CochainComplex.ExtendScalars

variable {A B : Type u} [CommRing A] [CommRing B]

open Functor.OplaxMonoidal in
/-- The inverse of the projection formula
`CochainComplex.KFlat.ScalarBaseChange.projectionFormulaIso φ V W`, for a `B`-module `V` and an
`A`-module `W`, is the transpose along extension and restriction of scalars of the oplax structure
map `δ` of extension of scalars followed by the counit at `V` tensored with the identity. -/
theorem projectionFormulaIso_inv_eq_homEquiv (φ : A →+* B) (V : ModuleCat.{u} B)
    (W : ModuleCat.{u} A) :
    (CochainComplex.KFlat.ScalarBaseChange.projectionFormulaIso.{u, u, u} φ V W).inv =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).homEquiv _ _
          (δ (ModuleCat.extendScalars.{u, u, u} φ)
              ((ModuleCat.restrictScalars.{u} φ).obj V) W ≫
            ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).counit.app V ⊗ₘ
              𝟙 ((ModuleCat.extendScalars.{u, u, u} φ).obj W))) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro v w
  let : Algebra A B := φ.toAlgebra
  exact congrArg (fun (x : V) => x ⊗ₜ[B] ((1 : B) ⊗ₜ[A] w))
    (ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul φ V v).symm

open Functor.OplaxMonoidal in
/-- The inverse of the projection formula
`CochainComplex.KFlat.ScalarBaseChange.projectionFormulaIso φ V W` is the unit of extension and
restriction of scalars followed by the restriction of the composite of the oplax structure map `δ`
of extension of scalars with the counit at `V` tensored with the identity. -/
theorem projectionFormulaIso_inv_eq_unit_comp (φ : A →+* B) (V : ModuleCat.{u} B)
    (W : ModuleCat.{u} A) :
    (CochainComplex.KFlat.ScalarBaseChange.projectionFormulaIso.{u, u, u} φ V W).inv =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.app
          ((ModuleCat.restrictScalars.{u} φ).obj V ⊗ W) ≫
        (ModuleCat.restrictScalars.{u} φ).map
          (δ (ModuleCat.extendScalars.{u, u, u} φ)
              ((ModuleCat.restrictScalars.{u} φ).obj V) W ≫
            ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).counit.app V ⊗ₘ
              𝟙 ((ModuleCat.extendScalars.{u, u, u} φ).obj W))) :=
  (projectionFormulaIso_inv_eq_homEquiv φ V W).trans
    (Adjunction.homEquiv_unit (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ) _ _ _)

/-- On the summand of bidegree `(i, j)` of a tensor product of cochain complexes, `f ⊗ₘ g` is
`f.f i ⊗ₘ g.f j`. -/
private theorem ι_tensorObj_tensorHom_f {T : Type u} [CommRing T]
    {K₁ K₂ M₁ M₂ : CochainComplex (ModuleCat.{u} T) ℤ} (f : K₁ ⟶ M₁) (g : K₂ ⟶ M₂)
    (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj K₁ K₂ i j n h ≫ (f ⊗ₘ g).f n =
      (f.f i ⊗ₘ g.f j) ≫ HomologicalComplex.ιTensorObj M₁ M₂ i j n h := by
  show HomologicalComplex.ιMapBifunctor K₁ K₂ (curriedTensor (ModuleCat.{u} T))
      (ComplexShape.up ℤ) i j n h ≫
    (HomologicalComplex.mapBifunctorMap f g (curriedTensor (ModuleCat.{u} T))
      (ComplexShape.up ℤ)).f n = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp [tensorHom_def]

/-- `(u ≫ G.map d) ≫ G.map c = i ≫ v ≫ G.map w` whenever `i ≫ v = u ≫ G.map e` and
`e ≫ w = d ≫ c`. -/
private theorem comp_glue_unit {C D : Type*} [Category* C] [Category* D] (G : D ⥤ C)
    {S T : C} {X Y Z M : D}
    (i : S ⟶ T) (v : T ⟶ G.obj X) (u : S ⟶ G.obj Y) (e : Y ⟶ X) (w : X ⟶ Z)
    (d : Y ⟶ M) (c : M ⟶ Z)
    (hnat : i ≫ v = u ≫ G.map e) (hd : e ≫ w = d ≫ c) :
    (u ≫ G.map d) ≫ G.map c = i ≫ v ≫ G.map w := by
  simp only [← Category.assoc, hnat]
  simp only [Category.assoc, ← Functor.map_comp, hd]

/-- `e ≫ m ≫ k = (d ≫ t) ≫ c` whenever `e ≫ m = d ≫ j` and `j ≫ k = t ≫ c`. -/
private theorem comp_glue_two {D : Type*} [Category* D] {X Y Z V W U : D}
    (e : Y ⟶ X) (m : X ⟶ Z) (k : Z ⟶ V) (d : Y ⟶ W) (j : W ⟶ Z) (t : W ⟶ U) (c : U ⟶ V)
    (h1 : e ≫ m = d ≫ j) (h2 : j ≫ k = t ≫ c) :
    e ≫ m ≫ k = (d ≫ t) ≫ c := by
  simp only [← Category.assoc, h1]
  simp only [Category.assoc, h2]

/-- `e ≫ α.inv = d ≫ j` whenever `j ≫ α.hom = mu ≫ e` and `d ≫ mu = 𝟙 Y`. -/
private theorem comp_inv_eq_of_section {D : Type*} [Category* D] {X Y Z W : D} (e : Y ⟶ X)
    (α : Z ≅ X) (d : Y ⟶ W) (j : W ⟶ Z) (mu : W ⟶ Y)
    (h0 : j ≫ α.hom = mu ≫ e) (hdm : d ≫ mu = 𝟙 Y) :
    e ≫ α.inv = d ≫ j := by
  rw [Iso.comp_inv_eq]
  simp only [Category.assoc, h0]
  simp only [← Category.assoc, hdm, Category.id_comp]

section
variable (φ : A →+* B) (P : CochainComplex (ModuleCat.{u} A) ℤ)
  (L : CochainComplex (ModuleCat.{u} B) ℤ)

/-- The unit at `P` tensored with the identity of `L|_A`, followed by
`CochainComplex.ExtendScalars.restrictScalarsLaxTensor`, is the transpose of the inverse of the
monoidality isomorphism of extension of scalars followed by the counit at `L` tensored with the
identity. -/
theorem tensorHom_unit_comp_restrictScalarsLaxTensor :
    (𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L) ⊗ₘ
        (extendRestrictScalarsComplexAdj φ).unit.app P) ≫
      restrictScalarsLaxTensor φ L ((mapCochainComplex φ).obj P) =
    (extendRestrictScalarsComplexAdj φ).homEquiv _ _
      ((extendScalarsMonoidalIso φ
            ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L) P).inv ≫
        ((extendRestrictScalarsComplexAdj φ).counit.app L ⊗ₘ
          𝟙 ((mapCochainComplex φ).obj P))) := by
  have h := Adjunction.homEquiv_tensorHom_unit (extendRestrictScalarsComplexAdj φ)
    (extendScalarsMonoidalIso φ
      ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L) P).inv
    (extendScalarsMonoidalIso φ
      ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L)
      ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj
        ((mapCochainComplex φ).obj P))).inv
    (extendScalarsMonoidalIso_inv_naturality_right φ
      ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L)
      ((extendRestrictScalarsComplexAdj φ).unit.app P))
    ((extendRestrictScalarsComplexAdj φ).counit.app L)
    (𝟙 (L ⊗ (mapCochainComplex φ).obj P))
  have e1 : ((extendRestrictScalarsComplexAdj φ).counit.app L ⊗ₘ
        (extendRestrictScalarsComplexAdj φ).counit.app ((mapCochainComplex φ).obj P)) ≫
      𝟙 (L ⊗ (mapCochainComplex φ).obj P) =
      ((extendRestrictScalarsComplexAdj φ).counit.app L ⊗ₘ
        (extendRestrictScalarsComplexAdj φ).counit.app ((mapCochainComplex φ).obj P)) :=
    Category.comp_id _
  rw [e1] at h
  rwa [restrictScalarsLaxTensor]

/-- On the summand of bidegree `(q, pp)`, the inverse of the projection formula for `L.X q` and
`P.X pp` followed by the restricted inclusion of that summand is the inclusion of the summand
followed by the degree-`n` component of the unit and of the restriction of the inverse monoidality
isomorphism of extension of scalars followed by the counit at `L` tensored with the identity. -/
private theorem baseChange_tensor_isoX_inv_comp_ι (n q pp : ℤ) (hqp : q + pp = n) :
    (CochainComplex.KFlat.ScalarBaseChange.projectionFormulaIso.{u, u, u}
          φ (L.X q) (P.X pp)).inv ≫
        (ModuleCat.restrictScalars.{u} φ).map
          (HomologicalComplex.ιTensorObj L ((mapCochainComplex φ).obj P) q pp n hqp) =
      HomologicalComplex.ιTensorObj
          ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L) P q pp n hqp ≫
        ((extendRestrictScalarsComplexAdj φ).unit.app
            ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L ⊗ P) ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} φ).map
            ((extendScalarsMonoidalIso φ
                ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L) P).inv ≫
              ((extendRestrictScalarsComplexAdj φ).counit.app L ⊗ₘ
                𝟙 ((mapCochainComplex φ).obj P)))).f n := by
  have hu : ((extendRestrictScalarsComplexAdj φ).unit.app
        ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L ⊗ P)).f n =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.app
        ((((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L) ⊗ P).X n) := rfl
  have hm : ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).map
        ((extendScalarsMonoidalIso φ
            ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L) P).inv ≫
          ((extendRestrictScalarsComplexAdj φ).counit.app L ⊗ₘ
            𝟙 ((mapCochainComplex φ).obj P)))).f n =
      (ModuleCat.restrictScalars.{u} φ).map
        (((extendScalarsMonoidalIso φ
            ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L) P).inv ≫
          ((extendRestrictScalarsComplexAdj φ).counit.app L ⊗ₘ
            𝟙 ((mapCochainComplex φ).obj P))).f n) := rfl
  rw [HomologicalComplex.comp_f, hu, hm, HomologicalComplex.comp_f,
    projectionFormulaIso_inv_eq_unit_comp]
  refine comp_glue_unit (ModuleCat.restrictScalars.{u} φ) _ _ _ _ _ _ _
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit_naturality _).symm ?_
  refine comp_glue_two _ _ _ _ _ _ _ ?_
    (ι_tensorObj_tensorHom_f ((extendRestrictScalarsComplexAdj φ).counit.app L)
      (𝟙 ((mapCochainComplex φ).obj P)) q pp n hqp)
  exact comp_inv_eq_of_section _
    ((HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.up ℤ) n).mapIso
      (extendScalarsMonoidalIso φ ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L) P))
    _ _ _ (ι_extendScalarsMonoidalIso_hom φ
      ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L) P n q pp hqp)
    (Functor.Monoidal.δ_μ (ModuleCat.extendScalars.{u, u, u} φ) _ _)

/-- The inverse of the chain-level projection formula is the transpose of the inverse of the
monoidality isomorphism of extension of scalars followed by the counit at `L` tensored with the
identity. -/
theorem baseChange_tensor_iso_inv_eq_homEquiv :
    (CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso.{u, u, u} φ P L).inv =
    (extendRestrictScalarsComplexAdj φ).homEquiv _ _
      ((extendScalarsMonoidalIso φ
            ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L) P).inv ≫
        ((extendRestrictScalarsComplexAdj φ).counit.app L ⊗ₘ
          𝟙 ((mapCochainComplex φ).obj P))) := by
  rw [Adjunction.homEquiv_unit]
  ext n : 1
  apply GradedObject.Monoidal.tensorObj_ext
  intro q pp hqp
  have hinv : (CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso.{u, u, u}
        φ P L).inv.f n =
      (CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_isoX.{u, u, u} φ P L n).inv := rfl
  rw [hinv]
  exact (CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_isoX_inv_ι
    φ P L n q pp hqp).trans (baseChange_tensor_isoX_inv_comp_ι φ P L n q pp hqp)

/-- **The chain-level projection formula, inverted, is the restricted lax tensor after the
unit.** -/
theorem baseChange_tensor_iso_inv_eq :
    (CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso.{u, u, u} φ P L).inv =
      (𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L) ⊗ₘ
          (extendRestrictScalarsComplexAdj φ).unit.app P) ≫
        restrictScalarsLaxTensor φ L ((mapCochainComplex φ).obj P) :=
  (baseChange_tensor_iso_inv_eq_homEquiv φ P L).trans
    (tensorHom_unit_comp_restrictScalarsLaxTensor φ P L).symm

end

end CochainComplex.ExtendScalars

end
