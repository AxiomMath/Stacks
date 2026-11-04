module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import StacksFrontier.Homology.TensorComplex.ExactFunctor

/-!
# Tensoring with a complex concentrated in degree zero

For an object `N` of a monoidal category and a cochain complex `D`, the total tensor complex
`N[0] ⊗ D` has a single nonzero summand in each degree, so it is the complex obtained by applying
`N ⊗ -` degreewise. This file records that identification and its naturality in `D`.

## Main definitions

* `TotalTensorComplex.SingleTensor.singleTensorTermIso`: in degree `i`, the total tensor complex
  `N[0] ⊗ D` is `N ⊗ D^i`.
* `TotalTensorComplex.SingleTensor.singleTensorIso`: the resulting isomorphism of complexes
  `N[0] ⊗ D ≅ (N ⊗ -)(D)`.

## Main results

* `TotalTensorComplex.SingleTensor.singleTensorIso_naturality`: `singleTensorIso` is natural in
  `D`.

## Implementation notes

`N[0] ⊗ D` is the total complex of the tensor-product double complex, so its degree-`i` term is a
biproduct over the pairs `(a, b)` with `a + b = i`, of which only `(0, i)` contributes. The
isomorphism is therefore the summand inclusion, with the projection onto that summand as its
inverse; the two composites are computed from `mapBifunctorDesc` and the vanishing of the other
summands.

Everything is stated for an arbitrary preadditive monoidal category with additive tensor product,
which is the generality the argument has. Complexes of modules are the case of interest, at any
module universe: the instances hold for `ModuleCat.{max u v} R` with the lifted monoidal structure
as well as for `ModuleCat.{u} R` with Mathlib's.

## References

* [The Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
* [The Stacks Project, Tag 068F](https://stacks.math.columbia.edu/tag/068F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

namespace TotalTensorComplex.SingleTensor

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [∀ (K₁ K₂ : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor C) (ComplexShape.up ℤ)]

set_option backward.isDefEq.respectTransparency false

/-- In degree `i`, the total tensor complex `N[0] ⊗ D` is the single summand `N ⊗ D^i`. -/
public noncomputable def singleTensorTermIso (N : C) (D : CochainComplex C ℤ) (i : ℤ) :
    ((TleftCochain ((single C (ComplexShape.up ℤ) 0).obj N)).obj D).X i ≅ N ⊗ D.X i := by
  let K : CochainComplex C ℤ := (single C (ComplexShape.up ℤ) 0).obj N
  let F := curriedTensor C
  let j := ιMapBifunctor K D F (ComplexShape.up ℤ) 0 i i (by simp)
  let p : (mapBifunctor K D F (ComplexShape.up ℤ)).X i ⟶ K.X 0 ⊗ D.X i :=
    mapBifunctorDesc fun a b hab =>
      if h : a = 0 then by
        subst a
        have hb : b = i := by simpa using hab
        subst b
        exact 𝟙 _
      else 0
  have hpj : p ≫ j = 𝟙 _ := by
    refine mapBifunctor.hom_ext fun a b hab => ?_
    rcases eq_or_ne a 0 with rfl | ha
    · obtain rfl : b = i := by simpa using hab
      simp [j, p]
    · exact (tensorRight (D.X b)).map_isZero
        (isZero_single_obj_X (ComplexShape.up ℤ) 0 N a ha) |>.eq_of_src _ _
  exact (⟨j, p, by simp [j, p], hpj⟩ : _ ≅ _).symm ≪≫
    tensorIso (singleObjXSelf (ComplexShape.up ℤ) 0 N) (Iso.refl _)

omit [MonoidalPreadditive C] [HasBinaryBiproducts C] in
/-- The inverse of `singleTensorTermIso` is the inclusion of the `(0, i)` summand. -/
public lemma singleTensorTermIso_inv (N : C) (D : CochainComplex C ℤ) (i : ℤ) :
    (singleTensorTermIso N D i).inv =
      ιMapBifunctor ((single C (ComplexShape.up ℤ) 0).obj N) D
        (curriedTensor C) (ComplexShape.up ℤ) 0 i i (by simp) := by
  simp only [singleTensorTermIso, Iso.trans_inv, Iso.symm_inv, tensorIso_inv,
    Iso.refl_inv, tensorHom_id]
  show (𝟙 N ▷ D.X i) ≫ _ = _
  simp

/-- Tensoring on the left with `N[0]` is tensoring degreewise with `N`. -/
public noncomputable def singleTensorIso (N : C) (D : CochainComplex C ℤ) :
    (TleftCochain ((single C (ComplexShape.up ℤ) 0).obj N)).obj D ≅
      ((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj D := by
  refine HomologicalComplex.Hom.isoOfComponents (singleTensorTermIso N D) fun i j hij => ?_
  change i + 1 = j at hij
  apply (cancel_epi (singleTensorTermIso N D i).inv).1
  simp only [Iso.inv_hom_id_assoc]
  rw [singleTensorTermIso_inv, ← Category.assoc]
  let K : CochainComplex C ℤ := (single C (ComplexShape.up ℤ) 0).obj N
  let F := curriedTensor C
  change (tensorLeft N).map (D.d i j) =
    (ιMapBifunctor K D F (ComplexShape.up ℤ) 0 i i _ ≫
      (mapBifunctor K D F (ComplexShape.up ℤ)).d i j) ≫ _
  rw [mapBifunctor.d_eq, Preadditive.comp_add,
    mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl) i j
      (by change 1 + i = j; omega),
    mapBifunctor.d₂_eq _ _ _ _ 0 hij j (by simp)]
  simp only [K, single_obj_d, Functor.map_zero, Limits.zero_app,
    Limits.zero_comp, smul_zero, zero_add]
  rw [show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (0, i) = 1 from rfl,
    one_smul, Category.assoc, ← singleTensorTermIso_inv,
    Iso.inv_hom_id, Category.comp_id]
  rfl

omit [MonoidalPreadditive C] [HasBinaryBiproducts C] in
/-- `singleTensorIso` is natural in the varying complex. -/
public lemma singleTensorIso_naturality (N : C)
    {D D' : CochainComplex C ℤ} (f : D ⟶ D') :
    (singleTensorIso N D).inv ≫
        (TleftCochain ((single C (ComplexShape.up ℤ) 0).obj N)).map f =
      ((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).map f ≫
        (singleTensorIso N D').inv := by
  ext i : 1
  show (singleTensorTermIso N D i).inv ≫
    (mapBifunctorMap (𝟙 _) f (curriedTensor C) (ComplexShape.up ℤ)).f i =
      (tensorLeft N).map (f.f i) ≫ (singleTensorTermIso N D' i).inv
  rw [singleTensorTermIso_inv, singleTensorTermIso_inv, ι_mapBifunctorMap]
  simp
  rfl

end TotalTensorComplex.SingleTensor

end
