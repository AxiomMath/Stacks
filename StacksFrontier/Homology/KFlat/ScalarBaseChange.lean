module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section


/-!
# K-flatness and scalar base change

Let `φ : R → R'` be a homomorphism of commutative rings, `K` a complex of `R`-modules and `L` a
complex of `R'`-modules, all modules living in one universe above both ring universes. The
projection formula `V ⊗_{R'} (R' ⊗_R W) ≅ V ⊗_R W` holds for an `R'`-module `V` and an
`R`-module `W`, and it is compatible with the Koszul differentials of the total complexes. So the
underlying complex of `R`-modules of `L ⊗_{R'} (R' ⊗_R K)` is `L ⊗_R K`.

Since restriction of scalars neither creates nor destroys acyclicity, that identification says
that extension of scalars carries K-flat complexes of `R`-modules to K-flat complexes of
`R'`-modules.

## Main definitions

* `CochainComplex.KFlat.ScalarBaseChange.projectionFormulaIso`: the projection formula for one
  pair of modules.
* `CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_isoX`: its degreewise form on the
  antidiagonal summands of a total complex.
* `CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso`: the resulting isomorphism of
  total complexes.

## Main results

* `CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars`: extension of scalars preserves
  K-flatness.
* `CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso_naturality`: the comparison of
  total complexes is natural in the complex over `R`.
* `CochainComplex.KFlat.ScalarBaseChange.projectionFormulaIso_natural_left` and
  `..._natural_right`: the projection formula is natural in both module variables.

## Implementation notes

The two ring universes are independent and the module universe is independent of both, so the
monoidal structures on the two module categories are the large-universe ones, with tensor units
`ULift R` and `ULift R'`; they are pinned explicitly at each ring because instance synthesis
cannot choose the extra universe argument on its own.

The degreewise comparison is built from the fact that restriction of scalars preserves the
coproduct of the antidiagonal summands, so a map out of the total degree-`n` object is
determined by its restrictions to those summands. Compatibility with the differentials is then
checked summand by summand, where the two signed partial differentials appear with the same
Koszul signs on both sides.

## References

* [The Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
* [The Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe uR uA v

namespace CochainComplex.KFlat.ScalarBaseChange

/-- Left tensoring by a fixed complex acts on the antidiagonal summand `N^i ⊗ K^j` by the
identity on `N^i` and the given map on `K^j`. -/
private lemma ι_tleftCochain_map
    {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
    [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]
    [∀ K L : CochainComplex C ℤ,
      HomologicalComplex.HasMapBifunctor K L (curriedTensor C) (.up ℤ)]
    (N : CochainComplex C ℤ) {K L : CochainComplex C ℤ} (g : K ⟶ L)
    (i j n : ℤ) (h : i + j = n) :
    HomologicalComplex.ιTensorObj N K i j n h ≫ ((TleftCochain N).map g).f n =
      (N.X i ◁ g.f j) ≫ HomologicalComplex.ιTensorObj N L i j n h := by
  change HomologicalComplex.ιMapBifunctor N K (curriedTensor C) (.up ℤ) i j n h ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 N) g (curriedTensor C) (.up ℤ)).f n = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp

/-- Restriction of scalars preserves and reflects acyclicity: in each degree the short complex
whose exactness is at stake has the same underlying maps of abelian groups. -/
lemma acyclic_restrictScalars_iff {R : Type uR} {A : Type uA}
    [CommRing R] [CommRing A] (f : R →+* A)
    (K : CochainComplex (ModuleCat.{max v uR uA} A) ℤ) :
    ((restrictScalarsLarge f).obj K).Acyclic ↔ K.Acyclic := by
  refine forall_congr' fun i => ?_
  rw [HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff,
    ShortComplex.moduleCat_exact_iff, ShortComplex.moduleCat_exact_iff]
  rfl

/-- Restriction of scalars preserves and reflects quasi-isomorphism. -/
lemma quasiIso_restrictScalars_iff {R : Type uR} {A : Type uA}
    [CommRing R] [CommRing A] (f : R →+* A)
    {K L : CochainComplex (ModuleCat.{max v uR uA} A) ℤ} (g : K ⟶ L) :
    QuasiIso ((restrictScalarsLarge f).map g) ↔ QuasiIso g :=
  HomologicalComplex.quasiIso_map_iff_of_preservesHomology g (ModuleCat.restrictScalars f)

section ProjectionFormula

open CategoryTheory.MonoidalCategory HomologicalComplex
open scoped TensorProduct

variable {R : Type uR} {R' : Type uA} [CommRing R] [CommRing R']

set_option backward.isDefEq.respectTransparency false

/-- The projection formula `V ⊗_{R'} (R' ⊗_R W) ≅ V ⊗_R W` for a ring homomorphism
`φ : R →+* R'`, an `R'`-module `V` and an `R`-module `W`, read as an isomorphism of
`R`-modules. -/
public noncomputable def projectionFormulaIso (φ : R →+* R') (V : ModuleCat.{max v uR uA} R') (W :
    ModuleCat.{max v uR uA} R) :
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  (ModuleCat.restrictScalars.{max v uR uA} φ).obj
      (V ⊗ (ModuleCat.extendScalars.{uR, uA, max v uR uA} φ).obj W)
      ≅ (ModuleCat.restrictScalars.{max v uR uA} φ).obj V ⊗ W :=
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  letI : Algebra R R' := φ.toAlgebra
  letI : Module R V := ((ModuleCat.restrictScalars.{max v uR uA} φ).obj V).isModule
  letI : IsScalarTower R R' V := ⟨fun a b v => by
    change (φ a * b) • v = φ a • b • v
    rw [mul_smul]⟩
  let e2 : (V ⊗[R'] (R' ⊗[R] W)) ≃ₗ[R] (V ⊗[R] W) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R R' R' V W).restrictScalars R
  LinearEquiv.toModuleIso e2

-- The degreewise comparison is assembled from the preserved coproduct of tensor summands.
/-- The degree-`n` component of the base-change comparison: on each antidiagonal summand it is
the projection formula, and restriction of scalars preserves the coproduct of those summands. -/
public noncomputable def baseChange_tensor_isoX (φ : R →+* R')
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (L : CochainComplex (ModuleCat.{max v uR uA}
      R') ℤ) (n : ℤ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  ((restrictScalarsLarge.{v, uR, uA} φ).obj
      (HomologicalComplex.tensorObj L ((extendScalarsLarge.{v, uR, uA} φ).obj K))).X n
      ≅ (HomologicalComplex.tensorObj ((restrictScalarsLarge.{v, uR, uA} φ).obj L) K).X n :=
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  by
  let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
  let Z := ((GradedObject.mapBifunctor
      (curriedTensor (ModuleCat.{max v uR uA} R')) ℤ ℤ).obj L.X).obj
      ((extendScalarsLarge.{v, uR, uA} φ).obj K).X
  have hcolim := isColimitOfPreserves (ModuleCat.restrictScalars.{max v uR uA} φ)
    (Z.isColimitCofanMapObj p n)
  let inv : ((HomologicalComplex.tensorObj ((restrictScalarsLarge.{v, uR, uA} φ).obj L) K).X n) ⟶
      (((restrictScalarsLarge.{v, uR, uA} φ).obj
        (HomologicalComplex.tensorObj L ((extendScalarsLarge.{v, uR, uA} φ).obj K))).X n) :=
    GradedObject.Monoidal.tensorObjDesc (fun q pp h =>
      (projectionFormulaIso φ (L.X q) (K.X pp)).inv ≫
        (ModuleCat.restrictScalars.{max v uR uA} φ).map
          (GradedObject.Monoidal.ιTensorObj L.X
            ((extendScalarsLarge.{v, uR, uA} φ).obj K).X q pp n h))
  let leg : (i : ↑(p ⁻¹' {n})) →
      ((ModuleCat.restrictScalars.{max v uR uA} φ).obj (Z.mapObjFun p n i)) ⟶
        ((HomologicalComplex.tensorObj ((restrictScalarsLarge.{v, uR, uA} φ).obj L) K).X n) :=
    fun ⟨⟨q, pp⟩, (h : q + pp = n)⟩ =>
      (projectionFormulaIso φ (L.X q) (K.X pp)).hom ≫
        GradedObject.Monoidal.ιTensorObj ((restrictScalarsLarge.{v, uR, uA} φ).obj L).X K.X q pp n h
  let tgt : Cocone (Discrete.functor (Z.mapObjFun p n) ⋙ ModuleCat.restrictScalars.{max v uR uA} φ)
    :=
    { pt := (HomologicalComplex.tensorObj ((restrictScalarsLarge.{v, uR, uA} φ).obj L) K).X n
      ι := Discrete.natTrans (fun i => leg i.as) }
  let hom := hcolim.desc tgt
  have fac : ∀ (q pp : ℤ) (h : q + pp = n),
      (ModuleCat.restrictScalars.{max v uR uA} φ).map
        (GradedObject.Monoidal.ιTensorObj L.X
          ((extendScalarsLarge.{v, uR, uA} φ).obj K).X q pp n h) ≫ hom
      = (projectionFormulaIso φ (L.X q) (K.X pp)).hom ≫
        GradedObject.Monoidal.ιTensorObj
          ((restrictScalarsLarge.{v, uR, uA} φ).obj L).X K.X q pp n h := by
    intro q pp h
    exact hcolim.fac tgt ⟨⟨(q, pp), h⟩⟩
  have hinv : ∀ (q pp : ℤ) (h : q + pp = n),
      GradedObject.Monoidal.ιTensorObj
        ((restrictScalarsLarge.{v, uR, uA} φ).obj L).X K.X q pp n h ≫ inv
      = (projectionFormulaIso φ (L.X q) (K.X pp)).inv ≫
        (ModuleCat.restrictScalars.{max v uR uA} φ).map
          (GradedObject.Monoidal.ιTensorObj L.X
            ((extendScalarsLarge.{v, uR, uA} φ).obj K).X q pp n h) := by
    intro q pp h
    exact GradedObject.Monoidal.ι_tensorObjDesc _ q pp h
  refine ⟨hom, inv, ?_, ?_⟩
  · refine hcolim.hom_ext fun ⟨⟨q, pp⟩, (h : q + pp = n)⟩ => ?_
    change (ModuleCat.restrictScalars.{max v uR uA} φ).map
        (GradedObject.Monoidal.ιTensorObj L.X ((extendScalarsLarge.{v, uR, uA} φ).obj K).X q pp n h)
        ≫ hom ≫ inv = _
    rw [reassoc_of% fac q pp h, hinv q pp h, Iso.hom_inv_id_assoc]
    exact (Category.comp_id _).symm
  · exact GradedObject.Monoidal.tensorObj_ext _ _ fun q pp h => by
      rw [reassoc_of% hinv q pp h, fac q pp h, Iso.inv_hom_id_assoc]
      exact (Category.comp_id _).symm

-- Both sides are compared on a single antidiagonal summand of the total complex.
/-- The inverse degreewise base-change comparison, read on an antidiagonal summand. -/
public theorem baseChange_tensor_isoX_inv_ι (φ : R →+* R')
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (L : CochainComplex (ModuleCat.{max v uR uA}
      R') ℤ) (n : ℤ)
    (q pp : ℤ) (h : q + pp = n) :
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  GradedObject.Monoidal.ιTensorObj ((restrictScalarsLarge.{v, uR, uA} φ).obj L).X K.X q pp n h
      ≫ (baseChange_tensor_isoX φ K L n).inv
      = (projectionFormulaIso φ (L.X q) (K.X pp)).inv ≫
        (ModuleCat.restrictScalars.{max v uR uA} φ).map
          (GradedObject.Monoidal.ιTensorObj L.X
            ((extendScalarsLarge.{v, uR, uA} φ).obj K).X q pp n h) :=
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  by
  exact GradedObject.Monoidal.ι_tensorObjDesc (fun q pp h =>
      (projectionFormulaIso φ (L.X q) (K.X pp)).inv ≫
        (ModuleCat.restrictScalars.{max v uR uA} φ).map
          (GradedObject.Monoidal.ιTensorObj L.X
            ((extendScalarsLarge.{v, uR, uA} φ).obj K).X q pp n h)) q pp h

-- The colimit-collapse identity is checked on every antidiagonal summand.
/-- The degreewise base-change comparison, read on an antidiagonal summand. -/
public theorem baseChange_tensor_isoX_hom_ι (φ : R →+* R')
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (L : CochainComplex (ModuleCat.{max v uR uA}
      R') ℤ) (n : ℤ)
    (q pp : ℤ) (h : q + pp = n) :
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  (ModuleCat.restrictScalars.{max v uR uA} φ).map
        (GradedObject.Monoidal.ιTensorObj L.X ((extendScalarsLarge.{v, uR, uA} φ).obj K).X q pp n h)
      ≫ (baseChange_tensor_isoX φ K L n).hom
      = (projectionFormulaIso φ (L.X q) (K.X pp)).hom ≫
        GradedObject.Monoidal.ιTensorObj
          ((restrictScalarsLarge.{v, uR, uA} φ).obj L).X K.X q pp n h :=
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  by
  have hinv := baseChange_tensor_isoX_inv_ι φ K L n q pp h
  have h2 := hinv =≫ (baseChange_tensor_isoX φ K L n).hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc] at h2
  rw [h2, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The projection formula evaluated on a homogeneous tensor. -/
public theorem projectionFormulaIso_hom_tmul (φ : R →+* R') (V : ModuleCat.{max v uR uA} R') (W :
    ModuleCat.{max v uR uA} R)
    (v : V) (r' : R') (w : W) :
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  (ModuleCat.Hom.hom (projectionFormulaIso φ V W).hom)
        (v ⊗ₜ[R'] ((r' : ((ModuleCat.restrictScalars.{uA} φ).obj (ModuleCat.of R' R'))) ⊗ₜ[R] w))
      = (letI : Module R V := ((ModuleCat.restrictScalars.{max v uR uA} φ).obj V).isModule; (r' •
        v) ⊗ₜ[R] w) :=
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  rfl

/-- The projection formula is natural in the `R'`-module variable. -/
public theorem projectionFormulaIso_natural_left (φ : R →+* R') {V V' : ModuleCat.{max v uR uA}
    R'} (W : ModuleCat.{max v uR uA} R)
    (f : V ⟶ V') :
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  (ModuleCat.restrictScalars.{max v uR uA} φ).map (f ▷ (ModuleCat.extendScalars.{uR, uA, max v uR
    uA} φ).obj W)
        ≫ (projectionFormulaIso φ V' W).hom
      = (projectionFormulaIso φ V W).hom ≫ ((ModuleCat.restrictScalars.{max v uR uA} φ).map f ▷ W)
        :=
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  by
  apply ModuleCat.hom_ext
  ext x
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [_root_.map_add, ha, hb]
  | tmul v y =>
    induction y using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.tmul_add, _root_.map_add, ha, hb]
    | tmul r' w =>
      let : Module R V := ((ModuleCat.restrictScalars φ).obj V).isModule
      let : Module R V' := ((ModuleCat.restrictScalars φ).obj V').isModule
      change ((show R' from r') • f v) ⊗ₜ[R] w = f ((show R' from r') • v) ⊗ₜ[R] w
      rw [_root_.map_smul]

/-- The projection formula is natural in the `R`-module variable. -/
public theorem projectionFormulaIso_natural_right (φ : R →+* R') (V : ModuleCat.{max v uR uA} R')
    {W W' : ModuleCat.{max v uR uA} R}
    (g : W ⟶ W') :
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  (ModuleCat.restrictScalars.{max v uR uA} φ).map (V ◁ (ModuleCat.extendScalars.{uR, uA, max v uR
    uA} φ).map g)
        ≫ (projectionFormulaIso φ V W').hom
      = (projectionFormulaIso φ V W).hom ≫ ((ModuleCat.restrictScalars.{max v uR uA} φ).obj V ◁ g)
        :=
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  by
  let : Algebra R R' := φ.toAlgebra
  apply ModuleCat.hom_ext
  ext x
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => simp only [_root_.map_add, ha, hb]
  | tmul v y =>
    induction y using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.tmul_add, _root_.map_add, ha, hb]
    | tmul r' w => rfl

/-- The total differential of a tensor product of complexes, read on an antidiagonal summand as
the sum of the two Koszul-signed partial differentials. -/
@[sga "4 XVII 1.1.10" "(i)"]
public theorem ι_tensorObj_d (A B : CochainComplex (ModuleCat.{max v uR} R) ℤ) (q pp i j : ℤ) (h :
    q + pp = i) :
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, v};
  letI : MonoidalCategory (ModuleCat.{max v uR} R) := ModuleCat.liftedModuleMonoidal.{uR, v};
  letI : MonoidalPreadditive (ModuleCat.{max v uR} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, v};
  GradedObject.Monoidal.ιTensorObj A.X B.X q pp i h ≫ (HomologicalComplex.tensorObj A B).d i j
    = HomologicalComplex.mapBifunctor.d₁ A B (curriedTensor (ModuleCat.{max v uR} R))
      (ComplexShape.up ℤ) q pp
        j
      + HomologicalComplex.mapBifunctor.d₂ A B (curriedTensor (ModuleCat.{max v uR} R))
        (ComplexShape.up
          ℤ) q pp j :=
  let : MonoidalCategoryStruct (ModuleCat.{max v uR} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, v};
  let : MonoidalCategory (ModuleCat.{max v uR} R) := ModuleCat.liftedModuleMonoidal.{uR, v};
  let : MonoidalPreadditive (ModuleCat.{max v uR} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, v};
  by
  change HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{max v uR} R))
    (ComplexShape.up ℤ) q
      pp i h ≫ _ = _
  rw [show (HomologicalComplex.tensorObj A B).d i j = HomologicalComplex.mapBifunctor.D₁ A B
    (curriedTensor (ModuleCat.{max v uR} R))
      (ComplexShape.up ℤ) i j + HomologicalComplex.mapBifunctor.D₂ A B (curriedTensor
        (ModuleCat.{max v uR} R))
      (ComplexShape.up ℤ) i j from HomologicalComplex.mapBifunctor.d_eq _ _ _ _ _ _]
  rw [Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
      HomologicalComplex.mapBifunctor.ι_D₂]

-- Compatibility with the differentials unfolds both signed partial differentials.
/-- The degreewise base-change comparisons commute with the total differentials. -/
public theorem baseChange_tensor_iso_comm (φ : R →+* R')
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (L : CochainComplex (ModuleCat.{max v uR uA}
      R') ℤ)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  (baseChange_tensor_isoX φ K L i).hom ≫
      (HomologicalComplex.tensorObj ((restrictScalarsLarge.{v, uR, uA} φ).obj L) K).d i j
      = ((restrictScalarsLarge.{v, uR, uA} φ).obj
        (HomologicalComplex.tensorObj L ((extendScalarsLarge.{v, uR, uA} φ).obj K))).d i j
        ≫ (baseChange_tensor_isoX φ K L j).hom :=
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  by
  let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
  let Z := ((CategoryTheory.GradedObject.mapBifunctor (curriedTensor (ModuleCat.{max v uR uA} R'))
    ℤ ℤ).obj
      L.X).obj
      ((extendScalarsLarge.{v, uR, uA} φ).obj K).X
  have hcolim := CategoryTheory.Limits.isColimitOfPreserves (ModuleCat.restrictScalars.{max v uR
    uA} φ)
    (Z.isColimitCofanMapObj p i)
  apply hcolim.hom_ext
  rintro ⟨⟨q, pp⟩, (h : q + pp = i)⟩
  have hleg : ((ModuleCat.restrictScalars.{max v uR uA} φ).mapCocone (Z.cofanMapObj p i)).ι.app
    ⟨⟨(q, pp), h⟩⟩
      = (ModuleCat.restrictScalars.{max v uR uA} φ).map
        (GradedObject.Monoidal.ιTensorObj L.X
          ((extendScalarsLarge.{v, uR, uA} φ).obj K).X q pp i h) := rfl
  rw [hleg]
  rw [reassoc_of% baseChange_tensor_isoX_hom_ι φ K L i q pp h]
  rw [ι_tensorObj_d.{uR, max v uA} ((restrictScalarsLarge.{v, uR, uA} φ).obj L) K q pp i j h]
  have hdLHS : ((restrictScalarsLarge.{v, uR, uA} φ).obj
    (HomologicalComplex.tensorObj L ((extendScalarsLarge.{v, uR, uA} φ).obj K))).d i j
      = (ModuleCat.restrictScalars.{max v uR uA} φ).map
        ((HomologicalComplex.tensorObj L ((extendScalarsLarge.{v, uR, uA} φ).obj K)).d i j) := rfl
  rw [hdLHS, ← Functor.map_comp_assoc,
    ι_tensorObj_d.{uA, max v uR} L ((extendScalarsLarge.{v, uR, uA} φ).obj K) q pp i j h,
      Functor.map_add,
    Preadditive.add_comp]
  rw [Preadditive.comp_add]
  have hij' : i + 1 = j := hij
  have hq' : (ComplexShape.up ℤ).Rel q (q + 1) := by simp [ComplexShape.up_Rel]
  have hpp' : (ComplexShape.up ℤ).Rel pp (pp + 1) := by simp [ComplexShape.up_Rel]
  have hd1L : (q + 1) + pp = j := by omega
  have hd2K : q + (pp + 1) = j := by omega
  have key : ∀ (a b : ℤ) (hab : a + b = j),
      (ModuleCat.restrictScalars.{max v uR uA} φ).map
          (HomologicalComplex.ιMapBifunctor L ((extendScalarsLarge.{v, uR, uA} φ).obj K)
            (curriedTensor (ModuleCat.{max v uR uA} R')) (ComplexShape.up ℤ) a b j hab) ≫
        (baseChange_tensor_isoX φ K L j).hom =
      (projectionFormulaIso φ (L.X a) (K.X b)).hom ≫
        HomologicalComplex.ιMapBifunctor ((restrictScalarsLarge.{v, uR, uA} φ).obj L) K
          (curriedTensor (ModuleCat.{max v uR uA} R)) (ComplexShape.up ℤ) a b j hab :=
    baseChange_tensor_isoX_hom_ι φ K L j
  congr 1
  · rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hq' pp j hd1L,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hq' pp j hd1L,
      Linear.comp_units_smul, Functor.map_units_smul, Linear.units_smul_comp]
    congr 1
    rw [Functor.map_comp, Category.assoc, key, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (projectionFormulaIso_natural_left φ (K.X pp) (L.d q (q + 1))).symm
  · rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ q hpp' j hd2K,
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ q hpp' j hd2K,
      Linear.comp_units_smul, Functor.map_units_smul, Linear.units_smul_comp]
    congr 1
    rw [Functor.map_comp, Category.assoc, key, ← Category.assoc, ← Category.assoc]
    congr 1
    exact (projectionFormulaIso_natural_right φ (L.X q) (K.d pp (pp + 1))).symm

set_option maxHeartbeats 2000000 in
-- Assembling the degreewise comparisons into a map of complexes.
/-- The base-change comparison of total complexes: the underlying complex of `R`-modules of
`L ⊗_{R'} (R' ⊗_R K)` is `L ⊗_R K`. -/
public noncomputable def baseChange_tensor_iso (φ : R →+* R')
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ) (L : CochainComplex (ModuleCat.{max v uR uA}
      R') ℤ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  ((restrictScalarsLarge.{v, uR, uA} φ).obj
      (HomologicalComplex.tensorObj L ((extendScalarsLarge.{v, uR, uA} φ).obj K)))
      ≅ (HomologicalComplex.tensorObj ((restrictScalarsLarge.{v, uR, uA} φ).obj L) K) :=
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  HomologicalComplex.Hom.isoOfComponents
    (fun n => baseChange_tensor_isoX φ K L n)
    (fun i j hij => baseChange_tensor_iso_comm φ K L i j hij)


set_option maxHeartbeats 2000000 in
-- Naturality is checked on the summands of the two total complexes.
/-- The base-change comparison of total complexes is natural in the complex over `R`. -/
public lemma baseChange_tensor_iso_naturality (φ : R →+* R')
    {K K' : CochainComplex (ModuleCat.{max v uR uA} R) ℤ}
    (g : K ⟶ K') (L : CochainComplex (ModuleCat.{max v uR uA} R') ℤ) :
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  letI : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  letI : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  letI : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  (restrictScalarsLarge.{v, uR, uA} φ).map
        ((TleftCochain L).map ((extendScalarsLarge.{v, uR, uA} φ).map g)) ≫
      (baseChange_tensor_iso φ K' L).hom =
    (baseChange_tensor_iso φ K L).hom ≫
      (TleftCochain ((restrictScalarsLarge.{v, uR, uA} φ).obj L)).map g := by
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  ext n : 1
  let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
  let Z := ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{max v uR uA} R')) ℤ ℤ).obj
    L.X).obj ((extendScalarsLarge.{v, uR, uA} φ).obj K).X
  apply (isColimitOfPreserves (ModuleCat.restrictScalars.{max v uR uA} φ)
    (Z.isColimitCofanMapObj p n)).hom_ext
  rintro ⟨⟨i, j⟩, (h : i + j = n)⟩
  change (ModuleCat.restrictScalars.{max v uR uA} φ).map
      (GradedObject.Monoidal.ιTensorObj L.X ((extendScalarsLarge.{v, uR, uA} φ).obj K).X i j n h) ≫
        ((ModuleCat.restrictScalars.{max v uR uA} φ).map (((TleftCochain L).map
          ((extendScalarsLarge.{v, uR, uA} φ).map g)).f n) ≫
          (baseChange_tensor_isoX φ K' L n).hom) =
    (ModuleCat.restrictScalars.{max v uR uA} φ).map
      (GradedObject.Monoidal.ιTensorObj L.X ((extendScalarsLarge.{v, uR, uA} φ).obj K).X i j n h) ≫
        ((baseChange_tensor_isoX φ K L n).hom ≫
          ((TleftCochain ((restrictScalarsLarge.{v, uR, uA} φ).obj L)).map g).f n)
  rw [← Functor.map_comp_assoc]
  erw [ι_tleftCochain_map]
  erw [Functor.map_comp, Category.assoc, baseChange_tensor_isoX_hom_ι,
    reassoc_of% baseChange_tensor_isoX_hom_ι]
  erw [ι_tleftCochain_map]
  change (ModuleCat.restrictScalars.{max v uR uA} φ).map
      (L.X i ◁ (ModuleCat.extendScalars.{uR, uA, max v uR uA} φ).map (g.f j)) ≫
        (projectionFormulaIso φ (L.X i) (K'.X j)).hom ≫ _ = _
  rw [reassoc_of% projectionFormulaIso_natural_right]
  rfl

/-- **Stacks 06Y1.** Extension of scalars along `φ : R →+* R'` carries a K-flat complex of
`R`-modules to a K-flat complex of `R'`-modules: tensoring over `R'` with the base change is,
after restriction of scalars, tensoring over `R`, and restriction of scalars reflects
acyclicity.

The two rings inhabit independent universes `uR` and `uA`, as they do in the source, where they
are related only by a ring map; the module universe `max v uR uA` is independent of both and
large enough to hold the modules of either ring. `CochainComplex.kFlat_baseChange` in
`StacksFrontier.Homology.KFlat.BaseChange` is the specialization of this statement to a single
common universe. -/
@[stacks 06Y1]
public lemma kFlat_extendScalars (φ : R →+* R')
    (K : CochainComplex (ModuleCat.{max v uR uA} R) ℤ)
    (hK : CochainComplex.KFlat.{uR, max v uA} K) :
    CochainComplex.KFlat.{uA, max v uR} ((extendScalarsLarge.{v, uR, uA} φ).obj K) := by
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalStruct.{uR, max v uA};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidal.{uR, max v uA};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R) :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uR, max v uA};
  let : MonoidalCategoryStruct (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalStruct.{uA, max v uR};
  let : MonoidalCategory (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidal.{uA, max v uR};
  let : MonoidalPreadditive (ModuleCat.{max v uR uA} R') :=
    ModuleCat.liftedModuleMonoidalPreadditive.{uA, max v uR};
  intro L hL
  exact (acyclic_restrictScalars_iff φ _).1 <| HomologicalComplex.Acyclic.of_iso
    (baseChange_tensor_iso φ K L).symm (hK _ ((acyclic_restrictScalars_iff φ L).2 hL))

end ProjectionFormula

end CochainComplex.KFlat.ScalarBaseChange

end
