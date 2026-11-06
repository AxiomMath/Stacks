module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.AlgebraicGeometry.Descent.Module.CechConerveTensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exactness of the Amitsur complex of a faithfully flat algebra

Let `A` be a faithfully flat commutative algebra over `R` and let `M` be an arbitrary
`R`-module. This file proves that the extended Amitsur cochain complex
`M → A ⊗[R] M → (A ⊗[R] A) ⊗[R] M → ⋯`
of `AlgebraicTopology.amitsurExtendedCochainComplex` is exact in every degree.

## Main definitions

* `Stacks.Descent.lTensorFunctor` is `B ⊗[R] -` as a functor of module categories.
* `Stacks.Descent.amitsurCosimplicial` is the cosimplicial module `(A/R)• ⊗[R] M`.
* `Stacks.Descent.amitsurShiftIso` is the module-level form of `Stacks.Descent.cechShiftIso`:
  `A ⊗[R] ((A/R)ₙ ⊗[R] M) ≅ (A/R)_{n+1} ⊗[R] M`.
* `AlgebraicTopology.shiftedCofaceSum` is the alternating sum of all coface maps of a
  cosimplicial object except the zeroth one.

## Main results

* `Stacks.Descent.amitsurExtendedCochainComplex_acyclic_of_faithfullyFlat` is Stacks 023M.
* `AlgebraicTopology.shiftedCofaceSum_comp_sigma_add` is the contracting homotopy: the zeroth
  codegeneracy contracts the complex built from the coface maps of positive index.
* `Stacks.Descent.exact_of_lTensor_ladder` reflects exactness of a two-step complex of
  `R`-modules from a contraction of a complex isomorphic to its base change along `R → A`.

## Implementation notes

The Čech conerve is an abstract wide pushout with no concrete description as a tensor power, so
faithful flatness is applied through `cechShiftIso`, which identifies its degree-`n + 1` part
with `A ⊗[R]` its degree-`n` part. Under that identification the base change along `R → A` of
the Amitsur complex is the complex of the coface maps of positive index, which is contracted by
the zeroth codegeneracy: this is a simplicial identity, so the whole argument needs no formula
for the terms of the complex. Faithful flatness then reflects exactness.

Degree zero of the extended complex uses that the degree-zero part of the Čech conerve is `A`
itself (`Stacks.Descent.cechConerveZeroIso`), which makes the augmentation the canonical map
`m ↦ 1 ⊗ₜ m`, injective by `Module.FaithfullyFlat.tensorProduct_mk_injective`.

The statement allows the ring and the coefficient module to have independent universes, while
the Čech conerve is formed in a single universe, so the results in a single universe are
transported to the lifted rings; `Stacks.Descent.faithfullyFlat_ulift` carries faithful flatness
across that lift.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Arrow AlgebraicTopology
open scoped TensorProduct

universe u v w

namespace AlgebraicTopology

section Cosimplicial

variable {C : Type u} [Category.{v} C] [Preadditive C] (X : CosimplicialObject C)

/-- The alternating sum of all coface maps of a cosimplicial object except the zeroth one. Under
the identification of the Čech conerve in degree `n + 1` with the base change of its degree-`n`
part, this is the differential of the base change of the alternating coface map complex. -/
noncomputable def shiftedCofaceSum (n : ℕ) : X.obj (.mk n) ⟶ X.obj (.mk (n + 1)) :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • X.δ i.succ

/-- In degree zero the only coface map of positive index is the one of index one. -/
lemma shiftedCofaceSum_zero : shiftedCofaceSum X 0 = X.δ (Fin.succ 0) := by
  rw [shiftedCofaceSum, Fin.sum_univ_one, Fin.val_zero, pow_zero, one_zsmul]

omit [Preadditive C] in
/-- The zeroth codegeneracy is a retraction of the coface map of index one. -/
lemma delta_succ_comp_sigma_self {n : ℕ} :
    X.δ (0 : Fin (n + 1)).succ ≫ X.σ 0 = 𝟙 (X.obj (.mk n)) := by
  dsimp only [CosimplicialObject.δ, CosimplicialObject.σ]
  rw [← X.map_comp, SimplexCategory.δ_comp_σ_succ, CategoryTheory.Functor.map_id]

omit [Preadditive C] in
/-- A coface map of index at least two commutes past the zeroth codegeneracy, with its index
lowered by one. -/
lemma delta_succ_succ_comp_sigma_zero {n : ℕ} (j : Fin (n + 1)) :
    X.δ j.succ.succ ≫ X.σ 0 = X.σ 0 ≫ X.δ j.succ := by
  dsimp only [CosimplicialObject.δ, CosimplicialObject.σ]
  rw [← X.map_comp, ← X.map_comp,
    show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc from Fin.castSucc_zero.symm,
    SimplexCategory.δ_comp_σ_of_gt (by rw [Fin.castSucc_zero]; exact Fin.succ_pos j)]

/-- In degree zero the zeroth codegeneracy is a retraction of `shiftedCofaceSum`. -/
lemma shiftedCofaceSum_zero_comp_sigma :
    shiftedCofaceSum X 0 ≫ X.σ 0 = 𝟙 (X.obj (.mk 0)) := by
  rw [shiftedCofaceSum_zero, delta_succ_comp_sigma_self]

/-- **The contracting homotopy.** The zeroth codegeneracy is a contracting homotopy for the
complex of the coface maps of positive index: this is the fourth simplicial identity for the
terms of positive index and the third one for the term of index one. -/
lemma shiftedCofaceSum_comp_sigma_add (n : ℕ) :
    shiftedCofaceSum X (n + 1) ≫ X.σ 0 + X.σ 0 ≫ shiftedCofaceSum X n =
      𝟙 (X.obj (.mk (n + 1))) := by
  have htail : ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j.succ : ℕ) • X.δ j.succ.succ) ≫ X.σ 0 =
      -(X.σ 0 ≫ shiftedCofaceSum X n) := by
    rw [shiftedCofaceSum, Preadditive.comp_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, delta_succ_succ_comp_sigma_zero,
      Fin.val_succ, pow_succ, mul_neg_one, neg_zsmul]
  have key : shiftedCofaceSum X (n + 1) ≫ X.σ 0 =
      𝟙 (X.obj (.mk (n + 1))) - X.σ 0 ≫ shiftedCofaceSum X n := by
    rw [shiftedCofaceSum, Preadditive.sum_comp, Fin.sum_univ_succ, Fin.val_zero, pow_zero,
      one_zsmul, delta_succ_comp_sigma_self, htail, ← sub_eq_add_neg]
  rw [key, sub_add_cancel]

end Cosimplicial

section Complex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The differential of the alternating coface map complex is the alternating sum of the coface
maps. -/
lemma alternatingCofaceMapComplex_obj_d (X : CosimplicialObject C) (n : ℕ) :
    ((alternatingCofaceMapComplex C).obj X).d n (n + 1) =
      AlternatingCofaceMapComplex.objD X n := by
  show (CochainComplex.of _ _ (AlternatingCofaceMapComplex.d_squared X)).d n (n + 1) = _
  exact CochainComplex.of_d (fun n : ℕ ↦ X.obj (.mk n))
    (AlternatingCofaceMapComplex.objD X) n

/-- Away from the augmentation, the differentials of the extended complex are those of the
alternating coface map complex. -/
lemma extendedAlternatingCofaceMapComplex_d_succ_succ (X : CosimplicialObject.Augmented C) (Y : C)
    (e : Y ⟶ X.left) (n : ℕ) :
    (extendedAlternatingCofaceMapComplex X Y e).d (n + 1) (n + 2) =
      AlternatingCofaceMapComplex.objD X.right n :=
  (CochainComplex.augment_d_succ_succ _ _ _ n (n + 1)).trans
    (alternatingCofaceMapComplex_obj_d X.right n)

variable {D : Type*} [Category.{v} D] [Preadditive D]

/-- An additive functor carries the alternating coface map differential of a cosimplicial object
to that of its image. -/
lemma objD_comp (X : CosimplicialObject C) (F : C ⥤ D) [F.Additive] (n : ℕ) :
    AlternatingCofaceMapComplex.objD (X ⋙ F) n =
      F.map (AlternatingCofaceMapComplex.objD X n) := by
  rw [AlternatingCofaceMapComplex.objD, AlternatingCofaceMapComplex.objD, F.map_sum]
  exact Finset.sum_congr rfl fun i _ => (F.map_zsmul).symm

end Complex

end AlgebraicTopology

namespace Stacks.Descent

/-- Tensoring on the left with a fixed module, as a functor between module categories. -/
noncomputable def lTensorFunctor (R : Type u) (B : Type v) [CommRing R] [AddCommGroup B]
    [Module R B] : ModuleCat.{w} R ⥤ ModuleCat.{max v w} R where
  obj N := ModuleCat.of R (B ⊗[R] N)
  map f := ModuleCat.ofHom (LinearMap.lTensor B f.hom)
  map_id N := ModuleCat.hom_ext (LinearMap.lTensor_id (R := R) (M := B) (N := N))
  map_comp _ _ := ModuleCat.hom_ext (LinearMap.lTensor_comp (M := B) _ _)

/-- Tensoring on the left with a fixed module is an additive functor. -/
instance lTensorFunctor_additive (R : Type u) (B : Type v) [CommRing R] [AddCommGroup B]
    [Module R B] : (lTensorFunctor.{u, v, w} R B).Additive where
  map_add {_ _} f g := ModuleCat.hom_ext (LinearMap.lTensor_add (M := B) f.hom g.hom)

/-- **Faithfully flat descent of exactness.** If the base change along a faithfully flat
`R`-algebra `A` of a two-step complex of `R`-modules is isomorphic to a two-step complex which is
exact in the middle, then the original complex is exact. -/
lemma exact_of_lTensor_ladder (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    [Module.FaithfullyFlat R A] {P Q S P' Q' S' : Type*} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] [AddCommGroup S] [Module R S] [AddCommGroup P'] [Module R P']
    [AddCommGroup Q'] [Module R Q'] [AddCommGroup S'] [Module R S']
    (d₁ : P →ₗ[R] Q) (d₂ : Q →ₗ[R] S) (e₁ : A ⊗[R] P ≃ₗ[R] P') (e₂ : A ⊗[R] Q ≃ₗ[R] Q')
    (e₃ : A ⊗[R] S ≃ₗ[R] S') (D₁ : P' →ₗ[R] Q') (D₂ : Q' →ₗ[R] S')
    (h₁ : ∀ x, e₂ (LinearMap.lTensor A d₁ x) = D₁ (e₁ x))
    (h₂ : ∀ x, e₃ (LinearMap.lTensor A d₂ x) = D₂ (e₂ x))
    (hzero : ∀ p, d₂ (d₁ p) = 0) (hc : ∀ x, D₂ x = 0 → ∃ y, D₁ y = x) :
    Function.Exact d₁ d₂ := by
  refine Module.FaithfullyFlat.lTensor_reflects_exact R A _ _ fun b => ⟨fun hb => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hc (e₂ b) (by rw [← h₂, hb, map_zero])
    refine ⟨e₁.symm y, e₂.injective ?_⟩
    rw [h₁, e₁.apply_symm_apply, hy]
  · rintro ⟨a, rfl⟩
    rw [← LinearMap.lTensor_comp_apply, show d₂ ∘ₗ d₁ = 0 from LinearMap.ext hzero,
      LinearMap.lTensor_zero, LinearMap.zero_apply]

/-- The contraction of the complex of the coface maps of positive index, read on elements. -/
lemma exists_shiftedCofaceSum_eq {R : Type u} [Ring R] (X : CosimplicialObject (ModuleCat.{v} R))
    (n : ℕ) (x : X.obj (.mk (n + 1))) (hx : shiftedCofaceSum X (n + 1) x = 0) :
    ∃ y, shiftedCofaceSum X n y = x := by
  refine ⟨X.σ 0 x, ?_⟩
  have h : (shiftedCofaceSum X (n + 1) ≫ X.σ 0) x + (X.σ 0 ≫ shiftedCofaceSum X n) x = x := by
    simpa using congr($(shiftedCofaceSum_comp_sigma_add X n) x)
  rwa [ModuleCat.comp_apply, ModuleCat.comp_apply, hx, map_zero, zero_add] at h

section SameUniverse

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  (M : Type w) [AddCommGroup M] [Module R M]

/-- The cosimplicial `R`-module `(A/R)• ⊗[R] M`, whose alternating coface map complex is the
Amitsur complex of `R → A` with coefficients in `M`. -/
noncomputable abbrev amitsurCosimplicial : CosimplicialObject (ModuleCat.{max u w} R) :=
  (algebraArrow R A).cechConerve ⋙ tensorModuleFunctor R M

/-- The retraction of the zeroth Čech coprojection in degree zero. -/
noncomputable def cechConerveZeroInv :
    (algebraArrow R A).cechConerve.obj (.mk 0) ⟶ CommAlgCat.of R A :=
  WidePushout.desc (arrows := cechLegs (algebraArrow R A) (.mk 0))
    (algebraArrow R A).hom (fun _ => 𝟙 _) (fun _ => Category.comp_id _)

/-- The degree-zero part of the Čech conerve of `R ⟶ A` is `A` itself, by the zeroth
coprojection. -/
noncomputable def cechConerveZeroIso :
    CommAlgCat.of R A ≅ (algebraArrow R A).cechConerve.obj (.mk 0) where
  hom := cechι (f := algebraArrow R A) (.mk 0) 0
  inv := cechConerveZeroInv R A
  hom_inv_id := WidePushout.ι_desc _ _ _ _ 0
  inv_hom_id := by
    apply cech_hom_ext (f := algebraArrow R A)
    intro i
    obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) i 0
    have h : cechι (f := algebraArrow R A) (.mk 0) 0 ≫ cechConerveZeroInv R A =
        𝟙 (CommAlgCat.of R A) := WidePushout.ι_desc _ _ _ _ 0
    rw [← Category.assoc, h]
    simp

/-- `A ⊗[R] ((A/R)ₙ ⊗[R] M) ≅ (A/R)_{n + 1} ⊗[R] M`: the coefficient-module form of
`cechShiftIso`. -/
noncomputable def amitsurShiftIso (n : ℕ) :
    (lTensorFunctor R A).obj ((amitsurCosimplicial R A M).obj (.mk n)) ≅
      (amitsurCosimplicial R A M).obj (.mk (n + 1)) :=
  (TensorProduct.assoc R A ((algebraArrow R A).cechConerve.obj (.mk n)) M).symm.toModuleIso ≪≫
    (tensorModuleFunctor R M).mapIso (cechShiftIso R A n).symm

/-- The value of `amitsurShiftIso` on a pure tensor. -/
lemma amitsurShiftIso_hom_tmul (n : ℕ) (a : A)
    (x : (algebraArrow R A).cechConerve.obj (.mk n)) (m : M) :
    (amitsurShiftIso R A M n).hom (a ⊗ₜ (x ⊗ₜ m)) =
      (cechShiftBwd R A n).hom (a ⊗ₜ x) ⊗ₜ m := rfl

/-- `A ⊗[R] M ≃ₗ[R] (A/R)₀ ⊗[R] M`, the degree-zero case of `amitsurShiftIso`. -/
noncomputable def amitsurShiftZeroEquiv :
    A ⊗[R] M ≃ₗ[R] ((amitsurCosimplicial R A M).obj (.mk 0) : Type (max u w)) :=
  TensorProduct.congr (CommAlgCat.algEquivOfIso (cechConerveZeroIso R A)).toLinearEquiv
    (LinearEquiv.refl R M)

/-- The value of `amitsurShiftZeroEquiv` on a pure tensor. -/
lemma amitsurShiftZeroEquiv_tmul (a : A) (m : M) :
    amitsurShiftZeroEquiv R A M (a ⊗ₜ m) =
      (cechι (f := algebraArrow R A) (.mk 0) 0).hom a ⊗ₜ m := rfl

/-- `cechShiftIso` is natural for the structure maps fixing the leading index, in the direction
of `cechShiftBwd`. -/
lemma cechShiftBwd_naturality {n m : ℕ} (g : SimplexCategory.mk n ⟶ .mk m)
    (h : SimplexCategory.mk (n + 1) ⟶ .mk (m + 1)) (h₀ : h.toOrderHom 0 = 0)
    (hs : ∀ j : Fin (n + 1), h.toOrderHom j.succ = (g.toOrderHom j).succ) :
    cechShiftBwd R A n ≫ (algebraArrow R A).cechConerve.map h =
      cechTensorMap R A g ≫ cechShiftBwd R A m := by
  calc cechShiftBwd R A n ≫ (algebraArrow R A).cechConerve.map h
      = cechShiftBwd R A n ≫
          ((algebraArrow R A).cechConerve.map h ≫ cechShiftFwd R A m) ≫ cechShiftBwd R A m := by
        rw [Category.assoc, cechShiftFwd_cechShiftBwd, Category.comp_id]
    _ = cechShiftBwd R A n ≫ (cechShiftFwd R A n ≫ cechTensorMap R A g) ≫ cechShiftBwd R A m := by
        rw [cechShiftFwd_naturality R A g h h₀ hs]
    _ = cechTensorMap R A g ≫ cechShiftBwd R A m := by
        rw [Category.assoc, ← Category.assoc (cechShiftBwd R A n), cechShiftBwd_cechShiftFwd,
          Category.id_comp]

/-- Every coface map of positive index is the base change along `R → A` of a coface map one
degree down. -/
lemma cechShiftBwd_comp_map_delta_succ (n : ℕ) (i : Fin (n + 2)) :
    cechShiftBwd R A n ≫ (algebraArrow R A).cechConerve.map (SimplexCategory.δ i.succ) =
      cechTensorMap R A (SimplexCategory.δ i) ≫ cechShiftBwd R A (n + 1) :=
  cechShiftBwd_naturality R A _ _ (by simp [SimplexCategory.δ])
    (fun j => by simp [SimplexCategory.δ])

/-- `amitsurShiftIso` carries the base change of a coface map to the coface map of the next
index. -/
lemma amitsurShiftIso_naturality (n : ℕ) (i : Fin (n + 2)) :
    (lTensorFunctor R A).map ((amitsurCosimplicial R A M).δ i) ≫
        (amitsurShiftIso R A M (n + 1)).hom =
      (amitsurShiftIso R A M n).hom ≫ (amitsurCosimplicial R A M).δ i.succ := by
  apply ModuleCat.hom_ext
  refine TensorProduct.ext_threefold' fun a x m => ?_
  exact congrArg (fun z => z ⊗ₜ m)
    (congr($(cechShiftBwd_comp_map_delta_succ R A n i) (a ⊗ₜ x))).symm

/-- The base change along `R → A` of the Amitsur differential is, under `amitsurShiftIso`, the
alternating sum of the coface maps of positive index. -/
lemma amitsurShiftIso_ladder (n : ℕ) :
    (lTensorFunctor R A).map (AlternatingCofaceMapComplex.objD (amitsurCosimplicial R A M) n) ≫
        (amitsurShiftIso R A M (n + 1)).hom =
      (amitsurShiftIso R A M n).hom ≫ shiftedCofaceSum (amitsurCosimplicial R A M) (n + 1) := by
  rw [AlternatingCofaceMapComplex.objD, shiftedCofaceSum, Functor.map_sum, Preadditive.sum_comp,
    Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Functor.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    amitsurShiftIso_naturality]

/-- The base change along `R → A` of the augmentation is, under the shift isomorphisms, the
coface map of index one. -/
lemma amitsurShiftZeroEquiv_ladder :
    (amitsurShiftIso R A M 0).toLinearEquiv.toLinearMap ∘ₗ
        LinearMap.lTensor A (TensorProduct.mk R
          ((algebraArrow R A).cechConerve.obj (.mk 0) : Type u) M 1) =
      (shiftedCofaceSum (amitsurCosimplicial R A M) 0).hom ∘ₗ
        (amitsurShiftZeroEquiv R A M).toLinearMap := by
  rw [shiftedCofaceSum_zero]
  refine TensorProduct.ext' fun a m => ?_
  have hidx : (SimplexCategory.δ (Fin.succ (0 : Fin 1))).toOrderHom 0 = 0 := by
    simp [SimplexCategory.δ]
  have k2 : cechι (f := algebraArrow R A) (.mk 0) 0 ≫
      (algebraArrow R A).cechConerve.map (SimplexCategory.δ (Fin.succ (0 : Fin 1))) =
      cechι (f := algebraArrow R A) (.mk 1) 0 := by
    rw [cechι_comp_map, hidx]
  exact congrArg (fun z => z ⊗ₜ m)
    ((congr($(includeLeft_comp_cechShiftBwd R A 0) a)).trans (congr($k2 a)).symm)

/-- Every coface map fixes the image of the augmentation, because it is an algebra map. -/
lemma amitsurCosimplicial_delta_mk_one (n : ℕ) (i : Fin (n + 2)) (m : M) :
    ((amitsurCosimplicial R A M).δ i).hom
        ((1 : ((algebraArrow R A).cechConerve.obj (.mk n) : Type u)) ⊗ₜ m) = 1 ⊗ₜ m := by
  show ((algebraArrow R A).cechConerve.map (SimplexCategory.δ i)).hom 1 ⊗ₜ m = _
  rw [map_one]

/-- The augmentation composed with the first Amitsur differential vanishes. -/
lemma objD_zero_mk_one (m : M) :
    (AlternatingCofaceMapComplex.objD (amitsurCosimplicial R A M) 0).hom
      ((1 : ((algebraArrow R A).cechConerve.obj (.mk 0) : Type u)) ⊗ₜ m) = 0 := by
  have h2 : AlternatingCofaceMapComplex.objD (amitsurCosimplicial R A M) 0 =
      (amitsurCosimplicial R A M).δ 0 - (amitsurCosimplicial R A M).δ 1 := by
    rw [AlternatingCofaceMapComplex.objD, Fin.sum_univ_two]
    simp [sub_eq_add_neg]
  rw [h2]
  show ((amitsurCosimplicial R A M).δ 0).hom (1 ⊗ₜ m) -
    ((amitsurCosimplicial R A M).δ 1).hom (1 ⊗ₜ m) = 0
  rw [amitsurCosimplicial_delta_mk_one, amitsurCosimplicial_delta_mk_one]
  exact sub_self _

variable [Module.FaithfullyFlat R A]

/-- The Amitsur complex with coefficients in `M` is exact away from the augmentation. -/
theorem exact_objD_objD (n : ℕ) :
    Function.Exact (AlternatingCofaceMapComplex.objD (amitsurCosimplicial R A M) n).hom
      (AlternatingCofaceMapComplex.objD (amitsurCosimplicial R A M) (n + 1)).hom :=
  exact_of_lTensor_ladder R A _ _ (amitsurShiftIso R A M n).toLinearEquiv
    (amitsurShiftIso R A M (n + 1)).toLinearEquiv (amitsurShiftIso R A M (n + 2)).toLinearEquiv
    (shiftedCofaceSum (amitsurCosimplicial R A M) (n + 1)).hom
    (shiftedCofaceSum (amitsurCosimplicial R A M) (n + 2)).hom
    (fun x => congr($(amitsurShiftIso_ladder R A M n) x))
    (fun x => congr($(amitsurShiftIso_ladder R A M (n + 1)) x))
    (fun p => congr($(AlternatingCofaceMapComplex.d_squared (amitsurCosimplicial R A M) n) p))
    (fun x hx => exists_shiftedCofaceSum_eq _ (n + 1) x hx)

/-- The Amitsur complex with coefficients in `M` is exact at the term next to the
augmentation. -/
theorem exact_mk_objD :
    Function.Exact (TensorProduct.mk R ((algebraArrow R A).cechConerve.obj (.mk 0) : Type u) M 1)
      (AlternatingCofaceMapComplex.objD (amitsurCosimplicial R A M) 0).hom :=
  exact_of_lTensor_ladder R A _ _ (amitsurShiftZeroEquiv R A M)
    (amitsurShiftIso R A M 0).toLinearEquiv (amitsurShiftIso R A M 1).toLinearEquiv
    (shiftedCofaceSum (amitsurCosimplicial R A M) 0).hom
    (shiftedCofaceSum (amitsurCosimplicial R A M) 1).hom
    (fun x => congr($(amitsurShiftZeroEquiv_ladder R A M) x))
    (fun x => congr($(amitsurShiftIso_ladder R A M 0) x))
    (objD_zero_mk_one R A M) (fun x hx => exists_shiftedCofaceSum_eq _ 0 x hx)

/-- The augmentation of the Amitsur complex is injective. -/
theorem injective_mk_one :
    Function.Injective
      (TensorProduct.mk R ((algebraArrow R A).cechConerve.obj (.mk 0) : Type u) M 1) := by
  have : Module.FaithfullyFlat R ((algebraArrow R A).cechConerve.obj (.mk 0) : Type u) :=
    Module.FaithfullyFlat.of_linearEquiv R A
      (CommAlgCat.algEquivOfIso (cechConerveZeroIso R A)).symm.toLinearEquiv
  exact Module.FaithfullyFlat.tensorProduct_mk_injective M

end SameUniverse

section IndependentUniverses

variable (R : Type u) (A : Type v) (M : Type w) [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]

attribute [local instance] ULift.algebra'

/-- Faithful flatness is preserved by the canonical presentation of the two rings in a common
universe. -/
theorem faithfullyFlat_ulift [Module.FaithfullyFlat R A] :
    Module.FaithfullyFlat (ULift.{v} R) (ULift.{u} A) := by
  have : Module.FaithfullyFlat (ULift.{v} R) R :=
    Module.FaithfullyFlat.of_linearEquiv (ULift.{v} R) (ULift.{v} R)
      { toFun := ULift.up, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl,
        invFun := ULift.down, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have : Module.FaithfullyFlat R (ULift.{u} A) :=
    Module.FaithfullyFlat.of_linearEquiv R A ULift.moduleEquiv
  have : IsScalarTower (ULift.{v} R) R (ULift.{u} A) :=
    ⟨fun x y z => ULift.ext (mul_smul x.down y z.down)⟩
  exact Module.FaithfullyFlat.trans (ULift.{v} R) R (ULift.{u} A)

/-- Away from the augmentation, the differential of the extended Amitsur complex is the
alternating sum of the coface maps of `(A/R)• ⊗[R] M`. -/
lemma amitsurExtendedCochainComplex_d_succ_succ (n : ℕ) :
    (amitsurExtendedCochainComplex R A M).d (n + 1) (n + 2) =
      (ModuleCat.restrictScalars (algebraMap R (ULift.{v} R))).map
        (AlternatingCofaceMapComplex.objD
          (amitsurCosimplicial (ULift.{v} R) (ULift.{u} A) M) n) :=
  (extendedAlternatingCofaceMapComplex_d_succ_succ _ _ _ n).trans
    (objD_comp (amitsurCosimplicial (ULift.{v} R) (ULift.{u} A) M)
      (ModuleCat.restrictScalars (algebraMap R (ULift.{v} R))) n)

/-- The augmentation of the extended Amitsur complex is `m ↦ 1 ⊗ₜ m`. -/
lemma amitsurExtendedCochainComplex_d_zero_one_apply (x : ULift.{max u v} M) :
    (amitsurExtendedCochainComplex R A M).d 0 1 x =
      TensorProduct.mk (ULift.{v} R)
        ((algebraArrow (ULift.{v} R) (ULift.{u} A)).cechConerve.obj (.mk 0) :
          Type (max u v)) M 1 x.down := by
  show (cechHead (f := algebraArrow (ULift.{v} R) (ULift.{u} A)) (.mk 0)).hom 1 ⊗ₜ x.down = _
  rw [map_one]
  rfl

/-- **Stacks Lemma 023M.** For a faithfully flat algebra `A` over a commutative ring `R` and an
arbitrary `R`-module `M`, the extended Amitsur cochain complex
`M → A ⊗[R] M → (A ⊗[R] A) ⊗[R] M → ⋯`
is exact in every degree. -/
@[stacks 023M,
  stacks 03OA "coefficients in M",
  stacks 03O9 "the case M = R",
  sga "1 VIII 1.7" "affine case"]
theorem amitsurExtendedCochainComplex_acyclic_of_faithfullyFlat [Module.FaithfullyFlat R A] :
    (amitsurExtendedCochainComplex R A M).Acyclic := by
  have hff : Module.FaithfullyFlat (ULift.{v} R) (ULift.{u} A) := faithfullyFlat_ulift R A
  rw [HomologicalComplex.acyclic_iff]
  intro n
  match n with
  | 0 =>
    rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hx' := (amitsurExtendedCochainComplex_d_zero_one_apply R A M x).symm.trans hx
    have hdown : x.down = 0 :=
      injective_mk_one (ULift.{v} R) (ULift.{u} A) M (hx'.trans (map_zero _).symm)
    refine ⟨0, ?_⟩
    rw [map_zero]
    exact (ULift.down_injective hdown).symm
  | 1 =>
    rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hx' := (congr($(amitsurExtendedCochainComplex_d_succ_succ R A M 0) x)).symm.trans hx
    obtain ⟨m, hm⟩ := (exact_mk_objD (ULift.{v} R) (ULift.{u} A) M x).mp hx'
    exact ⟨ULift.up m,
      (amitsurExtendedCochainComplex_d_zero_one_apply R A M (ULift.up m)).trans hm⟩
  | n + 2 =>
    rw [HomologicalComplex.exactAt_iff' _ (n + 1) (n + 2) (n + 3) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hx' := (congr($(amitsurExtendedCochainComplex_d_succ_succ R A M (n + 1)) x)).symm.trans hx
    obtain ⟨y, hy⟩ := (exact_objD_objD (ULift.{v} R) (ULift.{u} A) M n x).mp hx'
    exact ⟨y, (congr($(amitsurExtendedCochainComplex_d_succ_succ R A M n) y)).trans hy⟩

end IndependentUniverses

end Stacks.Descent
