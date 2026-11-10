module

public import StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorAssoc
public import StacksFrontier.Homology.HomComplex.RHom.RestrictScalarsLaxTensorProjection

/-!
# The chain-level projection formula with the extended factor on the left

For `φ : A →+* B`, a complex `K` of `A`-modules and a complex `L` of `B`-modules, the unit of `K`
followed by the lax monoidal structure map of restriction of scalars is a map
`K ⊗_A L|_A ⟶ ((B ⊗_A K) ⊗_B L)|_A`, `k ⊗ l ↦ (1 ⊗ k) ⊗ l` on each summand of the total complex.
It is an isomorphism: this is the projection formula of Stacks 06Y6 with the two factors in the
opposite order to `CochainComplex.KFlat.ScalarBaseChange.baseChange_tensor_iso`.

## Main definitions

* `CochainComplex.ExtendScalars.leftProjectionModuleMap`: the module-level map
  `W ⊗_A V|_A ⟶ ((B ⊗_A W) ⊗_B V)|_A`.
* `CochainComplex.ExtendScalars.leftProjectionMap`: the map of complexes.

## Main results

* `CochainComplex.ExtendScalars.ιTensorObj_leftProjectionMap_f`: its value on a summand.
* `CochainComplex.ExtendScalars.isIso_leftProjectionMap`: it is an isomorphism.
* `CochainComplex.ExtendScalars.leftProjectionMap_naturality_right`: naturality in `L`.

## References

* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Functor.OplaxMonoidal
open scoped TensorProduct

universe u

namespace CochainComplex.ExtendScalars

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Extension of scalars along `φ` is additive. -/
local instance extendScalarsAdditiveLeftProjection :
    (ModuleCat.extendScalars.{u, u, u} φ).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).left_adjoint_additive

/-! ### The module-level map -/

/-- The module-level projection map `W ⊗_A V|_A ⟶ ((B ⊗_A W) ⊗_B V)|_A`: the unit, the oplax
comparison of extension of scalars and the counit in the second factor. -/
def leftProjectionModuleMap (W : ModuleCat.{u} A) (V : ModuleCat.{u} B) :
    W ⊗ (ModuleCat.restrictScalars.{u} φ).obj V ⟶
      (ModuleCat.restrictScalars.{u} φ).obj ((ModuleCat.extendScalars.{u, u, u} φ).obj W ⊗ V) :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.app _ ≫
    (ModuleCat.restrictScalars.{u} φ).map
      (δ (ModuleCat.extendScalars.{u, u, u} φ) W ((ModuleCat.restrictScalars.{u} φ).obj V) ≫
        (𝟙 _ ⊗ₘ (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).counit.app V))

open ChangeOfRings in
/-- The module-level projection map sends `w ⊗ v` to `(1 ⊗ w) ⊗ v`. -/
theorem leftProjectionModuleMap_tmul (W : ModuleCat.{u} A) (V : ModuleCat.{u} B) (w : W)
    (v : V) :
    (leftProjectionModuleMap φ W V).hom (w ⊗ₜ[A] (v : (ModuleCat.restrictScalars.{u} φ).obj V)) =
      TensorProduct.tmul B (M := (ModuleCat.extendScalars.{u, u, u} φ).obj W) (N := V)
        ((1 : B) ⊗ₜ[A,φ] w) v := by
  refine (congrArg (𝟙 ((ModuleCat.extendScalars.{u, u, u} φ).obj W) ⊗ₘ
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).counit.app V).hom
    (ModuleCat.extendScalars_δ_tmul φ W ((ModuleCat.restrictScalars.{u} φ).obj V) w v)).trans ?_
  exact congrArg (TensorProduct.tmul B (M := (ModuleCat.extendScalars.{u, u, u} φ).obj W)
    (N := V) ((1 : B) ⊗ₜ[A,φ] w))
    (ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul φ V v)

/-- The module-level projection map is an isomorphism. -/
instance isIso_leftProjectionModuleMap (W : ModuleCat.{u} A) (V : ModuleCat.{u} B) :
    IsIso (leftProjectionModuleMap φ W V) := by
  let := φ.toAlgebra
  let : Module A V := ((ModuleCat.restrictScalars.{u} φ).obj V).isModule
  have : IsScalarTower A B V := ⟨fun a b v => by
    change (φ a * b) • v = φ a • b • v
    rw [mul_smul]⟩
  let e : W ⊗[A] V ≃+ (B ⊗[A] W) ⊗[B] V :=
    (TensorProduct.comm A W V).toAddEquiv.trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange A B B V W).symm.toAddEquiv.trans
        (TensorProduct.comm B V (B ⊗[A] W)).toAddEquiv)
  have he : ∀ x : (W ⊗ (ModuleCat.restrictScalars.{u} φ).obj V : ModuleCat.{u} A),
      (leftProjectionModuleMap φ W V).hom x = e x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul w v => exact (leftProjectionModuleMap_tmul φ W V w v).trans rfl
    | add x y hx hy =>
      exact ((leftProjectionModuleMap φ W V).hom.map_add x y).trans
        ((congrArg₂ (· + ·) hx hy).trans (map_add e x y).symm)
  rw [ConcreteCategory.isIso_iff_bijective]
  have hfun : (⇑(leftProjectionModuleMap φ W V).hom : W ⊗[A] V → (B ⊗[A] W) ⊗[B] V) = ⇑e :=
    funext he
  change Function.Bijective (⇑(leftProjectionModuleMap φ W V).hom)
  rw [hfun]
  exact e.bijective

/-! ### The map of complexes -/

section Complexes

variable (K : CochainComplex (ModuleCat.{u} A) ℤ) (L : CochainComplex (ModuleCat.{u} B) ℤ)

/-- **The chain-level projection map with the extended factor on the left**
`K ⊗_A L|_A ⟶ ((B ⊗_A K) ⊗_B L)|_A`: the unit of `K` followed by the lax monoidal structure map
of restriction of scalars. -/
def leftProjectionMap :
    K ⊗ (CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L ⟶
      (CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj ((mapCochainComplex φ).obj K ⊗ L) :=
  ((extendRestrictScalarsComplexAdj φ).unit.app K ⊗ₘ
      𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L)) ≫
    restrictScalarsLaxTensor φ ((mapCochainComplex φ).obj K) L

/-- The projection map is the transpose of the inverse monoidality comparison followed by the
counit in the second factor. -/
theorem leftProjectionMap_eq_homEquiv :
    leftProjectionMap φ K L = (extendRestrictScalarsComplexAdj φ).homEquiv _ _
      ((extendScalarsMonoidalIso φ K
          ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L)).inv ≫
        (𝟙 ((mapCochainComplex φ).obj K) ⊗ₘ (extendRestrictScalarsComplexAdj φ).counit.app L)) := by
  rw [leftProjectionMap, restrictScalarsLaxTensor]
  refine ((extendRestrictScalarsComplexAdj φ).homEquiv_naturality_left _ _).symm.trans ?_
  congr 1
  refine (congrArg (· ≫ _) (extendScalarsMonoidalIso_inv_naturality φ _ _)).trans ?_
  rw [Category.assoc, tensorHom_comp_tensorHom,
    (extendRestrictScalarsComplexAdj φ).left_triangle_components,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The projection map on a summand** of the total complex is the module-level projection map
followed by the inclusion of the corresponding summand. -/
theorem ιTensorObj_leftProjectionMap_f (a b n : ℤ) (h : a + b = n) :
    HomologicalComplex.ιTensorObj K ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L)
        a b n h ≫ (leftProjectionMap φ K L).f n =
      leftProjectionModuleMap φ (K.X a) (L.X b) ≫
        (ModuleCat.restrictScalars.{u} φ).map
          (HomologicalComplex.ιTensorObj ((mapCochainComplex φ).obj K) L a b n h) := by
  set RL := (CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L with hRL
  set μK := extendScalarsMonoidalIso φ K RL with hμK
  have hμ : (ModuleCat.extendScalars.{u, u, u} φ).map
        (HomologicalComplex.ιTensorObj K RL a b n h) ≫ μK.inv.f n =
      δ (ModuleCat.extendScalars.{u, u, u} φ) (K.X a) (RL.X b) ≫
        HomologicalComplex.ιTensorObj ((mapCochainComplex φ).obj K)
          ((mapCochainComplex φ).obj RL) a b n h := by
    have e := ι_extendScalarsMonoidalIso_hom φ K RL n a b h
    calc (ModuleCat.extendScalars.{u, u, u} φ).map
          (HomologicalComplex.ιTensorObj K RL a b n h) ≫ μK.inv.f n
        = (δ (ModuleCat.extendScalars.{u, u, u} φ) (K.X a) (RL.X b) ≫
            Functor.LaxMonoidal.μ (ModuleCat.extendScalars.{u, u, u} φ) (K.X a) (RL.X b)) ≫
          (ModuleCat.extendScalars.{u, u, u} φ).map
            (HomologicalComplex.ιTensorObj K RL a b n h) ≫ μK.inv.f n := by
          rw [Functor.Monoidal.δ_μ, Category.id_comp]
      _ = δ (ModuleCat.extendScalars.{u, u, u} φ) (K.X a) (RL.X b) ≫
          (HomologicalComplex.ιTensorObj ((mapCochainComplex φ).obj K)
            ((mapCochainComplex φ).obj RL) a b n h ≫ μK.hom.f n) ≫ μK.inv.f n := by
          rw [e]
          simp only [Category.assoc]
      _ = _ := by
          rw [Category.assoc, ← HomologicalComplex.comp_f, μK.hom_inv_id, HomologicalComplex.id_f]
          exact congrArg (_ ≫ ·) (Category.comp_id _)
  have hε : HomologicalComplex.ιTensorObj ((mapCochainComplex φ).obj K)
        ((mapCochainComplex φ).obj RL) a b n h ≫
        (𝟙 ((mapCochainComplex φ).obj K) ⊗ₘ (extendRestrictScalarsComplexAdj φ).counit.app L).f n =
      (𝟙 _ ⊗ₘ (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).counit.app (L.X b)) ≫
        HomologicalComplex.ιTensorObj ((mapCochainComplex φ).obj K) L a b n h := by
    change HomologicalComplex.ιMapBifunctor _ _ (curriedTensor (ModuleCat.{u} B))
        (ComplexShape.up ℤ) a b n h ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 _) ((extendRestrictScalarsComplexAdj φ).counit.app L)
        (curriedTensor (ModuleCat.{u} B)) (ComplexShape.up ℤ)).f n = _
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp [tensorHom_def]
    rfl
  have hη : HomologicalComplex.ιTensorObj K RL a b n h ≫
        (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.app ((K ⊗ RL).X n) =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.app (K.X a ⊗ RL.X b) ≫
        (ModuleCat.restrictScalars.{u} φ).map ((ModuleCat.extendScalars.{u, u, u} φ).map
          (HomologicalComplex.ιTensorObj K RL a b n h)) :=
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.naturality
      (HomologicalComplex.ιTensorObj K RL a b n h)).symm
  rw [leftProjectionMap_eq_homEquiv, Adjunction.homEquiv_unit]
  change HomologicalComplex.ιTensorObj K RL a b n h ≫
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).unit.app ((K ⊗ RL).X n) ≫
        (ModuleCat.restrictScalars.{u} φ).map (μK.inv.f n ≫
          (𝟙 ((mapCochainComplex φ).obj K) ⊗ₘ
            (extendRestrictScalarsComplexAdj φ).counit.app L).f n) = _
  rw [reassoc_of% hη, ← Functor.map_comp, reassoc_of% hμ, hε, leftProjectionModuleMap,
    Category.assoc, ← Functor.map_comp, Category.assoc]
  rfl

/-- The chain-level projection map is an isomorphism. -/
instance isIso_leftProjectionMap : IsIso (leftProjectionMap φ K L) := by
  suffices ∀ n, IsIso ((leftProjectionMap φ K L).f n) from
    HomologicalComplex.Hom.isIso_of_components _
  intro n
  let RL := (CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L
  let p : ℤ × ℤ → ℤ := fun x => x.1 + x.2
  let Z₁ := ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} A)) ℤ ℤ).obj K.X).obj RL.X
  let Z₂ := ((GradedObject.mapBifunctor (curriedTensor (ModuleCat.{u} B)) ℤ ℤ).obj
    ((mapCochainComplex φ).obj K).X).obj L.X
  have hc₁ := Z₁.isColimitCofanMapObj p n
  have hc₂ := isColimitOfPreserves (ModuleCat.restrictScalars.{u} φ) (Z₂.isColimitCofanMapObj p n)
  let w : Discrete.functor (Z₁.mapObjFun p n) ≅
      Discrete.functor (Z₂.mapObjFun p n) ⋙ ModuleCat.restrictScalars.{u} φ :=
    Discrete.natIso fun ⟨⟨⟨a, b⟩, _⟩⟩ =>
      @asIso _ _ _ _ (leftProjectionModuleMap φ (K.X a) (L.X b))
        (isIso_leftProjectionModuleMap φ (K.X a) (L.X b))
  have he : (leftProjectionMap φ K L).f n = (hc₁.coconePointsIsoOfNatIso hc₂ w).hom := by
    refine hc₁.hom_ext fun ⟨⟨⟨a, b⟩, hab⟩⟩ => ?_
    refine Eq.trans ?_ (IsColimit.comp_coconePointsIsoOfNatIso_hom hc₁ hc₂ w _).symm
    exact ιTensorObj_leftProjectionMap_f φ K L a b n hab
  rw [he]
  exact (hc₁.coconePointsIsoOfNatIso hc₂ w).isIso_hom

/-- **Naturality of the projection map in the complex of `B`-modules.** -/
theorem leftProjectionMap_naturality_right {L L' : CochainComplex (ModuleCat.{u} B) ℤ}
    (v : L ⟶ L') :
    (K ◁ (CochainComplex.restrictScalarsLarge.{u, u, u} φ).map v) ≫ leftProjectionMap φ K L' =
      leftProjectionMap φ K L ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} φ).map
          ((mapCochainComplex φ).obj K ◁ v) := by
  have h := restrictScalarsLaxTensor_naturality φ (𝟙 ((mapCochainComplex φ).obj K)) v
  have e : (K ◁ (CochainComplex.restrictScalarsLarge.{u, u, u} φ).map v) ≫
      ((extendRestrictScalarsComplexAdj φ).unit.app K ⊗ₘ
        𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L')) =
      ((extendRestrictScalarsComplexAdj φ).unit.app K ⊗ₘ
        𝟙 ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj L)) ≫
        ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).map
            (𝟙 ((mapCochainComplex φ).obj K)) ⊗ₘ
          (CochainComplex.restrictScalarsLarge.{u, u, u} φ).map v) := by
    rw [CategoryTheory.Functor.map_id, ← id_tensorHom, tensorHom_comp_tensorHom,
      tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    exact congrArg (· ⊗ₘ _) (Category.comp_id _).symm
  rw [leftProjectionMap, leftProjectionMap, Category.assoc, reassoc_of% e, h, id_tensorHom]

/-- **The projection map on a tensor product.** The projection map of `E ⊗_A P`, followed by the
inverse monoidality comparison, is the projection map of `P` tensored with `E`, followed by the
projection map of `E` and the associator. -/
theorem leftProjectionMap_tensor (E P : CochainComplex (ModuleCat.{u} A) ℤ)
    (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    leftProjectionMap φ (E ⊗ P) Z ≫
        (CochainComplex.restrictScalarsLarge.{u, u, u} φ).map
          ((extendScalarsMonoidalIso φ E P).inv ▷ Z) =
      (α_ E P ((CochainComplex.restrictScalarsLarge.{u, u, u} φ).obj Z)).hom ≫
        (E ◁ leftProjectionMap φ P Z) ≫ leftProjectionMap φ E ((mapCochainComplex φ).obj P ⊗ Z) ≫
          (CochainComplex.restrictScalarsLarge.{u, u, u} φ).map
            (α_ ((mapCochainComplex φ).obj E) ((mapCochainComplex φ).obj P) Z).inv := by
  let res := CochainComplex.restrictScalarsLarge.{u, u, u} φ
  let ext := mapCochainComplex φ
  let ηE := (extendRestrictScalarsComplexAdj φ).unit.app E
  let ηP := (extendRestrictScalarsComplexAdj φ).unit.app P
  let ηEP := (extendRestrictScalarsComplexAdj φ).unit.app (E ⊗ P)
  let μ := extendScalarsMonoidalIso φ E P
  let ρ := restrictScalarsLaxTensor φ
  have h1 : (res.map μ.inv ▷ res.obj Z) ≫ ρ (ext.obj E ⊗ ext.obj P) Z =
      ρ (ext.obj (E ⊗ P)) Z ≫ res.map (μ.inv ▷ Z) := by
    have h := restrictScalarsLaxTensor_naturality φ μ.inv (𝟙 Z)
    rw [CategoryTheory.Functor.map_id, tensorHom_id, tensorHom_id] at h
    exact h
  have h2 : (ηE ⊗ₘ ηP) ≫ ρ (ext.obj E) (ext.obj P) = ηEP ≫ res.map μ.inv :=
    unit_tensorHom_comp_restrictScalarsLaxTensor_eq φ E P
  have h3 : (ρ (ext.obj E) (ext.obj P) ▷ res.obj Z) ≫ ρ (ext.obj E ⊗ ext.obj P) Z =
      (α_ (res.obj (ext.obj E)) (res.obj (ext.obj P)) (res.obj Z)).hom ≫
        (res.obj (ext.obj E) ◁ ρ (ext.obj P) Z) ≫ ρ (ext.obj E) (ext.obj P ⊗ Z) ≫
          res.map (α_ (ext.obj E) (ext.obj P) Z).inv := by
    have h := restrictScalarsLaxTensor_associativity φ (ext.obj E) (ext.obj P) Z
    rw [tensorHom_id, id_tensorHom] at h
    rw [← reassoc_of% h, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have h4 : ((ηE ⊗ₘ ηP) ▷ res.obj Z) ≫
        (α_ (res.obj (ext.obj E)) (res.obj (ext.obj P)) (res.obj Z)).hom =
      (α_ E P (res.obj Z)).hom ≫ (ηE ⊗ₘ (ηP ▷ res.obj Z)) := by
    have h := associator_naturality ηE ηP (𝟙 (res.obj Z))
    rw [tensorHom_id, tensorHom_id] at h
    exact h
  have h5 : (E ◁ ((ηP ▷ res.obj Z) ≫ ρ (ext.obj P) Z)) ≫ (ηE ▷ res.obj (ext.obj P ⊗ Z)) =
      (ηE ⊗ₘ (ηP ▷ res.obj Z)) ≫ (res.obj (ext.obj E) ◁ ρ (ext.obj P) Z) := by
    rw [whiskerLeft_comp, Category.assoc, whisker_exchange, ← Category.assoc,
      ← tensorHom_def']
    rfl
  have hL : leftProjectionMap φ (E ⊗ P) Z ≫ res.map (μ.inv ▷ Z) =
      (ηEP ▷ res.obj Z) ≫ ρ (ext.obj (E ⊗ P)) Z ≫ res.map (μ.inv ▷ Z) := by
    rw [leftProjectionMap, tensorHom_id, Category.assoc]
  have hR : (α_ E P (res.obj Z)).hom ≫ (E ◁ leftProjectionMap φ P Z) ≫
        leftProjectionMap φ E (ext.obj P ⊗ Z) ≫ res.map (α_ (ext.obj E) (ext.obj P) Z).inv =
      (α_ E P (res.obj Z)).hom ≫ (E ◁ ((ηP ▷ res.obj Z) ≫ ρ (ext.obj P) Z)) ≫
        (ηE ▷ res.obj (ext.obj P ⊗ Z)) ≫ ρ (ext.obj E) (ext.obj P ⊗ Z) ≫
          res.map (α_ (ext.obj E) (ext.obj P) Z).inv := by
    rw [leftProjectionMap, leftProjectionMap, tensorHom_id, tensorHom_id, Category.assoc]
  rw [hL, hR, ← h1]
  rw [← reassoc_of% (comp_whiskerRight ηEP (res.map μ.inv) (res.obj Z))]
  refine (congrArg (· ≫ ρ (ext.obj E ⊗ ext.obj P) Z) (congrArg (· ▷ res.obj Z) h2.symm)).trans ?_
  rw [comp_whiskerRight, Category.assoc, h3, reassoc_of% h4, reassoc_of% h5]

end Complexes

end CochainComplex.ExtendScalars

end
