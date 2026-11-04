module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon
public import StacksFrontier.CategoryTheory.GradedObject.InvertibleGradedVectorSpace
public import StacksFrontier.CategoryTheory.GradedObject.KoszulBraiding
public import StacksFrontier.CategoryTheory.GradedObject.MonoidalFunctorElements
public import StacksFrontier.CategoryTheory.Monoidal.Rigid

/-!
# Monoidal functors into graded vector spaces: twists and duality

Let `G : D ⥤ GradedObject ℤ (ModuleCat F)` be a monoidal functor into `ℤ`-graded `F`-vector
spaces (Stacks, Homology, Example 0FFX). This file proves Poincaré duality for `G(X)`, from the
duality of `X` in `D` and Stacks 0FFV.

* If `G(T)` is one dimensional, concentrated in degree `s` and spanned by `e`, then
  `x ↦ x ⊗ e` is an isomorphism `G(X)ᵖ ≅ G(X ⊗ T)^{p+s}` (`Functor.bijective_gradedMul_right`).
* A left dual `Y` of `X` gives perfect pairings `G(Y)⁻ⁿ × G(X)ⁿ → F`, `(w, v) ↦ ε(w ⊗ v)`, by
  `ExactPairing.map` and Stacks 0FFV (`Functor.isPerfPair_gradedPairing_map`).
* If `M` is a monoid object whose left dual is `M ⊗ T`, with evaluation
  `(M ⊗ T) ⊗ M ≅ (M ⊗ M) ⊗ T ⟶ M ⊗ T ⟶ 𝟙` built from the multiplication of `M` and a morphism
  `t : M ⊗ T ⟶ 𝟙`, then the pairings `G(M)ᵖ × G(M)^q → F`, `(a, b) ↦ ∫(a b)` with
  `∫ x = t(x ⊗ e)`, are perfect for `p + q + s = 0`, and every `G(M)ⁿ` is finite dimensional
  (`Functor.isPerfPair_gradedTrace_gradedMonMul`).

## Main definitions

* `CategoryTheory.Functor.gradedCounit`: `G(𝟙)⁰ → F`, through the inverse of `ε`.
* `CategoryTheory.Functor.gradedMonMul`: its multiplication `G(M)ᵖ × G(M)^q → G(M)^{p+q}`.
* `CategoryTheory.Functor.gradedTrace`: `x ↦ t(x ⊗ e)`, for `t : M ⊗ T ⟶ 𝟙`.

## Main results

* `CategoryTheory.Functor.bijective_gradedMul_right`: `x ↦ x ⊗ e` is a bijection
  `G(X)ᵖ → G(X ⊗ T)^{p+s}`.
* `CategoryTheory.Functor.isPerfPair_gradedTrace_gradedMonMul`: the pairing `(a, b) ↦ t(a b ⊗ e)`
  on `G(M)ᵖ × G(M)^q` is perfect for `p + q + s = 0`.
* `CategoryTheory.Functor.finiteDimensional_of_exactPairing`: an object with a left dual has
  finite dimensional realization in every degree.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

open MonoidalCategory GradedObject GradedObject.Monoidal Limits
open scoped TensorProduct

universe w

variable {D : Type*} [Category D] [MonoidalCategory D] {F : Type w} [Field F]
  (G : D ⥤ GradedObject ℤ (ModuleCat.{w} F))

/-! ### Products in arbitrary degrees -/

section Lax

variable [G.LaxMonoidal] {G}

/-- Associativity of the product of a lax monoidal functor, with arbitrary intermediate
degrees. -/
lemma map_associator_gradedMul' (X Y Z : D) (i j l ij jl k : ℤ) (hij : i + j = ij)
    (hjl : j + l = jl) (h : ij + l = k) (h' : i + jl = k) (x : G.obj X i) (y : G.obj Y j)
    (z : G.obj Z l) :
    G.map (α_ X Y Z).hom k (gradedMul G (X ⊗ Y) Z ij l k h (gradedMul G X Y i j ij hij x y) z) =
      gradedMul G X (Y ⊗ Z) i jl k h' x (gradedMul G Y Z j l jl hjl y z) := by
  subst hij hjl
  exact map_associator_gradedMul X Y Z i j l k h x y z

/-- The inverse associator on products. -/
lemma map_associator_inv_gradedMul' (X Y Z : D) (i j l ij jl k : ℤ) (hij : i + j = ij)
    (hjl : j + l = jl) (h : ij + l = k) (h' : i + jl = k) (x : G.obj X i) (y : G.obj Y j)
    (z : G.obj Z l) :
    G.map (α_ X Y Z).inv k (gradedMul G X (Y ⊗ Z) i jl k h' x (gradedMul G Y Z j l jl hjl y z)) =
      gradedMul G (X ⊗ Y) Z ij l k h (gradedMul G X Y i j ij hij x y) z := by
  rw [← map_associator_gradedMul' X Y Z i j l ij jl k hij hjl h h' x y z,
    ← ConcreteCategory.comp_apply, ← categoryOfGradedObjects_comp, ← G.map_comp,
    Iso.hom_inv_id, G.map_id]
  rfl

end Lax

/-! ### The counit -/

section Monoidal

variable [G.Monoidal]

/-- The linear form `G(𝟙)⁰ → F` given by the inverse `η` of the unit `ε : 𝟏 ≅ G(𝟙)`. -/
def gradedCounit : G.obj (𝟙_ D) 0 →ₗ[F] F :=
  ((OplaxMonoidal.η G) 0 ≫ (tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} F)).hom).hom

/-- The counit `gradedCounit` sends the unit element `gradedOne G` of `G(𝟙)⁰` to `1`. -/
theorem gradedCounit_gradedOne : G.gradedCounit (gradedOne G) = 1 := by
  have h := congr($(Monoidal.ε_η (F := G)) 0)
  simp only [categoryOfGradedObjects_comp, categoryOfGradedObjects_id] at h
  show ((tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} F)).hom)
      ((OplaxMonoidal.η G 0) ((LaxMonoidal.ε G 0)
        ((tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} F)).inv (1 : F)))) = 1
  rw [← ConcreteCategory.comp_apply (LaxMonoidal.ε G 0), h, ModuleCat.id_apply,
    Iso.inv_hom_id_apply]

/-! ### Twisting by a line -/

variable {G}

/-- If `W` is zero outside degree `s`, every element of `(V ⊗ W)ⁿ` comes from the summand
`V^{n-s} ⊗ Wˢ`. -/
lemma surjective_ιTensorObj_of_isZero (V W : GradedObject ℤ (ModuleCat.{w} F)) {s : ℤ}
    (hW : ∀ i, i ≠ s → IsZero (W i)) (p n : ℤ) (h : p + s = n) :
    Function.Surjective (ιTensorObj V W p s n h).hom := by
  classical
  intro y
  rw [← sum_ι_comps V W n y]
  refine Submodule.sum_mem (LinearMap.range (ιTensorObj V W p s n h).hom) fun a _ ↦ ?_
  obtain ⟨⟨a₁, a₂⟩, ha⟩ := a
  by_cases has : a₂ = s
  · subst has
    obtain rfl : a₁ = p := by simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha; omega
    exact ⟨_, rfl⟩
  · have : Subsingleton (W a₂) := (ModuleCat.isZero_iff_subsingleton.1 (hW a₂ has))
    have : comps V W n y ⟨(a₁, a₂), ha⟩ = 0 := by
      induction (comps V W n y ⟨(a₁, a₂), ha⟩) using TensorProduct.induction_on with
      | zero => rfl
      | tmul x z => rw [Subsingleton.elim z 0, TensorProduct.tmul_zero]
      | add x z hx hz => rw [hx, hz, add_zero]
    rw [this, map_zero]
    exact Submodule.zero_mem _

/-- **Twisting by a line.** If `G(T)` is one dimensional, concentrated in degree `s` and spanned
by `e`, then `x ↦ x ⊗ e` is a bijection `G(X)ᵖ → G(X ⊗ T)ⁿ` for `p + s = n`. -/
theorem bijective_gradedMul_right {T : D} {s : ℤ}
    (hT : ∀ i, i ≠ s → IsZero (G.obj T i)) {e : G.obj T s} (he : e ≠ 0)
    (hrank : Module.finrank F (G.obj T s) = 1) (X : D) (p n : ℤ) (h : p + s = n) :
    Function.Bijective (fun x ↦ gradedMul G X T p s n h x e) := by
  have hμ : Function.Bijective ((LaxMonoidal.μ G X T) n).hom :=
    ((Pi.isoApp (Monoidal.μIso G X T) n).toLinearEquiv).bijective
  let ee : F ≃ₗ[F] G.obj T s := LinearEquiv.ofBijective (LinearMap.toSpanSingleton F _ e)
    ⟨fun a b hab ↦ smul_left_injective F he hab, (finrank_eq_one_iff_of_nonzero' e he).1 hrank⟩
  let te : G.obj X p ≃ₗ[F] G.obj X p ⊗[F] G.obj T s :=
    (TensorProduct.rid F _).symm.trans (TensorProduct.congr (LinearEquiv.refl F _) ee)
  have hte : ∀ x, te x = x ⊗ₜ[F] e := fun x ↦ by
    simp only [te, LinearEquiv.trans_apply, TensorProduct.rid_symm_apply, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply]
    exact congrArg (x ⊗ₜ[F] ·) (one_smul F e)
  have hι : Function.Bijective (ιTensorObj (G.obj X) (G.obj T) p s n h).hom :=
    ⟨ιTensorObj_injective _ _ p s n h, surjective_ιTensorObj_of_isZero _ _ hT p n h⟩
  have : (fun x ↦ gradedMul G X T p s n h x e) =
      ((LaxMonoidal.μ G X T) n).hom ∘ (ιTensorObj (G.obj X) (G.obj T) p s n h).hom ∘ te := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, hte]
    rfl
  rw [this]
  exact hμ.comp (hι.comp te.bijective)

end Monoidal

/-! ### Monoid objects -/

section Mon

variable [G.LaxMonoidal]

/-- The product `G(M)ᵖ × G(M)^q → G(M)ⁿ`, `p + q = n`, of the monoid object `G(M)`. -/
def gradedMonMul (M : D) [MonObj M] (p q n : ℤ) (h : p + q = n) :
    G.obj M p →ₗ[F] G.obj M q →ₗ[F] G.obj M n :=
  (gradedMul G M M p q n h).compr₂ (G.map MonObj.mul n).hom

/-- `gradedMonMul G M p q n h a b` is the image of `a ⊗ b` under `G` of the multiplication of
`M`. -/
theorem gradedMonMul_apply (M : D) [MonObj M] (p q n : ℤ) (h : p + q = n) (a : G.obj M p)
    (b : G.obj M q) :
    gradedMonMul G M p q n h a b = G.map MonObj.mul n (gradedMul G M M p q n h a b) :=
  rfl

/-- `gradedMonMul` is the multiplication of the monoid object `G(M)` of Mathlib's
`CategoryTheory.Functor.monObjObj` on the summand
`G(M)ᵖ ⊗ G(M)^q`. -/
theorem gradedMonMul_eq (M : D) [MonObj M] (p q n : ℤ) (h : p + q = n) (a : G.obj M p)
    (b : G.obj M q) :
    gradedMonMul G M p q n h a b =
      (ιTensorObj (G.obj M) (G.obj M) p q n h ≫ (monObjObj (F := G) M).mul n) (a ⊗ₜ b) :=
  rfl

end Mon

/-! ### The trace -/

section Trace

variable [G.Monoidal]

/-- **The trace `x ↦ t(x ⊗ e)`** on `G(M)ᵐ` defined by a morphism `t : M ⊗ T ⟶ 𝟙` and an element
`e ∈ G(T)ˢ`, `m + s = 0`. -/
def gradedTrace {M T : D} (t : M ⊗ T ⟶ 𝟙_ D) {s : ℤ} (e : G.obj T s) (m : ℤ) (h : m + s = 0) :
    G.obj M m →ₗ[F] F :=
  G.gradedCounit ∘ₗ (G.map t 0).hom ∘ₗ (gradedMul G M T m s 0 h).flip e

/-- `gradedTrace t e m h x` is `gradedCounit` applied to `t(x ⊗ e)`. -/
theorem gradedTrace_apply {M T : D} (t : M ⊗ T ⟶ 𝟙_ D) {s : ℤ} (e : G.obj T s) (m : ℤ)
    (h : m + s = 0) (x : G.obj M m) :
    G.gradedTrace t e m h x = G.gradedCounit (G.map t 0 (gradedMul G M T m s 0 h x e)) :=
  rfl

end Trace

/-! ### Braided functors -/

section Braided

variable [BraidedCategory D]
  [@Functor.Braided D _ _ _ (GradedObject ℤ (ModuleCat.{w} F)) _ _ koszulBraidedCategory G]

/-- **The Koszul sign rule for a braided functor**: `β(x ⊗ y) = (-1)^{ij} y ⊗ x`. -/
lemma map_braiding_gradedMul (X Y : D) (i j k : ℤ) (h : i + j = k) (h' : j + i = k)
    (x : G.obj X i) (y : G.obj Y j) :
    G.map (β_ X Y).hom k (gradedMul G X Y i j k h x y) =
      (i * j).negOnePow • gradedMul G Y X j i k h' y x := by
  have H := ConcreteCategory.congr_hom
    (ιTensorObj (G.obj X) (G.obj Y) i j k h ≫=
      congr($(@Functor.Braided.braided _ _ _ _ _ _ _ koszulBraidedCategory G _ X Y) k))
    (x ⊗ₜ y)
  simp only [categoryOfGradedObjects_comp, koszulBraidedCategory_braiding,
    ι_koszulBraiding_hom_assoc, Units.smul_def, Preadditive.zsmul_comp, ModuleCat.hom_zsmul,
    LinearMap.smul_apply, ConcreteCategory.comp_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply] at H
  exact H

/-! ### Duality -/

/-- The pairing `G(Y)⁻ⁿ × G(X)ⁿ → F` of Stacks 0FFV for the image of an exact pairing is
`(w, v) ↦ ε(w ⊗ v)`. -/
theorem gradedPairing_map (X Y : D) [ExactPairing X Y] (n : ℤ) (w : G.obj Y (-n))
    (v : G.obj X n) :
    letI := ExactPairing.map G X Y
    gradedPairing (G.obj X) (G.obj Y) n w v =
      G.gradedCounit (G.map (ε_ X Y) 0 (gradedMul G Y X (-n) n 0 (neg_add_cancel n) w v)) :=
  rfl

/-- **Poincaré duality for a realization.** Let `M` be a monoid object with left dual `M ⊗ T`,
whose evaluation `(M ⊗ T) ⊗ M ≅ (M ⊗ M) ⊗ T ⟶ M ⊗ T ⟶ 𝟙` is the multiplication of `M` followed
by a morphism `t : M ⊗ T ⟶ 𝟙`. Let `G(T)` be one dimensional, concentrated in an even degree
`s` and spanned by `e`. Then for `p + q + s = 0` the pairing `G(M)ᵖ × G(M)^q → F`,
`(a, b) ↦ t(a b ⊗ e)`, is perfect. -/
theorem isPerfPair_gradedTrace_gradedMonMul (M T : D) [MonObj M] [ExactPairing M (M ⊗ T)]
    (t : M ⊗ T ⟶ 𝟙_ D)
    (hε : ε_ M (M ⊗ T) =
      (α_ M T M).hom ≫ M ◁ (β_ T M).hom ≫ (α_ M M T).inv ≫ MonObj.mul ▷ T ≫ t)
    {s : ℤ} (hs : Even s) (hT : ∀ i, i ≠ s → IsZero (G.obj T i)) {e : G.obj T s} (he : e ≠ 0)
    (hrank : Module.finrank F (G.obj T s) = 1) (p q m : ℤ) (hpq : p + q = m) (hm : m + s = 0) :
    ((gradedMonMul G M p q m hpq).compr₂ (G.gradedTrace t e m hm)).IsPerfPair := by
  let := ExactPairing.map G M (M ⊗ T)
  have hP := (finiteDimensional_and_isPerfPair_of_exactPairing (G.obj M) (G.obj (M ⊗ T))).2.2 q
  have hpsq : p + s = -q := by omega
  let φ : G.obj M p ≃ₗ[F] G.obj (M ⊗ T) (-q) := LinearEquiv.ofBijective
    ((gradedMul G M T p s (-q) hpsq).flip e) (bijective_gradedMul_right hT he hrank M p (-q) hpsq)
  have heq : (gradedMonMul G M p q m hpq).compr₂ (G.gradedTrace t e m hm) =
      (gradedPairing (G.obj M) (G.obj (M ⊗ T)) q).compl₁₂ φ.toLinearMap
        (LinearEquiv.refl F _).toLinearMap := by
    refine LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ?_
    have hsign : (s * q).negOnePow = 1 := Int.negOnePow_even _ (hs.mul_right q)
    have hφ : φ a = gradedMul G M T p s (-q) hpsq a e := rfl
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.refl_apply,
      LinearEquiv.coe_coe, hφ, gradedPairing_map, hε, G.map_comp, categoryOfGradedObjects_comp,
      ConcreteCategory.comp_apply, gradedTrace_apply, gradedMonMul_apply]
    rw [map_associator_gradedMul' M T M p s q (-q) (s + q) 0 hpsq rfl (neg_add_cancel q)
        (by omega),
      map_whiskerLeft_gradedMul,
      map_braiding_gradedMul G T M s q (s + q) rfl (by omega), hsign, one_smul,
      map_associator_inv_gradedMul' M M T p q s m (s + q) 0 hpq (add_comm q s) hm (by omega),
      map_whiskerRight_gradedMul]
  rw [heq]
  exact LinearMap.IsPerfPair.compl₁₂ _ _ _

/-- An object with a left dual has finite dimensional realization in every degree
(Stacks 0FFV). -/
theorem finiteDimensional_of_exactPairing (X Y : D) [ExactPairing X Y] (n : ℤ) :
    FiniteDimensional F (G.obj X n) :=
  let := ExactPairing.map G X Y
  finiteDimensional_apply (G.obj X) (G.obj Y) n

end Braided

end CategoryTheory.Functor

end
