module

public import StacksFrontier.CategoryTheory.GradedObject.MonoidalFunctorDuality
public import StacksFrontier.CategoryTheory.GradedObject.TotalTensor

/-!
# Monoidal functors into graded vector spaces: the Künneth formula

Let `G : D ⥤ GradedObject ℤ (ModuleCat F)` be a monoidal functor into `ℤ`-graded `F`-vector
spaces (Stacks, Homology, Example 0FFX). This file proves that for monoid objects `M`, `N`, `P`
and morphisms `i₁ : M ⟶ P`, `i₂ : N ⟶ P` such that `(i₁ ⊗ i₂) ≫ μ_P : M ⊗ N ⟶ P` is an
isomorphism, the map `(⨁ G(M)ⁱ) ⊗ (⨁ G(N)ʲ) → ⨁ G(P)ⁿ`, `a ⊗ b ↦ G(i₁)(a) · G(i₂)(b)` is
bijective. For the motive `P = h(X × Y)` with `i₁ = h(pr₁)`, `i₂ = h(pr₂)` this is the Künneth map
`a ⊗ b ↦ pr₁^*a ∪ pr₂^*b`.

## Main definitions

* `CategoryTheory.GradedObject.Monoidal.totalEquiv`: the isomorphism `⨁ Vⁿ ≅ ⨁ Wⁿ` induced by an
  isomorphism `V ≅ W` of graded vector spaces.

## Main results

* `CategoryTheory.Functor.map_tensorHom_gradedMul`: naturality of the product.
* `CategoryTheory.Functor.gradedMonMul_map_map`: `G(i₁)(a) · G(i₂)(b) = G((i₁ ⊗ i₂) ≫ μ)(a ⊗ b)`.
* `CategoryTheory.Functor.bijective_of_gradedMonMul_map_map`: the Künneth bijection.
* `CategoryTheory.Functor.map_tensorμ_gradedMul`: the interchange law, with its Koszul sign.
* `CategoryTheory.Functor.gradedTrace_gradedMonMul_map_map`: the Künneth formula for traces.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

open MonoidalCategory GradedObject GradedObject.Monoidal Limits DirectSum
open scoped TensorProduct

universe w

variable {D : Type*} [Category D] [MonoidalCategory D] {F : Type w} [Field F]
  {G : D ⥤ GradedObject ℤ (ModuleCat.{w} F)}

section Lax

variable [G.LaxMonoidal]

/-- Naturality of the product of a lax monoidal functor. -/
lemma map_tensorHom_gradedMul {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') (i j k : ℤ)
    (h : i + j = k) (x : G.obj X i) (y : G.obj Y j) :
    G.map (f ⊗ₘ g) k (gradedMul G X Y i j k h x y) =
      gradedMul G X' Y' i j k h (G.map f i x) (G.map g j y) := by
  rw [MonoidalCategory.tensorHom_def, G.map_comp, categoryOfGradedObjects_comp,
    ConcreteCategory.comp_apply, map_whiskerRight_gradedMul, map_whiskerLeft_gradedMul]

/-- **`G(i₁)(a) · G(i₂)(b) = G((i₁ ⊗ i₂) ≫ μ)(a ⊗ b)`** in the monoid object `G(P)`. -/
lemma gradedMonMul_map_map {M N P : D} [MonObj P] (i₁ : M ⟶ P) (i₂ : N ⟶ P) (i j k : ℤ)
    (h : i + j = k) (a : G.obj M i) (b : G.obj N j) :
    gradedMonMul G P i j k h (G.map i₁ i a) (G.map i₂ j b) =
      G.map ((i₁ ⊗ₘ i₂) ≫ MonObj.mul) k (gradedMul G M N i j k h a b) := by
  rw [gradedMonMul_apply, G.map_comp, categoryOfGradedObjects_comp, ConcreteCategory.comp_apply,
    map_tensorHom_gradedMul]

/-- **Products of elements of the form `G(u)(e₁)`**: if `(u ⊗ v) ≫ μ = ψ ≫ w` for
`u : T₁ ⟶ M`, `v : T₂ ⟶ M`, `w : T₃ ⟶ M`, `ψ : T₁ ⊗ T₂ ⟶ T₃`, and `e₃ = G(ψ)(e₁ · e₂)`, then
`G(u)(e₁) · G(v)(e₂) = G(w)(e₃)` in the monoid object `G(M)`. -/
lemma gradedMonMul_map_map_eq_map {M T₁ T₂ T₃ : D} [MonObj M] (u : T₁ ⟶ M) (v : T₂ ⟶ M)
    (w : T₃ ⟶ M) (ψ : T₁ ⊗ T₂ ⟶ T₃) (hw : (u ⊗ₘ v) ≫ MonObj.mul = ψ ≫ w) {i j k : ℤ}
    (h : i + j = k) (e₁ : G.obj T₁ i) (e₂ : G.obj T₂ j) (e₃ : G.obj T₃ k)
    (he : e₃ = G.map ψ k (gradedMul G T₁ T₂ i j k h e₁ e₂)) :
    gradedMonMul G M i j k h (G.map u i e₁) (G.map v j e₂) = G.map w k e₃ := by
  rw [gradedMonMul_map_map, hw, G.map_comp, categoryOfGradedObjects_comp,
    ConcreteCategory.comp_apply, he]

end Lax

/-- The isomorphism `⨁ G(X)ⁿ ≅ ⨁ G(Y)ⁿ` of total spaces induced by an isomorphism of graded
vector spaces. -/
def _root_.CategoryTheory.GradedObject.Monoidal.totalEquiv
    {V W : GradedObject ℤ (ModuleCat.{w} F)} (e : V ≅ W) : (⨁ n, V n) ≃ₗ[F] ⨁ n, W n :=
  DFinsupp.mapRange.linearEquiv fun n ↦ (Pi.isoApp e n).toLinearEquiv

/-- `totalEquiv e` sends `x` in the summand `Vⁿ` to `e x` in the summand `Wⁿ`. -/
theorem _root_.CategoryTheory.GradedObject.Monoidal.totalEquiv_lof
    {V W : GradedObject ℤ (ModuleCat.{w} F)} (e : V ≅ W) (n : ℤ) (x : V n) :
    totalEquiv e (lof F ℤ (fun n ↦ V n) n x) = lof F ℤ (fun n ↦ W n) n (e.hom n x) :=
  DFinsupp.mapRange_single (hf := fun _ ↦ map_zero _)

section Monoidal

variable [G.Monoidal]

/-- **The Künneth bijection for a monoidal functor.** Let `M`, `N`, `P` be objects, `P` a monoid
object, and `i₁ : M ⟶ P`, `i₂ : N ⟶ P` morphisms such that `(i₁ ⊗ i₂) ≫ μ_P : M ⊗ N ⟶ P` is an
isomorphism. Then a linear map `(⨁ G(M)ⁱ) ⊗ (⨁ G(N)ʲ) → ⨁ G(P)ⁿ` sending `a ⊗ b` to
`G(i₁)(a) · G(i₂)(b)` for homogeneous `a`, `b` is bijective. -/
theorem bijective_of_gradedMonMul_map_map {M N P : D} [MonObj P] (i₁ : M ⟶ P) (i₂ : N ⟶ P)
    [IsIso ((i₁ ⊗ₘ i₂) ≫ MonObj.mul)]
    (κ : (⨁ i, G.obj M i) ⊗[F] (⨁ j, G.obj N j) →ₗ[F] ⨁ n, G.obj P n)
    (hκ : ∀ (i j : ℤ) (a : G.obj M i) (b : G.obj N j),
      κ (lof F ℤ (fun i ↦ G.obj M i) i a ⊗ₜ lof F ℤ (fun j ↦ G.obj N j) j b) =
        lof F ℤ (fun n ↦ G.obj P n) (i + j)
          (gradedMonMul G P i j (i + j) rfl (G.map i₁ i a) (G.map i₂ j b))) :
    Function.Bijective κ := by
  let e : (⨁ i, G.obj M i) ⊗[F] (⨁ j, G.obj N j) ≃ₗ[F] ⨁ n, G.obj P n :=
    (totalTensorEquiv (G.obj M) (G.obj N)).trans
      ((totalEquiv (Monoidal.μIso G M N)).trans
        (totalEquiv (G.mapIso (asIso ((i₁ ⊗ₘ i₂) ≫ MonObj.mul)))))
  have : κ = e.toLinearMap := by
    refine TensorProduct.ext (linearMap_ext F fun i ↦ LinearMap.ext fun a ↦
      linearMap_ext F fun j ↦ LinearMap.ext fun b ↦ ?_)
    show κ (lof F ℤ (fun i ↦ G.obj M i) i a ⊗ₜ lof F ℤ (fun j ↦ G.obj N j) j b) =
      e (lof F ℤ (fun i ↦ G.obj M i) i a ⊗ₜ lof F ℤ (fun j ↦ G.obj N j) j b)
    rw [hκ, gradedMonMul_map_map]
    simp only [e, LinearEquiv.trans_apply, totalTensorEquiv_tmul, totalEquiv_lof]
    rfl
  rw [this]
  exact e.bijective

/-! ### The counit -/

/-- `G(𝟙)` vanishes outside degree `0`. -/
theorem isZero_unit_apply {p : ℤ} (hp : p ≠ 0) : IsZero (G.obj (𝟙_ D) p) :=
  ((isInitialTensorUnitApply (C := ModuleCat.{w} F) p hp).isZero).of_iso
    (Pi.isoApp (Monoidal.εIso G).symm p)

/-- `G(𝟙)⁰` is spanned by the unit `1`, with coordinate the counit. -/
theorem eq_gradedCounit_smul_gradedOne (u : G.obj (𝟙_ D) 0) :
    u = G.gradedCounit u • gradedOne G := by
  have h := congr($(Monoidal.η_ε (F := G)) 0)
  simp only [categoryOfGradedObjects_comp, categoryOfGradedObjects_id] at h
  conv_lhs => rw [← ModuleCat.id_apply (G.obj (𝟙_ D) 0) u, ← h, ConcreteCategory.comp_apply]
  rw [gradedOne, ← (LaxMonoidal.ε G 0).hom.map_smul]
  congr 1
  apply (tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} F)).toLinearEquiv.injective
  show (tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} F)).hom ((OplaxMonoidal.η G 0) u) =
    (tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} F)).hom
      (G.gradedCounit u • (tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} F)).inv (1 : F))
  rw [_root_.map_smul, Iso.inv_hom_id_apply]
  show _ = G.gradedCounit u * 1
  rw [mul_one]
  rfl

/-- **The counit is multiplicative**: `η(u ⊗ v) = η(u) η(v)` on `G(𝟙)⁰ ⊗ G(𝟙)⁰`, through
`𝟙 ⊗ 𝟙 ≅ 𝟙`. -/
theorem gradedCounit_map_leftUnitor_gradedMul (u v : G.obj (𝟙_ D) 0) :
    G.gradedCounit (G.map (λ_ (𝟙_ D)).hom 0 (gradedMul G (𝟙_ D) (𝟙_ D) 0 0 0 (add_zero 0) u v)) =
      G.gradedCounit u * G.gradedCounit v := by
  conv_lhs => rw [eq_gradedCounit_smul_gradedOne u]
  rw [LinearMap.map_smul₂, (G.map (λ_ (𝟙_ D)).hom 0).hom.map_smul, map_leftUnitor_gradedMul,
    _root_.map_smul, smul_eq_mul]

end Monoidal

/-! ### Braided functors: the interchange law -/

section Braided

variable [BraidedCategory D]
  [@Functor.Braided D _ _ _ (GradedObject ℤ (ModuleCat.{w} F)) _ _ koszulBraidedCategory G]

/-- **The interchange law on elements**: `(a ⊗ b) ⊗ (c ⊗ d) ↦ (-1)^{|b||c|} (a ⊗ c) ⊗ (b ⊗ d)`. -/
lemma map_tensorμ_gradedMul (X₁ X₂ Y₁ Y₂ : D) (i₁ i₂ j₁ j₂ i j k l n : ℤ) (hi : i₁ + i₂ = i)
    (hj : j₁ + j₂ = j) (hk : i₁ + j₁ = k) (hl : i₂ + j₂ = l) (h : i + j = n) (h' : k + l = n)
    (a : G.obj X₁ i₁) (b : G.obj X₂ i₂) (c : G.obj Y₁ j₁) (d : G.obj Y₂ j₂) :
    G.map (tensorμ X₁ X₂ Y₁ Y₂) n
        (gradedMul G _ _ i j n h (gradedMul G X₁ X₂ i₁ i₂ i hi a b)
          (gradedMul G Y₁ Y₂ j₁ j₂ j hj c d)) =
      (i₂ * j₁).negOnePow • gradedMul G _ _ k l n h'
        (gradedMul G X₁ Y₁ i₁ j₁ k hk a c) (gradedMul G X₂ Y₂ i₂ j₂ l hl b d) := by
  simp only [tensorμ, G.map_comp, categoryOfGradedObjects_comp, ConcreteCategory.comp_apply]
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul F,
    map_associator_gradedMul' X₁ X₂ (Y₁ ⊗ Y₂) i₁ i₂ j i (i₂ + j) n hi rfl h (by omega),
    map_whiskerLeft_gradedMul,
    map_associator_inv_gradedMul' X₂ Y₁ Y₂ i₂ j₁ j₂ (i₂ + j₁) j (i₂ + j) rfl hj (by omega)
      (by omega),
    map_whiskerLeft_gradedMul, map_whiskerRight_gradedMul,
    map_braiding_gradedMul G X₂ Y₁ i₂ j₁ (i₂ + j₁) rfl (by omega), Units.smul_def,
    ← Int.cast_smul_eq_zsmul F, LinearMap.map_smul₂, _root_.map_smul,
    _root_.map_smul, map_whiskerLeft_gradedMul,
    map_associator_gradedMul' Y₁ X₂ Y₂ j₁ i₂ j₂ (i₂ + j₁) l (i₂ + j) (by omega) hl (by omega)
      (by omega),
    _root_.map_smul,
    map_associator_inv_gradedMul' X₁ Y₁ (X₂ ⊗ Y₂) i₁ j₁ l k (i₂ + j) n hk (by omega) h'
      (by omega)]

/-- **The Künneth formula for traces.** Let `i₁ : M ⟶ P`, `i₂ : N ⟶ P` with `P` a monoid object,
`ψ : T_M ⊗ T_N ⟶ T_P` with `e_P = ψ(e_M ⊗ e_N)`, and `t_M : M ⊗ T_M ⟶ 𝟙`, `t_N`, `t_P` with
`((i₁ ⊗ i₂) ≫ μ_P) ⊗ ψ ≫ t_P = (t_M ⊗ t_N)` up to the interchange and `𝟙 ⊗ 𝟙 ≅ 𝟙`. If the degree
`s_M` of `e_M` is even, then `t_P(G(i₁)a · G(i₂)b ⊗ e_P) = t_M(a ⊗ e_M) · t_N(b ⊗ e_N)` for `a`,
`b` in the degrees complementary to `s_M`, `s_N`, and `t_P(G(i₁)a · G(i₂)b ⊗ e_P) = 0` for `a` in
any other degree. -/
theorem gradedTrace_gradedMonMul_map_map {M N P T_M T_N T_P : D} [MonObj P] (i₁ : M ⟶ P)
    (i₂ : N ⟶ P) (ψ : T_M ⊗ T_N ⟶ T_P) (t_M : M ⊗ T_M ⟶ 𝟙_ D) (t_N : N ⊗ T_N ⟶ 𝟙_ D)
    (t_P : P ⊗ T_P ⟶ 𝟙_ D)
    (ht : (((i₁ ⊗ₘ i₂) ≫ MonObj.mul) ⊗ₘ ψ) ≫ t_P =
      tensorμ M N T_M T_N ≫ (t_M ⊗ₘ t_N) ≫ (λ_ (𝟙_ D)).hom)
    {s_M s_N s_P : ℤ} (hs : Even s_M) (hsP : s_M + s_N = s_P) (e_M : G.obj T_M s_M)
    (e_N : G.obj T_N s_N) (e_P : G.obj T_P s_P)
    (he : e_P = G.map ψ s_P (gradedMul G T_M T_N s_M s_N s_P hsP e_M e_N))
    (i j m : ℤ) (hij : i + j = m) (hm : m + s_P = 0) (a : G.obj M i) (b : G.obj N j) :
    G.gradedTrace t_P e_P m hm (gradedMonMul G P i j m hij (G.map i₁ i a) (G.map i₂ j b)) =
      if hi : i + s_M = 0 then
        G.gradedTrace t_M e_M i hi a * G.gradedTrace t_N e_N j (by omega) b
      else 0 := by
  rw [gradedTrace_apply, gradedMonMul_map_map, he, ← map_tensorHom_gradedMul, ←
    ConcreteCategory.comp_apply, ← categoryOfGradedObjects_comp, ← G.map_comp, ht]
  simp only [G.map_comp, categoryOfGradedObjects_comp, ConcreteCategory.comp_apply]
  split_ifs with hi
  · rw [map_tensorμ_gradedMul M N T_M T_N i j s_M s_N m s_P 0 0 0 hij hsP hi (by omega) hm
        (add_zero 0), Int.negOnePow_even _ (hs.mul_left j), one_smul, map_tensorHom_gradedMul,
      gradedCounit_map_leftUnitor_gradedMul]
    rfl
  · rw [map_tensorμ_gradedMul M N T_M T_N i j s_M s_N m s_P (i + s_M) (j + s_N) 0 hij hsP rfl rfl
        hm (by omega), Int.negOnePow_even _ (hs.mul_left j), one_smul, map_tensorHom_gradedMul]
    have : Subsingleton (G.obj (𝟙_ D) (i + s_M)) :=
      ModuleCat.isZero_iff_subsingleton.1 (isZero_unit_apply hi)
    rw [Subsingleton.elim (G.map t_M (i + s_M) _) 0, LinearMap.map_zero₂, _root_.map_zero,
      _root_.map_zero]

end Braided

end CategoryTheory.Functor

end
