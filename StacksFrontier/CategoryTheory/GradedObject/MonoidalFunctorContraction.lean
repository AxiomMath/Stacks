module

public import StacksFrontier.CategoryTheory.GradedObject.MonoidalFunctorDuality
public import StacksFrontier.CategoryTheory.GradedObject.MonoidalFunctorKunneth
public import StacksFrontier.CategoryTheory.Monoidal.ExactPairingName

/-!
# Monoidal functors into graded vector spaces: morphisms out of a dual

Let `G : D ⥤ GradedObject ℤ (ModuleCat F)` be a monoidal functor into `ℤ`-graded `F`-vector
spaces and let `B` be a right dual of `A`. A morphism `c : B ⟶ Y` is recovered from its name
`η ≫ A ◁ c : 𝟙 ⟶ A ⊗ Y` by contracting with the counit
(`CategoryTheory.ExactPairing.eq_contract_name`). This file computes the effect on `G`: `G(c)(b)`
is the contraction `b ⊗ w ↦ ε(b ⊗ x) y` of `b` with the image `w = Σ x ⊗ y` of `1` under the
name (`CategoryTheory.Functor.map_eq_gradedContract`,
`CategoryTheory.Functor.gradedContract_gradedMul`). For a monoid object `M` whose dual is `M ⊗ T`
with counit built from the multiplication and a trace `t`, the scalar `ε((a ⊗ e) ⊗ x)` is the
trace `t(a x ⊗ e)` (`CategoryTheory.Functor.gradedCounit_map_evaluation_gradedMul`). This is the
linear algebra by which the proof of Stacks 0FHM computes the realization of a correspondence.

## Main definitions

* `CategoryTheory.Functor.gradedContract`: `G(B)ᵐ × G(A ⊗ Y)⁰ → G(Y)ᵐ`, through the counit.

## References

* [Stacks Project, Tag 0FHM](https://stacks.math.columbia.edu/tag/0FHM)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

open MonoidalCategory GradedObject GradedObject.Monoidal Limits
open scoped TensorProduct

universe w

variable {D : Type*} [Category D] [MonoidalCategory D] {F : Type w} [Field F]
  {G : D ⥤ GradedObject ℤ (ModuleCat.{w} F)}

section Monoidal

variable [G.Monoidal]

/-- **Linear maps out of `G(X ⊗ Y)ᵏ` are determined on products** `x · y`, `x ∈ G(X)ⁱ`,
`y ∈ G(Y)ʲ`, `i + j = k`. -/
theorem linearMap_ext_gradedMul {X Y : D} {k : ℤ} {V : Type w} [AddCommGroup V] [Module F V]
    {φ ψ : G.obj (X ⊗ Y) k →ₗ[F] V}
    (h : ∀ (i j : ℤ) (hij : i + j = k) (x : G.obj X i) (y : G.obj Y j),
      φ (gradedMul G X Y i j k hij x y) = ψ (gradedMul G X Y i j k hij x y)) : φ = ψ := by
  have hμ : Function.Surjective ((LaxMonoidal.μ G X Y) k).hom :=
    ((Pi.isoApp (Monoidal.μIso G X Y) k).toLinearEquiv).surjective
  have key : (LaxMonoidal.μ G X Y k ≫ ModuleCat.ofHom φ : _ ⟶ ModuleCat.of F V) =
      LaxMonoidal.μ G X Y k ≫ ModuleCat.ofHom ψ := by
    refine tensorObj_ext _ _ fun i j hij ↦ ?_
    exact ModuleCat.MonoidalCategory.tensor_ext fun x y ↦ h i j hij x y
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨u, rfl⟩ := hμ v
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom key) u

variable (G) in
/-- **The contraction** `G(B)ᵐ × G(A ⊗ Y)⁰ → G(Y)ᵐ`, `b ⊗ w ↦ (λ ∘ (ε ▷ Y) ∘ α⁻¹)(b ⊗ w)`, for
a right dual `B` of `A`. -/
def gradedContract (A B Y : D) [ExactPairing A B] (m : ℤ) :
    G.obj B m →ₗ[F] G.obj (A ⊗ Y) 0 →ₗ[F] G.obj Y m :=
  (gradedMul G B (A ⊗ Y) m 0 m (add_zero m)).compr₂
    (G.map ((α_ B A Y).inv ≫ ε_ A B ▷ Y ≫ (λ_ Y).hom) m).hom

/-- `G(ρ⁻¹)(b) = b · 1`. -/
theorem map_rightUnitor_inv (X : D) (m : ℤ) (x : G.obj X m) :
    G.map (ρ_ X).inv m x = gradedMul G X (𝟙_ D) m 0 m (add_zero m) x (gradedOne G) := by
  conv_lhs => rw [← map_rightUnitor_gradedMul X m x]
  rw [← ConcreteCategory.comp_apply, ← categoryOfGradedObjects_comp, ← G.map_comp,
    Iso.hom_inv_id, G.map_id]
  rfl

/-- **A morphism out of a dual, from its name**: `G(c)(b)` is the contraction of `b` with the
image of `1` under the name `η ≫ A ◁ c` of `c`. -/
theorem map_eq_gradedContract {A B Y : D} [ExactPairing A B] (c : B ⟶ Y) (m : ℤ)
    (b : G.obj B m) :
    G.map c m b = gradedContract G A B Y m b (G.map (η_ A B ≫ A ◁ c) 0 (gradedOne G)) := by
  conv_lhs => rw [ExactPairing.eq_contract_name (A := A) c]
  simp only [gradedContract, LinearMap.compr₂_apply, G.map_comp, categoryOfGradedObjects_comp,
    ConcreteCategory.comp_apply]
  rw [map_rightUnitor_inv, map_whiskerLeft_gradedMul, G.map_comp, categoryOfGradedObjects_comp,
    ConcreteCategory.comp_apply]

/-- The contraction of `b` with a product `x · y` is `λ (ε(b · x) · y)`. -/
private theorem gradedContract_gradedMul_eq {A B Y : D} [ExactPairing A B] {m i j p : ℤ}
    (hij : i + j = 0) (hp : m + i = p) (hj : p + j = m) (b : G.obj B m) (x : G.obj A i)
    (y : G.obj Y j) :
    gradedContract G A B Y m b (gradedMul G A Y i j 0 hij x y) =
      G.map (λ_ Y).hom m
        (gradedMul G (𝟙_ D) Y p j m hj (G.map (ε_ A B) p (gradedMul G B A m i p hp b x)) y) := by
  simp only [gradedContract, LinearMap.compr₂_apply, G.map_comp, categoryOfGradedObjects_comp,
    ConcreteCategory.comp_apply]
  rw [map_associator_inv_gradedMul' B A Y m i j p 0 m hp hij hj (add_zero m),
    map_whiskerRight_gradedMul]

/-- **The contraction with a product in matching degrees**: `b ⊗ (x · y) ↦ ε(b · x) y`. -/
theorem gradedContract_gradedMul {A B Y : D} [P : ExactPairing A B] {m i : ℤ} (hi : i + m = 0)
    (b : G.obj B m) (x : G.obj A i) (y : G.obj Y m) :
    gradedContract G A B Y m b (gradedMul G A Y i m 0 hi x y) =
      G.gradedCounit (G.map (ε_ A B) 0 (gradedMul G B A m i 0 (by omega) b x)) • y := by
  rw [gradedContract_gradedMul_eq hi (by omega) (zero_add m)]
  conv_lhs => rw [eq_gradedCounit_smul_gradedOne (G.map (ε_ A B) 0 _)]
  rw [LinearMap.map_smul₂, (G.map (λ_ Y).hom m).hom.map_smul, map_leftUnitor_gradedMul]

/-- **The contraction with a product in other degrees vanishes.** -/
theorem gradedContract_gradedMul_of_ne {A B Y : D} [P : ExactPairing A B] {m i j : ℤ}
    (hij : i + j = 0) (hj : j ≠ m) (b : G.obj B m) (x : G.obj A i) (y : G.obj Y j) :
    gradedContract G A B Y m b (gradedMul G A Y i j 0 hij x y) = 0 := by
  have hz : G.map (ε_ A B) (m + i) (gradedMul G B A m i (m + i) rfl b x) = 0 :=
    have := ModuleCat.subsingleton_of_isZero (isZero_unit_apply (G := G) (by omega : m + i ≠ 0))
    Subsingleton.elim _ _
  rw [gradedContract_gradedMul_eq hij rfl (by omega), hz, LinearMap.map_zero₂, map_zero]

end Monoidal

section Braided

variable [BraidedCategory D]
  [@Functor.Braided D _ _ _ (GradedObject ℤ (ModuleCat.{w} F)) _ _ koszulBraidedCategory G]

/-- **The counit of a monoid with dual `M ⊗ T` is the trace of the product**:
`ε((a ⊗ e) ⊗ x) = t(a x ⊗ e)` for `e ∈ G(T)ˢ` in an even degree, when the counit is
`(M ⊗ T) ⊗ M ≅ (M ⊗ M) ⊗ T ⟶ M ⊗ T ⟶ 𝟙` built from the multiplication and `t`. -/
theorem gradedCounit_map_evaluation_gradedMul (M T : D) [MonObj M] [P : ExactPairing M (M ⊗ T)]
    (t : M ⊗ T ⟶ 𝟙_ D)
    (hε : ε_ M (M ⊗ T) =
      (α_ M T M).hom ≫ M ◁ (β_ T M).hom ≫ (α_ M M T).inv ≫ MonObj.mul ▷ T ≫ t)
    {s : ℤ} (hs : Even s) (e : G.obj T s) {p q r m : ℤ} (hr : p + s = r) (h0 : r + q = 0)
    (hpq : p + q = m) (hm : m + s = 0) (a : G.obj M p) (x : G.obj M q) :
    G.gradedCounit (G.map (ε_ M (M ⊗ T)) 0
        (gradedMul G (M ⊗ T) M r q 0 h0 (gradedMul G M T p s r hr a e) x)) =
      G.gradedTrace t e m hm (gradedMonMul G M p q m hpq a x) := by
  have hsign : (s * q).negOnePow = 1 := Int.negOnePow_even _ (hs.mul_right q)
  rw [hε]
  simp only [G.map_comp, categoryOfGradedObjects_comp, ConcreteCategory.comp_apply,
    gradedTrace_apply, gradedMonMul_apply]
  rw [map_associator_gradedMul' M T M p s q r (s + q) 0 hr rfl h0 (by omega),
    map_whiskerLeft_gradedMul, map_braiding_gradedMul G T M s q (s + q) rfl (by omega), hsign,
    one_smul, map_associator_inv_gradedMul' M M T p q s m (s + q) 0 hpq (add_comm q s) hm
      (by omega),
    map_whiskerRight_gradedMul]

end Braided

end CategoryTheory.Functor

end
