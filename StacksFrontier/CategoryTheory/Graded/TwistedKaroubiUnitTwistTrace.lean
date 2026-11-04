module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTate

/-!
# Morphisms to the unit from untwisted objects tensored with a twisted unit

Let `C` be a graded monoidal category and `M_C` its twisted Karoubi envelope. A morphism
`a : A ⟶ 𝟙` of `C` homogeneous of degree `-d` is a morphism of triples
`(A, 1, 0) ⊗ T(d) ⟶ 𝟙`, through `A ⊗ 𝟙 ≅ A`, where `T(d) = (𝟙, 1, d)` is the twisted unit
(`CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistTrace`). For the category of Chow motives
and `a = [X] ∈ Corr^{-d}(X, Spec k)` this is the morphism `h(X)(d) ⟶ 𝟏` giving the trace map of a
realization (proof of Stacks 0FHK, datum (D3)).

If `(a ⊗ b) ≫ λ = c` in `C`, then the morphisms of triples are multiplicative: the morphism
attached to `c` is the tensor product of those attached to `a` and `b`, up to the interchange
`(A ⊗ B) ⊗ (T(d) ⊗ T(e)) ≅ (A ⊗ T(d)) ⊗ (B ⊗ T(e))` and `T(d) ⊗ T(e) ≅ T(d + e)`
(`CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistTrace_tensor`). For fundamental classes
this is the multiplicativity of the trace maps, axiom (B)(b).

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistTrace`.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistTrace_tensor`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Category

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u

/- The statements below use the tensor product of triples through the monoidal structure
`TwistedKaroubi.monoidalCategory`, as monoid objects and monoidal functors do; the direct
instance `TwistedKaroubi.monoidalCategoryStruct` would give an equal but differently built tensor
product. -/
attribute [-instance] TwistedKaroubi.monoidalCategoryStruct

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]
  [MonoidalCategory C] [IsGradedMonoidal R C]

/-- **A morphism `a : A ⟶ 𝟙` of degree `-d` as a morphism of triples `(A, 1, 0) ⊗ T(d) ⟶ 𝟙`**,
through `A ⊗ 𝟙 ≅ A`. -/
def unitTwistTrace {A : C} (d : ℤ) (a : A ⟶ 𝟙_ C) (ha : a ∈ grade (R := R) A (𝟙_ C) (-d)) :
    ofObj (R := R) A ⊗ tateTriple R C d ⟶ 𝟙_ (TwistedKaroubi R C) :=
  Hom.mk ((ρ_ A).hom ≫ a)
    ⟨grade_cast (comp_mem (R := R) ha (IsGradedMonoidal.rightUnitor_hom_mem (R := R) A)) (by
        change -d + 0 = 0 - (0 + d); ring),
      by
        change (𝟙 A ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ A).hom ≫ a = (ρ_ A).hom ≫ a
        rw [id_tensorHom_id, id_comp],
      comp_id _⟩

/-- The underlying morphism of `unitTwistTrace d a ha` is `ρ_A ≫ a : A ⊗ 𝟙 ⟶ 𝟙`. -/
@[simp]
theorem unitTwistTrace_val {A : C} (d : ℤ) (a : A ⟶ 𝟙_ C)
    (ha : a ∈ grade (R := R) A (𝟙_ C) (-d)) :
    (unitTwistTrace d a ha).val = (ρ_ A).hom ≫ a :=
  rfl

section Braided

variable [BraidedCategory C] [IsGradedBraided R C]

/-- The interchange of triples with trivial idempotents is the interchange of `C`. -/
theorem tensorμ_val_of_p {M N P Q : TwistedKaroubi R C} (hM : M.p = 𝟙 M.X) (hN : N.p = 𝟙 N.X)
    (hP : P.p = 𝟙 P.X) (hQ : Q.p = 𝟙 Q.X) :
    (tensorμ M N P Q).val = tensorμ M.X N.X P.X Q.X := by
  simp only [tensorμ, comp_val, whiskerLeft_val, whiskerRight_val, associator_hom_val,
    associator_inv_val, braiding_hom_val, tensorObj_p, hM, hN, hP, hQ]
  dsimp only [tensorObj_X]
  simp [MonoidalCategory.tensorHom_def]

/-- **Multiplicativity of `unitTwistTrace`.** Let `a : A ⟶ 𝟙`, `b : B ⟶ 𝟙`, `c : P ⟶ 𝟙` and
`u : A ⊗ B ⟶ P` with `(a ⊗ b) ≫ λ = u ≫ c`. Then the morphism of triples attached to `c`,
precomposed with `φ ⊗ ψ` for `φ : (A, 1, 0) ⊗ (B, 1, 0) ⟶ (P, 1, 0)` over `u` and
`ψ : T(d) ⊗ T(e) ⟶ T(n)` over `𝟙 ⊗ 𝟙 ≅ 𝟙`, is the tensor product of those attached to `a` and
`b`, after the interchange. -/
theorem unitTwistTrace_tensor {A B P : C} {d e n : ℤ} (a : A ⟶ 𝟙_ C) (b : B ⟶ 𝟙_ C)
    (u : A ⊗ B ⟶ P) (c : P ⟶ 𝟙_ C) (ha : a ∈ grade (R := R) A (𝟙_ C) (-d))
    (hb : b ∈ grade (R := R) B (𝟙_ C) (-e)) (hc : c ∈ grade (R := R) P (𝟙_ C) (-n))
    (h : (a ⊗ₘ b) ≫ (λ_ (𝟙_ C)).hom = u ≫ c)
    (φ : ofObj (R := R) A ⊗ ofObj (R := R) B ⟶ ofObj (R := R) P) (hφ : φ.val = u)
    (ψ : tateTriple R C d ⊗ tateTriple R C e ⟶ tateTriple R C n) (hψ : ψ.val = (ρ_ (𝟙_ C)).hom) :
    (φ ⊗ₘ ψ) ≫ unitTwistTrace n c hc =
      tensorμ (ofObj (R := R) A) (ofObj (R := R) B) (tateTriple R C d) (tateTriple R C e) ≫
        (unitTwistTrace d a ha ⊗ₘ unitTwistTrace e b hb) ≫ (λ_ (𝟙_ (TwistedKaroubi R C))).hom := by
  apply hom_ext
  rw [comp_val, comp_val, comp_val, tensorHom_val, tensorHom_val, unitTwistTrace_val,
    unitTwistTrace_val, unitTwistTrace_val, tensorμ_val_of_p rfl rfl rfl rfl, leftUnitor_hom_val,
    hψ, hφ]
  change (u ⊗ₘ (ρ_ (𝟙_ C)).hom) ≫ (ρ_ P).hom ≫ c =
    tensorμ A B (𝟙_ C) (𝟙_ C) ≫ (((ρ_ A).hom ≫ a) ⊗ₘ ((ρ_ B).hom ≫ b)) ≫
      (𝟙 (𝟙_ C) ⊗ₘ 𝟙 (𝟙_ C)) ≫ (λ_ (𝟙_ C)).hom
  rw [MonoidalCategory.id_tensorHom_id, Category.id_comp, MonoidalCategory.tensorHom_def',
    Category.assoc, rightUnitor_naturality_assoc, ← h,
    ← MonoidalCategory.tensorHom_comp_tensorHom, tensor_right_unitality]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, unitors_inv_equal, Iso.hom_inv_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

end Braided

end CategoryTheory.GradedCategory.TwistedKaroubi

end
