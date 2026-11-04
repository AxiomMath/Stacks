module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiMonObj
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiUnitTwistTrace

/-!
# Multiplicativity of unit-twist traces through a monoid

Let `C` be a graded braided monoidal category, `P` a monoid of `C` and `f : A ⟶ P`, `g : B ⟶ P`
of degree zero. For `a : A ⟶ 𝟙`, `b : B ⟶ 𝟙`, `c : P ⟶ 𝟙` of degrees `-d`, `-e`, `-n` with
`(a ⊗ b) ≫ λ = ((f ⊗ g) ≫ μ_P) ≫ c`, the morphism of triples attached to `c`
(`TwistedKaroubi.unitTwistTrace`), precomposed with `((f ⊗ g) ≫ μ) ⊗ ψ` for
`ψ : T(d) ⊗ T(e) ⟶ T(n)` over `𝟙 ⊗ 𝟙 ≅ 𝟙`, is the tensor product of those attached to `a` and
`b` after the interchange (`TwistedKaroubi.unitTwistTrace_tensor_ofObjHom_mul`). This is
`TwistedKaroubi.unitTwistTrace_tensor` for the comparison `(f ⊗ g) ≫ μ_P`, stated generically so
that for a concrete `C` no comparison between spellings of the objects of `C` is needed. For
motives it is the multiplicativity of fundamental classes behind axiom (B)(b) (Stacks 0FHK).

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistTrace_tensor_ofObjHom_mul`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u

attribute [-instance] TwistedKaroubi.monoidalCategoryStruct

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]
  [MonoidalCategory C] [IsGradedMonoidal R C] [BraidedCategory C] [IsGradedBraided R C]

/-- **Unit-twist traces are multiplicative through a monoid**: if
`(a ⊗ b) ≫ λ = ((f ⊗ g) ≫ μ_P) ≫ c`, then
`(((f ⊗ g) ≫ μ) ⊗ ψ) ≫ [c] = tensorμ ≫ ([a] ⊗ [b]) ≫ λ` on triples. -/
theorem unitTwistTrace_tensor_ofObjHom_mul {A B P : C} [MonObj P]
    (hη : η[P] ∈ grade (R := R) (𝟙_ C) P 0) (hμ : μ[P] ∈ grade (R := R) (P ⊗ P) P 0)
    (f : A ⟶ P) (hf : f ∈ grade (R := R) A P 0) (g : B ⟶ P) (hg : g ∈ grade (R := R) B P 0)
    {d e n : ℤ} (a : A ⟶ 𝟙_ C) (b : B ⟶ 𝟙_ C) (c : P ⟶ 𝟙_ C)
    (ha : a ∈ grade (R := R) A (𝟙_ C) (-d)) (hb : b ∈ grade (R := R) B (𝟙_ C) (-e))
    (hc : c ∈ grade (R := R) P (𝟙_ C) (-n))
    (h : (a ⊗ₘ b) ≫ (λ_ (𝟙_ C)).hom = ((f ⊗ₘ g) ≫ μ[P]) ≫ c)
    (ψ : tateTriple R C d ⊗ tateTriple R C e ⟶ tateTriple R C n)
    (hψ : ψ.val = (ρ_ (𝟙_ C)).hom) :
    letI := monObjOfObj P hη hμ
    (((ofObjHom f hf ⊗ₘ ofObjHom g hg) ≫ μ[ofObj (R := R) P]) ⊗ₘ ψ) ≫ unitTwistTrace n c hc =
      tensorμ (ofObj (R := R) A) (ofObj (R := R) B) (tateTriple R C d) (tateTriple R C e) ≫
        (unitTwistTrace d a ha ⊗ₘ unitTwistTrace e b hb) ≫
          (λ_ (𝟙_ (TwistedKaroubi R C))).hom :=
  let := monObjOfObj P hη hμ
  unitTwistTrace_tensor a b ((f ⊗ₘ g) ≫ μ[P]) c ha hb hc h _
    (by rw [comp_val, tensorHom_val, ofObjHom_val, ofObjHom_val, monObjOfObj_mul_val]; rfl) ψ hψ

end CategoryTheory.GradedCategory.TwistedKaroubi

end
