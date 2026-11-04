module

public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTate

/-!
# Coherence of the products of twisted units

In the twisted Karoubi envelope of a graded monoidal category, the twisted units
`T(n) = (𝟙_ C, 𝟙, n)` multiply: `T(n) ⊗ T(m) ≅ T(n + m)`
(`CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistTensorIso`). This file shows that these
isomorphisms are compatible with the associativity and unit constraints, i.e. `n ↦ T(n)` is a
monoidal functor from the discrete monoidal category `ℤ`. The target twist is left flexible
(`unitTwistTensorIsoOfEq`), so that the coherence laws hold as equalities of morphisms without
transport between `T((n + m) + l)` and `T(n + (m + l))`.

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistTensorIsoOfEq`:
  `T(n) ⊗ T(m) ≅ T(p)` for `n + m = p`.

## Main results

* `CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistTensorIsoOfEq_assoc`: associativity.
* `CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistTensorIsoOfEq_leftUnitor` and
  `CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistTensorIsoOfEq_rightUnitor`: unitality.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Category

namespace CategoryTheory.GradedCategory.TwistedKaroubi

universe w v u

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]
  [MonoidalCategory C] [IsGradedMonoidal R C]

omit [IsGradedMonoidal R C] in
/-- The identification `T(n) ≅ T(m)` of twisted units along `n = m` has the identity of `𝟙_ C` as
underlying morphism. -/
@[simp]
theorem eqToHom_tateTriple_val {n m : ℤ} (h : n = m) :
    (eqToHom (congrArg (tateTriple R C) h)).val = 𝟙 (𝟙_ C) := by
  subst h
  rfl

/-- `T(n) ⊗ T(m) ≅ T(p)` for `n + m = p`. -/
def unitTwistTensorIsoOfEq (n m p : ℤ) (h : n + m = p) :
    tateTriple R C n ⊗ tateTriple R C m ≅ tateTriple R C p :=
  unitTwistTensorIso n m ≪≫ eqToIso (congrArg (tateTriple R C) h)

/-- Precomposing with the tensor of two identities of `𝟙_ C` does nothing. -/
private theorem tensorHom_id_id_comp {D : Type*} [Category D] [MonoidalCategory D] {X : D}
    (f : 𝟙_ D ⊗ 𝟙_ D ⟶ X) : (𝟙 (𝟙_ D) ⊗ₘ 𝟙 (𝟙_ D)) ≫ f = f := by
  rw [id_tensorHom_id, id_comp]

/-- The isomorphism `T(n) ⊗ T(m) ≅ T(p)` has the right unitor of `𝟙_ C` as underlying
morphism. -/
@[simp]
theorem unitTwistTensorIsoOfEq_hom_val (n m p : ℤ) (h : n + m = p) :
    (unitTwistTensorIsoOfEq (R := R) (C := C) n m p h).hom.val = (ρ_ (𝟙_ C)).hom := by
  subst h
  exact (comp_id _).trans (tensorHom_id_id_comp _)

/-- For `p = n + m`, `unitTwistTensorIsoOfEq` agrees with `unitTwistTensorIso`. -/
theorem unitTwistTensorIsoOfEq_hom_rfl (n m : ℤ) :
    (unitTwistTensorIsoOfEq (R := R) (C := C) n m (n + m) rfl).hom =
      (unitTwistTensorIso n m).hom := by
  simp [unitTwistTensorIsoOfEq]

/-- **Associativity of the products of twisted units.** -/
theorem unitTwistTensorIsoOfEq_assoc (n m l p : ℤ) (h : n + m + l = p) :
    (unitTwistTensorIsoOfEq (R := R) (C := C) n m (n + m) rfl).hom ▷ tateTriple R C l ≫
        (unitTwistTensorIsoOfEq (n + m) l p h).hom =
      (α_ (tateTriple R C n) (tateTriple R C m) (tateTriple R C l)).hom ≫
        tateTriple R C n ◁ (unitTwistTensorIsoOfEq m l (m + l) rfl).hom ≫
          (unitTwistTensorIsoOfEq n (m + l) p (by rw [← h, add_assoc])).hom := by
  ext
  simp only [comp_val, whiskerRight_val, whiskerLeft_val, associator_hom_val,
    unitTwistTensorIsoOfEq_hom_val, tensorObj_p]
  have key : ((ρ_ (𝟙_ C)).hom ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ (𝟙_ C)).hom =
      (((𝟙 (𝟙_ C) ⊗ₘ 𝟙 (𝟙_ C)) ⊗ₘ 𝟙 (𝟙_ C)) ≫ (α_ (𝟙_ C) (𝟙_ C) (𝟙_ C)).hom) ≫
        (𝟙 (𝟙_ C) ⊗ₘ (ρ_ (𝟙_ C)).hom) ≫ (ρ_ (𝟙_ C)).hom := by
    rw [id_tensorHom_id, id_tensorHom_id, id_comp, tensorHom_id, id_tensorHom,
      ← rightUnitor_tensor_hom_assoc, rightUnitor_naturality]
  exact key

/-- **Left unitality of the products of twisted units.** -/
theorem unitTwistTensorIsoOfEq_leftUnitor (n : ℤ) :
    (unitTwistTensorIsoOfEq (R := R) (C := C) 0 n n (zero_add n)).hom =
      (λ_ (tateTriple R C n)).hom := by
  ext
  simp only [unitTwistTensorIsoOfEq_hom_val, leftUnitor_hom_val, tensorObj_p, tensorUnit_p]
  exact unitors_equal.symm.trans (tensorHom_id_id_comp _).symm

/-- **Right unitality of the products of twisted units.** -/
theorem unitTwistTensorIsoOfEq_rightUnitor (n : ℤ) :
    (unitTwistTensorIsoOfEq (R := R) (C := C) n 0 n (add_zero n)).hom =
      (ρ_ (tateTriple R C n)).hom := by
  ext
  simp only [unitTwistTensorIsoOfEq_hom_val, rightUnitor_hom_val, tensorObj_p, tensorUnit_p]
  exact (tensorHom_id_id_comp _).symm

end CategoryTheory.GradedCategory.TwistedKaroubi
