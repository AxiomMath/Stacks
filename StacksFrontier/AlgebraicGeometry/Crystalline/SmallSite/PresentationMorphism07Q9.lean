module

public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeFunctoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeRetract

/-!
# Morphisms of presentations and the envelopes `D(n)`

Let `σ : s ⟶ t` be a morphism of affine crystalline situations, `P → C` and `Q → C'` polynomial
presentations of the targets, and `r : P → Q` a ring map over the bases commuting with the two
presentations and `σ`.  This file builds the induced map of `(n + 1)`-fold tensor powers
`P^{⊗(n + 1)} → Q^{⊗(n + 1)}` and the induced divided power morphisms of the uncompleted
divided power envelopes of their kernels, by the universal property of the divided power envelope
([Stacks, Tag 07H8]), and proves that they commute with the reindexings of the variables, that
is, with the cosimplicial structure of `D(•)`.

## Main definitions

* `Crystalline.tensorPowerRingHom` — the `(n + 1)`-fold tensor power of `r`.
* `Crystalline.tensorPowerEnvelopeMapOver` — the induced divided power morphism of the
  envelopes of the kernels of `P^{⊗(n + 1)} → C` and `Q^{⊗(n + 1)} → C'`.

## Main results

* `Crystalline.tensorPowerEnvelopeMapOver_polynomial` — it extends the tensor power of `r`.
* `Crystalline.tensorPowerEnvelopeMapOver_comp_envelopeReindex` — it commutes with the
  reindexings of the variables.

## References

* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory Simplicial

universe u

noncomputable section

namespace Crystalline

variable {s t : AffineCrystallineSituation.{u, u}} (σ : AffineCrystallineSituation.Hom s t)
  {ι κ : Type u} (g : MvPolynomial ι s.A →ₐ[s.A] s.C) (g₂ : MvPolynomial κ t.A →ₐ[t.A] t.C)
  (r : MvPolynomial ι s.A →+* MvPolynomial κ t.A)

/-- **The `(n + 1)`-fold tensor power of a ring map of polynomial algebras over a morphism of
the bases**: the variable `x_i(j)` of the `j`-th factor goes to the image of `r(x_i)` in the
`j`-th factor. -/
def tensorPowerRingHom (n : ℕ) :
    MvPolynomial (Fin (n + 1) × ι) s.A →+* MvPolynomial (Fin (n + 1) × κ) t.A :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp σ.base.toRingHom) fun ji ↦
    mvPolynomialCoprojection t.A (n := n) ji.1 (r (MvPolynomial.X ji.2))

variable (hrC : ∀ b : s.A, r (MvPolynomial.C b) = MvPolynomial.C (σ.base.toRingHom b))

include hrC in
/-- The tensor power of `r` restricts to `r` on each factor. -/
theorem tensorPowerRingHom_coprojection (n : ℕ) (j : Fin (n + 1)) (q : MvPolynomial ι s.A) :
    tensorPowerRingHom σ r n (mvPolynomialCoprojection s.A (n := n) j q) =
      mvPolynomialCoprojection t.A (n := n) j (r q) := by
  have h : (tensorPowerRingHom σ r n).comp (mvPolynomialCoprojection s.A (n := n) j).toRingHom =
      (mvPolynomialCoprojection t.A (n := n) j).toRingHom.comp r := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp [tensorPowerRingHom, mvPolynomialCoprojection, hrC]
    · intro i
      simp [tensorPowerRingHom, mvPolynomialCoprojection]
  exact RingHom.congr_fun h q

/-- The tensor power of `r` is over the morphism of the bases. -/
theorem tensorPowerRingHom_C (n : ℕ) (b : s.A) :
    tensorPowerRingHom σ r n (MvPolynomial.C b) = MvPolynomial.C (σ.base.toRingHom b) := by
  simp [tensorPowerRingHom]

variable (hr : g₂.toRingHom.comp r = σ.target.comp g.toRingHom)

include hrC hr in
/-- **The tensor power of `r` commutes with the two tensor power presentations.** -/
theorem tensorPowerRingHom_comp_presentation (n : ℕ) :
    (tensorPowerPresentation t g₂ n).toRingHom.comp (tensorPowerRingHom σ r n) =
      σ.target.comp (tensorPowerPresentation s g n).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro b
    change tensorPowerPresentation t g₂ n (tensorPowerRingHom σ r n (MvPolynomial.C b)) =
      σ.target (tensorPowerPresentation s g n (MvPolynomial.C b))
    rw [tensorPowerRingHom_C, MvPolynomial.C_eq_algebraMap, MvPolynomial.C_eq_algebraMap,
      AlgHom.commutes, AlgHom.commutes]
    exact (RingHom.congr_fun σ.commutes b).symm
  · rintro ⟨j, i⟩
    simp only [RingHom.comp_apply, tensorPowerRingHom, MvPolynomial.eval₂Hom_X',
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← AlgHom.comp_apply, tensorPowerPresentation_comp_coprojection]
    simpa [tensorPowerPresentation] using RingHom.congr_fun hr (MvPolynomial.X i)

include hrC in
/-- **The tensor power of `r` commutes with the reindexings of the variables.** -/
theorem tensorPowerRingHom_rename {n m : SimplexCategory} (φ : n ⟶ m)
    (q : MvPolynomial (Fin (n.len + 1) × ι) s.A) :
    tensorPowerRingHom σ r m.len (MvPolynomial.rename (simplexVariableMap (ι := ι) φ) q) =
      MvPolynomial.rename (simplexVariableMap (ι := κ) φ) (tensorPowerRingHom σ r n.len q) := by
  have h : (tensorPowerRingHom σ r m.len).comp
      (MvPolynomial.rename (simplexVariableMap (ι := ι) φ)).toRingHom =
      (MvPolynomial.rename (simplexVariableMap (ι := κ) φ)).toRingHom.comp
        (tensorPowerRingHom σ r n.len) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp [tensorPowerRingHom]
    · rintro ⟨j, i⟩
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.rename_X, tensorPowerRingHom, simplexVariableMap, MvPolynomial.eval₂Hom_X']
      simp [mvPolynomialCoprojection, MvPolynomial.rename_rename, Function.comp_def,
        simplexVariableMap]
  exact RingHom.congr_fun h q

/-- **The divided power morphism of envelopes induced by a morphism of presentations**, in
tensor degree `n`: the universal property of the divided power envelope of the kernel of
`P^{⊗(n + 1)} → C`, applied to the tensor power of `r` followed by the map into the envelope of
the kernel of `Q^{⊗(n + 1)} → C'`. -/
def tensorPowerEnvelopeMapOver (n : ℕ) :
    DividedPowers.DPMorphism (polynomialDividedPowerEnvelope s
        (tensorPowerPresentation s g n)).object.dividedPowers
      (polynomialDividedPowerEnvelope t (tensorPowerPresentation t g₂ n)).object.dividedPowers :=
  (polynomialEnvelopeMapOver σ (tensorPowerPresentation s g n) (tensorPowerPresentation t g₂ n)
    (tensorPowerRingHom σ r n) (tensorPowerRingHom_C σ r n)
    (tensorPowerRingHom_comp_presentation σ g g₂ r hrC hr n)).1

/-- The induced morphism of envelopes is over the morphism of the bases. -/
theorem tensorPowerEnvelopeMapOver_structureMap (n : ℕ) :
    (tensorPowerEnvelopeMapOver σ g g₂ r hrC hr n).comp
        (polynomialDividedPowerEnvelope s (tensorPowerPresentation s g n)).structureMap =
      (polynomialDividedPowerEnvelope t (tensorPowerPresentation t g₂ n)).structureMap.comp
        σ.base :=
  (polynomialEnvelopeMapOver σ (tensorPowerPresentation s g n) (tensorPowerPresentation t g₂ n)
    (tensorPowerRingHom σ r n) (tensorPowerRingHom_C σ r n)
    (tensorPowerRingHom_comp_presentation σ g g₂ r hrC hr n)).2

/-- **The induced morphism of envelopes extends the tensor power of `r`.** -/
theorem tensorPowerEnvelopeMapOver_polynomial (n : ℕ)
    (q : MvPolynomial (Fin (n + 1) × ι) s.A) :
    tensorPowerEnvelopeMapOver σ g g₂ r hrC hr n
        ((polynomialDividedPowerEnvelope s
          (tensorPowerPresentation s g n)).algebraMap.toRingHom q) =
      (polynomialDividedPowerEnvelope t (tensorPowerPresentation t g₂ n)).algebraMap.toRingHom
        (tensorPowerRingHom σ r n q) :=
  polynomialEnvelopeMapOver_polynomial σ _ _ _ _ _ q

/-- **The induced morphisms of envelopes commute with the reindexings of the variables**, which
are the structure maps of the cosimplicial ring `D(•)` before completion. -/
theorem tensorPowerEnvelopeMapOver_comp_envelopeReindex {n m : SimplexCategory} (φ : n ⟶ m) :
    (tensorPowerEnvelopeMapOver σ g g₂ r hrC hr m.len).comp (envelopeReindex s g φ).1 =
      (envelopeReindex t g₂ φ).1.comp (tensorPowerEnvelopeMapOver σ g g₂ r hrC hr n.len) := by
  refine envelopeHom_ext (polynomialDividedPowerEnvelope s (tensorPowerPresentation s g n.len))
    (polynomialDividedPowerEnvelope t (tensorPowerPresentation t g₂ m.len)).object _ _ ?_ ?_
  · apply DividedPowers.DPMorphism.ext
    funext a
    let Es := fun k ↦ polynomialDividedPowerEnvelope s (tensorPowerPresentation s g k)
    let Et := fun k ↦ polynomialDividedPowerEnvelope t (tensorPowerPresentation t g₂ k)
    have h₁ : (envelopeReindex s g φ).1 ((Es n.len).structureMap a) =
        (Es m.len).structureMap a :=
      DFunLike.congr_fun (envelopeReindex s g φ).2 a
    have h₂ : tensorPowerEnvelopeMapOver σ g g₂ r hrC hr m.len ((Es m.len).structureMap a) =
        (Et m.len).structureMap (σ.base a) :=
      DFunLike.congr_fun (tensorPowerEnvelopeMapOver_structureMap σ g g₂ r hrC hr m.len) a
    have h₃ : tensorPowerEnvelopeMapOver σ g g₂ r hrC hr n.len ((Es n.len).structureMap a) =
        (Et n.len).structureMap (σ.base a) :=
      DFunLike.congr_fun (tensorPowerEnvelopeMapOver_structureMap σ g g₂ r hrC hr n.len) a
    have h₄ : (envelopeReindex t g₂ φ).1 ((Et n.len).structureMap (σ.base a)) =
        (Et m.len).structureMap (σ.base a) :=
      DFunLike.congr_fun (envelopeReindex t g₂ φ).2 (σ.base a)
    change tensorPowerEnvelopeMapOver σ g g₂ r hrC hr m.len
        ((envelopeReindex s g φ).1 ((Es n.len).structureMap a)) =
      (envelopeReindex t g₂ φ).1
        (tensorPowerEnvelopeMapOver σ g g₂ r hrC hr n.len ((Es n.len).structureMap a))
    rw [h₁, h₂, h₃, h₄]
  · refine RingHom.ext fun q ↦ ?_
    change tensorPowerEnvelopeMapOver σ g g₂ r hrC hr m.len ((envelopeReindex s g φ).1
        ((polynomialDividedPowerEnvelope s
          (tensorPowerPresentation s g n.len)).algebraMap.toRingHom q)) =
      (envelopeReindex t g₂ φ).1 (tensorPowerEnvelopeMapOver σ g g₂ r hrC hr n.len
        ((polynomialDividedPowerEnvelope s
          (tensorPowerPresentation s g n.len)).algebraMap.toRingHom q))
    rw [envelopeReindex_polynomial, tensorPowerEnvelopeMapOver_polynomial,
      tensorPowerEnvelopeMapOver_polynomial, envelopeReindex_polynomial,
      tensorPowerRingHom_rename σ r hrC]

end Crystalline

end

end
