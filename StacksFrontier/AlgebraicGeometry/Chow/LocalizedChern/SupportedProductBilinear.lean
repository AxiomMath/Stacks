module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.SupportedIntersectionProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearChangeOfRings

/-!
# Bilinearity of the product of classes supported on closed subschemes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `Z₁, Z₂ ⊆ X` be closed subschemes with `W = Z₁ ×_X Z₂`. The product
`c₁ c₂ = res(c₁) ∘ c₂ ∈ A^{p+q}(W ⟶ X)` of `c₁ ∈ A^p(Z₁ ⟶ X)` and `c₂ ∈ A^q(Z₂ ⟶ X)`
(`Stacks.Chow.supportedIntersectionMul`) is bilinear, because restriction (Remark 0F9Z), the
composition of Stacks 0B75 and the transport along `Z₁ ×_X Z₂ ≅ W` are additive. Its extension of
scalars to `𝐐` is the product of rational classes in which the formula
`ch(Z₁ ∩ Z₂ ⟶ X, F₁ ⊗^L F₂) = ch(Z₁ ⟶ X, F₁) ch(Z₂ ⟶ X, F₂)` of Stacks 0FBF is written, in
`∏_{n ≥ 0} A^n(Z₁ ∩ Z₂ ⟶ X) ⊗ 𝐐`; its degree `n` component follows from the formula
`P_n = ∑_{n₁ + n₂ = n} C(n, n₁) P_{n₁} P_{n₂}` for the localized power sums.

## Main definitions

* `Stacks.Chow.supportedIntersectionMulBilin` — the product as a `ℤ`-bilinear map.
* `Stacks.Chow.rationalSupportedIntersectionMul` — its base change to `𝐐`.
* `Stacks.Chow.rationalBivariantClassDegreeCongr` — rational classes of equal degrees.

## Main results

* `Stacks.Chow.supportedIntersectionMul_add_left`, `Stacks.Chow.supportedIntersectionMul_add_right`
  — additivity in each factor.
* `Stacks.Chow.rationalSupportedIntersectionMul_tmul` — the rational product on pure tensors.
* `Stacks.Chow.tmul_eq_sum_rationalSupportedIntersectionMul_of_eq_sum_choose` — the Chern
  character formula follows from the power sum formula.

## Implementation notes

The product of two families of rational classes indexed by the degree is the Cauchy product of
the components, `(a b)_n = ∑_{n₁ + n₂ = n} a_{n₁} b_{n₂}`, each summand read in degree `n` through
`Stacks.Chow.rationalBivariantClassDegreeCongr`; an identity in `∏_n A^n(W ⟶ X) ⊗ 𝐐` is an
identity of components, which is how it is stated.

## References

* [Stacks Project, Tag 0FBF](https://stacks.math.columbia.edu/tag/0FBF)
* [Stacks Project, Tag 0FE5](https://stacks.math.columbia.edu/tag/0FE5)
* [Stacks Project, Tag 0FB5](https://stacks.math.columbia.edu/tag/0FB5)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct Finset

universe u

namespace Stacks.Chow

section Bilinear

variable (C : ChowSituation.{u}) {X Z₁ Z₂ W : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X) [LocallyOfFiniteType f₁] (f₂ : Z₂ ⟶ X)
  [LocallyOfFiniteType f₂] {w₁ : W ⟶ Z₁} {w₂ : W ⟶ Z₂} (sq : IsPullback w₁ w₂ f₁ f₂)
  (iW : W ⟶ X) [LocallyOfFiniteType iW] (hW : w₂ ≫ f₂ = iW) {p q : ℤ}

/-- The product of classes supported on two closed subschemes is additive in the first factor:
restriction (Remark 0F9Z), composition (Stacks 0B75) and the transport to `W` are additive. -/
theorem supportedIntersectionMul_add_left
    (c₁ c₁' : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q) :
    supportedIntersectionMul C sX f₁ f₂ sq iW hW (c₁ + c₁') c₂ =
      supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁ c₂ +
        supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁' c₂ := by
  simp only [supportedIntersectionMul, bivariantCompositeOfInvertible, bivariantRestriction_add,
    bivariantComposite_add_left, bivariantTransport_add]

/-- The product of classes supported on two closed subschemes is additive in the second factor. -/
theorem supportedIntersectionMul_add_right
    (c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p)
    (c₂ c₂' : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q) :
    supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁ (c₂ + c₂') =
      supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁ c₂ +
        supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁ c₂' := by
  simp only [supportedIntersectionMul, bivariantCompositeOfInvertible,
    bivariantComposite_add_right, bivariantTransport_add]

/-- The product `A^p(Z₁ ⟶ X) × A^q(Z₂ ⟶ X) ⟶ A^{p+q}(W ⟶ X)` of classes supported on two closed
subschemes, as a biadditive map. -/
def supportedIntersectionMulAddHom :
    BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p →+
      BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q →+
        BivariantClass C (gysinSystemOfInvertible C) (iW ≫ sX) sX iW rfl (p + q) :=
  AddMonoidHom.mk' (fun c₁ ↦ AddMonoidHom.mk' (supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁)
      (supportedIntersectionMul_add_right C sX f₁ f₂ sq iW hW c₁))
    fun c₁ c₁' ↦ AddMonoidHom.ext fun c₂ ↦
      supportedIntersectionMul_add_left C sX f₁ f₂ sq iW hW c₁ c₁' c₂

/-- **The product of classes supported on two closed subschemes is `ℤ`-bilinear**: the product
`Stacks.Chow.supportedIntersectionMul` as a `ℤ`-bilinear map
`A^p(Z₁ ⟶ X) × A^q(Z₂ ⟶ X) ⟶ A^{p+q}(W ⟶ X)`. -/
def supportedIntersectionMulBilin :
    BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p →ₗ[ℤ]
      BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q →ₗ[ℤ]
        BivariantClass C (gysinSystemOfInvertible C) (iW ≫ sX) sX iW rfl (p + q) :=
  LinearMap.mk₂ ℤ (supportedIntersectionMul C sX f₁ f₂ sq iW hW)
    (supportedIntersectionMul_add_left C sX f₁ f₂ sq iW hW)
    (fun n c₁ c₂ ↦ by
      have := congrArg (fun φ ↦ φ c₂)
        (map_zsmul (supportedIntersectionMulAddHom C sX f₁ f₂ sq iW hW (p := p) (q := q)) n c₁)
      simpa [supportedIntersectionMulAddHom] using this)
    (supportedIntersectionMul_add_right C sX f₁ f₂ sq iW hW)
    (fun n c₁ c₂ ↦ map_zsmul (supportedIntersectionMulAddHom C sX f₁ f₂ sq iW hW c₁) n c₂)

/-- **The product of rational classes supported on two closed subschemes**: the `ℚ`-bilinear map
`(A^p(Z₁ ⟶ X) ⊗ 𝐐) × (A^q(Z₂ ⟶ X) ⊗ 𝐐) ⟶ A^{p+q}(W ⟶ X) ⊗ 𝐐` obtained from the product of
`Stacks.Chow.supportedIntersectionMul` by extension of scalars
(`Stacks.Sheaves.BilinearChangeOfRings.baseChange₂`). -/
def rationalSupportedIntersectionMul :
    ℚ ⊗[ℤ] BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p →ₗ[ℚ]
      ℚ ⊗[ℤ] BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q →ₗ[ℚ]
        ℚ ⊗[ℤ] BivariantClass C (gysinSystemOfInvertible C) (iW ≫ sX) sX iW rfl (p + q) :=
  Stacks.Sheaves.BilinearChangeOfRings.baseChange₂ (S := ℚ)
    (supportedIntersectionMulBilin C sX f₁ f₂ sq iW hW)

/-- The rational product on pure tensors: `(a ⊗ c₁) (a' ⊗ c₂) = (a a') ⊗ c₁ c₂`. -/
theorem rationalSupportedIntersectionMul_tmul (a a' : ℚ)
    (c₁ : BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl p)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl q) :
    rationalSupportedIntersectionMul C sX f₁ f₂ sq iW hW (a ⊗ₜ c₁) (a' ⊗ₜ c₂) =
      (a * a') ⊗ₜ supportedIntersectionMul C sX f₁ f₂ sq iW hW c₁ c₂ :=
  Stacks.Sheaves.BilinearChangeOfRings.baseChange₂_tmul _ _ _ _ _

end Bilinear

section Degree

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX)

/-- A rational bivariant class of degree `p` is one of degree `p'` whenever `p = p'`: the base
change to `𝐐` of `Stacks.Chow.bivariantClassDegreeCongr`. -/
def rationalBivariantClassDegreeCongr {p p' : ℤ} (h : p = p') :
    ℚ ⊗[ℤ] BivariantClass C G sX sY f hf p ≃ₗ[ℚ] ℚ ⊗[ℤ] BivariantClass C G sX sY f hf p' :=
  LinearEquiv.baseChange ℤ ℚ _ _ (bivariantClassDegreeCongr C G sX sY f hf h).toIntLinearEquiv

/-- `Stacks.Chow.rationalBivariantClassDegreeCongr` on pure tensors. -/
theorem rationalBivariantClassDegreeCongr_tmul {p p' : ℤ} (h : p = p') (a : ℚ)
    (c : BivariantClass C G sX sY f hf p) :
    rationalBivariantClassDegreeCongr C G sX sY f hf h (a ⊗ₜ c) =
      a ⊗ₜ bivariantClassDegreeCongr C G sX sY f hf h c :=
  rfl

end Degree


section Character

variable (C : ChowSituation.{u}) {X Z₁ Z₂ W : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X) [LocallyOfFiniteType f₁] (f₂ : Z₂ ⟶ X)
  [LocallyOfFiniteType f₂] {w₁ : W ⟶ Z₁} {w₂ : W ⟶ Z₂} (sq : IsPullback w₁ w₂ f₁ f₂)
  (iW : W ⟶ X) [LocallyOfFiniteType iW] (hW : w₂ ≫ f₂ = iW)

/-- **The Chern character formula from the power sum formula.** Let `P₁`, `P₂`, `P` be families of
classes `P_{1,n} ∈ A^n(Z₁ ⟶ X)`, `P_{2,n} ∈ A^n(Z₂ ⟶ X)`, `P_n ∈ A^n(W ⟶ X)`. If
`P_n = ∑_{n₁ + n₂ = n} C(n, n₁) P_{1,n₁} P_{2,n₂}`, then in `A^n(W ⟶ X) ⊗ 𝐐`

  `P_n / n! = ∑_{n₁ + n₂ = n} (P_{1,n₁} / n₁!) (P_{2,n₂} / n₂!)`,

since `C(n, n₁) / n! = 1 / (n₁! n₂!)`. This is the degree `n` component of
`ch = ch₁ ch₂` in `∏_n A^n(W ⟶ X) ⊗ 𝐐` for `ch_n = P_n / n!`, the product being the Cauchy product
of the components. -/
theorem tmul_eq_sum_rationalSupportedIntersectionMul_of_eq_sum_choose
    (P₁ : ∀ n : ℕ, BivariantClass C (gysinSystemOfInvertible C) (f₁ ≫ sX) sX f₁ rfl n)
    (P₂ : ∀ n : ℕ, BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ sX) sX f₂ rfl n)
    (P : ∀ n : ℕ, BivariantClass C (gysinSystemOfInvertible C) (iW ≫ sX) sX iW rfl n) (n : ℕ)
    (h : P n = ∑ q ∈ (antidiagonal n).attach, (n.choose q.1.1 : ℤ) •
      bivariantClassDegreeCongr C _ _ _ _ rfl (by have := mem_antidiagonal.1 q.2; omega)
        (supportedIntersectionMul C sX f₁ f₂ sq iW hW (P₁ q.1.1) (P₂ q.1.2))) :
    ((n.factorial : ℚ)⁻¹ ⊗ₜ[ℤ] P n) = ∑ q ∈ (antidiagonal n).attach,
      rationalBivariantClassDegreeCongr C _ _ _ _ rfl (by have := mem_antidiagonal.1 q.2; omega)
        (rationalSupportedIntersectionMul C sX f₁ f₂ sq iW hW
          ((q.1.1.factorial : ℚ)⁻¹ ⊗ₜ[ℤ] P₁ q.1.1) ((q.1.2.factorial : ℚ)⁻¹ ⊗ₜ[ℤ] P₂ q.1.2)) := by
  rw [h, tmul_sum]
  refine sum_congr rfl fun q _ ↦ ?_
  rw [rationalSupportedIntersectionMul_tmul, rationalBivariantClassDegreeCongr_tmul, tmul_smul,
    smul_tmul', zsmul_eq_mul]
  congr 1
  obtain ⟨⟨i, j⟩, hq⟩ := q
  obtain rfl : i + j = n := mem_antidiagonal.1 hq
  have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hij : ((i + j).factorial : ℚ) ≠ 0 := by exact_mod_cast (i + j).factorial_ne_zero
  rw [Int.cast_natCast, Nat.cast_add_choose]
  field_simp

end Character

end Stacks.Chow

end
