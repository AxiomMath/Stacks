module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeRow
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Trace

/-!
# The duality pairing of the degree-`n` row of Tag 01XW

Let `S` be a scheme, let `n = m + 1 ≥ 1` and let `f : ℙⁿ_S ⟶ S` be the structure morphism. For
integers `d` and `t` with `t + d = -n-1`, multiplication by the monomial `T^b` of a multidegree
`b` of total degree `t` is a morphism `𝒪(d) ⟶ 𝒪(-n-1)`, so the trace
`Rⁿ f_* 𝒪(-n-1) ≅ 𝒪_S` turns the family of those multiplications into a single morphism

`Rⁿ f_* 𝒪(d) ⟶ ∏_{b} 𝒪_S`,

the product being over the multidegrees of total degree `t`. That product is the `𝒪_S`-dual of
`(𝒪_S[T₀, …, Tₙ])_t`, so this is the comparison morphism of the degree-`n` row of the display of
[Stacks, Tag 01XW]; this file constructs it and proves the one identity the row's induction on
`t` runs on: **the comparison morphisms intertwine multiplication by a coordinate on the left
with its transpose on the right.**

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `MonomialIndex.addOf`: the sum of two multidegrees, at a named total degree.
* `monomialSum`: the direct sum of copies of `𝒪_S` indexed by the multidegrees of total degree
  `t`, which is the dual of `(𝒪_S[T₀, …, Tₙ])_t`.
* `monomialSumMul`: **the transpose of multiplication by `Tᵢ`**, `monomialSum t ⟶ monomialSum t'`
  for `1 + t' = t`.
* `pairing`: **the comparison morphism `Rⁿ f_* 𝒪(d) ⟶ monomialSum t` of the degree-`n` row.**

## Main results

* `twistOverMulMonomial_congr` and `twistOverMulMonomial_comp'`: multiplication by a monomial
  depends on the multidegree alone, and the multiplications compose by adding multidegrees, both
  with the total degrees named rather than computed.
* `pairing_comp_monomialSumMul`: **the comparison morphisms intertwine multiplication by a
  coordinate with its transpose.**
* `monomialSumIsoDual`: `monomialSum t` is the `𝒪_S`-dual of `(𝒪_S[T₀, …, Tₙ])_t`.
* `isZero_monomialSum_of_neg`: it vanishes in a negative degree.

## Implementation notes

Every total degree is carried as a named integer together with an equation, as in
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistOverMulLeft`: the composition law
for monomial multiplication produces the product monomial in the degree
`b.degree + c.degree`, which is the degree the consumer wants only propositionally, and naming
the degree removes every transport. `twistOverMulMonomial_congr` is what makes that possible —
multiplication by a monomial is determined by the monomial, not by the degree in which it is
presented as homogeneous.

The dual of `(𝒪_S[T₀, …, Tₙ])_t` is a direct sum rather than a product because the index set is
finite, where the two agree; the direct sum is the shape in which both the comparison morphism
(a lift) and the Koszul differentials (matrices) are written.

No `stacks` attribute is attached: the degree-`n` row of [Stacks, Tag 01XW] is the assertion that
the comparison morphism below is an isomorphism, and nothing of that is claimed here.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

/-! ### Multidegrees at a named total degree -/

/-- **The sum of two multidegrees, at a named total degree.** -/
def MonomialIndex.addOf {n : ℕ} {e₁ e₂ e₃ : ℤ} (b : MonomialIndex.{u} n e₁)
    (c : MonomialIndex.{u} n e₂) (h : e₁ + e₂ = e₃) : MonomialIndex.{u} n e₃ :=
  ⟨b.1 + c.1, h ▸ (MonomialIndex.add b c).2⟩

/-- The underlying multidegree of `MonomialIndex.addOf b c h` is `b.1 + c.1`. -/
@[simp] theorem MonomialIndex.addOf_val {n : ℕ} {e₁ e₂ e₃ : ℤ} (b : MonomialIndex.{u} n e₁)
    (c : MonomialIndex.{u} n e₂) (h : e₁ + e₂ = e₃) : (MonomialIndex.addOf b c h).1 = b.1 + c.1 :=
  rfl

/-- **The multidegree of the coordinate `Tᵢ`.** -/
def coordIndex {n : ℕ} (i : Fin (n + 1)) : MonomialIndex.{u} n 1 :=
  ⟨Finsupp.single (ULift.up i) 1, by rw [Finsupp.degree_single]; rfl⟩

/-- The monomial of the multidegree of `Tᵢ` is `Tᵢ`. -/
theorem coordMonomial_coordIndex {n : ℕ} (i : Fin (n + 1)) :
    coordMonomial (coordIndex.{u} i) = MvPolynomial.X i := by
  rw [coordMonomial, coordIndex]
  exact congrArg (fun z => MvPolynomial.monomial z (1 : ULift.{u} ℤ))
    (Finsupp.equivMapDomain_single _ _ _)

/-! ### Multiplication by a monomial, with named degrees -/

/-- **Multiplication by a monomial depends on the multidegree alone**, not on the total degree in
which the multidegree is presented. -/
theorem twistOverMulMonomial_congr (n : ℕ) (S : Scheme.{u}) {e₁ e₂ : ℤ}
    (b : MonomialIndex.{u} n e₁) (c : MonomialIndex.{u} n e₂) (hbc : b.1 = c.1) (d g : ℤ)
    (hb : e₁ + d = g) (hc : e₂ + d = g) :
    twistOverMulMonomial n S b d g hb = twistOverMulMonomial n S c d g hc :=
  twistOverMulLeft_congr n S ⟨coordMonomial b, coordMonomial_mem b⟩
    ⟨coordMonomial c, coordMonomial_mem c⟩
    (congrArg (fun z => MvPolynomial.monomial
      (Finsupp.equivMapDomain Equiv.ulift z) (1 : ULift.{u} ℤ)) hbc) d g _ _

/-- **The monomial multiplications compose by adding the multidegrees**, with the total degree of
the product named rather than computed. -/
theorem twistOverMulMonomial_comp' (n : ℕ) (S : Scheme.{u}) {e₁ e₂ e₃ : ℤ}
    (b : MonomialIndex.{u} n e₁) (c : MonomialIndex.{u} n e₂) (d g h : ℤ)
    (hg : e₁ + d = g) (hh : e₂ + g = h) (hadd : e₁ + e₂ = e₃) (hfin : e₃ + d = h) :
    twistOverMulMonomial n S b d g hg ≫ twistOverMulMonomial n S c g h hh =
      twistOverMulMonomial n S (MonomialIndex.addOf b c hadd) d h hfin := by
  rw [twistOverMulMonomial_comp]
  exact twistOverMulMonomial_congr n S (MonomialIndex.add b c) (MonomialIndex.addOf b c hadd)
    rfl d h (by omega) hfin

/-! ### The dual of the degree-`t` part of the polynomial algebra -/

/-- **The direct sum of copies of `𝒪_S` indexed by the multidegrees of total degree `t`.** For a
finite index set a direct sum is a product, so this is the `𝒪_S`-dual of
`(𝒪_S[T₀, …, Tₙ])_t`. -/
abbrev monomialSum (n : ℕ) (S : Scheme.{u}) (t : ℤ) : S.Modules :=
  ⨁ fun _ : MonomialIndex.{u} n t => Scheme.unitModule S

/-- **`monomialSum t` is the `𝒪_S`-dual of `(𝒪_S[T₀, …, Tₙ])_t`.** -/
def monomialSumIsoDual (n : ℕ) (S : Scheme.{u}) (t : ℤ) :
    monomialSum n S t ≅ dualSheaf (baseDegreeSheaf n S t) :=
  biproduct.isoCoproduct (fun _ : MonomialIndex.{u} n t => Scheme.unitModule S) ≪≫
    (dualBaseDegreeSheafIso n S t).symm

/-- **`monomialSum t` vanishes in a negative degree**: there is no multidegree of negative total
degree. -/
theorem isZero_monomialSum_of_neg (n : ℕ) (S : Scheme.{u}) {t : ℤ} (ht : t < 0) :
    IsZero (monomialSum n S t) := by
  have := isEmpty_monomialIndex.{u} n ht
  rw [IsZero.iff_id_eq_zero]
  exact biproduct.hom_ext' _ _ fun b => isEmptyElim b

/-- **The transpose of multiplication by the coordinate `Tᵢ`**: the morphism
`monomialSum t ⟶ monomialSum t'`, for `1 + t' = t`, whose component at a multidegree `b'` of
total degree `t'` is the projection onto the component `b' + δᵢ`. -/
def monomialSumMul (n : ℕ) (S : Scheme.{u}) (i : Fin (n + 1)) (t t' : ℤ) (ht : 1 + t' = t) :
    monomialSum n S t ⟶ monomialSum n S t' :=
  biproduct.lift fun b' => biproduct.π _ (MonomialIndex.addOf (coordIndex i) b' ht)

/-! ### The comparison morphism of the degree-`n` row -/

/-- **The comparison morphism of the degree-`n` row of [Stacks, Tag 01XW]**: the morphism

`Rⁿ f_* 𝒪(d) ⟶ monomialSum t`

whose component at a multidegree `b` of total degree `t` is multiplication by `T^b`, a map to
`Rⁿ f_* 𝒪(-n-1)`, followed by the trace isomorphism of that module with `𝒪_S`. -/
def pairing (m : ℕ) (S : Scheme.{u}) (d t : ℤ) (ht : t + d = -((m + 1 : ℕ) : ℤ) - 1) :
    (push m S (m + 1)).obj (twistOver (m + 1) S d) ⟶ monomialSum (m + 1) S t :=
  biproduct.lift fun b =>
    (push m S (m + 1)).map
      (twistOverMulMonomial (m + 1) S b d (-((m + 1 : ℕ) : ℤ) - 1) ht) ≫ (trace m S).hom

/-- **The comparison morphisms intertwine multiplication by a coordinate with its transpose**:
for `1 + d = d'` and `1 + t' = t`,

`Rⁿ f_*(Tᵢ) ≫ pairing d' t' = pairing d t ≫ (transpose of Tᵢ)`.

Both sides, read at the component of a multidegree `b'` of total degree `t'`, are multiplication
by `T^{b' + δᵢ}` followed by the trace: on the left because the monomial multiplications compose
by adding multidegrees, on the right because the transpose of `Tᵢ` projects onto the component
`b' + δᵢ`. -/
theorem pairing_comp_monomialSumMul (m : ℕ) (S : Scheme.{u}) (i : Fin (m + 1 + 1))
    (d d' t t' : ℤ) (hd : 1 + d = d') (ht : 1 + t' = t)
    (htd : t + d = -((m + 1 : ℕ) : ℤ) - 1) (htd' : t' + d' = -((m + 1 : ℕ) : ℤ) - 1) :
    (push m S (m + 1)).map (twistOverMulMonomial (m + 1) S (coordIndex i) d d' hd) ≫
        pairing m S d' t' htd' =
      pairing m S d t htd ≫ monomialSumMul (m + 1) S i t t' ht := by
  refine biproduct.hom_ext _ _ fun b' => ?_
  simp only [pairing, monomialSumMul, Category.assoc, biproduct.lift_π]
  rw [← Category.assoc, ← Functor.map_comp,
    twistOverMulMonomial_comp' (m + 1) S (coordIndex i) b' d d' (-((m + 1 : ℕ) : ℤ) - 1) hd htd'
      ht htd]

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
