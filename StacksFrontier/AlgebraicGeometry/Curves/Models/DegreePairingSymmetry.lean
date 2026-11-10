module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ModelNumericalType
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Additivity
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0C64]: the degree pairing on a regular proper model is bilinear and symmetric

In the situation of [Stacks, Tag 0C61] let `C₁, …, Cₙ` be the irreducible components of the
special fibre of a regular proper model `X ⟶ Spec(R)` and let `ℒ` be an invertible
`𝒪_X`-module. [Stacks, Tag 0C64] defines the degree pairing

`⟨a, ℒ⟩ = ∑ᵢ aᵢ · deg(ℒ|_{Cᵢ})`  for `a = (a₁, …, aₙ) ∈ ℤⁿ`,

asserts that it is bilinear, and asserts the symmetry

`⟨a, 𝒪_X(∑ⱼ bⱼCⱼ)⟩ = ⟨b, 𝒪_X(∑ᵢ aᵢCᵢ)⟩`  for `a, b ∈ ℤⁿ`.

All three are proved here, with no hypothesis beyond those of [Stacks, Tag 0C61].

## Main definitions

The elided prefix is `Stacks.Models`.

* `verticalDivisorSheaf` — the invertible module `𝒪_X(∑ⱼ bⱼCⱼ)` of an **integer** combination of
  the components, written as the difference twist `𝒪_X(D⁺ - D⁻)` of [Stacks, Tag 01WX] (4) of
  the positive and negative parts of `b`.

## Main results

* `componentDegreeAdditive` — `deg((ℒ ⊗ ℳ)|_{Cᵢ}) = deg(ℒ|_{Cᵢ}) + deg(ℳ|_{Cᵢ})`, the
  invertible case of [Stacks, Tag 0AYX] on a component. This discharges the hypothesis
  `Stacks.Models.ComponentDegreeAdditive` that
  `StacksFrontier/AlgebraicGeometry/Curves/Models/GenusFormula.lean` carries.
* `componentDegree_invertibleSheaf_eq_finrank` — `deg(𝒪_X(D')|_D) = dim_k Γ(D ∩ D', 𝒪)` for an
  integral `D` not contained in `D'`, the second assertion of [Stacks, Tag 0AYY] read on `D`.
* `RegularProperModelSituation.specialFiberIntersectionMatrix_comm` — **the symmetry of the
  intersection matrix**, `(C_Z · C_Y) = (C_Y · C_Z)`. This is the form of the symmetry that
  [Stacks, Tag 0C66] and [Stacks, Tag 0C6A] consume.
* `RegularProperModelSituation.specialFiberDivisorDegree_eq_sum` — the bilinear expansion
  `deg(𝒪_X(∑ⱼ cⱼCⱼ)|_{C_Z}) = ∑ⱼ cⱼ (C_Z · Cⱼ)`, the hypothesis `hexpand` carried elsewhere.
* `RegularProperModelSituation.specialFiberIntersectionProduct_comm` — the symmetry of the
  intersection product of [Stacks, Tag 0C65] on nonnegative coefficient families.
* `RegularProperModelSituation.specialFiberDegreePairing_bilinear_and_comm` — **[Stacks, Tag
  0C64]**: the defining formula for the pairing, its bilinearity, and its symmetry on integer
  combinations of the components. Its fourth clause is **the second displayed equality of
  [Stacks, Tag 0C65] at integer coefficients**, which is why that tag is attached to it as well.
* `RegularProperModelSituation.specialFiberVerticalDivisorSheaf_eq_differenceTwist`,
  `RegularProperModelSituation.specialFiberComponentDegree_specialFiberVerticalDivisorSheaf_eq_sum`
  and
  `RegularProperModelSituation.specialFiberDegreePairing_specialFiberVerticalDivisorSheaf_natCast`
  — the three guards on the integer-coefficient reading: the module is the difference twist of
  [Stacks, Tag 01WX] (4), its degree on `C_Z` is still `∑_Y c_Y (C_Z · C_Y)`, and on a
  nonnegative family the pairing against it is `Stacks.Models.intersectionProduct`.

## Implementation notes

**How the symmetry is proved.** The source reduces to the symmetry of the matrix
`(Cᵢ · Cⱼ) = deg(𝒪_X(Cⱼ)|_{Cᵢ})` by bilinearity, and proves that by identifying both entries
with `deg(Cᵢ ∩ Cⱼ)`. Both steps are run here. For `i ≠ j` the canonical section `1_{Cⱼ}` of
`𝒪_X(Cⱼ)` restricts to a regular section of `𝒪_X(Cⱼ)|_{Cᵢ}` — regular because `Cᵢ` is integral
and is not contained in `Cⱼ`, two distinct irreducible components being incomparable — whose
zero scheme is the scheme-theoretic intersection `Cᵢ ∩ Cⱼ`. The second assertion of
[Stacks, Tag 0AYY], in the shape
`AlgebraicGeometry.invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_unit_zeroScheme`,
then computes the degree as `dim_k H⁰(Cᵢ ∩ Cⱼ, 𝒪)`; and `Cᵢ ∩ Cⱼ` formed inside `Cᵢ` is
isomorphic, over `Spec(k)`, to `Cⱼ ∩ Cᵢ` formed inside `Cⱼ`, both being the fibre product of the
two closed immersions. The case `i = j` is the identity. The diagonal is where the argument
would break if it were run through the intersection alone, and it is why the two sides are
compared only after the off-diagonal reduction.

**The second coefficient family is integer-valued.** `Stacks.Models.intersectionProduct` takes
its second family in `ℕ`, because the library's sum of effective Cartier divisors is the
multiplicative monoid of `AlgebraicGeometry.Scheme.IdealSheafData` whose `Pow` is indexed by
`ℕ`. The source's `b` is in `ℤ`, and `𝒪_X(∑ⱼ bⱼCⱼ)` for such a `b` is the difference twist
`𝒪_X(D⁺ - D⁻) = 𝒪_X(D⁺) ⊗ 𝒪_X(-D⁻)` of [Stacks, Tag 01WX] (4) at the positive and negative
parts of `b`; that is `Stacks.Models.verticalDivisorSheaf`, and the tagged statement below is at
integer coefficients on both sides, as the source is.

**The family of components is indexed by a `Finset`.** `Stacks.Models.degreePairing` sums over a
`Finset` of the index type, and the tagged statement inherits that. Taking it to be
`Finset.univ` of the (finite) set of irreducible components of the special fibre recovers the
source's `∑_{i=1}^n`; no finiteness of the index type is needed for the statement or its proof,
so none is assumed.

## References

* [Stacks Project, Tag 0C64](https://stacks.math.columbia.edu/tag/0C64)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C65](https://stacks.math.columbia.edu/tag/0C65)
* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Divisors (IsEffectiveCartierDivisor)

universe u

namespace Stacks.Models

/-! ### Additivity of the component degree in the tensor product -/

section Additive

variable (S : RegularProperModelSituation.{u}) {ι : Type*} (C : ι → S.X.IdealSheafData)
  (g : ∀ i, (C i).subscheme ⟶ Spec (.of S.k)) (hg : ∀ i, IsProper (g i))
  (hdim : ∀ i, topologicalKrullDim (C i).subscheme ≤ 1)

/-- **The invertible case of [Stacks, Tag 0AYX] on a component of the special fibre**,
`deg((ℒ ⊗ ℳ)|_{Cᵢ}) = deg(ℒ|_{Cᵢ}) + deg(ℳ|_{Cᵢ})`, with no hypothesis.

The component is a closed subscheme of `X`, proper of dimension at most one over the residue
field, so this is `Stacks.Models.componentDegree_tensorSheaf_eq_add` read at `Cᵢ`. It discharges
the hypothesis `Stacks.Models.ComponentDegreeAdditive`. -/
theorem componentDegreeAdditive (i : ι) : ComponentDegreeAdditive S C g hg hdim i :=
  fun L M hL hM hLM =>
    componentDegree_tensorSheaf_eq_add S.k (C i) (g i) (hg i) (hdim i) L M hL hM hLM

/-- **The degree pairing is additive in the invertible module**,
`⟨a, ℒ ⊗ ℳ⟩ = ⟨a, ℒ⟩ + ⟨a, ℳ⟩`. With
`Stacks.Models.degreePairing_add` this is the bilinearity asserted by [Stacks, Tag 0C64]. -/
theorem degreePairing_tensorSheaf (s : Finset ι) (a : ι → ℤ) (L M : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L)
    (hM : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property M)
    (hLM : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(S.X.toRingedSpace).presheaf, (S.X.toRingedSpace).IsSheaf⟩).obj (L)).obj (M)))) :
    degreePairing S s C g hg hdim a ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(S.X.toRingedSpace).presheaf, (S.X.toRingedSpace).IsSheaf⟩).obj (L)).obj (M))) hLM =
      degreePairing S s C g hg hdim a L hL + degreePairing S s C g hg hdim a M hM := by
  simp only [degreePairing]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [componentDegreeAdditive S C g hg hdim j L M hL hM hLM, mul_add]

end Additive

/-! ### The bilinear expansion of the degree of a divisor sheaf -/

section Expansion

variable (S : RegularProperModelSituation.{u}) {ι : Type*} (C : ι → S.X.IdealSheafData)
  (g : ∀ i, (C i).subscheme ⟶ Spec (.of S.k)) (hg : ∀ i, IsProper (g i))
  (hdim : ∀ i, topologicalKrullDim (C i).subscheme ≤ 1) (i : ι)

/-- Equal divisors have equal degrees on a component. The two invertibility arguments are
unconstrained: `Stacks.Models.componentDegree` does not depend on them, invertibility being a
proposition. -/
theorem componentDegree_invertibleSheaf_congr {D D' : S.X.IdealSheafData} (h : D = D')
    (h₁ : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property (Stacks.Divisors.invertibleSheaf' D))
    (h₂ : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property (Stacks.Divisors.invertibleSheaf' D')) :
    componentDegree S.k (C i) (g i) (hg i) (hdim i) (Stacks.Divisors.invertibleSheaf' D) h₁ =
      componentDegree S.k (C i) (g i) (hg i) (hdim i) (Stacks.Divisors.invertibleSheaf' D') h₂ := by
  subst h
  rfl

/-- **The empty divisor has degree zero on a component**: `𝒪_X(∅) ≅ 𝒪_X`. -/
theorem componentDegree_invertibleSheaf_top
    (h₁ : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property
      (Stacks.Divisors.invertibleSheaf' (⊤ : S.X.IdealSheafData))) :
    componentDegree S.k (C i) (g i) (hg i) (hdim i)
      (Stacks.Divisors.invertibleSheaf' (⊤ : S.X.IdealSheafData)) h₁ = 0 := by
  rw [componentDegree_eq_of_iso S.k (C i) (g i) (hg i) (hdim i) _
    (SheafOfModules.unit S.X.ringCatSheaf) h₁ (isTensorInvertible_unit S.X)
    Stacks.Divisors.invertibleSheafTopIsoUnit]
  exact componentDegree_unit_eq_zero S.k (C i) (g i) (hg i) (hdim i) (isTensorInvertible_unit S.X)

/-- **The degree on a component is additive in the divisor**,
`deg(𝒪_X(D + D')|_{Cᵢ}) = deg(𝒪_X(D)|_{Cᵢ}) + deg(𝒪_X(D')|_{Cᵢ})`: the sum of divisors is the
tensor product of their sheaves ([Stacks, Tag 02OP]) and the degree is additive in the tensor
product ([Stacks, Tag 0AYX]). -/
theorem componentDegree_invertibleSheaf_mul (D D' : S.X.IdealSheafData)
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D']
    (h₁ : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property (Stacks.Divisors.invertibleSheaf' (D * D')))
    (h₂ : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property (Stacks.Divisors.invertibleSheaf' D))
    (h₃ : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property (Stacks.Divisors.invertibleSheaf' D')) :
    componentDegree S.k (C i) (g i) (hg i) (hdim i)
          (Stacks.Divisors.invertibleSheaf' (D * D')) h₁ =
      componentDegree S.k (C i) (g i) (hg i) (hdim i) (Stacks.Divisors.invertibleSheaf' D) h₂ +
        componentDegree S.k (C i) (g i) (hg i) (hdim i)
          (Stacks.Divisors.invertibleSheaf' D') h₃ := by
  have := h₂
  have := h₃
  have hLM : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(S.X.toRingedSpace).presheaf, (S.X.toRingedSpace).IsSheaf⟩).obj
          ((Stacks.Divisors.invertibleSheaf' D))).obj ((Stacks.Divisors.invertibleSheaf' D')))) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _
  rw [← componentDegreeAdditive S C g hg hdim i (Stacks.Divisors.invertibleSheaf' D)
    (Stacks.Divisors.invertibleSheaf' D') h₂ h₃ hLM]
  exact componentDegree_eq_of_iso S.k (C i) (g i) (hg i) (hdim i) _ _ h₁ hLM
    (Stacks.Divisors.invertibleSheafSumIso D D').symm

/-- A divisor equal to `⊤` has degree zero on a component. -/
private theorem componentDegree_invertibleSheaf_eq_zero_of_eq_top {D : S.X.IdealSheafData}
    (h : D = ⊤) (h₁ : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property (Stacks.Divisors.invertibleSheaf' D)) :
    componentDegree S.k (C i) (g i) (hg i) (hdim i) (Stacks.Divisors.invertibleSheaf' D) h₁ =
      0 := by
  subst h
  exact componentDegree_invertibleSheaf_top S C g hg hdim i h₁

/-- The degree on a component of the sheaf of a divisor `E = D * D'` is the sum of the degrees. -/
private theorem componentDegree_invertibleSheaf_eq_add {D D' E : S.X.IdealSheafData}
    [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor D'] (h : E = D * D')
    (h₁ : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property (Stacks.Divisors.invertibleSheaf' E)) :
    componentDegree S.k (C i) (g i) (hg i) (hdim i) (Stacks.Divisors.invertibleSheaf' E) h₁ =
      componentDegree S.k (C i) (g i) (hg i) (hdim i) (Stacks.Divisors.invertibleSheaf' D)
          (Stacks.Divisors.isTensorInvertible_invertibleSheaf D) +
        componentDegree S.k (C i) (g i) (hg i) (hdim i) (Stacks.Divisors.invertibleSheaf' D')
          (Stacks.Divisors.isTensorInvertible_invertibleSheaf D') := by
  subst h
  exact componentDegree_invertibleSheaf_mul S C g hg hdim i D D' h₁ _ _

/-- **The degree on a component is homogeneous in the divisor**,
`deg(𝒪_X(nD)|_{Cᵢ}) = n · deg(𝒪_X(D)|_{Cᵢ})`. -/
theorem componentDegree_invertibleSheaf_pow (D : S.X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (n : ℕ)
    (h₁ : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property (Stacks.Divisors.invertibleSheaf' (D ^ n)))
    (h₂ : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property (Stacks.Divisors.invertibleSheaf' D)) :
    componentDegree S.k (C i) (g i) (hg i) (hdim i)
        (Stacks.Divisors.invertibleSheaf' (D ^ n)) h₁ =
      (n : ℤ) * componentDegree S.k (C i) (g i) (hg i) (hdim i)
        (Stacks.Divisors.invertibleSheaf' D) h₂ := by
  induction n with
  | zero =>
      rw [Nat.cast_zero, zero_mul]
      exact componentDegree_invertibleSheaf_eq_zero_of_eq_top S C g hg hdim i
        ((pow_zero D).trans Scheme.IdealSheafData.one_eq_top) h₁
  | succ n ih =>
      have hpow := Stacks.Divisors.isTensorInvertible_invertibleSheaf (D ^ n)
      rw [componentDegree_invertibleSheaf_eq_add S C g hg hdim i (pow_succ D n) h₁, ih hpow,
        Nat.cast_add, Nat.cast_one]
      ring

/-- **The bilinear expansion of the degree of a nonnegative combination of divisors**,
`deg(𝒪_X(∑ⱼ cⱼCⱼ)|_{Cᵢ}) = ∑ⱼ cⱼ · deg(𝒪_X(Cⱼ)|_{Cᵢ})`. This is the expansion the proof of
[Stacks, Tag 0C64] obtains from [Stacks, Tag 0AYX]. -/
theorem componentDegree_invertibleSheaf_prod
    (hC : ∀ j, IsEffectiveCartierDivisor (C j)) (s : Finset ι) (c : ι → ℕ)
    (h₁ : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property
      (Stacks.Divisors.invertibleSheaf' (∏ j ∈ s, C j ^ c j)))
    (h₂ : ∀ j, Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property (Stacks.Divisors.invertibleSheaf' (C j))) :
    componentDegree S.k (C i) (g i) (hg i) (hdim i)
        (Stacks.Divisors.invertibleSheaf' (∏ j ∈ s, C j ^ c j)) h₁ =
      ∑ j ∈ s, (c j : ℤ) * componentDegree S.k (C i) (g i) (hg i) (hdim i)
        (Stacks.Divisors.invertibleSheaf' (C j)) (h₂ j) := by
  classical
  have : ∀ j, IsEffectiveCartierDivisor (C j) := hC
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact componentDegree_invertibleSheaf_eq_zero_of_eq_top S C g hg hdim i
        (Finset.prod_empty.trans Scheme.IdealSheafData.one_eq_top) h₁
  | insert a t ha ih =>
      have hT := Stacks.Divisors.isTensorInvertible_invertibleSheaf (∏ j ∈ t, C j ^ c j)
      rw [componentDegree_invertibleSheaf_eq_add S C g hg hdim i (Finset.prod_insert ha) h₁,
        componentDegree_invertibleSheaf_pow S C g hg hdim i (C a) (c a) _ (h₂ a), ih hT,
        Finset.sum_insert ha]

/-- **`𝒪_X(∑ⱼ bⱼCⱼ)` for an integer coefficient family `b`**: the difference twist
`𝒪_X(D⁺ - D⁻) = 𝒪_X(D⁺) ⊗ 𝒪_X(-D⁻)` of [Stacks, Tag 01WX] (4) at the positive part
`D⁺ = ∑ⱼ max(bⱼ,0)Cⱼ` and the negative part `D⁻ = ∑ⱼ max(-bⱼ,0)Cⱼ` of `b`. -/
def verticalDivisorSheaf (s : Finset ι) (b : ι → ℤ) : S.X.Modules :=
  Stacks.Divisors.differenceTwist' (∏ j ∈ s, C j ^ (b j).toNat)
    (∏ j ∈ s, C j ^ (-b j).toNat)

/-- `𝒪_X(∑ⱼ bⱼCⱼ)` is invertible, being a tensor product of an invertible sheaf of a divisor and
the ideal sheaf of a divisor. -/
theorem isInvertible_verticalDivisorSheaf (hC : ∀ j, IsEffectiveCartierDivisor (C j))
    (s : Finset ι) (b : ι → ℤ) :
    Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property (verticalDivisorSheaf S C s b) := by
  have : ∀ j, IsEffectiveCartierDivisor (C j) := hC
  have := Stacks.Divisors.isTensorInvertible_invertibleSheaf (∏ j ∈ s, C j ^ (b j).toNat)
  have := Stacks.Divisors.isTensorInvertible_negativeTwist (∏ j ∈ s, C j ^ (-b j).toNat)
  exact Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _

/-- **The bilinear expansion at integer coefficients**,
`deg(𝒪_X(∑ⱼ bⱼCⱼ)|_{Cᵢ}) = ∑ⱼ bⱼ · deg(𝒪_X(Cⱼ)|_{Cᵢ})` for `b ∈ ℤ^ι`. The positive part
expands by `Stacks.Models.componentDegree_invertibleSheaf_prod` and the negative part by the same
with a sign, `deg(𝒪_X(-D)|_{Cᵢ}) = -deg(𝒪_X(D)|_{Cᵢ})`. -/
theorem componentDegree_verticalDivisorSheaf_eq_sum
    (hC : ∀ j, IsEffectiveCartierDivisor (C j)) (s : Finset ι) (b : ι → ℤ)
    (h₁ : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property (verticalDivisorSheaf S C s b))
    (h₂ : ∀ j, Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property (Stacks.Divisors.invertibleSheaf' (C j))) :
    componentDegree S.k (C i) (g i) (hg i) (hdim i) (verticalDivisorSheaf S C s b) h₁ =
      ∑ j ∈ s, b j * componentDegree S.k (C i) (g i) (hg i) (hdim i)
        (Stacks.Divisors.invertibleSheaf' (C j)) (h₂ j) := by
  have : ∀ j, IsEffectiveCartierDivisor (C j) := hC
  have hPcd : IsEffectiveCartierDivisor (∏ j ∈ s, C j ^ (b j).toNat) :=
    Stacks.Divisors.isEffectiveCartierDivisor_prod s C _ fun j _ => hC j
  have hNcd : IsEffectiveCartierDivisor (∏ j ∈ s, C j ^ (-b j).toNat) :=
    Stacks.Divisors.isEffectiveCartierDivisor_prod s C _ fun j _ => hC j
  have hP : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property
      (Stacks.Divisors.invertibleSheaf' (∏ j ∈ s, C j ^ (b j).toNat)) :=
    Stacks.Divisors.isTensorInvertible_invertibleSheaf _
  have hN : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property
      (Stacks.Divisors.invertibleSheaf' (∏ j ∈ s, C j ^ (-b j).toNat)) :=
    Stacks.Divisors.isTensorInvertible_invertibleSheaf _
  have hNneg : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property
      (Stacks.Divisors.negativeTwist' (∏ j ∈ s, C j ^ (-b j).toNat)) :=
    Stacks.Divisors.isTensorInvertible_negativeTwist _
  have hPN : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(S.X.toRingedSpace).presheaf, (S.X.toRingedSpace).IsSheaf⟩).obj
          ((Stacks.Divisors.invertibleSheaf' (∏ j ∈ s, C j ^ (b j).toNat)))).obj
          ((Stacks.Divisors.negativeTwist' (∏ j ∈ s, C j ^ (-b j).toNat))))) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _
  have hsplit : componentDegree S.k (C i) (g i) (hg i) (hdim i)
        (verticalDivisorSheaf S C s b) h₁ =
      componentDegree S.k (C i) (g i) (hg i) (hdim i)
          (Stacks.Divisors.invertibleSheaf' (∏ j ∈ s, C j ^ (b j).toNat)) hP +
        componentDegree S.k (C i) (g i) (hg i) (hdim i)
          (Stacks.Divisors.negativeTwist' (∏ j ∈ s, C j ^ (-b j).toNat)) hNneg :=
    componentDegreeAdditive S C g hg hdim i _ _ hP hNneg hPN
  have hneg : componentDegree S.k (C i) (g i) (hg i) (hdim i)
        (Stacks.Divisors.negativeTwist' (∏ j ∈ s, C j ^ (-b j).toNat)) hNneg =
      -componentDegree S.k (C i) (g i) (hg i) (hdim i)
        (Stacks.Divisors.invertibleSheaf' (∏ j ∈ s, C j ^ (-b j).toNat)) hN :=
    componentDegree_negativeTwist_eq_neg S C g hg hdim i _ hNcd
  rw [hsplit, hneg, componentDegree_invertibleSheaf_prod S C g hg hdim i hC s _ hP h₂,
    componentDegree_invertibleSheaf_prod S C g hg hdim i hC s _ hN h₂,
    ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← sub_mul, Int.toNat_sub_toNat_neg]

end Expansion

/-! ### The degree of `𝒪_X(D')` on a closed subscheme is the degree of the intersection -/

/-- **The degree of `𝒪_X(D')` on a closed subscheme `D` is the dimension of `H⁰` of the
scheme-theoretic intersection `D ∩ D'`**, for `D` integral, proper of dimension at most one over
`k` and not contained in `D'`.

This is the second assertion of [Stacks, Tag 0AYY] read on `D`: the canonical section `1_{D'}`
restricts to a regular section of `𝒪_X(D')|_D` whose zero scheme is `D ∩ D'`, and the degree of
an invertible module with a regular section is the dimension of `H⁰` of the structure sheaf of
that section's zero scheme. -/
theorem componentDegree_invertibleSheaf_eq_finrank (k : Type u) [Field k] {X : Scheme.{u}}
    (D D' : X.IdealSheafData) [IsEffectiveCartierDivisor D']
    (g : D.subscheme ⟶ Spec (.of k)) (hg : IsProper g)
    (hdim : topologicalKrullDim D.subscheme ≤ 1)
    (hD : IsIntegral D.subscheme) (hle : ¬ D' ≤ D) :
    componentDegree k D g hg hdim (Stacks.Divisors.invertibleSheaf' D')
        (Stacks.Divisors.isTensorInvertible_invertibleSheaf D') =
      (Module.finrank k (cohomologyOverField k ((D'.comap D.subschemeι).subschemeι ≫ g)
        (SheafOfModules.unit (D'.comap D.subschemeι).subscheme.ringCatSheaf) 0) : ℤ) := by
  have := hg
  have key := invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_unit_zeroScheme k g hdim
    ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.modulesInvertibleSheaf D'))
    (restrictCanonicalSection D D')
    (isRegularSection_restrictCanonicalSection D D' hD hle)
  rw [zeroScheme_restrictCanonicalSection D D'] at key
  exact key

/-! ### Distinct components of the special fibre are incomparable -/

namespace RegularModelSituation

variable (S : RegularModelSituation.{u})

/-- **Two distinct irreducible components of the special fibre are incomparable**: the reduced
ideal sheaf of one is not contained in that of the other. Containment of ideal sheaves is reverse
containment of supports, the support of a component ideal is the image of the component, and an
irreducible component is maximal among irreducible closed subsets. -/
theorem not_specialFiberComponentIdeal_le (Z Z' : irreducibleComponents S.specialFiber)
    (hne : Z ≠ Z') :
    ¬ (S.specialFiberComponentIdeal Z' ≤ S.specialFiberComponentIdeal Z) := by
  intro hle
  have hsupp := Scheme.IdealSheafData.support_antitone hle
  have h1 : S.specialFiberι.base '' (Z.1 : Set S.specialFiber) ⊆
      S.specialFiberι.base '' (Z'.1 : Set S.specialFiber) := by
    rw [← S.coe_support_specialFiberComponentIdeal Z,
      ← S.coe_support_specialFiberComponentIdeal Z']
    exact hsupp
  have h2 : (Z.1 : Set S.specialFiber) ⊆ (Z'.1 : Set S.specialFiber) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := h1 ⟨x, hx, rfl⟩
    rwa [S.specialFiberι.isClosedEmbedding.injective hxy] at hy
  exact hne (Subtype.ext (le_antisymm h2 (Z.2.2 Z'.2.1 h2)))

end RegularModelSituation

/-! ### The symmetry of the intersection matrix -/

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- The two readings of the intersection `C_Z ∩ C_Y` of two components are isomorphic over the
residue field: the two closed immersions into `X` factor through the closed immersion of the
special fibre, which is a monomorphism, so the two structure morphisms over `k` agree. -/
theorem specialFiberComponentToSpec_comapCommIso
    (Z Z' : irreducibleComponents S.specialFiber) :
    ((comapCommIso (S.specialFiberComponentIdeal Z)
          (S.specialFiberComponentIdeal Z')).hom ≫
        ((S.specialFiberComponentIdeal Z).comap
          (S.specialFiberComponentIdeal Z').subschemeι).subschemeι) ≫
        S.specialFiberComponentToSpec Z' =
      ((S.specialFiberComponentIdeal Z').comap
        (S.specialFiberComponentIdeal Z).subschemeι).subschemeι ≫
          S.specialFiberComponentToSpec Z := by
  set p := ((S.specialFiberComponentIdeal Z').comap
    (S.specialFiberComponentIdeal Z).subschemeι).subschemeι with hp
  set q := (comapCommIso (S.specialFiberComponentIdeal Z)
      (S.specialFiberComponentIdeal Z')).hom ≫
    ((S.specialFiberComponentIdeal Z).comap
      (S.specialFiberComponentIdeal Z').subschemeι).subschemeι with hq
  have h : p ≫ (S.specialFiberComponentIdeal Z).subschemeι =
      q ≫ (S.specialFiberComponentIdeal Z').subschemeι :=
    comapCommIso_compat _ _
  have h3 : (p ≫ S.specialFiberComponentι Z) ≫ S.specialFiberι =
      (q ≫ S.specialFiberComponentι Z') ≫ S.specialFiberι := by
    rw [Category.assoc, Category.assoc, S.specialFiberComponentι_specialFiberι Z,
      S.specialFiberComponentι_specialFiberι Z']
    exact h
  have h4 : p ≫ S.specialFiberComponentι Z = q ≫ S.specialFiberComponentι Z' :=
    (cancel_mono S.specialFiberι).mp h3
  change q ≫ (S.specialFiberComponentι Z' ≫ S.specialFiberToSpec) =
    p ≫ (S.specialFiberComponentι Z ≫ S.specialFiberToSpec)
  rw [← Category.assoc, ← Category.assoc, h4]

/-- **The degree of `𝒪_X(C_Y)` on a distinct component `C_Z` is the dimension of `H⁰` of the
intersection `C_Z ∩ C_Y`**, the second assertion of [Stacks, Tag 0AYY] at the two components. -/
theorem componentDegree_specialFiberComponent_eq_finrank
    (Z Z' : irreducibleComponents S.specialFiber) (hne : Z ≠ Z') :
    componentDegree S.k (S.specialFiberComponentIdeal Z) (S.specialFiberComponentToSpec Z)
        (S.isProper_specialFiberComponentToSpec Z)
        (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
        (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z'))
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
          (S.isEffectiveCartierDivisor_specialFiberComponent Z')) =
      (Module.finrank S.k (cohomologyOverField S.k
        (((S.specialFiberComponentIdeal Z').comap
            (S.specialFiberComponentIdeal Z).subschemeι).subschemeι ≫
          S.specialFiberComponentToSpec Z)
        (SheafOfModules.unit ((S.specialFiberComponentIdeal Z').comap
          (S.specialFiberComponentIdeal Z).subschemeι).subscheme.ringCatSheaf) 0) : ℤ) := by
  have := S.isEffectiveCartierDivisor_specialFiberComponent Z'
  exact componentDegree_invertibleSheaf_eq_finrank S.k _ _ _
    (S.isProper_specialFiberComponentToSpec Z)
    (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
    (S.toRegularModelSituation.isIntegral_specialFiberComponentIdeal Z)
    (S.toRegularModelSituation.not_specialFiberComponentIdeal_le Z Z' hne)

/-- **Stacks Project, Tag 0C64, the symmetry of the intersection matrix.** For two irreducible
components of the special fibre of a regular proper model,

`deg(𝒪_X(C_Y)|_{C_Z}) = deg(𝒪_X(C_Z)|_{C_Y})`.

For `Z = Y` the two sides are the same expression. For `Z ≠ Y` both are the dimension over `k`
of `H⁰` of the scheme-theoretic intersection `C_Z ∩ C_Y`, by the second assertion of
[Stacks, Tag 0AYY]; the intersection does not depend on which component it is formed inside, and
the two structure morphisms over `k` agree on it because both factor through the special
fibre. -/
theorem componentDegree_specialFiberComponent_comm
    (Z Z' : irreducibleComponents S.specialFiber) :
    componentDegree S.k (S.specialFiberComponentIdeal Z) (S.specialFiberComponentToSpec Z)
        (S.isProper_specialFiberComponentToSpec Z)
        (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
        (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z'))
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
          (S.isEffectiveCartierDivisor_specialFiberComponent Z')) =
      componentDegree S.k (S.specialFiberComponentIdeal Z') (S.specialFiberComponentToSpec Z')
        (S.isProper_specialFiberComponentToSpec Z')
        (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z')
        (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z))
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
          (S.isEffectiveCartierDivisor_specialFiberComponent Z)) := by
  rcases eq_or_ne Z Z' with rfl | hne
  · rfl
  · rw [S.componentDegree_specialFiberComponent_eq_finrank Z Z' hne,
      S.componentDegree_specialFiberComponent_eq_finrank Z' Z hne.symm]
    exact congrArg _ (finrank_cohomologyOverField_comap_comm (S.specialFiberComponentIdeal Z)
      (S.specialFiberComponentIdeal Z') S.k (S.specialFiberComponentToSpec Z)
      (S.specialFiberComponentToSpec Z') (S.specialFiberComponentToSpec_comapCommIso Z Z'))

section Fintype

variable [Fintype (irreducibleComponents S.specialFiber)]
  [DecidableEq (irreducibleComponents S.specialFiber)]

/-- The intersection matrix of the special fibre is the degree of the invertible sheaf of a
single component on another, `(C_Z · C_Y) = deg(𝒪_X(C_Y)|_{C_Z})`: the divisor
`∑_W (eᵁ)_W C_W` of the basis vector at `Y` is `C_Y`. -/
theorem specialFiberIntersectionMatrix_eq_componentDegree
    (Z Y : irreducibleComponents S.specialFiber) :
    S.specialFiberIntersectionMatrix Z Y =
      componentDegree S.k (S.specialFiberComponentIdeal Z) (S.specialFiberComponentToSpec Z)
        (S.isProper_specialFiberComponentToSpec Z)
        (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
        (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Y))
        (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
          (S.isEffectiveCartierDivisor_specialFiberComponent Y)) := by
  have hprod : (∏ W, S.specialFiberComponentIdeal W ^
        (Pi.single Y 1 : irreducibleComponents S.specialFiber → ℕ) W) =
      S.specialFiberComponentIdeal Y := by
    rw [Finset.prod_eq_single_of_mem Y (Finset.mem_univ Y)
      (fun W _ hW => by rw [Pi.single_eq_of_ne hW, pow_zero]), Pi.single_eq_same, pow_one]
  exact componentDegree_invertibleSheaf_congr S (fun W => S.specialFiberComponentIdeal W)
    (fun W => S.specialFiberComponentToSpec W)
    (fun W => S.isProper_specialFiberComponentToSpec W)
    (fun W => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent W) Z hprod
    (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
      (Stacks.Divisors.isEffectiveCartierDivisor_prod Finset.univ
        (fun W => S.specialFiberComponentIdeal W) (Pi.single Y 1)
        (fun W _ => S.isEffectiveCartierDivisor_specialFiberComponent W)))
    (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
      (S.isEffectiveCartierDivisor_specialFiberComponent Y))

/-- **Stacks Project, Tag 0C64, the symmetry of the intersection matrix**, in the spelling
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionMatrix`:
`(C_Z · C_Y) = (C_Y · C_Z)`. -/
theorem specialFiberIntersectionMatrix_comm (Z Y : irreducibleComponents S.specialFiber) :
    S.specialFiberIntersectionMatrix Z Y = S.specialFiberIntersectionMatrix Y Z := by
  rw [S.specialFiberIntersectionMatrix_eq_componentDegree Z Y,
    S.specialFiberIntersectionMatrix_eq_componentDegree Y Z]
  exact S.componentDegree_specialFiberComponent_comm Z Y

/-- **The bilinear expansion on the components of the special fibre**,
`deg(𝒪_X(∑_Y c_Y C_Y)|_{C_Z}) = ∑_Y c_Y (C_Z · C_Y)`. This is the hypothesis `hexpand` that
`Stacks.Models.RegularProperModelSituation.specialFiberNumericalType` and
`Stacks.Models.intersectionProduct_comm_of_expansion_of_matrix_symm` carry; it is the invertible
case of [Stacks, Tag 0AYX], unconditional in this library. -/
theorem specialFiberDivisorDegree_eq_sum (Z : irreducibleComponents S.specialFiber)
    (c : irreducibleComponents S.specialFiber → ℕ) :
    S.specialFiberDivisorDegree Z c = ∑ Y, (c Y : ℤ) * S.specialFiberIntersectionMatrix Z Y := by
  refine (componentDegree_invertibleSheaf_prod S (fun W => S.specialFiberComponentIdeal W)
    (fun W => S.specialFiberComponentToSpec W)
    (fun W => S.isProper_specialFiberComponentToSpec W)
    (fun W => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent W) Z
    (fun W => S.isEffectiveCartierDivisor_specialFiberComponent W) Finset.univ c
    (isInvertible_divisorSheaf S Finset.univ (fun W => S.specialFiberComponentIdeal W) c
      (fun W _ => S.isEffectiveCartierDivisor_specialFiberComponent W))
    (fun W => @Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
      (S.isEffectiveCartierDivisor_specialFiberComponent W))).trans
    (Finset.sum_congr rfl fun Y _ => ?_)
  rw [S.specialFiberIntersectionMatrix_eq_componentDegree Z Y]

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- **Stacks Project, Tag 0C65, second equality**, on nonnegative coefficient families: the
intersection product of the components of the special fibre is symmetric,
`(∑_Z a_Z C_Z · ∑_Y b_Y C_Y) = (∑_Y b_Y C_Y · ∑_Z a_Z C_Z)`.

This is `Stacks.Models.intersectionProduct_comm_of_expansion_of_matrix_symm` with both of its
hypotheses discharged: `hexpand` by
`Stacks.Models.RegularProperModelSituation.specialFiberDivisorDegree_eq_sum` and `hsymm` by
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionMatrix_comm`. -/
@[stacks 0C65 "the second displayed equality, the symmetry \
⟨a, O_X(∑ b_Y C_Y)⟩ = ⟨b, O_X(∑ a_Z C_Z)⟩, at the irreducible components of the special fibre \
and on nonnegative coefficient families; at integer coefficients it is the fourth clause of \
Stacks.Models.RegularProperModelSituation.specialFiberDegreePairing_bilinear_and_comm"]
theorem specialFiberIntersectionProduct_comm
    (a b : irreducibleComponents S.specialFiber → ℕ) :
    S.specialFiberIntersectionProduct (fun Z => (a Z : ℤ)) b =
      S.specialFiberIntersectionProduct (fun Z => (b Z : ℤ)) a :=
  intersectionProduct_comm_of_expansion_of_matrix_symm S Finset.univ
    (fun W => S.specialFiberComponentIdeal W) (fun W => S.specialFiberComponentToSpec W)
    (fun W => S.isProper_specialFiberComponentToSpec W)
    (fun W => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent W)
    S.specialFiberIntersectionMatrix a b
    (fun W _ => S.isEffectiveCartierDivisor_specialFiberComponent W)
    (fun c Z _ => S.specialFiberDivisorDegree_eq_sum Z c)
    (fun Z _ Y _ => S.specialFiberIntersectionMatrix_comm Z Y)

end Fintype

/-! ### The whole of Tag 0C64 -/

/-- **`𝒪_X(∑_Z b_Z C_Z)` for an integer family on the components of the special fibre.** -/
def specialFiberVerticalDivisorSheaf (s : Finset (irreducibleComponents S.specialFiber))
    (b : irreducibleComponents S.specialFiber → ℤ) : S.X.Modules :=
  verticalDivisorSheaf S (fun Z => S.specialFiberComponentIdeal Z) s b

/-- `𝒪_X(∑_Z b_Z C_Z)` is invertible. -/
theorem isInvertible_specialFiberVerticalDivisorSheaf
    (s : Finset (irreducibleComponents S.specialFiber))
    (b : irreducibleComponents S.specialFiber → ℤ) :
    Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property
      (S.specialFiberVerticalDivisorSheaf s b) :=
  isInvertible_verticalDivisorSheaf S (fun Z => S.specialFiberComponentIdeal Z)
    (fun Z => S.isEffectiveCartierDivisor_specialFiberComponent Z) s b

end RegularProperModelSituation

/-- The double sum of a symmetric matrix against two coefficient families is unchanged by
exchanging the families. -/
private theorem sum_sum_mul_comm_of_symm {ι : Type*} (s : Finset ι) (a b : ι → ℤ)
    (M : ι → ι → ℤ) (hM : ∀ x y, M x y = M y x) :
    ∑ x ∈ s, ∑ y ∈ s, a x * b y * M x y = ∑ x ∈ s, ∑ y ∈ s, b x * a y * M x y := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [hM y x]; ring

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **Stacks Project, Tag 0C64.** In the situation of [Stacks, Tag 0C61], let `C_Z` run over the
irreducible components of the special fibre of the regular proper model `X ⟶ Spec(R)`, each with
its reduced induced structure as a closed subscheme of `X`. For an invertible `𝒪_X`-module `ℒ`
and an integer family `a` the degree pairing is

`⟨a, ℒ⟩ = ∑_Z a_Z · deg(ℒ|_{C_Z})`;

it is bilinear, and for integer families `a` and `b`

`⟨a, 𝒪_X(∑_Y b_Y C_Y)⟩ = ⟨b, 𝒪_X(∑_Z a_Z C_Z)⟩`.

The four clauses are, in order: the defining formula for the pairing, additivity in the
coefficient family, additivity in the invertible module — the Picard group being written
multiplicatively, so that addition of its elements is the tensor product — and the symmetry.
The third is the invertible case of [Stacks, Tag 0AYX] on each component, and the fourth is
proved as the source proves it: expand both sides by the first three clauses and appeal to the
symmetry of the intersection matrix
`deg(𝒪_X(C_Y)|_{C_Z}) = deg(𝒪_X(C_Z)|_{C_Y})`, which is
`Stacks.Models.RegularProperModelSituation.componentDegree_specialFiberComponent_comm`. -/
@[stacks 0C64 "the pairing ⟨a, L⟩ = ∑ a_Z deg(L|_{C_Z}), its bilinearity, and the symmetry \
⟨a, O_X(∑ b_Y C_Y)⟩ = ⟨b, O_X(∑ a_Z C_Z)⟩ at integer coefficients",
  stacks 0C65 "the second displayed equality ⟨a, O_X(∑ b_Y C_Y)⟩ = ⟨b, O_X(∑ a_Z C_Z)⟩ at \
INTEGER coefficient families a, b, which is the fourth clause. Here O_X(∑ b_Y C_Y) is \
Stacks.Models.RegularProperModelSituation.specialFiberVerticalDivisorSheaf, the difference twist \
of Stacks 01WX part (4) at the positive and negative parts of b; its degree on C_Z is \
∑_Y b_Y (C_Z · C_Y) by \
Stacks.Models.RegularProperModelSituation.\
specialFiberComponentDegree_specialFiberVerticalDivisorSheaf_eq_sum, \
and on a nonnegative family the pairing against it is the intersection product \
Stacks.Models.intersectionProduct of the first displayed equality, by \
Stacks.Models.RegularProperModelSituation.\
specialFiberDegreePairing_specialFiberVerticalDivisorSheaf_natCast"]
theorem specialFiberDegreePairing_bilinear_and_comm
    (s : Finset (irreducibleComponents S.specialFiber)) :
    (∀ (a : irreducibleComponents S.specialFiber → ℤ) (L : S.X.Modules)
        (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
          (structureSheafRing S.X.toRingedSpace).property L),
        S.specialFiberDegreePairing s a L hL =
          ∑ Z ∈ s, a Z * S.specialFiberComponentDegree Z L hL) ∧
      (∀ (a a' : irreducibleComponents S.specialFiber → ℤ) (L : S.X.Modules)
        (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
          (structureSheafRing S.X.toRingedSpace).property L),
        S.specialFiberDegreePairing s (a + a') L hL =
          S.specialFiberDegreePairing s a L hL + S.specialFiberDegreePairing s a' L hL) ∧
      (∀ (a : irreducibleComponents S.specialFiber → ℤ) (L M : S.X.Modules)
        (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
          (structureSheafRing S.X.toRingedSpace).property L)
        (hM : Stacks.SheafOfModules.IsInvertible S.X.presheaf
          (structureSheafRing S.X.toRingedSpace).property M)
        (hLM : Stacks.SheafOfModules.IsInvertible S.X.presheaf
          (structureSheafRing S.X.toRingedSpace).property
            ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨(S.X.toRingedSpace).presheaf, (S.X.toRingedSpace).IsSheaf⟩).obj (L)).obj (M)))),
        S.specialFiberDegreePairing s a ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(S.X.toRingedSpace).presheaf, (S.X.toRingedSpace).IsSheaf⟩).obj (L)).obj (M))) hLM =
          S.specialFiberDegreePairing s a L hL + S.specialFiberDegreePairing s a M hM) ∧
      (∀ a b : irreducibleComponents S.specialFiber → ℤ,
        S.specialFiberDegreePairing s a (S.specialFiberVerticalDivisorSheaf s b)
            (S.isInvertible_specialFiberVerticalDivisorSheaf s b) =
          S.specialFiberDegreePairing s b (S.specialFiberVerticalDivisorSheaf s a)
            (S.isInvertible_specialFiberVerticalDivisorSheaf s a)) := by
  refine ⟨fun a L hL => rfl, fun a a' L hL => degreePairing_add S s _ _ _ _ a a' L hL,
    fun a L M hL hM hLM => degreePairing_tensorSheaf S _ _ _ _ s a L M hL hM hLM, fun a b => ?_⟩
  have hexp : ∀ (c : irreducibleComponents S.specialFiber → ℤ)
      (Z : irreducibleComponents S.specialFiber),
      componentDegree S.k (S.specialFiberComponentIdeal Z) (S.specialFiberComponentToSpec Z)
          (S.isProper_specialFiberComponentToSpec Z)
          (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
          (S.specialFiberVerticalDivisorSheaf s c)
          (S.isInvertible_specialFiberVerticalDivisorSheaf s c) =
        ∑ Y ∈ s, c Y * componentDegree S.k (S.specialFiberComponentIdeal Z)
          (S.specialFiberComponentToSpec Z) (S.isProper_specialFiberComponentToSpec Z)
          (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
          (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Y))
          (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
            (S.isEffectiveCartierDivisor_specialFiberComponent Y)) :=
    fun c Z => componentDegree_verticalDivisorSheaf_eq_sum S
      (fun W => S.specialFiberComponentIdeal W) (fun W => S.specialFiberComponentToSpec W)
      (fun W => S.isProper_specialFiberComponentToSpec W)
      (fun W => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent W) Z
      (fun W => S.isEffectiveCartierDivisor_specialFiberComponent W) s c _ _
  have hdouble : ∀ c d : irreducibleComponents S.specialFiber → ℤ,
      S.specialFiberDegreePairing s c (S.specialFiberVerticalDivisorSheaf s d)
          (S.isInvertible_specialFiberVerticalDivisorSheaf s d) =
        ∑ Z ∈ s, ∑ Y ∈ s, c Z * d Y * componentDegree S.k (S.specialFiberComponentIdeal Z)
          (S.specialFiberComponentToSpec Z) (S.isProper_specialFiberComponentToSpec Z)
          (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
          (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Y))
          (@Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
            (S.isEffectiveCartierDivisor_specialFiberComponent Y)) := by
    intro c d
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [hexp d Z, Finset.mul_sum]
    exact Finset.sum_congr rfl fun Y _ => by ring
  rw [hdouble a b, hdouble b a]
  exact sum_sum_mul_comm_of_symm s a b _ fun Z Y =>
    S.componentDegree_specialFiberComponent_comm Z Y

/-! ### Guards on the integer-coefficient reading of the symmetry -/

/-- **The module the symmetry is stated against is the registered [Stacks, Tag 01WX] (4)
object**: `𝒪_X(∑_Z b_Z C_Z)` is the difference twist `Stacks.Divisors.differenceTwist'` of the
positive and negative parts of `b`, and nothing else. -/
theorem specialFiberVerticalDivisorSheaf_eq_differenceTwist
    (s : Finset (irreducibleComponents S.specialFiber))
    (b : irreducibleComponents S.specialFiber → ℤ) :
    S.specialFiberVerticalDivisorSheaf s b =
      Stacks.Divisors.differenceTwist'
        (∏ Z ∈ s, S.specialFiberComponentIdeal Z ^ (b Z).toNat)
        (∏ Z ∈ s, S.specialFiberComponentIdeal Z ^ (-b Z).toNat) :=
  rfl

section Guards

variable [Fintype (irreducibleComponents S.specialFiber)]
  [DecidableEq (irreducibleComponents S.specialFiber)]

/-- **The degree of `𝒪_X(∑_Y c_Y C_Y)` on `C_Z` is `∑_Y c_Y (C_Z · C_Y)` at integer
coefficients.** This is
`Stacks.Models.RegularProperModelSituation.specialFiberDivisorDegree_eq_sum` with its coefficient
family in `ℤ` rather than `ℕ`, and it is the degree formula the fourth clause of
`Stacks.Models.RegularProperModelSituation.specialFiberDegreePairing_bilinear_and_comm` expands
by. -/
theorem specialFiberComponentDegree_specialFiberVerticalDivisorSheaf_eq_sum
    (Z : irreducibleComponents S.specialFiber)
    (s : Finset (irreducibleComponents S.specialFiber))
    (c : irreducibleComponents S.specialFiber → ℤ) :
    S.specialFiberComponentDegree Z (S.specialFiberVerticalDivisorSheaf s c)
        (S.isInvertible_specialFiberVerticalDivisorSheaf s c) =
      ∑ Y ∈ s, c Y * S.specialFiberIntersectionMatrix Z Y :=
  (componentDegree_verticalDivisorSheaf_eq_sum S (fun W => S.specialFiberComponentIdeal W)
    (fun W => S.specialFiberComponentToSpec W)
    (fun W => S.isProper_specialFiberComponentToSpec W)
    (fun W => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent W) Z
    (fun W => S.isEffectiveCartierDivisor_specialFiberComponent W) s c
    (S.isInvertible_specialFiberVerticalDivisorSheaf s c)
    (fun W => @Stacks.Divisors.isTensorInvertible_invertibleSheaf _ _
      (S.isEffectiveCartierDivisor_specialFiberComponent W))).trans
    (Finset.sum_congr rfl fun Y _ => by
      rw [S.specialFiberIntersectionMatrix_eq_componentDegree Z Y])

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- **On a nonnegative family `𝒪_X(∑_Y b_Y C_Y)` has the same degree on each component as the
sheaf of the divisor sum itself**, so the integer-coefficient reading does not drift from
`Stacks.Models.specialFiberDivisorDegree`. -/
theorem specialFiberComponentDegree_specialFiberVerticalDivisorSheaf_natCast
    (Z : irreducibleComponents S.specialFiber)
    (b : irreducibleComponents S.specialFiber → ℕ) :
    S.specialFiberComponentDegree Z
        (S.specialFiberVerticalDivisorSheaf Finset.univ fun W => (b W : ℤ))
        (S.isInvertible_specialFiberVerticalDivisorSheaf Finset.univ fun W => (b W : ℤ)) =
      S.specialFiberDivisorDegree Z b := by
  rw [S.specialFiberComponentDegree_specialFiberVerticalDivisorSheaf_eq_sum Z Finset.univ
    (fun W => (b W : ℤ)), S.specialFiberDivisorDegree_eq_sum Z b]

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- **The pairing the symmetry is stated against agrees with `Stacks.Models.intersectionProduct`
on a nonnegative second family**: `⟨a, 𝒪_X(∑_Y b_Y C_Y)⟩ = (∑_Z a_Z C_Z · ∑_Y b_Y C_Y)` for
`b` in `ℕ`. So the fourth clause of
`Stacks.Models.RegularProperModelSituation.specialFiberDegreePairing_bilinear_and_comm` extends
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionProduct_comm` rather than
replacing it by a different pairing. -/
theorem specialFiberDegreePairing_specialFiberVerticalDivisorSheaf_natCast
    (a : irreducibleComponents S.specialFiber → ℤ)
    (b : irreducibleComponents S.specialFiber → ℕ) :
    S.specialFiberDegreePairing Finset.univ a
        (S.specialFiberVerticalDivisorSheaf Finset.univ fun W => (b W : ℤ))
        (S.isInvertible_specialFiberVerticalDivisorSheaf Finset.univ fun W => (b W : ℤ)) =
      S.specialFiberIntersectionProduct a b := by
  refine Finset.sum_congr rfl fun Z _ => congrArg (fun d : ℤ => a Z * d) ?_
  exact S.specialFiberComponentDegree_specialFiberVerticalDivisorSheaf_natCast Z b

end Guards

end RegularProperModelSituation

end Stacks.Models

end
