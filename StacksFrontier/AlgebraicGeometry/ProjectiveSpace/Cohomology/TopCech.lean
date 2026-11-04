module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.LaurentCharts
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TopDegree

/-!
# The rank of the top Čech cohomology of the twists of the structure sheaf on projective space

Projective `n`-space over a ring `R` is covered by the `n + 1` standard opens `D₊(T₀), …, D₊(Tₙ)`,
so the alternating Čech complex of that cover has top term `p = n`, the sections of `𝒪(d)` on the
total intersection `D₊(T₀ ⋯ Tₙ)`. That the top cohomology of the cover is the free `R`-module on
the degree-`d` Laurent monomials with every exponent negative — and so vanishes exactly when
`-n ≤ d` — is computed in
`StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TopDegree`. This file identifies the
*rank* of that module, by the duality `e ↦ -e - 1`.

Shifting every exponent by `-1` is an involution of the exponent vectors which carries the
degree-`d` vectors with every entry negative to the degree-`(-d - (n + 1))` vectors with every
entry nonnegative, that is to the polynomial monomials of that degree. Hence the top cohomology
of `𝒪(d)` is the degree-`(-d - n - 1)` part of the polynomial ring, which is free of rank
`binom(-d - 1, n)`; equivalently it is the degree-`d` part of
$$ \left(\tfrac{1}{T_0 \cdots T_n} R[\tfrac{1}{T_0}, \ldots, \tfrac{1}{T_n}]\right) $$
of the source's statement. This is the module appearing in the top-degree case of
[Stacks, Tag 01XT].

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.negativeLaurentMonomialsEquiv` — the duality `e ↦ -e - 1`
  between the degree-`d` Laurent monomials with every exponent negative and the polynomial
  monomials of degree `-d - (n + 1)`.
* `Stacks.ProjectiveSpace.Cohomology.negativeTwistPartLinearEquiv` — the resulting identification
  of the top Čech cohomology with the polynomial chart in the complementary degree, which exhibits
  the source's rank.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open Finsupp

universe u

namespace Stacks.ProjectiveSpace.Cohomology

variable {R : Type u} [CommRing R] {n : ℕ} {d : ℤ}

/-- The total degree of the shifted exponent vector `-eᵢ - 1`. -/
private theorem sum_neg_sub_one (n : ℕ) (e : Fin (n + 1) → ℤ) :
    (∑ i, (-(e i) - 1)) = -(∑ i, e i) - ((n : ℤ) + 1) := by
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  ring

/-- **Shifting every exponent by `-1`** matches the degree-`d` Laurent monomials with all
exponents negative with the *polynomial* monomials of degree `-d - (n + 1)`, the map
`e ↦ -e - 1` being an involution. This is the duality `1/(T₀ ⋯ Tₙ) · Tᵖ ↦ T^{-p-1}` in the
source's description of the top cohomology. -/
def negativeLaurentMonomialsEquiv (n : ℕ) (d : ℤ) :
    negativeLaurentMonomials n d ≃
      laurentMonomials n (-d - ((n : ℤ) + 1)) (∅ : Set (Fin (n + 1))) where
  toFun e := ⟨fun i => -(e.1 i) - 1, by
    refine ⟨?_, fun i _ => ?_⟩
    · rw [sum_neg_sub_one, (mem_negativeLaurentMonomials.1 e.2).1]
    · have := (mem_negativeLaurentMonomials.1 e.2).2 i
      dsimp only
      omega⟩
  invFun e := ⟨fun i => -(e.1 i) - 1, by
    refine ⟨?_, fun i => ?_⟩
    · rw [sum_neg_sub_one, (mem_laurentMonomials.1 e.2).1]
      ring
    · have := (mem_laurentMonomials.1 e.2).2 i (by simp)
      dsimp only
      omega⟩
  left_inv e := Subtype.ext (funext fun i => by change -(-(e.1 i) - 1) - 1 = e.1 i; ring)
  right_inv e := Subtype.ext (funext fun i => by change -(-(e.1 i) - 1) - 1 = e.1 i; ring)

variable (R n d)

/-- **The top Čech cohomology of `𝒪(d)` on `ℙⁿ_R` is free of the source's rank.** Through the
duality `e ↦ -e - 1` the free module on the negative Laurent monomials of degree `d` is the free
module on the polynomial monomials of degree `-d - (n + 1)`, which is the degree-`d` part of
$$ \tfrac{1}{T_0 \cdots T_n} R[\tfrac{1}{T_0}, \ldots, \tfrac{1}{T_n}]. $$
Composing with `Stacks.ProjectiveSpace.Cohomology.twistChartEmptyLinearEquiv` identifies it, for
`d ≤ -(n + 1)`, with the degree-`(-d - n - 1)` homogeneous polynomials in `T₀, …, Tₙ`, which is
free of rank `binom(-d - 1, n)`. -/
def negativeTwistPartLinearEquiv :
    negativeTwistPart R n d ≃ₗ[R]
      twistChart R n (-d - ((n : ℤ) + 1)) (∅ : Set (Fin (n + 1))) :=
  (Finsupp.supportedEquivFinsupp _).trans
    ((Finsupp.domLCongr (negativeLaurentMonomialsEquiv n d)).trans
      (Finsupp.supportedEquivFinsupp _).symm)

end Stacks.ProjectiveSpace.Cohomology

end
