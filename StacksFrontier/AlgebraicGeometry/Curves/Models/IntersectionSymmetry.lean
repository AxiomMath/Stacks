module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.IntersectionPairing
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Symmetry of the intersection product on a regular proper model

In the situation of [Stacks, Tag 0C61] the second displayed equality of [Stacks, Tag 0C65] is

`⟨a, 𝒪_X(∑ⱼ bⱼCⱼ)⟩ = ⟨b, 𝒪_X(∑ᵢ aᵢCᵢ)⟩`,

the symmetry of the intersection product `Stacks.Models.intersectionProduct` in its two
coefficient families. The proof of [Stacks, Tag 0C64] reduces it to the symmetry of the matrix
`(Cᵢ · Cⱼ) = deg(𝒪_X(Cⱼ)|_{Cᵢ})`: expand both sides by bilinearity, which is
[Stacks, Tag 0AYX], and then identify `deg(𝒪_X(Cⱼ)|_{Cᵢ})` with `deg(Cᵢ ∩ Cⱼ)`, which is
[Stacks, Tag 0AYY], a quantity visibly symmetric in `i` and `j`.

This file carries out that reduction: the two cited inputs appear as the arguments `hexpand` and
`hsymm` of `Stacks.Models.intersectionProduct_comm_of_expansion_of_matrix_symm`, and what is
proved here is the exchange of the double sum, together with the isomorphism invariance of the
pairing. Both arguments are supplied, for the components of the special fibre, in
`StacksFrontier/AlgebraicGeometry/Curves/Models/DegreePairingSymmetry.lean`, where the symmetry of
[Stacks, Tag 0C64] and of [Stacks, Tag 0C65] is obtained from this reduction.

## Main definitions

* `Stacks.Models.divisorSheaf` — the invertible module `𝒪_X(∑ⱼ cⱼCⱼ)` of a nonnegative
  combination of the components, with `Stacks.Models.isInvertible_divisorSheaf` its
  invertibility.

## Main results

* `Stacks.Models.componentDegree_eq_of_iso`, `Stacks.Models.degreePairing_congr_iso` — the
  component degree and the degree pairing depend only on the isomorphism class of the module.
* `Stacks.Models.intersectionProduct_eq_degreePairing_divisorSheaf` — the intersection product
  in the spelling of `Stacks.Models.divisorSheaf`.
* `Stacks.Models.intersectionProduct_comm_of_expansion_of_matrix_symm` — the symmetry of
  [Stacks, Tag 0C65], from the bilinear expansion of [Stacks, Tag 0AYX] and the symmetry of the
  intersection matrix of [Stacks, Tag 0AYY].

## Implementation notes

**No `@[stacks 0C64]` and no `@[stacks 0C65]` attribute is attached in this file**, because the
statement below has the two arguments `hexpand` and `hsymm` in place of the results they stand
for, and a tag belongs on a statement with the source's own hypotheses. Both are theorems of
this library, at the components of the special fibre, in
`StacksFrontier/AlgebraicGeometry/Curves/Models/DegreePairingSymmetry.lean`:

* `hexpand` is the invertible case of [Stacks, Tag 0AYX] on a component, proved there as
  `Stacks.Models.componentDegreeAdditive` and expanded over a divisor sum by
  `Stacks.Models.componentDegree_invertibleSheaf_prod`; the underlying tag is
  `AlgebraicGeometry.curveDegree_tensorSheaf_eq_add_of_topologicalKrullDim_le_one`, which carries
  no hypothesis beyond the source's.
* `hsymm` needs `deg(𝒪_{Cᵢ}(E)) = deg(E)` for an effective Cartier divisor `E` on a component,
  the twist formula of [Stacks, Tag 0AYY]. That formula is the third conjunct
  `AlgebraicGeometry.isFinite_and_curveDegree_tensorSheaf_invertibleSheaf … |>.2.2` of
  `StacksFrontier/AlgebraicGeometry/Variety/Curve/DivisorTwistDegree.lean`, obtained from additivity
  of the Euler characteristic along `0 ⟶ 𝒪 ⟶ 𝒪(E) ⟶ i_*i^*𝒪(E) ⟶ 0`, [Stacks, Tag 08AA],
  which is unconditional here because [Stacks, Tag 02O6] over a field is the theorem
  `AlgebraicGeometry.cohomologyFiniteDimensionalOverField_of_isProper`. Its degree clause is
  `AlgebraicGeometry.curveDegree_invertibleSheaf_eq_finrank_globalSections`. The conjunct spells
  `𝒪_X(D)` as `Stacks.Divisors.invertibleSheaf'`, whereas the zero-scheme development spells
  it `Stacks.Divisors.modulesInvertibleSheaf`; the two are the same term and `exact`, `show` and
  `apply` cross between them freely, but `rw` and `simp` do **not**, so a rewrite step must be
  written in whichever spelling its goal already carries. The symmetry itself is
  `Stacks.Models.RegularProperModelSituation.componentDegree_specialFiberComponent_comm`.

The whole of [Stacks, Tag 0C64] is
`Stacks.Models.RegularProperModelSituation.specialFiberDegreePairing_bilinear_and_comm`.

**The intersection matrix is an abstract `ι → ι → ℤ`.** `hexpand` constrains it — taking `c`
supported at a single index recovers each entry from a component degree — so nothing is lost by
not defining it, and the statement avoids a second spelling of the invertibility witness.

**Both coefficient families are `ℕ`-valued.** `Stacks.Models.intersectionProduct` takes its
first family in `ℤ` and its second in `ℕ`, because only the second forms a divisor; the two
sides of a symmetry statement exchange those roles, so both families must be admissible in the
second slot. The `ℤ`-valued first argument is recovered by `Nat.cast`, and linearity in the
first family is already proved as `Stacks.Models.intersectionProduct_add_left` and
`Stacks.Models.intersectionProduct_smul_left`.

## References

* [Stacks Project, Tag 0C65](https://stacks.math.columbia.edu/tag/0C65)
* [Stacks Project, Tag 0C64](https://stacks.math.columbia.edu/tag/0C64)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe v u

namespace Stacks.Models

/-- The degree of an invertible module restricted to a closed subscheme depends only on the
isomorphism class of the module: `deg(ℒ|_D) = deg(ℳ|_D)` whenever `ℒ ≅ ℳ`. -/
theorem componentDegree_eq_of_iso (k : Type u) [Field k] {X : Scheme.{u}}
    (D : X.IdealSheafData) (g : D.subscheme ⟶ Spec (.of k)) (hg : IsProper g)
    (hdim : topologicalKrullDim D.subscheme ≤ 1) (L M : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L)
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property M)
    (e : L ≅ M) :
    componentDegree k D g hg hdim L hL = componentDegree k D g hg hdim M hM :=
  @AlgebraicGeometry.invertibleCurveDegree_eq_of_iso k _ D.subscheme g hg hdim _ _
    (isInvertible_restrict D L hL) (isInvertible_restrict D M hM)
    ((Scheme.Modules.pullback D.subschemeι).mapIso e)

variable (S : RegularProperModelSituation.{u}) {ι : Type v} (s : Finset ι)
  (C : ι → S.X.IdealSheafData) (g : ∀ i, (C i).subscheme ⟶ Spec (.of S.k))
  (hg : ∀ i, IsProper (g i)) (hdim : ∀ i, topologicalKrullDim (C i).subscheme ≤ 1)

/-- The degree pairing depends only on the isomorphism class of the invertible module. -/
theorem degreePairing_congr_iso (a : ι → ℤ) (L M : S.X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property L)
    (hM : Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property M)
    (e : L ≅ M) :
    degreePairing S s C g hg hdim a L hL = degreePairing S s C g hg hdim a M hM :=
  Finset.sum_congr rfl fun i _ ↦ by
    rw [componentDegree_eq_of_iso S.k (C i) (g i) (hg i) (hdim i) L M hL hM e]

/-- The invertible module `𝒪_X(∑ⱼ cⱼCⱼ)` of a nonnegative integer combination of the
components, the divisor sum being written multiplicatively. -/
def divisorSheaf (c : ι → ℕ) : S.X.Modules :=
  Stacks.Divisors.invertibleSheaf' (∏ j ∈ s, C j ^ c j)

/-- `Stacks.Models.divisorSheaf` is invertible, a product of effective Cartier divisors being an
effective Cartier divisor. -/
theorem isInvertible_divisorSheaf (c : ι → ℕ)
    (hC : ∀ i ∈ s, Stacks.Divisors.IsEffectiveCartierDivisor (C i)) :
    Stacks.SheafOfModules.IsInvertible S.X.presheaf
      (structureSheafRing S.X.toRingedSpace).property (divisorSheaf S s C c) :=
  @Stacks.Divisors.isTensorInvertible_invertibleSheaf _ (∏ j ∈ s, C j ^ c j)
    (Stacks.Divisors.isEffectiveCartierDivisor_prod s C c hC)

/-- **Stacks Project, Tag 0C65, first equality**, in the spelling of
`Stacks.Models.divisorSheaf`: the intersection product `(∑ᵢ aᵢCᵢ · ∑ⱼ bⱼCⱼ)` is the degree
pairing `⟨a, 𝒪_X(∑ⱼ bⱼCⱼ)⟩`. -/
theorem intersectionProduct_eq_degreePairing_divisorSheaf (a : ι → ℤ) (b : ι → ℕ)
    (hC : ∀ i ∈ s, Stacks.Divisors.IsEffectiveCartierDivisor (C i)) :
    intersectionProduct S s C g hg hdim a b hC =
      degreePairing S s C g hg hdim a (divisorSheaf S s C b)
        (isInvertible_divisorSheaf S s C b hC) := rfl

/-- **The symmetry of [Stacks, Tag 0C65], reduced to the two results its proof cites.** Given
the bilinear expansion `deg(𝒪_X(∑ⱼ cⱼCⱼ)|_{Cᵢ}) = ∑ⱼ cⱼ · (Cᵢ · Cⱼ)` of [Stacks, Tag 0AYX] and
the symmetry `(Cᵢ · Cⱼ) = (Cⱼ · Cᵢ)` of the intersection matrix, which [Stacks, Tag 0AYY]
supplies by identifying both entries with `deg(Cᵢ ∩ Cⱼ)`, the intersection product is symmetric
in its two coefficient families.

Neither hypothesis is available in this library; see the module docstring. What is proved here
is the remaining step of the source's argument, the exchange of the two summations. -/
theorem intersectionProduct_comm_of_expansion_of_matrix_symm (N : ι → ι → ℤ) (a b : ι → ℕ)
    (hC : ∀ i ∈ s, Stacks.Divisors.IsEffectiveCartierDivisor (C i))
    (hexpand : ∀ c : ι → ℕ, ∀ i ∈ s,
      componentDegree S.k (C i) (g i) (hg i) (hdim i) (divisorSheaf S s C c)
        (isInvertible_divisorSheaf S s C c hC) = ∑ j ∈ s, (c j : ℤ) * N i j)
    (hsymm : ∀ i ∈ s, ∀ j ∈ s, N i j = N j i) :
    intersectionProduct S s C g hg hdim (fun i ↦ (a i : ℤ)) b hC =
      intersectionProduct S s C g hg hdim (fun i ↦ (b i : ℤ)) a hC := by
  simp only [intersectionProduct_eq_degreePairing_divisorSheaf, degreePairing]
  have key : ∀ c d : ι → ℕ, ∑ i ∈ s, (c i : ℤ) * componentDegree S.k (C i) (g i) (hg i) (hdim i)
        (divisorSheaf S s C d) (isInvertible_divisorSheaf S s C d hC) =
      ∑ i ∈ s, ∑ j ∈ s, (c i : ℤ) * (d j : ℤ) * N i j := fun c d ↦
    Finset.sum_congr rfl fun i hi ↦ by
      rw [hexpand d i hi, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [key a b, key b a]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun j hj ↦ ?_)
  exact Finset.sum_congr rfl fun i hi ↦ by rw [hsymm i hi j hj]; ring

end Stacks.Models

end
