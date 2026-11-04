module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TopCech
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BaseDegreeSheaf

/-!
# The degree-`d` negative Laurent monomials are the degree-`(-n-1-d)` monomials

The top cohomology of `𝒪(d)` on `ℙⁿ` is free on the degree-`d` Laurent monomials with every
exponent negative, and the degree-`n` row of [Stacks, Tag 01XW] states it as the dual of the
degree-`(-n-1-d)` part of the polynomial algebra, which is free on the degree-`(-n-1-d)`
multidegrees. The two index sets are matched by `e ↦ -e - 1`, and this file records that
bijection in the spelling the two sides of the row use:
`Stacks.ProjectiveSpace.Cohomology.negativeLaurentMonomials` on the cohomology side and
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MonomialIndex` on the side of the
sheaf `(𝒪_S[T₀, …, Tₙ])_{-n-1-d}`.

Beyond the shift the two spellings differ in two ways: the multidegrees of `MonomialIndex` are
`ℕ`-valued functions on a `ULift` of the variables, as the universe of the base scheme requires,
while the Laurent exponents are `ℤ`-valued functions on the variables themselves.

The names below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `MonomialIndex.uliftEquiv`: relabelling the variables along `Equiv.ulift` matches the
  degree-`k` multidegrees in the two spellings.
* `MonomialIndex.negativeLaurentEquiv`: **the duality `e ↦ -e - 1`**, matching the degree-`d`
  negative Laurent monomials with the degree-`(-n-1-d)` multidegrees.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open Stacks.ProjectiveSpace.Cohomology

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

/-- Relabelling the variables along `Equiv.ulift` matches the degree-`k` multidegrees in `n + 1`
`ULift`ed variables with the degree-`k` multidegrees in `n + 1` variables. -/
def MonomialIndex.uliftEquiv (n k : ℕ) :
    {x : ULift.{u} (Fin (n + 1)) →₀ ℕ | x.degree = k} ≃
      {x : Fin (n + 1) →₀ ℕ | x.degree = k} :=
  Equiv.subtypeEquiv (Finsupp.equivCongrLeft Equiv.ulift) fun x => by
    change x.degree = k ↔
      (Finsupp.equivMapDomain (Equiv.ulift : ULift.{u} (Fin (n + 1)) ≃ Fin (n + 1)) x).degree = k
    rw [degree_equivMapDomain_ulift]

/-- **The duality `e ↦ -e - 1`.** The degree-`d` Laurent monomials with every exponent negative
are matched with the degree-`k` multidegrees for `k = -n - 1 - d`, which index the monomial basis
of `(𝒪_S[T₀, …, Tₙ])_{-n-1-d}`. -/
def MonomialIndex.negativeLaurentEquiv (n : ℕ) (d : ℤ) (k : ℕ)
    (hk : (k : ℤ) = -((n : ℤ)) - 1 - d) :
    MonomialIndex.{u} n (k : ℤ) ≃ negativeLaurentMonomials n d :=
  have hd : (0 : ℤ) ≤ -d - ((n : ℤ) + 1) := by omega
  have htoNat : (-d - ((n : ℤ) + 1)).toNat = k := by omega
  (MonomialIndex.natEquiv.{u} n k).trans
    ((MonomialIndex.uliftEquiv.{u} n k).trans
      (((laurentMonomialsEmptyEquiv n hd).trans
          (Equiv.subtypeEquivRight fun _ => by rw [htoNat])).symm.trans
        (negativeLaurentMonomialsEquiv n d).symm))

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
