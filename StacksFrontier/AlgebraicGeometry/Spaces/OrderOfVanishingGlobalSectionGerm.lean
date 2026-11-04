module

public import StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingChartComparison

/-!
# The order of vanishing of a section whose ratio is the germ of a regular function

Let `X` be a decent algebraic space, `Z ⊆ X` a prime divisor with generic point `ξ`, `ℒ` an
`𝒪_X`-module and `s` a meromorphic section of `ℒ`.  Stacks 0EPR reads `ord_{Z,ℒ}(s)` off the
ratio `s / s_ξ`, an element of `Q(𝒪^h_{X, ξ})`.  When that ratio is the image of the germ at the
marked point of an elementary étale neighbourhood `(U, u)` of `ξ` of a regular function `r` on
`U` — which is what happens when `s` comes from a *global* section and `s_ξ` from a
trivialization of `ℒ` over `U` — the order of vanishing is the length of `𝒪_{U, u} ⧸ (r)`.

## Main results

* `AlgebraicGeometry.Space.orderOfVanishingSection_eq_ord_of_eq_stalkToHenselianLocalRing`:
  `ord_{Z,ℒ}(s) = ord_{𝒪_{U,u}}(r)` under that hypothesis on the ratio.

## Implementation notes

The ratio is a *unit* of `Q(𝒪^h_{X, ξ})`, so the image of `r` in `𝒪^h_{X, ξ}` is a
nonzerodivisor, being a unit in the total ring of fractions.
`AlgebraicGeometry.Space.PrimeDivisor.ord_algebraMap` evaluates `ord_{Z,ℒ}(s)` as `Ring.ord` of
that image, and `AlgebraicGeometry.Space.ord_stalkToHenselianLocalRing` moves it down to
`𝒪_{U, u}`: the canonical map is the structure map of a henselization, which is flat and local
with the maximal ideal extended, so it leaves the length of the quotient by a principal ideal
unchanged.

Cofilteredness of the elementary étale neighbourhoods of `ξ`, Stacks 0BGV, is the hypothesis
`hCofiltered`; it is what makes `𝒪^h_{X, ξ}` a henselization of `𝒪_{U, u}`.  Unlike Stacks 0ENM
no integrality, Noetherianness or codimension hypothesis on `U` is needed, because both sides are
lengths over `𝒪^h_{X, ξ}` and `𝒪_{U, u}` directly.

## References

* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0BGV](https://stacks.math.columbia.edu/tag/0BGV)
* [Stacks Project, Tag 0BGW](https://stacks.math.columbia.edu/tag/0BGW)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped nonZeroDivisors

universe u z

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    [∀ W : PrimeDivisor B S hS X, Nontrivial ↥(W.genericHenselianLocalRing B S hS hX hdec)]
    [∀ W : PrimeDivisor B S hS X, IsNoetherianRing ↥(W.genericHenselianLocalRing B S hS hX hdec)]
    [∀ W : PrimeDivisor B S hS X, Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing B S hS hX hdec)]
    (Z : PrimeDivisor B S hS X)
    [IsLocalRing ↥(Z.genericHenselianLocalRing B S hS hX hdec)]
    (hCofiltered :
      IsCofiltered (ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X)))
    (U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))

include hCofiltered in
/-- If the ratio `s / s_ξ` of a meromorphic section of
`ℒ` at the generic point of a prime divisor `Z` is the image of the germ at the marked point of
an elementary étale neighbourhood `U` of a regular function `r` on `U`, then `ord_{Z,ℒ}(s)` is
the order of vanishing of `r` at that point, that is the length of `𝒪_{U,u} ⧸ (r)`. -/
theorem orderOfVanishingSection_eq_ord_of_eq_stalkToHenselianLocalRing
    (L : Modules.{u, max u z} B S hS X hX) (s : MeromorphicSection.{u, z} B S hS X hX L)
    (ratio : LocalRatio.{u, z} B S hS hX hdec Z L)
    (r : ↥((Over.left U.scheme).obj.presheaf.stalk U.point))
    (hr : (ratio s : Z.genericTotalFractionRing B S hS hX hdec) =
      algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (Z.genericTotalFractionRing B S hS hX hdec)
        (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U r)) :
    orderOfVanishingSection.{u, z} B S hS hX hdec Z L s ratio =
      ((Ring.ord ↥((Over.left U.scheme).obj.presheaf.stalk U.point) r).toNat : ℤ) := by
  have hunit : IsUnit (algebraMap ↥(Z.genericHenselianLocalRing B S hS hX hdec)
      (Z.genericTotalFractionRing B S hS hX hdec)
      (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U r)) :=
    hr ▸ (ratio s).isUnit
  have hnzd : stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec U r ∈
      (↥(Z.genericHenselianLocalRing B S hS hX hdec))⁰ :=
    mem_nonZeroDivisors_of_injective
      (IsFractionRing.injective ↥(Z.genericHenselianLocalRing B S hS hX hdec)
        (Z.genericTotalFractionRing B S hS hX hdec)) hunit.mem_nonZeroDivisors
  rw [show orderOfVanishingSection.{u, z} B S hS hX hdec Z L s ratio =
      Z.ord B S hS hX hdec _ hunit from
    PrimeDivisor.ord_congr B S hS hX hdec Z _ hunit hr,
    Z.ord_algebraMap B S hS hX hdec _ hnzd,
    ord_stalkToHenselianLocalRing B S hS hX hdec Z hCofiltered U r]

end AlgebraicGeometry.Space

end
