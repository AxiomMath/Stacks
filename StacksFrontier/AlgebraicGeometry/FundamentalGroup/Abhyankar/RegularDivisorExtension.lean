module

public import StacksFrontier.AlgebraicGeometry.CartierAffineLocalConverse.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.PseudoMorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria

/-!
# Extending a cover across a regular divisor

Let `X` be a locally Noetherian scheme and `D ⊆ X` an effective Cartier divisor which is a
regular scheme. A finite étale cover of `X ∖ D` which is unramified over `X` in codimension one
extends to a finite étale cover of `X` ([Stacks, Tag 0EYE]).

## Main results

* `AlgebraicGeometry.isRegularLocalRing_stalk_of_isEffectiveCartierDivisor_of_stalk`: the local
  ring of `X` at a point of an effective Cartier divisor `D` is regular when that of `D` is.

The extension itself ([Stacks, Tag 0EYE]) is
`AlgebraicGeometry.exists_finiteEtale_extension_of_isEffectiveCartierDivisor`.

## Implementation notes

The source deduces the lemma from [Stacks, Tag 0H2W]. The complement of an effective Cartier
divisor is scheme-theoretically dense, hence dense, and at a point `x` of `D` the local ring
`𝒪_{D, x}` is the quotient of `𝒪_{X, x}` by a nonzerodivisor of its maximal ideal, so
`𝒪_{X, x}` is regular by [Stacks, Tag 00NU]. "`D` is a regular scheme" is spelled as regularity
of every local ring of the closed subscheme `D`. The extension carries the argument
`h0BMA : PurityAtRegularLocalRings` of
`AlgebraicGeometry.exists_finiteEtale_of_isUnramifiedInCodimensionOne`, purity for regular local
rings ([Stacks, Tag 0BMA] (1)).

## References

* [Stacks Project, Tag 0EYE](https://stacks.math.columbia.edu/tag/0EYE)
* [Stacks Project, Tag 0H2W](https://stacks.math.columbia.edu/tag/0H2W)
* [Stacks Project, Tag 00NU](https://stacks.math.columbia.edu/tag/00NU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The local rings along a regular effective Cartier divisor are regular.** If `D ⊆ X` is an
effective Cartier divisor of a locally Noetherian scheme and the local ring of `D` at a point
`x ∈ D` is regular, then so is `𝒪_{X, x}`: the local ring `𝒪_{D, x}` is the quotient of
`𝒪_{X, x}` by a nonzerodivisor. -/
theorem isRegularLocalRing_stalk_of_isEffectiveCartierDivisor_of_stalk {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (x : X) (hx : x ∈ D.support)
    (hreg : IsRegularLocalRing
      (D.subscheme.presheaf.stalk (IdealSheafData.subschemePoint D x hx))) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨V, hxV, g, hg, hgen⟩ :=
    (Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_nonZeroDivisor D).mp hD x
  let germ := X.presheaf.germ V.1 x hxV
  have hstalk : IdealSheafData.stalk D x = Ideal.span {germ.hom g} := by
    rw [IdealSheafData.stalk_eq_map_germ D x V hxV, hgen, Ideal.map_span, Set.image_singleton]
  have hg' : germ.hom g ∈ nonZeroDivisors (X.presheaf.stalk x) :=
    Stacks.Divisors.germ_mem_nonZeroDivisors V.2 (isRegular_iff_mem_nonZeroDivisors.mpr hg) x
      hxV
  let z := IdealSheafData.subschemePoint D x hx
  let σ : (X.presheaf.stalk x ⧸ Ideal.span {germ.hom g}) ≃+* D.subscheme.presheaf.stalk z :=
    (Ideal.quotEquivOfEq hstalk.symm).trans (IdealSheafData.subschemeStalkQuotEquiv D z)
  exact isRegularLocalRing_of_nonZeroDivisor _ (germ.hom g) hg'
    (IsRegularLocalRing.of_ringEquiv σ.symm)

end AlgebraicGeometry
