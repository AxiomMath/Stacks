module

public import StacksFrontier.AlgebraicGeometry.Thickenings.LineBundleLiftNondegenerate
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.DivisorFirstChernClassNonzero
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective

/-!
# The line bundle of a nonzero effective divisor does not extend along every deformation

Let `X` be a smooth projective surface over a field `k` of characteristic zero. Let
`D ⊆ X` be a nonempty effective Cartier divisor. There is a class
`α ∈ Ext¹(Ω_{X/k}, ω_X)` such that `𝒪_X(D)` does not extend along any immersion `X ⟶ X'` over
`k` whose Kodaira–Spencer class is carried to `α` by an isomorphism `𝒞_{X/X'} ≅ ω_X`.

This combines the obstruction calculation
`Stacks.Thickenings.LineBundleLift.not_extends_of_firstChern_ne_zero` with the non-vanishing of
the Hodge first Chern class of a nonempty effective Cartier divisor
(`AlgebraicGeometry.Scheme.Hom.hodgeFirstChernClass_ne_zero_of_isEffectiveCartierDivisor`). In
the proof of [Stacks, Tag 0D1R], `D` is the trace on the K3 surface of the complement of an affine
open of the algebraization.

## Main results

* `Stacks.Thickenings.LineBundleLift.not_extends_of_isEffectiveCartierDivisor`.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open Stacks.Picard (ofScheme schemePullbackClassHom)

universe u

namespace Stacks.Thickenings.LineBundleLift

/-- **The line bundle of a nonempty effective Cartier divisor on a smooth projective surface is
obstructed along some first-order direction.** Let `k` have characteristic zero. Let
`f : X ⟶ Spec k` be smooth and projective of relative dimension `2`, with `X` equidimensional
of dimension `2`, and let `D` be an effective Cartier divisor with `D ≠ ⊤`. There is
`α ∈ Ext¹(Ω_{X/k}, ω_X)` such that the class `c` of `𝒪_X(D)` is not the pullback of a Picard
class of `X'`, for every immersion `i : X ⟶ X'` over `k` and every isomorphism
`ψ : 𝒞_{X/X'} ≅ ω_X` carrying the Kodaira–Spencer class of `i` to `α`. -/
theorem not_extends_of_isEffectiveCartierDivisor {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [AlgebraicGeometry.Smooth f] (hf : IsProjective f)
    (hX : AlgebraicGeometry.RelativeDimension f 2)
    (hequi : TopologicalSpace.Equidimensional X) (hd : topologicalKrullDim X = (2 : ℕ))
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D] (hD : D ≠ ⊤)
    (c : ofScheme X)
    (hc : c = Stacks.WeilCohomology.picardClassOf X (Stacks.Divisors.divisorSheaf D)
      (Stacks.Divisors.isInvertible_divisorSheaf D)) :
    haveI : IsProper f := hf.isProper
    ∃ α : Ext.{u} (Scheme.Hom.relativeDifferentials f) (Stacks.Duality.dualizingModule f) 1,
      ∀ {X' : Scheme.{u}} (i : X ⟶ X') [IsImmersion i] (q : X' ⟶ Spec (.of k))
        (hq : i ≫ q = f) (ψ : conormalModule i ≅ Stacks.Duality.dualizingModule f),
        (kodairaSpencerClassOf f i q hq).comp (Ext.mk₀ ψ.hom) (add_zero 1) = α →
          ∀ c' : ofScheme X', schemePullbackClassHom i c' ≠ c :=
  haveI : IsProper f := hf.isProper
  not_extends_of_firstChern_ne_zero f hequi hd c
    (Scheme.Hom.hodgeFirstChernClass_ne_zero_of_isEffectiveCartierDivisor f hf hX D hD c hc)

end Stacks.Thickenings.LineBundleLift

end
