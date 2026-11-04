module

public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FibreRegularity
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness at a closed point of a curve

Let `k` be a field, let `X` be a curve over `k` and let `x` be a closed point of `X`, regarded as a
reduced closed subscheme with sheaf of ideals `ℐ`. When `k` is perfect, or when `κ(x)` is separable
over `k`, the morphism `X → Spec k` is smooth at `x` if and only if `𝒪_{X,x}` is regular,
equivalently normal, equivalently a discrete valuation ring, equivalently `ℐ` is invertible,
equivalently `x` is an effective Cartier divisor on `X`.

## Main results

* `AlgebraicGeometry.smoothAt_closedPoint_tfae_of_isCurve_of_isSeparable`: the equivalence, for
  `κ(x)` separable over `k`.
* `AlgebraicGeometry.smoothAt_closedPoint_tfae_of_isCurve_of_perfectField`: the equivalence, for
  `k` perfect.

## References

* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 0B8X](https://stacks.math.columbia.edu/tag/0B8X)
* [Stacks Project, Tag 00TV](https://stacks.math.columbia.edu/tag/00TV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Smoothness at a closed point of a curve, for a separable residue field.** Let `k` be a field,
let `X` be a curve over `k` and let `x` be a closed point of `X` whose residue field is separable
over `k`. Then the following are equivalent: `𝒪_{X,x}` is regular; `𝒪_{X,x}` is normal; `𝒪_{X,x}`
is a discrete valuation ring; the sheaf of ideals of the reduced closed subscheme `{x}` is an
invertible `𝒪_X`-module, which is to say that `x` is an effective Cartier divisor on `X`; and
`X → Spec k` is smooth at `x`. -/
@[stacks 0B8Y "(1), (2), (3), (4), (5) and (6), for κ(x) separable over k",
  ega "IV 17.15.1" "the smoothness item", sga "1 II 5.4" "κ(x)/k separable"]
public theorem smoothAt_closedPoint_tfae_of_isCurve_of_isSeparable [IsCurve k f] {x : X}
    (hx : IsClosed ({x} : Set X))
    (hsep : letI : Algebra k (X.residueField x) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Algebra.IsSeparableExtension k (X.residueField x)) :
    List.TFAE [IsRegularLocalRing (X.presheaf.stalk x), IsNormalRing (X.presheaf.stalk x),
      IsDiscreteValuationRing (X.presheaf.stalk x),
      Stacks.Divisors.IsEffectiveCartierDivisor
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)),
      InfinitesimalLifting.SmoothAt f x] := by
  have H := isEffectiveCartierDivisor_closedPoint_tfae_of_isCurve k f hx
  tfae_have 1 ↔ 2 := H.out 1 2
  tfae_have 1 ↔ 3 := H.out 1 3
  tfae_have 1 ↔ 4 := H.out 1 4
  tfae_have 5 ↔ 1 := smoothAt_iff_isRegularLocalRing_stalk f x hsep
  tfae_finish

/-- **Smoothness at a closed point of a curve, over a perfect field.** Let `k` be a perfect field,
let `X` be a curve over `k` and let `x` be a closed point of `X`. Then the following are
equivalent: `𝒪_{X,x}` is regular; `𝒪_{X,x}` is normal; `𝒪_{X,x}` is a discrete valuation ring; the
sheaf of ideals of the reduced closed subscheme `{x}` is an invertible `𝒪_X`-module, which is to
say that `x` is an effective Cartier divisor on `X`; and `X → Spec k` is smooth at `x`. -/
@[stacks 0B8Y "(1), (2), (3), (4), (5) and (6), for k perfect",
  ega "IV 17.15.2" "the smoothness item", sga "1 II 5.4" "k perfect", ega "IV 6.7.5" "special case"]
public theorem smoothAt_closedPoint_tfae_of_isCurve_of_perfectField [PerfectField k] [IsCurve k f]
    {x : X} (hx : IsClosed ({x} : Set X)) :
    List.TFAE [IsRegularLocalRing (X.presheaf.stalk x), IsNormalRing (X.presheaf.stalk x),
      IsDiscreteValuationRing (X.presheaf.stalk x),
      Stacks.Divisors.IsEffectiveCartierDivisor
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)),
      InfinitesimalLifting.SmoothAt f x] := by
  have H := isEffectiveCartierDivisor_closedPoint_tfae_of_isCurve k f hx
  have h6 : InfinitesimalLifting.SmoothAt f x ↔ IsRegularLocalRing (X.presheaf.stalk x) :=
    Set.ext_iff.mp (smoothAt_locus_eq_regular_locus k f) x
  tfae_have 1 ↔ 2 := H.out 1 2
  tfae_have 1 ↔ 3 := H.out 1 3
  tfae_have 1 ↔ 4 := H.out 1 4
  tfae_have 5 ↔ 1 := h6
  tfae_finish

end AlgebraicGeometry

end
