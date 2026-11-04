module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ChowToDimensionLayer
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FunctionFieldDenominator

/-!
# The multiplicities of the two denominator quotients at a prime divisor

Let `X` be an integral locally Noetherian scheme and `g` a nonzero rational function on `X`,
with ideal of denominators `I`. The two short exact sequences of Stacks 02P0,

`0 → I → 𝒪_X → 𝒪_X/I → 0`  and  `0 → I →^{g} 𝒪_X → 𝒪_X/gI → 0`,

present the two quotients as cokernels. At a point `x` of codimension one — the generic point of
a prime divisor — the multiplicities of Stacks 02QX part (1) of the two quotients differ by the
order of vanishing of `g` at `x`:

`m_{𝒪_X/gI}(x) − m_{𝒪_X/I}(x) = ord_x(g)`.

This is the pointwise form of the claim `[𝒪_X/I]_k − [𝒪_X/gI]_k = div(g)` in the proof of
Stacks 0FDS, read one coefficient at a time.

## Main results

* `Stacks.Chow.sheafMultiplicity_cokernel_sub_eq_ord` — the identity for an abstract pair of
  morphisms `i, j : F ⟶ 𝒪_X` whose stalk maps at `x` satisfy `g · i = j` in the function field,
  with `i` not identically zero on that stalk.
* `AlgebraicGeometry.sheafMultiplicity_denominator_sub_eq_ord` — its instance for the inclusion
  of the ideal of denominators of `g` and multiplication by `g` on it.

## Implementation notes

The identity is stated first for an abstract `F : X.Modules` and an abstract pair of morphisms
into `𝒪_X`, and only then instantiated. That is not presentational: the ideal of denominators is
indexed by `Stacks.Sheaves.Differentials.ringSheaf X.sheaf` rather than
`AlgebraicGeometry.Scheme.ringCatSheaf`, and although the two are the same sheaf of rings,
instance search does not identify them — so the module structure on the stalk of the ideal of
denominators over the local ring is not synthesizable at a concrete call site, while for a
variable `F : X.Modules` it is found at once. With the statement made at `F`, the concrete case
is an application and no instance has to be found.

For the same reason nothing here is proved by `rw`: the two spellings of the structure sheaf are
not interchangeable at the transparency level a motive check uses, and a rewrite on any of these
goals reports the target as not type-correct. Both proofs are `Eq.trans` chains.

Three inputs meet here: the multiplicity of a cokernel of a map into `𝒪_X` as a length over the
local ring (`Stacks.Chow.sheafMultiplicity_cokernel_unit`), the lattice-distance computation of
Stacks 02MH and 02MI (`Stacks.Chow.length_quotient_sub_length_quotient_eq_ordR`), and the
agreement of the scheme-level order of vanishing with the one computed in the stalk
(`Stacks.Chow.ord_eq_ordR`).

## What is not proved

No declaration here carries the tag `0FDS`. The content of that tag is the existence of the
homomorphism `CH_k(X) → K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`, and this file proves one coefficient
of one of the identities in its proof; the cycle identity itself, which also needs the
coefficients of `div(g)` and the vanishing of both sides away from codimension one, is not
stated here.

## References

* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 02MH](https://stacks.math.columbia.edu/tag/02MH)
* [Stacks Project, Tag 02MI](https://stacks.math.columbia.edu/tag/02MI)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Ample (unitModule)

universe u

namespace Stacks.Chow

/-- **The multiplicities of two cokernels over `𝒪_X` differ by an order of vanishing.** Let
`i, j : F ⟶ 𝒪_X` be two morphisms of modules on an integral locally Noetherian scheme whose
stalk maps at a point `x` of codimension one satisfy `g · i(m) = j(m)` in the function field,
with `i` not identically zero on that stalk. Then the multiplicities of the two cokernels at `x`
differ by the order of vanishing of `g` at `x`.

The two stalk maps are lattices in the function field, and the distance between a lattice and
its image under multiplication by `g` is `ord_x(g)`. -/
theorem sheafMultiplicity_cokernel_sub_eq_ord {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (g : X.functionFieldˣ) {x : X} (hx : Order.coheight x = 1)
    {F : X.Modules} (i j : F ⟶ unitModule X)
    (hne : ∃ m, Scheme.Modules.unitStalkLinearMap x i m ≠ 0)
    (hmul : ∀ m, (g : X.functionField) * algebraMap (X.presheaf.stalk x) X.functionField
          (Scheme.Modules.unitStalkLinearMap x i m) =
        algebraMap (X.presheaf.stalk x) X.functionField
          (Scheme.Modules.unitStalkLinearMap x j m)) :
    sheafMultiplicity (cokernel j) x - sheafMultiplicity (cokernel i) x =
      X.ord (g : X.functionField) x :=
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hx]; rfl
  (congrArg₂ (· - ·) (sheafMultiplicity_cokernel_unit j x)
      (sheafMultiplicity_cokernel_unit i x)).trans
    ((length_quotient_sub_length_quotient_eq_ordR hdim g
        (Scheme.Modules.unitStalkLinearMap x i) (Scheme.Modules.unitStalkLinearMap x j)
        hne hmul).trans (ord_eq_ordR g x hx).symm)

end Stacks.Chow

namespace AlgebraicGeometry

/-- **The two denominator quotients of a rational function at a prime divisor.** At a point `x`
of codimension one of an integral locally Noetherian scheme, the multiplicity of `𝒪_X/gI` minus
the multiplicity of `𝒪_X/I` is the order of vanishing of `g` at `x`, where `I` is the ideal of
denominators of `g`.

This is the coefficient at `x` of the claim `[𝒪_X/I]_k − [𝒪_X/gI]_k = div(g)` in the proof of
Stacks 0FDS. -/
theorem sheafMultiplicity_denominator_sub_eq_ord {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (g : X.functionFieldˣ) {x : X} (hx : Order.coheight x = 1) :
    Stacks.Chow.sheafMultiplicity
        (cokernel (denominatorIdealMul X (unitModule X)
          (meromorphicSectionOfFunctionField X g))) x -
      Stacks.Chow.sheafMultiplicity
        (cokernel (denominatorIdealι X (unitModule X)
          (meromorphicSectionOfFunctionField X g))) x =
      X.ord (g : X.functionField) x :=
  Stacks.Chow.sheafMultiplicity_cokernel_sub_eq_ord g hx _ _
    (exists_unitStalkLinearMap_denominatorIdealι_ne_zero X g x)
    (mul_algebraMap_unitStalkLinearMap_denominatorIdealι X g x)

end AlgebraicGeometry
