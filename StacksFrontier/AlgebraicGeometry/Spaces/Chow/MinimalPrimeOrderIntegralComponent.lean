module

public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureQuotientStalk
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Chow.StalkLocalSituation.ComponentDimension
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianLocallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.MinimalPrimeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.OrderOfVanishingDomain
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The order of vanishing along a branch is the order of vanishing on its component

Let `X` be a locally Noetherian scheme, `x` a point of `X` whose local ring `O = 𝒪_{X, x}` has
Krull dimension at most one, and `𝔭` a minimal prime of `O`. The quotient `O ⧸ 𝔭` is a
one-dimensional Noetherian local domain, and `Ring.minimalPrimeOrd` is the order of vanishing
taken in it of a unit of the total ring of fractions of `O` — the order of vanishing *along the
branch of `X` at `x` cut out by `𝔭`*.

That branch is the germ at `x` of an irreducible component of `X`, namely the reduced closed
subscheme `W` spanned by the point `X.fromSpecStalk x 𝔭`, and `W` is an integral scheme whose
local ring at `x` is `O ⧸ 𝔭`. This file identifies the two orders of vanishing:

`Ring.minimalPrimeOrd 𝔭 f = W.ord f x`,

where the right-hand side is `AlgebraicGeometry.Scheme.ord` of Stacks 02MD on `W` and `f` is read
in the function field of `W` through the identification of `Frac(O ⧸ 𝔭)` with it.

`AlgebraicGeometry.Scheme.ord` is `0` by convention at a point which does not have codimension
one, so the identification needs the branch to be one-dimensional: `dim(O ⧸ 𝔭) = 1`. It is not
enough for `O` to have dimension at most one — if `dim O = 0` then `𝔭` is the maximal ideal and
both sides are zero for a different reason. When `dim O = 1` the hypothesis is automatic, since a
minimal prime of a one-dimensional local ring is not its maximal ideal.

## Main results

* `Stacks.Chow.minimalPrimeOrd_eq_ord_of_ringEquiv_stalk`: **the dictionary.** For *any* integral
  locally Noetherian scheme `Y` with a point `z` and an identification `O ⧸ 𝔭 ≃ 𝒪_{Y, z}` of its
  local ring there, the order of vanishing along the branch `𝔭` is the order of vanishing at `z`
  on `Y` of the corresponding rational function.
* `Stacks.Chow.minimalPrimeOrd_eq_ord_integralComponentAt`: the same at the canonical component,
  the reduced closed subscheme spanned by the point that `𝔭` cuts out, where the identification
  is `Stacks.Chow.quotStalkEquivClosureStalk`.
* `Stacks.Chow.minimalPrimeOrd_eq_ord_integralComponentAt_of_ringKrullDim_stalk_eq_one`: the same
  with the hypothesis on the dimension of the branch discharged from the dimension of `O`.

## References

* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

open scoped nonZeroDivisors

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

/-- The closed subscheme cut out by an ideal sheaf on a locally Noetherian scheme is locally
Noetherian. -/
@[ega "I 6.1.4" "special case"]
local instance isLocallyNoetherian_idealSheafData_subscheme {X : Scheme.{u}}
    [IsLocallyNoetherian X] (J : X.IdealSheafData) : IsLocallyNoetherian J.subscheme :=
  isLocallyNoetherian_of_isImmersion J.subschemeι

section Dictionary

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {x : X}
  [Ring.KrullDimLE 1 (X.presheaf.stalk x)]

/-- **The order of vanishing along a branch is the order of vanishing on the component carrying
it.** Let `x` be a point of a locally Noetherian scheme `X` whose local ring `O = 𝒪_{X, x}` has
Krull dimension at most one, let `𝔭` be a minimal prime of `O` with `dim(O ⧸ 𝔭) = 1`, and let
`Y` be an integral locally Noetherian scheme with a point `z` and an identification
`O ⧸ 𝔭 ≃ 𝒪_{Y, z}` — the germ at `x` of the irreducible component of `X` cut out by `𝔭`. Then for
a unit `f` of the total ring of fractions of `O` the order of vanishing of `f` along the branch
`𝔭` is the order of vanishing on `Y` at `z` of the rational function that `f` becomes under the
induced identification of `Frac(O ⧸ 𝔭)` with the function field of `Y`. -/
theorem minimalPrimeOrd_eq_ord_of_ringEquiv_stalk (p : minimalPrimes (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x ⧸ (p : Ideal (X.presheaf.stalk x))) = 1)
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] {z : Y}
    (e : (X.presheaf.stalk x ⧸ (p : Ideal (X.presheaf.stalk x))) ≃+* Y.presheaf.stalk z)
    {K : Type*} [CommRing K] [Algebra (X.presheaf.stalk x) K]
    [IsFractionRing (X.presheaf.stalk x) K] (f : K) (hf : IsUnit f) :
    Ring.minimalPrimeOrd p f hf =
      Y.ord (IsFractionRing.ringEquivOfRingEquiv (L := ↥Y.functionField) e
        (Ring.minimalPrimeFractionMap p f)) z := by
  have hpp : (p : Ideal (X.presheaf.stalk x)).IsPrime := p.2.1.1
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x ⧸ (p : Ideal (X.presheaf.stalk x))) :=
    Ring.krullDimLE_one_quotient _
  have : IsDomain (X.presheaf.stalk x ⧸ (p : Ideal (X.presheaf.stalk x))) :=
    Ideal.Quotient.isDomain _
  have hco : Order.coheight z = 1 :=
    StalkLocalSituation.coheight_eq_one_of_ringKrullDim_stalk
      ((ringKrullDim_eq_of_ringEquiv e).symm.trans hdim)
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk z) := krullDimLE_of_coheight_le hco.le
  have hy0 : Ring.minimalPrimeFractionMap p f ≠ 0 :=
    (hf.map (Ring.minimalPrimeFractionMap (K := K) p)).ne_zero
  have hE0 : IsFractionRing.ringEquivOfRingEquiv (L := ↥Y.functionField) e
      (Ring.minimalPrimeFractionMap p f) ≠ 0 := fun h =>
    hy0 ((RingEquiv.map_eq_zero_iff _).mp h)
  rw [ord_eq_ordInt z hco _ hE0,
    ordInt_congr e (IsFractionRing.ringEquivOfRingEquiv (L := ↥Y.functionField) e)
      (fun r => IsFractionRing.ringEquivOfRingEquiv_algebraMap e r) _ hy0 hE0]
  rfl

/-- **The dictionary at the canonical component.** The component of the previous statement, built
from the data at hand: the reduced closed subscheme spanned by the point `X.fromSpecStalk x 𝔭`
that the branch cuts out, whose local ring at `x` is `O ⧸ 𝔭` by
`Stacks.Chow.quotStalkEquivClosureStalk`. -/
theorem minimalPrimeOrd_eq_ord_integralComponentAt (p : minimalPrimes (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x ⧸ (p : Ideal (X.presheaf.stalk x))) = 1)
    {K : Type*} [CommRing K] [Algebra (X.presheaf.stalk x) K]
    [IsFractionRing (X.presheaf.stalk x) K] (f : K) (hf : IsUnit f) :
    Ring.minimalPrimeOrd p f hf =
      (integralComponentAt (X.fromSpecStalk x
            ⟨(p : Ideal (X.presheaf.stalk x)), p.2.1.1⟩)).subscheme.ord
        (IsFractionRing.ringEquivOfRingEquiv
          (L := ↥(integralComponentAt (X.fromSpecStalk x
            ⟨(p : Ideal (X.presheaf.stalk x)), p.2.1.1⟩)).subscheme.functionField)
          (quotStalkEquivClosureStalk x ⟨(p : Ideal (X.presheaf.stalk x)), p.2.1.1⟩)
          (Ring.minimalPrimeFractionMap p f))
        (fromSpecStalkClosurePoint x ⟨(p : Ideal (X.presheaf.stalk x)), p.2.1.1⟩) :=
  minimalPrimeOrd_eq_ord_of_ringEquiv_stalk p hdim
    (quotStalkEquivClosureStalk x ⟨(p : Ideal (X.presheaf.stalk x)), p.2.1.1⟩) f hf

/-- **The dictionary at the canonical component, with the dimension of the branch discharged.**
The identification of the previous statement when the local ring `O` at `x` is one-dimensional,
so that every branch `𝔭` through `x` is one-dimensional. -/
theorem minimalPrimeOrd_eq_ord_integralComponentAt_of_ringKrullDim_stalk_eq_one
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) (p : minimalPrimes (X.presheaf.stalk x))
    {K : Type*} [CommRing K] [Algebra (X.presheaf.stalk x) K]
    [IsFractionRing (X.presheaf.stalk x) K] (f : K) (hf : IsUnit f) :
    Ring.minimalPrimeOrd p f hf =
      (integralComponentAt (X.fromSpecStalk x
            ⟨(p : Ideal (X.presheaf.stalk x)), p.2.1.1⟩)).subscheme.ord
        (IsFractionRing.ringEquivOfRingEquiv
          (L := ↥(integralComponentAt (X.fromSpecStalk x
            ⟨(p : Ideal (X.presheaf.stalk x)), p.2.1.1⟩)).subscheme.functionField)
          (quotStalkEquivClosureStalk x ⟨(p : Ideal (X.presheaf.stalk x)), p.2.1.1⟩)
          (Ring.minimalPrimeFractionMap p f))
        (fromSpecStalkClosurePoint x ⟨(p : Ideal (X.presheaf.stalk x)), p.2.1.1⟩) :=
  minimalPrimeOrd_eq_ord_integralComponentAt p
    (StalkLocalSituation.ringKrullDim_quotient_eq_one_of_mem_minimalPrimes hdim p.2) f hf

end Dictionary

end Stacks.Chow

end
