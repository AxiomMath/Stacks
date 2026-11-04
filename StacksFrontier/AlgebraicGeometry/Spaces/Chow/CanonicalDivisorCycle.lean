module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFibreSum
public import StacksFrontier.AlgebraicGeometry.Spaces.InducedDimensionFunction
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClassTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleRationalFunctionUnitLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisor

/-!
# The Weil divisor of a regular meromorphic section at the canonical choices

In Situation 0EDT let `X/B` be good and integral with `dim_δ(X) = n`, let `ℒ` be an invertible
`𝒪_X`-module and let `s` be a regular meromorphic section of `ℒ`.  Stacks 0EQE, part (1), is the
`(n-1)`-cycle `div_ℒ(s) = ∑_Z ord_{Z,ℒ}(s) [Z]`.  The library states it as
`AlgebraicGeometry.Space.divisorCycleOfSection`, with four inputs: a family of ratios at the
generic points of the prime divisors (Stacks 0EPR), the local finiteness of the prime divisors
of nonzero order (Stacks 0EPS), and a dimension function on `|X|` together with its agreement
with `δ_{X/B}` (Stacks 0EDN).  On a good integral space none of the four is a choice of the
source: this file supplies all of them.

* The ratio family is the canonical one, `AlgebraicGeometry.Space.canonicalLocalRatioFamily`,
  the ratio `s / s_ξ` against the generator of `ℒ` at `ξ` of Stacks 0EPR.
* Local finiteness is
  `AlgebraicGeometry.Space.locallyFinite_divisorCoefficients_ne_zero_canonicalLocalRatioFamily`,
  Stacks 0EPS at the canonical ratio for an arbitrary regular meromorphic section.
* The dimension function is `AlgebraicGeometry.Space.deltaDimensionFunction`, the function
  `δ_{X/B}` itself, which is a dimension function by Stacks 0EDN.

## Main definitions

* `AlgebraicGeometry.Space.deltaDimensionFunction`: `δ_{X/B}` as a dimension function on `|X|`.
* `AlgebraicGeometry.Space.canonicalDivisorCycle`: `div_ℒ(s) ∈ Z_{n-1}(X)` at the canonical
  choices.

## References

* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- `δ_{X/B}` as a dimension function on `|X|`, by Stacks 0EDN. -/
def deltaDimensionFunction : DimensionFunction (points D.site D.base D.base_mem X) :=
  (exists_dimensionFunction_inducedDimensionValue D.site D.base D.base_mem D.isAlgebraicSpace
    (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
      D.isAlgebraicSpace D.quasiSeparated)
    D.locallyNoetherian D.universallyCatenary D.delta hX.1 (isDecentSpace_of_isGood D sX hX) sX
    hX.2.2).choose

/-- The dimension function `AlgebraicGeometry.Space.deltaDimensionFunction` is `δ_{X/B}`. -/
theorem deltaDimensionFunction_apply (x : points D.site D.base D.base_mem X) :
    deltaDimensionFunction D sX hX x = D.deltaValue sX x :=
  Exists.choose_spec
    (p := fun f : DimensionFunction (points D.site D.base D.base_mem X) =>
      ∀ x, f x = D.deltaValue sX x) _ x

variable (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)

/-- **Stacks 0EQE, part (1), at the canonical choices.** The Weil divisor
`div_ℒ(s) = ∑_Z ord_{Z,ℒ}(s) [Z] ∈ Z_{n-1}(X)` of a regular meromorphic section `s` of an
invertible module on a good integral algebraic space of δ-dimension `n`, the order of vanishing
being taken against the generator of `ℒ` at the generic point of each prime divisor (Stacks
0EPR), with local finiteness from Stacks 0EPS and the dimension function `δ_{X/B}` from Stacks
0EDN. -/
def canonicalDivisorCycle (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    CycleGroup D sX (n - 1) :=
  haveI := fun W : PrimeDivisor D.site D.base D.base_mem X =>
    W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
  haveI := fun W : PrimeDivisor D.site D.base D.base_mem X =>
    W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
  haveI := fun W : PrimeDivisor D.site D.base D.base_mem X =>
    W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
  divisorCycleOfSection.{u, u} D sX hX (isDecentSpace_of_isGood D sX hX) L s
    (canonicalLocalRatioFamily D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) L
      hL hint (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX))
    (locallyFinite_divisorCoefficients_ne_zero_canonicalLocalRatioFamily D.site D.base
      D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) L hL s hs)
    hint (deltaDimensionFunction D sX hX) (deltaDimensionFunction_apply D sX hX) hn

/-- The cycle `AlgebraicGeometry.Space.canonicalDivisorCycle` graded by an integer `k` with
`dim_δ(X) = k + 1`, so that it is an element of `Z_k(X)`: the two gradings `(k + 1) - 1` and `k`
are equal but not syntactically so, and the cap product of Stacks 0EQJ and the component cycles
on prime divisors need the second.  No mathematics is added. -/
def canonicalDivisorCycleAt (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s) {k : ℤ}
    (hk : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    CycleGroup D sX k :=
  ⟨(canonicalDivisorCycle D sX hX hint L hL s hs hk).1, by
    simpa only [add_sub_cancel_right] using (canonicalDivisorCycle D sX hX hint L hL s hs hk).2⟩

/-- The two gradings of the canonical divisor cycle have the same coefficients. -/
theorem canonicalDivisorCycleAt_coe
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (hs : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L s) {k : ℤ}
    (hk : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    (canonicalDivisorCycleAt D sX hX hint L hL s hs hk).1 =
      (canonicalDivisorCycle D sX hX hint L hL s hs hk).1 :=
  rfl

/-- **Stacks 0EQ1 at the canonical choices.** The principal divisor
`div(f) = ∑_Z ord_Z(f) [Z]` of an invertible rational function `f ∈ R(X)^*` on a good integral
algebraic space of δ-dimension `k + 1`, as an element of `Z_k(X)`: the order of vanishing is
the one of Stacks 0ENL, through the canonical embeddings `R(X) → Q(𝒪^h_{X,ξ})` of Stacks 0ENK,
local finiteness is Stacks 0ENN and the dimension function is `δ_{X/B}` (Stacks 0EDN). -/
def canonicalPrincipalDivisorCycleAt
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ) {k : ℤ}
    (hk : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    CycleGroup D sX k :=
  letI E := genericFractionEmbedding D.site D.base D.base_mem hX.1 hint.isDecentSpace hint
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
  letI := E.nontrivial
  letI := E.isNoetherianRing
  letI := E.krullDimLE
  ⟨principalDivisorCycleCoefficients D sX hX hint.isDecentSpace E.emb
      (f : rationalFunctions D.site D.base D.base_mem hX.1) (fun W => f.isUnit.map (E.emb W)), by
    simpa only [add_sub_cancel_right] using
      principalDivisorCycleCoefficients_mem_cyclesOfDimension D sX hX hint.isDecentSpace E.emb
        (f : rationalFunctions D.site D.base D.base_mem hX.1) (fun W => f.isUnit.map (E.emb W))
        (ordRationalFunction_mem_weilDivisor D.site D.base D.base_mem hX.1 hint
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) f)
        hint (deltaDimensionFunction D sX hX) (deltaDimensionFunction_apply D sX hX) hk⟩

end AlgebraicGeometry.Space

end
