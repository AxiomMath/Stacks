module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionPullbackRegular

/-!
# Stacks 0EQS at the pullback `f^*ℒ` and `f^*s`

In Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be dominant and quasi-compact,
let `X` and `Y` be integral with `dim_δ(X) = dim_δ(Y) = n`, let `ℒ` be an invertible
`𝒪_Y`-module and let `s` be a nonzero meromorphic section of `ℒ`. Stacks 0EQS asserts

`f_*(div_{f^*ℒ}(f^*s)) = [R(X) : R(Y)] div_ℒ(s)` in `Z_{n-1}(Y)`

and, in `CH_{n-1}(Y)`, `f_*(c₁(f^*ℒ) ∩ [X]) = c₁(ℒ) ∩ f_*[X]`.

Here the module on `X` is the inverse image `AlgebraicGeometry.Space.pullbackSheaf` of
Stacks 03LU, which is `f^*ℒ` as in Stacks 0ER3, and its section is the pullback
`AlgebraicGeometry.Space.pullbackMeromorphicSection` of Stacks 0ENC, part (1), which is `f^*s`;
forming `f^*s` needs pullbacks of meromorphic functions to be defined along `f`
(`AlgebraicGeometry.Space.PullbacksMeromorphicSections`, Stacks 0EN8). Invertibility of `f^*ℒ`
is Stacks 0B8P (`AlgebraicGeometry.Space.isInvertibleSheaf_pullbackSheaf`) and regularity of
`f^*s` is Stacks 0ENC, part (2). The last section takes both divisors to be
`AlgebraicGeometry.Space.canonicalDivisorCycle` (Stacks 0EQE, part (1)), at the canonical ratio
family of Stacks 0EPR: the ratio against a generator of the module at each generic point.

The identities are stated under the coefficient identity at the prime divisors of `Y`
(`AlgebraicGeometry.Space.ProperPushforwardNormRule`, or the hypothesis `hcoeff`). This is
Stacks 0EQ4, `p_* div(g) = div(Nm_{R(X)/R(Y)}(g))`, for the rational function `g` attached to
`s` after trivialising `ℒ` on the torsor of Stacks 0EQG, with
`Nm_{R(X)/R(Y)}(g) = g^{[R(X):R(Y)]}` because `g` lies in `R(Y)^*`. The field-theoretic step of
Stacks 0EQ4 is `Stacks.Norm.norm_baseChange_eq_prod_quotient`, and its geometric statement is
reduced to coefficients in
`AlgebraicGeometry.Space.properPushforward_principalDivisorCycle_eq_iff`.

For arbitrary ratio families (`AlgebraicGeometry.Space.LocalRatio`) the identity of Stacks 0EQS
is false: a unit of the total ring of fractions at the generic point of a prime divisor may have
nonzero order, so rescaling a ratio family changes `div`. For ratio families against generators
the remaining ambiguity is a unit of the henselian local ring, which leaves the order unchanged.

The morphism `f` is only assumed quasi-compact, which is what the pushforward of cycles
`AlgebraicGeometry.Space.properCyclePushforward` asks for.

## Main results

* `AlgebraicGeometry.Space.isRegularMeromorphicSection_pullbackMeromorphicSectionOfGood`:
  Stacks 0ENC, part (2): `f^*s` is a nonzero meromorphic section of `f^*ℒ` when `s` is one
  of `ℒ`.
* `AlgebraicGeometry.Space.properPushforward_pullbackDivisorCycleOfSection_eq_iff`: the first
  identity, with `f^*ℒ` and `f^*s` on `X`, holds in `Z_{n-1}(Y)` if and only if it holds
  coefficientwise at every prime divisor of `Y`.
* `AlgebraicGeometry.Space.properPushforward_pullbackDivisorCycleOfSection`: the first identity,
  under `AlgebraicGeometry.Space.ProperPushforwardNormRule`.
* `AlgebraicGeometry.Space.properPushforward_firstChernClassCapFundamental_pullback`: the second
  identity, under the same hypothesis.
* `AlgebraicGeometry.Space.properPushforward_canonicalDivisorCycle_eq_iff`: the same equivalence
  with both divisors `AlgebraicGeometry.Space.canonicalDivisorCycle`.
* `AlgebraicGeometry.Space.properPushforward_canonicalDivisorCycle`: the first identity in that
  form, under the coefficient identity at the prime divisors of `Y`.

## References

* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 0ER3](https://stacks.math.columbia.edu/tag/0ER3)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u w v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] Classical.propDecidable

section PullbackIdentities

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hdecX : IsDecentSpace D.site D.base D.base_mem X)
    (hdecY : IsDecentSpace D.site D.base D.base_mem Y)

variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem Y,
    Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdecY)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem Y,
    IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdecY)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem Y,
    Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdecY)]

variable (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L)
    (ratio : LocalRatioFamily.{u, u} D.site D.base D.base_mem hY.1 hdecY L)

variable (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (dX : DimensionFunction (points D.site D.base D.base_mem X))
    (hdX : ∀ x, dX x = D.deltaValue sX x)
    (dY : DimensionFunction (points D.site D.base D.base_mem Y))
    (hdY : ∀ y, dY y = D.deltaValue sY y) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))

variable {f : X ⟶ Y}
    (hPull : PullbacksMeromorphicSections D.site D.base D.base_mem f)

/-! ### The pulled-back module and section -/

/-- `f` as a morphism in the category of algebraic spaces of Stacks 02X2. -/
abbrev spaceMorphismOfGood :
    (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨Y, hY.1⟩ :=
  ⟨f⟩

/-- **`f^*s`.** The pullback along `f` of a meromorphic section of `ℒ`, as the map on global
meromorphic sections of Stacks 0ENC, part (1), evaluated at `σ`. Its module is `f^*ℒ`, the
inverse image `AlgebraicGeometry.Space.pullbackSheaf` of Stacks 03LU (Stacks 0ER3). -/
abbrev pullbackMeromorphicSectionOfGood :
    MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1
      (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L) :=
  pullbackMeromorphicSection D.site D.base D.base_mem
    (spaceMorphismOfGood D sX hX sY hY (f := f)) L hPull σ

/-- **Stacks 0ENC, part (2), in this chapter's vocabulary.** The pullback `f^*s` of a nonzero —
that is, regular — meromorphic section of an invertible `𝒪_Y`-module `ℒ` is again a nonzero
meromorphic section, now of `f^*ℒ`. -/
@[stacks 0ENC "part (2) in the vocabulary of this chapter: the pullback f^*s of a regular
meromorphic section of an invertible sheaf on a good algebraic space is regular"]
theorem isRegularMeromorphicSection_pullbackMeromorphicSectionOfGood
    (hL : IsInvertibleSheaf D sY hY L)
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L σ) :
    IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1
      (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
      (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull) :=
  isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem
    (spaceMorphismOfGood D sX hX sY hY (f := f)) hPull L hL σ hσ

/-! ### The two identities of Stacks 0EQS at `f^*ℒ` and `f^*s` -/

/-- **Stacks 0EQS, the identity in `Z_{n-1}(Y)` at the pullback, reduced to its coefficients at the
prime divisors of `Y`.** In Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be dominant
and quasi-compact over `B`, let `X` and `Y` be integral with `dim_δ(X) = dim_δ(Y) = n`, let `ℒ` be
an invertible `𝒪_Y`-module, let `s` be a nonzero meromorphic section of `ℒ`, and let pullbacks of
meromorphic functions be defined along `f`. Then

`f_*(div_{f^*ℒ}(f^*s)) = [R(X) : R(Y)] div_ℒ(s)` in `Z_{n-1}(Y)`

holds exactly when it holds coefficientwise at every prime divisor of `Y`. Here the module on `X`
is the inverse image `f^*ℒ` of Stacks 03LU and its section is `f^*s`, the image of `s` under the
map of Stacks 0ENC, part (1). The coefficient identity on the right is Stacks 0EQ4 at the prime
divisors of `Y`. -/
theorem properPushforward_pullbackDivisorCycleOfSection_eq_iff
    (hL : IsInvertibleSheaf D sY hY L) (hfB : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (hdom : IsDominant D.site D.base D.base_mem f)
    (ratioX : LocalRatioFamily.{u, u} D.site D.base D.base_mem hX.1 hdecX
      (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L))
    (hDvX : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdecX
          (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
          (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull) ratioX W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hDvY : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem Y =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1 hdecY L σ ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem Y) :
    properCyclePushforward D sX hX sY hY hfB hf (n - 1)
          (divisorCycleOfSection D sX hX hdecX
            (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
            (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull) ratioX hDvX hintX dX hdX
            hnX) =
        (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) •
          divisorCycleOfSection D sY hY hdecY L σ ratio hDvY hintY dY hdY hnY ↔
      ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
        (∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
            divisorCycleCoefficients D sX hX hdecX
                (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
                (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull) ratioX Z *
              properCycleMult D sX hX sY hY f Z
                (W.toIntegralClosedSubspace D.site D.base D.base_mem)) =
          (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) *
            divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1 hdecY L σ ratio W :=
  properPushforward_divisorCycleOfSection_eq_iff D sX hX sY hY hdecX hdecY _ _ ratioX L σ ratio
    hintX hintY dX hdX dY hdY hnX hnY hL hfB hf hdom hDvX hDvY

/-- **Stacks 0EQS, first conclusion, at the pullback.** In the situation above,

`f_*(div_{f^*ℒ}(f^*s)) = [R(X) : R(Y)] div_ℒ(s)` in `Z_{n-1}(Y)`,

with the module on `X` the inverse image `f^*ℒ` and its section the pullback `f^*s`. The
hypothesis `hnorm` is `AlgebraicGeometry.Space.ProperPushforwardNormRule`, Stacks 0EQ4 at the
prime divisors of `Y` with the norm eliminated. -/
theorem properPushforward_pullbackDivisorCycleOfSection
    (hL : IsInvertibleSheaf D sY hY L) (hfB : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (hdom : IsDominant D.site D.base D.base_mem f)
    (ratioX : LocalRatioFamily.{u, u} D.site D.base D.base_mem hX.1 hdecX
      (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L))
    (hDvX : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdecX
          (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
          (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull) ratioX W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hDvY : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem Y =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1 hdecY L σ ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem Y)
    (hnorm : ProperPushforwardNormRule D sX hX sY hY hdecX hdecY
      (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
      (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull) ratioX L σ ratio hintX f) :
    properCyclePushforward D sX hX sY hY hfB hf (n - 1)
        (divisorCycleOfSection D sX hX hdecX
          (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
          (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull) ratioX hDvX hintX dX hdX
          hnX) =
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) •
        divisorCycleOfSection D sY hY hdecY L σ ratio hDvY hintY dY hdY hnY :=
  properPushforward_divisorCycleOfSection D sX hX sY hY hdecX hdecY _ _ ratioX L σ ratio
    hintX hintY dX hdX dY hdY hnX hnY hL hfB hf hdom hDvX hDvY hnorm

/-- **Stacks 0EQS, second conclusion, at the pullback.** In the situation above,

`f_*(c₁(f^*ℒ) ∩ [X]) = c₁(ℒ) ∩ f_*[X]` in `CH_{n-1}(Y)`,

the left side read as the class on `Y` of the pushforward cycle of `div_{f^*ℒ}(f^*s)` and the
right side as `[R(X) : R(Y)] · (c₁(ℒ) ∩ [Y])`, which is what
`AlgebraicGeometry.Space.properPushforward_integralCycle_integralClosedSubspaceUniv` —
`f_*[X] = [R(X) : R(Y)] [Y]` — makes of it. The hypothesis `hnorm` is Stacks 0EQ4 at the prime
divisors of `Y`, as for the first conclusion. -/
theorem properPushforward_firstChernClassCapFundamental_pullback
    (hL : IsInvertibleSheaf D sY hY L)
    {CH : Type w} [AddCommGroup CH] (chow : ChowTarget.{u, w, v} D sY hY (n - 1) CH)
    (hfB : f ≫ sY = sX) (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (hdom : IsDominant D.site D.base D.base_mem f)
    (ratioX : LocalRatioFamily.{u, u} D.site D.base D.base_mem hX.1 hdecX
      (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L))
    (hDvX : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdecX
          (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
          (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull) ratioX W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hDvY : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem Y =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1 hdecY L σ ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem Y)
    (hnorm : ProperPushforwardNormRule D sX hX sY hY hdecX hdecY
      (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
      (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull) ratioX L σ ratio hintX f) :
    chow.cls (properCyclePushforward D sX hX sY hY hfB hf (n - 1)
        (divisorCycleOfSection D sX hX hdecX
          (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
          (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull) ratioX hDvX hintX dX hdX
          hnX)) =
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) •
        firstChernClassCapFundamental D sY hY hdecY L chow σ ratio hDvY hintY dY hdY hnY :=
  properPushforward_firstChernClassCapFundamental_of_normRule D sX hX sY hY hdecX hdecY _ _
    ratioX L σ ratio hintX hintY dX hdX dY hdY hnX hnY hL chow hfB hf hdom hDvX hDvY hnorm

end PullbackIdentities

/-! ### Stacks 0EQS at the canonical choices -/

section Canonical

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (B := D.site) ⟨Y, hY.1⟩ L)
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L)
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L σ)
    {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    {f : X ⟶ Y} (hPull : PullbacksMeromorphicSections D.site D.base D.base_mem f)

include hL in
/-- The two spellings of invertibility of a sheaf of modules agree: the
`AlgebraicGeometry.Space.IsInvertibleSheaf` of this chapter is the
`AlgebraicGeometry.Space.IsInvertibleModule` through which the canonical ratio family of Stacks
0EPR is built. -/
theorem isInvertibleSheaf_of_isInvertibleModule :
    IsInvertibleSheaf D sY hY L :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL

include hL in
/-- **Stacks 0B8P.** The inverse image `f^*ℒ` of an invertible module is invertible, in the
spelling the canonical ratio family of Stacks 0EPR asks for. -/
theorem isInvertibleModule_pullbackSheafOfGood :
    IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)
      (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L) :=
  modulePullbackInvertible (spaceMorphismOfGood D sX hX sY hY (f := f)) L hL

/-- **Stacks 0EQS, the identity in `Z_{n-1}(Y)` with every choice made, reduced to its
coefficients at the prime divisors of `Y`.** In Situation 0EDT let `X/B` and `Y/B` be good, let
`f : X ⟶ Y` be dominant and quasi-compact over `B`, let `X` and `Y` be integral with
`dim_δ(X) = dim_δ(Y) = n`, let `ℒ` be an invertible `𝒪_Y`-module, let `s` be a regular — that
is, nonzero — meromorphic section of `ℒ`, and let pullbacks of meromorphic functions be defined
along `f`. Then

`f_*(div_{f^*ℒ}(f^*s)) = [R(X) : R(Y)] div_ℒ(s)` in `Z_{n-1}(Y)`

holds exactly when it holds coefficientwise at every prime divisor of `Y`.

Here:

* the module on `X` is `f^*ℒ` and its section is `f^*s`, as in
  `AlgebraicGeometry.Space.properPushforward_pullbackDivisorCycleOfSection_eq_iff`;
* both divisors are `AlgebraicGeometry.Space.canonicalDivisorCycle`, Stacks 0EQE, part (1), at
  the canonical choices — the ratio family of Stacks 0EPR against the *generator* of the module
  at each generic point, local finiteness from Stacks 0EPS and the dimension function `δ_{X/B}`
  of Stacks 0EDN.

The coefficient identity on the right is Stacks 0EQ4 at the prime divisors of `Y`. -/
theorem properPushforward_canonicalDivisorCycle_eq_iff
    (hfB : f ≫ sY = sX) (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (hdom : IsDominant D.site D.base D.base_mem f) :
    properCyclePushforward D sX hX sY hY hfB hf (n - 1)
          (canonicalDivisorCycle D sX hX hintX
            (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
            (isInvertibleModule_pullbackSheafOfGood D sX hX sY hY L hL)
            (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull)
            (isRegularMeromorphicSection_pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull
              (isInvertibleSheaf_of_isInvertibleModule D sY hY L hL) hσ) hnX) =
        (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) •
          canonicalDivisorCycle D sY hY hintY L hL σ hσ hnY ↔
      ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
        (∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
            (canonicalDivisorCycle D sX hX hintX
              (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
              (isInvertibleModule_pullbackSheafOfGood D sX hX sY hY L hL)
              (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull)
              (isRegularMeromorphicSection_pullbackMeromorphicSectionOfGood D sX hX sY hY L σ
                hPull (isInvertibleSheaf_of_isInvertibleModule D sY hY L hL) hσ) hnX).1 Z *
              properCycleMult D sX hX sY hY f Z
                (W.toIntegralClosedSubspace D.site D.base D.base_mem)) =
          (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) *
            (canonicalDivisorCycle D sY hY hintY L hL σ hσ hnY).1
              (W.toIntegralClosedSubspace D.site D.base D.base_mem) := by
  have hdecX := isDecentSpace_of_isGood D sX hX
  have hdecY := isDecentSpace_of_isGood D sY hY
  have hnoethX := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  have hnoethY := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY
  have := fun W : PrimeDivisor D.site D.base D.base_mem X =>
    W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX hintX hnoethX
  have := fun W : PrimeDivisor D.site D.base D.base_mem X =>
    W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX hintX hnoethX
  have := fun W : PrimeDivisor D.site D.base D.base_mem X =>
    W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX hintX hnoethX
  have := fun W : PrimeDivisor D.site D.base D.base_mem Y =>
    W.nontrivial_genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdecY hintY hnoethY
  have := fun W : PrimeDivisor D.site D.base D.base_mem Y =>
    W.isNoetherianRing_genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdecY hintY hnoethY
  have := fun W : PrimeDivisor D.site D.base D.base_mem Y =>
    W.krullDimLE_genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdecY hintY hnoethY
  have hLY := isInvertibleSheaf_of_isInvertibleModule D sY hY L hL
  refine Iff.trans (properPushforward_divisorCycleOfSection_eq_iff D sX hX sY hY hdecX hdecY
    (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
    (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull)
    (canonicalLocalRatioFamily D.site D.base D.base_mem hX.1 hdecX
      (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
      (isInvertibleModule_pullbackSheafOfGood D sX hX sY hY L hL) hintX hnoethX)
    L σ (canonicalLocalRatioFamily D.site D.base D.base_mem hY.1 hdecY L hL hintY hnoethY)
    hintX hintY (deltaDimensionFunction D sX hX) (deltaDimensionFunction_apply D sX hX)
    (deltaDimensionFunction D sY hY) (deltaDimensionFunction_apply D sY hY) hnX hnY hLY hfB hf hdom
    (locallyFinite_divisorCoefficients_ne_zero_canonicalLocalRatioFamily D.site D.base D.base_mem
      hX.1 hdecX hintX hnoethX
      (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
      (isInvertibleModule_pullbackSheafOfGood D sX hX sY hY L hL)
      (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull)
      (isRegularMeromorphicSection_pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull
        hLY hσ))
    (locallyFinite_divisorCoefficients_ne_zero_canonicalLocalRatioFamily D.site D.base D.base_mem
      hY.1 hdecY hintY hnoethY L hL σ hσ))
    (forall_congr' fun W => ?_)
  rw [← divisorCycleCoefficients_toIntegralClosedSubspace D sY hY hdecY L σ
    (canonicalLocalRatioFamily D.site D.base D.base_mem hY.1 hdecY L hL hintY hnoethY) W]
  exact Iff.rfl

/-- **Stacks 0EQS, first conclusion, with every choice of the source made.** In the situation
above,

`f_*(div_{f^*ℒ}(f^*s)) = [R(X) : R(Y)] div_ℒ(s)` in `Z_{n-1}(Y)`,

the module on `X` being `f^*ℒ`, its section `f^*s`, and both divisors the canonical
`AlgebraicGeometry.Space.canonicalDivisorCycle` of Stacks 0EQE, part (1).

The hypothesis `hcoeff` is the coefficient identity at the prime divisors of `Y`, which is
Stacks 0EQ4 read along `f` with the norm eliminated as the `[R(X) : R(Y)]`-th power. -/
theorem properPushforward_canonicalDivisorCycle
    (hfB : f ≫ sY = sX) (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (hdom : IsDominant D.site D.base D.base_mem f)
    (hcoeff : ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
      (∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
          (canonicalDivisorCycle D sX hX hintX
            (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
            (isInvertibleModule_pullbackSheafOfGood D sX hX sY hY L hL)
            (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull)
            (isRegularMeromorphicSection_pullbackMeromorphicSectionOfGood D sX hX sY hY L σ
              hPull (isInvertibleSheaf_of_isInvertibleModule D sY hY L hL) hσ) hnX).1 Z *
            properCycleMult D sX hX sY hY f Z
              (W.toIntegralClosedSubspace D.site D.base D.base_mem)) =
        (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) *
          (canonicalDivisorCycle D sY hY hintY L hL σ hσ hnY).1
            (W.toIntegralClosedSubspace D.site D.base D.base_mem)) :
    properCyclePushforward D sX hX sY hY hfB hf (n - 1)
        (canonicalDivisorCycle D sX hX hintX
          (pullbackSheaf D sY hY sX hX (spaceMorphismOfGood D sX hX sY hY (f := f)) L)
          (isInvertibleModule_pullbackSheafOfGood D sX hX sY hY L hL)
          (pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull)
          (isRegularMeromorphicSection_pullbackMeromorphicSectionOfGood D sX hX sY hY L σ hPull
            (isInvertibleSheaf_of_isInvertibleModule D sY hY L hL) hσ) hnX) =
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) •
        canonicalDivisorCycle D sY hY hintY L hL σ hσ hnY :=
  (properPushforward_canonicalDivisorCycle_eq_iff D sX hX sY hY hintX hintY L hL σ hσ hnX hnY
    hPull hfB hf hdom).mpr hcoeff

end Canonical

end AlgebraicGeometry.Space

end
