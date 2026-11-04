module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafCycle

/-!
# The divisor of a nonzero section of an invertible sheaf and the cycle of its zero scheme

In Situation 0EDT let `X/B` be good, let `X` be integral with `n = dim_δ(X)`, let `ℒ` be an
invertible `𝒪_X`-module and let `s ∈ Γ(X, ℒ)` be a nonzero global section. Stacks 0EQF asserts
the two identities

`div_ℒ(s) = [Z(s)]_{n-1}` in `Z_{n-1}(X)` and `c₁(ℒ) ∩ [X] = [Z(s)]_{n-1}` in `CH_{n-1}(X)`.

The left side of the first and the left side of the second are Stacks 0EQE, parts (1) and (2),
that is `AlgebraicGeometry.Space.divisorCycleOfSection` and
`AlgebraicGeometry.Space.firstChernClassCapFundamental`. This module supplies the right side —
the cycle `[Z(s)]_{n-1}` of the zero scheme of Stacks 0845 as an element of `Z_{n-1}(X)` — then
reduces the first identity to its coefficients at the prime divisors of `X`, and derives the
second identity from the first.

The coefficient identity at a prime divisor is the right-hand side of the equivalence
`AlgebraicGeometry.Space.divisorCycleOfSection_eq_zeroSchemeCycle_iff`, and it is the hypothesis
of nothing. It is **proved**, with no chart carried, in
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/GlobalSectionDivisorCycle.lean`; see "The
coefficient identity" below.

## Main definitions

* `AlgebraicGeometry.Space.zeroSchemeCycleCoeff`: the coefficient family of `[Z(s)]_k`, the
  `k`-cycle of the zero scheme `Z(s)` of a global section of a sheaf of modules.
* `AlgebraicGeometry.Space.zeroSchemeCycle`: that cycle as an element of `Z_k(X)`.

## Main results

* `AlgebraicGeometry.Space.zeroSchemeCycleCoeff_mem_cyclesOfDimension`: **Stacks 0EQF**, the
  right side of both identities is a `k`-cycle: `[Z(s)]_k ∈ Z_k(X)`.
* `AlgebraicGeometry.Space.divisorCycleOfSection_eq_zeroSchemeCycle_iff`: **Stacks 0EQF**, the
  first identity holds in `Z_{n-1}(X)` if and only if it holds coefficientwise at every prime
  divisor of `X`.
* `AlgebraicGeometry.Space.firstChernClassCapFundamental_eq_cls_zeroSchemeCycle`: **Stacks
  0EQF**, the second identity, in `CH_{n-1}(X)`, from the first.

## Implementation notes

### The coefficient of `[Z(s)]_k`

The cycle `[Y]_k` of a closed subspace is Stacks 0EE9, which this library has coefficientwise,
as `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace`: the coefficient of an integral closed
subspace `Z` is the multiplicity of `Z` in `Y`, the length of `𝒪_Y` at the generic point of `Z`
read inside `Y`. Length on an algebraic space is `AlgebraicGeometry.Space.geometricLength`,
taken at a *geometric* point, and the choice of geometric point above a point of `|X|` is the
explicit argument `γ`, exactly as in Stacks 0EED, Stacks 0EEB and Stacks 0EQL. That
choice does not matter: the independence of it is Stacks 0EE1,
`AlgebraicGeometry.Space.geometricLength_eq_of_image_eq`, which **is** available, and it is what
`AlgebraicGeometry.Space.closedSubspaceMultiplicity_eq_toNat_geometricLength` uses to read the
multiplicity `m_{Z,Y}` at an arbitrary representative. `γ` is carried only because
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace`, which this library shares with every other
cycle of a closed subspace, is stated at a chosen representative; dropping it would mean
restating that definition. The closed subspace is
`AlgebraicGeometry.Space.vanishingLocus` of Stacks 0845, which is the `Z(s)` of the source.

### What is carried, and in what shape

Exactly one argument is carried beyond those that Stacks 0EQE and Stacks 0EPZ already carry:

`hfin`, the local finiteness of the coefficient family of `[Z(s)]_k`. It is the same argument
that `AlgebraicGeometry.Space.divisorOfSection` and
`AlgebraicGeometry.Space.divisorCycleOfSection` carry under the same name on the other side of
the identity, and it is a property of the *input* datum `γ` together with `ℒ` and `s`, not a
statement about either identity. Discharging it from Stacks 0EE5, as
`AlgebraicGeometry.Space.locallyFinite_cycleCoeffOfModule` does for the cycle of a coherent
module, needs two inputs the library does not have: that an integral closed subspace with
nonzero multiplicity in `Z(s)` is an irreducible component of `|Z(s)|`, which is (3) ⇒ (4) of
Stacks 0EE4 (`AlgebraicGeometry.Space.tfae_isGenericPoint_supportOfSheaf_of_isDecentSpace`)
read on `Z(s)`, a reading no declaration here makes; and `dim_δ(Z(s)) ≤ k`, which
for a nonzero `s` needs the étale-local description of the defining ideal of Stacks 0845 to know
that `Z(s) ≠ X`.

The remaining arguments are inherited verbatim: `hdec`, `hDv`, `hint`, `dimF`, `hdimF` and `hn`
from Stacks 0EQE and Stacks 0EPZ — `dimF` and `hdimF` being the assertion of Stacks 0EDN that
`δ_{X/B}` is a dimension function, which Situation 0EDT invokes — and the three instance
arguments on `AlgebraicGeometry.Space.PrimeDivisor.genericHenselianLocalRing`, quantified over
all prime divisors, which are Stacks 0ENK and are carried as in
`StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection`.

### The coefficient identity

The coefficient identity at a prime divisor `Z` with generic point `ξ`,

`ord_{Z,ℒ}(s) = m_{Z, Z(s)}`,

is proved, in
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/GlobalSectionDivisorCycle.lean`, as
`AlgebraicGeometry.Space.invertibleDivisorCoefficients_globalSection_toIntegralClosedSubspace`,
and quantified over every integral closed subspace of `X` as
`AlgebraicGeometry.Space.zeroSchemeCycleCoeff_eq_invertibleDivisorCoefficients_globalSection`.
It is proved for the *canonical* meromorphic section
`AlgebraicGeometry.Space.globalSectionMeromorphic` of `s`, which is what ties the `σ` of the
equivalence below to `s`; for the arbitrary parameters `σ` and `ratio` the identity is false,
nothing tying them to `s`. No chart is carried: the chart on which `ℒ` is free and on which a
local equation for `Z(s)` is read, Stacks 0846, is produced per prime divisor as a small étale
neighbourhood of its generic point, so the identity is quantified over all prime divisors and
the two identities of Stacks 0EQF follow whole, as
`AlgebraicGeometry.Space.sectionWeilDivisor_eq_zeroSchemeCycle_and_weilDivisorOfInvertibleSheaf_eq`
of that module.

The first identity of Stacks 0EQF is nevertheless *also* stated here as the equivalence
`AlgebraicGeometry.Space.divisorCycleOfSection_eq_zeroSchemeCycle_iff`, whose own content is
that the two coefficient families agree away from the prime divisors: off codimension one the
coefficient of `div_ℒ(σ)` vanishes by Stacks 0EQE, part (1), and the subspace has δ-dimension
other than `n - 1` by Stacks 0EPZ, so its coefficient in `[Z(s)]_{n-1}` vanishes too.

### `c₁(ℒ) ∩ [X]` is the class of `div_ℒ(σ)`

The second identity is the image of the first under the class map of the Chow group, which is
how the source derives it: `c₁(ℒ) ∩ [X]` is by definition — Stacks 0EQE, part (2),
`AlgebraicGeometry.Space.firstChernClassCapFundamental` — the class of `div_ℒ(σ)` for a nonzero
meromorphic section `σ` of `ℒ`, independent of `σ` by
`AlgebraicGeometry.Space.firstChernClassCapFundamental_eq`. The hypothesis `heq` of
`AlgebraicGeometry.Space.firstChernClassCapFundamental_eq_cls_zeroSchemeCycle` is therefore the
*first* conclusion of Stacks 0EQF, a different statement from that theorem's own conclusion. The
Chow group is the parameter `AlgebraicGeometry.Space.ChowTarget` of Stacks 0EQ6, reused
unchanged, parts (2)-(4) of Stacks 0EQ6 not being available for algebraic spaces here.

## References

* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPU](https://stacks.math.columbia.edu/tag/0EPU)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u w v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The cycle of the zero scheme of a global section -/

section ZeroSchemeCycle

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : L.sections) (k : ℤ)
    (γ : points D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)

/-- **Stacks 0EE9, at a chosen geometric point.** The coefficient family of the cycle
`[Z(s)]_k` of the zero scheme of a global section `s` of a sheaf of modules `ℒ` on `X`: the
coefficient of an integral closed subspace of δ-dimension `k` is its multiplicity in `Z(s)`,
and the coefficient elsewhere is zero. -/
def zeroSchemeCycleCoeff : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ :=
  cycleCoeffOfClosedSubspace D sX hX (vanishingLocus D sX hX L s).1
    (vanishingLocus D sX hX L s).2 k γ

/-- An integral closed subspace of δ-dimension other than `k` has coefficient zero in
`[Z(s)]_k`. -/
theorem zeroSchemeCycleCoeff_of_deltaDimension_ne
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ : deltaDimension D sX Z ≠ k) :
    zeroSchemeCycleCoeff D sX hX L s k γ Z = 0 := by
  unfold zeroSchemeCycleCoeff cycleCoeffOfClosedSubspace
  exact ite_eq_right hZ

/-- An integral closed subspace with nonzero coefficient in `[Z(s)]_k` has δ-dimension `k`. -/
theorem deltaDimension_of_zeroSchemeCycleCoeff_ne_zero
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ : zeroSchemeCycleCoeff D sX hX L s k γ Z ≠ 0) :
    deltaDimension D sX Z = k := by
  by_contra h
  exact hZ (zeroSchemeCycleCoeff_of_deltaDimension_ne D sX hX L s k γ h)

/-- **Stacks 0EQF.** The right side of both identities of the source is a `k`-cycle: the
coefficient family of `[Z(s)]_k` lies in `Z_k(X)`.

The δ-dimension clause holds by construction, the coefficient of Stacks 0EE9 at an integral
closed subspace of δ-dimension other than `k` being zero. Local finiteness is the argument
`hfin`, a property of the input datum `(ℒ, s, γ)`, as it is for `div_ℒ(s)` on the other side. -/
@[stacks 0EQF "[Z(s)]_k is a k-cycle, so that at k = n - 1 the right side of both identities is
an element of Z_{n-1}(X); the multiplicity of Stacks 0EE9 is read at the chosen geometric
representative γ, which by Stacks 0EE1 (geometricLength_eq_of_image_eq) does not change its
value, and local finiteness of the coefficient family is the argument hfin, a property of the
input datum (ℒ, s, γ), as it is for div_ℒ(s) in Stacks 0EQE part (1) and for divisorOfSection in
Stacks 0EPU part (1)"]
theorem zeroSchemeCycleCoeff_mem_cyclesOfDimension
    (hfin : LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if zeroSchemeCycleCoeff D sX hX L s k γ Z = 0 then ∅
      else subspacePointSet D.site D.base D.base_mem X Z.subspace) :
    zeroSchemeCycleCoeff D sX hX L s k γ ∈ cyclesOfDimension D sX k :=
  ⟨hfin, fun _ hZ => deltaDimension_of_zeroSchemeCycleCoeff_ne_zero D sX hX L s k γ hZ⟩

/-- The cycle `[Z(s)]_k` of the zero scheme of a global section, as an element of `Z_k(X)`. -/
def zeroSchemeCycle
    (hfin : LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if zeroSchemeCycleCoeff D sX hX L s k γ Z = 0 then ∅
      else subspacePointSet D.site D.base D.base_mem X Z.subspace) :
    CycleGroup D sX k :=
  ⟨zeroSchemeCycleCoeff D sX hX L s k γ,
    zeroSchemeCycleCoeff_mem_cyclesOfDimension D sX hX L s k γ hfin⟩

/-- The coefficient of `[Z(s)]_k` at an integral closed subspace of `X`. -/
@[simp]
theorem zeroSchemeCycle_coe
    (hfin : LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if zeroSchemeCycleCoeff D sX hX L s k γ Z = 0 then ∅
      else subspacePointSet D.site D.base D.base_mem X Z.subspace) :
    (zeroSchemeCycle D sX hX L s k γ hfin).1 = zeroSchemeCycleCoeff D sX hX L s k γ :=
  rfl

end ZeroSchemeCycle

/-! ### The two identities of Stacks 0EQF -/

section Identities

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (hdec : IsDecentSpace D.site D.base D.base_mem X)

variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdec)]

variable (L : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : L.sections)
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 L)
    (ratio : LocalRatioFamily.{u, u} D.site D.base D.base_mem hX.1 hdec L)
    (γ : points D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)
    (hDv : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdec L σ ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (dimF : DimensionFunction (points D.site D.base D.base_mem X))
    (hdimF : ∀ x, dimF x = D.deltaValue sX x) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))

/-- **Stacks 0EQF, the identity in `Z_{n-1}(X)`, reduced to its coefficients at the prime
divisors.** In Situation 0EDT let `X/B` be good, let `X` be integral with `n = dim_δ(X)`, let
`ℒ` be an invertible `𝒪_X`-module, let `s ∈ Γ(X, ℒ)` and let `σ` be a nonzero meromorphic
section of `ℒ`. Then

`div_ℒ(σ) = [Z(s)]_{n-1}` in `Z_{n-1}(X)`

holds exactly when it holds coefficientwise at every prime divisor of `X`, that is when
`ord_{Z,ℒ}(σ)` is the multiplicity of `Z` in `Z(s)` for every prime divisor `Z ⊆ X`.

Both sides are coefficient families on the integral closed subspaces of `X`, and away from the
prime divisors both vanish: the coefficient of `div_ℒ(σ)` at an integral closed subspace whose
point set does not have codimension one is zero by Stacks 0EQE, part (1), and such a subspace
has δ-dimension other than `n - 1` by Stacks 0EPZ, so its coefficient in `[Z(s)]_{n-1}` is zero
too. That is the whole content of the reduction. The right-hand side — the coefficient identity
at a prime divisor — is proved, for the canonical meromorphic section of `s`, by
`AlgebraicGeometry.Space.invertibleDivisorCoefficients_globalSection_toIntegralClosedSubspace`. -/
@[stacks 0EQF "first conclusion REDUCED to its coefficients: div_ℒ(s) = [Z(s)]_{n-1} in
Z_{n-1}(X) holds IF AND ONLY IF it holds at every prime divisor, where div_ℒ(s) is Stacks 0EQE
part (1) and [Z(s)]_{n-1} is Stacks 0EE9 at the chosen geometric representative γ; what is proved
here is that the two coefficient families agree away from the prime divisors, by Stacks 0EQE part
(1) and Stacks 0EPZ. The coefficient identity ord_{Z,ℒ}(s) = m_{Z,Z(s)} AT a prime divisor — the
right-hand side of this equivalence — is proved separately, in GlobalSectionDivisorCycle.lean,
for the canonical meromorphic section of s and with no chart carried"]
theorem divisorCycleOfSection_eq_zeroSchemeCycle_iff (_hL : IsInvertibleSheaf D sX hX L)
    (hfin : LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if zeroSchemeCycleCoeff D sX hX L s (n - 1) γ Z = 0 then ∅
      else subspacePointSet D.site D.base D.base_mem X Z.subspace) :
    divisorCycleOfSection D sX hX hdec L σ ratio hDv hint dimF hdimF hn =
        zeroSchemeCycle D sX hX L s (n - 1) γ hfin ↔
      ∀ W : PrimeDivisor D.site D.base D.base_mem X,
        divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdec L σ ratio W =
          zeroSchemeCycleCoeff D sX hX L s (n - 1) γ
            (W.toIntegralClosedSubspace D.site D.base D.base_mem) := by
  refine ⟨fun heq W => ?_, fun hW => Subtype.ext (funext fun Z => ?_)⟩
  · have h := congrArg (fun c : CycleGroup D sX (n - 1) => c.1
      (W.toIntegralClosedSubspace D.site D.base D.base_mem)) heq
    rwa [divisorCycleOfSection_coe, zeroSchemeCycle_coe,
      divisorCycleCoefficients_toIntegralClosedSubspace D sX hX hdec L σ ratio W] at h
  · rw [divisorCycleOfSection_coe, zeroSchemeCycle_coe]
    by_cases hZ : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1
    · rw [divisorCycleCoefficients_of_codimension_eq_one D sX hX hdec L σ ratio hZ]
      have h := hW (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 hZ)
      rwa [IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor] at h
    · rw [divisorCycleCoefficients_of_codimension_ne_one D sX hX hdec L σ ratio hZ,
        zeroSchemeCycleCoeff_of_deltaDimension_ne D sX hX L s (n - 1) γ
          fun h => hZ (((isPrimeDivisor_tfae_of_isIntegralSpace D sX hX hint dimF hdimF hn
            Z).out 3 2).mp h)]

/-- **Stacks 0EQF, the identity in `CH_{n-1}(X)`, from the identity in `Z_{n-1}(X)`.** In the
situation above, if

`div_ℒ(σ) = [Z(s)]_{n-1}` in `Z_{n-1}(X)`,

which is the first conclusion of the source and the hypothesis `heq`, then

`c₁(ℒ) ∩ [X] = [Z(s)]_{n-1}` in `CH_{n-1}(X)`.

This is the source's own derivation of its second conclusion from its first: `c₁(ℒ) ∩ [X]` is by
Stacks 0EQE, part (2), the class of `div_ℒ(σ)` for a nonzero meromorphic section `σ` of `ℒ`, a
class independent of `σ` by
`AlgebraicGeometry.Space.firstChernClassCapFundamental_eq`, so the second identity is the image
of the first under the class map of the Chow group. -/
@[stacks 0EQF "second conclusion: c₁(ℒ) ∩ [X] = [Z(s)]_{n-1} in CH_{n-1}(X), where c₁(ℒ) ∩ [X] is
Stacks 0EQE part (2) — the class of div_ℒ(s) in the ChowTarget parameter standing in for Stacks
0EQ6; this is the source's own derivation of its second conclusion FROM its first, so the
argument heq is the FIRST conclusion of this tag (reduced to the prime divisors by
divisorCycleOfSection_eq_zeroSchemeCycle_iff) and not this theorem's own conclusion"]
theorem firstChernClassCapFundamental_eq_cls_zeroSchemeCycle
    (_hL : IsInvertibleSheaf D sX hX L) {CH : Type w} [AddCommGroup CH]
    (chow : ChowTarget.{u, w, v} D sX hX (n - 1) CH)
    (hfin : LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if zeroSchemeCycleCoeff D sX hX L s (n - 1) γ Z = 0 then ∅
      else subspacePointSet D.site D.base D.base_mem X Z.subspace)
    (heq : divisorCycleOfSection D sX hX hdec L σ ratio hDv hint dimF hdimF hn =
      zeroSchemeCycle D sX hX L s (n - 1) γ hfin) :
    firstChernClassCapFundamental D sX hX hdec L chow σ ratio hDv hint dimF hdimF hn =
      chow.cls (zeroSchemeCycle D sX hX L s (n - 1) γ hfin) :=
  congrArg chow.cls heq

end Identities

end AlgebraicGeometry.Space

end
