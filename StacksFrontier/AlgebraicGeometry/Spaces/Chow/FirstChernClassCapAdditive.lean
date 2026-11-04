module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection

/-!
# Additivity of the first Chern class cap product on an algebraic space

In the situation of Stacks 0EDT let `X/B` be good and let `ℒ` and `𝒩` be invertible
`O_X`-modules.  Stacks 0EQK is the pair of assertions

  `c₁(ℒ) ∩ α + c₁(𝒩) ∩ α = c₁(ℒ ⊗_{O_X} 𝒩) ∩ α`   and   `c₁(O_X) ∩ α = 0`

for every `α ∈ Z_{k+1}(X)`, in `CH_k(X)`.  The cap product itself is Stacks 0EQJ, which this
repository carries as `AlgebraicGeometry.Space.firstChernClassCap`.

The source writes `α ∈ Z_{k-1}(X)`, which is a slip: the operation of Stacks 0EQJ is
`c₁(ℒ) ∩ - : Z_{k+1}(X) ⟶ CH_k(X)`, so only `α ∈ Z_{k+1}(X)` gives an identity in `CH_k(X)`,
and the identical lemma on the scheme side (Stacks 02SP) states `Z_{k+1}(X)`.  The statements
below use `Z_{k+1}(X)`.

The source proves the first assertion from Stacks 0EPV, the identity
`div_{ℒ⊗𝒩}(st) = div_ℒ(s) + div_𝒩(t)` of Weil divisors on an integral algebraic space, and the
second one by observing that the global section `1` of `O_X` restricts to an everywhere nonzero
section of `O_X|_W` on every integral closed subspace `W ⊆ X`, so that its order of vanishing
along every prime divisor of `W` is zero.  Both arguments are carried out below on the carried
forms of those inputs; nothing about either side of the equality is assumed.

## Main definitions

* `AlgebraicGeometry.Space.SubspaceDivisorSetup`: the hypotheses on the integral closed
  subspaces of `X` under which one may speak of the order of vanishing of a meromorphic section
  along a prime divisor of such a subspace — that each is an algebraic space, that each is
  decent, and the three standing hypotheses of Stacks 0ENK on the henselian local ring at the
  generic point of each of its prime divisors.
* `AlgebraicGeometry.Space.SubspaceDivisorSetup.sectionOrder`: `ord_{P,ℒ}(s)` of Stacks 0EPR
  for a prime divisor `P` of an integral closed subspace `W ⊆ X`, with those hypotheses
  supplied.
* `AlgebraicGeometry.Space.IsDivisorPresentation`: the property that a component cycle of
  Stacks 0EQJ on `W` *is* the Weil divisor `div_{ℒ|_W}(s)` of a meromorphic section — its
  coefficient at a prime divisor is the order of vanishing there, and it vanishes at an
  integral closed subspace underlying no prime divisor.  This is the content of Stacks 0EQE
  for the component cycle at `W`, which this repository does not have; see the implementation
  notes.
* `AlgebraicGeometry.Space.ComponentDivisorData`: such a presentation of a whole component rule
  of Stacks 0EQJ, by a meromorphic section on every integral closed subspace of δ-dimension
  `k + 1`.

## Main results

* `AlgebraicGeometry.Space.SubspaceDivisorSetup.sectionOrder_mul` is Stacks 0EPV on a prime
  divisor of an integral closed subspace of `X`, and
  `AlgebraicGeometry.Space.cycle_add_of_isDivisorPresentation` lifts it to the identity
  `div_{ℒ⊗𝒩}(st) = div_ℒ(s) + div_𝒩(t)` of component cycles on `W`.
* `AlgebraicGeometry.Space.firstChernCapCycleMap_add_of_componentCycle_add`: the additive
  extension of Stacks 0EQJ carries an additive family of component rules to an additive family
  of maps `Z_{k+1}(X) ⟶ Z_k(X)`.  This is where the infinite sums are handled.
* `AlgebraicGeometry.Space.firstChernClassCap_tensor`: **Stacks 0EQK**, first assertion.
* `AlgebraicGeometry.Space.firstChernClassCap_structureSheaf_eq_zero`: **Stacks 0EQK**, second
  assertion.

## Implementation notes

### What is carried and what is proved

Stacks 0EQJ is carried with the component cycle `c₁(ℒ|_W) ∩ [W]` and the Chow group `CH_k(X)`
as explicit parameters, because Stacks 0EQE for the component cycle at an integral closed
subspace and Stacks 0EQ6 parts (2)–(4) do not exist for algebraic spaces here; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCap`.  Those two parameters therefore
come along here as well, and the statements below are about the carried
`AlgebraicGeometry.Space.firstChernClassCap`.

The component rules are *not* assumed to be additive — that assumption would make Stacks 0EQK
vacuous, since it is the whole content of the lemma.  Instead each of the three rules is
assumed, separately, to be presented by the Weil divisor of a meromorphic section of its own
sheaf, which is the *definition* Stacks 0EQE would supply, and their additivity is then
*derived* from the carried Stacks 0EPV
(`AlgebraicGeometry.Space.orderOfVanishingSection_mul`).

### The tensor product and the product section

The repository has neither the tensor product `ℒ ⊗_{O_X} 𝒩` of two sheaves of modules on an
algebraic space nor the product `st` of two meromorphic sections.  Exactly as the carried
Stacks 0EPV does, the third sheaf and the third section are therefore unconstrained, and what
identifies them as the tensor product and the product is the hypothesis that at the generic
point of every prime divisor the ratio of the third section is the product of the ratios of the
first two — which is the source's own step, that `s_ξ ⊗ t_ξ` generates `(ℒ ⊗ 𝒩)_ξ` and hence
`st/(s_ξ t_ξ) = (s/s_ξ)(t/t_ξ)`.

For the second assertion the corresponding hypothesis is that the ratio of the section against
the chosen generator is a *unit of the henselian local ring itself*, rather than merely of its
total ring of fractions.  This is the source's "`1` restricts to an everywhere nonzero section
of `O_X|_W`": a nowhere vanishing section generates, so the ratio against a generator is a unit.

### Why the presentation is coefficientwise

Stacks 0EPT and Stacks 0EPV are carried coefficientwise, at each prime divisor, because the
principal divisor `div(f)` of Stacks 0ENP is not available.  The presentation below is
coefficientwise for the same reason, and because it must also say what the component cycle does
at an integral closed subspace of `W` that underlies no prime divisor — namely vanish — which
is what makes the three component cycles comparable at *every* coefficient.

## References

* [Stacks Project, Tag 0EQK](https://stacks.math.columbia.edu/tag/0EQK)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPV](https://stacks.math.columbia.edu/tag/0EPV)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u w v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] Classical.propDecidable

/-! ### Additivity of the extension in the component rule

The additive extension of Stacks 0EQJ, case (2), is a sum over the integral closed subspaces
occurring in a cycle, and that sum is infinite: it is finite at each coefficient only because
the family carrying a cycle is locally finite.  So additivity of the extension in the component
rule is not formal, and it is proved here from the finiteness of the defining sum. -/

section ComponentRuleAdd

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (chernL chernN chernM : FirstChernComponentCycleRule D sX k)

/-- If a component rule is the sum of two others at every integral closed subspace of
δ-dimension `k + 1`, then the same holds for the component cycles of Stacks 0EQJ, case (1), on
`X`: the pushforward along a closed immersion is additive, and at a subspace of any other
δ-dimension all three vanish. -/
theorem firstChernComponentCycle_add_of_add
    (h : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D sX W = k + 1), chernM W hW = chernL W hW + chernN W hW)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    firstChernComponentCycle D sX hX k chernM W =
      firstChernComponentCycle D sX hX k chernL W +
        firstChernComponentCycle D sX hX k chernN W := by
  by_cases hW : deltaDimension D sX W = k + 1
  · rw [firstChernComponentCycle_of_deltaDimension_eq D sX hX k chernM hW,
      firstChernComponentCycle_of_deltaDimension_eq D sX hX k chernL hW,
      firstChernComponentCycle_of_deltaDimension_eq D sX hX k chernN hW, h W hW, map_add]
  · rw [firstChernComponentCycle_of_deltaDimension_ne D sX hX k chernM hW,
      firstChernComponentCycle_of_deltaDimension_ne D sX hX k chernL hW,
      firstChernComponentCycle_of_deltaDimension_ne D sX hX k chernN hW, add_zero]

/-- The coefficientwise extension of Stacks 0EQJ, case (2), is additive in the component rule.

At a fixed integral closed subspace `Z` the defining sum is finite for each of the two
summands, so the sum of the two sums is the sum of the termwise sums. -/
theorem firstChernCapCoeff_add_of_componentCycle_add
    (h : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D sX W = k + 1), chernM W hW = chernL W hW + chernN W hW)
    (α : CycleGroup D sX (k + 1)) :
    firstChernCapCoeff D sX hX k chernM α =
      firstChernCapCoeff D sX hX k chernL α + firstChernCapCoeff D sX hX k chernN α := by
  funext Z
  rw [Pi.add_apply, firstChernCapCoeff_def, firstChernCapCoeff_def, firstChernCapCoeff_def,
    ← finsum_add_distrib (hasFiniteSupport_firstChernCapCoeff D sX hX k chernL α Z)
      (hasFiniteSupport_firstChernCapCoeff D sX hX k chernN α Z)]
  refine finsum_congr fun W => ?_
  rw [firstChernComponentCycle_add_of_add D sX hX k chernL chernN chernM h W]
  have hcoe : (firstChernComponentCycle D sX hX k chernL W +
      firstChernComponentCycle D sX hX k chernN W).1 Z =
      (firstChernComponentCycle D sX hX k chernL W).1 Z +
        (firstChernComponentCycle D sX hX k chernN W).1 Z := rfl
  rw [hcoe, mul_add]

/-- **Stacks 0EQJ, case (2), in the component rule.** The additive extension
`Z_{k+1}(X) ⟶ Z_k(X)` of a component rule which is the sum of two others is the sum of their
additive extensions. -/
theorem firstChernCapCycleMap_add_of_componentCycle_add
    (h : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D sX W = k + 1), chernM W hW = chernL W hW + chernN W hW)
    (α : CycleGroup D sX (k + 1)) :
    firstChernCapCycleMap D sX hX k chernM α =
      firstChernCapCycleMap D sX hX k chernL α + firstChernCapCycleMap D sX hX k chernN α :=
  Subtype.ext (firstChernCapCoeff_add_of_componentCycle_add D sX hX k chernL chernN chernM h α)

/-- If a component rule vanishes at every integral closed subspace of δ-dimension `k + 1`, its
additive extension `Z_{k+1}(X) ⟶ Z_k(X)` is zero. -/
theorem firstChernCapCycleMap_eq_zero_of_componentCycle_eq_zero
    (h : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D sX W = k + 1), chernM W hW = 0)
    (α : CycleGroup D sX (k + 1)) :
    firstChernCapCycleMap D sX hX k chernM α = 0 := by
  have hadd := firstChernCapCycleMap_add_of_componentCycle_add D sX hX k chernM chernM chernM
    (fun W hW => by rw [h W hW, add_zero]) α
  exact left_eq_add.mp hadd

end ComponentRuleAdd

/-! ### Orders of vanishing on the integral closed subspaces of `X` -/

section Setup

variable (D : BaseSpaceDimensionSituation.{u})

/-- The standing hypotheses under which the order of vanishing of a meromorphic section along a
prime divisor of an integral closed subspace `W ⊆ X` is defined: that `W` is an algebraic space
and is decent, and the three hypotheses of Stacks 0ENK — nontrivial, Noetherian, of Krull
dimension at most one — on the henselian local ring at the generic point of each prime divisor
of `W`.

These are hypotheses on `X` alone, not on any sheaf, and they are shared by the three sheaves
appearing in Stacks 0EQK. -/
structure SubspaceDivisorSetup
    (X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u) : Prop where
  /-- Each integral closed subspace of `X` is an algebraic space. -/
  isSpace : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
    IsAlgebraicSpace D.site D.base D.base_mem W.subspace.toFunctor
  /-- Each integral closed subspace of `X` is decent. -/
  isDecent : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
    IsDecentSpace D.site D.base D.base_mem W.subspace.toFunctor
  /-- **Stacks 0ENK.** The henselian local ring at the generic point of a prime divisor of an
  integral closed subspace is nontrivial. -/
  nontrivial : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor),
    Nontrivial ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (isSpace W) (isDecent W))
  /-- **Stacks 0ENK.** That henselian local ring is Noetherian. -/
  noetherian : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor),
    IsNoetherianRing
      ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (isSpace W) (isDecent W))
  /-- **Stacks 0ENK.** That henselian local ring has Krull dimension at most one. -/
  krullDimLE : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor),
    Ring.KrullDimLE 1
      ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (isSpace W) (isDecent W))

variable {D} {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

namespace SubspaceDivisorSetup

variable (setup : SubspaceDivisorSetup D X)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)

/-- **Stacks 0EPR** on an integral closed subspace of `X`: the order of vanishing
`ord_{P,ℒ}(s)` of a meromorphic section `s` of a sheaf `ℒ` on `W` along a prime divisor `P` of
`W`, with the hypotheses of Stacks 0ENK supplied by the setup. -/
def sectionOrder
    (L : Modules.{u, u} D.site D.base D.base_mem W.subspace.toFunctor (setup.isSpace W))
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (setup.isSpace W) L)
    (ratio : LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W)
      (setup.isDecent W) L)
    (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor) : ℤ :=
  haveI := setup.nontrivial W
  haveI := setup.noetherian W
  haveI := setup.krullDimLE W
  orderOfVanishingSection.{u, u} D.site D.base D.base_mem (setup.isSpace W) (setup.isDecent W)
    P L s (ratio P)

/-- **Stacks 0EPV**, coefficientwise, on a prime divisor of an integral closed subspace of `X`:
if the ratio of `st` at the generic point of `P` is the product of the ratios of `s` and of `t`
there, then `ord_{P,ℒ⊗𝒩}(st) = ord_{P,ℒ}(s) + ord_{P,𝒩}(t)`. -/
theorem sectionOrder_mul
    (L N M : Modules.{u, u} D.site D.base D.base_mem W.subspace.toFunctor (setup.isSpace W))
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (setup.isSpace W) L)
    (t : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (setup.isSpace W) N)
    (st : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (setup.isSpace W) M)
    (ratioL : LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W)
      (setup.isDecent W) L)
    (ratioN : LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W)
      (setup.isDecent W) N)
    (ratioM : LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W)
      (setup.isDecent W) M)
    (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor)
    (hst : (ratioM P st :
        P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
          (setup.isDecent W)) =
      (ratioL P s : P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
          (setup.isDecent W)) *
        (ratioN P t : P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
          (setup.isDecent W))) :
    setup.sectionOrder W M st ratioM P =
      setup.sectionOrder W L s ratioL P + setup.sectionOrder W N t ratioN P := by
  have := setup.nontrivial W
  have := setup.noetherian W
  have := setup.krullDimLE W
  exact orderOfVanishingSection_mul.{u, u} D.site D.base D.base_mem (setup.isSpace W)
    (setup.isDecent W) P L N M s t st (ratioL P) (ratioN P) (ratioM P) hst

/-- The order of vanishing of a section whose ratio against the chosen generator is a unit of
the henselian local ring itself is zero.  This is the source's "an everywhere nonzero section":
such a section generates, so the ratio is a unit of the local ring and not merely of its total
ring of fractions, and the order of vanishing of a unit is zero. -/
theorem sectionOrder_eq_zero_of_isUnit
    (L : Modules.{u, u} D.site D.base D.base_mem W.subspace.toFunctor (setup.isSpace W))
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (setup.isSpace W) L)
    (ratio : LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W)
      (setup.isDecent W) L)
    (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor)
    {vP : ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (setup.isSpace W)
      (setup.isDecent W))}
    (hv : IsUnit vP)
    (hvr : (ratio P s :
        P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
          (setup.isDecent W)) =
      algebraMap
        ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (setup.isSpace W)
          (setup.isDecent W))
        (P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
          (setup.isDecent W)) vP) :
    setup.sectionOrder W L s ratio P = 0 := by
  have := setup.nontrivial W
  have := setup.noetherian W
  have := setup.krullDimLE W
  have hmem := hv.mem_nonZeroDivisors
  have hcongr : setup.sectionOrder W L s ratio P =
      P.ord D.site D.base D.base_mem (setup.isSpace W) (setup.isDecent W)
        (algebraMap _ _ vP) (IsLocalization.map_units _ ⟨vP, hmem⟩) :=
    Ring.ordTotalFracInt_congr _ (ratio P s).isUnit
      (IsLocalization.map_units _ ⟨vP, hmem⟩) hvr
  rw [hcongr, P.ord_algebraMap D.site D.base D.base_mem (setup.isSpace W) (setup.isDecent W)
    vP hmem, Ring.ord_of_isUnit hv]
  rfl

end SubspaceDivisorSetup

end Setup

/-! ### Component cycles presented by Weil divisors

Stacks 0EQE says that `c₁(ℒ|_W) ∩ [W]` is the class of the Weil divisor `div_{ℒ|_W}(s)` of a
nonzero meromorphic section.  This repository carries it for the fundamental cycle of an
integral algebraic space, as `AlgebraicGeometry.Space.firstChernClassCapFundamental`, but not
in the form needed here — for the component cycle of Stacks 0EQJ at each integral closed
subspace `W ⊆ X` — so that component rule is a parameter of Stacks 0EQJ as carried.  The
property below says of a given component cycle that it
*is* that Weil divisor, coefficientwise; it is the input that Stacks 0EQE would supply, and it
is the only thing assumed about the three sheaves of Stacks 0EQK apart from the relation
between their sections. -/

section Presentation

variable {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (k : ℤ) (setup : SubspaceDivisorSetup D X)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)

/-- A `k`-cycle on an integral closed subspace `W ⊆ X` *is the Weil divisor* `div_{ℒ|_W}(s)` of
a meromorphic section `s` of a sheaf `ℒ` on `W`: its coefficient at a prime divisor `P` of `W`
is `ord_{P,ℒ}(s)`, and it vanishes at an integral closed subspace of `W` underlying no prime
divisor.

This is what Stacks 0EQE would give for the component cycle of Stacks 0EQJ; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernClassCapAdditive`. -/
structure IsDivisorPresentation
    (c : CycleGroup D (W.subspace.ι ≫ sX) k)
    (L : Modules.{u, u} D.site D.base D.base_mem W.subspace.toFunctor (setup.isSpace W))
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (setup.isSpace W) L)
    (ratio : LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W)
      (setup.isDecent W) L) : Prop where
  /-- At a prime divisor of `W` the coefficient is the order of vanishing of `s` there. -/
  coeff_primeDivisor : ∀ P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
    c.1 (P.toIntegralClosedSubspace D.site D.base D.base_mem) =
      setup.sectionOrder W L s ratio P
  /-- At an integral closed subspace of `W` underlying no prime divisor the coefficient is
  zero: a Weil divisor is carried by the prime divisors. -/
  coeff_eq_zero : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor,
    (∀ P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
      P.toIntegralClosedSubspace D.site D.base D.base_mem ≠ Z) → c.1 Z = 0

/-- Two `k`-cycles on `W` are equal if they agree at every prime divisor and at every integral
closed subspace of `W` underlying no prime divisor. -/
private theorem cycle_eq_of_forall_primeDivisor
    {c c' : CycleGroup D (W.subspace.ι ≫ sX) k}
    (hP : ∀ P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
      c.1 (P.toIntegralClosedSubspace D.site D.base D.base_mem) =
        c'.1 (P.toIntegralClosedSubspace D.site D.base D.base_mem))
    (h0 : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor,
      (∀ P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
        P.toIntegralClosedSubspace D.site D.base D.base_mem ≠ Z) → c.1 Z = c'.1 Z) :
    c = c' := by
  refine Subtype.ext (funext fun Z => ?_)
  by_cases hex : ∃ P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
      P.toIntegralClosedSubspace D.site D.base D.base_mem = Z
  · obtain ⟨P, rfl⟩ := hex
    exact hP P
  · push Not at hex
    exact h0 Z hex

/-- **Stacks 0EPV for component cycles.** If three `k`-cycles on `W` are the Weil divisors of
meromorphic sections `s`, `t` and `st` of three sheaves, and at the generic point of every
prime divisor the ratio of `st` is the product of the ratios of `s` and of `t`, then the third
cycle is the sum of the first two: `div_{ℒ⊗𝒩}(st) = div_ℒ(s) + div_𝒩(t)`.

No additivity is assumed: at a prime divisor the three coefficients are orders of vanishing and
Stacks 0EPV applies, and at any other integral closed subspace all three vanish. -/
theorem cycle_add_of_isDivisorPresentation
    {L N M : Modules.{u, u} D.site D.base D.base_mem W.subspace.toFunctor (setup.isSpace W)}
    {s : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (setup.isSpace W) L}
    {t : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (setup.isSpace W) N}
    {st : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (setup.isSpace W) M}
    {ratioL : LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W)
      (setup.isDecent W) L}
    {ratioN : LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W)
      (setup.isDecent W) N}
    {ratioM : LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W)
      (setup.isDecent W) M}
    {cL cN cM : CycleGroup D (W.subspace.ι ≫ sX) k}
    (hL : IsDivisorPresentation sX k setup W cL L s ratioL)
    (hN : IsDivisorPresentation sX k setup W cN N t ratioN)
    (hM : IsDivisorPresentation sX k setup W cM M st ratioM)
    (hst : ∀ P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
      (ratioM P st : P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
          (setup.isDecent W)) =
        (ratioL P s : P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
            (setup.isDecent W)) *
          (ratioN P t : P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
            (setup.isDecent W))) :
    cM = cL + cN := by
  have hcoe : ∀ Z, (cL + cN).1 Z = cL.1 Z + cN.1 Z := fun _ => rfl
  refine cycle_eq_of_forall_primeDivisor sX k W (fun P => ?_) fun Z hex => ?_
  · rw [hM.coeff_primeDivisor P, hcoe, hL.coeff_primeDivisor P,
      hN.coeff_primeDivisor P]
    exact setup.sectionOrder_mul W L N M s t st ratioL ratioN ratioM P (hst P)
  · rw [hM.coeff_eq_zero Z hex, hcoe, hL.coeff_eq_zero Z hex,
      hN.coeff_eq_zero Z hex, add_zero]

/-- If a `k`-cycle on `W` is the Weil divisor of a meromorphic section whose ratio against the
chosen generator is a unit of the henselian local ring at the generic point of every prime
divisor, then the cycle is zero.  This is `div_{O_W}(1) = 0` for the everywhere nonzero section
`1` of the structure sheaf. -/
theorem cycle_eq_zero_of_isDivisorPresentation
    {L : Modules.{u, u} D.site D.base D.base_mem W.subspace.toFunctor (setup.isSpace W)}
    {s : MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (setup.isSpace W) L}
    {ratio : LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W)
      (setup.isDecent W) L}
    {c : CycleGroup D (W.subspace.ι ≫ sX) k}
    (hc : IsDivisorPresentation sX k setup W c L s ratio)
    (hunit : ∀ P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor,
      ∃ vP : ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (setup.isSpace W)
        (setup.isDecent W)), IsUnit vP ∧
        (ratio P s : P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
            (setup.isDecent W)) =
          algebraMap
            ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (setup.isSpace W)
              (setup.isDecent W))
            (P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
              (setup.isDecent W)) vP) :
    c = 0 := by
  refine cycle_eq_of_forall_primeDivisor sX k W (fun P => ?_) fun Z hex => hc.coeff_eq_zero Z hex
  obtain ⟨vP, hv, hvr⟩ := hunit P
  rw [hc.coeff_primeDivisor P]
  exact setup.sectionOrder_eq_zero_of_isUnit W L s ratio P hv hvr

end Presentation

/-! ### Stacks 0EQK -/

section Cap

variable {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) (setup : SubspaceDivisorSetup D X)

/-- A presentation of a whole component rule of Stacks 0EQJ by Weil divisors: on every integral
closed subspace `W ⊆ X` of δ-dimension `k + 1` a sheaf, a meromorphic section of it, a choice of
generator at the generic point of each prime divisor of `W`, and the statement that the
component cycle at `W` is the Weil divisor of that section.

This is the datum Stacks 0EQE would produce for an invertible sheaf on `X`, restricted to `W`;
here it is a hypothesis, and it is the only thing assumed about the sheaf. -/
structure ComponentDivisorData (chern : FirstChernComponentCycleRule D sX k) where
  /-- The sheaf on each integral closed subspace, intended as `ℒ|_W`. -/
  sheaf : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
    Modules.{u, u} D.site D.base D.base_mem W.subspace.toFunctor (setup.isSpace W)
  /-- The meromorphic section of it whose Weil divisor the component cycle is. -/
  sect : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
    MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor
      (setup.isSpace W) (sheaf W)
  /-- The choice of a generator at the generic point of each prime divisor, read off as the
  ratio it assigns to a meromorphic section. -/
  ratio : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
    LocalRatioFamily.{u, u} D.site D.base D.base_mem (setup.isSpace W) (setup.isDecent W)
      (sheaf W)
  /-- **Stacks 0EQE.** The component cycle at `W` is the Weil divisor of that section. -/
  presentation : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : deltaDimension D sX W = k + 1),
    IsDivisorPresentation sX k setup W (chern W hW) (sheaf W) (sect W) (ratio W)

variable {sX k setup}

/-- **Stacks 0EQK, first assertion.** *Additivity of the first Chern class cap product.* For
invertible sheaves `ℒ` and `𝒩` on a good algebraic space `X/B` and every `α ∈ Z_{k+1}(X)`,

  `c₁(ℒ) ∩ α + c₁(𝒩) ∩ α = c₁(ℒ ⊗_{O_X} 𝒩) ∩ α`   in   `CH_k(X)`.

The cap product is the carried Stacks 0EQJ,
`AlgebraicGeometry.Space.firstChernClassCap`, whose component cycle and Chow group are explicit
parameters; the three component rules here are its parameters for the three sheaves, and the
Chow group `CH` is shared.

Nothing about the conclusion is assumed.  Each of the three component rules is assumed only to
be presented by the Weil divisor of a meromorphic section of its own sheaf, which is the
definition Stacks 0EQE would supply, and the hypothesis `hst` is the source's own step that
`s_ξ ⊗ t_ξ` generates `(ℒ ⊗ 𝒩)_ξ`, so that `st/(s_ξ t_ξ) = (s/s_ξ)(t/t_ξ)`.  Additivity of the
component cycles is then Stacks 0EPV, and additivity of the cap product follows from it by the
extension of Stacks 0EQJ, case (2). -/
@[stacks 0EQK "first assertion: c_1(L) ∩ α + c_1(N) ∩ α = c_1(L ⊗ N) ∩ α in CH_k(X), for the
cap product of Stacks 0EQJ as carried in this repository — so the component cycle
c_1(L|_W) ∩ [W] and the Chow group CH_k(X) remain explicit parameters, standing in for Stacks
0EQE and Stacks 0EQ6 parts (2)-(4), neither of which exists for algebraic spaces here.
QUALIFIED: carried as explicit named hypotheses are (i) that each of the three component rules
is the Weil divisor div_{L|_W}(s) of a meromorphic section, which is the definition of Stacks
0EQE, and (ii) that the ratio of the third section at the generic point of every prime divisor
is the product of the ratios of the first two, which stands in for `M = L ⊗ N` and `st = s·t`
because this repository has neither the tensor product of sheaves of modules on an algebraic
space nor the product of meromorphic sections — this is the hypothesis shape of the carried
Stacks 0EPV. Proved on top of those: the additivity of the component cycles, from Stacks 0EPV,
and the additivity of the cap product, from it. Neither side of the equality, and no conjunct
of it, is a hypothesis. CORRECTED: the source writes α ∈ Z_{k-1}(X), which cannot give an
identity in CH_k(X) for the operation Z_{k+1}(X) → CH_k(X) of Stacks 0EQJ; stated here for
α ∈ Z_{k+1}(X), as the identical scheme-side lemma Stacks 02SP does"]
theorem firstChernClassCap_tensor
    {L N M : Modules.{u, u} D.site D.base D.base_mem X hX.1}
    (hL : IsInvertibleSheaf D sX hX L) (hN : IsInvertibleSheaf D sX hX N)
    (hM : IsInvertibleSheaf D sX hX M)
    {chernL chernN chernM : FirstChernComponentCycleRule D sX k}
    {CH : Type w} [AddCommGroup CH] (chow : ChowTarget.{u, w, v} D sX hX k CH)
    (dL : ComponentDivisorData sX k setup chernL)
    (dN : ComponentDivisorData sX k setup chernN)
    (dM : ComponentDivisorData sX k setup chernM)
    (hst : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor),
      (dM.ratio W P (dM.sect W) :
          P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
            (setup.isDecent W)) =
        (dL.ratio W P (dL.sect W) :
            P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
              (setup.isDecent W)) *
          (dN.ratio W P (dN.sect W) :
            P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
              (setup.isDecent W)))
    (α : CycleGroup D sX (k + 1)) :
    firstChernClassCap D sX hX L k hL chernL chow α +
        firstChernClassCap D sX hX N k hN chernN chow α =
      firstChernClassCap D sX hX M k hM chernM chow α := by
  have hrule : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D sX W = k + 1), chernM W hW = chernL W hW + chernN W hW :=
    fun W hW => cycle_add_of_isDivisorPresentation sX k setup W
      (dL.presentation W hW) (dN.presentation W hW) (dM.presentation W hW) (hst W)
  rw [firstChernClassCap, firstChernClassCap, firstChernClassCap, AddMonoidHom.comp_apply,
    AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    firstChernCapCycleMap_add_of_componentCycle_add D sX hX k chernL chernN chernM hrule α,
    map_add]

/-- **Stacks 0EQK, second assertion.** `c₁(O_X) ∩ α = 0` for every `α ∈ Z_{k+1}(X)`.

The source's proof: the global section `1` of `O_X` restricts, on an integral closed subspace
`W ⊆ X`, to an everywhere nonzero section of `O_X|_W`, so `c₁(O_X|_W) ∩ [W] = 0`.  Here the
hypothesis `hunit` is that everywhere nonzero section: a nowhere vanishing section generates, so
its ratio against the chosen generator at the generic point of a prime divisor is a unit of the
henselian local ring there, and the order of vanishing of a unit is zero.  That the component
cycles all vanish is then proved, not assumed, and the vanishing of the cap product follows
from it. -/
@[stacks 0EQK "second assertion: c_1(O_X) ∩ α = 0 in CH_k(X), for the cap product of Stacks
0EQJ as carried in this repository — so the component cycle and the Chow group CH_k(X) remain
explicit parameters, standing in for Stacks 0EQE and Stacks 0EQ6 parts (2)-(4). QUALIFIED:
carried as explicit named hypotheses are (i) that the component rule is the Weil divisor
div_{O_X|_W}(s) of a meromorphic section, the definition of Stacks 0EQE, and (ii) that the
ratio of that section against the chosen generator is a unit of the henselian local ring at the
generic point of every prime divisor, which is the source's `1` restricting to an everywhere
nonzero section of O_X|_W — the structure sheaf itself is not named because this repository has
no tensor-unit sheaf of modules on an algebraic space. Proved on top of those: that every
component cycle vanishes, from the order of vanishing of a unit being zero, and that the cap
product vanishes, from that. The conclusion is not a hypothesis"]
theorem firstChernClassCap_structureSheaf_eq_zero
    {L : Modules.{u, u} D.site D.base D.base_mem X hX.1} (hL : IsInvertibleSheaf D sX hX L)
    {chern : FirstChernComponentCycleRule D sX k}
    {CH : Type w} [AddCommGroup CH] (chow : ChowTarget.{u, w, v} D sX hX k CH)
    (d : ComponentDivisorData sX k setup chern)
    (hunit : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (P : PrimeDivisor D.site D.base D.base_mem W.subspace.toFunctor),
      ∃ vP : ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (setup.isSpace W)
        (setup.isDecent W)), IsUnit vP ∧
        (d.ratio W P (d.sect W) :
            P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
              (setup.isDecent W)) =
          algebraMap
            ↥(P.genericHenselianLocalRing D.site D.base D.base_mem (setup.isSpace W)
              (setup.isDecent W))
            (P.genericTotalFractionRing D.site D.base D.base_mem (setup.isSpace W)
              (setup.isDecent W)) vP)
    (α : CycleGroup D sX (k + 1)) :
    firstChernClassCap D sX hX L k hL chern chow α = 0 := by
  have hrule : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D sX W = k + 1), chern W hW = 0 :=
    fun W hW => cycle_eq_zero_of_isDivisorPresentation sX k setup W
      (d.presentation W hW) (hunit W)
  rw [firstChernClassCap, AddMonoidHom.comp_apply,
    firstChernCapCycleMap_eq_zero_of_componentCycle_eq_zero D sX hX k chern hrule α, map_zero]

end Cap

end AlgebraicGeometry.Space

end
