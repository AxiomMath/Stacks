module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValued
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic

/-!
# Sharpness of representability for maps of affine formal algebraic spaces

**Stacks 0AN7** records that the discussion of Stacks 0AN5, Stacks 0AKP and Stacks 0AKQ is
sharp in two senses. First, a continuous homomorphism `φ : A → B` of weakly admissible
topological rings need not have `Spf (φ) : Spf B → Spf A` representable. Second, the source of
a representable morphism of affine formal algebraic spaces whose target is a McQuillan formal
spectrum need not be McQuillan.

This file supplies the ring-theoretic half of the example the source gives for the first sense: `A = k` is a field
with the discrete topology and `B = k⟦t⟧` carries the `t`-adic topology. Both rings are weakly
admissible, the inclusion of constants is continuous because the source is discrete, and it is
*not taut*: the zero ideal is a weak ideal of definition of `k`, its extension to `k⟦t⟧` is
closed and equal to the zero ideal, and the zero ideal of `k⟦t⟧` is not open because `tⁿ ≠ 0`
for every `n`. By the equivalence of conditions (1) and (3) of Stacks 0AN5 the formal spectrum
of a non-taut homomorphism is not representable, which is the assertion of the remark. The
complete remark, both senses and with no hypothesis, is
`AlgebraicGeometry.FormalSpace.exists_formalSpectrumMap_constants_not_representable` and
`AlgebraicGeometry.FormalSpace.exists_representable_formalSpectrum_not_mcQuillan` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.SharpnessOfRepresentabilityExamples`.

## Main definitions

* `TopologicalRing.TAdicPowerSeries`: the ring `k⟦t⟧` carrying the `t`-adic topology.
* `TopologicalRing.constantsToTAdicPowerSeries`: the homomorphism `k → k⟦t⟧` of the example.
* `AlgebraicGeometry.FormalSpace.IsTautOfRepresentableFormalSpectrumMap`: the implication
  (1) ⟹ (3) of Stacks 0AN5 at all quotient systems, with no condition on the site, as a
  proposition.

## Main results

* `TopologicalRing.isWeaklyAdmissible_discreteTopology` and
  `TopologicalRing.isWeaklyAdmissible_tAdicPowerSeries`: the two rings of the example are
  weakly admissible.
* `TopologicalRing.continuous_constantsToTAdicPowerSeries`: the homomorphism of the example is
  continuous.
* `TopologicalRing.not_isTaut_constantsToTAdicPowerSeries`: the homomorphism of the example is
  not taut.
* `AlgebraicGeometry.FormalSpace.not_isRepresentableByAlgebraicSpaces_formalSpectrumMap_constants`:
  the formal spectrum of the homomorphism of the example is not representable by algebraic
  spaces, from the implication (1) ⟹ (3) of Stacks 0AN5 in the form
  `IsTautOfRepresentableFormalSpectrumMap`. The unconditional statement, which uses the proved
  implication `AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`
  instead, is
  `AlgebraicGeometry.FormalSpace.not_isRepresentableByAlgebraicSpaces_formalSpectrumMap_constants'`.

## Implementation notes

A discrete topology is the `⊥`-adic one and a discrete module is `⊥`-adically complete, while
`k⟦t⟧` is `(t)`-adically complete by `PowerSeries.instIsAdicComplete`; weak admissibility of
both rings is therefore `TopologicalRing.isWeaklyAdmissible_of_isAdic`. The `t`-adic topology
is attached to `k⟦t⟧` through a type synonym carrying a `WithIdeal` instance, which supplies
the topology, its compatibility with the ring structure, and the linearity of the topology all
at once; the discrete side is left as a hypothesis `[DiscreteTopology k]` on `k` itself, whose
linear topology is transported from the `⊥`-adic one.

Non-tautness is read off the first clause of `RingHom.IsTaut`, openness of the closed extended
ideals, and does not need the basis clause. The witness is the zero ideal, which is open in a
discrete ring; its extension is zero, hence closed because a weakly admissible ring is
separated, so tautness would make `{0}` a neighbourhood of zero in `k⟦t⟧` and therefore make
some `(t)ⁿ` vanish.

The second sense of the remark is not treated here. Its example is the lemma of Stacks 0CBE,
`AlgebraicGeometry.FormalSpace.exists_representable_hasSomeSurjectivePresentation_not`, and the
second sense is
`AlgebraicGeometry.FormalSpace.exists_representable_formalSpectrum_not_mcQuillan` in
`StacksFrontier.AlgebraicGeometry.FormalSpace.SharpnessOfRepresentabilityExamples`.

## References

* [Stacks Project, Tag 0AN7](https://stacks.math.columbia.edu/tag/0AN7)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AMX](https://stacks.math.columbia.edu/tag/0AMX)
* [Stacks Project, Tag 0CBC](https://stacks.math.columbia.edu/tag/0CBC)
* [Stacks Project, Tag 0CBE](https://stacks.math.columbia.edu/tag/0CBE)
-/

@[expose] public noncomputable section

namespace TopologicalRing

universe u

/-! ### A field with the discrete topology -/

/-- A discrete ring carries the `⊥`-adic topology. -/
theorem isAdic_bot_of_discreteTopology (k : Type u) [CommRing k] [TopologicalSpace k]
    [DiscreteTopology k] : _root_.IsAdic (⊥ : Ideal k) :=
  is_bot_adic_iff.mpr inferInstance

/-- The topology of a discrete ring is linear: it is the `⊥`-adic topology, and an adic
topology has the powers of its defining ideal as a basis of open ideals. -/
instance isLinearTopology_of_discreteTopology (k : Type u) [CommRing k] [TopologicalSpace k]
    [DiscreteTopology k] : IsLinearTopology k k :=
  isAdic_bot_of_discreteTopology k ▸ (⊥ : Ideal k).isLinearTopology

/-- A discrete ring is weakly admissible: the zero ideal is a weak ideal of definition, and a
discrete ring is complete and separated. -/
theorem isWeaklyAdmissible_discreteTopology (k : Type u) [CommRing k] [TopologicalSpace k]
    [DiscreteTopology k] : IsWeaklyAdmissible k :=
  isWeaklyAdmissible_of_isAdic (isAdic_bot_of_discreteTopology k) inferInstance

/-! ### Power series with the `t`-adic topology -/

/-- The ring `k⟦t⟧` of formal power series in one variable, carrying the `t`-adic topology.
Its `WithIdeal` instance names the ideal `(t)`, which is what puts the `t`-adic topology on it.
-/
def TAdicPowerSeries (k : Type u) [CommRing k] : Type u := PowerSeries k

instance instCommRingTAdicPowerSeries (k : Type u) [CommRing k] :
    CommRing (TAdicPowerSeries k) :=
  inferInstanceAs (CommRing (PowerSeries k))

instance instWithIdealTAdicPowerSeries (k : Type u) [CommRing k] :
    WithIdeal (TAdicPowerSeries k) :=
  ⟨Ideal.span {(PowerSeries.X : PowerSeries k)}⟩

/-- The distinguished ideal of `k⟦t⟧` is `(t)`. -/
theorem withIdeal_i_tAdicPowerSeries (k : Type u) [CommRing k] :
    (WithIdeal.i : Ideal (TAdicPowerSeries k)) =
      Ideal.span {(PowerSeries.X : PowerSeries k)} := rfl

/-- The topology of `TopologicalRing.TAdicPowerSeries` is the `t`-adic one. -/
theorem isAdic_tAdicPowerSeries (k : Type u) [CommRing k] :
    _root_.IsAdic (WithIdeal.i : Ideal (TAdicPowerSeries k)) := rfl

instance instIsAdicCompleteTAdicPowerSeries (k : Type u) [CommRing k] :
    IsAdicComplete (WithIdeal.i : Ideal (TAdicPowerSeries k)) (TAdicPowerSeries k) :=
  inferInstanceAs
    (IsAdicComplete (Ideal.span {(PowerSeries.X : PowerSeries k)}) (PowerSeries k))

/-- The ring `k⟦t⟧` with the `t`-adic topology is weakly admissible: it is `t`-adically
complete, and an adically complete ring carrying its adic topology is weakly admissible. -/
theorem isWeaklyAdmissible_tAdicPowerSeries (k : Type u) [CommRing k] :
    IsWeaklyAdmissible (TAdicPowerSeries k) :=
  isWeaklyAdmissible_of_isAdic (isAdic_tAdicPowerSeries k) inferInstance

/-- The zero ideal of `k⟦t⟧` is not open for the `t`-adic topology: an open neighbourhood of
zero contains some `(t)ⁿ`, and `tⁿ` is a nonzero element of it. -/
theorem not_isOpen_bot_tAdicPowerSeries (k : Type u) [CommRing k] [Nontrivial k] :
    ¬ IsOpen ((⊥ : Ideal (TAdicPowerSeries k)) : Set (TAdicPowerSeries k)) := by
  intro hopen
  rw [Submodule.bot_coe] at hopen
  obtain ⟨n, -, hn⟩ :=
    ((WithIdeal.i : Ideal (TAdicPowerSeries k)).hasBasis_nhds_zero_adic).mem_iff.mp
      (hopen.mem_nhds rfl)
  have hmem : (PowerSeries.X : PowerSeries k) ^ n ∈ (WithIdeal.i : Ideal (TAdicPowerSeries k)) ^ n
      := Ideal.pow_mem_pow (by rw [withIdeal_i_tAdicPowerSeries]; exact Ideal.subset_span rfl) n
  have hvanish : (PowerSeries.X : PowerSeries k) ^ n = 0 := hn hmem
  have hcoeff := congrArg (PowerSeries.coeff (R := k) n) hvanish
  rw [PowerSeries.coeff_X_pow_self] at hcoeff
  exact one_ne_zero hcoeff

/-! ### The homomorphism of the example -/

/-- The inclusion of constants `k → k⟦t⟧`, with `k` discrete and `k⟦t⟧` carrying the `t`-adic
topology. This is the continuous homomorphism of weakly admissible topological rings of the
example of Stacks 0AN7. -/
def constantsToTAdicPowerSeries (k : Type u) [CommRing k] : k →+* TAdicPowerSeries k :=
  PowerSeries.C

/-- The inclusion of constants of a discrete ring into `k⟦t⟧` is continuous, the source being
discrete. -/
theorem continuous_constantsToTAdicPowerSeries (k : Type u) [CommRing k] [TopologicalSpace k]
    [DiscreteTopology k] : Continuous (constantsToTAdicPowerSeries k) :=
  continuous_of_discreteTopology

/-- The example for the first sense of **Stacks 0AN7**, at the level of rings. Let `k` be a field
with the discrete topology and let `k⟦t⟧` carry the `t`-adic topology. The inclusion of
constants is a continuous homomorphism of weakly admissible topological rings which is not
taut: the zero ideal of `k` is open, its extension to `k⟦t⟧` is the zero ideal and is closed
because `k⟦t⟧` is separated, and the zero ideal of `k⟦t⟧` is not open. -/
theorem not_isTaut_constantsToTAdicPowerSeries (k : Type u) [Field k] [TopologicalSpace k]
    [DiscreteTopology k] : ¬ RingHom.IsTaut (constantsToTAdicPowerSeries k) := by
  rintro ⟨hopen, -⟩
  have hbot := hopen ⊥ (isOpen_discrete _)
  rw [Ideal.map_bot] at hbot
  have hclosure : (⊥ : Ideal (TAdicPowerSeries k)).closure = ⊥ := by
    refine Ideal.closure_eq_of_isClosed _ ?_
    have : T2Space (TAdicPowerSeries k) := (isWeaklyAdmissible_tAdicPowerSeries k).2.2
    rw [Submodule.bot_coe]
    exact isClosed_singleton
  rw [hclosure] at hbot
  exact not_isOpen_bot_tAdicPowerSeries k hbot

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

open CategoryTheory

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The implication (1) ⟹ (3) of **Stacks 0AN5**, as a proposition quantified over all quotient
systems with no condition on the site: a continuous homomorphism of weakly admissible
topological rings over `S` whose formal spectrum is representable by algebraic spaces is taut.
The library proves this implication when both quotient systems satisfy the set-theoretic
condition of Stacks 0AIS,
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`,
and when both formal spectra are affine formal algebraic spaces,
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isAffine`.
-/
abbrev IsTautOfRepresentableFormalSpectrumMap : Prop :=
  ∀ (A C : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
    (_ : IsLinearTopology A A) (_ : CommRing C) (_ : TopologicalSpace C)
    (_ : IsTopologicalRing C) (_ : IsLinearTopology C C)
    (hA : TopologicalRing.IsWeaklyAdmissible A) (_ : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E),
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (formalSpectrumMap hA f).hom →
      RingHom.IsTaut f.toRingHom

/-- Let `k` be a field with the discrete topology, let `k⟦t⟧` carry the `t`-adic topology, and
let `Spf (φ) : Spf k⟦t⟧ ⟶ Spf k` be the formal spectrum of the inclusion of constants. Given the
implication (1) ⟹ (3) of Stacks 0AN5 in the form `IsTautOfRepresentableFormalSpectrumMap`,
`Spf (φ)` is not representable by algebraic spaces: the inclusion of constants is not taut.
The same conclusion with no hypothesis is
`AlgebraicGeometry.FormalSpace.not_isRepresentableByAlgebraicSpaces_formalSpectrumMap_constants'`,
and the first sense of **Stacks 0AN7** is
`AlgebraicGeometry.FormalSpace.exists_formalSpectrumMap_constants_not_representable`. -/
theorem not_isRepresentableByAlgebraicSpaces_formalSpectrumMap_constants
    (k : Type u) [Field k] [TopologicalSpace k] [DiscreteTopology k]
    (h0AN5 : IsTautOfRepresentableFormalSpectrumMap B S hS)
    (D : QuotientSystem B S hS k)
    (E : QuotientSystem B S hS (TopologicalRing.TAdicPowerSeries k))
    (f : ContinuousHom D E)
    (hf : f.toRingHom = TopologicalRing.constantsToTAdicPowerSeries k) :
    ¬ Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (formalSpectrumMap (TopologicalRing.isWeaklyAdmissible_discreteTopology k) f).hom := by
  intro hrep
  refine TopologicalRing.not_isTaut_constantsToTAdicPowerSeries k (hf ▸ ?_)
  exact h0AN5 k (TopologicalRing.TAdicPowerSeries k) _ _ _ _ _ _ _ _
    (TopologicalRing.isWeaklyAdmissible_discreteTopology k)
    (TopologicalRing.isWeaklyAdmissible_tAdicPowerSeries k) D E f hrep

end AlgebraicGeometry.FormalSpace

end
