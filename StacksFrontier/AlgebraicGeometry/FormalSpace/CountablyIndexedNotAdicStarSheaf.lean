module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedAdicStar
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.Topology.Algebra.AdicTopology.EquivTransport

/-!
# Gabber's countably indexed completion is not adic\* (Stacks 0APW, clause (2))

Clause (1) of **Stacks 0APW** says that the completion of `Spec A` along a closed set `T` cut
out by *countably many* equations is adic\* as soon as it is countably indexed; it is
`AlgebraicGeometry.FormalSpace.isAdicStar_countableCompletion`. Clause (2) says that the
countability of the equations cannot be dropped, and Gabber's example — the `ℚ`-algebra on
`x_α`, `α ∈ ω₁`, and `y_{αβ}`, modulo `x_α = y_{αβ} x_β`, completed along
`T = V(x_α : α ∈ ω₁)` — witnesses it. The ring-theoretic halves of the example are in
`StacksFrontier/AlgebraicGeometry/FormalSpace/CountablyIndexedNotAdicStarExample.lean`:
`AlgebraicGeometry.FormalSpace.isCofinalVanishingSequence_gabberPowerIdeal` and
`AlgebraicGeometry.FormalSpace.gabberCompletion_no_fg_isWeakIdealOfDefinition`. This file
lifts them to the fppf sheaf they are about.

The lift is not formal. Adic\*-ness of a sheaf quantifies *existentially* over the topological
rings presenting it, so exhibiting one presenting ring with no finitely generated ideal of
definition refutes nothing on its own: what is needed is that *every* presenting ring is
isomorphic, as a topological ring, to the inverse limit of the cofinal sequence. That is the
uniqueness of the associated ring of **Stacks 0AIC**, now available as
`AlgebraicGeometry.FormalSpace.exists_continuous_ringEquiv_of_isPresentingRing`, together with
the transport of the conditions of **Stacks 0AID** along such an isomorphism, from
`StacksFrontier/Topology/Algebra/AdicTopology/EquivTransport.lean`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.gabberCompletionSheaf`: the completion of `Spec A` along `T`
  for Gabber's ring `A` and the sequence `J_n = (x_α^(n+1))`, as an fppf sheaf over `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.isPresentingRing_countableCompletion`: the inverse limit of a
  decreasing sequence of ideals all cutting out `T` presents the completion of `Spec A` along
  `T` that the sequence defines.
* `AlgebraicGeometry.FormalSpace.isCountablyIndexedAffine_countableCompletion`: such a
  completion is a countably indexed affine formal algebraic space.
* `AlgebraicGeometry.FormalSpace.not_isAdicStar_countableCompletion`: if that inverse limit
  has no finitely generated weak ideal of definition then the completion is not adic\*.
* `AlgebraicGeometry.FormalSpace.isCountablyIndexed_not_isAdicStar_gabberCompletionSheaf`:
  **clause (2) of Stacks 0APW at sheaf level**, the two halves for Gabber's example.

## Implementation notes

The statement is parametrised over the ambient site exactly as clause (1) is: a big fppf site
`B` containing `S` and `Spec A`, and a structure morphism `Spec A ⟶ S`. Nothing is assumed
about them beyond that, so the example is available over every base over which Gabber's ring
is a scheme of the site.

Countable indexedness of the completion is read off **Stacks 0AN1**, condition (2) implies
condition (1): the inverse limit of the sequence is weakly admissible, the kernels of its
projections are a countable fundamental system of neighbourhoods of zero, and
`AlgebraicGeometry.FormalSpace.countableCompletionIsoFormalSpectrum` identifies the completion
with its formal spectrum. The absence of a finitely generated *weak* ideal of definition is
what the example provides, and it is more than is needed: an ideal of definition is a weak one
by `TopologicalRing.isWeakIdealOfDefinition_of_isIdealOfDefinition`.

## References

* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AN1](https://stacks.math.columbia.edu/tag/0AN1)
* [Stacks Project, Tag 0APW](https://stacks.math.columbia.edu/tag/0APW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

attribute [local instance] idealSequenceLimitTopology isTopologicalRing_idealSequenceLimit
  isLinearTopology_idealSequenceLimit sheaf_hasColimits

variable {A : Type u} [CommRing A]

/-! ### The completion of an affine scheme along a cofinal sequence of ideals -/

/-- The inverse limit `Q = lim A ⧸ J' n` of a decreasing sequence of ideals all cutting out the
same closed set presents the completion of `Spec A` along that closed set: it is weakly
admissible, and the completion is the colimit of the spectra of its quotients by weak ideals of
definition. -/
theorem isPresentingRing_countableCompletion (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (f : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {T : Set (PrimeSpectrum A)} (J' : ℕ → Ideal A) (hJ'dec : ∀ n, J' (n + 1) ≤ J' n)
    (hJ'zero : ∀ n, PrimeSpectrum.zeroLocus (J' n : Set A) = T) :
    IsPresentingRing B S hS (IdealSequenceLimit A J' hJ'dec)
      (countableCompletion B S hS f hA J' hJ'dec) :=
  ⟨isWeaklyAdmissible_countableCompletion J' hJ'dec hJ'zero,
    ⟨countableCompletionWeakIdealPresentation B S hS f hA J' hJ'dec hJ'zero⟩⟩

/-- **Stacks 0AN1, condition (2) implies condition (1), for a completion along a cofinal
sequence.** The completion of `Spec A` along a closed set `T`, presented by a decreasing
sequence of ideals all cutting out `T`, is a countably indexed affine formal algebraic space:
the inverse limit of the quotients is weakly admissible and the kernels of its projections are
a countable fundamental system of neighbourhoods of zero. -/
theorem isCountablyIndexedAffine_countableCompletion (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (f : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {T : Set (PrimeSpectrum A)} (J' : ℕ → Ideal A) (hJ'dec : ∀ n, J' (n + 1) ≤ J' n)
    (hJ'zero : ∀ n, PrimeSpectrum.zeroLocus (J' n : Set A) = T) :
    IsCountablyIndexedAffine B S hS (countableCompletion B S hS f hA J' hJ'dec) :=
  isCountablyIndexedAffine_of_hasCountableWeakPresentation B S hS _
    ⟨{ ring := IdealSequenceLimit A J' hJ'dec
       system := countableCompletionQuotientSystem B S hS f hA J' hJ'dec
       iso := ⟨countableCompletionIsoFormalSpectrum B S hS f hA J' hJ'dec hJ'zero⟩ },
      isWeaklyAdmissible_countableCompletion J' hJ'dec hJ'zero,
      (idealSequenceLimit_hasBasis_nhds_zero J' hJ'dec).isCountablyGenerated⟩

/-- **The criterion for a completion along a cofinal sequence not to be adic\*.** If the
inverse limit `Q = lim A ⧸ J' n` has no finitely generated weak ideal of definition, then the
completion of `Spec A` along `T` presented by the sequence is not adic\*.

Adic\*-ness quantifies existentially over the presenting rings, so the hypothesis on `Q` alone
would not suffice: the proof uses that every ring presenting the completion is isomorphic as a
topological ring to `Q`, which is the uniqueness of the associated ring of Stacks 0AIC, and
then transports the finitely generated ideal of definition back to `Q`. -/
theorem not_isAdicStar_countableCompletion (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (f : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
    {T : Set (PrimeSpectrum A)} (J' : ℕ → Ideal A) (hJ'dec : ∀ n, J' (n + 1) ≤ J' n)
    (hJ'zero : ∀ n, PrimeSpectrum.zeroLocus (J' n : Set A) = T)
    (hno : ¬ ∃ I : Ideal (IdealSequenceLimit A J' hJ'dec),
      I.FG ∧ TopologicalRing.IsWeakIdealOfDefinition I) :
    ¬ IsAdicStar B S hS (countableCompletion B S hS f hA J' hJ'dec) := by
  rintro ⟨hpres, C, instCR, instTS, instTR, instLT, hCpres, -, I, hIdef, hIfg⟩
  let : CommRing C := instCR
  let : TopologicalSpace C := instTS
  let : IsTopologicalRing C := instTR
  let : IsLinearTopology C C := instLT
  obtain ⟨φ, hφ, hφ'⟩ := exists_continuous_ringEquiv_of_isPresentingRing hCpres
    (isPresentingRing_countableCompletion B S hS f hA J' hJ'dec hJ'zero)
  obtain ⟨JQ, hJQdef, hJQfg⟩ :=
    TopologicalRing.exists_fg_isIdealOfDefinition_of_ringEquiv φ hφ hφ' ⟨I, hIdef, hIfg⟩
  exact hno ⟨JQ, hJQfg,
    TopologicalRing.isWeakIdealOfDefinition_of_isIdealOfDefinition hJQdef⟩

/-! ### Gabber's example at sheaf level -/

/-- **Gabber's example as an fppf sheaf.** The completion of `Spec A` along
`T = V(x_α : α ∈ ω₁)` for Gabber's ring `A`, presented by the sequence of ideals
`J_n = (x_α^(n+1))`: the colimit, in fppf sheaves over `S`, of the spectra of the quotients
`A ⧸ J_n`. -/
def gabberCompletionSheaf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (f : Spec (.of GabberRing.{u}) ⟶ S) (hA : B.Contains (Spec (.of GabberRing.{u}))) :
    FppfSheaf B S hS :=
  countableCompletion B S hS f hA gabberPowerIdeal.{u} gabberPowerIdeal_antitone.{u}

/-- **Stacks 0APW (2).** Gabber's completion is a countably indexed affine formal algebraic
space which is not adic\*: so the hypothesis of clause (1) that the closed set be cut out by
countably many functions cannot be dropped.

Both halves are the ring-theoretic ones of
`StacksFrontier/AlgebraicGeometry/FormalSpace/CountablyIndexedNotAdicStarExample.lean` read at
sheaf level. Countable indexedness is the cofinality of the sequence `J_n`, through Stacks
0AN1. For the failure of adic\*-ness, every topological ring presenting the completion is
isomorphic to `lim A ⧸ J_n` by the uniqueness of the associated ring of Stacks 0AIC, so a
finitely generated ideal of definition of any of them would give one of `lim A ⧸ J_n`, and
hence a finitely generated weak ideal of definition, which that ring has none of. -/
@[stacks 0APW "clause (2) at sheaf level: Gabber's completion is countably indexed and is not \
adic star"]
theorem isCountablyIndexed_not_isAdicStar_gabberCompletionSheaf (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (f : Spec (.of GabberRing.{u}) ⟶ S)
    (hA : B.Contains (Spec (.of GabberRing.{u}))) :
    IsCountablyIndexed B S hS (gabberCompletionSheaf B S hS f hA) ∧
      ¬ IsAdicStar B S hS (gabberCompletionSheaf B S hS f hA) := by
  refine ⟨(isCountablyIndexedAffine_countableCompletion B S hS f hA gabberPowerIdeal.{u}
    gabberPowerIdeal_antitone.{u} isCofinalVanishingSequence_gabberPowerIdeal.{u}.2.1).2, ?_⟩
  refine not_isAdicStar_countableCompletion B S hS f hA gabberPowerIdeal.{u}
    gabberPowerIdeal_antitone.{u} isCofinalVanishingSequence_gabberPowerIdeal.{u}.2.1 ?_
  rintro ⟨I, hIfg, hIweak⟩
  exact gabberCompletion_no_fg_isWeakIdealOfDefinition.{u} ⟨I, hIfg, hIweak⟩

end AlgebraicGeometry.FormalSpace

end
