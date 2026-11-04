module

public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.NoetherianBase

/-!
# The finite-type clause of Tag 0EX4 over a locally Noetherian base, unconditionally

[Stacks, Tag 0EX4] asserts, for `f : X ⟶ Y` proper all of whose fibres have dimension at most
`d` and `F` quasi-coherent of finite type, that `R ᵈ f_* F` is quasi-coherent of finite type.
`StacksFrontier/AlgebraicGeometry/TopDegreeFiniteType/NoetherianBase.lean` proves the finite-type
half of that conclusion over a locally Noetherian base, in every degree and with no hypothesis
on the fibres, from [Stacks, Tag 02O6] carried as a hypothesis. That hypothesis is a theorem:
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology` proves [Stacks, Tag 02O6]
with no hypothesis at all. This file composes the two.

**Why the composition needs a separate module.**
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology` is proved by dévissage over
Chow's lemma, and its import cone contains `NoetherianBase.lean` itself — through
`StacksFrontier/AlgebraicGeometry/CohomologyFinitenessCoproduct/RingBase.lean`, which consumes
`…TopDegreeFiniteType.isFiniteType_rightDerived_of_forall_exists_epi_ringBase`. So the
hypothesis cannot be discharged where it is written: doing so would make the module that states
the reduction import the module that proves its input. The discharge happens here instead, above
both.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeFiniteType`'s
  `isFiniteType_rightDerived_of_isProper_of_isLocallyNoetherian`: **the finite-type clause of
  [Stacks, Tag 0EX4] over a locally Noetherian base, with no hypothesis** — in every degree and
  with no bound on the fibres of `f`.

## Implementation notes

**The `@[stacks 0EX4]` attribute here is for the finite-type clause over a locally Noetherian
base only.** The tag's base carries no Noetherian hypothesis, and that part of it — the source's
limit argument, [Stacks, Tags 09ZR, 05M5, 01ZM, 081F, 01ZR, 0EX3, 086M] — is untouched; the
residue is located in `TopDegreeFiniteType/AffineBase.lean` and
`TopDegreeFiniteType/AffineModuleFinite.lean`. The quasi-coherence clause carries its own
`@[stacks 0EX4 "quasi-coherence"]` in
`StacksFrontier/AlgebraicGeometry/ProperQcoh/Basic.lean`.

**The fibre-dimension bound is absent rather than assumed.** The statement below is strictly
stronger than the tag's finite-type clause read at a locally Noetherian base: over such a base
the bound is provably inert, which is what
`…TopDegreeFiniteType.forall_isFiniteType_rightDerived_iff_forall_moduleFinite_cohomology`
measures. A consumer wanting the tag's own shape instantiates this and discards the bound.

## References

* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeFiniteType

/-! ### The finite-type clause of Tag 0EX4 over a locally Noetherian base -/

/-- **The finite-type clause of [Stacks, Tag 0EX4] over a locally Noetherian base.** For
`f : X ⟶ Y` proper with `Y` locally Noetherian and `F` quasi-coherent of finite type, the
`𝒪_Y`-module `R ᵈ f_* F` is of finite type in every degree `d`, with no bound on the fibres
of `f`. -/
@[stacks 0EX4 "finite-type clause only, and only over a locally Noetherian base; there in \
every degree and with no hypothesis on the fibres. An arbitrary base is not covered."]
theorem isFiniteType_rightDerived_of_isProper_of_isLocallyNoetherian {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (d : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFiniteType :=
  isFiniteType_rightDerived_of_moduleFinite_cohomology f F d
    (fun X₀ S₀ g hg hS₀ hS₀N G hG n =>
      @_root_.AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology
        X₀ S₀ g hg hS₀ hS₀N G hG n)

end Stacks.AlgebraicGeometry.TopDegreeFiniteType

end
