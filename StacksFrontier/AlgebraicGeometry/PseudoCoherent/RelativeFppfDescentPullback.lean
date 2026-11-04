module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeFppfDescent

/-!
# The fppf pullback of relative pseudo-coherence

Let `f : X ⟶ S` be locally of finite type, let `{g i : Y i ⟶ X}` be an fppf covering of schemes,
let `E` be an object of `D(𝒪_X)` and let `m` be an integer. If `E` is `m`-pseudo-coherent relative
to `S`, then so is every derived pullback `L(g i)^*E`: this is the forward implication of
Stacks 0CSN. It is
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_mem_fppfPrecoverage` with
its hypothesis `AlgebraicGeometry.Scheme.Hom.RelativePseudoCoherencePullbackAlongPseudoCoherent`
supplied by Stacks 09US, `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_comp_derivedPullback`,
whose statement is that proposition verbatim.

## Main results

* `AlgebraicGeometry.Scheme.Hom.relativePseudoCoherencePullbackAlongPseudoCoherent_of_baseChange`:
  Stacks 09US, as the proposition
  `AlgebraicGeometry.Scheme.Hom.RelativePseudoCoherencePullbackAlongPseudoCoherent`.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_mem_fppfPrecoverage'`:
  the forward implication of Stacks 0CSN.

## Implementation notes

**Why the instance binder is repeated in a `letI`.** The conclusion mentions
`LocallyOfFiniteType (g i ≫ f)`, which
`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom` takes as an instance argument and which
follows from the covering rather than from the binders. The statement below therefore binds
`LocallyOfFinitePresentation (g i)` with a term-level `letI` exactly as the statement it
strengthens does, so that the two propositions are literally the same apart from the replaced
hypothesis. The instance argument does not occur in the body of the predicate, so the choice of
derivation does not affect the proposition.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`, made
a local instance at a high priority because part of the import closure supplies a global instance
of the same class; this is the declaration made by Stacks 09UI and by both of the statements
combined here, in whose spelling the statements below are read.

## References

* [The Stacks Project, Lemma 37.70.1 (0CSN)](https://stacks.math.columbia.edu/tag/0CSN)
* [The Stacks Project, Lemma 37.59.16 (09US)](https://stacks.math.columbia.edu/tag/09US)
* [The Stacks Project, Lemma 36.22.9 (0E23)](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.PseudoCoherence.FlatDescent
  (locallyOfFinitePresentation_of_mem_fppfPrecoverage)

namespace AlgebraicGeometry

universe v u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Scheme.Hom

/-- **Stacks 09US, as the proposition
`AlgebraicGeometry.Scheme.Hom.RelativePseudoCoherencePullbackAlongPseudoCoherent`.** If
`p : X ⟶ Y` is a pseudo-coherent morphism of schemes, `q : Y ⟶ S` is locally of finite type and
`E` is an object of `D(𝒪_Y)` which is `m`-pseudo-coherent relative to `S`, then `Lp^*E` is
`m`-pseudo-coherent relative to `S`. The hypothesis `_hbc`, the conclusion of Stacks 0E23, is not
used. -/
public theorem relativePseudoCoherencePullbackAlongPseudoCoherent_of_baseChange
    (_hbc : DerivedBaseChangeIsoOfTorIndependent.{u}) :
    RelativePseudoCoherencePullbackAlongPseudoCoherent.{u} := by
  intro X Y S p q _ _ E m hE
  exact isPseudoCoherentFrom_comp_derivedPullback p q E m hE

/-- **The forward implication of Stacks 0CSN.** Let `f : X ⟶ S` be locally of finite type, let
`{g i : Y i ⟶ X}` be an fppf covering of schemes, let `E` be an object of `D(𝒪_X)` and let `m` be
an integer. If `E` is `m`-pseudo-coherent relative to `S`, then so is `L(g i)^*E` for every member
`g i` of the covering.

The hypothesis `hbc`, the conclusion of Stacks 0E23, is not needed: Stacks 09US,
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_comp_derivedPullback`, holds without it.
Neither joint surjectivity of the covering nor any hypothesis on the cohomology sheaves of `E` is
needed. -/
public theorem isPseudoCoherentFrom_derivedPullback_of_mem_fppfPrecoverage'
    {X S : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u}) (g : ∀ i, Y i ⟶ X) (f : X ⟶ S)
    [LocallyOfFiniteType f] (hg : Presieve.ofArrows Y g ∈ Scheme.fppfPrecoverage X)
    (hbc : DerivedBaseChangeIsoOfTorIndependent.{u})
    (E : DerivedCategory X.Modules) (m : ℤ) (hE : f.IsPseudoCoherentFrom E m) (i : ι) :
    letI : LocallyOfFinitePresentation (g i) :=
      locallyOfFinitePresentation_of_mem_fppfPrecoverage Y g hg i
    (g i ≫ f).IsPseudoCoherentFrom ((derivedPullback (g i).toLRSHom.toShHom).obj E) m :=
  isPseudoCoherentFrom_derivedPullback_of_mem_fppfPrecoverage Y g f hg
    (relativePseudoCoherencePullbackAlongPseudoCoherent_of_baseChange hbc) E m hE i

end Scheme.Hom

end AlgebraicGeometry


add_to_stacks 0CSN "THE FORWARD IMPLICATION ONLY, with the Stacks 09US hypothesis DISCHARGED;
the tag is an iff and its converse is NOT proved. Base already registers the forward half at
PseudoCoherent/RelativeFppfDescent.lean:148, which carries 09US as a hypothesis; that file's own
notes say discharging it is what would make the implication unconditional. 09US is now proved
(PseudoCoherent/DerivedPullback09US.lean:634), so this restatement carries only 0E23
(DerivedBaseChangeIsoOfTorIndependent), which 09US itself already requires -- strictly fewer
hypotheses than the base form. The covering is genuinely fppf (Presieve.ofArrows in
Scheme.fppfPrecoverage), not etale or Zariski; no quasi-compactness, finiteness or Noetherian
hypothesis is added, and nothing is assumed about E's cohomology sheaves. THE CONVERSE needs
exactly two things the library lacks: Stacks 08EU at a GENERAL K (the library has it only at
K = O_Y[0], and its docstring says the devissage to general K is not carried out), and
the local splitting of O_X -> pi_* O_Y for a surjective finite locally free pi, which is absent
entirely."
  AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_mem_fppfPrecoverage'

end
