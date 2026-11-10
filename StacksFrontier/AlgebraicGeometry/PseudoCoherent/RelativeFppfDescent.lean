module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FppfDescent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Relative
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedPullback
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US

/-!
# Relative `m`-pseudo-coherence along an fppf covering

Let `f : X ⟶ S` be locally of finite type, let `{g i : Y i ⟶ X}` be an fppf covering of schemes,
let `E` be an object of `D(𝒪_X)` and let `m` be an integer. Stacks 0CSN says that `E` is
`m`-pseudo-coherent relative to `S` if and only if every derived pullback `L(g i)^*E` is
`m`-pseudo-coherent relative to `S`, for `E` with quasi-coherent cohomology sheaves.

What is proved here is the forward implication, which is the source's first paragraph: a member of
an fppf covering is flat and locally of finite presentation, hence a pseudo-coherent morphism by
Stacks 0695, and relative `m`-pseudo-coherence is preserved by derived pullback along a
pseudo-coherent morphism by Stacks 09US. No quasi-coherence of the cohomology sheaves of `E` is
needed for this implication, and neither is joint surjectivity of the covering: the statement
below is proved one member at a time.

Stacks 09US is not available in the library, so it is carried as the hypothesis
`AlgebraicGeometry.Scheme.Hom.RelativePseudoCoherencePullbackAlongPseudoCoherent`, which is its
statement verbatim and nothing more. Everything else is discharged.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.RelativePseudoCoherencePullbackAlongPseudoCoherent`: Stacks 09US
  as a proposition, so that it can be carried as a hypothesis.

## Main results

* `isPseudoCoherentFrom_derivedPullback_of_flat_of_locallyOfFinitePresentation`, in
  `AlgebraicGeometry.Scheme.Hom`: the single-morphism form — along a flat morphism locally of
  finite presentation, relative `m`-pseudo-coherence is preserved by derived pullback.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback_of_mem_fppfPrecoverage`:
  **the forward implication of Stacks 0CSN.**

## Implementation notes

**Why Stacks 09US is carried.** The library has no declaration for Stacks 09US: relative
`m`-pseudo-coherence is `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom` (Stacks 09UI) and the
results proved about its behaviour under derived pullback are Stacks 09UR, base change along a
Tor-independent square, in `AlgebraicGeometry.Scheme.Hom` under the name
`isPseudoCoherentFrom_derivedPullback_of_torIndependentCharts`, and the *absolute* Stacks 09U7
(`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPseudoCoherentFrom_derivedPullback`, read at
a morphism of schemes as `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_derivedPullback`).
Neither gives the pullback of a *relative* condition along an arbitrary pseudo-coherent morphism:
a member of an fppf covering is not a base change of `X` over `S`, and the absolute statement says
nothing about the relative one. So the hypothesis is the shortest honest input, and discharging it
is what would turn the implication below into an unconditional theorem.

**What is not proved.** The converse implication of Stacks 0CSN — descent — is not proved here.
Its argument refines the covering by Zariski coverings and surjective finite locally free
morphisms (Stacks 05WN, `AlgebraicGeometry.exists_openCover_finiteLocallyFree_refinement`), uses
Stacks 0683 (`AlgebraicGeometry.pseudoCoherent_of_comp`) and Stacks 09US to move the hypothesis to
the refinement, and then descends along one surjective finite locally free `π : Y ⟶ X` using
Stacks 09UK (`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward`), the
projection formula identification `Rπ_*Lπ^*E ≅ E ⊗^L π_*𝒪_Y` of Stacks 08EU and 08D7, and
Stacks 09UN (`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom.of_biprod_left`). The step with no
counterpart in the library is the identification of `Rπ_*Lπ^*E` with `E ⊗^L π_*𝒪_Y` together with
the local splitting of `𝒪_X ⟶ π_*𝒪_Y`; that is where the quasi-coherence hypothesis on `E` enters,
and it is why the statement below carries no such hypothesis.

**The index type of the covering.** A family in `AlgebraicGeometry.Scheme.fppfPrecoverage` is a
`CategoryTheory.Presieve.ofArrows`, whose index type may live in any universe; it is kept free
here. Flatness and finite presentation of a member are not re-derived: they are
`Stacks.Cohomology.PseudoCoherence.FlatDescent.flat_of_mem_fppfPrecoverage` and
`Stacks.Cohomology.PseudoCoherence.FlatDescent.locallyOfFinitePresentation_of_mem_fppfPrecoverage`,
proved with Stacks 09UF, and they are the only two names opened from that namespace.

**Locally of finite type for the composite.** `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom`
takes `[LocallyOfFiniteType _]` as an instance argument, and for the composite `g i ≫ f` that
instance follows from the covering rather than from the binders, so the statement binds it with a
term-level `letI`. The instance argument does not occur in the body of the predicate, so which
derivation is used does not affect the proposition.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`, made
a local instance at a high priority because part of the import closure supplies a global instance
of the same class; the same declaration is made by Stacks 09UI, in whose spelling the statements
below are read.

## References

* [The Stacks Project, Lemma 37.70.1 (0CSN)](https://stacks.math.columbia.edu/tag/0CSN)
* [The Stacks Project, Lemma 37.59.13 (09US)](https://stacks.math.columbia.edu/tag/09US)
* [The Stacks Project, Lemma 37.60.9 (0695)](https://stacks.math.columbia.edu/tag/0695)
* [The Stacks Project, Definition 37.59.2 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.PseudoCoherence.FlatDescent
  (flat_of_mem_fppfPrecoverage locallyOfFinitePresentation_of_mem_fppfPrecoverage)

namespace AlgebraicGeometry

universe v u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Scheme.Hom

/-- **Stacks 09US** as a proposition: if `p : X ⟶ Y` is a pseudo-coherent morphism of schemes,
`q : Y ⟶ S` is locally of finite type and `E` is an object of `D(𝒪_Y)` which is
`m`-pseudo-coherent relative to `S`, then `Lp^*E` is `m`-pseudo-coherent relative to `S`.

The source phrases the hypothesis on `p` as pseudo-coherence of `𝒪_X` relative to `Y`, which by
the footnote of the source is pseudo-coherence of `p` in the sense of Stacks 067Z, i.e.
`AlgebraicGeometry.PseudoCoherent`. The instance `LocallyOfFiniteType (p ≫ q)` needed to state the
conclusion is found from `[PseudoCoherent p]` through Stacks 0682. -/
public abbrev RelativePseudoCoherencePullbackAlongPseudoCoherent : Prop :=
  ∀ {X Y S : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ S) [LocallyOfFiniteType q] [PseudoCoherent p]
      (E : DerivedCategory Y.Modules) (m : ℤ),
    q.IsPseudoCoherentFrom E m →
      (p ≫ q).IsPseudoCoherentFrom ((derivedPullback p.toLRSHom.toShHom).obj E) m

/-- **The first paragraph of Stacks 0CSN, for a single morphism.** Let `f : X ⟶ S` be locally of
finite type, let `p : X' ⟶ X` be flat and locally of finite presentation and let `E` be an object
of `D(𝒪_X)` which is `m`-pseudo-coherent relative to `S`. Then `Lp^*E` is `m`-pseudo-coherent
relative to `S`.

Such a `p` is a pseudo-coherent morphism by Stacks 0695,
`AlgebraicGeometry.pseudoCoherent_of_flat_of_locallyOfFinitePresentation`, so the carried
Stacks 09US applies. -/
public theorem isPseudoCoherentFrom_derivedPullback_of_flat_of_locallyOfFinitePresentation
    {X' X S : Scheme.{u}} (p : X' ⟶ X) (f : X ⟶ S) [LocallyOfFiniteType f] [Flat p]
    [LocallyOfFinitePresentation p]
    (h09US : RelativePseudoCoherencePullbackAlongPseudoCoherent.{u})
    (E : DerivedCategory X.Modules) (m : ℤ) (hE : f.IsPseudoCoherentFrom E m) :
    (p ≫ f).IsPseudoCoherentFrom ((derivedPullback p.toLRSHom.toShHom).obj E) m :=
  h09US p f E m hE

/-- **Stacks 0CSN, the forward implication.** Let `f : X ⟶ S` be locally of finite type, let
`{g i : Y i ⟶ X}` be an fppf covering of schemes, let `E` be an object of `D(𝒪_X)` and let `m` be
an integer. If `E` is `m`-pseudo-coherent relative to `S`, then so is `L(g i)^*E` for every member
`g i` of the covering.

This is a corollary of Stacks 09US,
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_comp_derivedPullback`, and it is the forward
branch of Stacks 0CSN,
`Scheme.Hom.isPseudoCoherentFrom_iff_forall_derivedPullback_of_mem_fppfPrecoverage`:
the member `g i` is flat and locally of finite presentation because the covering lies in the fppf
precoverage, hence pseudo-coherent by Stacks 0695. Joint
surjectivity of the covering is not used, and no hypothesis on the cohomology sheaves of `E` is
needed: both enter only in the converse implication. -/
public theorem isPseudoCoherentFrom_derivedPullback_of_mem_fppfPrecoverage
    {X S : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u}) (g : ∀ i, Y i ⟶ X) (f : X ⟶ S)
    [LocallyOfFiniteType f] (hg : Presieve.ofArrows Y g ∈ Scheme.fppfPrecoverage X)
    (E : DerivedCategory X.Modules) (m : ℤ) (hE : f.IsPseudoCoherentFrom E m) (i : ι) :
    letI : LocallyOfFinitePresentation (g i) :=
      locallyOfFinitePresentation_of_mem_fppfPrecoverage Y g hg i
    (g i ≫ f).IsPseudoCoherentFrom ((derivedPullback (g i).toLRSHom.toShHom).obj E) m :=
  letI : LocallyOfFinitePresentation (g i) :=
    locallyOfFinitePresentation_of_mem_fppfPrecoverage Y g hg i
  haveI : Flat (g i) := flat_of_mem_fppfPrecoverage Y g hg i
  isPseudoCoherentFrom_comp_derivedPullback (g i) f E m hE

end Scheme.Hom

end AlgebraicGeometry

end
