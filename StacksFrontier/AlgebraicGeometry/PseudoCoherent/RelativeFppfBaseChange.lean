module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Noetherian
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FppfDescent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeAbsolute
import StacksCore.Tactic.StacksAttribute

/-!
# Relative `m`-pseudo-coherence along an fppf covering of the base

Let `f : X ⟶ S` be a morphism of schemes, let `{g i : S i ⟶ S}` be an fppf covering, write
`X i = X ×_S S i` and let `q i : X i ⟶ S i` and `p i : X i ⟶ X` be the two projections. For an
object `E` of `D(𝒪_X)` and an integer `m`, Stacks 0CSQ says that `E` is `m`-pseudo-coherent
relative to `S` if and only if every `L(p i)^*E` is `m`-pseudo-coherent relative to `S i`.

Both directions are proved here for a pseudo-coherent `f`, which by Stacks 0684 covers every `f`
locally of finite type over a locally Noetherian base. Over a pseudo-coherent morphism relative
and absolute `m`-pseudo-coherence agree (Stacks 0DII), `q i` is again pseudo-coherent because
`g i` is flat (Stacks 0680), and `{p i : X i ⟶ X}` is an fppf covering of `X`, so the equivalence
is the absolute fppf descent of Stacks 09UF read on both sides of that agreement.

## Main results

In `AlgebraicGeometry.Scheme.Hom`:

* `isPseudoCoherentFrom_iff_forall_pullback_snd_of_pseudoCoherent`: **Stacks 0CSQ for a
  pseudo-coherent `f`**, in both directions.
* `isPseudoCoherentFrom_iff_forall_pullback_snd_of_isLocallyNoetherian`: the same equivalence
  under the source's own hypothesis on `f`, that it be locally of finite type, over a locally
  Noetherian `S`.

## Implementation notes

**The range of the hypothesis on `f`.** The source asks only that `f` be locally of finite type.
For such an `f` the equivalence reduces by Stacks 0CSP, which crosses the flat morphism
`g i` locally of finite presentation, to Stacks 0CSN at the fppf covering `{p i}` of `X`; the
forward half of that is Stacks 09US, whose proof in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/DerivedPullback09US.lean:634` rests on Stacks 0E23,
which the library reaches only through the stalkwise identification
`Stacks.Cohomology.ClosedImmersionBaseChange.DerivedStalkBaseChangeEqKFlat` at
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/ClosedImmersionBaseChange.lean:181`,
and its descent half needs in addition Stacks 08EU at a general complex. Pseudo-coherence of `f`
replaces that whole route by Stacks 0DII, whose proof uses neither.

**No hypothesis on the cohomology sheaves of `E`.** The source assumes `E` in `D_QCoh(𝒪_X)`. That
hypothesis is not needed on this route: absolute fppf descent of `m`-pseudo-coherence, Stacks
09UF, holds for an arbitrary object of `D(𝒪_X)`, so the statements below quantify over all of
`D(𝒪_X)`.

**The instances on the two projections.** `q i` is locally of finite type because `f` is and that
property is stable under base change, so the right-hand side needs no instance beyond the
binders; the flatness of `g i` that turns `q i` into a pseudo-coherent morphism is read off the
covering inside the proof.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
made a local instance at a high priority because part of the import closure supplies a global
instance of the same class; this is the declaration made by Stacks 09UI, 09UF and 0DII, in whose
spelling the statements below are read.

## References

* [The Stacks Project, Lemma 37.70.3 (0CSQ)](https://stacks.math.columbia.edu/tag/0CSQ)
* [The Stacks Project, Lemma 37.59.19 (0DII)](https://stacks.math.columbia.edu/tag/0DII)
* [The Stacks Project, Lemma 36.12.3 (09UF)](https://stacks.math.columbia.edu/tag/09UF)
* [The Stacks Project, Lemma 37.60.3 (0680)](https://stacks.math.columbia.edu/tag/0680)
* [The Stacks Project, Lemma 37.60.7 (0684)](https://stacks.math.columbia.edu/tag/0684)
* [The Stacks Project, Definition 37.59.2 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.Cohomology.PseudoCoherence.FlatDescent
  (flat_of_mem_fppfPrecoverage isPseudoCoherentFrom_iff_forall_fppf)

namespace AlgebraicGeometry

universe v u

attribute [local instance 10000] HasDerivedCategory.standard

/-- The base change of an fppf covering of `S` along `f : X ⟶ S` is an fppf covering of `X`. -/
public theorem ofArrows_pullback_fst_mem_fppfPrecoverage {X S : Scheme.{u}} (f : X ⟶ S)
    {ι : Type v} (Y : ι → Scheme.{u}) (g : ∀ i, Y i ⟶ S)
    (hg : Presieve.ofArrows Y g ∈ Scheme.fppfPrecoverage S) :
    Presieve.ofArrows (fun i => pullback f (g i)) (fun i => pullback.fst f (g i)) ∈
      Scheme.fppfPrecoverage X :=
  Precoverage.mem_coverings_of_isPullback g hg f _ (fun i => pullback.snd f (g i))
    fun i => IsPullback.of_hasPullback f (g i)

/-- **Stacks 0CSQ for a pseudo-coherent `f`.** Let `f : X ⟶ S` be a pseudo-coherent morphism of
schemes, let `{g i : S i ⟶ S}` be an fppf covering, let `E` be an object of `D(𝒪_X)` and let `m`
be an integer. Then `E` is `m`-pseudo-coherent relative to `S` if and only if the derived pullback
of `E` to `X ×_S S i` is `m`-pseudo-coherent relative to `S i` for every `i`. -/
@[stacks 0CSQ "both directions, for a pseudo-coherent f -- by Stacks 0684 this is every f \
locally of finite type over a locally Noetherian base; no hypothesis on the cohomology \
sheaves of E is used"]
public theorem Scheme.Hom.isPseudoCoherentFrom_iff_forall_pullback_snd_of_pseudoCoherent
    {X S : Scheme.{u}} (f : X ⟶ S) [PseudoCoherent f] {ι : Type v} (Y : ι → Scheme.{u})
    (g : ∀ i, Y i ⟶ S) (hg : Presieve.ofArrows Y g ∈ Scheme.fppfPrecoverage S)
    (E : DerivedCategory X.Modules) (m : ℤ) :
    f.IsPseudoCoherentFrom E m ↔
      ∀ i, (pullback.snd f (g i)).IsPseudoCoherentFrom
        ((derivedPullback (pullback.fst f (g i)).toLRSHom.toShHom).obj E) m := by
  refine (Scheme.Hom.isPseudoCoherentFrom_iff_of_pseudoCoherent f E m).trans
    ((isPseudoCoherentFrom_iff_forall_fppf _ _
      (ofArrows_pullback_fst_mem_fppfPrecoverage f Y g hg) E m).trans
      (forall_congr' fun i => ?_))
  have : Flat (g i) := flat_of_mem_fppfPrecoverage Y g hg i
  have : PseudoCoherent (pullback.snd f (g i)) := pseudoCoherent_pullback_snd f (g i)
  exact (Scheme.Hom.isPseudoCoherentFrom_iff_of_pseudoCoherent (pullback.snd f (g i)) _ m).symm

/-- **Stacks 0CSQ over a locally Noetherian base.** Let `f : X ⟶ S` be locally of finite type with
`S` locally Noetherian, let `{g i : S i ⟶ S}` be an fppf covering, let `E` be an object of
`D(𝒪_X)` and let `m` be an integer. Then `E` is `m`-pseudo-coherent relative to `S` if and only if
the derived pullback of `E` to `X ×_S S i` is `m`-pseudo-coherent relative to `S i` for every
`i`. -/
public theorem Scheme.Hom.isPseudoCoherentFrom_iff_forall_pullback_snd_of_isLocallyNoetherian
    {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f]
    {ι : Type v} (Y : ι → Scheme.{u}) (g : ∀ i, Y i ⟶ S)
    (hg : Presieve.ofArrows Y g ∈ Scheme.fppfPrecoverage S)
    (E : DerivedCategory X.Modules) (m : ℤ) :
    f.IsPseudoCoherentFrom E m ↔
      ∀ i, (pullback.snd f (g i)).IsPseudoCoherentFrom
        ((derivedPullback (pullback.fst f (g i)).toLRSHom.toShHom).obj E) m :=
  have : PseudoCoherent f := (pseudoCoherent_iff_locallyOfFiniteType f).mpr ‹_›
  Scheme.Hom.isPseudoCoherentFrom_iff_forall_pullback_snd_of_pseudoCoherent f Y g hg E m

end AlgebraicGeometry

end
