module

public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.AffineMorphism
public import StacksFrontier.AlgebraicGeometry.ProjectivityLabelChoice.Basic

/-!
# Stacks Tag 087S part (2) at the tag's own hypotheses, and a circular reduction

Part (2) of Stacks Tag 087S says that over a base `S` carrying an ample invertible sheaf every
quasi-projective `f : X ⟶ S` is H-quasi-projective. This file does two things.

## 1. The reduction in `Stacks.Tag087SBundle` is circular, and by how much

`Stacks.Tag087SBundle.isHQuasiProjective_of_isQuasiProjective_of_isAmple`
proves part (2) from
`Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective`
`@Stacks.HProjective.IsHProjective`, replacing the hypothesis
`Stacks.HProjective.ProjectiveCompactification` that
`Stacks.QuasiProjectiveCompactification.projectiveCompactification_iff`
shows **equivalent to part (2) in full**. Its docstring records the new hypothesis as
"strictly weaker than the conclusion", on the ground that it quantifies only over quasi-compact
quasi-separated bases while part (2) in full quantifies over all of them.

That is true and it is not the relevant comparison. `Stacks.Tag087SAmpleRoute.`
`immersionIntoProjective_iff` below proves

> `Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective`
> `@Stacks.HProjective.IsHProjective` **is equivalent to part
> (2) of Stacks Tag 087S with the base hypothesis weakened from "carries an ample invertible
> module" to "quasi-compact and quasi-separated"**,

so the hypothesis is not upstream of part (2) at all: it is part (2) again, over a slightly
larger class of bases. Since a base carrying an ample invertible module *is* quasi-compact and
quasi-separated — `Stacks.Ample.IsAmple.compactSpace` and
`Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple`, recorded here as
`Stacks.Tag087SAmpleRoute.isHQuasiProjective_of_isQuasiProjective_of_isAmple_of_qcqs` — the
implication chain is

    part (2) at every base  ⟹  ImmersionIntoProjective  ⟺  part (2) at qcqs bases
                                                        ⟹  part (2) of the tag,

with the first two arrows already proved as
`Stacks.QuasiProjectiveCompactification.projectiveCompactification_iff`. So the move from
`ProjectiveCompactification` to `ImmersionIntoProjective` traded an exact circularity for a
circularity modulo one weakening of the base hypothesis, and part (2) was still being assumed in
order to be proved. This is the same defect the sibling file diagnosed, one notch milder.

## 2. A reduction that is not circular, at the tag's own hypotheses

The two existing non-circular statements of part (2) each restrict a corner:
`Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffine`
assumes the **base** affine, where the tag's ample sheaf carries no information, and
`Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffineHom`
assumes the **morphism** affine, where the tag's relatively
ample module is never used. The latter's file names the one statement
separating its corner from part (2) in full: **Stacks Tag 0892 part (1)**, that `L ⊗ f^* M ^⊗ a`
is ample for `a` large when `L` is relatively ample and `M` is ample on `S`.

That statement is already reduced, in this tree, to a hypothesis about sections and nothing else.
`Stacks.AmplePullbackPart1.exists_threshold_isAmple` proves Tag 0892 part (1) from
`Stacks.AmplePullbackPart1.EventualAffineDatum` — the module-valued form of [Stacks, Tag 01PW] in
pointwise shape — together with quasi-compactness of `X`, and that quasi-compactness is supplied
from the tag's own hypotheses by `Stacks.AmplePullbackPart1.compactSpace_of_isAmple`.

Composing them is all of `Stacks.Tag087SAmpleRoute.`
`isHQuasiProjective_of_isQuasiProjective_of_isAmple`: part (2) of Stacks Tag 087S for an
**arbitrary** base carrying an ample invertible module and an **arbitrary** quasi-projective
morphism, from two hypotheses, each of which is a named Stacks tag already available in the
library:

* `Stacks.Tag087SAmpleRoute.EventualAffineDatumUniform` — [Stacks, Tag 0892] part (1)'s pointwise
  input, i.e. [Stacks, Tag 01PW] for an invertible coefficient module;
* `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` — [Stacks, Tag 01VS], the
  hypothesis both corner results above already assume.

Neither is implied by part (2). `EventualAffineDatumUniform` mentions no projective space and no
immersion; it asks only for global sections of `L ^⊗ k ⊗ (f^* M) ^⊗ (ak)` with a prescribed affine
nonvanishing open. `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` does mention
`ℙⁿ`, but it asks for an immersion whose pullback of `𝒪(1)` **is** the given tensor power of an
absolutely ample module, which is strictly more than H-quasi-projectivity asserts and is asked of
bases with no hypothesis whatever. So this reduction is upstream of its conclusion in the way the
two previous ones were not, and it reaches the tag's hypotheses rather than a corner of them.

## Main definitions

* `Stacks.ProjectivityLabelChoice.HQuasiProjectiveOfQuasiProjectiveQcqs`: part (2) of Stacks
  Tag 087S with the base assumed only quasi-compact and quasi-separated.
* `Stacks.Tag087SAmpleRoute.EventualAffineDatumUniform`: `Stacks.AmplePullbackPart1.`
  `EventualAffineDatum` at every situation Stacks Tag 0892 part (1) speaks about.

## Main results

* `Stacks.Tag087SAmpleRoute.immersionIntoProjective_iff`:
  **`Stacks.QuasiProjectiveCompactification.`**
  **`ImmersionIntoProjective` at the axiom-clean projectivity predicate is equivalent to part (2)
  of Stacks Tag 087S over quasi-compact quasi-separated bases.**
* `Stacks.Tag087SAmpleRoute.isHQuasiProjective_of_isQuasiProjective_of_isAmple_of_qcqs`: that
  condition implies part (2) of the tag, because an ample invertible module makes its base
  quasi-compact and quasi-separated.
* `Stacks.Tag087SAmpleRoute.exists_isAmple_tensorPullbackPowModule`: **Stacks Tag 0892 part (1)**
  from `Stacks.Tag087SAmpleRoute.EventualAffineDatumUniform`, with the quasi-compactness of `X`
  that it needs derived from the hypotheses of Tag 087S.
* `Stacks.Tag087SAmpleRoute.isHQuasiProjective_of_isQuasiProjective_of_isAmple`: **part (2) of
  Stacks Tag 087S, for an arbitrary base with an ample invertible module and an arbitrary
  quasi-projective morphism**, from Stacks Tag 0892 part (1)'s input and Stacks Tag 01VS.

## Implementation notes

**The ample module produced on `X` is left to be inferred.** Tag 0892 part (1) concludes ampleness
of `Stacks.AmplePullbackPart1.tensorPullbackPowModule f L M a`, whose invertibility instance is
assembled from `Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules`; writing the module as
`_` in the application of
`Stacks.QuasiProjectiveCompactification.isHQuasiProjective_of_isAmple` and letting unification
take it from the ampleness term avoids restating that instance, exactly as
`Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffineHom` does for the pullback
module.

**`Stacks.Tag087SAmpleRoute.EventualAffineDatumUniform` carries Tag 0892 part (1)'s two ampleness
hypotheses.** Quantifying `Stacks.AmplePullbackPart1.EventualAffineDatum` over every `(f, L, M)`
unconditionally would be a false hypothesis — the datum asserts the existence of sections, and a
module with no relative ampleness has no reason to have any — and an implication from a false
hypothesis records nothing. The relative ampleness of `L` and the ampleness of `M` are therefore
part of the definition, which is also what makes it line up with the source's statement.

## What is not done, and no tag is attached

**Neither label of Stacks Tag 087S is closed and no 087S attribute is attached anywhere in this
file.** Stacks Tag 087S has two labels with one assertion each, and `Stacks.Tag087SAmpleRoute.isHQuasiProjective_of_isQuasiProjective_of_isAmple` carries
two hypotheses the tag lacks — `Stacks.Tag087SAmpleRoute.EventualAffineDatumUniform` and
`Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` — so it does not
establish part (2). Nothing
here touches part (1), whose residue remains
`Stacks.Tag087SBundle.BundlesAreHProjective`, shown *equivalent* to part (1) by
`Stacks.Tag087SBundle.isHProjective_of_isProjective_iff`.

**The two hypotheses are not reduced further here.** For
`Stacks.Tag087SAmpleRoute.EventualAffineDatumUniform` the missing input is the one
`Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffineHom` names: no statement
in the repository extends a section of an
invertible `F` over `X_σ` to a global section of `F ⊗ N ^⊗ e`, which is [Stacks, Tag 01PW] with a
module-valued coefficient; `Stacks.SectionExtension.IsSectionRatio` is its structure-sheaf case.
For `Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform` the missing input is
[Stacks, Tag 01NE], recorded in the file that declares it.

## References

* [Stacks Project, Tag 087S](https://stacks.math.columbia.edu/tag/087S)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.QuasiProjectiveCompactification
  (exists_isOpenImmersion_isHProjective isHQuasiProjective_of_exists_isOpenImmersion_isHProjective)

universe u

namespace Stacks.Tag087SAmpleRoute

/-! ### What `Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` is -/

/-- **`Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` at the axiom-clean
projectivity predicate is
equivalent to part (2) of Stacks Tag 087S over quasi-compact quasi-separated bases.**

Forward is Tag 07RM at that predicate
(`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isHProjective`)
followed by half 2 of its own proof
(`Stacks.QuasiProjectiveCompactification.`
`isHQuasiProjective_of_exists_isOpenImmersion_isHProjective`). Backward is free:
H-quasi-projectivity already supplies an immersion over the base into `ℙⁿ_S`, whose structure
morphism is H-projective by `Stacks.HProjective.isHProjective_over`.

So the hypothesis of `Stacks.Tag087SBundle.isHQuasiProjective_of_isQuasiProjective_of_isAmple`
is not upstream of part (2): it is part (2) over a slightly larger class of bases. See the module
documentation. -/
theorem immersionIntoProjective_iff :
    Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective
        @Stacks.HProjective.IsHProjective.{u} ↔
      Stacks.ProjectivityLabelChoice.HQuasiProjectiveOfQuasiProjectiveQcqs.{u} := by
  constructor
  · intro h X S f _ _ hf
    exact isHQuasiProjective_of_exists_isOpenImmersion_isHProjective hf.quasiCompact
      (exists_isOpenImmersion_isHProjective h f hf)
  · intro h X S f hqc hqs hf
    obtain ⟨n, i, hi, -, hif⟩ := h X S f hqc hqs hf
    exact ⟨projectiveSpaceOver n S, i, _, hi, Stacks.HProjective.isHProjective_over n S, hif⟩

/-- **Part (2) over quasi-compact quasi-separated bases implies part (2) of the tag**, because a
scheme carrying an ample invertible module is quasi-compact (clause (1) of [Stacks, Tag 01PS])
and quasi-separated (`Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple`, the first
paragraph of the proof of [Stacks, Tag 01PY]).

Recorded so that the last arrow of the chain in the module documentation is a statement: together
with `Stacks.Tag087SAmpleRoute.immersionIntoProjective_iff` it shows that assuming
`Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` in order to prove part (2) is
assuming part (2). -/
theorem isHQuasiProjective_of_isQuasiProjective_of_isAmple_of_qcqs
    (h : Stacks.ProjectivityLabelChoice.HQuasiProjectiveOfQuasiProjectiveQcqs.{u})
    {X S : Scheme.{u}} (f : X ⟶ S)
    (M : S.Modules) [Stacks.Ample.IsInvertibleModule S M] (hM : Stacks.Ample.IsAmple S M)
    (hf : Stacks.HProjective.IsQuasiProjective f) : Stacks.HProjective.IsHQuasiProjective f :=
  h X S f (Stacks.Ample.IsAmple.compactSpace S M hM)
    (Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple M hM) hf

/-! ### Stacks Tag 0892 part (1), from its pointwise input -/

/-- **`Stacks.AmplePullbackPart1.EventualAffineDatum` at every situation [Stacks, Tag 0892]
part (1) speaks about**: for `L` relatively ample over `f` and `M` ample on the base, every point
of `X` has an affine open `V` around it, and a threshold, beyond which every exponent `a` admits a
global section of `L ^⊗ k ⊗ (f^* M) ^⊗ (ak)` with nonvanishing open exactly `V`.

This is the pointwise form of [Stacks, Tag 01PW] with an invertible coefficient module, which is
the single input `Stacks.AmplePullbackPart1.exists_threshold_isAmple` still needs. The two
ampleness hypotheses are part of the definition; see the implementation notes. -/
def EventualAffineDatumUniform : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S) (L : X.Modules) (M : S.Modules)
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule S M],
    Stacks.RelativeAmple.IsRelativelyAmple f L → Stacks.Ample.IsAmple S M →
      Stacks.AmplePullbackPart1.EventualAffineDatum f L M

/-- **Stacks Tag 0892 part (1)**: for `L` relatively ample over `f` and `M` ample on `S`, the
module `L ⊗ f^* M ^⊗ a` is ample on `X` for every sufficiently large `a`.

This is `Stacks.AmplePullbackPart1.exists_threshold_isAmple` with both of its inputs discharged:
the pointwise datum by `Stacks.Tag087SAmpleRoute.EventualAffineDatumUniform`, and
quasi-compactness of `X` by `Stacks.AmplePullbackPart1.compactSpace_of_isAmple`, which needs
nothing beyond the two ampleness hypotheses already present. Neither of those two declarations
had a consumer anywhere in either tree before this one. -/
theorem exists_isAmple_tensorPullbackPowModule (hdatum : EventualAffineDatumUniform.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) (M : S.Modules)
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule S M]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L) (hM : Stacks.Ample.IsAmple S M) :
    ∃ n : ℕ, ∀ a : ℕ, n ≤ a →
      Stacks.Ample.IsAmple X (Stacks.AmplePullbackPart1.tensorPullbackPowModule f L M a) :=
  Stacks.AmplePullbackPart1.exists_threshold_isAmple f L M
    (Stacks.AmplePullbackPart1.compactSpace_of_isAmple f L M hL hM) (hdatum X S f L M hL hM)

/-! ### Part (2) of Stacks Tag 087S at the tag's hypotheses -/

/-- **Part (2) of Stacks Tag 087S, for an arbitrary base carrying an ample invertible module and
an arbitrary quasi-projective morphism**: `f` is H-quasi-projective.

The ample module `M` on `S` and the relatively ample module `L` of quasi-projectivity are
combined by Stacks Tag 0892 part (1) into an **absolutely** ample invertible module on `X`, and
`Stacks.QuasiProjectiveCompactification.isHQuasiProjective_of_isAmple` turns absolute ampleness
on the source into an
immersion into `ℙⁿ_S` over `S`, `Stacks.PowerFamilyBridge.immersionTwistGap_iff` moving [Stacks,
Tag 01VS] between the two tensor-power families. Both halves of quasi-projectivity are consumed:
the relatively ample module by Tag 0892 part (1), and the finite-type conjunct by Tag 01VS.

This is part (2) of the tag with exactly two hypotheses added and nothing removed, and it carries
no tag for that reason. It strictly generalises both of the library's other non-circular statements
of part (2) — `Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffine`, which
assumes the base affine, and
`Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffineHom`,
which assumes the morphism affine — at the price of the first hypothesis, which is exactly the
statement `Stacks.HProjective.isHQuasiProjective_of_isQuasiProjective_of_isAffineHom` names as
separating its corner from part (2) in full.
Unlike `Stacks.Tag087SBundle.isHQuasiProjective_of_isQuasiProjective_of_isAmple`, neither
hypothesis is equivalent to the conclusion; see the module documentation. -/
theorem isHQuasiProjective_of_isQuasiProjective_of_isAmple
    (hdatum : EventualAffineDatumUniform.{u})
    (hgap : Stacks.VeryAmplePowersUniformDegree.ImmersionTwistGapUniform.{u})
    {X S : Scheme.{u}} (f : X ⟶ S)
    (M : S.Modules) [Stacks.Ample.IsInvertibleModule S M] (hM : Stacks.Ample.IsAmple S M)
    (hf : Stacks.HProjective.IsQuasiProjective f) : Stacks.HProjective.IsHQuasiProjective f := by
  obtain ⟨⟨hft, hqc⟩, L, hLinv, hLamp⟩ := hf
  have := hLinv
  have := hft
  obtain ⟨n, hn⟩ := exists_isAmple_tensorPullbackPowModule hdatum f L M hLamp hM
  refine Stacks.QuasiProjectiveCompactification.isHQuasiProjective_of_isAmple f
    (Stacks.AmplePullbackPart1.tensorPullbackPowModule f L M n) (hn n le_rfl) hqc ?_
  exact (Stacks.PowerFamilyBridge.immersionTwistGap_iff f _).mpr (hgap X S f _)

end Stacks.Tag087SAmpleRoute

end
