module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHom
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointPredicateSupplement
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionRightAdjointSheafHomSupplement

/-!
# Tag 0A9X with its right adjoint produced rather than assumed

[Stacks, Tag 0A9X] says that a right adjoint `a` of `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)` along a
pseudo-coherent closed immersion agrees, on bounded-below complexes, with derived sheaf Hom out
of `𝒪_Z`. `Stacks.Duality.isDerivedSheafHomRightAdjointAtModel_of_pseudoCoherent` proves this
with `a` and its adjunction as parameters, which is how the source states it too: the
quasi-compactness and quasi-separatedness it asks of `W` are used there only to produce `a`.

This file supplies them. The right adjoint of [Stacks, Tag 0A9E] exists at the *locally small*
derived category of [Stacks, Tag 079Q] — `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`,
a global instance — and nowhere else, Brown representability needing the direct sums indexed by
the morphism universe which `CategoryTheory.HasDerivedCategory.standard` does not have. So the
statement below is at that model, and the twisted inverse image `i^×` of
`Stacks.Duality.twistedInverseImage` takes the place of the parameter.

## Main results

* `Stacks.Duality.isDerivedSheafHomRightAdjoint_twistedInverseImage` — **[Stacks, Tag 0A9X] for
  the twisted inverse image of [Stacks, Tag 0A9E]**, with nothing assumed about a right adjoint:
  for a closed immersion into a quasi-compact locally Noetherian scheme, `i^×` agrees with
  `R𝓗om_{𝒪_W}(𝒪_Z, -)` on `D⁺_QCoh(𝒪_W)`.
* `Stacks.Duality.isDerivedSheafHomRightAdjoint_twistedInverseImage_of_noetherian` — the
  parenthetical case of the tag, where pseudo-coherence of `i` is automatic.

## Implementation notes

**No model is pinned here and none may be.** The file installs no
`attribute [local instance] HasDerivedCategory.standard`: the locally small instances of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` are global and are the ones the
statements need, `Stacks.Duality.twistedInverseImage` being available only where the
[Stacks, Tag 0A9E] adjunction is.

**What makes this possible.** `isDerivedSheafHomRightAdjointAtModel_of_pseudoCoherent` used to be
stated at `HasDerivedCategory.standard`, by a file-level local instance, and so could never be
instantiated here; the model of both its derived categories is now a binder. Its one
model-specific input, part (1) of [Stacks, Tag 0A78], is still proved at the standard model —
part (1) of [Stacks, Tag 0A6H] underneath it is — and reaches an arbitrary model through
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`
`.derivedCategoryBPlus_derivedSheafHom_modelEquiv_iff` of
`…/Duality/RightAdjointLemmas/ExactSupportModelComparison.lean`.

**The hypotheses are the tag's own.** [Stacks, Tag 0A9E] asks quasi-compactness and
quasi-separatedness of the *morphism*, which a closed immersion has for free, and
quasi-compactness of the target, which is the tag's own hypothesis on `W`. So the only thing
left to assume is the pseudo-coherence of `i` that [Stacks, Tag 0A9X] asks for; the
quasi-separatedness of `W` that the source also asks is not needed. The Noetherian variant is
the tag's parenthetical case, [Stacks, Tag 0684].

## References

* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 0684](https://stacks.math.columbia.edu/tag/0684)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

variable {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i] [CompactSpace W]

/-- **Stacks Project, Tag 0A9X (Lemma 48.9.7), with the right adjoint produced.** Let
`i : Z ⟶ W` be a closed immersion into a quasi-compact locally Noetherian scheme. Then the
twisted inverse image `i^×` of [Stacks, Tag 0A9E] — the right adjoint of
`Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)` that Brown representability produces — agrees on
bounded-below complexes with derived sheaf Hom out of the structure sheaf of the closed
subscheme: `i^×(K) = R𝓗om_{𝒪_W}(𝒪_Z, K)` for `K` in `D⁺_QCoh(𝒪_W)`.

This is `Stacks.Duality.isDerivedSheafHomRightAdjointAtModel_of_pseudoCoherent` fed with the
[Stacks, Tag 0A9E] adjunction
`AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward`, which is available only
at the locally small derived category of [Stacks, Tag 079Q] — the model in force here. The
hypotheses are the tag's own: quasi-compactness of `W` and pseudo-coherence of `i`. The
quasi-separatedness the source also asks of `W` is not needed, the morphism `i` being
quasi-compact and quasi-separated for free. -/
@[stacks 0A9X "with the right adjoint a produced rather than assumed: a is the twisted inverse \
image of Tag 0A9E, which exists at the locally small derived category of Tag 079Q and at no \
other model, Brown representability needing the direct sums indexed by the morphism universe. \
The hypotheses are the tag's own, quasi-compactness of the target and pseudo-coherence of the \
immersion; the quasi-separatedness the source also asks of the target is not needed, being \
automatic for the closed immersion itself, which is what Tag 0A9E consumes. Nothing is carried"]
theorem isDerivedSheafHomRightAdjoint_twistedInverseImage (hpc : PseudoCoherent i) :
    letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward i
    IsDerivedSheafHomRightAdjointAtModel i
      (twistedInverseImage i (isQuasicoherent_homology_derivedPushforward_of_qcqs i)) := by
  let := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward i
  exact isDerivedSheafHomRightAdjointAtModel_of_pseudoCoherent i hpc
    (isQuasicoherent_homology_derivedPushforward_of_qcqs i) _
    (twistedInverseImageAdjunction i (isQuasicoherent_homology_derivedPushforward_of_qcqs i))

/-- **[Stacks, Tag 0A9X] for a closed immersion into a quasi-compact locally Noetherian
scheme**, the parenthetical case of the tag: pseudo-coherence is then automatic by
[Stacks, Tag 0684], so the hypothesis is the Noetherian one and nothing about the immersion. -/
@[stacks 0A9X "with the right adjoint a produced rather than assumed, for a closed immersion \
into a quasi-compact locally Noetherian scheme: pseudo-coherence of i is then automatic by \
Tag 0684, which is the parenthetical case of the tag. Nothing is carried"]
theorem isDerivedSheafHomRightAdjoint_twistedInverseImage_of_noetherian
    [IsLocallyNoetherian W] :
    letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward i
    IsDerivedSheafHomRightAdjointAtModel i
      (twistedInverseImage i (isQuasicoherent_homology_derivedPushforward_of_qcqs i)) :=
  isDerivedSheafHomRightAdjoint_twistedInverseImage i
    ((pseudoCoherent_iff_locallyOfFiniteType i).2 inferInstance)

end Stacks.Duality

end
