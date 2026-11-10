module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.BlowUpUniversal.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separatedness of a relative `Proj`, and the input of Tag 0806 that it discharges

The reduction of [Stacks, Tag 0806] in
`StacksFrontier/AlgebraicGeometry/BlowUpUniversal/Basic.lean` takes five results of the Stacks
proof as hypotheses. One of them is [Stacks, Tag 01O2]: the blowup morphism is **separated**.
This file proves it, for an arbitrary relative `Proj` and hence for the blowup, and records the
reduction with that hypothesis gone.

Separatedness of the structure morphism is proved elsewhere in the library only for the
separate notion `Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData`
(`Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase`), which is a different
constant from `Stacks.RelativeProj.Situation.relativeProjToBase`, the one the blowup is built
from; the two are not bridged. The argument here is the same one, run over the situation's own
charts.

## Main results

* `Stacks.AlgebraicGeometry.BlowUpSeparatedInput.isSeparated_projInclusionToOpen`: the structure
  morphism `Proj Γ(U, 𝒜) ⟶ U` of a chart over an affine open of the base is separated.
* `Stacks.RelativeProj.Situation.isSeparated_relativeProjToBase`:
  **[Stacks, Tag 01O2].** The structure morphism of a relative `Proj` is separated. This is the
  one tag attached in this file: Tag 01O2 labels a single assertion, this is it over the
  repository's own 01NN/01NQ names (`Stacks.RelativeProj.Situation` carries `@[stacks 01NN]` at
  `Constructions/RelativeProjSectionRings.lean:78` and
  `Stacks.RelativeProj.Situation.relativeProjToBase` carries `@[stacks 01NQ]` at
  `RelativeProj/Charts/Descent.lean:320`), and it carries no hypothesis the tag lacks.
* `Stacks.AlgebraicGeometry.BlowUpSeparatedInput.isSeparated_blowUpToBase`: the blowup morphism
  is separated.
* `Stacks.AlgebraicGeometry.BlowUpSeparatedInput.nonempty_isTerminal_blowUp_of'`:
  the reduction of [Stacks, Tag 0806] with the separatedness hypothesis discharged — four
  hypotheses instead of five.

## Implementation notes

**The chart is separated because it is a composite of three separated morphisms.**
`Stacks.RelativeProj.Situation.projInclusionToOpen` is by definition
`Proj.toSpecZero ≫ Spec.map (sectionRingZeroMap) ≫ hU.isoSpec.inv`. Mathlib's
`AlgebraicGeometry.Proj.isSeparated` makes the first factor separated, the instance for
`Spec.map` the second, and the third is an isomorphism, hence a monomorphism, hence separated by
`AlgebraicGeometry.isSeparated_of_mono`. No finite-generation hypothesis is involved:
*properness* of `Proj` needs `Algebra.FiniteType`, separatedness does not.

**The descent to the base is locality of separatedness at the target.** `IsSeparated` is
`AlgebraicGeometry.IsZariskiLocalAtTarget`, so it is enough to check it on the restrictions of
`relativeProjToBase` to the affine opens of the base, which cover the base. The restriction and
the chart structure morphism are two pullbacks of the *same* cospan — the first by
`AlgebraicGeometry.isPullback_morphismRestrict`, the second by
`Stacks.RelativeProj.Situation.relativeProjChart_isPullback` — so they are isomorphic as arrows
and `IsSeparated` respects isomorphisms of arrows. No quasi-compactness of the base and no
choice of a finite cover enters.

**Only separatedness is discharged.** The other four hypotheses of the reduction — that the
exceptional divisor is an effective Cartier divisor and that the blowup morphism is an
isomorphism away from the centre (the two assertions of [Stacks, Tag 02OS]), that the complement
of an effective Cartier divisor is scheme-theoretically dense ([Stacks, Tag 07ZU]), and the
existence of one lift ([Stacks, Tag 01NS]) — are untouched, so **no `@[stacks 0806]` attribute is
attached**: the statement below still carries hypotheses that Tag 0806 does not.

## References

* [Stacks Project, Tag 01O2](https://stacks.math.columbia.edu/tag/01O2)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Stacks.AlgebraicGeometry.BlowUpSeparatedInput

universe u

/-- **The structure morphism of a chart of a relative `Proj` is separated.** It is
`Proj.toSpecZero` followed by a morphism of affine schemes and the inverse of an isomorphism, and
each of the three is separated. -/
@[ega "II 8.14.1" "special case"]
public instance isSeparated_projInclusionToOpen (s : Stacks.RelativeProj.Situation.{u})
    (U : s.base.Opens) (hU : IsAffineOpen U) :
    IsSeparated (Stacks.RelativeProj.Situation.projInclusionToOpen s U hU) := by
  rw [Stacks.RelativeProj.Situation.projInclusionToOpen]
  infer_instance

/-- **Stacks Project, Tag 01O2.** The structure morphism of the relative `Proj` of a
quasi-coherent, commutative, nonnegatively graded algebra on a scheme is separated.

Separatedness is local at the target, and over an affine open `W` of the base the restriction of
`relativeProjToBase` is the chart structure morphism `Proj Γ(W, 𝒜) ⟶ W`, because both are
pullbacks of `relativeProjToBase` along `W.ι`. -/
@[stacks 01O2, ega "II 3.1.3" "separated over Y", ega "II 8.14.1"]
public theorem _root_.Stacks.RelativeProj.Situation.isSeparated_relativeProjToBase
    (s : Stacks.RelativeProj.Situation.{u}) :
    IsSeparated (Stacks.RelativeProj.Situation.relativeProjToBase s) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun W : s.base.affineOpens => (W : s.base.Opens)) (iSup_affineOpens_eq_top s.base) fun W => ?_
  have h₁ :=
    (isPullback_morphismRestrict (Stacks.RelativeProj.Situation.relativeProjToBase s)
      (W : s.base.Opens)).flip
  have h₂ := Stacks.RelativeProj.Situation.relativeProjChart_isPullback s W
  refine (MorphismProperty.arrow_mk_iso_iff (P := @IsSeparated)
    (Arrow.isoMk (h₂.isoIsPullback _ _ h₁) (Iso.refl _) ?_)).mp
    (isSeparated_projInclusionToOpen s (W : s.base.Opens) W.2)
  exact h₂.isoIsPullback_hom_snd _ _ h₁

/-- **The blowup morphism is separated.** The blowup of `X` in a quasi-coherent ideal is the
relative `Proj` of the Rees algebra, so this is `isSeparated_relativeProjToBase` at
`AlgebraicGeometry.reesSituation`. -/
public theorem isSeparated_blowUpToBase {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsSeparated (blowUpToBase I) :=
  Stacks.RelativeProj.Situation.isSeparated_relativeProjToBase (reesSituation I)

/-- **The reduction of Stacks Project, Tag 0806, with the separatedness input discharged.** The
blowup of `X` in `I` is a final object of the full subcategory of `Sch/X` whose objects have
effective Cartier inverse image of the centre, given the *four* remaining results the Stacks
proof invokes:

* `hcartier`: the exceptional divisor is an effective Cartier divisor on the blowup —
  [Stacks, Tag 02OS (2)];
* `hiso`: the blowup morphism is an isomorphism over the complement of the centre —
  [Stacks, Tag 02OS (1)];
* `hdense`: the complement of an effective Cartier divisor is scheme-theoretically dense —
  [Stacks, Tag 07ZU];
* `hlift`: every object of the subcategory admits at least one morphism to the blowup over the
  base — the existence half, from [Stacks, Tag 01NS].

Separatedness of the blowup morphism, [Stacks, Tag 01O2], was the fifth and is now supplied by
`isSeparated_blowUpToBase`. [Stacks, Tag 01RH] was never a hypothesis: it is proved in this
repository as `AlgebraicGeometry.eq_of_isSchemeTheoreticallyDense`.

**No `@[stacks 0806]` attribute is attached**, and none may be: four hypotheses that Tag 0806
does not have remain. -/
public theorem nonempty_isTerminal_blowUp_of' {X : Scheme.{u}} (I : X.IdealSheafData)
    (hcartier : BlowUpUniversal.IsCartierOver I (Over.mk (blowUpToBase I)))
    (hiso : IsIso (blowUpToBase I ∣_ BlowUpUniversal.supportCompl I))
    (hdense : ∀ {W : Scheme.{u}} (D : W.IdealSheafData),
      Stacks.Divisors.IsEffectiveCartierDivisor D →
      Scheme.Opens.IsSchemeTheoreticallyDense (BlowUpUniversal.supportCompl D))
    (hlift : ∀ Y : Over X, BlowUpUniversal.IsCartierOver I Y →
      Nonempty (Y ⟶ Over.mk (blowUpToBase I))) :
    ∃ h : BlowUpUniversal.IsCartierOver I (Over.mk (blowUpToBase I)),
      Nonempty (IsTerminal
        (⟨Over.mk (blowUpToBase I), h⟩ : BlowUpUniversal.CartierOver I)) :=
  BlowUpUniversal.nonempty_isTerminal_blowUp_of I hcartier hiso (isSeparated_blowUpToBase I)
    hdense hlift

end Stacks.AlgebraicGeometry.BlowUpSeparatedInput

end
