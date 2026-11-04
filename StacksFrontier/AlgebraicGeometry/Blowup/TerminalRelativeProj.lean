module

public import StacksFrontier.AlgebraicGeometry.BlowUpSeparatedInput.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Separatedness of a relative `Proj`, and what remains of the universal property of blowing up

The structure morphism `π : Proj_S(𝒜) ⟶ S` of a relative `Proj` is separated. This is Tag 01O2,
and it is proved here for an arbitrary relative `Proj` gluing datum
`Stacks.RelativeProj.Data`, with no hypothesis at all: the charts of such a datum are honest
`Proj`s of graded rings, Mathlib knows `AlgebraicGeometry.Proj` to be a separated scheme
(Tag 01MC), a morphism out of a separated scheme is separated, and separatedness is local on the
target.

The consequence for Tag 0806 is that three of the five inputs of
`Stacks.Blowup.exists_nonempty_isTerminal` are not inputs at all. That lemma proves the
universal property of blowing up for a morphism `b : S' ⟶ S` given five facts about `b`:
separatedness, membership in the category `C`, being an isomorphism over the complement of the
center, scheme-theoretic density of the complement of an effective Cartier divisor, and the
existence of the classifying morphism. For the blowup morphism of Tag 01OG,
`AlgebraicGeometry.blowUpToBase`:

* separatedness is `Stacks.RelativeProj.Data.isSeparated_toBase` below, because the blowup is a
  relative `Proj` (Tag 01OG);
* membership in `C` is Tag 02OS part (2),
  `Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal`;
* the density statement is Tag 07ZU,
  `Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor`.

So `Stacks.Blowup.exists_nonempty_isTerminal_blowUp` below states Tag 0806 for the blowup of an
arbitrary scheme in an arbitrary quasi-coherent ideal sheaf, with exactly **two** hypotheses
left: Tag 02OS part (1), that the blowup is an isomorphism over the complement of the center,
and the universal property of relative `Proj` (Constructions, Section 01NS), that every object
of `C` admits a morphism to the blowup over the base. Neither is proved anywhere in the
repository, so no `@[stacks 0806]` attribute is attached.

## Main results

* `Stacks.RelativeProj.Data.isSeparated_toBase`: **Tag 01O2.** The structure morphism of a
  relative `Proj` is separated.
  `Stacks.RelativeProj.Situation.isSeparated_relativeProjToBase`, the same statement for the
  relative `Proj` of a quasi-coherent graded algebra on a scheme -- the form Tag 01O2 is stated
  in -- is proved in `StacksFrontier.AlgebraicGeometry.BlowUpSeparatedInput.Basic`, which this
  module imports and which is where the tag is registered for that form.
* `Stacks.Blowup.exists_nonempty_isTerminal_relativeProj`: Tag 0806 for the relative `Proj` of a
  situation, with separatedness and Tag 07ZU discharged.
* `Stacks.Blowup.exists_nonempty_isTerminal_blowUp`: the same for the blowup morphism of Tag
  01OG, with Tag 02OS part (2) discharged as well. This is the statement of Tag 0806 for the
  blowup; it is left untagged because two of its inputs are hypotheses rather than theorems.

## Implementation notes

The chart over an affine open `U` of the base is `Proj (𝒜 U)`, and
`Stacks.RelativeProj.Data.toBase_preimage_coe` says that its image is the preimage of `U`. So
`Stacks.RelativeProj.Data.isSeparated_preimage` transports `Scheme.IsSeparated (Proj (𝒜 U))`
along `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` to the open subscheme `π ⁻¹ U`, after
which `AlgebraicGeometry.Scheme.IsSeparated` of the source hands over separatedness of
`π ∣_ U` and `AlgebraicGeometry.IsZariskiLocalAtTarget` assembles the affine opens. This is
exactly the argument of the Stacks proof of Tag 01O2: work locally on the base, use that
`Proj (𝒜 U)` is separated, and use that a morphism from a separated scheme is separated.

The tag is attached to the `Stacks.RelativeProj.Data` form, which generalizes the
`Stacks.RelativeProj.Situation` form and from which the latter follows by applying it to
`Stacks.RelativeProj.Situation.chartData`.

`Stacks.RelativeProj.Situation.relativeProjToBase` is a plain `def`, so it is not reducibly
defeq to the `Stacks.RelativeProj.Data` structure projection that defines it, and instance
search for `IsSeparated` of it fails even though `isSeparated_toBase` applies: the class's
implicit target is assigned from the goal on one side and from the instance head on the other.
Both separatedness statements below therefore spell the class out as `@IsSeparated`, with its
arguments supplied, rather than relying on synthesis.

## References

* [Stacks Project, Tag 01O2](https://stacks.math.columbia.edu/tag/01O2)
* [Stacks Project, Tag 01MC](https://stacks.math.columbia.edu/tag/01MC)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.RelativeProj.Data

variable {S : Scheme.{u}} {A σ : S.affineOpens → Type u} [∀ U, CommRing (A U)]
  [∀ U, SetLike (σ U) (A U)] [∀ U, AddSubgroupClass (σ U) (A U)]
  {𝒜 : ∀ U, ℕ → σ U} [∀ U, GradedRing (𝒜 U)]

/-- The preimage of an affine open `U` of the base in a relative `Proj` is a separated scheme: it
is the chart `Proj (𝒜 U)`, which is separated by **Stacks Project, Tag 01MC**. -/
theorem isSeparated_preimage (d : Data 𝒜) (U : S.affineOpens) :
    Scheme.IsSeparated (d.toBase ⁻¹ᵁ (U : S.Opens)).toScheme := by
  have e : AlgebraicGeometry.Proj (𝒜 U) ≅ (d.toBase ⁻¹ᵁ (U : S.Opens)).toScheme :=
    IsOpenImmersion.isoOfRangeEq (d.chartι U) (d.toBase ⁻¹ᵁ (U : S.Opens)).ι (by
      have h : (d.chartι U).opensRange = (d.toBase ⁻¹ᵁ (U : S.Opens)).ι.opensRange := by
        rw [Scheme.Opens.opensRange_ι, d.toBase_preimage_coe U]
      simpa only [Scheme.Hom.coe_opensRange] using
        congrArg (fun Z : d.relativeProj.Opens => (Z : Set d.relativeProj)) h)
  refine ⟨?_⟩
  have h : terminal.from (d.toBase ⁻¹ᵁ (U : S.Opens)).toScheme
      = e.inv ≫ terminal.from (AlgebraicGeometry.Proj (𝒜 U)) := terminal.hom_ext _ _
  rw [h]
  infer_instance

/-- **Stacks Project, Tag 01O2.** The structure morphism of a relative `Proj` is separated.

Separatedness is local on the target, so it suffices to check it over the affine opens of the
base; over an affine open `U` the preimage is the chart `Proj (𝒜 U)`, a separated scheme, and a
morphism out of a separated scheme is separated. -/
@[stacks 01O2 "the gluing-datum form",
  ega "II 2.4.2",
  ega "II 3.1.3" "separated over Y",
  ega "II 8.14.1" "more general"]
instance isSeparated_toBase (d : Data 𝒜) : IsSeparated d.toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsSeparated)
    (fun U : S.affineOpens => (U : S.Opens)) (iSup_affineOpens_eq_top S)]
  intro U
  have := d.isSeparated_preimage U
  infer_instance

end Stacks.RelativeProj.Data

namespace Stacks.RelativeProj.Situation

end Stacks.RelativeProj.Situation

namespace Stacks.Blowup

open Stacks.RelativeProj

/-- **Stacks Project, Tag 0806** for the relative `Proj` of a quasi-coherent graded algebra, with
separatedness of the structure morphism discharged by
`Stacks.RelativeProj.Data.isSeparated_toBase` and the density statement by Tag 07ZU,
`Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor`.

The remaining hypotheses are two of the five geometric inputs of
`Stacks.Blowup.exists_nonempty_isTerminal`: that the structure morphism is an object of the
category `C` and that it is an isomorphism over the complement of the center (for the blowup,
Tag 02OS parts 2 and 1), together with the universal property of relative `Proj`
(Constructions, Section 01NS). For the blowup the first of those is a theorem; see
`Stacks.Blowup.exists_nonempty_isTerminal_blowUp`. -/
theorem exists_nonempty_isTerminal_relativeProj (s : Situation.{u})
    (I : s.base.IdealSheafData)
    (hb : IsCartierOver I (Over.mk (Situation.relativeProjToBase s)))
    (hiso : IsIso (Situation.relativeProjToBase s ∣_ I.support.compl))
    (hex : ∀ Y : Over s.base, IsCartierOver I Y →
      ∃ g : Y.left ⟶ Situation.relativeProj s,
        g ≫ Situation.relativeProjToBase s = Y.hom) :
    ∃ h : IsCartierOver I (Over.mk (Situation.relativeProjToBase s)),
      Nonempty (IsTerminal
        (⟨Over.mk (Situation.relativeProjToBase s), h⟩ : CartierOver I)) := by
  have : @IsSeparated _ s.base (Situation.relativeProjToBase s) :=
    Situation.isSeparated_relativeProjToBase s
  exact exists_nonempty_isTerminal I _ hb hiso
    (fun _ J hJ =>
      Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor J hJ) hex

/-- **Stacks Project, Tag 0806** for the blowup of a scheme in a quasi-coherent ideal sheaf, i.e.
for the relative `Proj` of the Rees algebra `⨁ₙ Iⁿ` of Tag 01OG, with separatedness of the
blowup morphism, membership of the blowup in the category `C` (Tag 02OS part 2) and the density
statement (Tag 07ZU) all discharged.

This is the fold point for Tag 0806: the tag's own `isTerminal_blowUp` is this statement with
Stacks' names for `AlgebraicGeometry.blowUpToBase` and
`Stacks.Divisors.IsEffectiveCartierDivisor`, so once the two remaining hypotheses are theorems
Tag 0806 is this lemma applied to them. No `@[stacks]` attribute is attached, because they are
hypotheses here:

* `hiso` is **Tag 02OS part (1)**, that the blowup is an isomorphism over the complement of the
  center. The Stacks proof of it reduces to Tag 0805 (blowing up commutes with restriction to an
  open subscheme) and Tag 01MI (the relative `Proj` of a graded algebra concentrated in degree
  zero is the base); neither is formalized.
* `hex` is the mapping-in half of the universal property of relative `Proj` (Constructions,
  Section 01NS). Nothing in the repository classifies a morphism into a relative `Proj` with a
  non-trivial twist; `Stacks.Blowup.toBlowUpSpec` does the case where the graded datum collapses
  to a ring map. -/
theorem exists_nonempty_isTerminal_blowUp {X : Scheme.{u}} (I : X.IdealSheafData)
    (hiso : IsIso (AlgebraicGeometry.blowUpToBase I ∣_ I.support.compl))
    (hex : ∀ Y : Over X, IsCartierOver I Y →
      ∃ g : Y.left ⟶ AlgebraicGeometry.blowUp I,
        g ≫ AlgebraicGeometry.blowUpToBase I = Y.hom) :
    ∃ h : IsCartierOver I (Over.mk (AlgebraicGeometry.blowUpToBase I)),
      Nonempty (IsTerminal
        (⟨Over.mk (AlgebraicGeometry.blowUpToBase I), h⟩ : CartierOver I)) :=
  exists_nonempty_isTerminal_relativeProj (AlgebraicGeometry.reesSituation I) I
    (isEffectiveCartierDivisor_exceptionalIdeal I) hiso hex

end Stacks.Blowup

end
