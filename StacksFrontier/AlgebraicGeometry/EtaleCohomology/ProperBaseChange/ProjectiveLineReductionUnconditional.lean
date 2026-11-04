module

public import StacksFrontier.AlgebraicGeometry.ChowQcqs.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SurjectiveCohomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCover.Tower

/-!
# Reducing proper base change to the projective line

[Stacks, Tag 0A4F](https://stacks.math.columbia.edu/tag/0A4F): to prove that cohomology commutes
with base change for every proper morphism of schemes it suffices to prove it for the morphisms
`ℙ¹_S ⟶ S`.

The assembly `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_projectiveLine` reduces
this to six inputs, each of which is now available unconditionally:

* the finite case, [Stacks, Tag 0A4E]
  (`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isFinite`);
* the composition, [Stacks, Tag 0A4D]
  (`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_comp`);
* the descent along a proper surjection, [Stacks, Tag 0A4C]
  (`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_comp_of_surjective`);
* the localization on the base, the use of [Stacks, Tag 03Q8] in the first paragraph of the source
  (`Stacks.EtaleCohomology.baseChangeZariskiLocalOnBase`);
* Chow's lemma, [Stacks, Tag 0202], over an affine base
  (`AlgebraicGeometry.hasChowModification_of_compactSpace_quasiSeparatedSpace`);
* the finite surjective cover of `ℙⁿ_S` by the `n`-fold power of `ℙ¹_S` displayed in the last
  paragraph of the source (`Stacks.ProjectiveLineCover.hasProjectiveLineTowerCover`).

## Main results

* `Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper_of_projectiveLine` —
  **Tag 0A4F**.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- [Stacks, Tag 0A4E] in the form consumed by the reduction. -/
theorem baseChangeForFinite : BaseChangeForFinite.{u, 0} :=
  fun f hf => cohomologyCommutesWithBaseChange_of_isFinite f hf

/-- [Stacks, Tag 0A4D] in the form consumed by the reduction. -/
theorem baseChangeForComp : BaseChangeForComp.{u, 0} := fun f g hf hg hfc hgc => by
  have := hf
  have := hg
  exact cohomologyCommutesWithBaseChange_comp f g hfc hgc

/-- [Stacks, Tag 0A4C] in the form consumed by the reduction. -/
theorem baseChangeDescendsAlongProperSurjective :
    BaseChangeDescendsAlongProperSurjective.{u, 0} := fun f g hf hg hsurj hfc hgfc => by
  have := hf
  have := hg
  have := hsurj
  exact cohomologyCommutesWithBaseChange_of_comp_of_surjective f g hfc hgfc

/-- Chow's lemma, [Stacks, Tag 0202], over an affine base, in the form consumed by the
reduction: a proper morphism is separated, of finite type and quasi-compact, and an affine
scheme is quasi-compact and quasi-separated. -/
theorem chowModificationOverAffine : ChowModificationOverAffine.{u} := fun f hY hf => by
  have := hY
  have := hf
  exact hasChowModification_of_compactSpace_quasiSeparatedSpace f

/-- **[Stacks, Tag 0A4F].** To prove that cohomology commutes with base change for every proper
morphism of schemes it suffices to prove it for the morphism `ℙ¹_S ⟶ S` for every scheme `S`. -/
public theorem cohomologyCommutesWithBaseChange_of_isProper_of_projectiveLine
    (hline : ∀ S : Scheme.{u},
      CohomologyCommutesWithBaseChange.{u, 0} (ProjectiveSpace 1 S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsProper f) :
    CohomologyCommutesWithBaseChange.{u, 0} f :=
  cohomologyCommutesWithBaseChange_of_projectiveLine baseChangeForFinite baseChangeForComp
    baseChangeZariskiLocalOnBase baseChangeDescendsAlongProperSurjective chowModificationOverAffine
    Stacks.ProjectiveLineCover.hasProjectiveLineTowerCover hline f hf

end Stacks.EtaleCohomology

end
