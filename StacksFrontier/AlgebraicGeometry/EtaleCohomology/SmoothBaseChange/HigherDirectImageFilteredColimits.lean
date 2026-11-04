module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.FilteredColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.FilteredColimitsOnALocallySmallSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsAtQcqsObjects

/-!
# Higher direct images along a quasi-compact quasi-separated morphism commute with filtered
colimits

For a quasi-compact and quasi-separated morphism of schemes `h : Y ⟶ X`, every higher direct
image `R^q h_*` of abelian sheaves on the small étale sites commutes with filtered colimits. The
higher direct image is the sheafification of the presheaf `V ↦ H^q(V ×_X Y, -)`, and it commutes
with a colimit as soon as the cohomology over the base changes of a covering family of every
object does (Stacks 0H7B). Every object of `X_étale` is covered by affine ones, whose base
changes `V ×_X Y` are quasi-compact and quasi-separated, and there étale cohomology commutes with
filtered colimits (Stacks 03Q5).

The smooth base change theorem (Stacks, Theorem 0EYU) uses this to pass from sheaves annihilated
by an integer to torsion sheaves.

## Main results

* `Stacks.EtaleCohomology.SmoothBaseChange.preservesColimit_rightDerived_smallEtalePushforwardAb`

## References

* [Stacks Project, Tag 0H7B](https://stacks.math.columbia.edu/tag/0H7B)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
* [Stacks Project, Tag 0EYU](https://stacks.math.columbia.edu/tag/0EYU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.SmoothBaseChange

/-- **Higher direct images along a quasi-compact and quasi-separated morphism commute with
filtered colimits** (Stacks 0H7B with Stacks 03Q5). -/
theorem preservesColimit_rightDerived_smallEtalePushforwardAb {X Y : Scheme.{u}} (h : Y ⟶ X)
    [QuasiCompact h] [QuasiSeparated h] (q : ℕ) {I : Type (u + 1)} [SmallCategory I]
    [IsFiltered I] (D : I ⥤ Sheaf Y.smallEtaleTopology Ab.{u + 1}) :
    PreservesColimit D ((smallEtalePushforwardAb h).rightDerived q) := by
  open Stacks.Cohomology.HigherDirectImage in
  refine preservesColimit_rightDerived_sheafPushforwardContinuous_of_hasEnoughObjects
    Ab.{u + 1} (smallEtaleBaseChange h) q D fun V => ?_
  let 𝒰 := V.left.affineCover
  let Ui : 𝒰.I₀ → X.Etale := fun i => smallEtaleObj (𝒰.f i ≫ V.hom)
  let fi : ∀ i, Ui i ⟶ V := fun i => MorphismProperty.Over.homMk (𝒰.f i) rfl
  refine ⟨𝒰.I₀, Ui, fi, (ofArrows_mem_smallEtaleTopology_iff fi).2
    (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨𝒰.idx x, 𝒰.covers x⟩), fun i => ?_⟩
  let W := (smallEtaleBaseChange h).obj (Ui i)
  have : CompactSpace W.left :=
    compactSpace_smallEtaleBaseChange_obj h (Ui i)
      (inferInstanceAs (CompactSpace (Spec _)))
  have : QuasiSeparatedSpace W.left :=
    quasiSeparatedSpace_smallEtaleBaseChange_obj h (Ui i)
      (inferInstanceAs (QuasiSeparatedSpace (Spec _)))
  have := isIso_colimit_post_rightDerived_sheafSections_of_qcqs.{0, u} q W
    ⟨inferInstance, inferInstance⟩ D
  exact preservesColimit_of_isIso_post _ _

end Stacks.EtaleCohomology.SmoothBaseChange

end
