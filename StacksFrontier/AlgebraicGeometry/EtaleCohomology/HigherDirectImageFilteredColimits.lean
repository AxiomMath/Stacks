module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageDirectSums
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.FilteredColimitsOnALocallySmallSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images along a quasi-compact quasi-separated morphism and filtered colimits

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes. For every `p ≥ 0` the
higher direct image `R^p f_*` of abelian sheaves on the small étale sites commutes with filtered
colimits:

> `R^p f_* (colim_i 𝓕_i) = colim_i R^p f_* 𝓕_i`.

This is the case of a constant system of [Stacks, Tag 09Z1].

## Main results

* `Stacks.EtaleCohomology.preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage_of_qcqs`
  — `R^p f_*` on abelian sheaves preserves filtered colimits.

## Implementation notes

Coefficients are `AddCommGrpCat.{max (u + 1) v}` and the index categories are small categories
in `Type (max (u + 1) v)`, the sizes at which Stacks 0739 is available on this site.

## References

* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
* [Stacks Project, Tag 0H7B](https://stacks.math.columbia.edu/tag/0H7B)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

/-- Every object of the small étale site of a scheme has a covering by objects with affine
underlying scheme: the members of an affine open cover of its underlying scheme. -/
theorem smallEtaleTopology_hasEnoughObjects_isAffine (Y : Scheme.{u}) :
    Y.smallEtaleTopology.HasEnoughObjects (fun V : Y.Etale => IsAffine V.left) := by
  intro V
  let C := V.left.affineCover
  let W (k : C.I₀) : Y.Etale := Scheme.Etale.mk (C.f k ≫ V.hom)
  let a (k : C.I₀) : W k ⟶ V := MorphismProperty.Over.homMk (C.f k)
  refine ⟨C.I₀, W, a, ?_, fun k => inferInstanceAs (IsAffine (C.X k))⟩
  exact (Scheme.ofArrows_mem_smallEtaleTopology_iff a).mpr
    (Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr (C.exists_eq x))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Higher direct images along a quasi-compact quasi-separated morphism commute with filtered
colimits** ([Stacks, Tag 09Z1] for a constant system). Let `f : X ⟶ Y` be quasi-compact and
quasi-separated. For every `p` the higher direct image `R^p f_*` of abelian sheaves on the small
étale sites preserves filtered colimits: `R^p f_* (colim_i 𝓕_i) = colim_i R^p f_* 𝓕_i`. -/
@[sga "4 VI 5.1" "special case"]
theorem preservesColimitsOfShape_rightDerived_etaleAbelianDirectImage_of_qcqs
    [QuasiCompact f] [QuasiSeparated f] (p : ℕ)
    (I : Type (max (u + 1) v)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I
      (((smallEtaleBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        Y.smallEtaleTopology X.smallEtaleTopology).rightDerived p) := by
  refine ⟨fun {F} => ?_⟩
  open Stacks.Cohomology.HigherDirectImage in
  refine preservesColimit_rightDerived_sheafPushforwardContinuous_of_hasEnoughObjects
    (J := Y.smallEtaleTopology) (K := X.smallEtaleTopology) AddCommGrpCat.{max (u + 1) v}
    (smallEtaleBaseChange f) p F ?_
  intro V
  obtain ⟨L, W, a, ha, hW⟩ := smallEtaleTopology_hasEnoughObjects_isAffine Y V
  refine ⟨L, W, a, ha, fun k => ?_⟩
  have : IsAffine (W k).left := hW k
  have hq : (smallEtaleBaseChange f).obj (W k) ∈ qcqsEtaleObjects X := by
    have hfst : QuasiSeparated (Limits.pullback.fst (W k).hom f) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated)
        (IsPullback.of_hasPullback (W k).hom f).flip ‹QuasiSeparated f›
    have : CompactSpace ((𝟭 Scheme.{u}).obj (W k).left) := inferInstanceAs (CompactSpace (W k).left)
    have : QuasiSeparatedSpace ((𝟭 Scheme.{u}).obj (W k).left) :=
      inferInstanceAs (QuasiSeparatedSpace (W k).left)
    refine ⟨?_, ?_⟩
    · change CompactSpace (Limits.pullback (W k).hom f : Scheme.{u})
      exact QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst (W k).hom f)
    · change QuasiSeparatedSpace (Limits.pullback (W k).hom f : Scheme.{u})
      exact quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.fst (W k).hom f)
  have := isIso_colimit_post_rightDerived_sheafSections_of_qcqs.{v} p
    ((smallEtaleBaseChange f).obj (W k)) hq F
  exact preservesColimit_of_isIso_post _ _

end Stacks.EtaleCohomology
