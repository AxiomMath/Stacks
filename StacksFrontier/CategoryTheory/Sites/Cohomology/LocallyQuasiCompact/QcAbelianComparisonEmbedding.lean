module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcAbelianComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonEmbedding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiPullbackQcSheaf

/-!
# The quasi-compact comparison morphism is an embedding of topoi, on abelian sheaves

Let `X` be an object of the site `LC_α` of Hausdorff, locally quasi-compact spaces and let
`a_X = π_X ∘ ε_X : Sh(LC_qc/X) → Sh(X)` be the comparison morphism of topoi to sheaves on the
underlying space. `QcComparisonEmbedding.lean` proves that `a_X^{-1}` is fully faithful on
sheaves of **sets**, which is the consequence of Stacks 09X3 that Stacks 0DAG quotes in its
opening sentence. This file proves the same for sheaves of **abelian groups**.

The argument is the one of the set-valued file, with each step replaced by its abelian form:

* `ε_{X,*}(a_X^{-1}G) = π_X^{-1}G`, because `π_X^{-1}G` already satisfies the sheaf condition
  for the quasi-compact topology. That is condition (0EZ6) of Situation 0EZ3 for this
  situation, and it is `zariskiPullbackClass_isSheaf_qc`.
  `StacksFrontier/CategoryTheory/Sites/Cohomology/LocallyQuasiCompact/QcAbelianComparison.lean`
  states
  this identification objectwise, as `qcAbelianDirectImageTopologicalInverseImageIso`, with the
  condition carried as a hypothesis `h0EZI`; here the hypothesis is discharged and the
  identification is assembled into a natural isomorphism of functors, which is the form in which
  full faithfulness consumes it.
* `π_X^{-1}` is fully faithful on abelian sheaves, which is the unit clause of Stacks 0DCU,
  `abelianComparisonAdjunction_unit_isIso`.
* `ε_{X,*}` is faithful, being a full subcategory inclusion.

Cancelling `ε_{X,*}` then gives full faithfulness of `a_X^{-1}`.

## Main definitions

In the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`:

* `qcAbelianDirectImageTopologicalInverseImageNatIso`: the identification
  `ε_{X,*} a_X^{-1} = π_X^{-1}` on abelian sheaves, as a natural isomorphism of functors and
  with no hypothesis.

## Main results

In the same namespace:

* `qcTopologicalAbelianInverseImage_fullyFaithful`: `a_X^{-1}` is full and faithful on abelian
  sheaves.

## Implementation notes

The coefficients are `AddCommGrpCat.{max (u + 1) v}`, the universe at which the abelian Zariski
comparison adjunction is available in this development. That is one universe higher than the
set-valued statement, which holds at `Type (max u t)` for every `t` and in particular at
`Type u`: `comparisonInverseImage` needs only `hasSheafify_zariskiTopology_over`, which comes
from `essentiallySmall_over` and so is available at `max u t`, whereas
`abelianComparisonDirectImage_isRightAdjoint` is proved only at `max (u + 1) v`, bounding the
coverings of the slice by `Small.{u + 1}` instead of going through `essentiallySmall_over`.
Whether that bound can be brought down to `max u t`, so that the abelian comparison exists at
the universe of the spaces as the set-valued one does, is not settled here.

## References

* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Tag 0EZI](https://stacks.math.columbia.edu/tag/0EZI)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 0DCY](https://stacks.math.columbia.edu/tag/0DCY)
* [Stacks Project, Tag 0DAG](https://stacks.math.columbia.edu/tag/0DAG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- **The identification `ε_{X,*} a_X^{-1} = π_X^{-1}` on abelian sheaves.** Direct image along
the change-of-topology morphism undoes quasi-compact sheafification on the Zariski comparison
inverse images, because those are already quasi-compact sheaves.

This is `qcAbelianDirectImageTopologicalInverseImageIso` with its hypothesis `h0EZI` discharged
by `zariskiPullbackClass_isSheaf_qc` and with the components assembled into a natural
isomorphism; naturality is naturality of the unit of the change-of-topology adjunction. -/
def qcAbelianDirectImageTopologicalInverseImageNatIso (X : S.category) :
    qcTopologicalAbelianInverseImage.{u, w, v} S X ⋙ qcAbelianDirectImage.{u, w, v} S X ≅
      S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X :=
  (NatIso.ofComponents
    (fun F =>
      have := isIso_qcAbelianComparisonAdjunction_unit_app.{u, w, v} S X _
        (zariskiPullbackClass_isSheaf_qc.{u, w, v} S X _
          (zariskiPullbackClass_abelianComparisonInverseImage.{u, w, v} S X F))
      asIso ((qcAbelianComparisonAdjunction.{u, w, v} S X).unit.app
        ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj F)))
    (fun f => (qcAbelianComparisonAdjunction.{u, w, v} S X).unit.naturality
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).map f))).symm

/-- **The comparison morphism to the underlying space is an embedding of topoi on abelian
sheaves.** The inverse image along `a_X = π_X ∘ ε_X : Sh(LC_qc/X) → Sh(X)` is full and faithful
on sheaves of abelian groups.

This is the abelian form of the sentence Stacks 0DAG opens with. Composing with `ε_{X,*}` gives
`π_X^{-1}` up to `qcAbelianDirectImageTopologicalInverseImageNatIso`; that composite is
therefore fully faithful, `π_X^{-1}` being so by the unit clause of Stacks 0DCU, and `ε_{X,*}`
is faithful, so `a_X^{-1}` is fully faithful. -/
theorem qcTopologicalAbelianInverseImage_fullyFaithful (X : S.category) :
    (qcTopologicalAbelianInverseImage.{u, w, v} S X).Full ∧
      (qcTopologicalAbelianInverseImage.{u, w, v} S X).Faithful := by
  have _ : IsIso (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).unit :=
    abelianComparisonAdjunction_unit_isIso.{u, w, v} S X
  have hff := (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X).fullyFaithfulLOfIsIsoUnit
  have _ := hff.full
  have _ := hff.faithful
  have hcomp : (qcTopologicalAbelianInverseImage.{u, w, v} S X ⋙
      qcAbelianDirectImage.{u, w, v} S X).Full :=
    Functor.Full.of_iso (qcAbelianDirectImageTopologicalInverseImageNatIso.{u, w, v} S X).symm
  have hcomp' : (qcTopologicalAbelianInverseImage.{u, w, v} S X ⋙
      qcAbelianDirectImage.{u, w, v} S X).Faithful :=
    Functor.Faithful.of_iso (qcAbelianDirectImageTopologicalInverseImageNatIso.{u, w, v} S X).symm
  exact ⟨Functor.Full.of_comp_faithful (qcTopologicalAbelianInverseImage.{u, w, v} S X)
      (qcAbelianDirectImage.{u, w, v} S X),
    Functor.Faithful.of_comp (F := qcTopologicalAbelianInverseImage.{u, w, v} S X)
      (G := qcAbelianDirectImage.{u, w, v} S X)⟩

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
