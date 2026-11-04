module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcComparisonEmbedding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcSmallModel
public import StacksFrontier.Topology.Simplicial.ProperHypercoveringDescent
import StacksCore.Tactic.StacksAttribute

/-!
# The quasi-compact side of the comparison diagram of Stacks 0DAF

The source proves Stacks 0DAG by comparing the topos of `U_Zar` with that of the total site
`(LC_qc/U)_total` of a hypercovering of `X` in the quasi-compact site `LC_qc` of Stacks 09X2,
through the commutative diagram of Stacks 0DAF. This file supplies the quasi-compact side of
that diagram, read through the small model of `LC_qc`: the bottom horizontal arrow
`(h_{-1})^{-1}`, which is the composite inverse image of Stacks 09X3, together with its full
faithfulness, and the right-hand column, the total site of Stacks 09X8 of a hypercovering
augmentation of `LC_qc` with its augmentation morphism of topoi.

`Stacks.Topology.LocallyQuasiCompactQcSite.smallOverSheafEquiv` identifies the topos of `LC_qc/X`
with the topos of the small model's localization, which is what lets the arrow of Stacks 09X3,
landing in `Sh(LC_qc/X)`, be read as a functor into the topos over which the total site exists.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcSmallTopologicalInverseImage`: the
  bottom horizontal arrow `(h_{-1})^{-1}` of the diagram of Stacks 0DAF.
* `Stacks.Topology.Simplicial.ProperHypercovering.qcTotalSituation` and
  `.qcAugmentationMorphism`: the total site `(LC_qc/U)_total` and its augmentation morphism of
  topoi, the right-hand column of the diagram.

## Main results

* `LocallyQuasiCompactZariskiSituation.qcSmallTopologicalInverseImage_fullyFaithful` (in
  `Stacks.Topology`): the bottom horizontal arrow is fully faithful (Stacks 09X3).

## Implementation notes

Stacks 0DAG itself is proved without the diagram, by descent on stalks, in
`StacksFrontier/Topology/Simplicial/ProperHypercoveringFullyFaithful.lean`.

## References

* [Stacks Project, Tag 0DAF](https://stacks.math.columbia.edu/tag/0DAF)
* [Stacks Project, Tag 09X2](https://stacks.math.columbia.edu/tag/09X2)
* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Tag 09X8](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u w

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- **The bottom horizontal arrow of the diagram of Stacks 0DAF.** Inverse image along the
comparison morphism of topoi `a_X : Sh(LC_qc/X) → Sh(X)` of Stacks 09X3, followed by the
identification of `Sh(LC_qc/X)` with the sheaves on the small model's localization.

The composite is needed, rather than `qcTopologicalInverseImage` itself, because the total site
of Situation 09WE — the target of the right vertical arrow of the diagram — exists only over a
site whose objects form a type in the universe of its morphisms, which `LC_qc` is not and its
small model is. -/
def qcSmallTopologicalInverseImage (X : S.category) :
    Sheaf (Opens.grothendieckTopology X.obj) (Type u) ⥤
      Sheaf (S.qcSite.smallOverTopology X) (Type u) :=
  qcTopologicalInverseImage.{u, w, u} S X ⋙
    (S.qcSite.smallOverSheafEquiv X (Type u)).functor

/-- **Stacks 09X3 for the small model's localization.** The bottom horizontal arrow of the
diagram of Stacks 0DAF is fully faithful.

This is the sentence Stacks 0DAG opens with. Full faithfulness of
`qcTopologicalInverseImage` is Stacks 09X3, and the identification of the two localized topoi
is an equivalence, so the composite is fully faithful. -/
def qcSmallTopologicalInverseImage_fullyFaithful (X : S.category) :
    (qcSmallTopologicalInverseImage S X).FullyFaithful := by
  obtain ⟨hfull, hfaithful⟩ := qcTopologicalInverseImage_fullyFaithful.{u, w, u} S X
  have := hfull
  have := hfaithful
  exact (Functor.FullyFaithful.ofFullyFaithful (qcTopologicalInverseImage.{u, w, u} S X)).comp
    (S.qcSite.smallOverSheafEquiv X (Type u)).fullyFaithfulFunctor

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

namespace Stacks.Topology.Simplicial.ProperHypercovering

open Stacks.Topology Stacks.Topology.Simplicial
open Stacks.CategoryTheory.Hypercovering CategoryTheory.SimplicialSemiRepresentable
open Stacks.Topology.LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- The simplicial object of the small model determined by a hypercovering augmentation of
`LC_qc`. Named so that the ambient category of the total site below is pinned at one spelling. -/
abbrev qcSmallSimplicialObject (Uq : SimplicialObject S.category) :
    SimplicialObject S.qcSite.smallSite :=
  Uq ⋙ S.qcSite.smallEquivalence.functor

/-- The augmentation of the small model determined by a hypercovering augmentation of
`LC_qc`. -/
abbrev qcSmallAugmentation (Xq : S.category) (Uq : SimplicialObject S.category)
    (aq : Uq ⟶ (SimplicialObject.const S.category).obj Xq) :
    qcSmallSimplicialObject S Uq ⟶
      (SimplicialObject.const S.qcSite.smallSite).obj
        (S.qcSite.smallEquivalence.functor.obj Xq) :=
  S.qcSite.smallAugmentation Uq aq

/-- The total site `(LC_qc/U)_total` of Stacks 09X8 of a hypercovering augmentation of `LC_qc`,
formed in the small model. This is the right-hand column of the diagram of Stacks 0DAF. -/
abbrev qcTotalSituation (Xq : S.category) (Uq : SimplicialObject S.category)
    (aq : Uq ⟶ (SimplicialObject.const S.category).obj Xq) :
    CategoryTheory.SimplicialSiteSituation.{u} :=
  totalSituation S.qcSite.smallPretopology (qcSmallSimplicialObject S Uq)
    (qcSmallAugmentation S Xq Uq aq)

/-- The augmentation morphism of topoi of Stacks 09X8, the right vertical arrow of the diagram
of Stacks 0DAF. -/
abbrev qcAugmentationMorphism (Xq : S.category) (Uq : SimplicialObject S.category)
    (aq : Uq ⟶ (SimplicialObject.const S.category).obj Xq) :
    _root_.MorphismOfTopoi
      (Sheaf (qcTotalSituation S Xq Uq aq).totalTopology (Type u))
      (Sheaf (S.qcSite.smallOverTopology Xq) (Type u)) :=
  augmentationMorphismOfTopoi S.qcSite.smallPretopology (qcSmallSimplicialObject S Uq)
    (qcSmallAugmentation S Xq Uq aq)

end Stacks.Topology.Simplicial.ProperHypercovering

end
