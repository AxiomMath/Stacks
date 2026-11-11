module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonEmbedding
import StacksCore.Tactic.StacksAttribute

/-!
# The quasi-compact comparison morphism is an embedding of topoi

Let `X` be an object of the site `LC_α` of Hausdorff, locally quasi-compact spaces, and let
`a_X = π_X ∘ ε_X : Sh(LC_qc/X) → Sh(X)` be the comparison morphism of topoi to sheaves on the
underlying space, as in
`Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcTopologicalMorphism`. This file proves
that `a_X^{-1}` is fully faithful with quasi-inverse `a_{X,*}`, which is the consequence of
Stacks 09X3 that Stacks 0DAG quotes in its opening sentence for the bottom horizontal arrow
`h_{-1}` of the diagram of Stacks 0DAF.

The argument is the one the source gives. Stacks 09X3 identifies `a_X^{-1}F` with the presheaf
`(f : Y → X) ↦ Γ(Y, f^{-1}F)`, whose content here is that the Zariski comparison inverse image
`π_X^{-1}F` already satisfies the sheaf condition for the quasi-compact topology
(`isSheaf_qc_comparisonInverseImage`). Hence the unit of the change-of-topology adjunction
`ε_X^{-1} ⊣ ε_{X,*}` is invertible at every `π_X^{-1}F`, so

`a_{X,*} a_X^{-1} = ε_{X,*} ε_X^{-1} π_X^{-1} ≅ π_X^{-1}`

as functors, which is `qcDirectImageTopologicalInverseImageIso`. Since `π_X^{-1}` is fully
faithful (`comparisonInverseImage_fullyFaithful`, the sheaves-of-sets form of the unit clause of
Stacks 0DCU) and `ε_{X,*}` is faithful, being a full subcategory inclusion, full faithfulness of
`a_X^{-1}` follows by cancelling `ε_{X,*}`.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcDirectImageTopologicalInverseImageIso`:
  the identification `ε_{X,*} a_X^{-1} = π_X^{-1}`.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcTopologicalInverseImage_fullyFaithful`:
  `a_X^{-1}` is full and faithful.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcTopologicalAdjunction_unit_isIso`:
  equivalently, the unit of `a_X^{-1} ⊣ a_{X,*}` is an isomorphism, so `a_{X,*}` is a
  quasi-inverse of `a_X^{-1}` on its essential image.

## Implementation notes

Both statements are for sheaves of sets, at coefficients in any universe containing the universe
of the spaces, which is the generality of `isSheaf_qc_comparisonInverseImage`. The abelian
form of that sheaf condition, a clause of Stacks 0EZI, is `zariskiPullbackClass_isSheaf_qc`, and
the abelian counterpart of these statements is `qcAbelianDirectImageTopologicalInverseImageNatIso`
and `qcTopologicalAbelianInverseImage_fullyFaithful` (in `QcAbelianComparisonEmbedding.lean`).

Full faithfulness is returned as a conjunction of `Full` and `Faithful`, matching
`comparisonInverseImage_fullyFaithful`, rather than as instances.

## References

* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 0DAG](https://stacks.math.columbia.edu/tag/0DAG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w t

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- The unit of the change-of-topology adjunction is invertible at every Zariski comparison
inverse image `π_X^{-1}F`, because that sheaf already satisfies the sheaf condition for the
quasi-compact topology. -/
theorem isIso_qcComparisonAdjunction_unit_app_comparisonInverseImage (X : S.category)
    (F : Sheaf (Opens.grothendieckTopology X.obj) (Type (max u t))) :
    IsIso ((qcComparisonAdjunction.{u, w, t} S X).unit.app
      ((comparisonInverseImage.{u, w, t} S X).obj F)) :=
  isIso_qcComparisonAdjunction_unit_app.{u, w, t} S X _
    (isSheaf_qc_comparisonInverseImage.{u, w, t} S X F)

/-- **Stacks 09X3, the identification `ε_{X,*} a_X^{-1} = π_X^{-1}`.** Direct image along the
change-of-topology morphism undoes quasi-compact sheafification on the Zariski comparison
inverse images, because those are already quasi-compact sheaves. -/
@[stacks 09X3 "the identification eps_{X,*}a_X^{-1} = pi_X^{-1} on sheaves of sets"]
def qcDirectImageTopologicalInverseImageIso (X : S.category) :
    qcTopologicalInverseImage.{u, w, t} S X ⋙ qcDirectImage.{u, w, t} S X ≅
      comparisonInverseImage.{u, w, t} S X :=
  (NatIso.ofComponents
    (fun F =>
      have := isIso_qcComparisonAdjunction_unit_app_comparisonInverseImage.{u, w, t} S X F
      asIso ((qcComparisonAdjunction.{u, w, t} S X).unit.app
        ((comparisonInverseImage.{u, w, t} S X).obj F)))
    (fun f => (qcComparisonAdjunction.{u, w, t} S X).unit.naturality
      ((comparisonInverseImage.{u, w, t} S X).map f))).symm

/-- **Stacks 09X3, full faithfulness of `a_X^{-1}`.** The inverse image along the comparison
morphism `a_X = π_X ∘ ε_X : Sh(LC_qc/X) → Sh(X)` is full and faithful on sheaves of sets.

This is the sentence Stacks 0DAG opens with, for the bottom horizontal arrow of the diagram of
Stacks 0DAF: `(h_{-1})^{-1}` is fully faithful with quasi-inverse `h_{-1,*}`.

Composing with `ε_{X,*}` gives `π_X^{-1}` up to the isomorphism
`qcDirectImageTopologicalInverseImageIso`; that composite is therefore fully faithful, and
`ε_{X,*}` is faithful, so `a_X^{-1}` is fully faithful. -/
@[stacks 09X3 "full faithfulness of the composite inverse image a_X^{-1} on sheaves of sets"]
theorem qcTopologicalInverseImage_fullyFaithful (X : S.category) :
    (qcTopologicalInverseImage.{u, w, t} S X).Full ∧
      (qcTopologicalInverseImage.{u, w, t} S X).Faithful := by
  obtain ⟨hfull, hfaithful⟩ := comparisonInverseImage_fullyFaithful.{u, w, t} S X
  have := hfull
  have := hfaithful
  have hcomp : (qcTopologicalInverseImage.{u, w, t} S X ⋙
      qcDirectImage.{u, w, t} S X).Full :=
    Functor.Full.of_iso (qcDirectImageTopologicalInverseImageIso.{u, w, t} S X).symm
  have hcomp' : (qcTopologicalInverseImage.{u, w, t} S X ⋙
      qcDirectImage.{u, w, t} S X).Faithful :=
    Functor.Faithful.of_iso (qcDirectImageTopologicalInverseImageIso.{u, w, t} S X).symm
  exact ⟨Functor.Full.of_comp_faithful (qcTopologicalInverseImage.{u, w, t} S X)
      (qcDirectImage.{u, w, t} S X),
    Functor.Faithful.of_comp (F := qcTopologicalInverseImage.{u, w, t} S X)
      (G := qcDirectImage.{u, w, t} S X)⟩

/-- **Stacks 09X3, the quasi-inverse clause.** The unit of the adjunction
`a_X^{-1} ⊣ a_{X,*}` of the comparison morphism of topoi is an isomorphism: `a_{X,*}` recovers
every sheaf on the space from its inverse image. -/
@[stacks 09X3 "the unit of a_X^{-1} is invertible on sheaves of sets"]
theorem qcTopologicalAdjunction_unit_isIso (X : S.category) :
    IsIso (qcTopologicalMorphism.{u, w, t} S X).adj.unit := by
  obtain ⟨hfull, hfaithful⟩ := qcTopologicalInverseImage_fullyFaithful.{u, w, t} S X
  have h1 : (qcTopologicalMorphism.{u, w, t} S X).inverseImage.Full := hfull
  have h2 : (qcTopologicalMorphism.{u, w, t} S X).inverseImage.Faithful := hfaithful
  exact Adjunction.unit_isIso_of_L_fully_faithful (qcTopologicalMorphism.{u, w, t} S X).adj

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
