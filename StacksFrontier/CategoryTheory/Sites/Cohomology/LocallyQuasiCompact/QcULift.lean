module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcComparisonEmbedding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiProperBaseChangeClause
public import StacksFrontier.Topology.Sheaves.Limits.GermPullbackULift

/-!
# The comparison inverse images of `LC_qc` commute with lifting the universe

Let `X` be an object of the quasi-compact site `LC_qc` of Stacks 09X2 and let
`a_X = π_X ∘ ε_X : Sh(LC_qc/X) → Sh(X)` be its comparison morphism of topoi (Section 09WY). Its
inverse image is defined for sheaves of sets in every universe containing that of the spaces,
and it commutes with lifting the universe of a sheaf of sets from `u` to `u + 1`:
`a_X^{-1}(F ⋙ ULift) ≅ (a_X^{-1}F) ⋙ ULift`.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.germSectionsPresheafULiftIso`: the
  germ-model sections presheaf of Stacks 09X3 commutes with lifting the universe.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonInverseImageULiftIso`:
  `π_X^{-1}` commutes with lifting the universe.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.qcTopologicalInverseImageULiftIso`:
  `a_X^{-1}` commutes with lifting the universe.

## References

* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Section 09WY](https://stacks.math.columbia.edu/tag/09WY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u w

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)

/-- The germ-model sections presheaf of Stacks 09X3 of the universe lift of a sheaf of sets is
the universe lift of its germ-model sections presheaf. -/
def germSectionsPresheafULiftIso (F : Sheaf (Opens.grothendieckTopology X.obj) (Type u)) :
    germSectionsPresheaf.{u, w, u + 1} S X
        ((sheafCompose (Opens.grothendieckTopology X.obj) uliftFunctor.{u + 1, u}).obj F) ≅
      germSectionsPresheaf.{u, w, u} S X F ⋙ uliftFunctor.{u + 1, u} :=
  NatIso.ofComponents
    (fun _ => ((GermPullback.sectionsULiftEquiv F.1 ⊤).symm.trans Equiv.ulift.symm).toIso)
    (fun {_ _} _ => ConcreteCategory.hom_ext _ _ fun _ => rfl)

/-- `π_X^{-1}` commutes with lifting the universe: for a sheaf of sets `F` on the space of `X`,
the Zariski comparison inverse image of the lift of `F` is the lift of `π_X^{-1}F`. -/
def comparisonInverseImageULiftIso (F : Sheaf (Opens.grothendieckTopology X.obj) (Type u)) :
    (comparisonInverseImage.{u, w, u + 1} S X).obj
        ((sheafCompose (Opens.grothendieckTopology X.obj) uliftFunctor.{u + 1, u}).obj F) ≅
      (sheafCompose (S.zariskiTopology.over X) uliftFunctor.{u + 1, u}).obj
        ((comparisonInverseImage.{u, w, u} S X).obj F) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (germSectionsPresheafIso.{u, w, u + 1} S X _ ≪≫ germSectionsPresheafULiftIso S X F ≪≫
      Functor.isoWhiskerRight (germSectionsPresheafIso.{u, w, u} S X F).symm _)

/-- `a_X^{-1}` commutes with lifting the universe: for a sheaf of sets `F` on the space of `X`,
the comparison inverse image `a_X^{-1} = ε_X^{-1}π_X^{-1}` of the lift of `F` is the lift of
`a_X^{-1}F`. -/
def qcTopologicalInverseImageULiftIso (F : Sheaf (Opens.grothendieckTopology X.obj) (Type u)) :
    (qcTopologicalInverseImage.{u, w, u + 1} S X).obj
        ((sheafCompose (Opens.grothendieckTopology X.obj) uliftFunctor.{u + 1, u}).obj F) ≅
      (sheafCompose (S.qcSite.grothendieckTopology.over X) uliftFunctor.{u + 1, u}).obj
        ((qcTopologicalInverseImage.{u, w, u} S X).obj F) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (show ((qcTopologicalInverseImage.{u, w, u + 1} S X).obj
          ((sheafCompose (Opens.grothendieckTopology X.obj) uliftFunctor.{u + 1, u}).obj F)).obj ≅
        ((qcTopologicalInverseImage.{u, w, u} S X).obj F).obj ⋙ uliftFunctor.{u + 1, u} from
      (sheafToPresheaf (S.zariskiTopology.over X) _).mapIso
          ((qcDirectImageTopologicalInverseImageIso.{u, w, u + 1} S X).app
            ((sheafCompose (Opens.grothendieckTopology X.obj) uliftFunctor.{u + 1, u}).obj F)) ≪≫
        (sheafToPresheaf (S.zariskiTopology.over X) _).mapIso
          (comparisonInverseImageULiftIso S X F) ≪≫
        Functor.isoWhiskerRight ((sheafToPresheaf (S.zariskiTopology.over X) _).mapIso
          ((qcDirectImageTopologicalInverseImageIso.{u, w, u} S X).app F)).symm
          uliftFunctor.{u + 1, u})

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
