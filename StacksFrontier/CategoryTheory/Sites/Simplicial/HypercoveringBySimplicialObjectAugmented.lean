module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PresheafObjects
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.FromSimplicialObject
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObject
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringEssSurjAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringLocallyFull
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDescentOver

/-!
Descent of sheaves along an augmented hypercovering by a simplicial object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe w v u

namespace CategoryTheory.SimplicialSemiRepresentable

open Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)

/-- **Stacks 0DA8 (1).** Let `C` be a site with fibre products, `X` an object of `C` and
`a : U ⟶ X` a hypercovering of `X` in `C`. Then `a^{-1} : Sh(C/X) ⥤ Sh((C/U)_total)` is fully
faithful with essential image the cartesian sheaves of sets, and `a_*` is a quasi-inverse: the
unit is invertible, and the counit is invertible at every cartesian sheaf. This is Stacks 0D8K
for the hypercovering `n ↦ {U_n ⟶ X}` of `X`. -/
theorem descent_sheaves_augmented_hypercoveringBySimplicialObjectAugmented
    (h : IsHypercoveringAugmentation P U a) :
    Nonempty (augmentationMorphismOfTopoi P U a).inverseImage.FullyFaithful ∧
      (∀ F : Sheaf (totalSituation P U a).totalTopology (Type u),
        (augmentationMorphismOfTopoi P U a).inverseImage.essImage F ↔
          (totalSituation P U a).IsCartesianSheaf F) ∧
      IsIso (augmentationMorphismOfTopoi P U a).adj.unit ∧
      ∀ F : Sheaf (totalSituation P U a).totalTopology (Type u),
        (totalSituation P U a).IsCartesianSheaf F →
          IsIso ((augmentationMorphismOfTopoi P U a).adj.counit.app F) :=
  descent_sheaves_of_isHypercovering_over_hypercoveringObjectDescentOver P
    (associatedSimplicialObject.{u} U a) (h.isHypercovering P U a)

/-- **Stacks 0DA8 (2).** For a hypercovering `a : U ⟶ X` of `X` in `C` the inverse image
`a^{-1} : Ab(C/X) ⥤ Ab((C/U)_total)` is fully faithful with essential image the cartesian sheaves
of abelian groups, and `a_*` is a quasi-inverse. -/
theorem descent_abelianSheaves_augmented_hypercoveringBySimplicialObjectAugmented
    (h : IsHypercoveringAugmentation P U a) :
    Nonempty (abelianInverseImage P U a).FullyFaithful ∧
      (∀ F : Sheaf (totalSituation P U a).totalTopology Ab.{u},
        (abelianInverseImage P U a).essImage F ↔ (totalSituation P U a).IsCartesianAbSheaf F) ∧
      IsIso (abelianAdjunction P U a).unit ∧
      ∀ F : Sheaf (totalSituation P U a).totalTopology Ab.{u},
        (totalSituation P U a).IsCartesianAbSheaf F →
          IsIso ((abelianAdjunction P U a).counit.app F) :=
  descent_abelianSheaves_of_isHypercovering_over_hypercoveringObjectDescentOver P
    (associatedSimplicialObject.{u} U a) (h.isHypercovering P U a)

end CategoryTheory.SimplicialSemiRepresentable

end
