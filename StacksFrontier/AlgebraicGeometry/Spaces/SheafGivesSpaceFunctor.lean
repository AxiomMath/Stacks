module

public import Mathlib.CategoryTheory.Sites.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleInverseImageUnitors
public import StacksFrontier.CategoryTheory.Bicategory.PseudofunctorSections

/-!
# The functor of Stacks 0GF6

For a sheaf of sets `𝓕` on the étale site of an algebraic space `Y` over `S`, Stacks 0GF6
considers the functor
`X(T) = {(y, s) | y : T → Y a morphism over S and s ∈ Γ(T, y⁻¹ 𝓕)}`
on `(Sch/S)_fppf`, with restriction along `g : T' ⟶ T` given by `(y, s) ↦ (y ∘ g, g⁻¹ s)`. We
define this functor, with `y⁻¹` the spaces-étale inverse image of Stacks 03G2, and show that for a
sheaf on the small étale site the sets of sections agree with those of the spaces-étale sheaf
corresponding to it under the equivalence of Stacks 03G1
(`AlgebraicGeometry.Space.smallEtaleToposEquiv`).

## Main definitions

* `AlgebraicGeometry.Space.sheafPairsPresheaf`: the functor of Stacks 0GF6, as a presheaf on the
  category of all algebraic spaces over `S`.
* `AlgebraicGeometry.Space.sheafPairsFunctor`: its restriction along the Yoneda embedding of the
  schemes of the big fppf site, the functor `X` on `(Sch/S)_fppf`.
* `AlgebraicGeometry.Space.sheafPairsToBase`: the structural morphism `X ⟶ Y`, the first
  projection.
* `AlgebraicGeometry.Space.smallEtaleSectionsEquiv`: the bijection between the global sections of
  the small étale inverse image `y⁻¹F` and those of the corresponding spaces-étale inverse image.

## Main results

* `AlgebraicGeometry.Space.sheafPairsPresheaf_obj`: the values of the functor are the pairs
  `(y, s)`.
* `AlgebraicGeometry.Space.sheafPairsPresheaf_map_fst`: restriction composes the first coordinate
  with the morphism of the base.

## References

* [Stacks Project, Tag 0GF6](https://stacks.math.columbia.edu/tag/0GF6)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The fibres of the spaces-étale inverse-image pseudofunctor have terminal objects, being
categories of sheaves of sets. -/
instance hasTerminal_spacesEtaleSheafCat (X : AlgebraicSpaces B S hS) :
    HasTerminal (spacesEtaleSheafCat B S hS X) :=
  inferInstanceAs (HasTerminal (Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1))))

/-- The terminal sheaf on the spaces-étale site of an algebraic space, read as an object of the
fibre `AlgebraicGeometry.Space.spacesEtaleSheafCat`. -/
noncomputable abbrev terminalSpacesEtaleSheaf (X : AlgebraicSpaces B S hS) :
    spacesEtaleSheafCat B S hS X :=
  ⊤_ (spacesEtaleSheafCat B S hS X)

/-- `AlgebraicGeometry.Space.terminalSpacesEtaleSheaf` is terminal. -/
noncomputable def terminalSpacesEtaleSheaf_isTerminal (X : AlgebraicSpaces B S hS) :
    IsTerminal (terminalSpacesEtaleSheaf B S hS X) :=
  terminalIsTerminal

/-- The spaces-étale inverse image carries terminal sheaves to terminal sheaves. -/
noncomputable def spacesEtaleInverseImage_isTerminal_obj {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {A : spacesEtaleSheafCat B S hS Y} (hA : IsTerminal A) :
    IsTerminal ((spacesEtaleInverseImage B S hS f).obj A) := by
  letI := (spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi.preservesFiniteLimits
  exact hA.isTerminalObj _ _

/-- **The functor of Stacks 0GF6**, on the category of all algebraic spaces over `S`: it sends
an algebraic space `T` to the set of pairs `(y, s)` with `y : T ⟶ Y` a morphism over `S` and
`s` a global section of the spaces-étale inverse image `y⁻¹ G`, and restricts along
`g : T' ⟶ T` by `(y, s) ↦ (g ≫ y, g⁻¹ s)`. -/
noncomputable def sheafPairsPresheaf {Y : AlgebraicSpaces B S hS}
    (G : spacesEtaleSheafCat B S hS Y) :
    (AlgebraicSpaces B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  LocallyDiscrete.sectionsPresheaf (spacesEtaleSheafCat B S hS)
    (fun {_ _} f => spacesEtaleInverseImage B S hS f)
    (fun X => terminalSpacesEtaleSheaf B S hS X)
    (fun X => terminalSpacesEtaleSheaf_isTerminal B S hS X)
    (fun {_ _} f {_} hA => spacesEtaleInverseImage_isTerminal_obj B S hS f hA)
    (fun X => spacesEtaleInverseImage_id B S hS X)
    (fun {_ _ _} f g => spacesEtaleInverseImage_comp B S hS f g)
    (fun {_ _} p => spacesEtaleInverseImage_id_comp B S hS p)
    (fun {_ _ _ _} f g h => spacesEtaleInverseImage_comp_assoc B S hS f g h) G

/-- The values of the functor of Stacks 0GF6 are the pairs `(y, s)`. -/
theorem sheafPairsPresheaf_obj {Y : AlgebraicSpaces B S hS}
    (G : spacesEtaleSheafCat B S hS Y) (T : (AlgebraicSpaces B S hS)ᵒᵖ) :
    (sheafPairsPresheaf B S hS G).obj T =
      Σ y : T.unop ⟶ Y, (terminalSpacesEtaleSheaf B S hS T.unop ⟶
        (spacesEtaleInverseImage B S hS y).obj G) :=
  rfl

/-- Restriction in the functor of Stacks 0GF6 acts on the first coordinate by composing with
the morphism of the base. -/
theorem sheafPairsPresheaf_map_fst {Y : AlgebraicSpaces B S hS}
    (G : spacesEtaleSheafCat B S hS Y) {T T' : (AlgebraicSpaces B S hS)ᵒᵖ} (g : T ⟶ T')
    (p : (sheafPairsPresheaf B S hS G).obj T) :
    ((sheafPairsPresheaf B S hS G).map g p).1 = g.unop ≫ p.1 :=
  rfl

/-- **The structural morphism `X ⟶ Y` of Stacks 0GF6**: the first projection, sending a pair
`(y, s)` to the morphism `y : T ⟶ Y`. -/
noncomputable def sheafPairsToBase {Y : AlgebraicSpaces B S hS}
    (G : spacesEtaleSheafCat B S hS Y) :
    sheafPairsPresheaf B S hS G ⟶ yoneda.obj Y where
  app _ := TypeCat.ofHom fun p => p.1
  naturality _ _ _ := rfl

/-- For a sheaf `F` of sets on the small étale site of `Y` and a morphism `y : T ⟶ Y` of
algebraic spaces, the global sections of the small étale inverse image `y⁻¹ F` of Stacks 03G2
part (3) are in bijection with the global sections of the spaces-étale inverse image of the
spaces-étale sheaf corresponding to `F` under the comparison equivalence of Stacks 03G1. -/
noncomputable def smallEtaleSectionsEquiv {T Y : AlgebraicSpaces B S hS} (y : T ⟶ Y)
    (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1))) :
    (⊤_ (Sheaf (SmallEtale.topology B S hS T.1) (Type (u + 1))) ⟶
        (smallToposMorphism B S hS y).inverseImage.obj F) ≃
      (terminalSpacesEtaleSheaf B S hS T ⟶ (spacesEtaleInverseImage B S hS y).obj
        ((smallEtaleToposEquiv B S hS Y).inverse.obj F)) :=
  have hT : IsTerminal ((smallEtaleToposEquiv B S hS T).inverse.obj
      (⊤_ (Sheaf (SmallEtale.topology B S hS T.1) (Type (u + 1))))) :=
    terminalIsTerminal.isTerminalObj _ _
  (((smallEtaleToposEquiv B S hS T).symm.toAdjunction.homEquiv _ _).symm).trans
    (Iso.homCongr (hT.uniqueUpToIso (terminalSpacesEtaleSheaf_isTerminal B S hS T))
      (Iso.refl _))

/-- **The functor `X` of Stacks 0GF6**, on `(Sch/S)_fppf`: the
restriction of `AlgebraicGeometry.Space.sheafPairsPresheaf` along the Yoneda embedding of the
schemes of the big fppf site into the algebraic spaces over `S`. -/
noncomputable abbrev sheafPairsFunctor {Y : AlgebraicSpaces B S hS}
    (G : spacesEtaleSheafCat B S hS Y) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1) :=
  (schemeSpaceFunctor B S hS).op ⋙ sheafPairsPresheaf B S hS G

end AlgebraicGeometry.Space

end
