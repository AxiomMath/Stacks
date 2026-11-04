module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpCompFactorization
public import StacksFrontier.Deformation.ToposThickening.Helpers.ThickeningTargetPushforward

/-!
# The morphism of thickened small étale topoi of a factorization

For morphisms of algebraic spaces `f : X ⟶ Y`, `g : Y ⟶ Z` and `k = f ≫ g`, the morphism of small
étale ringed topoi of `g` relates the morphisms of `f` and of `k`: the structure map of `k`,
read through the comparison `k_*𝒪_X ≅ g_*f_*𝒪_X` of Stacks 03G8, is `g^♯` followed by `g_*f^♯`.
This is the datum `Deformation.ToposThickening.ThickeningTargetMorphism` for the two
thickenings `X ⊂ Y` and `X ⊂ Z` when `f` and `k` are first order thickenings, as for
`X_A ⊂ X_{A'₂} ⊂ X_{A'₁}` and a surjection `A'₁ ⟶ A'₂` of thickenings of `A`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleThickeningTarget`: the datum.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS}

/-- The comparison `(f ≫ g)_*𝒪_X ⟶ g_*f_*𝒪_X` of Stacks 03G8. -/
def smallEtaleCompBaseMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    Deformation.ToposThickening.baseRing.{u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (f ≫ g)) ⟶
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).obj
        (Deformation.ToposThickening.baseRing.{u, u + 1, u, u, u + 1, u}
          (smallEtaleRingedToposHom B S hS f)) :=
  (smallEtaleRingedToposHom_compRingIso B S hS f g).inv.app (smallEtaleRingedTopos B S hS X).O ≫
    (pushforwardStructureCompIso B S hS f g (smallEtaleRingedTopos B S hS X).O).inv

/-- The structure map of `f ≫ g` followed by the comparison `(f ≫ g)_*𝒪_X ⟶ g_*f_*𝒪_X` is
`g^♯` followed by `g_*f^♯` (Stacks 03G8). -/
theorem fSharp_comp_smallEtaleCompBaseMap (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleRingedToposHom B S hS (f ≫ g)).fSharp ≫ smallEtaleCompBaseMap f g =
      (smallEtaleRingedToposHom B S hS g).fSharp ≫
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map
          (smallEtaleRingedToposHom B S hS f).fSharp := by
  refine (congrArg (· ≫ smallEtaleCompBaseMap f g)
    (smallEtaleRingedToposHom_comp_fSharp B S hS f g).symm).trans ?_
  simp only [smallEtaleCompBaseMap, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [smallEtaleRingedToposHom_comp_fSharp_eq']
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The morphism of small étale ringed topoi of `g`, relating those of `f` and of `f ≫ g`.**
The comparison of the two bases is the inverse of Stacks 03G8's comparison of direct images. -/
def smallEtaleThickeningTarget (f : X ⟶ Y) (g : Y ⟶ Z) :
    Deformation.ToposThickening.ThickeningTargetMorphism.{u, u + 1, u, u + 1, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS (f ≫ g)) (smallEtaleRingedToposHom B S hS f) where
  j := smallEtaleRingedToposHom B S hS g
  ρ := smallEtaleCompBaseMap f g
  comm := fSharp_comp_smallEtaleCompBaseMap f g

end AlgebraicGeometry.Space

end
