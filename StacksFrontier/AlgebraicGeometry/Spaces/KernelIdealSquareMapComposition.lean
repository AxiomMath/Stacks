module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealSquareMap
public import StacksFrontier.CategoryTheory.CompositeGluing

/-!
# The composition law for the map of kernel ideal sheaves of a commutative square

Let
```
Z₁ --i₁--→ X₁
|          |
f₁         g₁
↓          ↓
Z₂ --i₂--→ X₂
|          |
f₂         g₂
↓          ↓
Z₃ --i₃--→ X₃
```
be two commutative squares of algebraic spaces stacked vertically.
`AlgebraicGeometry.Space.kernelIdealSquareMap` attaches to each the map

`g^*(Ker(i'^♯)ⁿ) ⟶ Ker(i^♯)ⁿ`

of the `n`-th powers of the kernel ideal sheaves. This file proves that the map of the composite
square is the composite of the two, read through the composition comparison of inverse images of
[Stacks Project, Tag 03LU].

That is the ideal-sheaf level of the composition law of [Stacks Project, Tag 04G2] part (3) at
immersion generality, and it is where the content of that law sits: the canonical map of a square
is the square comparison followed by the inverse image along `i` of this single map
(`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_eq_comp`), and the square comparison is
built from `AlgebraicGeometry.Space.modulePullbackCompIso` alone.

## Route

Both sides are maps into a submodule of the unit module, whose inclusion is a monomorphism, so
it is enough to compare their composites with that inclusion. On each side
`AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι` turns the composite into the inverse image
of the inclusion followed by the comparison `g^*𝒪 ⟶ 𝒪` of
`AlgebraicGeometry.Space.structureModulePullbackMap`, and what is then left is exactly the
composition law for that comparison,
`AlgebraicGeometry.Space.structureModulePullbackMap_comp`, together with the naturality of the
composition comparison of inverse images.

No hypothesis on the four morphisms of either square is used beyond the two commutativities —
in particular nothing is assumed about immersions, closedness, quasi-compactness or
quasi-coherence.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_naturality_comp`: naturality of the
  inverse composition comparison, read at one object with the tail of the composite left as a
  variable.
* `AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι_lower`: the lower two factors of the
  claimed composite, read inside the structure sheaf.
* `AlgebraicGeometry.Space.kernelIdealSquareMap_comp`: **the composition law.**  The
  commutativity of the outer rectangle is a hypothesis of its own rather than assembled from the
  other two, so that the law composes with the one for the square comparison, which takes it the
  same way.

## Implementation notes

Every step is term mode and every reassociation is a generic lemma instantiated —
`CategoryTheory.map_comp_app_comp_of_naturality` and `CategoryTheory.comp_comp_eq_comp_of` of
`StacksFrontier/AlgebraicGeometry/Spaces/KernelIdealSquareMap.lean`,
`Stacks.CategoryTheory.map_square` and `Stacks.CategoryTheory.eq_comp_of_comp_mono`. That is
forced: `AlgebraicGeometry.Space.Modules` and `SheafOfModules` of the structure ring sheaf are
the same type only up to an unfolding that `rw` will not perform, so every `rw` whose motive
mentions a module here fails with *the target expression is not type-correct under the
`implicit` transparency level* — including the `rw [← cancel_mono …]` that would start the
argument. Each of the three steps also has its own declaration, the heartbeat budget being per
declaration.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z₁ Z₂ Z₃ X₁ X₂ X₃ : AlgebraicSpaces B S hS}

/-- Naturality of the inverse composition comparison of [Stacks Project, Tag 03LU], read at one
object with the tail of the composite left as a variable.  Its own declaration, for the reason
`AlgebraicGeometry.Space.squarePullbackCompIso_hom_app_naturality_comp` records: reconciling the
composite functor's action with the iterated one is what costs. -/
theorem modulePullbackCompIso_inv_app_naturality_comp (g₁ : X₁ ⟶ X₂) (g₂ : X₂ ⟶ X₃)
    {M N : Modules.{u, u} B S hS X₃.1 X₃.2} (c : M ⟶ N)
    {V : Modules.{u, u} B S hS X₁.1 X₁.2}
    (r : (modulePullback B S hS g₁).obj ((modulePullback B S hS g₂).obj N) ⟶ V) :
    (modulePullback B S hS (g₁ ≫ g₂)).map c ≫
        (modulePullbackCompIso B S hS g₁ g₂).inv.app N ≫ r =
      (modulePullbackCompIso B S hS g₁ g₂).inv.app M ≫
        (modulePullback B S hS g₁).map ((modulePullback B S hS g₂).map c) ≫ r :=
  CategoryTheory.map_comp_app_comp_of_naturality
    (modulePullbackCompIso B S hS g₁ g₂).inv c r

/-- **The lower two factors of the claimed composite, read inside the structure sheaf.**  The
inverse image along `g₁` of the map of the lower square, followed by the map of the upper square
and the inclusion into `𝒪_{X₁}`, is the inverse image of the inclusion of `Ker(i₃^♯)ⁿ` followed
by the two comparisons `g^*𝒪 ⟶ 𝒪`. -/
theorem kernelIdealSquareMap_comp_ι_lower (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂) (i₃ : Z₃ ⟶ X₃)
    (f₁ : Z₁ ⟶ Z₂) (g₁ : X₁ ⟶ X₂) (f₂ : Z₂ ⟶ Z₃) (g₂ : X₂ ⟶ X₃) (hsq₁ : i₁ ≫ g₁ = f₁ ≫ i₂)
    (hsq₂ : i₂ ≫ g₂ = f₂ ≫ i₃) (n : ℤ) :
    ((modulePullback B S hS g₁).map (kernelIdealSquareMap B S hS i₂ i₃ f₂ g₂ hsq₂ n) ≫
          kernelIdealSquareMap B S hS i₁ i₂ f₁ g₁ hsq₁ n) ≫
        (kernelIdealSheafZPow B S hS i₁ n).ι =
      (modulePullback B S hS g₁).map
          ((modulePullback B S hS g₂).map (kernelIdealSheafZPow B S hS i₃ n).ι) ≫
        (modulePullback B S hS g₁).map (structureModulePullbackMap B S hS g₂) ≫
          structureModulePullbackMap B S hS g₁ :=
  (CategoryTheory.comp_comp_eq_comp_of _ _ _ _ _ _
        (kernelIdealSquareMap_comp_ι B S hS i₁ i₂ f₁ g₁ hsq₁ n)
        (Stacks.CategoryTheory.map_square (modulePullback B S hS g₁)
          (kernelIdealSquareMap_comp_ι B S hS i₂ i₃ f₂ g₂ hsq₂ n))).trans
    (Category.assoc _ _ _)

/-- **The map of kernel ideal sheaves of two vertically stacked commutative squares composes.**
For the composite square the map is the inverse composition comparison of [Stacks Project,
Tag 03LU], followed by the inverse image along `g₁` of the map of the lower square, followed by
the map of the upper square.

Only the two commutativities are used: nothing is assumed about immersions, closedness,
quasi-compactness or quasi-coherence. -/
theorem kernelIdealSquareMap_comp (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂) (i₃ : Z₃ ⟶ X₃) (f₁ : Z₁ ⟶ Z₂)
    (g₁ : X₁ ⟶ X₂) (f₂ : Z₂ ⟶ Z₃) (g₂ : X₂ ⟶ X₃) (hsq₁ : i₁ ≫ g₁ = f₁ ≫ i₂)
    (hsq₂ : i₂ ≫ g₂ = f₂ ≫ i₃) (hsq : i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃) (n : ℤ) :
    kernelIdealSquareMap B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hsq n =
      (modulePullbackCompIso B S hS g₁ g₂).inv.app
          (kernelIdealSheafZPow B S hS i₃ n).toSheafOfModules ≫
        (modulePullback B S hS g₁).map (kernelIdealSquareMap B S hS i₂ i₃ f₂ g₂ hsq₂ n) ≫
          kernelIdealSquareMap B S hS i₁ i₂ f₁ g₁ hsq₁ n :=
  Stacks.CategoryTheory.eq_comp_of_comp_mono (kernelIdealSheafZPow B S hS i₁ n).ι
    (kernelIdealSquareMap_comp_ι B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hsq n)
    (structureModulePullbackMap_comp B S hS g₁ g₂)
    (modulePullbackCompIso_inv_app_naturality_comp B S hS g₁ g₂
      (kernelIdealSheafZPow B S hS i₃ n).ι
      ((modulePullback B S hS g₁).map (structureModulePullbackMap B S hS g₂) ≫
        structureModulePullbackMap B S hS g₁))
    (kernelIdealSquareMap_comp_ι_lower B S hS i₁ i₂ i₃ f₁ g₁ f₂ g₂ hsq₁ hsq₂ n)

end AlgebraicGeometry.Space

end
