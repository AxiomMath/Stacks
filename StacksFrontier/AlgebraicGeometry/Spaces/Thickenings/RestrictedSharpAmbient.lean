module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SharpCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceSection

/-!
# The transported comorphism determines the comorphism on the ambient site

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`, let
`W₀ ⊆ W` be a closed subspace with inclusion `j : W₀ ⟶ W`, and let `c : X ⟶ W` be a morphism
whose restriction to the thickening factors through `W₀`, say `i ≫ c = e₀ ≫ j`.
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceRestrictedTarget.lean` transports
the comorphism of `c`, read in the common target of the morphisms agreeing on the thickening, from
the small étale site of `W` to that of `W₀`:

`AlgebraicGeometry.Space.structureSharpThroughThickeningAt`, a morphism
`𝒪_W ⟶ (e₀ ≫ j)_*(i^{-1}𝒪_X)`, becomes
`AlgebraicGeometry.Space.restrictedSharpThroughThickening`, a morphism
`j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`.

The transport is the adjunction bijection of `j^{-1} ⊣ j_*` followed by the comparison
`AlgebraicGeometry.Space.pushforwardRingSheafCompInv` of iterated direct images, and **both are
invertible** — the first is a bijection on morphisms by construction and the second has
`AlgebraicGeometry.Space.pushforwardRingSheafCompHom` for an inverse.  So two morphisms with equal
transported comorphisms have equal comorphisms on the ambient site, and conversely.

This is where the uniqueness half of [Stacks Project, Tag 0CKE] starts: two sections of `Γ₀` with
the same difference have, by [Stacks Project, Tag 0618], the same transported comorphism; this
file carries that equality back to the site of `W`, where
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ThickeningSharpChartProjection.lean` reads it on
étale scheme charts.

## Main results

* `Space.structureSharpThroughThickeningAt_eq_of_restrictedSharpThroughThickening_eq`:
  **two morphisms whose transported comorphisms agree have equal comorphisms read in the common
  target on the site of `W`.**
* `Space.restrictedSharpThroughThickening_eq_of_structureSharpThroughThickeningAt_eq`:
  the converse.
* `Space.restrictedSharpThroughThickening_eq_iff_structureSharpThroughThickeningAt_eq`:
  the two together.

## Implementation notes

The cancellation of the comparison of iterated direct images is stated as a tiny lemma over an
abstract category with every morphism a variable, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSection.lean` require for these
composites; `rw [Category.assoc]` on the geometric terms is a deterministic `whnf` timeout.

The adjunction is used through the defining identity
`AlgebraicGeometry.Space.ringUnit_comp_map_restrictedSharpThroughThickening` rather than through
`CategoryTheory.Adjunction.homEquiv` directly: that identity is already stated at exactly these
sheaves, and composing with the unit is what makes the two sides of the equation comparable.

**No `@[stacks]` attribute is placed.**  This is a comparison of two readings of
[Stacks Project, Tag 03G8] internal to this development.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (3), iterated direct
  images.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the difference of two
  lifts.
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE), the tag this comparison
  is an input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1)

/-- **Two morphisms whose transported comorphisms agree have equal comorphisms read in the common
target on the small étale site of `W`.**

Composing with the unit of `j^{-1} ⊣ j_*` turns the equality of the transported comorphisms into
the equality of the comorphisms read through the comparison of iterated direct images, by the
defining adjunction identity
`AlgebraicGeometry.Space.ringUnit_comp_map_restrictedSharpThroughThickening`; the comparison is
invertible, so it cancels. -/
theorem structureSharpThroughThickeningAt_eq_of_restrictedSharpThroughThickening_eq
    (c c' : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (heq : restrictedSharpThroughThickening B S hS Z W₀ c e₀ h =
      restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h') :
    structureSharpThroughThickeningAt B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀) h =
      structureSharpThroughThickeningAt B S hS Z c' (e₀ ≫ subspaceInclusion B S hS W W₀) h' :=
  cancel_right_of_comp_id _ _
    (pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (pushforwardRingSheafCompHom B S hS e₀ (subspaceInclusion B S hS W W₀)
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    (pushforwardRingSheafCompInv_comp_hom B S hS e₀ (subspaceInclusion B S hS W W₀)
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
    ((ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z W₀ c e₀ h).symm.trans
      ((congrArg (fun m ↦ ringUnit (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀)) (structureRingSheaf B S hS W) ≫
          (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS W W₀))).map m) heq).trans
        (ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h')))

/-- **Two morphisms with equal comorphisms read in the common target on the site of `W` have
equal transported comorphisms.**  The transport is a function of the comorphism read through the
comparison of iterated direct images. -/
theorem restrictedSharpThroughThickening_eq_of_structureSharpThroughThickeningAt_eq
    (c c' : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (heq : structureSharpThroughThickeningAt B S hS Z c
        (e₀ ≫ subspaceInclusion B S hS W W₀) h =
      structureSharpThroughThickeningAt B S hS Z c'
        (e₀ ≫ subspaceInclusion B S hS W W₀) h') :
    restrictedSharpThroughThickening B S hS Z W₀ c e₀ h =
      restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h' :=
  congrArg (fun m ↦ ((ringImageAdjunction
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))).homEquiv
      (structureRingSheaf B S hS W)
      (restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀)).symm
    (m ≫ pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))) heq

/-- **The transported comorphism and the comorphism read in the common target on the site of `W`
determine one another.** -/
theorem restrictedSharpThroughThickening_eq_iff_structureSharpThroughThickeningAt_eq
    (c c' : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀) :
    restrictedSharpThroughThickening B S hS Z W₀ c e₀ h =
        restrictedSharpThroughThickening B S hS Z W₀ c' e₀ h' ↔
      structureSharpThroughThickeningAt B S hS Z c
          (e₀ ≫ subspaceInclusion B S hS W W₀) h =
        structureSharpThroughThickeningAt B S hS Z c'
          (e₀ ≫ subspaceInclusion B S hS W W₀) h' :=
  ⟨structureSharpThroughThickeningAt_eq_of_restrictedSharpThroughThickening_eq
      B S hS Z W₀ c c' e₀ h h',
    restrictedSharpThroughThickening_eq_of_structureSharpThroughThickeningAt_eq
      B S hS Z W₀ c c' e₀ h h'⟩

end AlgebraicGeometry.Space

end
