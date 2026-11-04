module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SharpCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedSharpAmbient

/-!
# Lifting a transported comorphism back to the ambient site

Let `Z ⊆ X` be a thickening of algebraic spaces over a scheme `S` with inclusion `i : Z ⟶ X`,
let `W₀ ⊆ W` be a closed subspace with inclusion `j : W₀ ⟶ W` and let `e₀ : Z ⟶ W₀` be a
morphism. The transport `AlgebraicGeometry.Space.restrictedSharpThroughThickening` carries the
comorphism of a morphism `c : X ⟶ W` with `i ≫ c = e₀ ≫ j`, read in the common target of the
morphisms agreeing on the thickening, from the small étale site of `W` to that of `W₀`:

`𝒪_W ⟶ (e₀ ≫ j)_*(i^{-1}𝒪_X)` becomes `j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`.

This file carries an arbitrary morphism `g : j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)` back to the ambient
site, inverting the transport: the adjunction `j^{-1} ⊣ j_*` is a bijection on morphisms and the
comparison of iterated direct images has `AlgebraicGeometry.Space.pushforwardRingSheafCompHom` for
an inverse. So the transport is a bijection, and a morphism `j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)` on
the site of `W₀` is the same thing as a morphism `𝒪_W ⟶ (e₀ ≫ j)_*(i^{-1}𝒪_X)` on the site of
`W`.

## Main definitions

* `AlgebraicGeometry.Space.liftRestrictedSharpThroughThickening`: the morphism on the ambient
  site attached to a morphism on the site of `W₀`.

## Main results

* `AlgebraicGeometry.Space.liftRestrictedSharpThroughThickening_restrictedSharpThroughThickening`:
  **it inverts the transport** — at the transported comorphism of a morphism `c` it is the
  comorphism of `c` read in the common target.
* `AlgebraicGeometry.Space.restrictedSharpThroughThickening_liftRestrictedSharpThroughThickening`:
  the transport inverts it, in the shape in which the transported comorphism is read off a
  lift.
* `AlgebraicGeometry.Space.liftRestrictedSharpThroughThickening_injective`: it is injective, so
  two lifts with the same morphism on the ambient site are equal.

## Implementation notes

The adjunction is used through the identity
`Stacks.Sheaves.ToposPushforward.ringImageAdjunction_homEquiv_apply` rather than through
`CategoryTheory.Adjunction.homEquiv` directly, so that the definition is a composite of named
morphisms of sheaves of rings and the equations below are cancellations of composites.

The target is written out as the direct image along `e₀ ≫ j`, which is the index
`AlgebraicGeometry.Space.structureSharpThroughThickeningAt` carries; no `eqToHom` appears, since
the index of the target here is the composite on the nose.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (3), iterated
  direct images.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the difference of two
  lifts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (W₀ : ClosedSubspaces B S hS W.1)

/-- **A morphism `j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)` on the small étale site of `W₀`, carried back
to the ambient site of `W`:** the adjunct along `j^{-1} ⊣ j_*`, read through the comparison of
iterated direct images. This is the inverse of the transport
`AlgebraicGeometry.Space.restrictedSharpThroughThickening`. -/
noncomputable def liftRestrictedSharpThroughThickening
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (g : structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) ⟶
      restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀) :
    structureRingSheaf B S hS W ⟶
      pullbackRingSheaf.{u, u, u, u + 1, u, u + 1} (SmallEtale.topology B S hS W.1)
        (smallToposMorphismTypeU B S hS (e₀ ≫ subspaceInclusion B S hS W W₀)).pushforward
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) :=
  (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))
        (structureRingSheaf B S hS W) ≫
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS W W₀))).map g) ≫
    pushforwardRingSheafCompHom B S hS e₀ (subspaceInclusion B S hS W W₀)
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))

/-- **The lift inverts the transport.** At the transported comorphism of a morphism `c` with
`i ≫ c = e₀ ≫ j` it is the comorphism of `c` read in the common target of the morphisms
agreeing on the thickening. -/
theorem liftRestrictedSharpThroughThickening_restrictedSharpThroughThickening (c : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀) :
    liftRestrictedSharpThroughThickening B S hS Z W₀ e₀
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h) =
      structureSharpThroughThickeningAt B S hS Z c
        (e₀ ≫ subspaceInclusion B S hS W W₀) h :=
  (congrArg
      (fun m ↦ m ≫ pushforwardRingSheafCompHom B S hS e₀ (subspaceInclusion B S hS W W₀)
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))
      (ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z W₀ c e₀ h)).trans
    (comp_cancel_right _ _ _
      (pushforwardRingSheafCompInv_comp_hom B S hS e₀ (subspaceInclusion B S hS W W₀)
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))))

/-- **The transport inverts the lift.** Transporting the morphism attached to `g` on the
ambient site back to the site of `W₀` returns `g`, in the spelling
`AlgebraicGeometry.Space.restrictedSharpThroughThickening` has: the composite of the lift with
the comparison of iterated direct images, read across the adjunction. -/
theorem restrictedSharpThroughThickening_liftRestrictedSharpThroughThickening
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (g : structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) ⟶
      restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀) :
    ((ringImageAdjunction
          (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))).homEquiv
        (structureRingSheaf B S hS W)
        (restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀)).symm
      (liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g ≫
        pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))) = g := by
  refine (Equiv.symm_apply_eq _).2 ?_
  exact (comp_cancel_right _ _ _
    (pushforwardRingSheafCompHom_comp_inv B S hS e₀ (subspaceInclusion B S hS W W₀)
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)))).trans
    (ringImageAdjunction_homEquiv_apply _ _ _ g).symm

/-- **The lift is injective.** Two solutions of the lifting problem on the site of `W₀` with
the same morphism on the ambient site of `W` are equal: the adjunction is a bijection on
morphisms and the comparison of iterated direct images is invertible. -/
theorem liftRestrictedSharpThroughThickening_injective
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (g g' : structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) ⟶
      restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀)
    (hgg : liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g =
      liftRestrictedSharpThroughThickening B S hS Z W₀ e₀ g') :
    g = g' :=
  Function.LeftInverse.injective (g := fun m ↦ ((ringImageAdjunction
        (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀))).homEquiv
      (structureRingSheaf B S hS W)
      (restrictedThickeningLiftRingSheaf B S hS Z W₀ e₀)).symm
    (m ≫ pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))))
    (restrictedSharpThroughThickening_liftRestrictedSharpThroughThickening B S hS Z W₀ e₀) hgg

end AlgebraicGeometry.Space

end
