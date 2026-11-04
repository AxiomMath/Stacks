module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.GraphKernelRestriction

/-!
# Invertibility of a morphism of quasi-coherent modules is detected on an affine open cover

A morphism of quasi-coherent modules on a scheme which is bijective on sections over an affine
open `W` is invertible after restriction to `W`, and hence a morphism bijective on sections over
the members of an affine open cover is invertible.

This is the shape in which the affine criterion is used: a local computation produces
bijectivity of the map on sections over one affine open at a time, and what is wanted is
invertibility of the morphism of sheaves.

## Main results

* `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_restrictFunctor_map_of_bijective_app`: over an
  affine open, bijectivity on sections gives invertibility of the restriction.
* `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_bijective_app_of_isOpenCover`: bijectivity
  on sections over the members of an affine open cover gives invertibility.

## Implementation notes

The two inputs are the affine criterion
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ`, which is stated for a
module on a spectrum, and the locality of invertibility
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`. The passage from an affine
open `W` of `X` to the spectrum `Spec Γ(X, W)` is restriction along
`AlgebraicGeometry.IsAffineOpen.isoSpec`, whose inverse is an open immersion; sections of a
restriction over an open are sections of the module over its image
(`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is the identity), so the global sections of
the twice-restricted morphism are the sections of the original over
`W.ι ''ᵁ hW.isoSpec.inv ''ᵁ ⊤`, which is `W`. That equality of opens is the only transport
needed, and it is applied to the *bijectivity statement* rather than to the morphism, which is
why no `eqToHom` appears.

Going back from `Spec Γ(X, W)` to `W` uses `AlgebraicGeometry.isIso_of_isIso_app` and
`AlgebraicGeometry.isIso_app_of_isIso` rather than a reflection property of restriction along an
isomorphism: every open of `W` is the image of an open of the spectrum, so sectionwise
invertibility transports directly.

This material belongs with
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ` in
`StacksFrontier/AlgebraicGeometry/AffineBaseChange/Basic.lean`, and is in a separate module only
because `AlgebraicGeometry.isIso_of_isIso_app` lives downstream of that file.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineBaseChange

/-- **Over an affine open, invertibility of a morphism of quasi-coherent modules is detected on
sections.** If `φ` is bijective on sections over an affine open `W`, then its restriction to `W`
is an isomorphism. -/
theorem isIso_restrictFunctor_map_of_bijective_app {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) {W : X.Opens} (hW : IsAffineOpen W)
    (h : Function.Bijective (φ.val.app (op W))) :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map φ) := by
  have : IsOpenImmersion hW.isoSpec.inv := IsOpenImmersion.of_isIso _
  set ψ := (Scheme.Modules.restrictFunctor W.ι).map φ
  set χ := (Scheme.Modules.restrictFunctor hW.isoSpec.inv).map ψ
  have htop : W.ι ''ᵁ (hW.isoSpec.inv ''ᵁ (⊤ : (Spec Γ(X, W)).Opens)) = W := by
    simp [Scheme.Hom.inv_image]
  have hχiso : IsIso χ := by
    refine isIso_of_isIso_moduleSpecΓ χ ?_
    refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
    have key : ∀ V : X.Opens, V = W → Function.Bijective (φ.val.app (op V)) := by
      intro V hV
      subst hV
      exact h
    exact key _ htop
  refine AlgebraicGeometry.isIso_of_isIso_app ψ fun V => ?_
  have hV : hW.isoSpec.inv ''ᵁ (hW.isoSpec.hom ''ᵁ V) = V := by
    rw [Scheme.Hom.inv_image, Scheme.Hom.preimage_image_eq]
  exact hV ▸ AlgebraicGeometry.isIso_app_of_isIso χ (hW.isoSpec.hom ''ᵁ V)

/-- **A morphism of quasi-coherent modules bijective on sections over the members of an affine
open cover is an isomorphism.** -/
theorem isIso_of_bijective_app_of_isOpenCover {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) {I : Type*} (W : I → X.Opens)
    (hcover : IsOpenCover W) (hW : ∀ i, IsAffineOpen (W i))
    (h : ∀ i, Function.Bijective (φ.val.app (op (W i)))) : IsIso φ :=
  isIso_of_isIso_restrict φ W hcover fun i =>
    isIso_restrictFunctor_map_of_bijective_app φ (hW i) (h i)

end Stacks.AlgebraicGeometry.AffineBaseChange

end
