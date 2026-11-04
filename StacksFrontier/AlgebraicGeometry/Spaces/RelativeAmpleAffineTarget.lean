module

public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOverScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Relative ampleness over an affine scheme

Let `f : X ⟶ V` be a morphism from an algebraic space to an affine scheme `V` of the site, and
let `L` be an invertible `𝒪_X`-module. Then `L` is ample relative to `f` in the sense of
Stacks 0D31 if and only if `X` is a scheme `U` and the restriction of `L` to `U` is ample in the
absolute sense of Stacks 01PS.

This combines Stacks 0D32, which reduces relative ampleness over a scheme to relative ampleness
of the restriction of `L` along the induced morphism of schemes `U ⟶ V`, with Stacks 01VK,
which identifies relative ampleness over an affine base with ampleness.

## Main results

* `AlgebraicGeometry.Space.isRelativelyAmple_iff_exists_isAmple_of_isAffine`: the equivalence.

## References

* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D32](https://stacks.math.columbia.edu/tag/0D32)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `V` be an affine scheme of the site, `f : X ⟶ V` a morphism from an algebraic space and
`L` an invertible `𝒪_X`-module. Then `L` is ample relative to `f` (Stacks 0D31) if and only if
`X` is a scheme `U`, through an isomorphism `h_U ≅ X`, on which the restriction of `L` is an
invertible and ample module (Stacks 01PS). -/
theorem isRelativelyAmple_iff_exists_isAmple_of_isAffine (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] {X : AlgebraicSpaces B S hS}
    (f : X ⟶ schemeSpace V) (L : Modules.{u, u} B S hS X.1 X.2)
    (hLinv : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).property L) :
    IsRelativelyAmple B S hS f L ↔
      ∃ (U : BigFppfOver B S hS) (eX : yoneda.obj U ≅ X.1)
        (_ : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
          (baseChangeModule B S hS L U eX.hom)),
        Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj U)
          (baseChangeModule B S hS L U eX.hom) := by
  rw [isRelativelyAmple_iff_exists_scheme f L hLinv V (Iso.refl _)]
  refine exists_congr fun U => exists_congr fun eX => exists_congr fun hL => ?_
  exact @Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ _ _ _ _ hL

end AlgebraicGeometry.Space

end
