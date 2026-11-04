module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic

/-!
# Quasi-affine morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is *quasi-affine* when its base change
along every morphism from an affine scheme to the target is represented by a quasi-affine
scheme.

## Main definitions

* `AlgebraicGeometry.Space.IsQuasiAffineHom` is quasi-affineness of a morphism of
  algebraic spaces.

## Implementation notes

Algebraic spaces over `S` are presheaves on the big fppf site over `S` and their morphisms
are natural transformations, so the fibre product of the source definition is the
categorical pullback taken in the presheaf category. A representing quasi-affine scheme is
an object of the site whose Yoneda presheaf is isomorphic to that pullback.

The test objects are those of the big affine fppf site, while the representing object is
only required to lie in the ambient site: a quasi-affine scheme need not be affine. The
predicate is stated for morphisms of presheaves.

## References

* [Stacks Project, Tag 03WL](https://stacks.math.columbia.edu/tag/03WL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- A morphism of algebraic spaces is quasi-affine if each of its base changes to an affine scheme
is represented by a quasi-affine scheme. -/
@[stacks 03WL]
abbrev IsQuasiAffineHom (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Prop :=
  ∀ (Z : BigAffineFppf B S hS)
    (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ Y),
    ∃ W : BigFppfOver B S hS,
      Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
        Nonempty (yoneda.obj W ≅ pullback g f)

end AlgebraicGeometry.Space

end
