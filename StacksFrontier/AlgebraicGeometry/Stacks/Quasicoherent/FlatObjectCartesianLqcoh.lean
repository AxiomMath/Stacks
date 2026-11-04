module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineFlatBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatObjectCartesian

/-!
# The pullback of `LQCoh^fbc` to the flat-fppf site is cartesian between affine objects

For `M` in `LQCoh^fbc(𝒪_𝒳)` on an algebraic stack `𝒳` (Stacks, Section 0GQG), the pullback
`g^{-1}M` to the flat-fppf site along the morphism of ringed topoi of **Stacks 0788** (2) is
cartesian along every arrow between objects over affine schemes: the comparison
`O(y) ⊗_{O(y')} M(y') ⟶ M(y)` is bijective for every arrow `y ⟶ y'` of flat objects over affine
schemes, flat or not.

This is the step GT of the proof of **Stacks 0779**: the step R2,
`AlgebraicGeometry.Stack.isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules`, gives the
bijectivity along flat arrows between affine objects, and
`AlgebraicGeometry.Stack.FlatFppf.isIso_restrictionBaseChange_modulePullback` extends it to all
arrows between flat objects.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.isIso_restrictionBaseChange_modulePullback_of_lqcohSheafFbc`

## References

* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

attribute [local instance] FlatFppf.isContinuous_inclusion' FlatFppf.isCocontinuous_inclusion'

/-- **The pullback of an object of `LQCoh^fbc(𝒪_𝒳)` to the flat-fppf site is cartesian along
every arrow between objects over affine schemes** (the step GT of the proof of **Stacks 0779**).
For `M` in `LQCoh^fbc(𝒪_𝒳)` and an arrow `f : y ⟶ y'` of the flat-fppf site of `𝒳` between
objects over affine schemes, the base-change comparison of `g^{-1}M` along `f` is an
isomorphism. -/
theorem FlatFppf.isIso_restrictionBaseChange_modulePullback_of_lqcohSheafFbc
    (M : fppfModules B S hS 𝒳) (hM : lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳 M)
    ⦃y y' : FlatFppf B S hS 𝒳⦄ (f : y ⟶ y')
    (hy : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y.obj))
    (hy' : IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj y'.obj)) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (subsiteStructureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology
        le_rfl (FlatFppf.objectProperty B S hS 𝒳)).obj)
      ((FlatFppf.modulePullback B S hS 𝒳).obj M).val f.op) :=
  FlatFppf.isIso_restrictionBaseChange_modulePullback B S hS M
    (isCartesianAlongFlatAffine_of_lqcohSheafFbcFppfModules B E h S hS M hM) f hy hy'

end AlgebraicGeometry.Stack

end
