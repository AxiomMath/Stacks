module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.InvertibleTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation

/-!
# The first Chern class of a tensor product of invertible modules, in the weak situation

The first Chern class of a tensor product of invertible modules is the sum of the first Chern
classes, stated for `Stacks.WeilCohomology.Weak.ChernSetup`: the standing situation of Stacks
Section 45.12 in which the projective bundle formula, condition (4), is only asked to be injective
and to resolve the top power `c₁^A(𝒪_P(1))^{r+1}` of the twist class (see
`StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation`, which explains why Tag
0FIE needs this generality).

## Main results

* `Stacks.WeilCohomology.Weak.c₁_picardClassOf_tensorObjRingedSpace`: `c₁^A` of the tensor product
  of two invertible modules is the sum of their first Chern classes.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v₁ w

namespace Stacks.WeilCohomology.Weak

/-- **The first Chern class of a tensor product of invertible modules is the sum of the first
Chern classes**, `c₁^A` being additive on `Pic(X)` and addition there being the tensor product. -/
theorem c₁_picardClassOf_tensorObjRingedSpace {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}
    (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C) (L N : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L)
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 N)
    (hLN : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 (Scheme.Modules.tensorObjRingedSpace (S.obj X) L N)) :
    𝔚.c₁ X (picardClassOf (S.obj X)
        (Scheme.Modules.tensorObjRingedSpace (S.obj X) L N) hLN) =
      𝔚.c₁ X (picardClassOf (S.obj X) L hL) + 𝔚.c₁ X (picardClassOf (S.obj X) N hN) := by
  rw [picardClassOf_tensorObjRingedSpace L N hL hN hLN, map_add]

end Stacks.WeilCohomology.Weak

end
