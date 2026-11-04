module

public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SourceChernSetup

/-!
# The Picard class of a tensor product, at the spelling `K₀(Vect(X))` is built over

Tag 01CX says that addition in `Pic(X)` is the tensor product of invertible modules. This
repository carries several constructions of the tensor product of sheaves of modules, and the two
that meet here are the one the Grothendieck ring of Tag 0FDK multiplies with,
`AlgebraicGeometry.Scheme.Modules.tensorObjRingedSpace`, and the one Tag 01CX is stated over,
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf`. They agree by construction, so Tag
01CX transfers; this file records that transfer, so that the first Chern class of a product of
two classes of invertible modules in `K₀(Vect(X))` can be computed.

## Main results

* `Stacks.WeilCohomology.isInvertible_tensorObjRingedSpace`: the tensor product of two
  invertible modules is invertible, at the spelling `K₀(Vect(X))` is built over.
* `Stacks.WeilCohomology.picardClassOf_tensorObjRingedSpace`: **Tag 01CX at that spelling** —
  the class in `Pic(X)` of the tensor product is the sum of the classes.
* `Stacks.WeilCohomology.c₁_picardClassOf_tensorObjRingedSpace`: the first Chern class of a
  tensor product of invertible modules is the sum of the first Chern classes.

## Implementation notes

Invertibility appears in two spellings as well: `AlgebraicGeometry.SheafOfModules.IsInvertible`,
in which short exact sequences of module sheaves and hence the splitting principle are stated,
and `Stacks.SheafOfModules.IsInvertible`, from which `Pic(X)` is built. They are exchanged by
`Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`, which is what
`Stacks.WeilCohomology.picardClassOf` does; the statements below are in the first spelling,
which is the one their consumers have.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v₁ w

namespace Stacks.WeilCohomology

/-- **The tensor product of two invertible modules is invertible**, at the spelling of the tensor
product that `K₀(Vect(X))` multiplies with. This is Tag 01CT (1); the two tensor products agree
by construction. -/
theorem isInvertible_tensorObjRingedSpace {X : Scheme.{u}} (L N : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Scheme.Modules.tensorObjRingedSpace X L N) := by
  have key := Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    X.presheaf X.ringCatIsSheaf
  have := (key L).mpr hL
  have := (key N).mpr hN
  exact (key _).mp (Stacks.SheafOfModules.isInvertible_tensorSheaf X.presheaf X.ringCatIsSheaf L N)

/-- **Stacks Tag 01CX, addition in `Pic(X)` is the tensor product**, at the spelling of the
tensor product that `K₀(Vect(X))` multiplies with. -/
@[stacks 01CX "addition in `Pic(X)` is the tensor product, read at the spelling of the tensor \
  product that the Grothendieck ring of Tag 0FDK multiplies with"]
theorem picardClassOf_tensorObjRingedSpace {X : Scheme.{u}} (L N : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N)
    (hLN : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Scheme.Modules.tensorObjRingedSpace X L N)) :
    picardClassOf X (Scheme.Modules.tensorObjRingedSpace X L N) hLN =
      picardClassOf X L hL + picardClassOf X N hN :=
  (X.picardClass_tensorSheaf L N _ _ _).symm

/-- **The first Chern class of a tensor product of invertible modules is the sum of the first
Chern classes**, `c₁^A` being additive on `Pic(X)` and addition there being the tensor product.
This is the form in which Tag 0FI9's proof of multiplicativity reads the Chern roots of a tensor
product: they are the sums `x_j + y_{j'}`. -/
theorem c₁_picardClassOf_tensorObjRingedSpace {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}
    (𝔄 : ChernSetup.{u, v, v₁, w} C S) (X : C) (L N : (S.obj X).Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 L)
    (hN : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 N)
    (hLN : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj X).presheaf
      (S.obj X).ringCatSheaf.2 (Scheme.Modules.tensorObjRingedSpace (S.obj X) L N)) :
    𝔄.c₁ X (picardClassOf (S.obj X)
        (Scheme.Modules.tensorObjRingedSpace (S.obj X) L N) hLN) =
      𝔄.c₁ X (picardClassOf (S.obj X) L hL) + 𝔄.c₁ X (picardClassOf (S.obj X) N hN) := by
  rw [picardClassOf_tensorObjRingedSpace L N hL hN hLN, map_add]

/-- **The class in `Pic(X)` of the structure sheaf is zero**, it being the neutral element for
the tensor product. -/
theorem picardClassOf_unit {X : Scheme.{u}}
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (SheafOfModules.unit X.ringCatSheaf)) :
    picardClassOf X (SheafOfModules.unit X.ringCatSheaf) h = 0 :=
  Stacks.SheafOfModules.picardClass_zero X.presheaf X.ringCatIsSheaf

end Stacks.WeilCohomology

end
