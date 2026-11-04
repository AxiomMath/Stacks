module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraCounitEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The composition comparison for pullbacks of sheaves of graded algebras, at unrelated universes

This is `Stacks.Sheaves.GradedAlgebraPullbackComp` with the objects, the morphisms and the
sections of the structure sheaf of the ringed topos in three unrelated universes, so that it
applies to `AlgebraicGeometry.Space.smallEtaleRingedTopos`, a
`AlgebraicGeometry.RingedTopos.{u, u + 1, u}`. The hypotheses are the original ones together
with `CategoryTheory.EssentiallySmall.{w} Y.C` and `CategoryTheory.EssentiallySmall.{w} Z.C` on
the two sites the direct images are taken to.

## Main definitions

* `gradedPull`, `gradedPush` and `gradedAdj` name the two functors of sheaves of graded algebras
  attached to a morphism of ringed topoi and the adjunction between them.
* `gradedPullbackCompIso`: the multiplicative composition comparison, from a graded comparison
  of the direct images.

## Main results

* `map_mul_gradedPullbackCompIso`: the degreewise components of that comparison preserve
  products of homogeneous local sections.

## Implementation notes

The construction is the original one with the graded adjunction replaced by
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedAlgebraPullbackPushforwardAdjunction`;
nothing about the universes enters the argument, which is uniqueness of left adjoints.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.GradedAlgebraPullback
open Stacks.Sites.SheafSection
open scoped Stacks.Sites.SheafSection.OfEssentiallySmall

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe v u₁ w

variable {X Y Z : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} Y.C] [EssentiallySmall.{w} Z.C]

/-- The pullback of sheaves of graded algebras along a morphism of ringed topoi, as the left
adjoint it is: part (2) of Stacks 0FQX. -/
public noncomputable abbrev gradedPull (f : AlgebraicGeometry.RingedToposHom X Y) :
    SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (gradedAlgebraPullbackSpecification f.toRingedToposModulesHom).1

/-- The direct image of sheaves of graded algebras along a morphism of ringed topoi, as the
right adjoint produced by part (3) of Stacks 0FQX. Its values on objects are the direct-image
graded algebras of `Stacks.Sheaves.GradedAlgebraPushforward.pushforwardGradedAlgebra`. -/
public noncomputable abbrev gradedPush (f : AlgebraicGeometry.RingedToposHom X Y) :
    SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  (gradedAlgebraPullbackPushforwardAdjunction f).1

/-- Part (3) of Stacks 0FQX: the pullback of sheaves of graded algebras is left adjoint to the
direct image. -/
public noncomputable abbrev gradedAdj (f : AlgebraicGeometry.RingedToposHom X Y) :
    gradedPull f ⊣ gradedPush f :=
  (gradedAlgebraPullbackPushforwardAdjunction f).2.1

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The right adjoint has the direct-image graded algebras as its values on objects. -/
public theorem gradedPush_obj (f : AlgebraicGeometry.RingedToposHom X Y)
    (A : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (gradedPush f).obj A = pushforwardGradedAlgebra f A :=
  (gradedAlgebraPullbackPushforwardAdjunction f).2.2 A

/-- **The multiplicative composition comparison for pullbacks of sheaves of graded algebras.**
Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed topoi, let `h : X ⟶ Z` play the role of
their composite, and let `τ` identify the composite of the direct images of sheaves of graded
algebras with the direct image along `h`. Then the pullback along `h` of sheaves of graded
algebras is isomorphic to the pullback along `g` followed by the pullback along `f`, as functors
of sheaves of **graded algebras** — so the comparison is multiplicative in every degree, which
is what `Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso` leaves open.

Both sides are left adjoint to `g_* ∘ f_*`: the left-hand side by the adjunction of `h`
transported along `τ`, the right-hand side because adjunctions compose. So they agree by
uniqueness of left adjoints. -/
public noncomputable def gradedPullbackCompIso (f : AlgebraicGeometry.RingedToposHom X Y)
    (g : AlgebraicGeometry.RingedToposHom Y Z)
    (h : AlgebraicGeometry.RingedToposHom X Z)
    (τ : gradedPush f ⋙ gradedPush g ≅ gradedPush h) :
    gradedPull h ≅ gradedPull g ⋙ gradedPull f :=
  ((gradedAdj h).ofNatIsoRight τ.symm).leftAdjointUniq ((gradedAdj g).comp (gradedAdj f))

/-- **The composition comparison of `gradedPullbackCompIso` preserves products of homogeneous
local sections in every degree.** This is multiplicativity of the comparison, spelled out: it is
a field of a homomorphism of sheaves of graded algebras, so no computation is involved — the
point is that the comparison is a morphism in the category of sheaves of graded algebras in the
first place. -/
public theorem map_mul_gradedPullbackCompIso (f : AlgebraicGeometry.RingedToposHom X Y)
    (g : AlgebraicGeometry.RingedToposHom Y Z)
    (h : AlgebraicGeometry.RingedToposHom X Z)
    (τ : gradedPush f ⋙ gradedPush g ≅ gradedPush h)
    (B : SheafOfModules.GradedAlgebra.{w, w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (i j : ℤ) (U : X.Cᵒᵖ)
    (x : (((gradedPull h).obj B).piece i).val.obj U)
    (y : (((gradedPull h).obj B).piece j).val.obj U) :
    ((((gradedPullbackCompIso f g h τ).hom.app B).app (i + j)).val.app U)
        ((((gradedPull h).obj B).mul i j).app U x y) =
      ((((gradedPull g ⋙ gradedPull f).obj B).mul i j)).app U
        ((((gradedPullbackCompIso f g h τ).hom.app B).app i).val.app U x)
        ((((gradedPullbackCompIso f g h τ).hom.app B).app j).val.app U y) :=
  ((gradedPullbackCompIso f g h τ).hom.app B).map_mul i j U x y

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

end
