module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSmallPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedPushforward

/-!
# The small presentation of a sheaf of graded algebras is isomorphic to it

`SheafOfModules.GradedAlgebra.smallPresentation A` re-presents a sheaf of graded `R`-algebras
`A` with its homogeneous sections in a chosen universe `w`, under the hypothesis that those
sections are `w`-small.  The comparison with `A` is given there as sectionwise data: a
degreewise `R(U)`-linear bijection, natural in `U`, multiplicative and unital.  This file
packages that data as morphisms of sheaves of graded algebras, one in each direction, and
records that the two are mutually inverse.

## Which notion of morphism

The two algebras have their sections in the unrelated universes `w` and `a`, so
`SheafOfModules.GradedAlgebra.Hom` and `UnitalHom` are unavailable: their components are
morphisms of sheaves of modules, which live in one module universe.  The library's
cross-universe notion is `SheafOfModules.GradedAlgebra.SemilinearHom`, a homomorphism along a
morphism of ringed sites — given on local sections, so the two module universes are free.
Taking the morphism of ringed sites to be the identity, `SemilinearHom (𝟭 C) (𝟙 R.obj)` is a
homomorphism of sheaves of graded algebras over `R` on the site `C` which is allowed to change
the module universe, and that is what the comparison is.

## Main definitions

* `SheafOfModules.GradedAlgebra.smallPresentationEquivAt`: the comparison on sections, read at
  the pieces of `smallPresentation A` rather than at their unfolded form.
* `SheafOfModules.GradedAlgebra.smallPresentationHom`: **the comparison**, from the small
  presentation of `A` to `A`.
* `SheafOfModules.GradedAlgebra.smallPresentationSymmHom`: **its inverse**, from `A` to the
  small presentation.

## Main results

* `SheafOfModules.GradedAlgebra.smallPresentationSymmHom_app_smallPresentationHom_app` and
  `smallPresentationHom_app_smallPresentationSymmHom_app`: **the two homomorphisms are mutually
  inverse on local sections**, in every degree over every object of the site.  So the comparison
  is an isomorphism of sheaves of graded algebras over `R`, in the only sense in which a
  morphism between two graded algebras of different module universes can be written at all.
* `SheafOfModules.GradedAlgebra.smallPresentationEquivAt_naturality`,
  `smallPresentationEquivAt_mul_app`, `smallPresentationEquivAt_one_eval` and their three
  `symm` counterparts: the comparison and its inverse commute with restriction and carry the
  multiplication and the unit of each algebra to those of the other.

## What this does not give

`SemilinearHom` carries no identity, composition or inverse API in the library, so there is no
`smallPresentationHom ≫ smallPresentationSymmHom = id` to state; "mutually inverse" is the pair
of cancellation identities on local sections, which is the whole of its content here, both
homomorphisms being given by one `LinearEquiv` and its inverse in each degree over each object.

There is also no functor `GradedAlgebra.{t, a} R ⥤ GradedAlgebra.{t, w} R`: the construction is
defined only on the graded algebras whose sections satisfy the size hypothesis, which is not a
full subcategory of anything, there being no category containing graded algebras of both module
universes.

## Implementation notes

Every statement here is phrased with `smallPresentationEquivAt`, whose domain is spelled
`((smallPresentation A).piece n).val.obj U`, and never with
`SheafOfModules.GradedAlgebra.smallPieceEquiv`, whose domain is the same type spelled
`(smallPiece A n).val.obj U`.  The two spellings are definitionally equal and interchangeable
for terms, but they resolve the `AddGroup` and `Module` instances on the sections to different
instance *terms*.  A goal that mixes them is then not closed: `simp` fails to apply `map_add`
for `smallPieceEquiv` to a sum formed at the other spelling, and is left with a goal of the
shape `x + y = x + y` whose two additions it cannot identify — the definitional unfolding that
would identify them runs into `Shrink` and `equivShrink`, which are not `@[expose]`d, and stops.
Phrasing everything at the spelling that the type of a `SemilinearHom` out of or into
`smallPresentation A` actually uses keeps every proof in this file syntactic.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FR7](https://stacks.math.columbia.edu/tag/0FR7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t a w v u

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  (A : GradedAlgebra.{t, a} R) [∀ (n : ℤ) (U : Cᵒᵖ), Small.{w} ((A.piece n).val.obj U)]

/-- The comparison between the sections of the small presentation of `A` and those of `A`, read
at the pieces of `smallPresentation A`.  This is
`SheafOfModules.GradedAlgebra.smallPieceEquiv` with its domain spelled the way the type of a
`SemilinearHom` out of `smallPresentation A` spells it; see the implementation notes. -/
def smallPresentationEquivAt (n : ℤ) (U : Cᵒᵖ) :
    ((smallPresentation.{t, a, w} A).piece n).val.obj U ≃ₗ[R.obj.obj U]
      (A.piece n).val.obj U :=
  smallPieceEquiv.{t, a, w} A n U

/-- The comparison commutes with restriction. -/
theorem smallPresentationEquivAt_naturality (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : ((smallPresentation.{t, a, w} A).piece n).val.obj U) :
    smallPresentationEquivAt.{t, a, w} A n V
        (((smallPresentation.{t, a, w} A).piece n).val.map f x) =
      (A.piece n).val.map f (smallPresentationEquivAt.{t, a, w} A n U x) :=
  smallPieceEquiv_naturality.{t, a, w} A n f x

/-- The comparison is multiplicative. -/
theorem smallPresentationEquivAt_mul_app (i j : ℤ) (U : Cᵒᵖ)
    (x : ((smallPresentation.{t, a, w} A).piece i).val.obj U)
    (y : ((smallPresentation.{t, a, w} A).piece j).val.obj U) :
    smallPresentationEquivAt.{t, a, w} A (i + j) U
        (((smallPresentation.{t, a, w} A).mul i j).app U x y) =
      (A.mul i j).app U (smallPresentationEquivAt.{t, a, w} A i U x)
        (smallPresentationEquivAt.{t, a, w} A j U y) :=
  (smallPresentationEquivAt.{t, a, w} A (i + j) U).apply_symm_apply _

/-- The comparison is unital. -/
theorem smallPresentationEquivAt_one_eval (U : Cᵒᵖ) :
    smallPresentationEquivAt.{t, a, w} A 0 U ((smallPresentation.{t, a, w} A).one.eval U) =
      A.one.eval U :=
  (smallPresentationEquivAt.{t, a, w} A 0 U).apply_symm_apply _

/-- The inverse comparison is multiplicative. -/
theorem smallPresentationEquivAt_symm_mul_app (i j : ℤ) (U : Cᵒᵖ)
    (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) :
    ((smallPresentation.{t, a, w} A).mul i j).app U
        ((smallPresentationEquivAt.{t, a, w} A i U).symm x)
        ((smallPresentationEquivAt.{t, a, w} A j U).symm y) =
      (smallPresentationEquivAt.{t, a, w} A (i + j) U).symm ((A.mul i j).app U x y) :=
  ofPieceEquiv_symm_mul_app (smallPresentationEquiv.{t, a, w} A) i j U x y

/-- The unit of the small presentation is the image of the unit of `A` under the inverse
comparison. -/
theorem smallPresentationEquivAt_symm_one_eval (U : Cᵒᵖ) :
    (smallPresentation.{t, a, w} A).one.eval U =
      (smallPresentationEquivAt.{t, a, w} A 0 U).symm (A.one.eval U) :=
  rfl

/-- The inverse comparison commutes with restriction. -/
theorem smallPresentationEquivAt_symm_naturality (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (z : (A.piece n).val.obj U) :
    ((smallPresentation.{t, a, w} A).piece n).val.map f
        ((smallPresentationEquivAt.{t, a, w} A n U).symm z) =
      (smallPresentationEquivAt.{t, a, w} A n V).symm ((A.piece n).val.map f z) :=
  (smallPresentationEquiv.{t, a, w} A).map_symm n f z

/-- **The comparison from the small presentation of `A` to `A`**, as a homomorphism of sheaves
of graded algebras along the identity morphism of ringed sites.  On sections it undoes the
shrink and then the universe lift. -/
def smallPresentationHom :
    SemilinearHom (𝟭 C) (𝟙 R.obj) (smallPresentation.{t, a, w} A) A where
  app n U := AddMonoidHom.mk' (fun x => smallPresentationEquivAt.{t, a, w} A n U x)
    (fun x y => by simp)
  map_smul n U s x := map_smul (smallPresentationEquivAt.{t, a, w} A n U) s x
  naturality := by
    intro n U V f x
    exact smallPresentationEquivAt_naturality.{t, a, w} A n f x
  map_mul i j U x y := smallPresentationEquivAt_mul_app.{t, a, w} A i j U x y
  map_one U := smallPresentationEquivAt_one_eval.{t, a, w} A U

/-- On sections, `smallPresentationHom A` is the comparison `smallPresentationEquivAt A`. -/
@[simp]
theorem smallPresentationHom_app_apply (n : ℤ) (U : Cᵒᵖ)
    (x : ((smallPresentation.{t, a, w} A).piece n).val.obj U) :
    (smallPresentationHom.{t, a, w} A).app n U x =
      smallPresentationEquivAt.{t, a, w} A n U x :=
  rfl

/-- **The comparison from `A` to its small presentation.**  On sections it lifts the universe
and then shrinks. -/
def smallPresentationSymmHom :
    SemilinearHom (𝟭 C) (𝟙 R.obj) A (smallPresentation.{t, a, w} A) where
  app n U := AddMonoidHom.mk' (fun x => (smallPresentationEquivAt.{t, a, w} A n U).symm x)
    (fun x y => by simp)
  map_smul n U s x := map_smul (smallPresentationEquivAt.{t, a, w} A n U).symm s x
  naturality := by
    intro n U V f z
    exact (smallPresentationEquivAt_symm_naturality.{t, a, w} A n f z).symm
  map_mul i j U x y := (smallPresentationEquivAt_symm_mul_app.{t, a, w} A i j U x y).symm
  map_one U := (smallPresentationEquivAt_symm_one_eval.{t, a, w} A U).symm

/-- On sections, `smallPresentationSymmHom A` is the inverse of `smallPresentationEquivAt A`. -/
@[simp]
theorem smallPresentationSymmHom_app_apply (n : ℤ) (U : Cᵒᵖ) (x : (A.piece n).val.obj U) :
    (smallPresentationSymmHom.{t, a, w} A).app n U x =
      (smallPresentationEquivAt.{t, a, w} A n U).symm x :=
  rfl

/-- The comparison and its inverse cancel on the sections of the small presentation. -/
@[simp]
theorem smallPresentationSymmHom_app_smallPresentationHom_app (n : ℤ) (U : Cᵒᵖ)
    (x : ((smallPresentation.{t, a, w} A).piece n).val.obj U) :
    (smallPresentationSymmHom.{t, a, w} A).app n U
        ((smallPresentationHom.{t, a, w} A).app n U x) = x :=
  (smallPresentationEquivAt.{t, a, w} A n U).symm_apply_apply x

/-- The comparison and its inverse cancel on the sections of `A`. -/
@[simp]
theorem smallPresentationHom_app_smallPresentationSymmHom_app (n : ℤ) (U : Cᵒᵖ)
    (x : (A.piece n).val.obj U) :
    (smallPresentationHom.{t, a, w} A).app n U
        ((smallPresentationSymmHom.{t, a, w} A).app n U x) = x :=
  (smallPresentationEquivAt.{t, a, w} A n U).apply_symm_apply x

end SheafOfModules.GradedAlgebra

end
