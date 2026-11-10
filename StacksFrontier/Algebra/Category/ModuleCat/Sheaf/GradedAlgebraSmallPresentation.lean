module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPieceTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom

/-!
# The small presentation of a sheaf of graded algebras

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of `ℤ`-graded `R`-algebras whose
homogeneous sections are `w`-small, in the sense of `Small.{w}`. This file constructs a sheaf of
graded `R`-algebras whose homogeneous pieces have sections in the universe `w`, together with a
degreewise, sectionwise identification of it with `A`.

## Main definitions

* `SheafOfModules.GradedAlgebra.PieceEquiv`: a degreewise, sectionwise, natural linear
  identification of a family `p` of sheaves of modules, in an arbitrary module universe, with
  the homogeneous pieces of a graded algebra `A`.
* `SheafOfModules.GradedAlgebra.ofPieceEquiv`: the graded algebra transported along such an
  identification, with pieces the family `p`.
* `SheafOfModules.GradedAlgebra.smallPresentation`: the small presentation of `A`, a
  `SheafOfModules.GradedAlgebra.{t, w} R` whose pieces are identified with those of `A`.

## Main results

* `SheafOfModules.GradedAlgebra.smallPresentationEquiv`: the comparison, a `PieceEquiv`
  identifying the pieces of the small presentation with those of `A` sectionwise.
* `SheafOfModules.GradedAlgebra.smallPresentation_equiv_mul_app` and
  `SheafOfModules.GradedAlgebra.smallPresentation_equiv_one_eval`: the comparison carries the
  multiplication and the unit of the small presentation to those of `A`.
* `SheafOfModules.GradedAlgebra.smallPresentationPieceIso`: after raising both module universes
  to `max a w`, the comparison is an isomorphism of sheaves of modules in each degree.

## Implementation notes

The size hypothesis is the instance argument `∀ n U, Small.{w} ((A.piece n).val.obj U)`.

A morphism of sheaves of modules has its source and target in one module universe, so a
transport along isomorphisms `p n ≅ A.piece n`, as in `SheafOfModules.GradedAlgebra.ofPieceIso`,
cannot change the module universe. `PieceEquiv` instead records a family of `R(U)`-linear
bijections of sections, natural in `U`, which may relate different module universes.

For the same reason the comparison is not a morphism in the sense of
`SheafOfModules.GradedAlgebra.Hom` or `SheafOfModules.GradedAlgebra.UnitalHom`, which relate
graded algebras with the same module universe.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 000H](https://stacks.math.columbia.edu/tag/000H)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t a b w v u

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### Transport of a graded algebra along a sectionwise identification of its pieces -/

/-- A degreewise identification of a family `p` of sheaves of modules with the homogeneous
pieces of a sheaf of graded algebras `A`, given on local sections: an `R(U)`-linear bijection
in each degree over each object of the site, compatible with restriction. The module universe
of `p` is unrelated to that of `A`. -/
structure PieceEquiv (A : GradedAlgebra.{t, a} R) (p : ℤ → SheafOfModules.{b} R) where
  /-- The identification of the sections in degree `n` over `U`. -/
  equiv (n : ℤ) (U : Cᵒᵖ) : (p n).val.obj U ≃ₗ[R.obj.obj U] (A.piece n).val.obj U
  /-- The identifications commute with restriction. -/
  naturality (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (x : (p n).val.obj U) :
    equiv n V ((p n).val.map f x) = (A.piece n).val.map f (equiv n U x)

namespace PieceEquiv

variable {A : GradedAlgebra.{t, a} R} {p : ℤ → SheafOfModules.{b} R} (e : PieceEquiv A p)

/-- The inverse identifications commute with restriction. -/
theorem map_symm (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (z : (A.piece n).val.obj U) :
    (p n).val.map f ((e.equiv n U).symm z) = (e.equiv n V).symm ((A.piece n).val.map f z) := by
  have h := e.naturality n f ((e.equiv n U).symm z)
  rw [LinearEquiv.apply_symm_apply] at h
  exact (e.equiv n V).eq_symm_apply.mpr h

/-- The inverse identifications carry an `HEq` between sections of two pieces of `A` in equal
degrees to an `HEq` between the corresponding sections of `p`. -/
theorem heq_symm (U : Cᵒᵖ) {i j : ℤ} (hij : i = j) {x : (A.piece i).val.obj U}
    {y : (A.piece j).val.obj U} (h : HEq x y) :
    HEq ((e.equiv i U).symm x) ((e.equiv j U).symm y) := by
  subst hij
  rw [eq_of_heq h]

/-- The multiplication of `A` in degrees `(i, j)`, conjugated onto the sections of `p` over an
object of the site. -/
def mulApp (i j : ℤ) (U : Cᵒᵖ) :
    (p i).val.obj U →+ (p j).val.obj U →+ (p (i + j)).val.obj U :=
  AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk'
      (fun y => (e.equiv (i + j) U).symm ((A.mul i j).app U (e.equiv i U x) (e.equiv j U y)))
      (fun y₁ y₂ => by simp))
    (fun x₁ x₂ => by ext y; simp)

/-- The conjugated multiplication `e.mulApp i j U x y` is the inverse identification applied to
the product in `A` of the images of `x` and `y`. -/
@[simp]
theorem mulApp_apply (i j : ℤ) (U : Cᵒᵖ) (x : (p i).val.obj U) (y : (p j).val.obj U) :
    e.mulApp i j U x y =
      (e.equiv (i + j) U).symm ((A.mul i j).app U (e.equiv i U x) (e.equiv j U y)) :=
  rfl

/-- The conjugated multiplication commutes with restriction. -/
theorem mulApp_naturality (i j : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (x : (p i).val.obj U)
    (y : (p j).val.obj U) :
    (p (i + j)).val.map f (e.mulApp i j U x y) =
      e.mulApp i j V ((p i).val.map f x) ((p j).val.map f y) := by
  change (p (i + j)).val.map f
        ((e.equiv (i + j) U).symm ((A.mul i j).app U (e.equiv i U x) (e.equiv j U y))) =
      (e.equiv (i + j) V).symm ((A.mul i j).app V (e.equiv i V ((p i).val.map f x))
        (e.equiv j V ((p j).val.map f y)))
  rw [e.map_symm, Stacks.BilinearMap.naturality, e.naturality, e.naturality]

/-- The multiplication of `A`, conjugated onto `p`. -/
def mul (i j : ℤ) : BilinearMap (p i) (p j) (p (i + j)) where
  app U := e.mulApp i j U
  map_smul_left U r x y := by
    simp only [mulApp_apply, _root_.map_smul, Stacks.BilinearMap.map_smul_left]
  map_smul_right U r x y := by
    simp only [mulApp_apply, _root_.map_smul, Stacks.BilinearMap.map_smul_right]
  naturality f x y := e.mulApp_naturality _ _ f x y

/-- The conjugated multiplication `e.mul i j` over `U` is the inverse identification applied to
the product in `A` of the images of `x` and `y`. -/
@[simp]
theorem mul_app (i j : ℤ) (U : Cᵒᵖ) (x : (p i).val.obj U) (y : (p j).val.obj U) :
    (e.mul i j).app U x y =
      (e.equiv (i + j) U).symm ((A.mul i j).app U (e.equiv i U x) (e.equiv j U y)) :=
  rfl

/-- The unit of `A`, carried to a global section of `p 0`. -/
def one : (p 0).sections :=
  PresheafOfModules.sectionsMk (fun U => (e.equiv 0 U).symm (A.one.eval U))
    (fun {_ _} f => by
      rw [e.map_symm]
      exact congrArg (e.equiv 0 _).symm (PresheafOfModules.sections_property A.one f))

/-- The section `e.one` over `U` is the inverse identification applied to the unit of `A`. -/
@[simp]
theorem one_eval (U : Cᵒᵖ) : e.one.eval U = (e.equiv 0 U).symm (A.one.eval U) :=
  rfl

end PieceEquiv

/-- The sheaf of graded algebras transported along a sectionwise identification `e` of its
pieces with a family `p`: the pieces are `p`, and the multiplication and the unit are those of
`A` conjugated through `e`. -/
def ofPieceEquiv {A : GradedAlgebra.{t, a} R} {p : ℤ → SheafOfModules.{b} R}
    (e : PieceEquiv A p) : GradedAlgebra.{t, b} R where
  piece := p
  mul := e.mul
  one := e.one
  mul_assoc i j k U x y z := by
    simp only [PieceEquiv.mul_app, LinearEquiv.apply_symm_apply]
    exact e.heq_symm U (add_assoc i j k) (A.mul_assoc i j k U _ _ _)
  one_mul i U x := by
    simp only [PieceEquiv.mul_app, PieceEquiv.one_eval, LinearEquiv.apply_symm_apply]
    exact (e.heq_symm U (zero_add i) (A.one_mul i U (e.equiv i U x))).trans
      (heq_of_eq ((e.equiv i U).symm_apply_apply x))
  mul_one i U x := by
    simp only [PieceEquiv.mul_app, PieceEquiv.one_eval, LinearEquiv.apply_symm_apply]
    exact (e.heq_symm U (add_zero i) (A.mul_one i U (e.equiv i U x))).trans
      (heq_of_eq ((e.equiv i U).symm_apply_apply x))

/-- The degree-`n` piece of `ofPieceEquiv e` is `p n`. -/
theorem ofPieceEquiv_piece {A : GradedAlgebra.{t, a} R} {p : ℤ → SheafOfModules.{b} R}
    (e : PieceEquiv A p) (n : ℤ) : (ofPieceEquiv e).piece n = p n :=
  rfl

/-- The multiplication of the transport, read through the identification: the identification is
multiplicative. -/
theorem ofPieceEquiv_equiv_mul_app {A : GradedAlgebra.{t, a} R}
    {p : ℤ → SheafOfModules.{b} R} (e : PieceEquiv A p) (i j : ℤ) (U : Cᵒᵖ)
    (x : (p i).val.obj U) (y : (p j).val.obj U) :
    e.equiv (i + j) U (((ofPieceEquiv e).mul i j).app U x y) =
      (A.mul i j).app U (e.equiv i U x) (e.equiv j U y) :=
  (e.equiv (i + j) U).apply_symm_apply _

/-- The unit of the transport, read through the identification: the identification is
unital. -/
theorem ofPieceEquiv_equiv_one_eval {A : GradedAlgebra.{t, a} R}
    {p : ℤ → SheafOfModules.{b} R} (e : PieceEquiv A p) (U : Cᵒᵖ) :
    e.equiv 0 U ((ofPieceEquiv e).one.eval U) = A.one.eval U :=
  (e.equiv 0 U).apply_symm_apply _

/-- The multiplication of the transport, read through the inverse identification: the inverse
identification is multiplicative. -/
theorem ofPieceEquiv_symm_mul_app {A : GradedAlgebra.{t, a} R}
    {p : ℤ → SheafOfModules.{b} R} (e : PieceEquiv A p) (i j : ℤ) (U : Cᵒᵖ)
    (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) :
    ((ofPieceEquiv e).mul i j).app U ((e.equiv i U).symm x) ((e.equiv j U).symm y) =
      (e.equiv (i + j) U).symm ((A.mul i j).app U x y) := by
  change (e.equiv (i + j) U).symm ((A.mul i j).app U (e.equiv i U ((e.equiv i U).symm x))
      (e.equiv j U ((e.equiv j U).symm y))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The unit of the transport is the image of the unit of `A` under the inverse
identification. -/
theorem ofPieceEquiv_symm_one_eval {A : GradedAlgebra.{t, a} R}
    {p : ℤ → SheafOfModules.{b} R} (e : PieceEquiv A p) (U : Cᵒᵖ) :
    (ofPieceEquiv e).one.eval U = (e.equiv 0 U).symm (A.one.eval U) :=
  rfl

/-! ### The small presentation of a sheaf of graded algebras -/

section Small

/-- Raising the universe of the sections of a sheaf of modules keeps them `w`-small. -/
instance small_moduleULift_obj (M : SheafOfModules.{a} R) (U : Cᵒᵖ)
    [Small.{w} (M.val.obj U)] :
    Small.{w} (((Stacks.SheafOfModules.moduleULift.{w} R).obj M).val.obj U) :=
  inferInstanceAs (Small.{w} (ULift.{w} (M.val.obj U)))

variable (A : GradedAlgebra.{t, a} R)
  [∀ (n : ℤ) (U : Cᵒᵖ), Small.{w} ((A.piece n).val.obj U)]

/-- The degree-`n` homogeneous piece of `A` with its sections raised to the universe
`max a w`. -/
abbrev piecePreShrink (n : ℤ) : SheafOfModules.{max a w} R :=
  (Stacks.SheafOfModules.moduleULift.{w} R).obj (A.piece n)

/-- The sections of the lifted piece, identified with the sections of `A.piece n` by
`ULift.down`. -/
def piecePreShrinkEquiv (n : ℤ) (U : Cᵒᵖ) :
    (piecePreShrink A n).val.obj U ≃ₗ[R.obj.obj U] (A.piece n).val.obj U :=
  ULift.moduleEquiv (R := R.obj.obj U) (M := (A.piece n).val.obj U)

/-- The degree-`n` homogeneous piece of the small presentation of `A`, whose sections lie in the
universe `w`. -/
abbrev smallPiece (n : ℤ) : SheafOfModules.{w} R :=
  Stacks.SheafOfModules.sheafShrink.{w, a} R (piecePreShrink A n)

/-- The sections of the small presentation, identified with those of `A`: the inverse of the
shrink followed by the inverse of the universe lift. -/
def smallPieceEquiv (n : ℤ) (U : Cᵒᵖ) :
    (smallPiece A n).val.obj U ≃ₗ[R.obj.obj U] (A.piece n).val.obj U :=
  (Shrink.linearEquiv (R.obj.obj U) ((piecePreShrink A n).val.obj U)).trans
    (piecePreShrinkEquiv A n U)

/-- The identification of the sections of the small presentation with those of `A` commutes
with restriction. -/
theorem smallPieceEquiv_naturality (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (smallPiece A n).val.obj U) :
    smallPieceEquiv A n V ((smallPiece A n).val.map f x) =
      (A.piece n).val.map f (smallPieceEquiv A n U x) :=
  congrArg (piecePreShrinkEquiv A n V)
    (Stacks.shrinkPresheaf_map_apply (piecePreShrink A n).val.presheaf f x)

/-- The comparison between the small presentation of `A` and `A` itself: a degreewise,
sectionwise, natural `R(U)`-linear identification of the pieces. -/
def smallPresentationEquiv : PieceEquiv A (smallPiece A) where
  equiv := smallPieceEquiv A
  naturality := smallPieceEquiv_naturality A

/-- The small presentation of a sheaf of graded `R`-algebras `A` whose homogeneous sections over
every object of the site are `w`-small: the sheaf of graded `R`-algebras with pieces
`smallPiece A`, whose sections lie in the universe `w`, and with multiplication and unit those of
`A` conjugated through `smallPresentationEquiv`. -/
def smallPresentation : GradedAlgebra.{t, w} R :=
  ofPieceEquiv (smallPresentationEquiv A)

/-- The degree-`n` piece of `smallPresentation A` is `smallPiece A n`. -/
theorem smallPresentation_piece (n : ℤ) :
    (smallPresentation A).piece n = smallPiece A n :=
  rfl

/-- The comparison is multiplicative: it carries the multiplication of the small presentation
to that of `A`. -/
theorem smallPresentation_equiv_mul_app (i j : ℤ) (U : Cᵒᵖ)
    (x : (smallPiece A i).val.obj U) (y : (smallPiece A j).val.obj U) :
    smallPieceEquiv A (i + j) U
        (((smallPresentation A).mul i j).app U x y) =
      (A.mul i j).app U (smallPieceEquiv A i U x)
        (smallPieceEquiv A j U y) :=
  ofPieceEquiv_equiv_mul_app (smallPresentationEquiv A) i j U x y

/-- The comparison is unital: it carries the unit of the small presentation to that of `A`. -/
theorem smallPresentation_equiv_one_eval (U : Cᵒᵖ) :
    smallPieceEquiv A 0 U ((smallPresentation A).one.eval U) =
      A.one.eval U :=
  ofPieceEquiv_equiv_one_eval (smallPresentationEquiv A) U

/-- The comparison in degree `n` as an isomorphism of sheaves of modules, after raising the
module universes of the degree-`n` pieces of the small presentation and of `A` to `max a w`. -/
def smallPresentationPieceIso (n : ℤ) :
    (Stacks.SheafOfModules.moduleULift.{a} R).obj ((smallPresentation A).piece n) ≅
      (Stacks.SheafOfModules.moduleULift.{w} R).obj (A.piece n) :=
  Stacks.SheafOfModules.sheafShrinkIso.{w, a} R (piecePreShrink A n)

end Small

end SheafOfModules.GradedAlgebra

end
