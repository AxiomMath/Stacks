module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits

/-!
# Sections of a cartesian square of algebraic spaces (Stacks 02X2)

The fibre product of two algebraic spaces over a third is the fibre product of the underlying
presheaves (Stacks 02X2), so on the sections over a single object of the big fppf site it is the
set-theoretic fibre product. This file records the half of that statement which is a statement
about an arbitrary cartesian square rather than about the chosen fibre product: in a cartesian
square of algebraic spaces the two projections are **jointly injective on sections**, and a
compatible pair of sections is in their joint image.

## Main results

* `AlgebraicGeometry.Space.section_eq_of_isPullback`: two sections of the upper left corner of a
  cartesian square of algebraic spaces with the same image under both projections are equal.
* `AlgebraicGeometry.Space.exists_section_of_isPullback`: two sections of the two middle terms
  with the same image in the lower right corner are the images of a section of the upper left
  corner.

## Implementation notes

Both are the universal property of the square applied to the representable algebraic space of
the test object, which is an algebraic space by Stacks 025Z
(`AlgebraicGeometry.isAlgebraicSpace_yoneda`); the translation between sections over a test
object and morphisms out of its representable presheaf is `CategoryTheory.yonedaEquiv`. This is
the same device as in `AlgebraicGeometry.Space.exists_point_of_isPullback`, which makes the
corresponding statement about field-valued points rather than about sections.

The square is one in the category `AlgebraicGeometry.AlgebraicSpaces` of Stacks 02X2, not one of
presheaves: that is the form in which the cartesian squares of a base change of a groupoid in
algebraic spaces (Stacks 0DTA) are recorded.

## References

* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The representable presheaf of an object of the big fppf site, as an algebraic space
(Stacks 025Z). -/
noncomputable abbrev yonedaSpace (T : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩

/-- Sections with the same image under two morphisms give equal composites out of the
representable algebraic space of the test object. -/
private theorem yonedaSpace_homMk_comp_eq {A A' C : AlgebraicSpaces B S hS} (u : A ⟶ C)
    (v : A' ⟶ C) {T : BigFppfOver B S hS} (a : A.1.obj (op T)) (a' : A'.1.obj (op T))
    (h : u.hom.app (op T) a = v.hom.app (op T) a') :
    (ObjectProperty.homMk (yonedaEquiv.symm a : yoneda.obj T ⟶ A.1) : yonedaSpace B S hS T ⟶ A)
        ≫ u
      = (ObjectProperty.homMk (yonedaEquiv.symm a' : yoneda.obj T ⟶ A'.1) :
        yonedaSpace B S hS T ⟶ A') ≫ v := by
  refine ObjectProperty.hom_ext _ ?_
  change (yonedaEquiv.symm a : yoneda.obj T ⟶ A.1) ≫ u.hom
      = (yonedaEquiv.symm a' : yoneda.obj T ⟶ A'.1) ≫ v.hom
  refine (yonedaEquiv (X := T) (F := C.1)).injective ?_
  rwa [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- A morphism `k` out of the representable algebraic space of `T` whose composite with `u` is
the one given by a section `z` satisfies `u (yonedaEquiv k) = z`. -/
private theorem app_yonedaEquiv_of_comp_eq {A C : AlgebraicSpaces B S hS} (u : A ⟶ C)
    {T : BigFppfOver B S hS} (z : C.1.obj (op T)) (k : yonedaSpace B S hS T ⟶ A)
    (hk : k ≫ u = (ObjectProperty.homMk (yonedaEquiv.symm z : yoneda.obj T ⟶ C.1) :
      yonedaSpace B S hS T ⟶ C)) :
    u.hom.app (op T) (yonedaEquiv k.hom) = z := by
  have hl : k.hom ≫ u.hom = (yonedaEquiv.symm z : yoneda.obj T ⟶ C.1) := congrArg (·.hom) hk
  have hy := congrArg (yonedaEquiv (X := T) (F := C.1)) hl
  rwa [yonedaEquiv_comp, Equiv.apply_symm_apply] at hy

/-- **The two projections of a cartesian square of algebraic spaces are jointly injective on
sections.** Sections over a test object are morphisms out of its representable algebraic space,
and the universal property of the square identifies two such morphisms that agree after both
projections. -/
theorem section_eq_of_isPullback {W Z X Y : AlgebraicSpaces B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    {T : BigFppfOver B S hS} (a b : W.1.obj (op T))
    (hp : p.hom.app (op T) a = p.hom.app (op T) b)
    (hq : q.hom.app (op T) a = q.hom.app (op T) b) :
    a = b :=
  yonedaEquiv.symm.injective
    (congrArg (fun k : yonedaSpace B S hS T ⟶ W => k.hom)
      (sq.hom_ext (yonedaSpace_homMk_comp_eq B S hS p p a b hp)
        (yonedaSpace_homMk_comp_eq B S hS q q a b hq)))

/-- **A compatible pair of sections of a cartesian square of algebraic spaces comes from a
section of its upper left corner.** This is surjectivity of
`(Z ×_Y X)(T) ⟶ Z(T) ×_{Y(T)} X(T)`, the universal property of the square applied to the
representable algebraic space of `T`. -/
theorem exists_section_of_isPullback {W Z X Y : AlgebraicSpaces B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    {T : BigFppfOver B S hS} (z : Z.1.obj (op T)) (x : X.1.obj (op T))
    (h : g.hom.app (op T) z = f.hom.app (op T) x) :
    ∃ a : W.1.obj (op T), p.hom.app (op T) a = z ∧ q.hom.app (op T) a = x :=
  have hcompat := yonedaSpace_homMk_comp_eq B S hS g f z x h
  ⟨yonedaEquiv (sq.lift _ _ hcompat).hom,
    app_yonedaEquiv_of_comp_eq B S hS p z _ (sq.lift_fst _ _ hcompat),
    app_yonedaEquiv_of_comp_eq B S hS q x _ (sq.lift_snd _ _ hcompat)⟩

end AlgebraicGeometry.Space

end
