module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Yoneda
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Representing a functor on schemes over a base by an object over that base

The representability theorems of the Stacks Project's chapter on flatness all have the shape
"the functor `F` on schemes over `S` is represented by a morphism `Z ⟶ S` with property `P`"
(Tags 05PF, 05UC, 05UE, 05UG, …), where `F` is *subterminal*: its value at a scheme `T` over
`S` is a proposition, namely that some condition holds after base change to `T`. Two pieces of
glue are common to all of them, and are proved here once:

* a representing object is unique up to isomorphism in `Over S`, so a property of morphisms
  stable under isomorphism holds for *every* representing morphism as soon as it holds for one;
* a subterminal functor is represented by a *monomorphism* into `S`, which is why these
  theorems can assert that their representing morphism is a monomorphism without any extra
  argument.

## Main results

* `Stacks.Flatness.representableByIso` is the isomorphism in `Over S` between two objects
  representing the same functor. This is `CategoryTheory.Functor.RepresentableBy.uniqueUpToIso`
  with no constraint tying the universe of the functor's values to the universe of the
  morphisms of `Over S`; see the implementation notes.
* `Stacks.Flatness.of_representableBy` transports a property of morphisms that is stable under
  isomorphism from one representing morphism to another.
* `Stacks.Flatness.mono_hom_of_representableBy` shows that an object representing a subterminal
  functor has monomorphic structure morphism, and
  `Stacks.Flatness.quasiSeparated_hom_of_representableBy` draws the consequence that its
  structure morphism is quasi-separated.
* `Stacks.Flatness.exists_isIso_comp_hom_of_representableBy` is the isomorphism of the previous
  item read as a factorization of one representing morphism through the other, and
  `Stacks.Flatness.locallyOfFinitePresentation_hom_of_representableBy` and
  `Stacks.Flatness.quasiCompact_hom_of_representableBy` are the transports along it of local
  finite presentation and of quasi-compactness.

## Implementation notes

Mathlib's `CategoryTheory.Functor.RepresentableBy.uniqueUpToIso` goes through
`CategoryTheory.Yoneda.ext`, which forces the functor to take values in the universe of the
morphisms of the ambient category. The functors of the flatness chapter are built from `PLift`
of a proposition and so take values in `Type 0`, while the morphisms of `Over S` for
`S : Scheme.{u}` live in `Type u`. `Stacks.Flatness.representableByIso` therefore rebuilds the
isomorphism directly out of the two bijections, which needs no such constraint: the two
mutually inverse morphisms are the ones corresponding to the identities, and the composites are
identified by applying the injectivity of a bijection to the compatibility of the bijections
with composition.

Being subterminal is expressed as a `Subsingleton` instance on every value of the functor; for
the functors of the flatness chapter, whose values are `PLift` of a proposition, it is found by
instance resolution.

Local finite presentation and quasi-compactness get their own transport lemmas instead of being
read off `Stacks.Flatness.of_representableBy`, because
`MorphismProperty.RespectsIso @AlgebraicGeometry.LocallyOfFinitePresentation` and
`MorphismProperty.RespectsIso @AlgebraicGeometry.QuasiCompact` are not synthesizable on this
Mathlib revision: the instances derived from `AlgebraicGeometry.HasAffineProperty` leave their
second argument undetermined. Both properties are nonetheless stable under composition with an
isomorphism, which is what the two lemmas use.

## References

* [Stacks Project, Tag 05PF](https://stacks.math.columbia.edu/tag/05PF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe v u

namespace Stacks.Flatness

variable {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type v} {Y Y' : C}

/-- Two objects representing the same functor are isomorphic.

This is `CategoryTheory.Functor.RepresentableBy.uniqueUpToIso` without the constraint that the
functor take values in the universe of the morphisms of `C`; see the implementation notes of
this file. -/
@[ega "0 8.1.8" "partial"]
def representableByIso (e : F.RepresentableBy Y) (e' : F.RepresentableBy Y') : Y ≅ Y' where
  hom := e'.homEquiv.symm (e.homEquiv (𝟙 Y))
  inv := e.homEquiv.symm (e'.homEquiv (𝟙 Y'))
  hom_inv_id := e.homEquiv.injective <| by
    rw [e.homEquiv_comp, Equiv.apply_symm_apply, ← e'.homEquiv_comp, Category.comp_id,
      Equiv.apply_symm_apply]
  inv_hom_id := e'.homEquiv.injective <| by
    rw [e'.homEquiv_comp, Equiv.apply_symm_apply, ← e.homEquiv_comp, Category.comp_id,
      Equiv.apply_symm_apply]

variable {S : Scheme.{u}} {G : (Over S)ᵒᵖ ⥤ Type v} {W W' : Over S}

/-- A property of morphisms of schemes stable under isomorphism holds for every morphism
representing a given functor on schemes over `S` as soon as it holds for one of them. -/
theorem of_representableBy (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (e : G.RepresentableBy W) (e' : G.RepresentableBy W') (h : P W.hom) : P W'.hom := by
  have hw : (representableByIso e e').hom.left ≫ W'.hom = W.hom :=
    Over.w (representableByIso e e').hom
  have : IsIso ((representableByIso e e').hom.left) :=
    ((Over.forget S).mapIso (representableByIso e e')).isIso_hom
  rwa [← hw, P.cancel_left_of_respectsIso] at h

/-- An object representing a subterminal functor on schemes over `S` has monomorphic structure
morphism: two morphisms into it agreeing after composition with the structure morphism are
morphisms over `S` from one and the same object, hence equal. -/
theorem mono_hom_of_representableBy [∀ T, Subsingleton (G.obj T)]
    (e : G.RepresentableBy W) : Mono W.hom where
  right_cancellation {Z} a b hab := by
    have := congrArg CommaMorphism.left (e.homEquiv (X := Over.mk (a ≫ W.hom)).injective
      (Subsingleton.elim (e.homEquiv (Over.homMk a rfl)) (e.homEquiv (Over.homMk b hab.symm))))
    simpa using this

/-- An object representing a subterminal functor on schemes over `S` has quasi-separated
structure morphism, since its structure morphism is a monomorphism and a monomorphism of schemes
is quasi-separated. -/
theorem quasiSeparated_hom_of_representableBy [∀ T, Subsingleton (G.obj T)]
    (e : G.RepresentableBy W) : QuasiSeparated W.hom := by
  have := mono_hom_of_representableBy e
  infer_instance

/-- The structure morphism of one object representing a functor on schemes over `S` factors the
structure morphism of any other through an isomorphism, namely through the component on the
sources of the isomorphism between the two representing objects. -/
theorem exists_isIso_comp_hom_of_representableBy (e : G.RepresentableBy W)
    (e' : G.RepresentableBy W') :
    ∃ u : W'.left ⟶ W.left, IsIso u ∧ u ≫ W.hom = W'.hom := by
  refine ⟨(representableByIso e e').inv.left, ?_, Over.w _⟩
  exact ((Over.forget S).mapIso (representableByIso e e')).isIso_inv

/-- Local finite presentation of a morphism representing a given functor on schemes over `S`
does not depend on the choice of representing object. -/
theorem locallyOfFinitePresentation_hom_of_representableBy (e : G.RepresentableBy W)
    (e' : G.RepresentableBy W') (h : LocallyOfFinitePresentation W.hom) :
    LocallyOfFinitePresentation W'.hom := by
  obtain ⟨u, hu, hw⟩ := exists_isIso_comp_hom_of_representableBy e e'
  rw [← hw]
  have := hu
  have := h
  infer_instance

/-- Quasi-compactness of a morphism representing a given functor on schemes over `S` does not
depend on the choice of representing object. -/
theorem quasiCompact_hom_of_representableBy (e : G.RepresentableBy W)
    (e' : G.RepresentableBy W') (h : QuasiCompact W.hom) : QuasiCompact W'.hom := by
  obtain ⟨u, hu, hw⟩ := exists_isIso_comp_hom_of_representableBy e e'
  rw [← hw]
  have := hu
  have := h
  infer_instance

end Stacks.Flatness

end
