module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# Restricted representable categories over `𝒞_Λ`

A map `R ⟶ S` of complete local algebras induces, by precomposition, a morphism from the
restricted functor represented by `S` to the restricted functor represented by `R`. This file
constructs that morphism and the corresponding morphism of based categories, and defines when a
map exhibits its target as a formal power series ring over its source.

## Main definitions

* `Deformation.restrictedCoyonedaMap` is the natural transformation induced by
  precomposition.
* `Deformation.restrictedRepresentable` is the category of elements of a restricted
  representable functor, viewed as a based category over `𝒞_Λ`.
* `Deformation.restrictedRepresentableMap` is the morphism of based categories induced by a
  map of representing rings.
* `Deformation.IsPowerSeriesOver` says that a map exhibits its target as a formal power
  series ring in finitely many variables over its source.

## Implementation notes

The underlined functor of the source is represented as the category of elements of
`Deformation.restrictedCoyoneda`; its projection makes this a based category. The phrase "a
power series ring over `R`" is expressed by an `R`-algebra equivalence with
`MvPowerSeries (Fin n) R`, where the `R`-algebra structure on `S` is the given morphism.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Precomposition with a map `R → S` gives a natural transformation from the restricted
representable functor of `S` to that of `R`. -/
def restrictedCoyonedaMap
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    restrictedCoyoneda S ⟶ restrictedCoyoneda R where
  app A := TypeCat.ofHom fun g ↦
    { hom := g.hom.comp f.hom
      isLocal := by
        let _ : IsLocalHom f.hom.toRingHom := f.isLocal
        let _ : IsLocalHom g.hom.toRingHom := g.isLocal
        exact RingHom.isLocalHom_comp g.hom.toRingHom f.hom.toRingHom
      residue_comm := fun r ↦ (g.residue_comm (f.hom r)).trans (f.residue_comm r) }
  naturality _ _ q := by
    ext
    rfl

/-- The restriction of the functor represented by `R`, regarded as a category over the
category of Artinian local algebras. -/
def restrictedRepresentable
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    BasedCategory (ArtinianLocalAlgCat.{u, v, w} Λ k) :=
  BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda R))

/-- The morphism of restricted representable categories induced contravariantly by a
morphism of representing complete local algebras. -/
def restrictedRepresentableMap
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    BasedFunctor (restrictedRepresentable S) (restrictedRepresentable R) where
  toFunctor := CategoryOfElements.map (restrictedCoyonedaMap f)
  w := CategoryOfElements.map_π (restrictedCoyonedaMap f)

/-- A morphism `R → S` exhibits `S` as a power series ring over `R` if, for some finite
number of variables, `S` is isomorphic as an `R`-algebra to the corresponding multivariate
formal power series ring. -/
abbrev IsPowerSeriesOver
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) : Prop :=
  letI : Algebra R S := f.hom.toRingHom.toAlgebra
  ∃ n : ℕ, Nonempty (S ≃ₐ[R] MvPowerSeries (Fin n) R)

end Deformation

end
