module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Homomorphisms of sheaves of differential graded algebras

Let `R` be a sheaf of rings on a site. A homomorphism of sheaves of differential graded
`R`-algebras is a morphism of their underlying cochain complexes of sheaves of modules which
respects the graded multiplication. Such homomorphisms have an evident identity and
composition, and the sheaves of differential graded algebras over a fixed `R` form a category.

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra.Hom` is a homomorphism of sheaves of differential
  graded algebras, and `SheafOfModules.DifferentialGradedAlgebra.instCategory` the category
  they form.

## Implementation notes

The sheaves of differential graded algebras themselves are
`SheafOfModules.DifferentialGradedAlgebra`, together with
`SheafOfModules.DifferentialGradedAlgebra.toGradedAlgebra`, which forgets the differential.

As in the source, a homomorphism is required to respect multiplication and no separate
unit-preservation axiom is imposed. The condition is stated on local sections, in the same
sectionwise form as the multiplication `SheafOfModules.BilinearMap` it constrains.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring and the algebra pieces are independent,
as for `SheafOfModules.DifferentialGradedAlgebra`; a ringed site `X` is the case
`R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
-/

@[expose] public section

open CategoryTheory

universe t a v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

namespace DifferentialGradedAlgebra

/-- A homomorphism of sheaves of differential graded algebras: a morphism of the underlying
cochain complexes which respects the graded multiplication. -/
@[stacks 0FRF "homomorphisms of differential graded algebras"]
structure Hom (A B : DifferentialGradedAlgebra.{t, a} R) where
  /-- The underlying morphism of cochain complexes. -/
  toHomologicalComplex : A.complex ⟶ B.complex
  /-- The underlying complex morphism respects graded multiplication. -/
  map_mul : ∀ (n m : ℤ) (U : Cᵒᵖ) (x : (A.complex.X n).val.obj U)
      (y : (A.complex.X m).val.obj U),
    (toHomologicalComplex.f (n + m)).val.app U ((A.mul n m).app U x y) =
      (B.mul n m).app U ((toHomologicalComplex.f n).val.app U x)
        ((toHomologicalComplex.f m).val.app U y)

/-- Homomorphisms of sheaves of differential graded algebras are determined by their maps in
every degree. -/
@[ext]
theorem Hom.ext {A B : DifferentialGradedAlgebra.{t, a} R} {f g : Hom A B}
    (h : ∀ n, f.toHomologicalComplex.f n = g.toHomologicalComplex.f n) : f = g := by
  cases f
  cases g
  congr 1
  exact HomologicalComplex.hom_ext _ _ h

/-- The identity homomorphism of a sheaf of differential graded algebras. -/
def Hom.id (A : DifferentialGradedAlgebra.{t, a} R) : Hom A A where
  toHomologicalComplex := 𝟙 A.complex
  map_mul _ _ _ _ _ := rfl

/-- Composition of homomorphisms of sheaves of differential graded algebras. -/
def Hom.comp {A B D : DifferentialGradedAlgebra.{t, a} R} (f : Hom A B) (g : Hom B D) :
    Hom A D where
  toHomologicalComplex := f.toHomologicalComplex ≫ g.toHomologicalComplex
  map_mul n m U x y := by
    change (g.toHomologicalComplex.f (n + m)).val.app U
      ((f.toHomologicalComplex.f (n + m)).val.app U ((A.mul n m).app U x y)) = _
    rw [f.map_mul, g.map_mul]
    rfl

/-- In every degree, the identity homomorphism is the identity morphism. -/
@[simp]
theorem Hom.id_f (A : DifferentialGradedAlgebra.{t, a} R) (n : ℤ) :
    (Hom.id A).toHomologicalComplex.f n = 𝟙 _ := rfl

/-- In every degree, the composite of two homomorphisms is the composite of their maps. -/
@[simp]
theorem Hom.comp_f {A B D : DifferentialGradedAlgebra.{t, a} R} (f : Hom A B) (g : Hom B D)
    (n : ℤ) : (f.comp g).toHomologicalComplex.f n =
      f.toHomologicalComplex.f n ≫ g.toHomologicalComplex.f n := rfl

/-- Sheaves of differential graded algebras over a fixed sheaf of rings form a category. -/
instance instCategory : Category (DifferentialGradedAlgebra.{t, a} R) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by ext n; simp
  comp_id f := by ext n; simp
  assoc f g h := by ext n; simp

/-- In every degree, the categorical identity morphism is the identity morphism. -/
@[simp]
theorem id_f (A : DifferentialGradedAlgebra.{t, a} R) (n : ℤ) :
    (𝟙 A : A ⟶ A).toHomologicalComplex.f n = 𝟙 _ := rfl

/-- In every degree, the categorical composite of two morphisms is the composite of their maps.
-/
@[simp]
theorem comp_f {A B D : DifferentialGradedAlgebra.{t, a} R} (f : A ⟶ B) (g : B ⟶ D) (n : ℤ) :
    (f ≫ g).toHomologicalComplex.f n =
      f.toHomologicalComplex.f n ≫ g.toHomologicalComplex.f n := rfl

end DifferentialGradedAlgebra

end SheafOfModules
