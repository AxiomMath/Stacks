module

public import StacksFrontier.Algebra.DifferentialGraded.AlgebraCochainComplex
public import StacksFrontier.RingTheory.Koszul.PowBaseTensorBalanceLadder

/-!
# The category of differential graded algebras

Homomorphisms of differential graded algebras over a commutative ring `R` compose and have
identities, so they make `DifferentialGradedAlgebra R` a category. An inverse system of
differential graded algebras is then a functor out of `ℕᵒᵖ`, with no further bookkeeping.

## Main definitions

* `DifferentialGradedAlgebra.instCategory`: the category structure.
* `DifferentialGradedAlgebra.toCochainComplexFunctor`: the underlying cochain complex of
  `R`-modules, as a functor out of it.

## Implementation notes

Two homomorphisms with the same underlying algebra homomorphism are equal, so the category
axioms reduce to the ones for `AlgHom`. The identity and the composition are the ones the
library already has; only their assembly is new.
-/
@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- Differential graded algebras over `R` and their homomorphisms form a category. -/
instance instCategory : Category (DifferentialGradedAlgebra.{u, u} R) where
  Hom A B := A.Hom B
  id A := Hom.id A
  comp f g := g.comp f
  id_comp _ := hom_eq_of_toAlgebraHom_eq rfl
  comp_id _ := hom_eq_of_toAlgebraHom_eq rfl
  assoc _ _ _ := hom_eq_of_toAlgebraHom_eq rfl

/-- The algebra homomorphism underlying the identity of `A` is the identity of `A.A`. -/
@[simp]
theorem id_toAlgebraHom (A : DifferentialGradedAlgebra.{u, u} R) :
    Hom.toAlgebraHom (𝟙 A) = AlgHom.id R A.A := rfl

/-- The algebra homomorphism underlying a composition is the composition of the underlying
algebra homomorphisms. The order is reversed because `Hom.comp` precomposes. -/
@[simp]
theorem comp_toAlgebraHom {A B C : DifferentialGradedAlgebra.{u, u} R} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).toAlgebraHom = g.toAlgebraHom.comp f.toAlgebraHom := rfl

/-- The underlying cochain complex of `R`-modules of a differential graded algebra, as a
functor. -/
def toCochainComplexFunctor :
    DifferentialGradedAlgebra.{u, u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj A := (regularModule A).toCochainComplex
  map φ := φ.toCochainMap
  map_id _ := Hom.toCochainMap_eq_id _ fun _ => rfl
  map_comp φ ψ := (Hom.toCochainMap_comp_eq φ ψ _ fun _ => rfl).symm

/-- `toCochainComplexFunctor` sends `A` to the cochain complex underlying its regular module. -/
@[simp]
theorem toCochainComplexFunctor_obj (A : DifferentialGradedAlgebra.{u, u} R) :
    (toCochainComplexFunctor (R := R)).obj A = (regularModule A).toCochainComplex := rfl

/-- `toCochainComplexFunctor` sends a homomorphism to its underlying cochain map. -/
@[simp]
theorem toCochainComplexFunctor_map {A B : DifferentialGradedAlgebra.{u, u} R} (φ : A ⟶ B) :
    (toCochainComplexFunctor (R := R)).map φ = φ.toCochainMap := rfl

end DifferentialGradedAlgebra

end
