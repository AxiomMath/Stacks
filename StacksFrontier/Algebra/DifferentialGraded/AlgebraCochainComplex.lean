module

public import StacksFrontier.Algebra.DifferentialGraded.HomotopyRetractDerived
public import StacksCore.Tactic.StacksAttribute

/-!
# The cochain complex underlying a homomorphism of differential graded algebras

A differential graded algebra over a commutative ring `R` is in particular a cochain complex of
`R`-modules, namely the one underlying its regular module, and a homomorphism of differential
graded algebras is in particular a map of those complexes.

## Main definitions

* `DifferentialGradedAlgebra.Hom.toCochainMap`: the map of underlying cochain complexes of
  `R`-modules induced by a homomorphism of differential graded algebras.

## Main results

* `DifferentialGradedAlgebra.Hom.toCochainMap_eq_id` and
  `DifferentialGradedAlgebra.Hom.toCochainMap_comp_eq`: the construction takes an endomorphism
  which is the identity on the algebra to the identity, and composites to composites. Both are
  stated through the underlying algebra homomorphism, because that is what determines a
  homomorphism of differential graded algebras.
-/
@[expose] public noncomputable section

open CategoryTheory DifferentialGradedModule

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- The map of underlying cochain complexes of `R`-modules induced by a homomorphism of
differential graded algebras. -/
def Hom.toCochainMap {A B : DifferentialGradedAlgebra.{u, u} R} (φ : A.Hom B) :
    (regularModule A).toCochainComplex ⟶ (regularModule B).toCochainComplex :=
  cochainMapOfGraded (M := regularModule A) (N := regularModule B)
    φ.toAlgebraHom.toLinearMap φ.map_grading φ.map_d

/-- The cochain map of a homomorphism of differential graded algebras is, in each degree,
the restriction of the underlying algebra homomorphism. -/
theorem Hom.toCochainMap_f {A B : DifferentialGradedAlgebra.{u, u} R} (φ : A.Hom B) (n : ℤ) :
    φ.toCochainMap.f n = ModuleCat.ofHom (gradedOfLinear (M := regularModule A)
      (N := regularModule B) φ.toAlgebraHom.toLinearMap φ.map_grading n) := rfl

/-- An endomorphism which is the identity on the underlying algebra induces the identity on
the underlying cochain complex. -/
theorem Hom.toCochainMap_eq_id {A : DifferentialGradedAlgebra.{u, u} R} (φ : A.Hom A)
    (h : ∀ a, φ.toAlgebraHom a = a) : φ.toCochainMap = 𝟙 _ := by
  ext n x
  exact Subtype.ext (h _)

/-- The cochain maps of two composable homomorphisms of differential graded algebras compose. -/
theorem Hom.toCochainMap_comp_eq {A B C : DifferentialGradedAlgebra.{u, u} R}
    (φ : A.Hom B) (ψ : B.Hom C) (χ : A.Hom C)
    (h : ∀ a, ψ.toAlgebraHom (φ.toAlgebraHom a) = χ.toAlgebraHom a) :
    φ.toCochainMap ≫ ψ.toCochainMap = χ.toCochainMap := by
  ext n x
  exact Subtype.ext (h _)

end DifferentialGradedAlgebra

end
