module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Sheaves.SheafCondition.OpensLeCover
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical polynomial presentation of a sheaf of rings on a space

Let `A ⟶ B` be a morphism of sheaves of commutative rings on a topological space `X`. The
presheaf `U ↦ A(U)[B(U)]`, with one polynomial variable for every section of `B` over `U`,
sheafifies to a sheaf `A[B]` of `A`-algebras, and evaluating the variable `[b]` at `b` produces
a morphism `A[B] ⟶ B` of `A`-algebras which is surjective as a map of sheaves. This exhibits
every sheaf of `A`-algebras as a quotient of a polynomial algebra over `A`.

## Main definitions

* `Stacks.Sheaves.PolynomialAlgebra.polynomialAlgebraPresheaf`: the presheaf
  `U ↦ A(U)[B(U)]`.
* `Stacks.Sheaves.PolynomialAlgebra.polynomialCoefficient`: the inclusion of coefficients
  `A ⟶ A(-)[B(-)]`.
* `Stacks.Sheaves.PolynomialAlgebra.polynomialEvaluation`: objectwise evaluation
  `A(U)[B(U)] ⟶ B(U)`.
* `Stacks.Sheaves.PolynomialAlgebra.polynomialAlgebraSheaf`: the sheaf `A[B]`.
* `Stacks.Sheaves.PolynomialAlgebra.polynomialAlgebraMap`: the structural morphism
  `A ⟶ A[B]`.
* `Stacks.Sheaves.PolynomialAlgebra.canonicalPolynomialPresentation`: the morphism
  `A[B] ⟶ B` induced by `[b] ↦ b`.

## Main results

* `Stacks.Sheaves.PolynomialAlgebra.polynomialAlgebraMap_comp_canonicalPolynomialPresentation`:
  the canonical presentation is compatible with the structural maps from `A`, hence is a
  morphism of `A`-algebras.
* `Stacks.Sheaves.PolynomialAlgebra.canonicalPolynomialPresentation_surjective`: the canonical
  presentation is locally surjective on underlying sets, which is what surjectivity of a
  morphism of sheaves means.

## Implementation notes

The objectwise polynomial rings form a presheaf by applying the restriction maps both to the
coefficients and to the names of the variables; this is `MvPolynomial.eval₂Hom` applied to the
coefficient restriction and to the reindexing of variables. The morphism `A[B] ⟶ B` is obtained
from objectwise evaluation by the universal property of sheafification, so the displayed rule
`[b] ↦ b` is forced rather than chosen, and local surjectivity is inherited from the objectwise
surjectivity of evaluation along the factorisation through the sheafification unit.

## References

* [Stacks Project, Tag 08TH](https://stacks.math.columbia.edu/tag/08TH)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Sheaves.PolynomialAlgebra

variable {X : TopCat.{u}}

/-- The presheaf `U ↦ A(U)[B(U)]`, with one polynomial variable for every section of `B`
over `U`. -/
noncomputable def polynomialAlgebraPresheaf
    (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    TopCat.Presheaf CommRingCat.{u} X where
  obj U := CommRingCat.of (MvPolynomial (B.obj.obj U) (A.obj.obj U))
  map {U V} f := CommRingCat.ofHom <|
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp (A.obj.map f).hom)
      (fun b ↦ MvPolynomial.X ((B.obj.map f).hom b))
  map_id U := by
    ext <;> simp
  map_comp f g := by
    ext <;> simp

/-- The natural inclusion of coefficients into the objectwise polynomial algebra. -/
noncomputable def polynomialCoefficient
    (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    A.obj ⟶ polynomialAlgebraPresheaf A B where
  app U := CommRingCat.ofHom MvPolynomial.C
  naturality U V g := by
    ext
    exact (MvPolynomial.eval₂Hom_C _ _ _).symm

/-- Objectwise evaluation of `A(U)[B(U)]` in `B(U)`, using the given map on coefficients and
sending the variable `[b]` to `b`. -/
noncomputable def polynomialEvaluation
    {A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    (f : A ⟶ B) : polynomialAlgebraPresheaf A B ⟶ B.obj where
  app U := CommRingCat.ofHom (MvPolynomial.eval₂Hom (f.hom.app U).hom id)
  naturality U V g := by
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext <;> intro <;> simp [polynomialAlgebraPresheaf]

/-- The sheaf `A[B]`: the sheafification of `U ↦ A(U)[B(U)]`. -/
@[stacks 08TH "the polynomial algebra sheaf"]
noncomputable def polynomialAlgebraSheaf
    (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    Sheaf (Opens.grothendieckTopology X) CommRingCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
    (polynomialAlgebraPresheaf A B)

/-- The structural morphism `A ⟶ A[B]`, obtained from the coefficient inclusions and the
sheafification unit. -/
@[stacks 08TH "the coefficient map"]
noncomputable def polynomialAlgebraMap
    (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    A ⟶ polynomialAlgebraSheaf A B :=
  ⟨polynomialCoefficient A B ≫
    toSheafify (Opens.grothendieckTopology X) (polynomialAlgebraPresheaf A B)⟩

/-- The canonical presentation `A[B] ⟶ B`, induced by `[b] ↦ b`. -/
@[stacks 08TH "the canonical map"]
noncomputable def canonicalPolynomialPresentation
    {A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (f : A ⟶ B) :
    polynomialAlgebraSheaf A B ⟶ B :=
  ⟨sheafifyLift (Opens.grothendieckTopology X) (polynomialEvaluation f) B.2⟩

/-- Evaluation `A[B] ⟶ B` is compatible with the structural maps from `A`, hence is a morphism
of `A`-algebras. -/
@[stacks 08TH "compatibility with coefficients"]
theorem polynomialAlgebraMap_comp_canonicalPolynomialPresentation
    {A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (f : A ⟶ B) :
    polynomialAlgebraMap A B ≫ canonicalPolynomialPresentation f = f := by
  apply Sheaf.hom_ext
  show polynomialCoefficient A B ≫
      toSheafify (Opens.grothendieckTopology X) (polynomialAlgebraPresheaf A B) ≫
      sheafifyLift (Opens.grothendieckTopology X) (polynomialEvaluation f) B.2 = f.hom
  rw [toSheafify_sheafifyLift]
  ext U a
  simp [polynomialCoefficient, polynomialEvaluation, polynomialAlgebraPresheaf]

/-- The canonical polynomial presentation `A[B] ⟶ B` is locally surjective on underlying
sets. -/
@[stacks 08TH "surjectivity"]
theorem canonicalPolynomialPresentation_surjective
    {A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (f : A ⟶ B) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (Functor.whiskerRight (canonicalPolynomialPresentation f).hom
        (forget CommRingCat)) := by
  let J := Opens.grothendieckTopology X
  have h : Presheaf.IsLocallySurjective J (polynomialEvaluation f) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget J _).2 <| by
      apply Presheaf.isLocallySurjective_of_surjective
      intro U b
      exact ⟨MvPolynomial.X b, MvPolynomial.eval₂_X _ _ _⟩
  have _ : Presheaf.IsLocallySurjective J
      (toSheafify J (polynomialAlgebraPresheaf A B) ≫
        sheafifyLift J (polynomialEvaluation f) B.2) := by
    simpa only [toSheafify_sheafifyLift] using h
  dsimp [canonicalPolynomialPresentation]
  exact (Presheaf.isLocallySurjective_iff_whisker_forget J _).1 <|
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (toSheafify_sheafifyLift (J := J) (polynomialEvaluation f) B.2)

end Stacks.Sheaves.PolynomialAlgebra

end
