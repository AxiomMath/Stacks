module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraOnBasis
public import StacksFrontier.AlgebraicGeometry.Conormal.Charts

/-!
# Sheaves of graded algebras on the source of an immersion, from chartwise data

Let `i : Z ⟶ X` be an immersion of schemes and let `A`, `B` be sheaves of graded
`𝒪_Z`-algebras. A homomorphism `A ⟶ B` is a morphism of sheaves of modules in every degree
together with multiplicativity over *every* open of `Z`, whereas the affine-local descriptions of
the conormal algebra of `i` live over the preimages of the affine charts of
`StacksFrontier/AlgebraicGeometry/Conormal/Charts.lean` and nowhere else.

This file specialises the general assembly of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedAlgebraOnBasis.lean` to those charts, which
form a basis of `Z` by `Stacks.Conormal.conormalChart_isBasis`. The result takes data given over
the charts of `i` alone.

## Main definitions

* `Stacks.Conormal.gradedAlgebraHomOfChartHom` and
  `Stacks.Conormal.gradedAlgebraIsoOfChartIso`: a homomorphism, resp. an isomorphism, of sheaves
  of graded algebras on `Z` assembled from chartwise data.

## Main results

* `Stacks.Conormal.gradedAlgebraHomOfChartHom_app_app`,
  `Stacks.Conormal.gradedAlgebraIsoOfChartIso_hom_app_app` and
  `Stacks.Conormal.gradedAlgebraIsoOfChartIso_inv_app_app`: the chartwise components of the
  assembled morphisms are the given data.

## Implementation notes

Multiplicativity over an arbitrary open is not among the hypotheses: it is derived from the
chartwise hypothesis by `Stacks.BasisRestriction.map_mul_of_onBasis`, which is separatedness of
the target. In particular nothing here asks that `A` be generated in degree one — see the
implementation notes of `GradedAlgebraOnBasis` for why such a hypothesis would be both unusable
for a conormal algebra and unnecessary.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}}

section GradedAlgebra

variable (i : Z ⟶ X) [IsImmersion i]
  (A B : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf)

/-- **A homomorphism of sheaves of graded algebras on the source of an immersion, assembled from
chartwise data.** The hypotheses are: a map of the degree-`n` sections over the preimage of each
chart, commuting with the restriction maps between charts, and multiplicative over each chart.
Multiplicativity over an arbitrary open is not assumed; it follows, by
`Stacks.BasisRestriction.map_mul_of_onBasis`. -/
noncomputable def gradedAlgebraHomOfChartHom
    (e : ∀ (n : ℤ) (U : ConormalChart i),
      (A.piece n).val.obj (op ((conormalChartFunctor i).obj U)) ⟶
        (B.piece n).val.obj (op ((conormalChartFunctor i).obj U)))
    (hcomp : ∀ n : ℤ, Stacks.BasisRestriction.IsCompatibleOnBasis (A.piece n) (B.piece n)
      (conormalChartFunctor i).obj (e n))
    (hmul : Stacks.BasisRestriction.IsMultiplicativeOnBasis A B
      (conormalChartFunctor i).obj e) : A ⟶ B :=
  Stacks.BasisRestriction.gradedAlgebraHomOfSectionHomOnBasis A B (conormalChartFunctor i).obj e
    (conormalChart_isBasis i) hcomp hmul

/-- The assembled homomorphism has the given map as its degree-`n` component over each chart. -/
theorem gradedAlgebraHomOfChartHom_app_app
    (e : ∀ (n : ℤ) (U : ConormalChart i),
      (A.piece n).val.obj (op ((conormalChartFunctor i).obj U)) ⟶
        (B.piece n).val.obj (op ((conormalChartFunctor i).obj U)))
    (hcomp : ∀ n : ℤ, Stacks.BasisRestriction.IsCompatibleOnBasis (A.piece n) (B.piece n)
      (conormalChartFunctor i).obj (e n))
    (hmul : Stacks.BasisRestriction.IsMultiplicativeOnBasis A B
      (conormalChartFunctor i).obj e) (n : ℤ) (U : ConormalChart i) :
    ((gradedAlgebraHomOfChartHom i A B e hcomp hmul).app n).val.app
        (op ((conormalChartFunctor i).obj U)) = e n U :=
  Stacks.BasisRestriction.gradedAlgebraHomOfSectionHomOnBasis_app_app A B
    (conormalChartFunctor i).obj e (conormalChart_isBasis i) hcomp hmul n U

variable (e : ∀ (n : ℤ) (U : ConormalChart i),
  (A.piece n).val.obj (op ((conormalChartFunctor i).obj U)) ≅
    (B.piece n).val.obj (op ((conormalChartFunctor i).obj U)))

/-- **An isomorphism of sheaves of graded algebras on the source of an immersion, assembled from
chartwise isomorphisms.** Multiplicativity is required only of the forward maps, and only over
the charts. -/
noncomputable def gradedAlgebraIsoOfChartIso
    (hcomp : ∀ n : ℤ, Stacks.BasisRestriction.IsCompatibleOnBasis (A.piece n) (B.piece n)
      (conormalChartFunctor i).obj fun U => (e n U).hom)
    (hmul : Stacks.BasisRestriction.IsMultiplicativeOnBasis A B
      (conormalChartFunctor i).obj fun n U => (e n U).hom) : A ≅ B :=
  Stacks.BasisRestriction.gradedAlgebraIsoOfSectionIsoOnBasis A B (conormalChartFunctor i).obj e
    (conormalChart_isBasis i) hcomp hmul

/-- The assembled isomorphism has the given isomorphism as its degree-`n` component over each
chart. -/
theorem gradedAlgebraIsoOfChartIso_hom_app_app
    (hcomp : ∀ n : ℤ, Stacks.BasisRestriction.IsCompatibleOnBasis (A.piece n) (B.piece n)
      (conormalChartFunctor i).obj fun U => (e n U).hom)
    (hmul : Stacks.BasisRestriction.IsMultiplicativeOnBasis A B
      (conormalChartFunctor i).obj fun n U => (e n U).hom) (n : ℤ) (U : ConormalChart i) :
    ((gradedAlgebraIsoOfChartIso i A B e hcomp hmul).hom.app n).val.app
        (op ((conormalChartFunctor i).obj U)) = (e n U).hom :=
  Stacks.BasisRestriction.gradedAlgebraIsoOfSectionIsoOnBasis_hom_app_app A B
    (conormalChartFunctor i).obj e (conormalChart_isBasis i) hcomp hmul n U

/-- The inverse of the assembled isomorphism has the inverse of the given isomorphism as its
degree-`n` component over each chart. -/
theorem gradedAlgebraIsoOfChartIso_inv_app_app
    (hcomp : ∀ n : ℤ, Stacks.BasisRestriction.IsCompatibleOnBasis (A.piece n) (B.piece n)
      (conormalChartFunctor i).obj fun U => (e n U).hom)
    (hmul : Stacks.BasisRestriction.IsMultiplicativeOnBasis A B
      (conormalChartFunctor i).obj fun n U => (e n U).hom) (n : ℤ) (U : ConormalChart i) :
    ((gradedAlgebraIsoOfChartIso i A B e hcomp hmul).inv.app n).val.app
        (op ((conormalChartFunctor i).obj U)) = (e n U).inv :=
  Stacks.BasisRestriction.gradedAlgebraIsoOfSectionIsoOnBasis_inv_app_app A B
    (conormalChartFunctor i).obj e (conormalChart_isBasis i) hcomp hmul n U

end GradedAlgebra

end Stacks.Conormal

end
