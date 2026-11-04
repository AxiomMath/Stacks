module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricPointStalkCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFiniteDirectImage

/-!
# Stalks of higher direct images along a proper morphism (Stacks 0DDF)

Let `f : X ⟶ Y` be a proper morphism of schemes and `ȳ : Spec Ω ⟶ Y` a geometric point, with
geometric fibre `X_ȳ = X ×_Y Spec Ω`. For a torsion abelian sheaf `F` on `X_étale`,
`(Rⁿf_* F)_ȳ = Hⁿ_étale(X_ȳ, F|_{X_ȳ})`, and for an object `E` of `D⁺(X_étale)` with torsion
cohomology sheaves, `(Hⁿ(Rf_* E))_ȳ = Hⁿ(X_ȳ, E|_{X_ȳ})`.

The proof is the source's: proper base change (Stacks 095T, in the form
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`) for the cartesian square
of the geometric fibre, followed by the identification of the stalk at a geometric point with
global sections over `Spec Ω`, which is
`Stacks.EtaleCohomology.etaleAbelianSheafFiberRightDerivedDirectImageIso` and
`Stacks.EtaleCohomology.etaleAbelianSheafFiberHomologyDerivedDirectImageIso`. The field `Ω` is
only required to be separably closed, which includes the algebraically closed fields of the
source's geometric points.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianSheafFiberRightDerivedDirectImageIsoOfIsProper`: part (1).
* `Stacks.EtaleCohomology.etaleAbelianSheafFiberHomologyDerivedDirectImageIsoOfIsProper`: part (2).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (y : Spec (.of Ω) ⟶ Y)

/-- **Stacks 0DDF (1).** For a proper morphism `f : X ⟶ Y`, a geometric point `ȳ : Spec Ω ⟶ Y`
and a torsion abelian sheaf `F` on `X_étale`, the stalk of `Rⁿf_* F` at `ȳ` is the étale
cohomology `Hⁿ(X_ȳ, F_ȳ)` of the restriction of `F` to the geometric fibre `X_ȳ = X ×_Y Spec Ω`. -/
@[stacks 0DDF "part (1)"]
def etaleAbelianSheafFiberRightDerivedDirectImageIsoOfIsProper
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) (n : ℕ) :
    letI := hasExt_sheaf_smallEtale_succ (pullback f y)
    (((pointSmallEtale y).ulift.{u + 1}).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      (((etaleAbelianDirectImage.{u, 0} f).rightDerived n).obj F) ≅
    AddCommGrpCat.of
      (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (pullback.fst f y)).obj F) n) :=
  letI := hasExt_sheaf_smallEtale_succ (pullback f y)
  etaleAbelianSheafFiberRightDerivedDirectImageIso.{u, 0} f y
    (cohomologyCommutesWithBaseChange_of_isProper f) F hF n

/-- **Stacks 0DDF (2).** For a proper morphism `f : X ⟶ Y`, a geometric point `ȳ : Spec Ω ⟶ Y`
and an object `E` of `D⁺(X_étale)` with torsion cohomology sheaves, the stalk at `ȳ` of the
`n`-th cohomology sheaf of `Rf_* E` is the `n`-th hypercohomology of the restriction of `E` to
the geometric fibre `X_ȳ = X ×_Y Spec Ω`. -/
@[stacks 0DDF "part (2)"]
def etaleAbelianSheafFiberHomologyDerivedDirectImageIsoOfIsProper
    (E : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (m : ℤ)
    (hE : E.IsGE m)
    (hT : Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology E) (n : ℤ) :
    letI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse (pullback f y)
    (((pointSmallEtale y).ulift.{u + 1}).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
        n).obj ((etaleAbelianDerivedDirectImage.{u, 0} f).obj E)) ≅
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
      ((Stacks.DerivedFunctor.totalRightDerived
        (Sheaf.Γ (pullback f y).smallEtaleTopology AddCommGrpCat.{u + 1})).obj
        ((etaleAbelianDerivedInverseImage.{u, 0} (pullback.fst f y)).obj E)) :=
  letI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse (pullback f y)
  etaleAbelianSheafFiberHomologyDerivedDirectImageIso.{u, 0} f y
    (cohomologyCommutesWithBaseChange_of_isProper f) E m hE hT n

end Stacks.EtaleCohomology

end
