module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaLeg
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaSituation
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaLegA

/-!
# The leg equation of the module direct-sum formula, for an arbitrary situation

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. The componentwise direct-sum formula of Stacks 0D72 (6) for sheaves of modules,
`CategoryTheory.SimplicialSiteSituation.moduleSumFormula`, is an isomorphism that says nothing
about which summand a given map lands in; what identifies the decomposition is that its `φ`th
summand inclusion is the canonical map
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg` attached to `φ`. That assertion is
proved in each of the two cases of Stacks 09WE separately — case (A) is
`CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA` and case (B) is
`CategoryTheory.CocontinuousSimplicialSite.ModuleSumFormulaLegEqB` — and the two statements name
their own case's formula, `…moduleSumFormulaA` and `…moduleSumFormulaB`, rather than the
situation's.

This file states the assertion once for an arbitrary situation, as
`CategoryTheory.SimplicialSiteSituation.ModuleSumFormulaLegEq`, and discharges it in case (A);
case (B) and the assembled theorem live downstream (see the implementation notes).
It is the form in which the derived summand inclusion of Stacks 0D72 (6) consumes it: the derived
statement is about `S.moduleSumFormula O n m` for a variable situation `S`, so it cannot be fed
either case's leg equation directly.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.ModuleSumFormulaLegEq`: the leg equation of
  Stacks 0D72 (6) for an arbitrary simplicial-site situation.

## Main results

* `CategoryTheory.SimplicialSite.moduleSumFormulaLegEq_situation`: **the leg equation holds in
  case (A)**, where the transitions are morphisms of sites. It is
  `CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA` read at the situation, which applies on
  the nose: `CategoryTheory.SimplicialSiteSituation.moduleSumFormula` is defined by a `match` on
  the situation whose case-(A) branch *is* `…moduleSumFormulaA`.

## Implementation notes

*Where case (B) is discharged.* The leg equation in case (B) is
`CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaLegEqB`, which sits above this module
in the import order; the two cases are assembled downstream into the situation-level theorem
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLegEq`.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **The leg equation of Stacks 0D72 (6), for an arbitrary simplicial-site situation**: for every
simplex map `φ : [n] ⟶ [m]`, the `φ`th summand inclusion of the componentwise direct-sum formula
`CategoryTheory.SimplicialSiteSituation.moduleSumFormula`, followed by the inverse of that
formula, is the canonical map
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg` attached to `φ`.

It is a `Prop`-valued definition because it is what the derived summand inclusion of
Stacks 0D72 (6) reduces to, and because the case-(B) half of its proof sits above this module in
the import order; the theorem for every situation is
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLegEq`. -/
def ModuleSumFormulaLegEq : Prop :=
  ∀ {n m : SimplexCategory} (φ : n ⟶ m),
    Sigma.ι (fun ψ : n ⟶ m => S.transitionPullbackModules' O ψ) φ ≫
        (S.moduleSumFormula O n m).inv =
      S.moduleSumFormulaLeg O φ

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.SimplicialSite

variable (C : SimplicialSite.{u}) (P : Sheaf (situation C).totalTopology CommRingCat.{u})

/-- **The leg equation of Stacks 0D72 (6) holds in case (A).**
`CategoryTheory.SimplicialSiteSituation.moduleSumFormula` is defined by a `match` on the
situation, and in case (A) the branch taken is literally
`CategoryTheory.SimplicialSite.moduleSumFormulaA`, so the case-(A) leg equation
`CategoryTheory.SimplicialSite.moduleSumFormulaLegEqA` is the situation-level one. -/
theorem moduleSumFormulaLegEq_situation :
    (situation C).ModuleSumFormulaLegEq P :=
  fun φ => moduleSumFormulaLegEqA C P φ

end CategoryTheory.SimplicialSite

end
