module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjectionRestrict
public import
  StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleOfModuleSystem

/-!
# The summandwise comparison of Stacks 0D9E (2) in case (B) of Stacks 09WE

Let `C` be a cocontinuous simplicial site — case (B) of the simplicial-site situation of
Stacks 09WE — and let `O` be a sheaf of commutative rings on its total site.
`CategoryTheory.SimplicialSiteSituation.isCartesianDerivedModule_iff_isIso_moduleProjection`
carries one hypothesis, `proj_restrict`, and
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleProjectionRestrict.lean`
reduces it to *two* inputs: the summand description
`CategoryTheory.SimplicialSiteSituation.DerivedModuleSumFormulaSummand` of the direct-sum formula
of Stacks 0D72 (6) on derived categories, and the residual square
`CategoryTheory.SimplicialSiteSituation.ModuleProjectionAdjunctSquare` at each simplex map.

**The first of the two is unconditional**, because the leg equation of Stacks 0D72 (6) is proved
in every simplicial-site situation (in case (B) by
`CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaLegEqB`), and its derived form is
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormulaSummand`. This file discharges it,
leaving the residual square as the single carried hypothesis of Stacks 0D9E (2) in case (B).

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.moduleProjection_restrict_of_adjunctSquare`:
  **the summandwise comparison `proj_restrict` of Stacks 0D9E (2) in case (B), from the residual
  square alone.**
* `CategoryTheory.CocontinuousSimplicialSite`'s
  `isCartesianDerivedModule_iff_isIso_moduleProjection_of_adjunctSquare`: **Stacks 0D9E (2) in
  case (B) with the residual square as its one carried hypothesis.**
* `CategoryTheory.CocontinuousSimplicialSite.isIso_moduleProjection_of_isCartesianDerivedModule`:
  the same conclusion in the spelling Stacks 0D9R asks for.

## Implementation notes

*What is left, and what it is blocked on.* The residual square
`CategoryTheory.SimplicialSiteSituation.ModuleProjectionAdjunctSquare` is **not** discharged by the
leg equation, and the leg equation is not what it needs. Its sheaf-level form is proved —
`CategoryTheory.SimplicialSiteSituation`'s
`transitionPullbackModules_map_componentModuleProjectionAdjunct_comp`
— but from two hypotheses, `…TransitionTensorCoherence` and `…TransitionUnitorCoherence`, which
together are the assertion that the comparison of Stacks 03EL is monoidal against the pullback
transition of Stacks 09WF. Neither is proved in this development, and the module docstring of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleTransitionTensor.lean` records
why: `Stacks.SheafOfModules.pullbackTensorIso` carries naturality in its two sheaf variables and no
composition law in the morphism of ringed topoi. So the leg equation and the monoidality are
*independent* inputs of `proj_restrict`, consumed at different places, and discharging the first
leaves the second untouched.

*Why flatness is one named hypothesis.* The canonical map
`CategoryTheory.SimplicialSiteSituation.moduleProjection` takes the flatness proof as an argument,
so two separately elaborated spellings of it give syntactically distinct maps and the `IsIso`
instance asked for by one is not found from a hypothesis about the other — proof irrelevance does
not help, because instance search compares the maps and not the proofs. Flatness is therefore taken
once, by name, and passed by that name; the strict-implicit spelling Stacks 0D9R uses is crossed
only in `…isIso_moduleProjection_of_isCartesianDerivedModule`, which exists for that crossing.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9R](https://stacks.math.columbia.edu/tag/0D9R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open scoped Simplicial

universe u

namespace CategoryTheory.CocontinuousSimplicialSite

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable (C : CocontinuousSimplicialSite.{u})
  (P : Sheaf (situation C).totalTopology CommRingCat.{u})

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
  (pullbackOnHomotopy ((situation C).transitionRingedToposHom P φ)).HasLeftDerivedFunctor
    (targetQuasiIso ((situation C).componentRingedTopos P m))]

/-- **The summandwise comparison `proj_restrict` of Stacks 0D9E (2), in case (B) of Stacks 09WE,
from the residual square alone.** Granted
`CategoryTheory.SimplicialSiteSituation.ModuleProjectionAdjunctSquare`, the restriction to degree
`m` of the canonical map `g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` is, under the direct-sum identifications
of its source and its target, the direct sum of the derived transitions of Stacks 07TF (4).

This is `CategoryTheory.SimplicialSiteSituation.moduleProjection_restrict_of_adjunctSquare` with
its summand description supplied by
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormulaSummand`. The leg equation of
Stacks 0D72 (6) is thereby spent; the residual square is independent of it and is what remains. -/
theorem moduleProjection_restrict_of_adjunctSquare
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m),
      ((situation C).transitionRingedToposHom P φ).IsFlat)
    (K : DerivedCategory ((situation C).totalRingedTopos P).Modules)
    (hadj : (situation C).ModuleProjectionAdjunctSquare P K)
    (n m : SimplexCategory) :
    ((situation C).derivedComponentModuleRestriction P m).map
          ((situation C).moduleProjection P n (hflat n) K) ≫
        ((situation C).moduleProjectionTargetIso P n m K).hom =
      ((situation C).derivedModuleSumFormula P n m (hflat n)
          (((situation C).derivedComponentModuleRestriction P n).obj K)).hom ≫
        Limits.biproduct.map fun φ : n ⟶ m =>
          ((situation C).derivedComponentModuleTransition P φ).app K :=
  (situation C).moduleProjection_restrict_of_adjunctSquare P hflat
    ((situation C).derivedModuleSumFormulaSummand P hflat) K hadj n m

/-- **Stacks 0D9E (2) in case (B) of Stacks 09WE, with the residual square as its one carried
hypothesis.** Under flatness of the structure-sheaf transitions, and granted
`CategoryTheory.SimplicialSiteSituation.ModuleProjectionAdjunctSquare`, an object `K` of `D(O)` is
cartesian exactly when the canonical map `g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` is an isomorphism in every
simplicial degree.

This is `CategoryTheory.SimplicialSiteSituation`'s
`isCartesianDerivedModule_iff_isIso_moduleProjection_of_adjunctSquare`
with its summand description supplied. The conclusion and the flatness hypothesis are those of the
source; what is carried beyond them is the residual square and nothing else. -/
theorem isCartesianDerivedModule_iff_isIso_moduleProjection_of_adjunctSquare
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m),
      ((situation C).transitionRingedToposHom P φ).IsFlat)
    (K : DerivedCategory ((situation C).totalRingedTopos P).Modules)
    (hadj : (situation C).ModuleProjectionAdjunctSquare P K) :
    (situation C).IsCartesianDerivedModule P K ↔
      ∀ n : SimplexCategory, IsIso ((situation C).moduleProjection P n (hflat n) K) :=
  (situation C).isCartesianDerivedModule_iff_isIso_moduleProjection_of_adjunctSquare P hflat
    ((situation C).derivedModuleSumFormulaSummand P hflat) K hadj

/-- **The invertibility of the canonical projection map of Stacks 0D9E (2) in case (B), in the
spelling Stacks 0D9R asks for.** The hypothesis `hproj` of
`CategoryTheory.SimplicialSiteSituation.eq_zero_of_derivedComponentModule_zero` is the
invertibility of `CategoryTheory.SimplicialSiteSituation.moduleProjection` in every degree `⦋i⦌`,
with flatness spelled `fun _ φ => hflat φ` out of a strict-implicit `hflat`. This delivers it from
cartesianness, granted the residual square.

This is `CategoryTheory.SimplicialSiteSituation.isIso_moduleProjection_of_isCartesianDerivedModule`
with its summand description supplied. Flatness is passed to
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormulaSummand` at the very spelling the
consumer uses, because the two spellings give syntactically distinct canonical maps and instance
search does not cross them. -/
theorem isIso_moduleProjection_of_isCartesianDerivedModule
    (hflat : ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n),
      ((situation C).transitionRingedToposHom P φ).IsFlat)
    (K : DerivedCategory ((situation C).totalRingedTopos P).Modules)
    (hadj : (situation C).ModuleProjectionAdjunctSquare P K)
    (hK : (situation C).IsCartesianDerivedModule P K) (i : ℕ) :
    IsIso ((situation C).moduleProjection P ⦋i⦌ (fun _ φ => hflat φ) K) :=
  (situation C).isIso_moduleProjection_of_isCartesianDerivedModule P hflat
    ((situation C).derivedModuleSumFormulaSummand P fun _ _ φ => hflat φ) K hadj hK i

end CategoryTheory.CocontinuousSimplicialSite

end
