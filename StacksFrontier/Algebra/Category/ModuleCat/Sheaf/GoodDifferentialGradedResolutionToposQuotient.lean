module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConeFreeDifferentialGradedModuleToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedResolutionQuotient
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0FSE: the good surjection onto a differential graded module

Let `Y` be a ringed topos, let `A` be a sheaf of differential graded `O_Y`-algebras on it and let
`M` be a right differential graded `A`-module. **There is a homomorphism `P ⟶ M` which is
surjective, which is surjective on the sheaves of cocycles, and whose source is good**, goodness
being `SheafOfModules.IsGoodToposBaseChange`: conditions (1), (2) and (3) of Tag 0FSA, the last
at the source's own quantifier over morphisms of ringed topoi.

The module `P` is the one of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedResolutionQuotient.lean` —
the first stage of the tower of Tag 0FSH, the twisted extension of the free differential graded
module `A[Z(M)]` on the sheaf of graded sets of closed sections of `M` by the free module on the
sheaf of graded sets of boundary pairs of `τ₀ : A[Z(M)] ⟶ M`. Nothing is an argument but `M`.
The two surjectivity clauses are taken from that file unchanged; what is added here is the third
clause at the whole of goodness.

## Main results

* `SheafOfModules.DifferentialGradedModule.isGoodToposBaseChange_towerStepFreeOnClosedSections`:
  **clause (3)**, the first stage of the tower is good.
* `SheafOfModules.DifferentialGradedModule.exists_good_surjection`: **Tag 0FSE**, the three
  clauses together, with `M` as its only argument.

## Implementation notes

**Why clause (3) is a one-liner here.** `A[Z(M)]` is good by Tag 0FSG,
`SheafOfModules.freeDGModule_isGoodToposBaseChange`, and the first stage is the twisted extension
of it, which is by definition the cone of
`SheafOfModules.dgLiftHom (boundaryPairs τ₀) A (A[Z(M)]) …` — a homomorphism whose *source* is a
free module. So `SheafOfModules.cone_freeDGModule_isGoodToposBaseChange` applies on the nose,
exactly as it does for a general stage of the tower in
`SheafOfModules.DifferentialGradedModule.exists_towerStep_isGoodToposBaseChange`.

**Why this is a second file and not an edit to the quotient.** Two reasons, the same two that
put the goodness-carrying tower of Tag 0FSH in its own file beside the flatness-carrying one.
First, `SheafOfModules.IsGoodToposBaseChange` is stated for a sheaf of differential graded
algebras `A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)` over a ringed topos
`Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}`, so the ring universe and the module universe
are one and the same and the site carries a structure sheaf of commutative rings; that boundary
comes from the differential graded transport along a morphism of ringed topoi and is recorded in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedToposDirectImage.lean`.
`SheafOfModules.DifferentialGradedModule.exists_flat_surjection` in the quotient file keeps the
two universes independent, and that is the statement its consumers use. Second, the closure lemma
`SheafOfModules.cone_freeDGModule_isGoodToposBaseChange` carries an import closure of some
hundreds of modules which the quotient file, a leaf of the flatness-only development, has no
other use for.

## References

* [Stacks Project, Tag 0FSE](https://stacks.math.columbia.edu/tag/0FSE)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks Stacks.SheafOfGradedSets Stacks.Sheaves.RingedToposModules

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules.DifferentialGradedModule

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)}

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-! ### Clause (3): goodness of the first stage -/

/-- **The first stage of the tower is good**, which is clause (3) of Tag 0FSE at the whole of
the definition of good in Section 0FSA: the free differential graded module `A[Z(M)]` on the
sheaf of graded sets of closed sections of `M` is good by Tag 0FSG, the first stage is the
twisted extension of it, a twisted extension is by definition the cone of
`SheafOfModules.dgLiftHom` — a homomorphism whose source is the free module on the boundary
pairs — and goodness is closed under the cone of a homomorphism out of a free module. -/
theorem isGoodToposBaseChange_towerStepFreeOnClosedSections [HasWeakSheafify Y.J (Type w)]
    (M : DifferentialGradedModule.{w, w, w} A) :
    IsGoodToposBaseChange.{w, v₁, u₁} (towerStep (freeOnClosedSectionsHom M)) :=
  cone_freeDGModule_isGoodToposBaseChange
    (boundaryPairs (freeOnClosedSectionsHom M).toHomologicalComplex)
    (freeDGModule_isGoodToposBaseChange (closedSections M.complex))
    (dgLiftHom (boundaryPairs (freeOnClosedSectionsHom M).toHomologicalComplex) A
      (freeDGModule (closedSections M.complex) A)
      (boundaryPairFamily (freeOnClosedSectionsHom M))
      (boundaryPairFamily_closed (freeOnClosedSectionsHom M)))

/-! ### The three clauses together -/

/-- **Tag 0FSE.** Every right differential graded `A`-module `M` receives a homomorphism from a
right differential graded `A`-module which is surjective, which is surjective on the sheaves of
cocycles, and whose source is good — `SheafOfModules.IsGoodToposBaseChange`, which is flat as a
graded module, K-flat, and such that along every morphism of ringed topoi out of the base, every
sheaf of differential graded algebras on its source and every unital homomorphism over it a
pullback exists and is again flat and K-flat.

The source is the first stage of the tower of the first proof of Tag 0FSH: the twisted extension
of the free differential graded module on the sheaf of graded sets of closed sections of `M` by
the free module on the sheaf of graded sets of boundary pairs of its homomorphism to `M`. It is
built from `M` alone.

Clause (2) is available on sections as well, as
`SheafOfModules.DifferentialGradedModule.exists_closed_preimage_towerStepMap`: every local
section of `M^n` killed by the differential is the image of a local section of the source killed
by the differential.

`SheafOfModules.DifferentialGradedModule.exists_flat_surjection` is the same three clauses with
the third read as conditions (1) and (2) of Section 0FSA alone, over a ringed site and with the
ring universe and the module universe independent. -/
@[stacks 0FSE]
theorem exists_good_surjection [HasWeakSheafify Y.J (Type w)]
    (M : DifferentialGradedModule.{w, w, w} A) :
    ∃ (Q : DifferentialGradedModule.{w, w, w} A) (π : Q ⟶ M),
      (∀ n : ℤ, Epi (π.toHomologicalComplex.f n)) ∧
        (∀ n : ℤ, Epi (HomologicalComplex.cyclesMap π.toHomologicalComplex n)) ∧
          IsGoodToposBaseChange.{w, v₁, u₁} Q :=
  ⟨towerStep (freeOnClosedSectionsHom M), towerStepMap (freeOnClosedSectionsHom M),
    epi_f_towerStepMap M, epi_cyclesMap_towerStepMap M,
    isGoodToposBaseChange_towerStepFreeOnClosedSections M⟩

end SheafOfModules.DifferentialGradedModule

end
