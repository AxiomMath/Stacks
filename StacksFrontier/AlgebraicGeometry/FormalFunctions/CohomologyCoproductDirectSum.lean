module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsHypotheses
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.Basic

/-!
# `H^p(X, ∐ₙ Fₙ) ≅ ⨁ₙ H^p(X, Fₙ)` as an isomorphism of `Γ(X, ⊤)`-modules

On a quasi-compact quasi-separated scheme cohomology commutes with arbitrary direct sums
([Stacks, Tag 01FF]); the form the library carries is the abstract preservation of
`Discrete J`-colimits, `preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections` in
`Stacks.AlgebraicGeometry.TopDegreeBaseChange`.
What [Stacks, Tag 0897]'s base change needs instead is a *concrete* comparison with
`DirectSum`: the graded cohomology `⨁ₙ H^p(X, Fₙ)` that [Stacks, Tag 0897] is about is a
`DirectSum`, and the `B`-action on it is given on the summands.

This file turns the preservation into that comparison, in two steps: the direct sum of a family
of modules is the coproduct in `ModuleCat R` (`directSumCofanIsColimit`), and the index type is
`ℕ`, which does not lie in the module universe, so the preservation is moved along
`ULift.{u} ℕ ≃ ℕ`.

## Main definitions

* `Stacks.Cohomology.CoproductDirectSum.directSumCofan` and
  `Stacks.Cohomology.CoproductDirectSum.directSumCofanIsColimit`: **`⨁ᵢ Nᵢ` is the coproduct of
  a family of modules**, with the inclusions `DirectSum.lof` as the cofan.
* `Stacks.Cohomology.CoproductDirectSum.cohomologyCoprodDirectSumIso`:
  **`H^p(X, ∐ₙ Fₙ) ≅ ⨁ₙ H^p(X, Fₙ)`**, an isomorphism of `Γ(X, ⊤)`-modules.

## Main results

* `Stacks.Cohomology.CoproductDirectSum.preservesColimitsOfShape_discrete_nat`: cohomology
  commutes with `ℕ`-indexed direct sums.
* `Stacks.Cohomology.CoproductDirectSum.map_sigmaι_comp_cohomologyCoprodDirectSumIso_hom`:
  **the comparison is the one determined by the coproduct injections**, which is the only
  property of it a consumer needs: `H^p(X, ιₙ)` followed by it is `DirectSum.lof n`.

## Implementation notes

The index type of `directSumCofan` is `ι : Type`, not `ι : Type u`: `DirectSum ι β` lands in
`Type (max u_ι u_β)`, so an index type in a universe above the module universe would take the
direct sum out of `ModuleCat.{u} R`. `ℕ` is the case [Stacks, Tag 0897] needs and it is in
`Type 0`.

`DirectSum.linearMap_ext` is not used for the uniqueness clause of `directSumCofanIsColimit`:
the composition `∘ₗ` forces the `Module` instance on `(directSumCofan N).pt` to be compared
with `DirectSum.instModule`, which are definitionally but not syntactically equal, so the
clause is proved by `DirectSum.induction_on` instead.

## References

* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.AffineBase
open scoped DirectSum AlgebraicGeometry

universe u

namespace Stacks.Cohomology.CoproductDirectSum

section Cofan

variable {R : Type u} [Ring R] {ι : Type} [DecidableEq ι] (N : ι → ModuleCat.{u} R)

/-- The cofan of a family of modules given by their direct sum. -/
public def directSumCofan : Cofan N :=
  Cofan.mk (ModuleCat.of R (⨁ i, (N i : Type u)))
    fun i => ModuleCat.ofHom (DirectSum.lof R ι (fun i => (N i : Type u)) i)

/-- **The direct sum is the coproduct in `ModuleCat R`.** -/
public def directSumCofanIsColimit : IsColimit (directSumCofan N) :=
  Cofan.IsColimit.mk _
    (fun t => ModuleCat.ofHom
      (DirectSum.toModule R ι (t.pt : Type u) fun i => (t.inj i).hom))
    (fun t i => by
      apply ModuleCat.hom_ext
      refine LinearMap.ext fun x => ?_
      simp [directSumCofan, DirectSum.toModule_lof])
    (fun t m hm => by
      apply ModuleCat.hom_ext
      dsimp only [directSumCofan, Cofan.mk_pt, ModuleCat.of_coe]
      refine LinearMap.ext fun z => ?_
      induction z using DirectSum.induction_on with
      | zero => rw [map_zero, map_zero]
      | of i x =>
          rw [← DirectSum.lof_eq_of R, ModuleCat.hom_ofHom, DirectSum.toModule_lof]
          exact congrArg (fun φ : N i ⟶ t.pt => φ.hom x) (hm i)
      | add z z' hz hz' => rw [map_add, map_add, hz, hz'])

end Cofan

section Cohomology

variable (X : Scheme.{u}) [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]
  (p : ℕ) (F : ℕ → X.Modules)

/-- **Cohomology of a quasi-compact quasi-separated scheme commutes with `ℕ`-indexed direct
sums.** -/
public theorem preservesColimitsOfShape_discrete_nat :
    PreservesColimitsOfShape (Discrete ℕ) ((moduleGlobalSections X).rightDerived p) :=
  have := open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
    preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections X p (ULift.{u} ℕ)
  preservesColimitsOfShape_of_equiv (Discrete.equivalence (Equiv.ulift : ULift.{u} ℕ ≃ ℕ)) _

/-- The direct sum of the cohomologies, as a cocone on the family `F` composed with `H^p`. -/
public def cohomologyDirectSumCocone :
    Cocone (Discrete.functor F ⋙ (moduleGlobalSections X).rightDerived p) :=
  (Cocone.precompose
    (Discrete.compNatIsoDiscrete F ((moduleGlobalSections X).rightDerived p)).hom).obj
      (directSumCofan fun n => ((moduleGlobalSections X).rightDerived p).obj (F n))

/-- That cocone is a colimit. -/
public def cohomologyDirectSumCoconeIsColimit : IsColimit (cohomologyDirectSumCocone X p F) :=
  (IsColimit.precomposeHomEquiv
    (Discrete.compNatIsoDiscrete F ((moduleGlobalSections X).rightDerived p)) _).symm
      (directSumCofanIsColimit fun n => ((moduleGlobalSections X).rightDerived p).obj (F n))

/-- **`H^p(X, ∐ₙ Fₙ) ≅ ⨁ₙ H^p(X, Fₙ)`** over `Γ(X, ⊤)`. -/
public def cohomologyCoprodDirectSumIso :
    ((moduleGlobalSections X).rightDerived p).obj (∐ F) ≅
      ModuleCat.of Γ(X, ⊤)
        (⨁ n : ℕ, (((moduleGlobalSections X).rightDerived p).obj (F n) : Type u)) := by
  haveI := preservesColimitsOfShape_discrete_nat X p
  exact IsColimit.coconePointUniqueUpToIso
    (isColimitOfPreserves ((moduleGlobalSections X).rightDerived p) (coproductIsCoproduct F))
    (cohomologyDirectSumCoconeIsColimit X p F)

/-- **The comparison is the one determined by the coproduct injections.** -/
public theorem map_sigmaι_comp_cohomologyCoprodDirectSumIso_hom (n : ℕ) :
    ((moduleGlobalSections X).rightDerived p).map (Sigma.ι F n) ≫
        (cohomologyCoprodDirectSumIso X p F).hom =
      ModuleCat.ofHom (DirectSum.lof Γ(X, ⊤) ℕ
        (fun n => (((moduleGlobalSections X).rightDerived p).obj (F n) : Type u)) n) := by
  have := preservesColimitsOfShape_discrete_nat X p
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitOfPreserves ((moduleGlobalSections X).rightDerived p) (coproductIsCoproduct F))
    (cohomologyDirectSumCoconeIsColimit X p F) ⟨n⟩
  simpa [cohomologyCoprodDirectSumIso, cohomologyDirectSumCocone, directSumCofan] using h

end Cohomology

end Stacks.Cohomology.CoproductDirectSum

end
