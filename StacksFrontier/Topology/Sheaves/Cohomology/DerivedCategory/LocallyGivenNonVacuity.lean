module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtLocalToGlobal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOverASaturatedCollection

/-!
# Negative self-Ext of the system prescribed by an object in degree zero

Let `(X, 𝒪_X)` be a ringed space. For a sheaf of `𝒪_X`-modules `F` placed in degree zero, the
system of locally given derived objects (Situation 0D67, `Stacks.DerivedGlueing.LocallyGiven`)
prescribed by `F` on a collection of opens has no negative self-Ext. For the system prescribed on
every open, this gives the vanishing clause of [Stacks, Tag 0D68] for the solution given by the
prescribed object on `⊤`.

## Main results

* `Stacks.DerivedGlueing.sSup_opens_locallyGivenOfTop`: the opens of the system
  `Stacks.DerivedGlueing.locallyGivenOfTop` have supremum `⊤`.
* `Stacks.DerivedGlueing.subsingleton_shiftedHom_locallyGivenOfGlobal_single`: the system
  prescribed by a sheaf of modules placed in degree zero, over an arbitrary collection of opens,
  has no negative self-Ext.
* `Stacks.DerivedGlueing.subsingleton_shiftedHom_selfSolution_single`: for the system prescribed
  on every open by a sheaf of modules placed in degree zero, the global object of the solution
  given by the prescribed object on `⊤` has no negative self-Ext.

## References

* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-- The opens of the system `Stacks.DerivedGlueing.locallyGivenOfTop X K` have supremum `⊤`. -/
theorem sSup_opens_locallyGivenOfTop (K : OpenDerivedCategory X ⊤) :
    sSup (locallyGivenOfTop X K).opens = ⊤ := by
  simp

/-- For a sheaf of `𝒪_X`-modules `F` on the open subspace `⊤` and a collection `𝒞` of opens, the
system `Stacks.DerivedGlueing.locallyGivenOfGlobal` prescribed by `F` placed in degree zero has
`Ext^i(K_U, K_U) = 0` for every `i < 0` and every member `U` of `𝒞`. -/
theorem subsingleton_shiftedHom_locallyGivenOfGlobal_single
    (𝒞 : Set (Opens X.carrier))
    (F : SheafOfModules.{u} (restrictedRingSheaf X ⊤))
    (U : Opens X.carrier) (hU : U ∈ (locallyGivenOfGlobal X 𝒞
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (restrictedRingSheaf X ⊤)) 0).obj F)).opens)
    (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom
      ((locallyGivenOfGlobal X 𝒞 ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (restrictedRingSheaf X ⊤)) 0).obj F)).obj U hU)
      ((locallyGivenOfGlobal X 𝒞 ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (restrictedRingSheaf X ⊤)) 0).obj F)).obj U hU) i) :=
  subsingleton_shiftedHom_of_iso
    (((openModuleRestriction X U ⊤ le_top).mapDerivedCategorySingleFunctor 0).app F)
    (((openModuleRestriction X U ⊤ le_top).mapDerivedCategorySingleFunctor 0).app F) i
    (Stacks.SheafOfModules.subsingleton_shiftedHom_single_of_neg _ _ i hi)

/-- For a sheaf of `𝒪_X`-modules `F` on the open subspace `⊤`, let `K` be the global object of
the solution `Stacks.DerivedGlueing.selfSolutionOver` of the system prescribed on every open by `F`
placed in degree zero, given by the prescribed object on `⊤`. Then `Ext^i(K, K) = 0` for every
`i < 0`. -/
theorem subsingleton_shiftedHom_selfSolution_single
    (F : SheafOfModules.{u} (restrictedRingSheaf X ⊤)) (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom
      ((selfSolutionOver (locallyGivenOfTop X ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (restrictedRingSheaf X ⊤)) 0).obj F)) ⊤
          (top_mem_locallyGivenOfTop_opens X _)).toSolution).obj
      ((selfSolutionOver (locallyGivenOfTop X ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (restrictedRingSheaf X ⊤)) 0).obj F)) ⊤
          (top_mem_locallyGivenOfTop_opens X _)).toSolution).obj i) :=
  Solution.subsingleton_shiftedHom_self
    (selfSolutionOver _ ⊤ (top_mem_locallyGivenOfTop_opens X _)).toSolution
    (sSup_opens_locallyGivenOfTop X _) (inter_eq_sSup_covered_locallyGivenOfTop X _)
    (subsingleton_shiftedHom_locallyGivenOfGlobal_single X Set.univ F) i hi

end Stacks.DerivedGlueing

end
