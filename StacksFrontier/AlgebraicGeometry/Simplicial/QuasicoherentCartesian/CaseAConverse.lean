module

public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.CaseAForward

/-!
# A cartesian module of case (A) with presented components is presented

## Main results

* `CategoryTheory.SimplicialSite.CartesianSlice.hasGlobalPresentation_over_of_isIso_transitionA`.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSite.CartesianSlice

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable (C : SimplicialSite.{u}) (O : Sheaf (situation C).totalTopology RingCat.{u})
  {n : SimplexCategory} (Q : (situation C).component n)

/-- Every object of the total slice at `Q` is the image of an object of a degree-`m` slice at
`u_φ Q` under the inclusion along the canonical arrow, for some `φ`. -/
theorem exists_eq_sliceInclusionAt_obj
    (Z : Over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q)) :
    ∃ (m : SimplexCategory) (ψ : n ⟶ m) (W : Over ((transitionFunctorA C ψ).obj Q)),
      (sliceInclusionAt C ψ Q).obj W = Z := by
  obtain ⟨⟨⟨k⟩, x⟩, ⟨⟨⟩⟩, ⟨⟨ψ⟩, g⟩⟩ := Z
  have e := Pseudofunctor.CoGrothendieck.ι_map_comp_ιNatTrans_app C.totalPseudofunctor
    (R := op k) (S := op n) ψ.op (a := Q) (x := x) g
  exact ⟨k, ψ, Over.mk g, congrArg Over.mk e⟩

/-- **The converse direction of Stacks 0D7M in case (A), locally.** If the transitions of `F` are
invertible and the degree-`n` component of `F` has a global presentation over `Q`, then `F` has
a global presentation over `Q` viewed in the total site. -/
theorem hasGlobalPresentation_over_of_isIso_transitionA (F : SheafOfModules.{u} O)
    (hcart : ∀ (m : SimplexCategory) (ψ : n ⟶ m), IsIso (transitionA C O ψ F))
    (hQ : ((((situation C).componentModuleRestriction O n).obj F).over Q).HasGlobalPresentation) :
    (F.over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj
      Q)).HasGlobalPresentation := by
  refine SimplicialSiteSituation.CartesianSlice.hasGlobalPresentation_of_sliceTransition
    (situation C) O _ hQ fun Z => ?_
  obtain ⟨m, ψ, W, hW⟩ := exists_eq_sliceInclusionAt_obj C Q Z
  refine ⟨m, _, canonicalArrow C ψ Q, W, hW, sliceTransitionA C O ψ Q, ?_⟩
  have := isIso_beckChevalleyA C O ψ Q
  have := hcart m ψ
  show IsIso ((sliceTransitionModules C O ψ Q).app _)
  rw [sliceTransitionModules_app_over C O ψ Q F]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (NatIso.isIso_app_of_isIso _ _) (Functor.map_isIso _ _)

end CategoryTheory.SimplicialSite.CartesianSlice
