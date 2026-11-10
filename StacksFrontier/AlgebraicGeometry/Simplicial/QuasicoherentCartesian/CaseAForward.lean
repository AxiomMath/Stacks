module

public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.CaseABeckChevalley
public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.CaseABridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismsOfSites

/-!
# A quasi-coherent module on the total site of case (A) is cartesian

## Main results

* `CategoryTheory.SimplicialSite.CartesianSlice.isIso_transitionA_of_isQuasicoherentOnSite`.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 08H2](https://stacks.math.columbia.edu/tag/08H2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSite.CartesianSlice

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable (C : SimplicialSite.{u}) (O : Sheaf (situation C).totalTopology RingCat.{u})
  {n m : SimplexCategory} (φ : n ⟶ m)

/-- **The transition is invertible over `u_φ Q` as soon as the module has a global presentation
over `Q`.** -/
theorem isIso_transitionA_over (F : SheafOfModules.{u} O) (Q : (situation C).component n)
    (hQ : SheafOfModules.HasGlobalPresentation
      (F.over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q))) :
    IsIso ((transitionA C O φ F).over ((transitionFunctorA C φ).obj Q)) := by
  have : ∀ N : SheafOfModules.{u}
      (O.over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q)),
      Small.{u} N.sections :=
    fun N => SheafOfModules.small_sections_of_isTerminal Over.mkIdTerminal N
  obtain ⟨P⟩ := SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections hQ
  have hτ := isIso_sliceTransitionModules_of_presentation C O φ Q P
  have := isIso_beckChevalleyA C O φ Q
  rw [sliceTransitionModules_app_over] at hτ
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ ((beckChevalleyA C O φ Q).app _) _
    inferInstance hτ


/-- **The forward direction of Stacks 0D7M in case (A), cartesian half.** -/
theorem isIso_transitionA_of_isQuasicoherentOnSite (F : SheafOfModules.{u} O)
    (hF : F.IsQuasicoherentOnSite) : IsIso (transitionA C O φ F) := by
  have : PreservesLimit (Functor.empty.{0} (Sheaf ((situation C).componentTopology n) (Type u)))
      ((transitionFunctorA C φ).sheafPullback (Type u) ((situation C).componentTopology n)
        ((situation C).componentTopology m)) :=
    have h : PreservesLimitsOfShape (Discrete PEmpty.{1})
        ((transitionFunctorA C φ).sheafPullback (Type u) ((situation C).componentTopology n)
          ((situation C).componentTopology m)) :=
      @PreservesFiniteLimits.preservesFiniteLimits _ _ _ _ _
        (C.isMorphismOfSites φ).preservesFiniteLimits (Discrete PEmpty.{1}) _ _
    h.preservesLimit
  have hu := GrothendieckTopology.coversTop_obj_of_preservesTerminal_sheafPullback
    (transitionFunctorA C φ) ((situation C).componentTopology n)
    ((situation C).componentTopology m)
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over
    (GrothendieckTopology.coversTop_map_of_coversTop_obj (transitionFunctorA C φ) hu
      (SimplicialSiteSituation.CartesianSlice.coversTop_component_hasGlobalPresentation
        (situation C) O F hF n)) _ fun i => ?_
  exact isIso_transitionA_over C O φ F i.1 i.2

end CategoryTheory.SimplicialSite.CartesianSlice
