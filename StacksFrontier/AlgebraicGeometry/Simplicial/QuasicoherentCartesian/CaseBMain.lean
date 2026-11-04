module

public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.CaseBCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransition
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModulePairFunctor

/-!
# Stacks 0D7M in case (B)

## Main results

In the namespace `CategoryTheory.CocontinuousSimplicialSite.CartesianSlice`:

* `isIso_transitionB_of_isQuasicoherentOnSite`.
* `hasGlobalPresentation_over_of_isIso_transitionB`.
* `isQuasicoherentOnSite_iff_isCartesianModule_caseB`.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.CocontinuousSimplicialSite.CartesianSlice

variable (C : CocontinuousSimplicialSite.{u})
  (P : Sheaf (situation C).totalTopology CommRingCat.{u})
  {n m : SimplexCategory} (φ : n ⟶ m)

/-- **The transition is invertible over `W` as soon as the module has a global presentation
over some `Q` receiving `u_φ W`.** -/
theorem isIso_transitionB_over (F : SheafOfModules.{u} ((situation C).totalRingSheaf P))
    {W : (situation C).component m} {Q : (situation C).component n}
    (b : (transitionFunctorB C φ).obj W ⟶ Q)
    (hQ : (F.over ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj
      Q)).HasGlobalPresentation) :
    IsIso ((Stacks.SheafOfModules.inverseImage.{u} (((situation C).componentTopology m).over W)
      ((situation C).componentTopology m) (Over.forget W) (ringSheafB C P m)).map
        (transitionB C P φ F)) := by
  have : ∀ N : SheafOfModules.{u} ((totalRing C P).over
      ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj Q)),
      Small.{u} N.sections :=
    fun N => SheafOfModules.small_sections_of_isTerminal Over.mkIdTerminal N
  obtain ⟨Pr⟩ := SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections hQ
  have hτ : IsIso ((sliceTransitionModules C P φ b).app _) :=
    (sliceTransitionB C P φ b).isIso_τ_app_of_presentation Pr
  have := isIso_beckChevalleyB C P φ b
  have h := sliceTransitionModules_app_over C P φ b F
  have : IsIso ((beckChevalleyB C P φ b).natTrans.app
      (((situation C).componentModuleRestriction (totalRing C P) n).obj F) ≫
        (Stacks.SheafOfModules.inverseImage.{u} (((situation C).componentTopology m).over W)
          ((situation C).componentTopology m) (Over.forget W) (ringSheafB C P m)).map
          (transitionB C P φ F)) := h ▸ hτ
  exact IsIso.of_isIso_comp_left ((beckChevalleyB C P φ b).natTrans.app
      (((situation C).componentModuleRestriction (totalRing C P) n).obj F)) _

/-- **The forward direction of Stacks 0D7M in case (B), cartesian half.** -/
theorem isIso_transitionB_of_isQuasicoherentOnSite
    (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) (hF : F.IsQuasicoherentOnSite) :
    IsIso (transitionB C P φ F) := by
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over
    (X := fun i : {W : (situation C).component m // ∃ (Q : (situation C).component n)
      (_ : (transitionFunctorB C φ).obj W ⟶ Q),
        (F.over ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj
          Q)).HasGlobalPresentation} => i.1) ?_ _ fun i => ?_
  · intro V
    have h := (transitionFunctorB C φ).cover_lift ((situation C).componentTopology m)
      ((situation C).componentTopology n)
      (SimplicialSiteSituation.CartesianSlice.coversTop_component_hasGlobalPresentation
        (situation C) (totalRing C P) F hF n ((transitionFunctorB C φ).obj V))
    refine ((situation C).componentTopology m).superset_covering ?_ h
    rintro V' g ⟨⟨Q, hQ⟩, ⟨b⟩⟩
    exact ⟨⟨V', Q, b, hQ⟩, ⟨𝟙 _⟩⟩
  · obtain ⟨Q, b, hQ⟩ := i.2
    exact isIso_transitionB_over C P φ F b hQ

/-- The localized transition is invertible at the restriction of a module whose transition is. -/
theorem isIso_sliceTransitionModules_app_over_of_isIso
    (F : SheafOfModules.{u} ((situation C).totalRingSheaf P))
    {W : (situation C).component m} {Q : (situation C).component n}
    (b : (transitionFunctorB C φ).obj W ⟶ Q) (h : IsIso (transitionB C P φ F)) :
    IsIso ((sliceTransitionModules C P φ b).app
      (F.over ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj
        Q))) := by
  have := isIso_beckChevalleyB C P φ b
  rw [sliceTransitionModules_app_over C P φ b F]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (NatIso.isIso_app_of_isIso _ _) (Functor.map_isIso _ _)

/-- **The converse direction of Stacks 0D7M in case (B), locally.** -/
theorem hasGlobalPresentation_over_of_isIso_transitionB
    (F : SheafOfModules.{u} ((situation C).totalRingSheaf P))
    (hcart : ∀ (k : SimplexCategory) (ψ : n ⟶ k), IsIso (transitionB C P ψ F))
    {Q : (situation C).component n}
    (hQ : ((((situation C).componentModuleRestriction (totalRing C P) n).obj F).over
      Q).HasGlobalPresentation) :
    (F.over ((CategoryTheory.SimplicialSiteSituation.componentFunctor (situation C) n).obj
      Q)).HasGlobalPresentation := by
  refine SimplicialSiteSituation.CartesianSlice.hasGlobalPresentation_of_sliceTransition
    (situation C) (totalRing C P) _ hQ fun Z => ?_
  obtain ⟨⟨⟨k⟩, x⟩, ⟨⟨⟩⟩, ⟨⟨ψ⟩, g⟩⟩ := Z
  refine ⟨k, x, canonicalArrow C ψ g, Over.mk (𝟙 x), ?_, sliceTransitionB C P ψ g, ?_⟩
  · have e : (Grothendieck.ι C.underlying (op k)).map (𝟙 x) ≫
        (Grothendieck.ιNatTrans (F := C.underlying) ψ.op).app x ≫
          (Grothendieck.ι C.underlying (op n)).map g = ⟨ψ.op, g⟩ :=
      (congrArg (· ≫ _) (Functor.map_id _ _)).trans ((Category.id_comp _).trans
        (Grothendieck.ιNatTrans_app_comp_ι_map ψ.op g))
    exact congrArg Over.mk e
  · exact isIso_sliceTransitionModules_app_over_of_isIso C P ψ F g (hcart k ψ)

/-- **Stacks 0D7M in case (B), with the cocontinuous pullback along the transitions.** -/
theorem isQuasicoherentOnSite_iff_isIso_transitionB
    (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    F.IsQuasicoherentOnSite ↔
      (∀ (n m : SimplexCategory) (ψ : n ⟶ m), IsIso (transitionB C P ψ F)) ∧
        ∀ n : SimplexCategory,
          (((situation C).componentModuleRestriction (totalRing C P) n).obj
            F).IsQuasicoherentOnSite :=
  ⟨fun hF => ⟨fun _ _ ψ => isIso_transitionB_of_isQuasicoherentOnSite C P ψ F hF,
      SimplicialSiteSituation.CartesianSlice.isQuasicoherentOnSite_componentModuleRestriction
        (situation C) (totalRing C P) F hF⟩,
    fun h => SimplicialSiteSituation.CartesianSlice.isQuasicoherentOnSite_of_components
      (situation C) (totalRing C P) F (fun ⟨⟨k⟩, x⟩ => ⟨k, x, rfl⟩) h.2
      fun n _ hQ => hasGlobalPresentation_over_of_isIso_transitionB C P F (h.1 n) hQ⟩

/-- In case (B), a module is cartesian exactly when its transitions for the cocontinuous pullback
are invertible. -/
theorem isCartesianModule_iff_isIso_transitionB
    (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    (situation C).IsCartesianModule P F ↔
      ∀ (n m : SimplexCategory) (ψ : n ⟶ m), IsIso (transitionB C P ψ F) := by
  refine ⟨fun h n m ψ => ?_, fun h n m ψ => ?_⟩
  · have h1 := (congrArg IsIso (fiberTransitionModules_eq_transitionB C P ψ F)).mp (h ψ)
    have : IsIso ((transitionPullbackModulesIsoB C P ψ).hom.app
        (((situation C).componentModuleRestriction (totalRing C P) n).obj F)) :=
      Iso.isIso_hom ((transitionPullbackModulesIsoB C P ψ).app _)
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ this h1
  · refine (congrArg IsIso (fiberTransitionModules_eq_transitionB C P ψ F)).mpr ?_
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      (Iso.isIso_hom ((transitionPullbackModulesIsoB C P ψ).app
        (((situation C).componentModuleRestriction (totalRing C P) n).obj F))) (h n m ψ)

/-- **Stacks 0D7M in case (B).** -/
theorem isQuasicoherentOnSite_iff_isCartesianModule_caseB
    (F : SheafOfModules.{u} ((situation C).totalRingSheaf P)) :
    F.IsQuasicoherentOnSite ↔
      (situation C).IsCartesianModule P F ∧
        ∀ n : SimplexCategory, ((situation C).componentModule P F n).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_isIso_transitionB C P F).trans
    (and_congr_left' (isCartesianModule_iff_isIso_transitionB C P F).symm)

end CategoryTheory.CocontinuousSimplicialSite.CartesianSlice
