module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleFaceCriterion
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerreModules
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

/-!
# Cartesian objects of `D(O)` are those with cartesian cohomology

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of rings on its total site
such that the morphisms of ringed topoi `f_{δ^n_j} : (Sh(C_n), O_n) ⟶ (Sh(C_{n-1}), O_{n-1})`
attached to the face maps are flat. Then an object `K` of `D(O)` is cartesian exactly when every
cohomology module `H^q(K)` is a cartesian `O`-module.

## Main results

* `CategoryTheory.isIso_liftedTransition_app_iff_forall_isIso_app_homology`: a transition of
  derived functors lifted from a transition `t : P ⋙ U ⟶ Q` of exact functors, through a
  comparison `Qh ⋙ L ⟶ U ⋙ Qh` which is invertible, is invertible at `K` exactly when `t` is
  invertible at every cohomology object of `K`.
* `CategoryTheory.SimplicialSiteSituation.isIso_derivedComponentModuleTransition_app_iff`: along
  a simplex map whose pullback of modules is exact, the derived transition
  `Lf_φ^* K_m ⟶ K_n` is invertible exactly when the transitions `f_φ^* H^q(K)_m ⟶ H^q(K)_n`
  are.
* `SimplicialSiteSituation.isCartesianDerivedModule_iff_forall_isCartesianModule_homology`
  (in the namespace `CategoryTheory`): for flat face transitions, an object `K` of `D(O)` is
  cartesian exactly when every `H^q(K)` is a cartesian `O`-module.

## References

* [Stacks Project, Tag 0D7L](https://stacks.math.columbia.edu/tag/0D7L)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 07TG](https://stacks.math.columbia.edu/tag/07TG)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

namespace CategoryTheory

section Lifted

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {Cm : Type*} [Category* Cm] [Abelian Cm] [HasDerivedCategory Cm]
  {Cn : Type*} [Category* Cn] [Abelian Cn] [HasDerivedCategory Cn]
  {P : C ⥤ Cm} [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {U : Cm ⥤ Cn} [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  {Q : C ⥤ Cn} [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  {L : DerivedCategory Cm ⥤ DerivedCategory Cn}
  (cmp : DerivedCategory.Qh ⋙ L ⟶
    U.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) [IsIso cmp]
  (t : P ⋙ U ⟶ Q)

/-- **Invertibility of a lifted derived transition is detected on cohomology.** Let
`t : P ⋙ U ⟶ Q` be a transformation of exact functors and `L` a functor of derived categories
with an invertible comparison `Qh ⋙ L ⟶ U ⋙ Qh`. The transformation `P ⋙ L ⟶ Q` of derived
functors lifted from `t` is invertible at `K` exactly when `t` is invertible at every cohomology
object of `K`. -/
theorem isIso_liftedTransition_app_iff_forall_isIso_app_homology (K : DerivedCategory C) :
    IsIso ((liftedTransition P.mapDerivedCategoryFactorsh cmp Q.mapDerivedCategoryFactorsh
        (mapHomotopyCategoryTransition (ComplexShape.up ℤ) P U Q t)
        (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))).app K) ↔
      ∀ q : ℤ, IsIso (t.app ((DerivedCategory.homologyFunctor C q).obj K)) := by
  have := Localization.essSurj (DerivedCategory.Q (C := C))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
  let X := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X) ≅ K :=
    (DerivedCategory.quotientCompQhIso C).app X ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have hH : ∀ q : ℤ, (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).obj X ≅
      (DerivedCategory.homologyFunctor C q).obj K := fun q ↦
    (DerivedCategory.homologyFunctorFactors C q).symm.app X ≪≫
      (DerivedCategory.homologyFunctor C q).mapIso (DerivedCategory.Q.objObjPreimageIso K)
  rw [← NatTrans.isIso_app_iff_of_iso _ e, liftedTransition_app_q, isIso_comp_left_iff,
    isIso_comp_left_iff, isIso_comp_right_iff, mapHomotopyCategoryTransition_app]
  change IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient Cn (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex t (ComplexShape.up ℤ)).app X))) ↔ _
  rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
  refine forall_congr' fun q ↦ ?_
  rw [← NatTrans.isIso_app_iff_of_iso t (hH q), quasiIsoAt_iff_isIso_homologyMap]
  refine (isIso_comp_right_iff ((HomologicalComplex.homologyFunctor Cn (ComplexShape.up ℤ) q).map
      ((NatTrans.mapHomologicalComplex t (ComplexShape.up ℤ)).app X))
      ((Q.mapHomologicalComplexCompHomologyFunctorIso q).hom.app X)).symm.trans ?_
  rw [Functor.mapHomologicalComplexCompHomologyFunctorIso_hom_naturality t q X,
    isIso_comp_left_iff]

end Lifted

end CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

section Exact

variable {m n : SimplexCategory} (φ : m ⟶ n)
  (hφ : PreservesFiniteLimits (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules)

include hφ

/-- Degreewise pullback along the transition of a simplex map inverts the quasi-isomorphisms
when pullback of modules along it is exact. -/
theorem isInvertedBy_pullbackOnHomotopy_transition_of_preservesFiniteLimits :
    (targetQuasiIso (S.componentRingedTopos O m)).IsInvertedBy
      (pullbackOnHomotopy.{u, u, u, u, u, u} (S.transitionRingedToposHom O φ)) := by
  have := hφ
  exact (MorphismProperty.IsInvertedBy.iff_of_iso _
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.mapDerivedCategoryFactorsh).1
    (MorphismProperty.IsInvertedBy.of_comp _ DerivedCategory.Qh
      (Localization.inverts DerivedCategory.Qh _) _)

/-- **`Lf_φ^* = f_φ^*` for an exact pullback.** When pullback of modules along the transition
of a simplex map is exact, the canonical comparison from the derived pullback to degreewise
pullback is invertible. -/
theorem isIso_derivedTransitionComparison_of_preservesFiniteLimits :
    IsIso (S.derivedTransitionComparison O φ) :=
  Functor.isIso_of_isLeftDerivedFunctor_of_inverts (S.derivedTransitionPullback O φ)
    (S.derivedTransitionComparison O φ)
    (S.isInvertedBy_pullbackOnHomotopy_transition_of_preservesFiniteLimits O φ hφ)

/-- Along a simplex map whose pullback of modules is exact, the derived transition
`Lf_φ^* K_m ⟶ K_n` is invertible exactly when the transitions `f_φ^* H^q(K)_m ⟶ H^q(K)_n` of
all the cohomology modules of `K` are. -/
theorem isIso_derivedComponentModuleTransition_app_iff
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    IsIso ((S.derivedComponentModuleTransition O φ).app K) ↔
      ∀ q : ℤ, IsIso (S.fiberTransitionModules O φ
        ((DerivedCategory.homologyFunctor (S.totalRingedTopos O).Modules q).obj K)) := by
  have := hφ
  have := S.isIso_derivedTransitionComparison_of_preservesFiniteLimits O φ hφ
  delta derivedComponentModuleTransition derivedComponentModuleRestriction
  exact (isIso_liftedTransition_app_iff_forall_isIso_app_homology _ _ K).trans
    (forall_congr' fun q ↦ Iff.of_eq (congrArg IsIso (S.componentModuleTransition_app O φ _)))

end Exact

/-- Let `O` be a sheaf of rings on the total site of a simplicial site such
that the morphisms of ringed topoi `f_{δ^n_j} : (Sh(C_n), O_n) ⟶ (Sh(C_{n-1}), O_{n-1})` of the
face maps are flat. Then an object `K` of `D(O)` is cartesian if and only if `H^q(K)` is a
cartesian `O`-module for all `q`. -/
@[stacks 0D7L "part (2), cartesian objects of D(O) for flat face transitions"]
theorem isCartesianDerivedModule_iff_forall_isCartesianModule_homology
    (flat : ∀ (k : ℕ) (i : Fin (k + 2)),
      (S.transitionRingedToposHom O (SimplexCategory.δ i)).IsFlat)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    S.IsCartesianDerivedModule O K ↔
      ∀ q : ℤ, IsCartesianModule S O
        ((DerivedCategory.homologyFunctor (S.totalRingedTopos O).Modules q).obj K) := by
  have hface : ∀ (k : ℕ) (i : Fin (k + 2)),
      IsIso ((S.derivedComponentModuleTransition O (SimplexCategory.δ i)).app K) ↔
        ∀ q : ℤ, IsIso (S.fiberTransitionModules O (SimplexCategory.δ i)
          ((DerivedCategory.homologyFunctor (S.totalRingedTopos O).Modules q).obj K)) :=
    fun k i ↦ S.isIso_derivedComponentModuleTransition_app_iff O (SimplexCategory.δ i)
      (S.preservesFiniteLimits_transitionPullbackModules_of_isFlat O _ (flat k i)) K
  rw [S.isCartesianDerivedModule_iff_faces O K]
  exact ⟨fun h q ↦ (S.isCartesianModule_iff_faces O _).2 fun k i ↦ (hface k i).1 (h k i) q,
    fun h k i ↦ (hface k i).2 fun q ↦ (S.isCartesianModule_iff_faces O _).1 (h q) k i⟩

end CategoryTheory.SimplicialSiteSituation

end
