module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianRestrictTransition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentLowerShriekAdjunction

/-!
# The summand inclusions of the abelian sum formula are the canonical transitions (Stacks 09WG)

The sum formula of Stacks 09WG writes `g_m^{-1} g_{n!}` on abelian sheaves as the direct sum, over
the simplex maps `φ : [n] ⟶ [m]`, of the inverse images along the transitions.  The isomorphism
itself says nothing about which summand a given map lands in; what identifies the decomposition is
that the `φ`th summand inclusion is the *canonical* map attached to `φ`, namely the unit of
`g_{n!} ⊣ g_n^{-1}` followed by the transition of Stacks 09WF with abelian coefficients.

That canonical map is `componentSumFormulaLeg`, and this file proves that in case (A) of
Stacks 09WE it is the summand inclusion.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentSumFormulaLeg`: the canonical map from the
  inverse image along the transition at `φ` into `g_m^{-1} g_{n!}`.

## Main results

* `CategoryTheory.Functor.ranAdjunction_unit_app_app_comp_map_comp_ranCounit`: the unit of a right
  Kan extension adjunction, transported along an arrow into the image of the functor and followed
  by the counit, is that transport.
* `CategoryTheory.Functor.map_sheafAdjunctionCocontinuous_unit_comp_ranRestrictSheafComparison`:
  the consequence for the comparison of right adjoints of the ran criterion.
* `CategoryTheory.SimplicialSiteSituation.homEquiv_componentSumFormulaLeg_app`: the transpose of
  the canonical map is the direct-image transition.
* `CategoryTheory.SimplicialSite`
  `.sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg`: **Stacks 09WG in
  case (A)**, the summand inclusion is the canonical map.

The primed versions state the same with `restrictAb` in place of `abelianComponent`.

## Implementation notes

The two results in `CategoryTheory.Functor` are stated for generic data — sites `C_n`, `C_m`,
`E`, functors `v_n`, `v_m`, a family `t i` and transformations `τ i` — rather than for the
simplicial component inclusions: specialized, they mention
`CategoryTheory.SimplicialSiteSituation.component n`, a `match` that does not unfold at the
transparency at which `rw` builds its motives. For the same reason the main proofs are chains of
`Eq.trans` and `congrArg` rather than `rw` sequences.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace CategoryTheory.Functor

universe w v₁ u₁ v₂ u₂ v₃ u₃ v u

/-- The unit of a right Kan extension adjunction, transported along an arrow into the image of the
functor and followed by the Kan extension counit, is that transport. -/
theorem ranAdjunction_unit_app_app_comp_map_comp_ranCounit {C D : Type*} [Category* C]
    [Category* D] (L : C ⥤ D) {A : Type*} [Category* A]
    [∀ P : C ⥤ A, L.HasRightKanExtension P] (P : D ⥤ A) (X : C) (Y : D) (g : Y ⟶ L.obj X) :
    ((L.ranAdjunction A).unit.app P).app Y ≫ (L.ran.obj (L ⋙ P)).map g ≫
        (L.ranCounit.app (L ⋙ P)).app X = P.map g := by
  have h : P.map g ≫ ((L.ranAdjunction A).unit.app P).app (L.obj X) =
      ((L.ranAdjunction A).unit.app P).app Y ≫ (L.ran.obj (L ⋙ P)).map g :=
    ((L.ranAdjunction A).unit.app P).naturality g
  rw [← Category.assoc, ← h, Category.assoc,
    L.ranCounit_app_app_ranAdjunction_unit_app_app P X]
  exact Category.comp_id _

variable {I : Type w} {Cn : Type u₁} [Category.{v₁} Cn] {Cm : Type u₂} [Category.{v₂} Cm]
  {E : Type u₃} [Category.{v₃} E]
  (A : Type u) [Category.{v} A]
  (Jn : GrothendieckTopology Cn) (Jm : GrothendieckTopology Cm) (L : GrothendieckTopology E)
  (vn : Cn ⥤ E) (vm : Cm ⥤ E) (t : I → (Cn ⥤ Cm)) (τ : ∀ i, t i ⋙ vm ⟶ vn)
  [∀ F : Cmᵒᵖ ⥤ A, vm.op.HasPointwiseRightKanExtension F]
  [vn.IsContinuous Jn L] [vm.IsContinuous Jm L] [vm.IsCocontinuous Jm L]
  [ht : ∀ i, (t i).IsContinuous Jn Jm]

/-- The unit of the adjunction of the cocontinuous `v_m`, restricted along `v_n` and followed by
the comparison of right adjoints of the ran criterion, is restriction along `τ i`. -/
theorem map_sheafAdjunctionCocontinuous_unit_comp_ranRestrictSheafComparison (i : I)
    (B : Sheaf L A) :
    (vn.sheafPushforwardContinuous A Jn L).map
          ((vm.sheafAdjunctionCocontinuous A Jm L).unit.app B) ≫
        (ranRestrictSheafComparison A Jn Jm L vn vm t τ i).app
          ((vm.sheafPushforwardContinuous A Jm L).obj B) =
      (⟨whiskerRight (NatTrans.op (τ i)) B.obj⟩ :
        (vn.sheafPushforwardContinuous A Jn L).obj B ⟶
          ((t i).sheafPushforwardContinuous A Jn Jm).obj
            ((vm.sheafPushforwardContinuous A Jm L).obj B)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext X
  obtain ⟨U⟩ := X
  show ((vm.sheafAdjunctionCocontinuous A Jm L).unit.app B).hom.app (op (vn.obj U)) ≫
      ((ranRestrictComparison A vn vm t τ i).app
        ((vm.sheafPushforwardContinuous A Jm L).obj B).obj).app (op U) = _
  rw [Functor.sheafAdjunctionCocontinuous_unit_app_hom, ranRestrictComparison_app_app]
  exact ranAdjunction_unit_app_app_comp_map_comp_ranCounit vm.op B.obj (op ((t i).obj U))
    (op (vn.obj U)) ((τ i).app U).op

end CategoryTheory.Functor

namespace CategoryTheory.SimplicialSiteSituation

universe u

/-- The canonical map from the inverse image along the transition at a simplex map
`φ : [n] ⟶ [m]` into `g_m^{-1} g_{n!}`: the unit of `g_{n!} ⊣ g_n^{-1}`, followed by the
transition of Stacks 09WF with abelian coefficients. -/
noncomputable def componentSumFormulaLeg (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    S.transitionInverseImageAb φ ⟶
      Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
        (S.componentTopology n) S.totalTopology ⋙ S.abelianComponent m :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (S.componentLowerShriekAbAdjunction n).unit
      (S.transitionInverseImageAb φ) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (S.fiberTransitionAb φ)

/-- The canonical map from the inverse image along the transition at a simplex map
`φ : [n] ⟶ [m]` into `g_m^{-1} g_{n!}`: the unit of `g_{n!} ⊣ g_n^{-1}`, followed by the
transition of Stacks 09WF with abelian coefficients, with target written with `restrictAb`. -/
noncomputable def componentSumFormulaLeg' (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) :
    S.transitionInverseImageAb φ ⟶
      Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
        (S.componentTopology n) S.totalTopology ⋙ S.restrictAb m :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (S.componentLowerShriekAbAdjunction' n).unit
      (S.transitionInverseImageAb φ) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (S.fiberTransitionAb' φ)

/-- On an abelian sheaf, the canonical map is the unit of `g_{n!} ⊣ g_n^{-1}` transported along the
transition, followed by the inverse-image transition. -/
@[simp] theorem componentSumFormulaLeg_app (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (X : Sheaf (S.componentTopology n) Ab.{u}) :
    (S.componentSumFormulaLeg φ).app X =
      (S.transitionInverseImageAb φ).map ((S.componentLowerShriekAbAdjunction n).unit.app X) ≫
        (S.fiberTransitionAb φ).app
          ((Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
            (S.componentTopology n) S.totalTopology).obj X) := by
  simp [componentSumFormulaLeg, Functor.whiskerLeft_app]

/-- On an abelian sheaf, the canonical map is the unit of `g_{n!} ⊣ g_n^{-1}` transported along the
transition, followed by the inverse-image transition, stated with `restrictAb`. -/
@[simp] theorem componentSumFormulaLeg_app' (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (X : Sheaf (S.componentTopology n) Ab.{u}) :
    (S.componentSumFormulaLeg' φ).app X =
      (S.transitionInverseImageAb φ).map ((S.componentLowerShriekAbAdjunction' n).unit.app X) ≫
        (S.fiberTransitionAb' φ).app
          ((Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
            (S.componentTopology n) S.totalTopology).obj X) := by
  simp [componentSumFormulaLeg', Functor.whiskerLeft_app]

/-- The transpose of the canonical map, under the adjunction of the simplicial transition, is the
unit of `g_{n!} ⊣ g_n^{-1}` followed by the direct-image transition. -/
theorem homEquiv_componentSumFormulaLeg_app (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (X : Sheaf (S.componentTopology n) Ab.{u}) :
    (S.transitionAdjunctionAb φ).homEquiv X _ ((S.componentSumFormulaLeg φ).app X) =
      (S.componentLowerShriekAbAdjunction n).unit.app X ≫
        (S.restrictTransitionAb φ).app
          ((Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
            (S.componentTopology n) S.totalTopology).obj X) := by
  rw [componentSumFormulaLeg_app, Adjunction.homEquiv_naturality_left]
  exact congrArg (fun g => (S.componentLowerShriekAbAdjunction n).unit.app X ≫ g)
    (S.fiberTransitionAb_adj φ _)

/-- The transpose of the canonical map, under the adjunction of the simplicial transition, is the
unit of `g_{n!} ⊣ g_n^{-1}` followed by the direct-image transition, stated with `restrictAb`. -/
theorem homEquiv_componentSumFormulaLeg_app' (S : SimplicialSiteSituation.{u})
    {n m : SimplexCategory} (φ : n ⟶ m) (X : Sheaf (S.componentTopology n) Ab.{u}) :
    (S.transitionAdjunctionAb φ).homEquiv X _ ((S.componentSumFormulaLeg' φ).app X) =
      (S.componentLowerShriekAbAdjunction' n).unit.app X ≫
        (S.restrictTransitionAb' φ).app
          ((Functor.sheafPullbackConstruction.sheafPullback (S.componentFunctor n) Ab.{u}
            (S.componentTopology n) S.totalTopology).obj X) := by
  rw [componentSumFormulaLeg_app', Adjunction.homEquiv_naturality_left]
  exact congrArg (fun g => (S.componentLowerShriekAbAdjunction' n).unit.app X ≫ g)
    (S.fiberTransitionAb_adj' φ _)

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.SimplicialSite

universe u

open CategoryTheory.SimplicialSiteSituation in
/-- **Stacks 09WG in case (A).** The `φ`th summand inclusion into the abelian sum formula,
followed by the inverse of that formula, is the canonical map attached to `φ`: the unit of
`g_{n!} ⊣ g_n^{-1}` followed by the transition of Stacks 09WF. -/
theorem sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg
    (C : SimplicialSite.{u}) (n m : SimplexCategory) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m =>
          transitionInverseImageAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) ψ) φ ≫
        (componentLowerShriekRestrictionIsoCoproduct C n m).inv =
      componentSumFormulaLeg (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ := by
  refine NatTrans.ext (funext fun X => ?_)
  refine ((transitionAdjunctionAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).homEquiv
    X _).injective ?_
  refine Eq.trans (congrArg ((transitionAdjunctionAb
    (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).homEquiv X _) (Category.comp_id _).symm) ?_
  refine Eq.trans (homEquiv_sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv
    C n m φ X _ (𝟙 _)) ?_
  refine Eq.trans (congrArg (fun g => g ≫ _)
    ((Adjunction.homEquiv_id _ X).trans (Adjunction.comp_unit_app _ _ X))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun g => _ ≫ g)
    (Functor.map_sheafAdjunctionCocontinuous_unit_comp_ranRestrictSheafComparison Ab.{u}
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
      (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n)
      (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m)
      (fun ψ : n ⟶ m => (C.underlying.map ψ).toFunctor)
      (fun ψ => continuousInclusionTransition C ψ)
      (ht := fun ψ => (C.isMorphismOfSites ψ).isContinuous) φ _)) ?_
  exact (homEquiv_componentSumFormulaLeg_app
    (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ X).symm

open CategoryTheory.SimplicialSiteSituation in
/-- **Stacks 09WG in case (A).** The `φ`th summand inclusion into the abelian sum formula,
followed by the inverse of that formula, is the canonical map attached to `φ`: the unit of
`g_{n!} ⊣ g_n^{-1}` followed by the transition of Stacks 09WF, stated with `restrictAb`. -/
theorem sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg'
    (C : SimplicialSite.{u}) (n m : SimplexCategory) (φ : n ⟶ m) :
    Sigma.ι (fun ψ : n ⟶ m =>
          transitionInverseImageAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) ψ) φ ≫
        (componentLowerShriekRestrictionIsoCoproduct C n m).inv =
      componentSumFormulaLeg' (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ := by
  refine NatTrans.ext (funext fun X => ?_)
  refine ((transitionAdjunctionAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).homEquiv
    X _).injective ?_
  refine Eq.trans (congrArg ((transitionAdjunctionAb
    (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ).homEquiv X _) (Category.comp_id _).symm) ?_
  refine Eq.trans (homEquiv_sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv
    C n m φ X _ (𝟙 _)) ?_
  refine Eq.trans (congrArg (fun g => g ≫ _)
    ((Adjunction.homEquiv_id _ X).trans (Adjunction.comp_unit_app _ _ X))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun g => _ ≫ g)
    (Functor.map_sheafAdjunctionCocontinuous_unit_comp_ranRestrictSheafComparison Ab.{u}
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
      (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology
      (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n)
      (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m)
      (fun ψ : n ⟶ m => (C.underlying.map ψ).toFunctor)
      (fun ψ => continuousInclusionTransition C ψ)
      (ht := fun ψ => (C.isMorphismOfSites ψ).isContinuous) φ _)) ?_
  exact (homEquiv_componentSumFormulaLeg_app'
    (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ X).symm

end CategoryTheory.SimplicialSite

add_to_stacks 09WG "summand inclusion is the canonical transition, case (A)"
  CategoryTheory.SimplicialSite.sigma_ι_comp_componentLowerShriekRestrictionIsoCoproduct_inv_eq_leg

end
