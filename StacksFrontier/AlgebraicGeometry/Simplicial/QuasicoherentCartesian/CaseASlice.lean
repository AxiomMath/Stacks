module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaCaseASummand
public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.SliceTransition

/-!
# The transition of a simplicial site of case (A), localized at an object

In case (A) of Stacks 09WE the transition `u_φ : Cₙ ⥤ C_m` of a simplex map `φ : [n] ⟶ [m]` is a
continuous functor. At an object `Q` of `Cₙ` it localizes to `h : Cₙ/Q ⥤ C_m/u_φ(Q)`, and the
canonical arrows `u_φ(Q) ⟶ Q` of the total category give the localized transition
`h^*(M|_Q) ⟶ M|_{u_φ Q}` for modules `M` on the total slice at `Q`, with `h^*` Mathlib's
pullback of sheaves of modules along the localized ring map.

## Main results

* `CategoryTheory.SimplicialSite.CartesianSlice.sliceTransitionA`: the localized transition, as a
  `CategoryTheory.SimplicialSiteSituation.CartesianSlice.SliceTransition`.

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSite.CartesianSlice

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable (C : SimplicialSite.{u}) (O : Sheaf (situation C).totalTopology RingCat.{u})
  {n m : SimplexCategory} (φ : n ⟶ m) (Q : (situation C).component n)

/-- The localized transition functor `Over Q ⥤ Over (u_φ Q)`. -/
abbrev sliceTransition : Over Q ⥤ Over ((transitionFunctorA C φ).obj Q) :=
  Over.post (transitionFunctorA C φ)

/-- The degree-`n` component inclusion, localized at `Q`. -/
abbrev sliceInclusion :
    Over Q ⥤ Over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q) :=
  SimplicialSiteSituation.CartesianSlice.sliceInclusion (situation C) Q

/-- The canonical arrow `u_φ Q ⟶ Q` of the total category. -/
abbrev canonicalArrow :
    (SimplicialSiteSituation.componentFunctor (situation C) m).obj
        ((transitionFunctorA C φ).obj Q) ⟶
      (SimplicialSiteSituation.componentFunctor (situation C) n).obj Q :=
  (transitionNatTransA C φ).app Q

/-- The degree-`m` component inclusion at `u_φ Q`, followed by the canonical arrow. -/
abbrev sliceInclusionAt :
    Over ((transitionFunctorA C φ).obj Q) ⥤
      Over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q) :=
  SimplicialSiteSituation.CartesianSlice.sliceInclusionAt (situation C) (canonicalArrow C φ Q)

/-- The localized ring map. -/
def sliceRingTransition :
    ((situation C).componentRingSheaf O n).over Q ⟶
      ((sliceTransition C φ Q).sheafPushforwardContinuous RingCat.{u}
        (((situation C).componentTopology n).over Q)
        (((situation C).componentTopology m).over ((transitionFunctorA C φ).obj Q))).obj
        (((situation C).componentRingSheaf O m).over ((transitionFunctorA C φ).obj Q)) :=
  ((Over.forget Q).sheafPushforwardContinuous RingCat.{u}
    (((situation C).componentTopology n).over Q)
    ((situation C).componentTopology n)).map (ringTransitionA C O φ)


/-- The arrows `(φ, 𝟙)` localized: a natural transformation `h ⋙ λ ⟶ μ`. -/
def sliceTransitionNatTrans :
    sliceTransition C φ Q ⋙ sliceInclusionAt C φ Q ⟶ sliceInclusion C Q where
  app Y := Over.homMk ((transitionNatTransA C φ).app Y.left)
    ((transitionNatTransA C φ).naturality Y.hom).symm
  naturality _ _ g :=
    Over.OverMorphism.ext ((transitionNatTransA C φ).naturality g.left)

/-- The localized transition followed by the inclusion of the slice at `u_φ(Q)` is continuous
from the degree-`n` component topology at `Q` to the localized total topology. -/
instance isContinuous_sliceTransition_comp_sliceInclusionAt :
    (sliceTransition C φ Q ⋙ sliceInclusionAt C φ Q).IsContinuous
      (((situation C).componentTopology n).over Q) ((situation C).totalTopology.over _) :=
  Functor.isContinuous_comp _ _ _
    (((situation C).componentTopology m).over ((transitionFunctorA C φ).obj Q)) _

/-- The ring map attached to `sliceTransitionNatTrans` is the localized ring map. -/
theorem sliceTransitionNatTrans_ring :
    (𝟙 (((situation C).componentRingSheaf O n).over Q)) ≫
        (Functor.sheafPushforwardContinuousNatTrans (sliceTransitionNatTrans C φ Q) RingCat.{u}
          (((situation C).componentTopology n).over Q) ((situation C).totalTopology.over _)).app
          (O.over _) =
      sliceRingTransition C O φ Q ≫
        ((sliceTransition C φ Q).sheafPushforwardContinuous RingCat.{u}
          (((situation C).componentTopology n).over Q)
          (((situation C).componentTopology m).over ((transitionFunctorA C φ).obj Q))).map
          (𝟙 (((situation C).componentRingSheaf O m).over ((transitionFunctorA C φ).obj Q))) := by
  ext : 2
  rfl


/-- Restriction of modules on the total slice at `Q` to the degree-`n` slice at `Q`. -/
abbrev sliceRestriction :
    SheafOfModules.{u} (O.over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q))
      ⥤ SheafOfModules.{u} (((situation C).componentRingSheaf O n).over Q) :=
  SimplicialSiteSituation.CartesianSlice.sliceRestriction (situation C) O Q

/-- Restriction of modules on the total slice at `Q` to the degree-`m` slice at `u_φ Q`. -/
abbrev sliceRestrictionAt :
    SheafOfModules.{u} (O.over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q))
      ⥤ SheafOfModules.{u}
        (((situation C).componentRingSheaf O m).over ((transitionFunctorA C φ).obj Q)) :=
  SimplicialSiteSituation.CartesianSlice.sliceRestrictionAt (situation C) O (canonicalArrow C φ Q)

/-- The localized direct image along the transition. -/
abbrev slicePushforward :
    SheafOfModules.{u}
        (((situation C).componentRingSheaf O m).over ((transitionFunctorA C φ).obj Q))
      ⥤ SheafOfModules.{u} (((situation C).componentRingSheaf O n).over Q) :=
  SheafOfModules.pushforward.{u} (sliceRingTransition C O φ Q)

/-- Step 1 of the direct transition. -/
def sliceDirectTransition₁ :
    sliceRestriction C O Q ⟶
      SheafOfModules.pushforward.{u} (F := sliceTransition C φ Q ⋙ sliceInclusionAt C φ Q)
        (J := ((situation C).componentTopology n).over Q)
        (K := (situation C).totalTopology.over _)
        ((𝟙 (((situation C).componentRingSheaf O n).over Q)) ≫
        (Functor.sheafPushforwardContinuousNatTrans (sliceTransitionNatTrans C φ Q) RingCat.{u}
          (((situation C).componentTopology n).over Q) ((situation C).totalTopology.over _)).app
          (O.over _)) :=
  SheafOfModules.pushforwardNatTrans.{u} (J := ((situation C).componentTopology n).over Q)
      (K := (situation C).totalTopology.over _)
      (T := ((situation C).componentRingSheaf O n).over Q)
      (S := O.over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q))
      (F := sliceTransition C φ Q ⋙ sliceInclusionAt C φ Q) (G := sliceInclusion C Q)
      (𝟙 (((situation C).componentRingSheaf O n).over Q)) (sliceTransitionNatTrans C φ Q)

/-- The direct form of the localized transition: `μ^* ⟶ Λ ⋙ h_*`. -/
def sliceDirectTransition :
    sliceRestriction C O Q ⟶ sliceRestrictionAt C O φ Q ⋙ slicePushforward C O φ Q :=
  sliceDirectTransition₁ C O φ Q ≫
    (SheafOfModules.pushforwardCongr.{u} (J := ((situation C).componentTopology n).over Q)
        (K := (situation C).totalTopology.over _)
        (S := ((situation C).componentRingSheaf O n).over Q)
        (R := O.over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q))
        (F := sliceTransition C φ Q ⋙ sliceInclusionAt C φ Q)
        (sliceTransitionNatTrans_ring C O φ Q)).hom ≫
      (SheafOfModules.pushforwardComp.{u}
        (J := ((situation C).componentTopology n).over Q)
        (K := ((situation C).componentTopology m).over ((transitionFunctorA C φ).obj Q))
        (K' := (situation C).totalTopology.over _)
        (F := sliceTransition C φ Q) (G := sliceInclusionAt C φ Q)
        (S := ((situation C).componentRingSheaf O n).over Q)
        (R := ((situation C).componentRingSheaf O m).over ((transitionFunctorA C φ).obj Q))
        (R' := O.over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q))
        (sliceRingTransition C O φ Q)
        (𝟙 (((situation C).componentRingSheaf O m).over ((transitionFunctorA C φ).obj Q)))).inv

/-- On sections, the localized direct transition is restriction along the canonical arrows. -/
theorem sliceDirectTransition_app_val_app
    (M : SheafOfModules.{u}
      (O.over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q)))
    (V : (Over Q)ᵒᵖ) (x : ((sliceRestriction C O Q).obj M).val.obj V) :
    ((sliceDirectTransition C O φ Q).app M).val.app V x =
      M.val.map ((sliceTransitionNatTrans C φ Q).app V.unop).op x :=
  rfl

/-- The localized pullback along the transition. -/
abbrev slicePullback :
    SheafOfModules.{u} (((situation C).componentRingSheaf O n).over Q) ⥤
      SheafOfModules.{u}
        (((situation C).componentRingSheaf O m).over ((transitionFunctorA C φ).obj Q)) :=
  SheafOfModules.pullback.{u} (sliceRingTransition C O φ Q)

/-- The localized pullback is left adjoint to the localized direct image. -/
abbrev slicePullbackAdj : slicePullback C O φ Q ⊣ slicePushforward C O φ Q :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (sliceRingTransition C O φ Q)

/-- **The localized transition** `h^* μ^* ⟶ Λ`: the mate of the direct form. -/
def sliceTransitionModules :
    sliceRestriction C O Q ⋙ slicePullback C O φ Q ⟶ sliceRestrictionAt C O φ Q :=
  Functor.whiskerRight (sliceDirectTransition C O φ Q) (slicePullback C O φ Q) ≫
    Functor.whiskerLeft (sliceRestrictionAt C O φ Q) (slicePullbackAdj C O φ Q).counit

/-- The localized transition at one module is the transpose of the localized direct transition. -/
theorem sliceTransitionModules_app
    (M : SheafOfModules.{u}
      (O.over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q))) :
    (sliceTransitionModules C O φ Q).app M =
      ((slicePullbackAdj C O φ Q).homEquiv _ _).symm ((sliceDirectTransition C O φ Q).app M) := by
  rw [Adjunction.homEquiv_counit]
  rfl


/-! ### The localized transition on the structure sheaf -/

/-- The degree-`n` restriction of the structure sheaf of the total slice is the structure sheaf. -/
abbrev sliceRestrictionUnitHom :
    SheafOfModules.unit (((situation C).componentRingSheaf O n).over Q) ⟶
      (sliceRestriction C O Q).obj (SheafOfModules.unit _) :=
  SimplicialSiteSituation.CartesianSlice.sliceRestrictionUnitHom (situation C) O Q

/-- The degree-`m` restriction of the structure sheaf of the total slice is the structure sheaf. -/
abbrev sliceRestrictionAtUnitHom :
    SheafOfModules.unit
        (((situation C).componentRingSheaf O m).over ((transitionFunctorA C φ).obj Q)) ⟶
      (sliceRestrictionAt C O φ Q).obj (SheafOfModules.unit _) :=
  SimplicialSiteSituation.CartesianSlice.sliceRestrictionAtUnitHom (situation C) O
    (canonicalArrow C φ Q)

/-- The localized ring map, read on the structure sheaf. -/
abbrev slicePushforwardUnitHom :
    SheafOfModules.unit (((situation C).componentRingSheaf O n).over Q) ⟶
      (slicePushforward C O φ Q).obj (SheafOfModules.unit _) :=
  SheafOfModules.unitToPushforwardObjUnit (sliceRingTransition C O φ Q)

/-- On the structure sheaf, the localized direct transition is the localized ring map. -/
theorem sliceDirectTransition_app_unit :
    sliceRestrictionUnitHom C O Q ≫ (sliceDirectTransition C O φ Q).app (SheafOfModules.unit _) =
      slicePushforwardUnitHom C O φ Q ≫
        (slicePushforward C O φ Q).map (sliceRestrictionAtUnitHom C O φ Q) := by
  ext V : 3
  rfl

/-- **The localized transition is invertible on the structure sheaf.** -/
theorem isIso_sliceTransitionModules_app_unit :
    IsIso ((sliceTransitionModules C O φ Q).app (SheafOfModules.unit _)) := by
  have hdir : (sliceDirectTransition C O φ Q).app (SheafOfModules.unit _) =
      inv (sliceRestrictionUnitHom C O Q) ≫ (slicePushforwardUnitHom C O φ Q ≫
        (slicePushforward C O φ Q).map (sliceRestrictionAtUnitHom C O φ Q)) := by
    rw [← sliceDirectTransition_app_unit, IsIso.inv_hom_id_assoc]
  rw [sliceTransitionModules_app, hdir, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm,
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardObjUnit]
  infer_instance


/-! ### The localized transition on a presented module -/

/-- The localized transition of case (A) at the canonical arrow `u_φ Q ⟶ Q`. -/
def sliceTransitionA :
    SimplicialSiteSituation.CartesianSlice.SliceTransition (O := O) (canonicalArrow C φ Q) where
  Φ := slicePullback C O φ Q
  preservesColimits := (slicePullbackAdj C O φ Q).leftAdjoint_preservesColimits
  τ := sliceTransitionModules C O φ Q
  isIso_τ_app_unit := isIso_sliceTransitionModules_app_unit C O φ Q

/-- **The localized transition is invertible on a module with a global presentation.** -/
theorem isIso_sliceTransitionModules_of_presentation
    {M : SheafOfModules.{u}
      (O.over ((SimplicialSiteSituation.componentFunctor (situation C) n).obj Q))}
    (P : M.Presentation) :
    IsIso ((sliceTransitionModules C O φ Q).app M) :=
  (sliceTransitionA C O φ Q).isIso_τ_app_of_presentation P

end CategoryTheory.SimplicialSite.CartesianSlice
