module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetLocalized
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardFinalPresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationIsIso
public import StacksFrontier.CategoryTheory.Sites.ArrowCoverTransport
public import StacksFrontier.CategoryTheory.Sites.CoversTopRefinement
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.SliceTransition

/-!
# Invertibility of transitions of restrictions, checked on slices

Consider a morphism of ringed sites `f : X ⟶ Y` given by `u : Y.C ⥤ X.C`, continuous functors
`G : X.C ⥤ T`, `G' : Y.C ⥤ T` to a site `T` with a sheaf of rings `R`, and `τ : u ⋙ G ⟶ G'`. The
transposed transition `θ : f^*(ρ_{G'}M) ⟶ ρ_G M` localizes at every `V : Y.C` to a transition
`θ_V : f'^*(q^*N) ⟶ p^*N` on the slice `T/G'(V)`. This file proves the two directions of the
local-to-global argument of Stacks 0D7M:

* the restriction of `θ` at `M` to `X.C/u(V)` is invertible exactly when `θ_V` is invertible at
  `M|_{G'(V)}`;
* `θ_V` is invertible at every module with a global presentation once `θ` is invertible at the
  structure sheaf, both sides preserving colimits when `G` and `G'` are cocontinuous;
* hence `θ` is invertible at `M` as soon as the objects `u(V)` with `M|_{G'(V)}` globally presented
  cover the final object of `X.C`;
* `θ_V` carries invertibility of `q^*c` to invertibility of `p^*c` for a morphism `c`
  between modules at which it is invertible;
* and a global presentation of `(ρ_{G'}M)|_V` lifts to a globally presented module `P` on
  `T/G'(V)` with a map `c : P ⟶ M|_{G'(V)}` such that `q^*c` is invertible.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.isIso_sliceTransitionPullback_app_iff`
* `AlgebraicGeometry.RingedSite.Hom.isIso_sliceTransitionPullback_app_of_hasGlobalPresentation`
* `AlgebraicGeometry.RingedSite.Hom.isIso_siteTransitionPullback_app_of_coversTop`
* `AlgebraicGeometry.RingedSite.Hom.isIso_siteTransitionPullback_app_of_locally`
* `AlgebraicGeometry.RingedSite.Hom.isIso_sliceRight_map_of_isIso`
* `AlgebraicGeometry.RingedSite.exists_hasGlobalPresentation_isIso_sliceLeft_map`

## References

* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Sheaves.ToposPullback Opposite

universe u

namespace AlgebraicGeometry.RingedSite.Hom

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable {T : Type u} [SmallCategory T] {JT : GrothendieckTopology T} (R : Sheaf JT RingCat.{u})
  {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) {G : X.C ⥤ T} {G' : Y.C ⥤ T}
  [hG : G.IsContinuous X.J JT] [hG' : G'.IsContinuous Y.J JT] (τ : f.u ⋙ G ⟶ G')
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) ⟶
    (G.sheafPushforwardContinuous RingCat.{u} X.J JT).obj R)
  (ψ' : (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O) ⟶
    (G'.sheafPushforwardContinuous RingCat.{u} Y.J JT).obj R)
  (hτ : f.RingCompatible R τ ψ ψ')

section Slice

variable (V : Y.C)

/-- The localized transposed transition `f'^*(q^*N) ⟶ p^*N` of modules on the slice `T/G'(V)`,
where `q = Over.post G'` and `p = Over.post G ⋙ Over.map τ_V`. -/
noncomputable abbrev sliceTransitionPullback :=
  (f.localized V).siteTransitionPullback (hG := f.isContinuous_sliceRight τ V)
    (hG' := isContinuous_sliceLeft V) (sliceRing R V) (f.sliceTransitionNatTrans τ V)
    (f.sliceRingMapRight R τ V ψ) (sliceRingMapLeft R V ψ')
    (f.ringCompatible_localized R τ V ψ ψ' hτ)

/-- The restriction to `X.C/u(V)` of the transposed transition at `M` is invertible exactly when
the localized transition is invertible at `M|_{G'(V)}`. -/
theorem isIso_sliceTransitionPullback_app_iff (M : SheafOfModules.{u} R) :
    IsIso ((f.sliceTransitionPullback R τ ψ ψ' hτ V).app
        ((restrictionModules (JT.over (G'.obj V)) JT (Over.forget (G'.obj V)) R).obj M)) ↔
      IsIso ((X.overRestrictionModules (f.u.obj V)).map
        ((f.siteTransitionPullback R τ ψ ψ' hτ).app M)) := by
  have h := f.localizedPullbackMate_comp_siteTransition R τ V ψ ψ' hτ M
  have e₁ : (f.sliceTransitionPullback R τ ψ ψ' hτ V).app
        ((restrictionModules (JT.over (G'.obj V)) JT (Over.forget (G'.obj V)) R).obj M) =
      ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
        (f.localized V).ringedToposHom).homEquiv _ _).symm
          ((f.sliceTransition R τ V ψ ψ' hτ).app
            ((restrictionModules (JT.over (G'.obj V)) JT (Over.forget (G'.obj V)) R).obj M)) :=
    (f.localized V).siteTransitionPullback_app (hG := f.isContinuous_sliceRight τ V)
      (hG' := isContinuous_sliceLeft V) (sliceRing R V) (f.sliceTransitionNatTrans τ V)
      (f.sliceRingMapRight R τ V ψ) (sliceRingMapLeft R V ψ')
      (f.ringCompatible_localized R τ V ψ ψ' hτ) _
  rw [← f.siteTransitionPullback_app R τ ψ ψ' hτ M] at h
  have := f.isIso_localizedPullbackMate V
  have : IsIso ((f.localizedPullbackMate V).app
      ((SheafOfModules.pushforward.{u} (F := G') ψ').obj M)) :=
    inferInstanceAs (IsIso (NatTrans.app (f.localizedPullbackMate V) _))
  rw [e₁, ← isIso_comp_right_iff _ (eqToHom (f.sliceRight_obj_restriction R τ V ψ M)), ← h,
    isIso_comp_left_iff, isIso_comp_left_iff]

/-- The localized transition is invertible at the structure sheaf of the slice as soon as the
transition is invertible at the structure sheaf. -/
theorem isIso_sliceTransitionPullback_app_unit
    (hunit : IsIso ((f.siteTransitionPullback R τ ψ ψ' hτ).app (SheafOfModules.unit R))) :
    IsIso ((f.sliceTransitionPullback R τ ψ ψ' hτ V).app
      (SheafOfModules.unit (sliceRing R V))) := by
  have hA : (restrictionModules (JT.over (G'.obj V)) JT (Over.forget (G'.obj V)) R).obj
      (SheafOfModules.unit R) = SheafOfModules.unit (sliceRing R V) := rfl
  have h := (f.isIso_sliceTransitionPullback_app_iff R τ ψ ψ' hτ V (SheafOfModules.unit R)).mpr
    inferInstance
  exact Eq.mp (congrArg (fun A ↦ IsIso ((f.sliceTransitionPullback R τ ψ ψ' hτ V).app A)) hA) h

/-- For a morphism `c : P ⟶ N` of modules on `T/G'(V)` at whose ends the localized transition is
invertible, if the restriction `q^*c` to `Y.C/V` is invertible then so is the restriction `p^*c`
to `X.C/u(V)`. -/
theorem isIso_sliceRight_map_of_isIso {P N : SheafOfModules.{u} (sliceRing R V)} (c : P ⟶ N)
    (hc : haveI := isContinuous_sliceLeft (G' := G') (hG' := hG') V
      IsIso ((SheafOfModules.pushforward.{u} (F := Over.post (X := V) G') (J := (Y.over V).J)
        (K := JT.over (G'.obj V)) (sliceRingMapLeft R V ψ')).map c))
    (hP : IsIso ((f.sliceTransitionPullback R τ ψ ψ' hτ V).app P))
    (hN : IsIso ((f.sliceTransitionPullback R τ ψ ψ' hτ V).app N)) :
    haveI := f.isContinuous_sliceRight (hG := hG) τ V
    IsIso ((SheafOfModules.pushforward.{u} (F := Over.post (X := f.u.obj V) G ⋙ Over.map (τ.app V))
        (J := (X.over (f.u.obj V)).J) (K := JT.over (G'.obj V))
        (f.sliceRingMapRight R τ V ψ)).map c) := by
  have := isContinuous_sliceLeft (G' := G') (hG' := hG') V
  have := f.isContinuous_sliceRight (hG := hG) τ V
  have e := (f.sliceTransitionPullback R τ ψ ψ' hτ V).naturality c
  have : IsIso ((f.sliceTransitionPullback R τ ψ ψ' hτ V).app P ≫
      (SheafOfModules.pushforward.{u} (F := Over.post (X := f.u.obj V) G ⋙ Over.map (τ.app V))
        (J := (X.over (f.u.obj V)).J) (K := JT.over (G'.obj V))
        (f.sliceRingMapRight R τ V ψ)).map c) := by
    rw [← e]
    exact inferInstanceAs (IsIso (
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
        ((f.localized V).ringedToposHom).toModulesHom).map _ ≫ _))
  exact IsIso.of_isIso_comp_left ((f.sliceTransitionPullback R τ ψ ψ' hτ V).app P) _

variable [hGc : G.IsCocontinuous X.J JT] [hG'c : G'.IsCocontinuous Y.J JT]

/-- If the transition is invertible at the structure sheaf and `G`, `G'` are cocontinuous, then the
localized transition is invertible at every module on `T/G'(V)` with a global presentation. -/
theorem isIso_sliceTransitionPullback_app_of_hasGlobalPresentation
    (hunit : IsIso ((f.siteTransitionPullback R τ ψ ψ' hτ).app (SheafOfModules.unit R)))
    {N : SheafOfModules.{u} (sliceRing R V)} (hN : N.HasGlobalPresentation) :
    IsIso ((f.sliceTransitionPullback R τ ψ ψ' hτ V).app N) := by
  have := isContinuous_sliceLeft (G' := G') (hG' := hG') V
  have := f.isContinuous_sliceRight (hG := hG) τ V
  have : (Over.post (X := V) G').IsCocontinuous (Y.over V).J (JT.over (G'.obj V)) :=
    inferInstanceAs ((Over.post (X := V) G').IsCocontinuous (Y.J.over V) (JT.over (G'.obj V)))
  have : (Over.post (X := f.u.obj V) G ⋙ Over.map (τ.app V)).IsCocontinuous
      (X.over (f.u.obj V)).J (JT.over (G'.obj V)) :=
    isCocontinuous_comp (Over.post (X := f.u.obj V) G) (Over.map (τ.app V))
      (X.J.over (f.u.obj V)) (JT.over (G.obj (f.u.obj V))) (L := JT.over (G'.obj V))
  have h₁ : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pushforward.{u} (F := Over.post (X := V) G') (J := (Y.over V).J)
        (K := JT.over (G'.obj V)) (sliceRingMapLeft R V ψ')) :=
    Stacks.SheafOfModules.pushforward_preservesColimits _ _
  have h₂ : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pushforward.{u} (F := Over.post (X := f.u.obj V) G ⋙ Over.map (τ.app V))
        (J := (X.over (f.u.obj V)).J) (K := JT.over (G'.obj V)) (f.sliceRingMapRight R τ V ψ)) :=
    Stacks.SheafOfModules.pushforward_preservesColimits _ _
  have h₃ : PreservesColimitsOfSize.{u, u}
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u, u, u, u, u, u}
        ((f.localized V).ringedToposHom).toModulesHom) :=
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
      (f.localized V).ringedToposHom).leftAdjoint_preservesColimits
  exact Stacks.SheafOfModules.isIso_app_of_hasGlobalPresentation _
    (f.isIso_sliceTransitionPullback_app_unit R τ ψ ψ' hτ V hunit) hN

end Slice

variable [hGc : G.IsCocontinuous X.J JT] [hG'c : G'.IsCocontinuous Y.J JT]

/-- If the transposed transition is invertible at the structure sheaf and the objects `u(V i)`, for
which `M|_{G'(V i)}` has a global presentation, cover the final object of `X.C`, then the
transposed transition is invertible at `M`. -/
theorem isIso_siteTransitionPullback_app_of_coversTop
    (hunit : IsIso ((f.siteTransitionPullback R τ ψ ψ' hτ).app (SheafOfModules.unit R)))
    (M : SheafOfModules.{u} R) {ι : Type*} {V : ι → Y.C}
    (hV : X.J.CoversTop fun i ↦ f.u.obj (V i))
    (hM : ∀ i, ((restrictionModules (JT.over (G'.obj (V i))) JT (Over.forget (G'.obj (V i)))
      R).obj M).HasGlobalPresentation) :
    IsIso ((f.siteTransitionPullback R τ ψ ψ' hτ).app M) := by
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop hV _ fun i W g ↦ ?_
  have h := (f.isIso_sliceTransitionPullback_app_iff R τ ψ ψ' hτ (V i) M).mp
    (f.isIso_sliceTransitionPullback_app_of_hasGlobalPresentation R τ ψ ψ' hτ (V i) hunit (hM i))
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward _ _ h
    (op (Over.mk g))

/-- If the transposed transition is invertible at the structure sheaf and every object of `Y.C` has
a covering family by objects `W` with `M|_{G'(W)}` globally presented, then the transposed
transition is invertible at `M`. -/
theorem isIso_siteTransitionPullback_app_of_locally
    (hunit : IsIso ((f.siteTransitionPullback R τ ψ ψ' hτ).app (SheafOfModules.unit R)))
    (M : SheafOfModules.{u} R)
    (hM : ∀ U : Y.C, ∃ S : Presieve U, Sieve.generate S ∈ Y.J U ∧ ∀ ⦃W : Y.C⦄ (g : W ⟶ U), S g →
      ((restrictionModules (JT.over (G'.obj W)) JT (Over.forget (G'.obj W)) R).obj
        M).HasGlobalPresentation) :
    IsIso ((f.siteTransitionPullback R τ ψ ψ' hτ).app M) := by
  have := f.isMorphismOfSites.isContinuous
  have := f.isMorphismOfSites.preservesFiniteLimits
  exact f.isIso_siteTransitionPullback_app_of_coversTop R τ ψ ψ' hτ hunit M
    (GrothendieckTopology.coversTop_obj_subtype f.u Y.J X.J
      (Stacks.Sites.coversTop_obj_of_preservesFiniteLimits f.u Y.J X.J) _ hM)
    (fun i ↦ i.2)

end AlgebraicGeometry.RingedSite.Hom

namespace AlgebraicGeometry.RingedSite

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable {T : Type u} [SmallCategory T] {JT : GrothendieckTopology T} (R : Sheaf JT RingCat.{u})
  {Y : RingedSite.{u, u, u}} {G' : Y.C ⥤ T} [hG' : G'.IsContinuous Y.J JT]
  [hG'c : G'.IsCocontinuous Y.J JT]
  (ψ' : (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O) ⟶
    (G'.sheafPushforwardContinuous RingCat.{u} Y.J JT).obj R)

/-- If the ring map `O_Y ⟶ G'^s R` is invertible and the restriction `(ρ_{G'}M)|_V` has a global
presentation, there is a globally presented module `P` on `T/G'(V)` with a map
`c : P ⟶ M|_{G'(V)}` whose restriction `q^*c` along `q = Over.post G'` is invertible. -/
theorem exists_hasGlobalPresentation_isIso_sliceLeft_map (hψ' : IsIso ψ') (V : Y.C)
    (M : SheafOfModules.{u} R)
    (hM : ((Y.overRestrictionModules V).obj
      ((SheafOfModules.pushforward.{u} (F := G') ψ').obj M)).HasGlobalPresentation) :
    ∃ (P : SheafOfModules.{u} (Hom.sliceRing R V))
      (c : P ⟶ (restrictionModules (JT.over (G'.obj V)) JT (Over.forget (G'.obj V)) R).obj M),
      P.HasGlobalPresentation ∧
        haveI := Hom.isContinuous_sliceLeft (G' := G') (hG' := hG') V
        IsIso ((SheafOfModules.pushforward.{u} (F := Over.post (X := V) G') (J := (Y.over V).J)
          (K := JT.over (G'.obj V)) (Hom.sliceRingMapLeft R V ψ')).map c) := by
  have := Hom.isContinuous_sliceLeft (G' := G') (hG' := hG') V
  have : (Over.post (X := V) G').IsCocontinuous (Y.over V).J (JT.over (G'.obj V)) :=
    inferInstanceAs ((Over.post (X := V) G').IsCocontinuous (Y.J.over V) (JT.over (G'.obj V)))
  have := hψ'
  have : IsIso (Hom.sliceRingMapLeft R V ψ') := Functor.map_isIso _ _
  exact Stacks.SheafOfModules.exists_hasGlobalPresentation_isIso_pushforward_map
    (Over.post (X := V) G') (Hom.sliceRingMapLeft R V ψ') hM

end AlgebraicGeometry.RingedSite

end
