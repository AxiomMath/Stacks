module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCommShift
public import StacksFrontier.AlgebraicGeometry.QcohShortExact.MayerVietorisInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.RestrictionOfKInjectives
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# The Mayer--Vietoris triangle with the units of the derived adjunctions as legs

Let `X` be a scheme covered by two opens `U` and `V`, and write `j_W : W ⟶ X` for the inclusion of
an open subscheme.  For `K` in `D(𝒪_X)` there is a distinguished triangle

`K ⟶ Rj_{U*}Lj_U^*K ⊞ Rj_{V*}Lj_V^*K ⟶ Rj_{U∩V*}Lj_{U∩V}^*K ⟶ K⟦1⟧`

whose first map is the pair of units of the derived adjunctions `Lj_U^* ⊣ Rj_{U*}` and
`Lj_V^* ⊣ Rj_{V*}`, and whose second map is the difference of the two transition maps, each of
which carries the unit of the larger open to the unit of the smaller one.

## Main definitions

* `Stacks.Cohomology.DerivedMayerVietoris.restrictPush`: the endofunctor `Rj_* Lj^*` of the
  derived category attached to an open immersion of ringed spaces.
* `Stacks.Cohomology.DerivedMayerVietoris.transition`: the transition
  `Rj_* Lj^* ⟶ Rk_* Lk^*` attached to a factorization `k = i ≫ j` of open immersions.

## Main results

* `Stacks.Cohomology.DerivedMayerVietoris.unit_comp_transition`: the transition carries the unit
  of `j` to the unit of `k`.
* `Stacks.Cohomology.DerivedMayerVietoris.hom_ext_of_derivedPullback`: a morphism into
  `Rj_* M` is determined by its restriction along `j`.

## References

* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open _root_.AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology.DerivedMayerVietoris

attribute [local instance] HasDerivedCategory.standard

section OpenImmersion

variable {U X : RingedSpace.{u, u}} (j : U ⟶ X)

/-- The endofunctor `Rj_* Lj^*` of `D(𝒪_X)` attached to a morphism `j : U ⟶ X`. -/
abbrev restrictPush :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  derivedPullback j ⋙ derivedPushforward j

/-- The unit `K ⟶ Rj_* Lj^* K` of the derived adjunction. -/
abbrev unit : 𝟭 _ ⟶ restrictPush j := (derivedAdjunction j).unit

/-- A morphism into `Rj_* M` is determined by its restriction along `j`. -/
theorem hom_ext_of_derivedPullback {N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {M : DerivedCategory (SheafOfModules.{u} (structureSheafRing U))}
    (x y : N ⟶ (derivedPushforward j).obj M)
    (h : (derivedPullback j).map x = (derivedPullback j).map y) : x = y := by
  apply ((derivedAdjunction j).homEquiv N M).symm.injective
  simp only [Adjunction.homEquiv_counit, h]

variable [SheafedSpace.IsOpenImmersion j]

/-- For an open immersion `j`, restricting the unit `K ⟶ Rj_* Lj^* K` along `j` gives an
isomorphism. -/
theorem isIso_derivedPullback_map_unit
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso ((derivedPullback j).map ((unit j).app K)) := by
  have := Stacks.Cohomology.DerivedBaseChange.isIso_derivedAdjunction_counit_of_isOpenImmersion j
  have : IsIso ((derivedAdjunction j).counit.app ((derivedPullback j).obj K)) :=
    NatIso.isIso_app_of_isIso _ _
  exact IsIso.of_isIso_fac_right (hh := IsIso.id _)
    ((derivedAdjunction j).left_triangle_components K)

end OpenImmersion

section Factorization

variable {W U X : RingedSpace.{u, u}} (i : W ⟶ U) (j : U ⟶ X) (k : W ⟶ X) (hk : i ≫ j = k)
  [SheafedSpace.IsOpenImmersion i] [SheafedSpace.IsOpenImmersion j]

omit [SheafedSpace.IsOpenImmersion i] in
include hk in
/-- For open immersions `k = i ≫ j`, restricting the unit of `j` along `k` gives an
isomorphism. -/
theorem isIso_derivedPullback_map_unit_of_comp
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso ((derivedPullback k).map ((unit j).app K)) := by
  subst hk
  have h := ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical i j).hom.naturality
    ((unit j).app K))
  have := isIso_derivedPullback_map_unit j K
  have : IsIso ((derivedPullback j ⋙ derivedPullback i).map ((unit j).app K)) :=
    (inferInstance : IsIso ((derivedPullback i).map ((derivedPullback j).map ((unit j).app K))))
  exact IsIso.of_isIso_fac_left h.symm

/-- **The transition `Rj_* Lj^* K ⟶ Rk_* Lk^* K`** for a factorization `k = i ≫ j` of open
immersions: the transpose, under `Lk^* ⊣ Rk_*`, of the inverse of the restriction along `k` of
the unit of `j`. -/
def transitionApp (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (restrictPush j).obj K ⟶ (restrictPush k).obj K :=
  have := isIso_derivedPullback_map_unit_of_comp i j k hk K
  (derivedAdjunction k).homEquiv _ _ (inv ((derivedPullback k).map ((unit j).app K)))

omit [SheafedSpace.IsOpenImmersion i] in
/-- The transition carries the unit of `j` to the unit of `k`. -/
theorem unit_comp_transitionApp
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (unit j).app K ≫ transitionApp i j k hk K = (unit k).app K := by
  have := isIso_derivedPullback_map_unit_of_comp i j k hk K
  rw [transitionApp, ← Adjunction.homEquiv_naturality_left, IsIso.hom_inv_id,
    Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

omit [SheafedSpace.IsOpenImmersion i] in
/-- The restriction along `k` of the transition is an isomorphism. -/
theorem isIso_derivedPullback_map_transitionApp [SheafedSpace.IsOpenImmersion k]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    IsIso ((derivedPullback k).map (transitionApp i j k hk K)) := by
  have := isIso_derivedPullback_map_unit_of_comp i j k hk K
  have := isIso_derivedPullback_map_unit k K
  exact IsIso.of_isIso_fac_left <| by
    rw [← Functor.map_comp, unit_comp_transitionApp i j k hk K]

/-- The transition is natural in the object. -/
def transition [SheafedSpace.IsOpenImmersion k] : restrictPush j ⟶ restrictPush k where
  app K := transitionApp i j k hk K
  naturality K L u := by
    apply hom_ext_of_derivedPullback k
    have hK := isIso_derivedPullback_map_unit_of_comp i j k hk K
    rw [← cancel_epi ((derivedPullback k).map ((unit j).app K)), ← Functor.map_comp,
      ← Functor.map_comp]
    congr 1
    rw [reassoc_of% unit_comp_transitionApp i j k hk K]
    refine ((unit j).naturality_assoc u _).symm.trans ?_
    rw [unit_comp_transitionApp]
    exact (unit k).naturality u

omit [SheafedSpace.IsOpenImmersion i] in
/-- The component of `transition` at `K` is `transitionApp`. -/
@[simp]
theorem transition_app [SheafedSpace.IsOpenImmersion k]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (transition i j k hk).app K = transitionApp i j k hk K := rfl

omit [SheafedSpace.IsOpenImmersion i] in
/-- The transition carries the unit of `j` to the unit of `k`, as natural transformations. -/
theorem unit_comp_transition [SheafedSpace.IsOpenImmersion k] :
    unit j ≫ transition i j k hk = unit k := by
  ext K
  exact unit_comp_transitionApp i j k hk K

end Factorization

section Modules

open RingedSpaceModuleAdjunction Stacks.AlgebraicGeometry.RelativeMayerVietoris

variable {X : Scheme.{u}}

/-- The morphism of ringed spaces underlying the inclusion of an open subscheme. -/
abbrev incl (Z : X.Opens) := Z.ι.toLRSHom.toShHom


/-- Restriction of modules to an open subscheme is isomorphic to the pullback along the underlying
morphism of ringed spaces. -/
def restrictIso (Z : X.Opens) :
    Scheme.Modules.restrictFunctor Z.ι ≅ modulePullback (incl Z) :=
  (Scheme.Modules.restrictAdjunction Z.ι).leftAdjointUniq
    (modulePullbackPushforwardAdjunction (incl Z))

/-- The endofunctor `j_* j^*` of `𝒪_X`-modules attached to an open subscheme, in the
ringed-space vocabulary. -/
abbrev pushPull (Z : X.Opens) : X.Modules ⥤ X.Modules :=
  modulePullback (incl Z) ⋙ modulePushforward (incl Z)

/-- Pullback of modules along the inclusion of an open subscheme is additive. -/
instance modulePullback_additive (Z : X.Opens) : (modulePullback (incl Z)).Additive :=
  (modulePullbackPushforwardAdjunction (incl Z)).left_adjoint_additive

/-- Pushforward of modules along the inclusion of an open subscheme is additive. -/
instance modulePushforward_additive (Z : X.Opens) : (modulePushforward (incl Z)).Additive :=
  (modulePullbackPushforwardAdjunction (incl Z)).right_adjoint_additive

/-- The endofunctor `j_* j^*` is additive. -/
instance pushPull_additive (Z : X.Opens) : (pushPull Z).Additive :=
  ⟨fun {_ _} f g =>
    (modulePullback (incl Z) ⋙ modulePushforward (incl Z)).map_add (f := f) (g := g)⟩

/-- The unit `F ⟶ j_* j^* F`. -/
abbrev pushPullUnit (Z : X.Opens) : 𝟭 X.Modules ⟶ pushPull Z :=
  (modulePullbackPushforwardAdjunction (incl Z)).unit

/-- `j_{Z*}(F|_Z)` in the scheme vocabulary is `j_* j^* F` in the ringed-space vocabulary. -/
def pushRestrictIso (Z : X.Opens) :
    Scheme.Modules.restrictFunctor Z.ι ⋙ Scheme.Modules.pushforward Z.ι ≅ pushPull Z :=
  Functor.isoWhiskerRight (restrictIso Z) (modulePushforward (incl Z))

/-- Under `pushRestrictIso`, the unit of the restriction adjunction is the unit `F ⟶ j_* j^* F`. -/
theorem unit_pushRestrictIso (Z : X.Opens) (F : X.Modules) :
    (Scheme.Modules.restrictAdjunction Z.ι).unit.app F ≫ (pushRestrictIso Z).hom.app F =
      (pushPullUnit Z).app F :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ F

/-- The unit of the restriction to `Z` followed by the restriction from `Z` to `Z' ≤ Z` is the
unit of the restriction to `Z'`. -/
@[reassoc]
theorem restrictAdjunction_unit_comp_resPush (F : X.Modules) {Z Z' : X.Opens} (h : Z' ≤ Z) :
    (Scheme.Modules.restrictAdjunction Z.ι).unit.app F ≫ resPush F h =
      (Scheme.Modules.restrictAdjunction Z'.ι).unit.app F := by
  refine Scheme.Modules.hom_ext _ _ fun T => ?_
  simp only [Scheme.Modules.Hom.comp_app, resPush_app,
    Scheme.Modules.restrictAdjunction_unit_app_app]
  dsimp only [Scheme.Modules.pushforward_obj_obj, Scheme.Modules.restrict_obj, Functor.id_obj,
    Functor.comp_obj]
  rw [← Functor.map_comp]
  rfl

/-- The restriction morphisms `j_{Z*}(F|_Z) ⟶ j_{Z'*}(F|_{Z'})`, natural in the module. -/
def resPushNat {Z Z' : X.Opens} (h : Z' ≤ Z) :
    Scheme.Modules.restrictFunctor Z.ι ⋙ Scheme.Modules.pushforward Z.ι ⟶
      Scheme.Modules.restrictFunctor Z'.ι ⋙ Scheme.Modules.pushforward Z'.ι where
  app F := resPush F h
  naturality F G φ := by
    refine Scheme.Modules.hom_ext _ _ fun T => ?_
    rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, resPush_app, resPush_app]
    exact (φ.mapPresheaf.naturality (Opposite.op (homOfLE (image_preimage_mono h T)))).symm

/-- The restriction from `Z` to `Z' ≤ Z`, in the ringed-space vocabulary. -/
def pushPullTransition {Z Z' : X.Opens} (h : Z' ≤ Z) : pushPull Z ⟶ pushPull Z' :=
  (pushRestrictIso Z).inv ≫ resPushNat h ≫ (pushRestrictIso Z').hom

/-- The transition from `Z` to `Z' ≤ Z` carries the unit of `Z` to the unit of `Z'`. -/
theorem unit_comp_pushPullTransition {Z Z' : X.Opens} (h : Z' ≤ Z) (F : X.Modules) :
    (pushPullUnit Z).app F ≫ (pushPullTransition h).app F = (pushPullUnit Z').app F := by
  rw [← unit_pushRestrictIso, ← unit_pushRestrictIso]
  simp only [pushPullTransition, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  exact restrictAdjunction_unit_comp_resPush_assoc F h _

end Modules

section ModuleSequence

open RingedSpaceModuleAdjunction Stacks.AlgebraicGeometry.RelativeMayerVietoris

variable {X : Scheme.{u}} (U V : X.Opens)

/-- The unit of the restriction to an open containing every other open is invertible. -/
theorem isIso_restrictAdjunction_unit_app_of_eq_top {Z : X.Opens} (hZ : Z = ⊤) (F : X.Modules) :
    IsIso ((Scheme.Modules.restrictAdjunction Z.ι).unit.app F) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro T
  have hT : Z.ι ''ᵁ (Z.ι ⁻¹ᵁ T) = T := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, hZ, top_inf_eq]
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  have h2 : homOfLE (Z.ι.image_preimage_le T) = eqToHom hT := rfl
  rw [h2, eqToHom_op]
  exact CategoryTheory.Functor.map_isIso _ _

/-- **The Mayer–Vietoris short complex of a module**, `F ⟶ j_{U*}j_U^*F ⊞ j_{V*}j_V^*F ⟶
j_{U∩V*}j_{U∩V}^*F`, with the units as first map and the difference of the two transitions as
second map. -/
def mvShort (F : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (biprod.lift ((pushPullUnit U).app F) ((pushPullUnit V).app F))
    (biprod.desc ((pushPullTransition (inf_le_left : U ⊓ V ≤ U)).app F)
      (-(pushPullTransition (inf_le_right : U ⊓ V ≤ V)).app F)) (by
    rw [biprod.lift_desc, unit_comp_pushPullTransition, Preadditive.comp_neg,
      unit_comp_pushPullTransition, add_neg_cancel])

/-- Under the inverse of `pushRestrictIso`, the unit `F ⟶ j_* j^* F` is the unit of the
restriction adjunction. -/
theorem unit_comp_pushRestrictIso_inv (Z : X.Opens) (F : X.Modules) :
    (pushPullUnit Z).app F ≫ (pushRestrictIso Z).inv.app F =
      (Scheme.Modules.restrictAdjunction Z.ι).unit.app F := by
  rw [← unit_pushRestrictIso, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- Under the inverse of `pushRestrictIso`, the transition from `Z` to `Z' ≤ Z` is `resPush`. -/
theorem pushPullTransition_comp_pushRestrictIso_inv {Z Z' : X.Opens} (h : Z' ≤ Z)
    (F : X.Modules) :
    (pushPullTransition h).app F ≫ (pushRestrictIso Z').inv.app F =
      (pushRestrictIso Z).inv.app F ≫ resPush F h := by
  simp only [pushPullTransition, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id]
  rfl

/-- The first map of `mvShort` agrees with `mvRes` under the identifications of the terms. -/
theorem mvShortIso_comm₁ (F : X.Modules) :
    (Scheme.Modules.restrictAdjunction (U ⊔ V).ι).unit.app F ≫ mvRes F U V =
      biprod.lift ((pushPullUnit U).app F) ((pushPullUnit V).app F) ≫
        biprod.map ((pushRestrictIso U).inv.app F) ((pushRestrictIso V).inv.app F) := by
  rw [biprod.lift_map, mvRes, biprod.comp_lift, unit_comp_pushRestrictIso_inv,
    unit_comp_pushRestrictIso_inv, restrictAdjunction_unit_comp_resPush,
    restrictAdjunction_unit_comp_resPush]
  rfl

/-- The second map of `mvShort` agrees with `mvDiff` under the identifications of the terms. -/
theorem mvShortIso_comm₂ (F : X.Modules) :
    biprod.map ((pushRestrictIso U).inv.app F) ((pushRestrictIso V).inv.app F) ≫ mvDiff F U V =
      biprod.desc ((pushPullTransition (inf_le_left : U ⊓ V ≤ U)).app F)
          (-(pushPullTransition (inf_le_right : U ⊓ V ≤ V)).app F) ≫
        (pushRestrictIso (U ⊓ V)).inv.app F := by
  rw [biprod.desc_comp, mvDiff, biprod.map_desc, Preadditive.neg_comp, Preadditive.comp_neg,
    pushPullTransition_comp_pushRestrictIso_inv, pushPullTransition_comp_pushRestrictIso_inv]

/-- The Mayer–Vietoris short complex of a module is that of the scheme vocabulary, up to the
identification of `F` with `j_{U ∪ V*}j_{U ∪ V}^*F`. -/
def mvShortIso (hUV : U ⊔ V = ⊤) (F : X.Modules) :
    mvShort U V F ≅ ShortComplex.mk (mvRes F U V) (mvDiff F U V) (mvRes_comp_mvDiff F U V) :=
  ShortComplex.isoMk
    (@asIso _ _ _ _ ((Scheme.Modules.restrictAdjunction (U ⊔ V).ι).unit.app F)
      (isIso_restrictAdjunction_unit_app_of_eq_top hUV F))
    (biprod.mapIso ((pushRestrictIso U).app F).symm ((pushRestrictIso V).app F).symm)
    ((pushRestrictIso (U ⊓ V)).app F).symm (mvShortIso_comm₁ U V F) (mvShortIso_comm₂ U V F)

/-- **The Mayer–Vietoris short complex of an injective module is short exact.** -/
theorem mvShort_shortExact (hUV : U ⊔ V = ⊤) (F : X.Modules)
    (hF : Injective (C := SheafOfModules.{u} X.ringCatSheaf) F) :
    (mvShort U V F).ShortExact :=
  ShortComplex.shortExact_of_iso (mvShortIso U V hUV F).symm
    (Stacks.AlgebraicGeometry.MayerVietorisInjective.shortExact_mv_of_injective F hF U V)

end ModuleSequence

section ComplexSequence

open RingedSpaceModuleAdjunction

variable {X : Scheme.{u}} (U V : X.Opens)

/-- Sheaves of modules on a scheme, in the spelling of its underlying ringed space. -/
abbrev Mods (Y : Scheme.{u}) := SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace)

/-- `j_* j^*`, as an endofunctor of `Mods X`. -/
abbrev pushPullM (Z : X.Opens) : Mods X ⥤ Mods X :=
  modulePullback (incl Z) ⋙ modulePushforward (incl Z)

/-- The endofunctor `j_* j^*` of `Mods X` is additive. -/
instance pushPullM_additive (Z : X.Opens) : (pushPullM Z).Additive :=
  ⟨fun {_ _} f g =>
    (modulePullback (incl Z) ⋙ modulePushforward (incl Z)).map_add (f := f) (g := g)⟩

/-- The unit `F ⟶ j_* j^* F`, in `Mods X`. -/
abbrev pushPullUnitM (Z : X.Opens) : 𝟭 (Mods X) ⟶ pushPullM Z :=
  (modulePullbackPushforwardAdjunction (incl Z)).unit

/-- The restriction from `Z` to `Z' ≤ Z`, in `Mods X`. -/
def pushPullTransitionM {Z Z' : X.Opens} (h : Z' ≤ Z) : pushPullM Z ⟶ pushPullM Z' :=
  pushPullTransition h

/-- The transition from `Z` to `Z' ≤ Z` carries the unit of `Z` to the unit of `Z'`, in
`Mods X`. -/
theorem unit_comp_pushPullTransitionM {Z Z' : X.Opens} (h : Z' ≤ Z) (F : Mods X) :
    (pushPullUnitM Z).app F ≫ (pushPullTransitionM h).app F = (pushPullUnitM Z').app F :=
  unit_comp_pushPullTransition h F

/-- The Mayer–Vietoris short complex of a module, in `Mods X`. -/
def mvShortM (F : Mods X) : ShortComplex (Mods X) :=
  ShortComplex.mk (biprod.lift ((pushPullUnitM U).app F) ((pushPullUnitM V).app F))
    (biprod.desc ((pushPullTransitionM (inf_le_left : U ⊓ V ≤ U)).app F)
      (-(pushPullTransitionM (inf_le_right : U ⊓ V ≤ V)).app F)) (by
    rw [biprod.lift_desc, unit_comp_pushPullTransitionM, Preadditive.comp_neg,
      unit_comp_pushPullTransitionM, add_neg_cancel])

/-- The Mayer–Vietoris short complex of an injective module is short exact, in `Mods X`. -/
theorem mvShortM_shortExact (hUV : U ⊔ V = ⊤) (F : Mods X)
    (hF : Injective (C := SheafOfModules.{u} X.ringCatSheaf) F) :
    (mvShortM U V F).ShortExact :=
  mvShort_shortExact U V hUV F hF

/-- The unit `I ⟶ j_* j^* I` of a complex, degreewise. -/
abbrev unitChain (Z : X.Opens) (I : CochainComplex (Mods X) ℤ) :
    I ⟶ ((pushPullM Z).mapHomologicalComplex (ComplexShape.up ℤ)).obj I :=
  (CategoryTheory.Adjunction.mapHomologicalComplexAdjunction
    (modulePullbackPushforwardAdjunction (incl Z)) (ComplexShape.up ℤ)).unit.app I

/-- The restriction `j_{Z*} j_Z^* I ⟶ j_{Z'*} j_{Z'}^* I` of a complex, degreewise. -/
abbrev transitionChain {Z Z' : X.Opens} (h : Z' ≤ Z) (I : CochainComplex (Mods X) ℤ) :
    ((pushPullM Z).mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶
      ((pushPullM Z').mapHomologicalComplex (ComplexShape.up ℤ)).obj I :=
  ((pushPullTransitionM h).mapHomologicalComplex (ComplexShape.up ℤ)).app I

/-- The restriction of complexes from `Z` to `Z' ≤ Z` carries the unit of `Z` to the unit of
`Z'`. -/
theorem unitChain_comp_transitionChain {Z Z' : X.Opens} (h : Z' ≤ Z)
    (I : CochainComplex (Mods X) ℤ) :
    unitChain Z I ≫ transitionChain h I = unitChain Z' I := by
  ext n : 1
  exact unit_comp_pushPullTransitionM h (I.X n)

/-- **The Mayer–Vietoris short complex of a complex of modules.** -/
def mvComplexSequence (I : CochainComplex (Mods X) ℤ) :
    ShortComplex (CochainComplex (Mods X) ℤ) :=
  ShortComplex.mk (biprod.lift (unitChain U I) (unitChain V I))
    (biprod.desc (transitionChain (inf_le_left : U ⊓ V ≤ U) I)
      (-transitionChain (inf_le_right : U ⊓ V ≤ V) I)) (by
    rw [biprod.lift_desc, unitChain_comp_transitionChain, Preadditive.comp_neg,
      unitChain_comp_transitionChain, add_neg_cancel])

/-- The degree-`n` component of a `biprod.lift` of complexes. -/
theorem biprod_lift_f_comp_biprodXIso {C : Type*} [Category* C] [Preadditive C]
    [HasBinaryBiproducts C] {I A B : CochainComplex C ℤ} (a : I ⟶ A) (b : I ⟶ B) (n : ℤ) :
    (biprod.lift a b).f n ≫ (HomologicalComplex.biprodXIso A B n).hom =
      biprod.lift (a.f n) (b.f n) := by
  apply biprod.hom_ext
  · rw [Category.assoc, HomologicalComplex.biprodXIso_hom_fst, ← HomologicalComplex.comp_f,
      biprod.lift_fst, biprod.lift_fst]
  · rw [Category.assoc, HomologicalComplex.biprodXIso_hom_snd, ← HomologicalComplex.comp_f,
      biprod.lift_snd, biprod.lift_snd]

/-- The degree-`n` component of a `biprod.desc` of complexes. -/
theorem biprodXIso_inv_comp_biprod_desc_f {C : Type*} [Category* C] [Preadditive C]
    [HasBinaryBiproducts C] {A B D : CochainComplex C ℤ} (a : A ⟶ D) (b : B ⟶ D) (n : ℤ) :
    (HomologicalComplex.biprodXIso A B n).inv ≫ (biprod.desc a b).f n =
      biprod.desc (a.f n) (b.f n) := by
  apply biprod.hom_ext'
  · rw [HomologicalComplex.inl_biprodXIso_inv_assoc, ← HomologicalComplex.comp_f,
      biprod.inl_desc, biprod.inl_desc]
  · rw [HomologicalComplex.inr_biprodXIso_inv_assoc, ← HomologicalComplex.comp_f,
      biprod.inr_desc, biprod.inr_desc]

/-- In each degree the Mayer–Vietoris short complex of a complex is that of its term. -/
def mvComplexSequenceEvalIso (I : CochainComplex (Mods X) ℤ) (n : ℤ) :
    (mvComplexSequence U V I).map (HomologicalComplex.eval _ (ComplexShape.up ℤ) n) ≅
      mvShortM U V (I.X n) :=
  ShortComplex.isoMk (Iso.refl _) (HomologicalComplex.biprodXIso _ _ n) (Iso.refl _)
    ((Category.id_comp _).trans
      (biprod_lift_f_comp_biprodXIso (unitChain U I) (unitChain V I) n).symm)
    (((Iso.eq_inv_comp _).mp (biprodXIso_inv_comp_biprod_desc_f
      (transitionChain (inf_le_left : U ⊓ V ≤ U) I)
      (-transitionChain (inf_le_right : U ⊓ V ≤ V) I) n).symm).trans
      (Category.comp_id _).symm)

/-- **The Mayer–Vietoris short complex of a complex of injective modules is short exact.** -/
theorem mvComplexSequence_shortExact (hUV : U ⊔ V = ⊤) (I : CochainComplex (Mods X) ℤ)
    (hI : ∀ n, Injective (C := SheafOfModules.{u} X.ringCatSheaf) (I.X n)) :
    (mvComplexSequence U V I).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    ShortComplex.shortExact_of_iso (mvComplexSequenceEvalIso U V I n).symm
      (mvShortM_shortExact U V hUV (I.X n) (hI n))

end ComplexSequence

section DerivedSequence

open RingedSpaceModuleAdjunction

variable {X : Scheme.{u}}

/-- Restriction to an open subspace, in the extension-by-zero vocabulary, is Mathlib's
restriction along the inclusion of the open subscheme. -/
theorem jStar_eq_restrictFunctor (Z : X.Opens) :
    ExtensionByZeroModules.jStar Z X.ringCatSheaf = Scheme.Modules.restrictFunctor Z.ι := by
  unfold ExtensionByZeroModules.jStar Scheme.Modules.restrictFunctor
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  rfl

/-- Extension by zero from an open subscheme, in the ringed-space vocabulary. -/
def extensionByZero (Z : X.Opens) :
    SheafOfModules.{u} (structureSheafRing Z.toScheme.toSheafedSpace) ⥤
      SheafOfModules.{u} (structureSheafRing X.toSheafedSpace) :=
  ExtensionByZeroModules.jShriek Z X.ringCatSheaf

/-- Extension by zero is additive. -/
instance extensionByZero_additive (Z : X.Opens) : (extensionByZero Z).Additive :=
  ExtensionByZeroModules.jShriek_additive Z X.ringCatSheaf

/-- Extension by zero preserves finite limits. -/
instance extensionByZero_preservesFiniteLimits (Z : X.Opens) :
    PreservesFiniteLimits (extensionByZero Z) :=
  ExtensionByZeroModules.jShriek_preservesFiniteLimits Z X.ringCatSheaf

/-- Extension by zero preserves finite colimits. -/
instance extensionByZero_preservesFiniteColimits (Z : X.Opens) :
    PreservesFiniteColimits (extensionByZero Z) :=
  inferInstanceAs (PreservesFiniteColimits (ExtensionByZeroModules.jShriek Z X.ringCatSheaf))

/-- Extension by zero is left adjoint to pullback to an open subscheme. -/
def extensionByZeroAdjunction (Z : X.Opens) : extensionByZero Z ⊣ modulePullback (incl Z) :=
  (ExtensionByZeroModules.jShriekAdjunction Z X.ringCatSheaf).ofNatIsoRight
    (eqToIso (jStar_eq_restrictFunctor Z) ≪≫ restrictIso Z)

/-- Restriction to an open subscheme carries K-injective complexes to K-injective complexes
([Stacks, Tag 08BS]). -/
theorem isKInjective_pullback (Z : X.Opens)
    (I : CochainComplex (Mods X) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((modulePullback (incl Z)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact (modulePullback (incl Z))
    (extensionByZero Z) (extensionByZeroAdjunction Z) I

/-- The comparison `j_* M ⟶ Rj_* M` is invertible at the restriction of a K-injective
complex. -/
theorem isIso_derivedPushforwardUnit_app_pullback (Z : X.Opens)
    (I : CochainComplex (Mods X) ℤ)
    [I.IsKInjective] :
    IsIso ((derivedPushforwardUnit (incl Z)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((modulePullback (incl Z)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :=
  isIso_derivedPushforwardUnit_app_of_isKInjective (incl Z) _ (isKInjective_pullback Z I)

/-- The comparison `Lj^* (Qh I) ≅ Qh (j^* I)` for an open immersion. -/
def pullbackComparisonIso (Z : X.Opens)
    (I : CochainComplex (Mods X) ℤ) :
    (derivedPullback (incl Z)).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≅
      (pullbackOnHomotopy (incl Z)).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) :=
  (@asIso _ _ _ _ (derivedPullbackComparison (incl Z))
    (Stacks.Cohomology.DerivedBaseChange.isIso_derivedPullbackComparison_of_isOpenImmersion
      (incl Z))).app _

/-- **`j_* j^* I` computes `Rj_* Lj^* I` for a K-injective complex `I`.** -/
def pushPullDerivedIso (Z : X.Opens)
    (I : CochainComplex (Mods X) ℤ)
    [I.IsKInjective] :
    DerivedCategory.Q.obj (((pushPullM Z).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      (restrictPush (incl Z)).obj (DerivedCategory.Q.obj I) :=
  ((DerivedCategory.quotientCompQhIso _).app
      (((pushPullM Z).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).symm ≪≫
    @asIso _ _ _ _ ((derivedPushforwardUnit (incl Z)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((modulePullback (incl Z)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
      (isIso_derivedPushforwardUnit_app_pullback Z I) ≪≫
    (derivedPushforward (incl Z)).mapIso (pullbackComparisonIso Z I).symm ≪≫
    (derivedPushforward (incl Z)).mapIso
      ((derivedPullback (incl Z)).mapIso ((DerivedCategory.quotientCompQhIso _).app I))

/-- Given isomorphisms `eI`, `eP`, `r` and three commuting squares, the composite
`u ≫ eP.inv ≫ a ≫ r.inv ≫ rL` equals `η`. -/
theorem unit_bookkeeping {C : Type*} [Category* C] {QI QhI QP QhP RQhI RQI W : C}
    (eI : QhI ≅ QI) (eP : QhP ≅ QP) (u : QI ⟶ QP) (uh : QhI ⟶ QhP) (a : QhP ⟶ W)
    (r : RQhI ≅ W) (rL : RQhI ⟶ RQI)
    (ηh : QhI ⟶ RQhI) (η : QI ⟶ RQI)
    (hQ : uh ≫ eP.hom = eI.hom ≫ u) (hfac : ηh ≫ r.hom = uh ≫ a) (hnat : eI.hom ≫ η = ηh ≫ rL) :
    u ≫ eP.inv ≫ a ≫ r.inv ≫ rL = η := by
  rw [← cancel_epi eI.hom, ← reassoc_of% hQ, eP.hom_inv_id_assoc, ← reassoc_of% hfac,
    r.hom_inv_id_assoc, hnat]

/-- The forward map of `pushPullDerivedIso` as an explicit composite. -/
theorem pushPullDerivedIso_hom (Z : X.Opens)
    (I : CochainComplex (Mods X) ℤ)
    [I.IsKInjective] :
    (pushPullDerivedIso Z I).hom =
      ((DerivedCategory.quotientCompQhIso _).app
        (((pushPullM Z).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).inv ≫
      (derivedPushforwardUnit (incl Z)).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((modulePullback (incl Z)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
      (derivedPushforward (incl Z)).map (pullbackComparisonIso Z I).inv ≫
      (derivedPushforward (incl Z)).map ((derivedPullback (incl Z)).map
        ((DerivedCategory.quotientCompQhIso _).hom.app I)) :=
  rfl

/-- **The unit of a complex computes the derived unit**: through `pushPullDerivedIso`, the class
of `I ⟶ j_* j^* I` is the unit `K ⟶ Rj_* Lj^* K` of the derived adjunction. -/
theorem Q_map_unitChain_comp_pushPullDerivedIso (Z : X.Opens)
    (I : CochainComplex (Mods X) ℤ)
    [I.IsKInjective] :
    DerivedCategory.Q.map (unitChain Z I) ≫ (pushPullDerivedIso Z I).hom =
      (unit (incl Z)).app (DerivedCategory.Q.obj I) := by
  rw [pushPullDerivedIso_hom]
  exact unit_bookkeeping ((DerivedCategory.quotientCompQhIso _).app I)
    ((DerivedCategory.quotientCompQhIso _).app
      (((pushPullM Z).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) _ _ _
    ((derivedPushforward (incl Z)).mapIso (pullbackComparisonIso Z I)) _ _ _
    (DerivedCategory.quotientCompQhIso_hom_naturality (unitChain Z I))
    (derivedAdjunction_unit_fac (incl Z) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))
    ((unit (incl Z)).naturality ((DerivedCategory.quotientCompQhIso _).hom.app I))

/-- The inclusion of a smaller open into a larger one, as a morphism of ringed spaces. -/
abbrev inclLE {Z Z' : X.Opens} (h : Z' ≤ Z) := (X.homOfLE h).toLRSHom.toShHom

/-- The inclusion of `Z'` into `Z` followed by that of `Z` into `X` is the inclusion of `Z'`. -/
theorem inclLE_comp {Z Z' : X.Opens} (h : Z' ≤ Z) : inclLE h ≫ incl Z = incl Z' := by
  have := congrArg (fun k : Z'.toScheme ⟶ X => k.toLRSHom.toShHom) (X.homOfLE_ι h)
  simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using this

/-- A morphism `c` whose image under `F` is invertible can be cancelled after applying `F`. -/
theorem map_eq_of_comp_eq {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {A B E : C}
    (c : A ⟶ B) (x y : B ⟶ E) [IsIso (F.map c)] (h : c ≫ x = c ≫ y) : F.map x = F.map y := by
  rw [← cancel_epi (F.map c), ← F.map_comp, ← F.map_comp, h]

/-- The image of `f ≫ g` is invertible when those of `f` and of `g` are. -/
theorem isIso_map_of_eq_comp {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {A B E : C}
    (c : A ⟶ E) (f : A ⟶ B) (g : B ⟶ E) (h : c = f ≫ g) [IsIso (F.map f)] [IsIso (F.map g)] :
    IsIso (F.map c) := by
  rw [h, F.map_comp]
  infer_instance

/-- If `c ≫ t = u'`, `u' ≫ e' = η'`, `c ≫ e = η` and `η ≫ tr = η'`, then
`c ≫ t ≫ e' = c ≫ e ≫ tr`. -/
theorem transition_bookkeeping {C : Type*} [Category* C] {A B B' E E' : C} (c : A ⟶ B)
    (t : B ⟶ B') (e' : B' ⟶ E') (u' : A ⟶ B') (e : B ⟶ E) (tr : E ⟶ E') (η : A ⟶ E)
    (η' : A ⟶ E') (h₁ : c ≫ t = u') (h₂ : u' ≫ e' = η') (h₃ : c ≫ e = η) (h₄ : η ≫ tr = η') :
    c ≫ t ≫ e' = c ≫ e ≫ tr := by
  rw [← Category.assoc, h₁, h₂, ← Category.assoc, h₃, h₄]

/-- **The restriction of a complex computes the derived transition.** -/
theorem Q_map_transitionChain_comp_pushPullDerivedIso {Z Z' : X.Opens} (h : Z' ≤ Z)
    (I : CochainComplex (Mods X) ℤ)
    [I.IsKInjective] :
    DerivedCategory.Q.map (transitionChain h I) ≫ (pushPullDerivedIso Z' I).hom =
      (pushPullDerivedIso Z I).hom ≫
        (transition (inclLE h) (incl Z) (incl Z') (inclLE_comp h)).app
          (DerivedCategory.Q.obj I) := by
  apply hom_ext_of_derivedPullback (incl Z')
  have hiso := isIso_derivedPullback_map_unit_of_comp (inclLE h) (incl Z) (incl Z')
    (inclLE_comp h) (DerivedCategory.Q.obj I)
  have : IsIso ((derivedPullback (incl Z')).map (DerivedCategory.Q.map (unitChain Z I))) :=
    @isIso_map_of_eq_comp _ _ _ _ (derivedPullback (incl Z')) _ _ _
      (DerivedCategory.Q.map (unitChain Z I)) ((unit (incl Z)).app (DerivedCategory.Q.obj I))
      (pushPullDerivedIso Z I).inv
      ((Iso.eq_comp_inv _).2 (Q_map_unitChain_comp_pushPullDerivedIso Z I)) hiso
      ((derivedPullback (incl Z')).mapIso (pushPullDerivedIso Z I).symm).isIso_hom
  exact map_eq_of_comp_eq (derivedPullback (incl Z')) (DerivedCategory.Q.map (unitChain Z I)) _ _
    (transition_bookkeeping _ _ _ _ _ _ _ _
      ((DerivedCategory.Q.map_comp _ _).symm.trans
        (congrArg DerivedCategory.Q.map (unitChain_comp_transitionChain h I)))
      (Q_map_unitChain_comp_pushPullDerivedIso Z' I)
      (Q_map_unitChain_comp_pushPullDerivedIso Z I)
      (unit_comp_transitionApp (inclLE h) (incl Z) (incl Z') (inclLE_comp h) _))

end DerivedSequence

section Triangle

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- For an additive functor `F` and isomorphisms `eA`, `eB` carrying `F.map uA` to `ηA` and
`F.map uB` to `ηB`, the map `biprod.lift ηA ηB` corresponds to `F.map (biprod.lift uA uB)`. -/
theorem lift_comp_biprod_inv {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D] (F : D ⥤ C) [F.Additive]
    {I A B : D} (uA : I ⟶ A) (uB : I ⟶ B) {RA RB : C} (eA : F.obj A ≅ RA) (eB : F.obj B ≅ RB)
    (ηA : F.obj I ⟶ RA) (ηB : F.obj I ⟶ RB) (hA : F.map uA ≫ eA.hom = ηA)
    (hB : F.map uB ≫ eB.hom = ηB) :
    biprod.lift ηA ηB ≫ (biprod.mapIso eA eB).inv ≫ (F.mapBiprod A B).inv =
      F.map (biprod.lift uA uB) := by
  rw [← hA, ← hB, biprod.mapIso_inv, biprod.lift_map_assoc, Functor.mapBiprod_inv,
    biprod.lift_desc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← F.map_comp, ← F.map_comp, ← F.map_add, ← biprod.lift_eq]

/-- For an additive functor `F` and isomorphisms `eA`, `eB`, `eW` carrying `F.map tA` to `dA`
and `F.map tB` to `dB`, the map `biprod.desc dA (-dB)` corresponds to
`F.map (biprod.desc tA (-tB))`. -/
theorem desc_comp_inv {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D] (F : D ⥤ C) [F.Additive]
    {A B W : D} (tA : A ⟶ W) (tB : B ⟶ W) {RA RB RW : C} (eA : F.obj A ≅ RA)
    (eB : F.obj B ≅ RB) (eW : F.obj W ≅ RW) (dA : RA ⟶ RW) (dB : RB ⟶ RW)
    (hA : F.map tA ≫ eW.hom = eA.hom ≫ dA) (hB : F.map tB ≫ eW.hom = eB.hom ≫ dB) :
    biprod.desc dA (-dB) ≫ eW.inv =
      ((biprod.mapIso eA eB).inv ≫ (F.mapBiprod A B).inv) ≫ F.map (biprod.desc tA (-tB)) := by
  have key : ∀ {P : D} {RP : C} (e : F.obj P ≅ RP) (t : P ⟶ W) (d : RP ⟶ RW),
      F.map t ≫ eW.hom = e.hom ≫ d → e.inv ≫ F.map t = d ≫ eW.inv := fun e t d h => by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, eW.hom_inv_id, Category.comp_id]
  have hA' := key eA tA dA hA
  have hB' := key eB tB dB hB
  apply biprod.hom_ext'
  · rw [biprod.inl_desc_assoc, biprod.mapIso_inv, Category.assoc, biprod.inl_map_assoc,
      Functor.mapBiprod_inv, biprod.inl_desc_assoc, ← F.map_comp, biprod.inl_desc, hA']
  · rw [biprod.inr_desc_assoc, biprod.mapIso_inv, Category.assoc, biprod.inr_map_assoc,
      Functor.mapBiprod_inv, biprod.inr_desc_assoc, ← F.map_comp, biprod.inr_desc, F.map_neg,
      Preadditive.comp_neg, hB', Preadditive.neg_comp]

end Triangle

section DistinguishedTriangle

open RingedSpaceModuleAdjunction

variable {X : Scheme.{u}} (U V : X.Opens)

/-- The transition from `U` to `U ∩ V`. -/
abbrev transitionFst : restrictPush (incl U) ⟶ restrictPush (incl (U ⊓ V)) :=
  transition (inclLE (inf_le_left : U ⊓ V ≤ U)) (incl U) (incl (U ⊓ V)) (inclLE_comp _)

/-- The transition from `V` to `U ∩ V`. -/
abbrev transitionSnd : restrictPush (incl V) ⟶ restrictPush (incl (U ⊓ V)) :=
  transition (inclLE (inf_le_right : U ⊓ V ≤ V)) (incl V) (incl (U ⊓ V)) (inclLE_comp _)

/-- **The Mayer–Vietoris triangle of a cover by two opens**, with the units of the derived
adjunctions as the first map and the difference of the two transitions as the second. -/
abbrev mvTriangle (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)))
    (δ : (restrictPush (incl (U ⊓ V))).obj K ⟶ K⟦(1 : ℤ)⟧) :
    Triangle (DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))) :=
  Triangle.mk (biprod.lift ((unit (incl U)).app K) ((unit (incl V)).app K))
    (biprod.desc ((transitionFst U V).app K) (-(transitionSnd U V).app K)) δ

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- The binary biproduct of `Rj_{U*}Lj_U^*K` and `Rj_{V*}Lj_V^*K` exists. -/
instance hasBinaryBiproduct_restrictPush
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))) :
    HasBinaryBiproduct ((restrictPush (incl U)).obj K) ((restrictPush (incl V)).obj K) :=
  inferInstance

/-- The binary biproduct of `j_{U*}j_U^*I` and `j_{V*}j_V^*I` exists. -/
instance hasBinaryBiproduct_pushPull (I : CochainComplex (Mods X) ℤ) :
    HasBinaryBiproduct (((pushPullM U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
      (((pushPullM V).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  inferInstance

/-- For a K-injective complex `I` of injective modules, the Mayer–Vietoris triangle of the class
of `I` in the derived category is distinguished for some connecting map. -/
theorem exists_distinguished_mvTriangle_Q (hUV : U ⊔ V = ⊤)
    (I : CochainComplex (Mods X) ℤ)
    [I.IsKInjective] (hinj : ∀ n, Injective (C := SheafOfModules.{u} X.ringCatSheaf) (I.X n)) :
    ∃ δ, mvTriangle U V (DerivedCategory.Q.obj I) δ ∈ distTriang _ := by
  have hS := mvComplexSequence_shortExact U V hUV I hinj
  refine ⟨(pushPullDerivedIso (U ⊓ V) I).inv ≫
      DerivedCategory.triangleOfSESδ
        (C := SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) hS,
    isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished
      (C := SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) hS) _ ?_⟩
  refine Triangle.isoMk _ _ (Iso.refl _)
    ((biprod.mapIso (pushPullDerivedIso U I) (pushPullDerivedIso V I)).symm ≪≫
      (DerivedCategory.Q.mapBiprod _ _).symm) (pushPullDerivedIso (U ⊓ V) I).symm ?_ ?_ ?_
  · exact (lift_comp_biprod_inv DerivedCategory.Q (unitChain U I) (unitChain V I)
      (pushPullDerivedIso U I) (pushPullDerivedIso V I) _ _
      (Q_map_unitChain_comp_pushPullDerivedIso U I)
      (Q_map_unitChain_comp_pushPullDerivedIso V I)).trans (Category.id_comp _).symm
  · exact desc_comp_inv DerivedCategory.Q _ _ (pushPullDerivedIso U I) (pushPullDerivedIso V I)
      (pushPullDerivedIso (U ⊓ V) I) _ _
      (Q_map_transitionChain_comp_pushPullDerivedIso (inf_le_left : U ⊓ V ≤ U) I)
      (Q_map_transitionChain_comp_pushPullDerivedIso (inf_le_right : U ⊓ V ≤ V) I)
  · exact (Category.assoc _ _ _).trans ((congrArg (fun k => (pushPullDerivedIso (U ⊓ V) I).inv ≫
      DerivedCategory.triangleOfSESδ (C := SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))
        hS ≫ k) (CategoryTheory.Functor.map_id _ _)).trans
      (congrArg (fun k => (pushPullDerivedIso (U ⊓ V) I).inv ≫ k) (Category.comp_id _)))

/-- **The Mayer–Vietoris triangle of a cover by two opens** ([Stacks, Tag 08BV]), with the units
of the derived adjunctions as first map and the difference of the two transitions as second
map. -/
theorem exists_distinguished_mvTriangle (hUV : U ⊔ V = ⊤)
    (K : DerivedCategory (Mods X)) :
    ∃ δ, mvTriangle U V K δ ∈ distTriang _ := by
  let M := DerivedCategory.Q.objPreimage K
  let I := (Stacks.Injectives.kInjectiveResolutionFunctor (Mods X)).obj M
  have : IsIso (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion (Mods X)).app M)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let e : DerivedCategory.Q.obj I ≅ K :=
    (asIso (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion (Mods X)).app M))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨δ, hδ⟩ := exists_distinguished_mvTriangle_Q U V hUV I
    (fun n => Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective _ M n)
  refine ⟨(restrictPush (incl (U ⊓ V))).map e.inv ≫ δ ≫ e.hom⟦(1 : ℤ)⟧',
    isomorphic_distinguished _ hδ _ ?_⟩
  refine Triangle.isoMk _ _ e.symm
    (biprod.mapIso ((restrictPush (incl U)).mapIso e.symm) ((restrictPush (incl V)).mapIso e.symm))
    ((restrictPush (incl (U ⊓ V))).mapIso e.symm) ?_ ?_ ?_
  · apply biprod.hom_ext
    · simp only [Triangle.mk_mor₁, Iso.symm_hom, biprod.mapIso_hom, Functor.mapIso_hom,
        Category.assoc, biprod.lift_map, biprod.lift_fst]
      exact ((unit (incl U)).naturality e.inv).symm
    · simp only [Triangle.mk_mor₁, Iso.symm_hom, biprod.mapIso_hom, Functor.mapIso_hom,
        Category.assoc, biprod.lift_map, biprod.lift_snd]
      exact ((unit (incl V)).naturality e.inv).symm
  · apply biprod.hom_ext'
    · simp only [Triangle.mk_mor₂, Iso.symm_hom, biprod.mapIso_hom, Functor.mapIso_hom,
        biprod.inl_desc, biprod.inl_map_assoc]
      rw [biprod.inl_desc_assoc]
      exact ((transitionFst U V).naturality e.inv).symm
    · simp only [Triangle.mk_mor₂, Iso.symm_hom, biprod.mapIso_hom, Functor.mapIso_hom,
        biprod.inr_desc, biprod.inr_map_assoc, Preadditive.comp_neg]
      rw [biprod.inr_desc_assoc, Preadditive.neg_comp]
      exact congrArg Neg.neg ((transitionSnd U V).naturality e.inv).symm
  · simp only [Triangle.mk_mor₃, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

end DistinguishedTriangle

end Stacks.Cohomology.DerivedMayerVietoris

end
