module

public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.ArbitraryModule.OpenSubBeta

/-!
# Stacks 070S (1) for an arbitrary module: local injectivity

Restrictions typed over the global functions of an open, the comparison of the transpose `β`
with the Zariski sheafification map on the span of the generators
(`AlgebraicGeometry.BigFppfOver.exists_openSubBeta_eq`), the covering
`AlgebraicGeometry.BigFppfOver.zariskiEqualizerCover` on which two sections with the same image
agree, local injectivity of the comparison for every `τ`, and **Stacks 070S (1)**
(`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoPullbackSections`).
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry ChangeOfRings

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Restriction of a section of the presheaf-level pullback from the whole space to an open**,
typed in the module of sections over that open.  Restriction in a presheaf of modules lands in a
restriction of scalars, so writing `0`, `+` or `•` on its value asks instance search to unfold
`CategoryTheory.PresheafOfModules.pullback`, which is a left adjoint with no formula; the
declared type here keeps every such instance on the module of sections itself. -/
public noncomputable def zariskiRestrictTop (F : S.Modules) (T : BigFppfOver B S hS)
    (V : T.left.obj.Opens) (t : (zariskiPullbackPresheaf T.hom.hom F).obj (op ⊤)) :
    (zariskiPullbackPresheaf T.hom.hom F).obj (op V) :=
  (zariskiPullbackPresheaf T.hom.hom F).map (homOfLE (le_top (a := V))).op t

/-- Restriction from the whole space to an open `V` sends `0` to `0`. -/
public theorem zariskiRestrictTop_zero (F : S.Modules) (T : BigFppfOver B S hS)
    (V : T.left.obj.Opens) : zariskiRestrictTop B S hS F T V 0 = 0 :=
  map_zero ((zariskiPullbackPresheaf T.hom.hom F).map (homOfLE (le_top (a := V))).op).hom

/-- Restriction from the whole space to an open `V` is additive. -/
public theorem zariskiRestrictTop_add (F : S.Modules) (T : BigFppfOver B S hS)
    (V : T.left.obj.Opens) (t₁ t₂ : (zariskiPullbackPresheaf T.hom.hom F).obj (op ⊤)) :
    zariskiRestrictTop B S hS F T V (t₁ + t₂) =
      zariskiRestrictTop B S hS F T V t₁ + zariskiRestrictTop B S hS F T V t₂ :=
  map_add ((zariskiPullbackPresheaf T.hom.hom F).map (homOfLE (le_top (a := V))).op).hom t₁ t₂

/-- Restriction from the whole space to an open `V` sends `c • t` to the restriction of the
global function `c` to `V` acting on the restriction of `t`. -/
public theorem zariskiRestrictTop_smul (F : S.Modules) (T : BigFppfOver B S hS)
    (V : T.left.obj.Opens) (c : T.left.obj.ringCatSheaf.obj.obj (op ⊤))
    (t : (zariskiPullbackPresheaf T.hom.hom F).obj (op ⊤)) :
    zariskiRestrictTop B S hS F T V (c • t) =
      T.left.obj.ringCatSheaf.obj.map (homOfLE (le_top (a := V))).op c •
        zariskiRestrictTop B S hS F T V t :=
  PresheafOfModules.map_smul (zariskiPullbackPresheaf T.hom.hom F)
    (homOfLE (le_top (a := V))).op c t

/-- Restricting from the whole space a generator which was already restricted from an open `U` of
`S` gives the generator restricted to the smaller open, there being at most one morphism of opens
either way. -/
public theorem zariskiRestrictTop_unit (F : S.Modules) (T : BigFppfOver B S hS) {U : S.Opens}
    (hUtop : (⊤ : T.left.obj.Opens) ≤ T.hom.hom ⁻¹ᵁ U) {V : T.left.obj.Opens}
    (hVU : V ≤ T.hom.hom ⁻¹ᵁ U)
    (a : ((SheafOfModules.forget S.ringCatSheaf).obj F).obj (op U)) :
    zariskiRestrictTop B S hS F T V ((zariskiPullbackPresheaf T.hom.hom F).map (homOfLE hUtop).op
        (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
          T.hom.hom.toRingCatSheafHom.hom).unit.app
            ((SheafOfModules.forget S.ringCatSheaf).obj F)).app (op U) a)) =
      (zariskiPullbackPresheaf T.hom.hom F).map (homOfLE hVU).op
        (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
          T.hom.hom.toRingCatSheafHom.hom).unit.app
            ((SheafOfModules.forget S.ringCatSheaf).obj F)).app (op U) a) :=
  ((zariskiPullbackPresheaf T.hom.hom F).map_comp_apply (homOfLE hUtop).op
      (homOfLE (le_top (a := V))).op _).symm.trans
    (congrArg (fun k : V ⟶ T.hom.hom ⁻¹ᵁ U =>
        (zariskiPullbackPresheaf T.hom.hom F).map k.op
      (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
        T.hom.hom.toRingCatSheafHom.hom).unit.app
          ((SheafOfModules.forget S.ringCatSheaf).obj F)).app (op U) a))
      (Subsingleton.elim _ (homOfLE hVU)))

/-- **Restriction of a section of the big-site pullback to an open subscheme of the object**,
typed in the module of sections over `openSubObj T V` itself.  As a function it is restriction
along `AlgebraicGeometry.BigFppfOver.openSubHom`; what the declared type adds is that the
scalars are the global functions of `V`, which is also the ring the component of
`AlgebraicGeometry.BigFppfOver.openSubBeta` at `V` lands over.  Restriction in a presheaf of
modules lands in a restriction of scalars along a *different* ring map, so without this the two
sides of the comparison below carry two module structures over two rings and no `+` or `•`
elaborates. -/
public noncomputable def openSubRestrict (F : S.Modules) (T : BigFppfOver B S hS)
    (V : T.left.obj.Opens) (z : (presheafPullback B S hS F).obj (op T)) :
    (presheafPullback B S hS F).obj (op (openSubObj B S hS T V)) :=
  (presheafPullback B S hS F).map (openSubHom B S hS T V).op z

/-- Restriction to the open subscheme `openSubObj T V` sends `0` to `0`. -/
public theorem openSubRestrict_zero (F : S.Modules) (T : BigFppfOver B S hS)
    (V : T.left.obj.Opens) : openSubRestrict B S hS F T V 0 = 0 :=
  map_zero ((presheafPullback B S hS F).map (openSubHom B S hS T V).op).hom

/-- Restriction to the open subscheme `openSubObj T V` is additive. -/
public theorem openSubRestrict_add (F : S.Modules) (T : BigFppfOver B S hS)
    (V : T.left.obj.Opens) (z₁ z₂ : (presheafPullback B S hS F).obj (op T)) :
    openSubRestrict B S hS F T V (z₁ + z₂) =
      openSubRestrict B S hS F T V z₁ + openSubRestrict B S hS F T V z₂ :=
  map_add ((presheafPullback B S hS F).map (openSubHom B S hS T V).op).hom z₁ z₂

/-- Restriction to the open subscheme `openSubObj T V` sends `c • z` to the restriction of `c`
along `openSubHom T V` acting on the restriction of `z`. -/
public theorem openSubRestrict_smul (F : S.Modules) (T : BigFppfOver B S hS)
    (V : T.left.obj.Opens) (c : (structureSheaf B S hS).obj.obj (op T))
    (z : (presheafPullback B S hS F).obj (op T)) :
    openSubRestrict B S hS F T V (c • z) =
      (structureSheaf B S hS).obj.map (openSubHom B S hS T V).op c •
        openSubRestrict B S hS F T V z :=
  PresheafOfModules.map_smul (presheafPullback B S hS F) (openSubHom B S hS T V).op c z

/-- The component of `AlgebraicGeometry.BigFppfOver.openSubBeta` at an open `V`, typed in the
module of sections of the big-site pullback over `openSubObj T V`; see
`AlgebraicGeometry.BigFppfOver.openSubRestrict`. -/
public noncomputable def openSubBetaApp (F : S.Modules) (T : BigFppfOver B S hS)
    (V : T.left.obj.Opens) (w : (zariskiPullbackPresheaf T.hom.hom F).obj (op V)) :
    (presheafPullback B S hS F).obj (op (openSubObj B S hS T V)) :=
  (openSubBeta B S hS F T).app (op V) w

/-- `openSubBetaApp T V` sends `0` to `0`. -/
public theorem openSubBetaApp_zero (F : S.Modules) (T : BigFppfOver B S hS)
    (V : T.left.obj.Opens) : openSubBetaApp B S hS F T V 0 = 0 :=
  map_zero ((openSubBeta B S hS F T).app (op V)).hom

/-- `openSubBetaApp T V` is additive. -/
public theorem openSubBetaApp_add (F : S.Modules) (T : BigFppfOver B S hS)
    (V : T.left.obj.Opens) (w₁ w₂ : (zariskiPullbackPresheaf T.hom.hom F).obj (op V)) :
    openSubBetaApp B S hS F T V (w₁ + w₂) =
      openSubBetaApp B S hS F T V w₁ + openSubBetaApp B S hS F T V w₂ :=
  map_add ((openSubBeta B S hS F T).app (op V)).hom w₁ w₂

/-- The component of `AlgebraicGeometry.BigFppfOver.openSubStructureMap` at an open `V`, typed
in the ring of global functions of `openSubObj T V`; see
`AlgebraicGeometry.BigFppfOver.openSubRestrict`. -/
public noncomputable def openSubScalar (T : BigFppfOver B S hS) (V : T.left.obj.Opens)
    (r : T.left.obj.ringCatSheaf.obj.obj (op V)) :
    (structureSheaf B S hS).obj.obj (op (openSubObj B S hS T V)) :=
  (openSubStructureMap B S hS T).app (op V) r

/-- `openSubBetaApp T V` sends `r • w` to `openSubScalar T V r • openSubBetaApp T V w`. -/
public theorem openSubBetaApp_smul (F : S.Modules) (T : BigFppfOver B S hS)
    (V : T.left.obj.Opens) (r : T.left.obj.ringCatSheaf.obj.obj (op V))
    (w : (zariskiPullbackPresheaf T.hom.hom F).obj (op V)) :
    openSubBetaApp B S hS F T V (r • w) =
      openSubScalar B S hS T V r • openSubBetaApp B S hS F T V w :=
  ((openSubBeta B S hS F T).app (op V)).hom.map_smul r w

/-- **The two ring maps to the global functions of `V` agree.**  Restricting a global function of
the underlying scheme of `T` to `V` and then applying
`AlgebraicGeometry.BigFppfOver.openSubStructureMap` is restriction along
`AlgebraicGeometry.BigFppfOver.openSubHom` in the structure sheaf of the big site.  This is
`AlgebraicGeometry.ι_appTop_eq_topIso_inv`, and it is what makes
`AlgebraicGeometry.BigFppfOver.openSubBetaApp_smul` and
`AlgebraicGeometry.BigFppfOver.openSubRestrict_smul` the same semilinearity. -/
public theorem openSubStructureMap_app_map_top (T : BigFppfOver B S hS)
    (V : T.left.obj.Opens) (c : (structureSheaf B S hS).obj.obj (op T)) :
    openSubScalar B S hS T V
        (T.left.obj.ringCatSheaf.obj.map (homOfLE (le_top (a := V))).op
          (show T.left.obj.ringCatSheaf.obj.obj (op ⊤) from c)) =
      (structureSheaf B S hS).obj.map (openSubHom B S hS T V).op c :=
  ((ConcreteCategory.congr_hom (ι_appTop_eq_topIso_inv V) c).trans
    (CommRingCat.comp_apply _ _ c)).symm

/-- **`β` on a generator, typed over the global functions of `V`.**  The restatement of
`AlgebraicGeometry.BigFppfOver.openSubBeta_generator` through
`AlgebraicGeometry.BigFppfOver.openSubBetaApp`. -/
public theorem openSubBetaApp_generator (F : S.Modules) (T : BigFppfOver B S hS) (U : S.Opens)
    {V : T.left.obj.Opens} (hVU : V ≤ T.hom.hom ⁻¹ᵁ U)
    (a : ((SheafOfModules.forget S.ringCatSheaf).obj F).obj (op U)) :
    openSubBetaApp B S hS F T V
        ((zariskiPullbackPresheaf T.hom.hom F).map (homOfLE hVU).op
          (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
            T.hom.hom.toRingCatSheafHom.hom).unit.app
              ((SheafOfModules.forget S.ringCatSheaf).obj F)).app (op U) a)) =
      presheafPullbackGenerator B S hS F
        (homOfRangeLe B S hS U (range_openSubObj_hom_subset B S hS T hVU)) a :=
  openSubBeta_generator B S hS F T U hVU a

/-- **Every section of the big-site pullback in the span of the generators over one open of `S`
comes from the small Zariski site of the object.**  Given `x` in the span of the generators
indexed by an open `W` of `S` through which `T` factors, there is a section `t` of the
presheaf-level pullback `AlgebraicGeometry.zariskiPullbackPresheaf` over all of the underlying
scheme of `T` whose image under the sheafification map
`AlgebraicGeometry.zariskiPullbackToSheaf` is the image of `x` under the comparison, and whose
restriction to each open `V` is carried by `AlgebraicGeometry.BigFppfOver.openSubBeta` to the
restriction of `x` to `openSubObj T V`.

The generators of the two sides correspond: `AlgebraicGeometry.BigFppfOver.openSubBeta_generator`
and `AlgebraicGeometry.zariskiPullbackToSheaf_generator` evaluate `β` and the sheafification map
on the same element of `zariskiPullbackPresheaf`, and
`AlgebraicGeometry.BigFppfOver.pullbackSectionsComparison_app_map_unit` evaluates the comparison on
the corresponding generator downstairs.  Both conclusions are additive and semilinear in `x`, so a
span induction extends them from the generators to the whole span; the semilinearities match by
`AlgebraicGeometry.BigFppfOver.openSubStructureMap_app_map_top`. -/
public theorem exists_openSubBeta_eq (F : S.Modules) (T : BigFppfOver B S hS) {W : S.Opens}
    (g : T ⟶ (opensToBig B S hS).obj W)
    {x : (presheafPullback B S hS F).obj (op T)}
    (hx : x ∈ Submodule.span ((structureSheaf B S hS).obj.obj (op T))
      (Set.range fun a : Γ(F, W) => presheafPullbackGenerator B S hS F g a)) :
    ∃ t : (zariskiPullbackPresheaf T.hom.hom F).obj (op ⊤),
      (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t =
          (pullbackSectionsComparison B S hS F).app (op T) x ∧
        ∀ V : T.left.obj.Opens,
          openSubBetaApp B S hS F T V (zariskiRestrictTop B S hS F T V t) =
            openSubRestrict B S hS F T V x := by
  have hWtop : (⊤ : T.left.obj.Opens) ≤ T.hom.hom ⁻¹ᵁ W :=
    fun z _ => range_le_of_hom B S hS g ⟨z, rfl⟩
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, rfl⟩ := hz
    refine ⟨(zariskiPullbackPresheaf T.hom.hom F).map (homOfLE hWtop).op
      (((PresheafOfModules.pullbackPushforwardAdjunction.{u}
        T.hom.hom.toRingCatSheafHom.hom).unit.app
          ((SheafOfModules.forget S.ringCatSheaf).obj F)).app (op W) a), ?_, fun V => ?_⟩
    · refine Eq.trans (zariskiPullbackToSheaf_generator T.hom.hom F W ⊤ hWtop a) ?_
      exact ((pullbackSectionsComparison_app_map_unit B S hS F g hWtop a).trans
        (pullbackSectionHom_apply T.hom.hom F W ⊤ hWtop a)).symm
    · have hVW : V ≤ T.hom.hom ⁻¹ᵁ W := fun z _ => hWtop trivial
      refine Eq.trans (congrArg (fun z => openSubBetaApp B S hS F T V z)
        (zariskiRestrictTop_unit B S hS F T hWtop hVW a)) ?_
      refine Eq.trans (openSubBetaApp_generator B S hS F T W hVW a) ?_
      exact (presheafPullbackGenerator_map B S hS F (openSubHom B S hS T V) g _ a).symm
  | zero =>
    refine ⟨0, ?_, fun V => ?_⟩
    · rw [map_zero, map_zero]
      rfl
    · rw [zariskiRestrictTop_zero, openSubBetaApp_zero, openSubRestrict_zero]
  | add z₁ z₂ _ _ h₁ h₂ =>
    obtain ⟨t₁, h₁, k₁⟩ := h₁
    obtain ⟨t₂, h₂, k₂⟩ := h₂
    refine ⟨t₁ + t₂, ?_, fun V => ?_⟩
    · rw [map_add, map_add, h₁, h₂]
      rfl
    · rw [zariskiRestrictTop_add, openSubBetaApp_add, k₁ V, k₂ V, openSubRestrict_add]
  | smul c z _ h =>
    obtain ⟨t, ht, kt⟩ := h
    refine ⟨(show T.left.obj.ringCatSheaf.obj.obj (op ⊤) from c) • t, ?_, fun V => ?_⟩
    · rw [((zariskiPullbackToSheaf T.hom.hom F).app (op ⊤)).hom.map_smul, ht,
        ((pullbackSectionsComparison B S hS F).app (op T)).hom.map_smul]
      rfl
    · rw [zariskiRestrictTop_smul, openSubBetaApp_smul, kt V,
        openSubStructureMap_app_map_top, openSubRestrict_smul]

/-- **Two sections of the presheaf-level pullback with the same image in `f^*F` agree near every
point of the object.**  `AlgebraicGeometry.exists_eq_map_of_zariskiPullbackToSheaf_app_eq` at
the structure morphism of `T` and `V = ⊤`. -/
public theorem exists_zariskiEqualizerOpen (F : S.Modules) (T : BigFppfOver B S hS)
    (t t' : (zariskiPullbackPresheaf T.hom.hom F).obj (op ⊤))
    (heq : (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t =
      (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t') (z : ↥T.left.obj) :
    ∃ V : T.left.obj.Opens, z ∈ V ∧
      zariskiRestrictTop B S hS F T V t = zariskiRestrictTop B S hS F T V t' := by
  obtain ⟨V, hVtop, hzV, hVeq⟩ :=
    exists_eq_map_of_zariskiPullbackToSheaf_app_eq T.hom.hom F ⊤ t t' heq z trivial
  exact ⟨V, hzV, hVeq⟩

/-- A chosen open around a point on which two sections with the same image in `f^*F` agree, from
`AlgebraicGeometry.BigFppfOver.exists_zariskiEqualizerOpen`. -/
public noncomputable def zariskiEqualizerOpen (F : S.Modules) (T : BigFppfOver B S hS)
    (t t' : (zariskiPullbackPresheaf T.hom.hom F).obj (op ⊤))
    (heq : (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t =
      (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t') (z : ↥T.left.obj) :
    T.left.obj.Opens :=
  (exists_zariskiEqualizerOpen B S hS F T t t' heq z).choose

/-- The point `z` lies in the open `zariskiEqualizerOpen F T t t' heq z` chosen around it. -/
public theorem mem_zariskiEqualizerOpen (F : S.Modules) (T : BigFppfOver B S hS)
    (t t' : (zariskiPullbackPresheaf T.hom.hom F).obj (op ⊤))
    (heq : (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t =
      (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t') (z : ↥T.left.obj) :
    z ∈ zariskiEqualizerOpen B S hS F T t t' heq z :=
  (exists_zariskiEqualizerOpen B S hS F T t t' heq z).choose_spec.1

/-- The sections `t` and `t'` have the same restriction to the open
`zariskiEqualizerOpen F T t t' heq z`. -/
public theorem zariskiRestrictTop_zariskiEqualizerOpen (F : S.Modules) (T : BigFppfOver B S hS)
    (t t' : (zariskiPullbackPresheaf T.hom.hom F).obj (op ⊤))
    (heq : (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t =
      (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t') (z : ↥T.left.obj) :
    zariskiRestrictTop B S hS F T (zariskiEqualizerOpen B S hS F T t t' heq z) t =
      zariskiRestrictTop B S hS F T (zariskiEqualizerOpen B S hS F T t t' heq z) t' :=
  (exists_zariskiEqualizerOpen B S hS F T t t' heq z).choose_spec.2

/-- **The covering of an object by the chosen opens on which two sections of the presheaf-level
pullback upstairs agree.**  Indexed by the points of the underlying scheme of `T`, the member at a
point being the open immersion of `AlgebraicGeometry.BigFppfOver.zariskiEqualizerOpen` there.

Indexing by points rather than by the opens with the agreement property keeps the index type free
of the presheaf-level pullback, whose values have no formula. -/
public noncomputable def zariskiEqualizerCover (F : S.Modules) (T : BigFppfOver B S hS)
    (t t' : (zariskiPullbackPresheaf T.hom.hom F).obj (op ⊤))
    (heq : (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t =
      (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t') :
    PreZeroHypercover.{u + 1} T where
  I₀ := ULift.{u + 1} ↥T.left.obj
  X i := openSubObj B S hS T (zariskiEqualizerOpen B S hS F T t t' heq i.down)
  f i := openSubHom B S hS T (zariskiEqualizerOpen B S hS F T t t' heq i.down)

/-- The covering of `AlgebraicGeometry.BigFppfOver.zariskiEqualizerCover` is an fppf covering
family of the chosen category of schemes: its members are open immersions, hence flat and locally
of finite presentation, and they are jointly surjective because the chosen open at a point
contains that point (`AlgebraicGeometry.BigFppfOver.mem_zariskiEqualizerOpen`). -/
public theorem isFppfCovering_zariskiEqualizerCover (F : S.Modules) (T : BigFppfOver B S hS)
    (t t' : (zariskiPullbackPresheaf T.hom.hom F).obj (op ⊤))
    (heq : (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t =
      (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t') :
    IsFppfCovering (κ := B.cutoff)
      ⟨T.left, (zariskiEqualizerCover B S hS F T t t' heq).map
        (Over.forget (B.obj hS))⟩ := by
  change Presieve.map B.inclusion
    ((zariskiEqualizerCover B S hS F T t t' heq).map
      (Over.forget (B.obj hS))).presieve₀ ∈
      Scheme.fppfPrecoverage.coverings _
  rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows]
  refine Scheme.zariskiPrecoverage_le_fppfPrecoverage _ ?_
  rw [Scheme.zariskiPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun z => ⟨⟨z⟩, ⟨⟨z, mem_zariskiEqualizerOpen B S hS F T t t' heq z⟩, rfl⟩⟩, fun i => ?_⟩
  exact inferInstanceAs (IsOpenImmersion (zariskiEqualizerOpen B S hS F T t t' heq i.down).ι)

/-- **The chosen opens of `AlgebraicGeometry.BigFppfOver.zariskiEqualizerCover` cover, for
each of the five topologies.**  As for
`AlgebraicGeometry.BigFppfOver.mem_baseTopology_sieve₀_affineSubordinateCover`: the members are
open immersions and they are jointly surjective because they already form an fppf covering
family, so `AlgebraicGeometry.BigFppfOver.sieve₀_mem_baseTopology_of_isOpenImmersion`
applies. -/
public theorem mem_baseTopology_sieve₀_zariskiEqualizerCover (τ : SiteKind) (F : S.Modules)
    (T : BigFppfOver B S hS) (t t' : (zariskiPullbackPresheaf T.hom.hom F).obj (op ⊤))
    (heq : (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t =
      (zariskiPullbackToSheaf T.hom.hom F).app (op ⊤) t') :
    (zariskiEqualizerCover B S hS F T t t' heq).sieve₀ ∈ baseOverTopology B S hS τ T := by
  have hfppf : (((zariskiEqualizerCover B S hS F T t t' heq).map
      (Over.forget (B.obj hS))).map B.inclusion).presieve₀ ∈
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)).coverings
        (B.inclusion.obj T.left) := by
    rw [PreZeroHypercover.presieve₀_map]
    exact isFppfCovering_zariskiEqualizerCover B S hS F T t t' heq
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact sieve₀_mem_baseTopology_of_isOpenImmersion B τ
    ((zariskiEqualizerCover B S hS F T t t' heq).map (Over.forget (B.obj hS)))
    ((Scheme.presieve₀_mem_precoverage_iff _).1 hfppf).1
    (fun i => inferInstanceAs (IsOpenImmersion
      (zariskiEqualizerOpen B S hS F T t t' heq i.down).ι))

/-- **The comparison of Stacks 070S (1) is locally injective, for every one of the five
topologies.**  Two sections of the pullback with the
same image under `AlgebraicGeometry.BigFppfOver.pullbackSectionsComparison` agree locally for the
localized `τ`-topology.

Each of the two lies, by
`AlgebraicGeometry.BigFppfOver.exists_mem_span_presheafPullbackGenerator`, in the span of the
generators indexed by a single open of `S` through which the object factors; replacing the two
opens by their intersection, one open `W` serves both.  Over that `W`,
`AlgebraicGeometry.BigFppfOver.exists_openSubBeta_eq` produces two sections `tx`, `ty` of the
presheaf-level pullback on the small Zariski site of the object which
`AlgebraicGeometry.BigFppfOver.openSubBeta` carries, open by open, to the restrictions of the two
given sections, and whose images under the sheafification map
`AlgebraicGeometry.zariskiPullbackToSheaf` are the images of the two given sections under the
comparison — hence equal.  Local injectivity of that sheafification map
(`AlgebraicGeometry.exists_eq_map_of_zariskiPullbackToSheaf_app_eq`) makes `tx` and `ty` agree on
a Zariski covering family of opens, and `β` then makes the two given sections agree on the
corresponding covering family of the big site,
`AlgebraicGeometry.BigFppfOver.zariskiEqualizerCover`.  Nothing is glued and no transitivity is
used.

This is the other half of Stacks 070S (1); the locally surjective half is
`AlgebraicGeometry.BigFppfOver.isLocallySurjective_pullbackSectionsComparison`. -/
public instance isLocallyInjective_pullbackSectionsComparison (τ : SiteKind)
    (F : S.Modules) :
    Presheaf.IsLocallyInjective (baseOverTopology B S hS τ)
      ((PresheafOfModules.toPresheaf (FibredSite.baseRingStructureSheaf B S hS τ).obj).map
        (pullbackSectionsComparison B S hS F)) where
  equalizerSieve_mem {Zop} x y h := by
    have h' : (pullbackSectionsComparison B S hS F).app Zop
          (x : (presheafPullback B S hS F).obj Zop) =
        (pullbackSectionsComparison B S hS F).app Zop
          (y : (presheafPullback B S hS F).obj Zop) := h
    obtain ⟨W₁, g₁, hx⟩ := exists_mem_span_presheafPullbackGenerator B S hS F (unop Zop)
      (x : (presheafPullback B S hS F).obj Zop)
    obtain ⟨W₂, g₂, hy⟩ := exists_mem_span_presheafPullbackGenerator B S hS F (unop Zop)
      (y : (presheafPullback B S hS F).obj Zop)
    have hr : Set.range ⇑(unop Zop).hom.hom ⊆ ((W₁ ⊓ W₂ : S.Opens) : Set S) :=
      Set.subset_inter (range_le_of_hom B S hS g₁) (range_le_of_hom B S hS g₂)
    obtain ⟨tx, htx, kx⟩ := exists_openSubBeta_eq B S hS F (unop Zop)
      (homOfRangeLe B S hS (W₁ ⊓ W₂) hr)
      (span_presheafPullbackGenerator_mono B S hS F inf_le_left g₁ _ hx)
    obtain ⟨ty, hty, ky⟩ := exists_openSubBeta_eq B S hS F (unop Zop)
      (homOfRangeLe B S hS (W₁ ⊓ W₂) hr)
      (span_presheafPullbackGenerator_mono B S hS F inf_le_right g₂ _ hy)
    have heq : (zariskiPullbackToSheaf (unop Zop).hom.hom F).app (op ⊤) tx =
        (zariskiPullbackToSheaf (unop Zop).hom.hom F).app (op ⊤) ty :=
      htx.trans (h'.trans hty.symm)
    refine (baseOverTopology B S hS τ).superset_covering ?_
      (mem_baseTopology_sieve₀_zariskiEqualizerCover B S hS τ F (unop Zop) tx ty heq)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    refine Eq.trans (kx (zariskiEqualizerOpen B S hS F (unop Zop) tx ty heq i.down)).symm ?_
    refine Eq.trans (congrArg
      (fun w => openSubBetaApp B S hS F (unop Zop)
        (zariskiEqualizerOpen B S hS F (unop Zop) tx ty heq i.down) w)
      (zariskiRestrictTop_zariskiEqualizerOpen B S hS F (unop Zop) tx ty heq i.down)) ?_
    exact ky (zariskiEqualizerOpen B S hS F (unop Zop) tx ty heq i.down)

/-- **Stacks 070S (1).**  Let `F` be an arbitrary sheaf of `𝒪_S`-modules.  For each of the five
topologies `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, the pullback of `F` along the
morphism of ringed sites `id_{τ,Zar} : ((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪_S)` is the
`τ`-sheafification of the presheaf `(f : T → S) ↦ Γ(T, f^*F)` on `(Sch/S)_τ`.

The pullback is `AlgebraicGeometry.BigFppfOver.baseAssociatedModule`, presented by
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleSheafificationIso` as the
`τ`-sheafification of the pullback of presheaves of modules; the presheaf of sections is
`AlgebraicGeometry.BigFppfOver.pullbackSectionsPresheaf`; and the identification is the
`τ`-sheafification of the comparison
`AlgebraicGeometry.BigFppfOver.pullbackSectionsComparison`, which is locally surjective and
locally injective for every `τ`
(`AlgebraicGeometry.BigFppfOver.isLocallySurjective_pullbackSectionsComparison` and
`AlgebraicGeometry.BigFppfOver.isLocallyInjective_pullbackSectionsComparison`). -/
@[stacks 070S "part (1)"]
public noncomputable def baseAssociatedModuleIsoPullbackSections (τ : SiteKind)
    (F : S.Modules) :
    (baseAssociatedModule B S hS τ).obj F ≅
      (PresheafOfModules.sheafification.{u}
          (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).obj
        (pullbackSectionsPresheaf B S hS F) :=
  (baseAssociatedModuleSheafificationIso B S hS τ).app F ≪≫
    @asIso _ _ _ _ _ (isIso_baseSheafification_map_pullbackSectionsComparison B S hS τ F)

/-- For a quasi-coherent `F`, the comparison `AlgebraicGeometry.BigFppfOver.sectionsComparison`
is `AlgebraicGeometry.BigFppfOver.pullbackSectionsComparison`: the statements of this file
specialise to those of `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections` and its
chain. -/
public theorem sectionsComparison_eq_pullbackSectionsComparison (F : S.Modules)
    [F.IsQuasicoherent] :
    sectionsComparison B S hS F = pullbackSectionsComparison B S hS F :=
  rfl

end BigFppfOver

end AlgebraicGeometry

end
