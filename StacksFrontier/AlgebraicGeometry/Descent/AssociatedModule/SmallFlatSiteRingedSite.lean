module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictionAlongCocontinuous
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallFlatSites

/-!
# The associated-module functor of the small smooth, syntomic and fppf sites

Let `S` be a scheme of a big fppf site `B` and let `τ ∈ {smooth, syntomic, fppf}`.  The small
`τ`-site `S_τ` of `S` is `AlgebraicGeometry.SmallFlatSite`.  This file constructs the functor
`𝓕 ↦ 𝓕^a`, from `𝒪_S`-modules to `𝒪`-modules on `S_τ`, exactly as Descent, Definition 03DU (4)
constructs it on the small étale site: it is the pullback of sheaves of modules along the morphism
of ringed sites `(S_τ, 𝒪) → (S_Zar, 𝒪_S)` given by the inclusion of the opens of `S`.  This
extends Definition 03DU (4), which treats `τ ∈ {Zariski, étale}` only.

The file then compares `S_τ` with the big `τ`-site `(Sch/S)_τ` through the inclusion
`ι : S_τ ⊆ (Sch/S)_τ`, which is fully faithful, continuous and cocontinuous.  Its *lower shriek*
`ι_! : Mod(S_τ, 𝒪) ⥤ Mod((Sch/S)_τ, 𝒪)`, the pullback of sheaves of modules along `ι`, is fully
faithful — restricting `ι_! 𝓝` back to `S_τ` returns `𝓝` — and it carries the associated module
of `S_τ` to the associated module of `(Sch/S)_τ`:

    `ι_!(𝓕^a|_{S_τ}) ≅ 𝓕^a|_{(Sch/S)_τ}`,  equivalently  `𝓕^a|_{S_τ} ≅ ι⁻¹(𝓕^a|_{(Sch/S)_τ})`,

because both sides are pullbacks along the composite `S_Zar → S_τ → (Sch/S)_τ`.  So the
sections of `𝓕^a` over an object `T → S` of `S_τ` are its sections over `T` on the big site.

## Main definitions

* `AlgebraicGeometry.SmallFlatSite.structureMap`: the comparison of structure sheaves along the
  inclusion of the opens of `S`.
* `AlgebraicGeometry.SmallFlatSite.associatedModule`: `𝓕 ↦ 𝓕^a` on `S_τ`, Definition 03DU (4)
  extended to `τ ∈ {smooth, syntomic, fppf}`.
* `AlgebraicGeometry.SmallFlatSite.restrictModule`: its right adjoint, restriction to the opens.
* `AlgebraicGeometry.SmallFlatSite.lowerShriek`: the lower shriek `ι_!` of the inclusion into the
  big site, and `AlgebraicGeometry.SmallFlatSite.restriction` the restriction `ι⁻¹`.

## Main results

* `AlgebraicGeometry.SmallFlatSite.mem_topology_iff`: a sieve of `S_τ` covers exactly when its
  image covers in `(Sch/S)_τ`.
* `AlgebraicGeometry.SmallFlatSite.isContinuous_opensToSmall`: the inclusion of the opens of `S`
  is continuous.
* `AlgebraicGeometry.SmallFlatSite.isIso_lowerShriekAdjunction_unit`: `ι⁻¹ ι_! = id`.
* `AlgebraicGeometry.SmallFlatSite.associatedModuleCompLowerShriekIso`:
  `ι_!(𝓕^a|_{S_τ}) ≅ 𝓕^a|_{(Sch/S)_τ}`.
* `AlgebraicGeometry.SmallFlatSite.associatedModuleIsoRestriction`:
  `𝓕^a|_{S_τ} ≅ ι⁻¹(𝓕^a|_{(Sch/S)_τ})`.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallFlatSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (κ : FlatSiteKind)

/-! ### The topology, read on the big site -/

/-- **A sieve of the small `τ`-site covers exactly when its image covers in the big `τ`-site.**
One direction is continuity of the inclusion; the other is cocontinuity, the inclusion being
fully faithful. -/
theorem mem_topology_iff {X : SmallFlatSite B S hS κ} (T : Sieve X) :
    T ∈ topology B S hS κ X ↔ T.functorPushforward (inclusion B S hS κ) ∈
      BigFppfOver.baseOverTopology B S hS κ.toSiteKind ((inclusion B S hS κ).obj X) := by
  refine ⟨fun h ↦ (CoverPreserving.of_isContinuous _ _ _).cover_preserve h, fun h ↦ ?_⟩
  have := (inclusion B S hS κ).cover_lift (topology B S hS κ)
    (BigFppfOver.baseOverTopology B S hS κ.toSiteKind) h
  rwa [Sieve.functorPullback_functorPushforward_eq] at this

/-! ### The opens of `S` inside the small `τ`-site -/

/-- The inclusion of the opens of `S` into the small `τ`-site preserves finite limits: its
composite with the inclusion into the big site does, and that inclusion is fully faithful. -/
instance preservesFiniteLimits_opensToSmall : PreservesFiniteLimits (opensToSmall B S hS κ) :=
  have : PreservesFiniteLimits (opensToSmall B S hS κ ⋙ inclusion B S hS κ) :=
    inferInstanceAs (PreservesFiniteLimits (BigFppfOver.opensToBig B S hS))
  preservesFiniteLimits_of_reflects_of_preserves _ (inclusion B S hS κ)

/-- The inclusion of the opens of `S` into the small `τ`-site is representably flat. -/
instance representablyFlat_opensToSmall : RepresentablyFlat (opensToSmall B S hS κ) :=
  flat_of_preservesFiniteLimits _

/-- The inclusion of the opens of `S` into the small `τ`-site is cover preserving. -/
theorem coverPreserving_opensToSmall :
    CoverPreserving (Opens.grothendieckTopology ↥S) (topology B S hS κ)
      (opensToSmall B S hS κ) := by
  refine ⟨fun {U R} hR ↦ (mem_topology_iff B S hS κ _).2 ?_⟩
  rw [← Sieve.functorPushforward_comp]
  exact (BigFppfOver.coverPreserving_baseOpensToBig B S hS κ.toSiteKind).cover_preserve hR

/-- **The inclusion of the opens of `S` into the small `τ`-site is continuous**, so it defines a
morphism of sites `S_τ → S_Zar`. -/
instance isContinuous_opensToSmall :
    (opensToSmall B S hS κ).IsContinuous (Opens.grothendieckTopology ↥S) (topology B S hS κ) :=
  Functor.isContinuous_iff_coverPreserving.2 (coverPreserving_opensToSmall B S hS κ)

/-- The opens of `S` form a final subcategory of the small `τ`-site. -/
instance final_opensToSmall : (opensToSmall B S hS κ).Final :=
  ⟨fun _ ↦ IsCofiltered.isConnected _⟩

/-! ### Binary products -/

/-- The objects of the small `τ`-site are closed under isomorphism in the big site. -/
instance isClosedUnderIsomorphisms :
    (BigFppfOver.IsSmallFlatSiteObj B S hS κ).IsClosedUnderIsomorphisms where
  of_iso e hX := BigFppfOver.isSmallFlatSiteObj_of_smallFlatSiteMorphisms B S hS κ e.inv
    (κ.morphismProperty_of_isOpenImmersion _) hX

/-- **The objects of the small `τ`-site are closed under binary products in the big site**: the
product of `T → S` and `T' → S` is `T ×_S T'`, whose projection to `T'` is a base change of
`T → S`. -/
instance isClosedUnderBinaryProducts :
    (BigFppfOver.IsSmallFlatSiteObj B S hS κ).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨h⟩
    let A := h.diag.obj ⟨.left⟩
    let A' := h.diag.obj ⟨.right⟩
    have e : X ≅ A ⨯ A' := h.isLimit.conePointUniqueUpToIso (limit.isLimit _) ≪≫
      HasLimit.isoOfNatIso (diagramIsoPair h.diag)
    refine ObjectProperty.prop_of_iso _ e.symm ?_
    have hpb := (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd A A')).map B.inclusion
    have hsnd : κ.morphismProperty (B.inclusion.map (prod.snd : A ⨯ A' ⟶ A').left) :=
      κ.morphismProperty.of_isPullback hpb (h.prop_diag_obj ⟨.left⟩)
    exact BigFppfOver.isSmallFlatSiteObj_of_smallFlatSiteMorphisms B S hS κ prod.snd hsnd
      (h.prop_diag_obj ⟨.right⟩)

/-! ### The associated-module functor -/

/-- The comparison of structure sheaves along the inclusion of the opens of `S` into the small
`τ`-site: over an open `U` it is the identification of the sections of `𝒪_S` over `U` with the
global functions of the open subscheme `U`.  It is the comparison of the big `τ`-site, the opens
of `S` reaching the big site through the small one. -/
noncomputable def structureMap :
    S.ringCatSheaf ⟶ ((opensToSmall B S hS κ).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology ↥S) (topology B S hS κ)).obj (ringStructureSheaf B S hS κ) :=
  BigFppfOver.baseStructureMap B S hS κ.toSiteKind

/-- The pushforward of presheaves of modules along the structure-sheaf comparison of the small
`τ`-site has a left adjoint. -/
instance presheafPushforward_structureMap_isRightAdjoint :
    (PresheafOfModules.pushforward.{u} (structureMap B S hS κ).hom).IsRightAdjoint :=
  Stacks.ModulePullback.isRightAdjoint_pushforward _

/-- The pushforward of sheaves of modules along the structure-sheaf comparison of the small
`τ`-site has a left adjoint. -/
instance sheafPushforward_structureMap_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (structureMap B S hS κ)).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u} (structureMap B S hS κ)).isRightAdjoint

/-- **The associated-module functor of the small `τ`-site of `S`**, Descent, Definition 03DU (4)
extended to `τ ∈ {smooth, syntomic, fppf}`: the pullback of sheaves of modules along the
morphism of ringed sites `(S_τ, 𝒪) → (S_Zar, 𝒪_S)`. -/
noncomputable def associatedModule :
    S.Modules ⥤ SheafOfModules.{u} (ringStructureSheaf B S hS κ) :=
  SheafOfModules.pullback.{u} (structureMap B S hS κ)

/-- Restriction of a sheaf of modules on the small `τ`-site of `S` to the opens of `S`, the right
adjoint of the associated-module functor. -/
noncomputable def restrictModule :
    SheafOfModules.{u} (ringStructureSheaf B S hS κ) ⥤ S.Modules :=
  SheafOfModules.pushforward.{u} (structureMap B S hS κ)

/-- The associated-module functor of the small `τ`-site is left adjoint to restriction to the
opens of `S`. -/
noncomputable def associatedModuleAdjunction :
    associatedModule B S hS κ ⊣ restrictModule B S hS κ :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS κ)

/-- The associated-module functor of the small `τ`-site preserves all colimits, being a left
adjoint. -/
noncomputable instance preservesColimitsOfSize_associatedModule.{w, w'} :
    PreservesColimitsOfSize.{w, w'} (associatedModule B S hS κ) :=
  (associatedModuleAdjunction B S hS κ).leftAdjoint_preservesColimits

/-- The pullback of the unit object to the small `τ`-site is the unit object, the opens of `S`
being final. -/
instance isIso_pullbackObjUnitToUnit :
    IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B S hS κ)) :=
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _

/-- The associated module of the structure sheaf of `S` is the structure sheaf of the small
`τ`-site. -/
noncomputable def associatedModuleUnitIso :
    (associatedModule B S hS κ).obj (SheafOfModules.unit S.ringCatSheaf) ≅
      SheafOfModules.unit (ringStructureSheaf B S hS κ) :=
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u} (structureMap B S hS κ))
    (isIso_pullbackObjUnitToUnit B S hS κ)

/-! ### The comparison with the big site -/

/-- **Restriction from the big `τ`-site to the small one**, `ι⁻¹ : Mod((Sch/S)_τ, 𝒪) ⥤
Mod(S_τ, 𝒪)`. -/
noncomputable abbrev restriction :
    SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS κ.toSiteKind) ⥤
      SheafOfModules.{u} (ringStructureSheaf B S hS κ) :=
  SheafOfModules.pushforward.{u} (𝟙 (ringStructureSheaf B S hS κ))

/-- The pushforward of presheaves of modules along the inclusion of the small `τ`-site has a left
adjoint: the small site is essentially small. -/
instance presheafPushforward_inclusion_isRightAdjoint :
    (PresheafOfModules.pushforward.{u} (F := inclusion B S hS κ)
      (show ringStructureSheaf B S hS κ ⟶ ringStructureSheaf B S hS κ from
        𝟙 _).hom).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall _

/-- Restriction of sheaves of modules from the big `τ`-site to the small one has a left
adjoint. -/
instance restriction_isRightAdjoint : (restriction B S hS κ).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u}
    (𝟙 (ringStructureSheaf B S hS κ))).isRightAdjoint

/-- **The lower shriek of the inclusion of the small `τ`-site into the big one**,
`ι_! : Mod(S_τ, 𝒪) ⥤ Mod((Sch/S)_τ, 𝒪)`, the left adjoint of restriction. -/
noncomputable def lowerShriek :
    SheafOfModules.{u} (ringStructureSheaf B S hS κ) ⥤
      SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS κ.toSiteKind) :=
  SheafOfModules.pullback.{u} (𝟙 (ringStructureSheaf B S hS κ))

/-- The lower shriek is left adjoint to restriction. -/
noncomputable def lowerShriekAdjunction : lowerShriek B S hS κ ⊣ restriction B S hS κ :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (𝟙 (ringStructureSheaf B S hS κ))

/-- **`ι⁻¹ ι_! = id`**: the unit of the lower-shriek adjunction is an isomorphism, the inclusion
being fully faithful, continuous and cocontinuous (Stacks 00XT on sheaves of modules). -/
instance isIso_lowerShriekAdjunction_unit : IsIso (lowerShriekAdjunction B S hS κ).unit :=
  Stacks.SheafOfModules.isIso_unit_of_restriction (inclusion B S hS κ) (topology B S hS κ)
    (BigFppfOver.baseOverTopology B S hS κ.toSiteKind)
    (FibredSite.baseRingStructureSheaf B S hS κ.toSiteKind) (lowerShriekAdjunction B S hS κ)

/-- **The lower shriek is fully faithful.** -/
noncomputable def fullyFaithfulLowerShriek : (lowerShriek B S hS κ).FullyFaithful :=
  (lowerShriekAdjunction B S hS κ).fullyFaithfulLOfIsIsoUnit

/-- The lower shriek `ι_!` is full. -/
instance : (lowerShriek B S hS κ).Full := (fullyFaithfulLowerShriek B S hS κ).full

/-- The lower shriek `ι_!` is faithful. -/
instance : (lowerShriek B S hS κ).Faithful := (fullyFaithfulLowerShriek B S hS κ).faithful

/-- The lower shriek preserves all colimits, being a left adjoint. -/
noncomputable instance preservesColimitsOfSize_lowerShriek.{w, w'} :
    PreservesColimitsOfSize.{w, w'} (lowerShriek B S hS κ) :=
  (lowerShriekAdjunction B S hS κ).leftAdjoint_preservesColimits

/-- The inclusion of the small `τ`-site into the big site is final: the comma category under an
object of the big site has the image of the final object of the small site as a terminal
object. -/
instance final_inclusion : (inclusion B S hS κ).Final := by
  refine ⟨fun Y ↦ isConnected_of_isTerminal _ (x := StructuredArrow.mk (Y := final B S hS κ)
    ((isTerminalInclusionFinal B S hS κ).from Y)) ?_⟩
  exact IsTerminal.ofUniqueHom
    (fun W ↦ StructuredArrow.homMk ((isTerminalFinal B S hS κ).from W.right)
      ((isTerminalInclusionFinal B S hS κ).hom_ext _ _))
    (fun W m ↦ StructuredArrow.ext _ _ ((isTerminalFinal B S hS κ).hom_ext _ _))

/-- Including the opens of `S` into the small `τ`-site and then into the big site is continuous. -/
instance isContinuous_opensToSmall_comp_inclusion :
    (opensToSmall B S hS κ ⋙ inclusion B S hS κ).IsContinuous (Opens.grothendieckTopology ↥S)
      (BigFppfOver.baseOverTopology B S hS κ.toSiteKind) :=
  Functor.isContinuous_comp _ _ _ (topology B S hS κ) _

/-- The comparison of structure sheaves of the small `τ`-site, followed by the identity of the
restricted structure sheaf, is the comparison of the big `τ`-site. -/
theorem structureMap_comp_map_id :
    structureMap B S hS κ ≫ ((opensToSmall B S hS κ).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology ↥S) (topology B S hS κ)).map (𝟙 (ringStructureSheaf B S hS κ)) =
      BigFppfOver.baseStructureMap B S hS κ.toSiteKind :=
  rfl

/-- Restriction from the big `τ`-site to the small one, followed by restriction to the opens of
`S`, is restriction from the big site to the opens of `S`. -/
noncomputable def restrictionCompRestrictModuleIso :
    restriction B S hS κ ⋙ restrictModule B S hS κ ≅
      BigFppfOver.baseRestrictModule B S hS κ.toSiteKind :=
  SheafOfModules.pushforwardComp.{u} (structureMap B S hS κ) (𝟙 (ringStructureSheaf B S hS κ)) ≪≫
    SheafOfModules.pushforwardCongr (structureMap_comp_map_id B S hS κ)

/-- **`ι_!(𝓕^a|_{S_τ}) ≅ 𝓕^a|_{(Sch/S)_τ}`.**  The lower shriek of the associated module of the
small `τ`-site is the associated module of the big `τ`-site: both are left adjoint to restriction
to the opens of `S`, which factors through the small site. -/
noncomputable def associatedModuleCompLowerShriekIso :
    associatedModule B S hS κ ⋙ lowerShriek B S hS κ ≅
      BigFppfOver.baseAssociatedModule B S hS κ.toSiteKind :=
  Adjunction.leftAdjointCompIso (associatedModuleAdjunction B S hS κ)
    (lowerShriekAdjunction B S hS κ)
    (BigFppfOver.baseAssociatedModuleAdjunction B S hS κ.toSiteKind)
    (restrictionCompRestrictModuleIso B S hS κ)

/-- **`𝓕^a|_{S_τ} ≅ ι⁻¹(𝓕^a|_{(Sch/S)_τ})`.**  The associated module of the small `τ`-site is the
restriction of the associated module of the big `τ`-site: apply restriction to
`AlgebraicGeometry.SmallFlatSite.associatedModuleCompLowerShriekIso` and use `ι⁻¹ ι_! = id`. -/
noncomputable def associatedModuleIsoRestriction :
    associatedModule B S hS κ ≅
      BigFppfOver.baseAssociatedModule B S hS κ.toSiteKind ⋙ restriction B S hS κ :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (associatedModule B S hS κ)
      (asIso (lowerShriekAdjunction B S hS κ).unit) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (associatedModuleCompLowerShriekIso B S hS κ) (restriction B S hS κ)

end AlgebraicGeometry.SmallFlatSite

end
