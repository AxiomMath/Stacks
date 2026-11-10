module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.RingUniverseLift
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf

/-!
# The module-valued direct image `R^i f_{cris, *}` along a morphism of small crystalline topoi

Work in the situation of [Stacks, Tag 07MJ]. This file builds the module-valued direct image
`f_{cris, *} : Mod(𝒪_{X/S}) ⥤ Mod(𝒪_{X'/S'})` and its right derived functors `R^i f_{cris, *}`, and
states [Stacks, Tag 07MP] and [Stacks, Tag 07MQ] about those sheaves as propositions.

As in [Stacks, Tag 07IK], `f_cris` is the composite `π_{X'} ∘ f_CRIS ∘ i_X`, and each factor
carries modules: `i_{X, *}` and `f_{CRIS, *}` are `Stacks.SheafOfModules.pushforwardCocontinuous`
along the cocontinuous inclusion `ι : Cris(X/S) ⥤ CRIS(X/S)` and the cocontinuous change of divided
power base, and `π_{X', *} = i_{X'}^{-1}` is `SheafOfModules.pushforward` along the continuous
inclusion.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `bigCrisRingULift` and `crisRingULift` — the universe lifts of the structure presheaves of rings
  of `CRIS(X/S)` and `Cris(X/S)`, valued in `RingCat.{u + 1}`.
* `bigStructureSheafULift` and `structureSheafULift` — those presheaves as sheaves of rings.
* `bigRingStructureMapULift` and `changeBaseRingStructureMapULift` — the two maps `f^♯`.
* `moduleRingULiftUp`, `moduleRingULiftDown` — the ring-universe isomorphism on modules.
* `bigModuleDirectImage`, `changeBaseModuleDirectImage`, `smallModuleRestrictionULift` — the three
  module-valued factors.
* `crisModuleDirectImage` — **`f_{cris, *} : Mod(𝒪_{X/S}) ⥤ Mod(𝒪_{X'/S'})`**.
* `higherCrisModuleDirectImage` — **`R^i f_{cris, *} : Mod(𝒪_{X/S}) ⥤ Mod(𝒪_{X'/S'})`**.
* `Quasicoherence07MP` — **the statement of [Stacks, Tag 07MP]** about that functor, as a
  proposition.
* `Boundedness07MQ` — **the statement of [Stacks, Tag 07MQ]** about that functor, as a
  proposition.

## Main results

* `hasCrisRingDirectImageULift` — **the requirement of `HasCrisRingDirectImage`, discharged at
  `RingCat.{u + 1}`.**
* `ι_op_comp_bigCrisRingULift` and `changeBase_op_comp_bigCrisRingULift` —
  `f_cris^{-1}𝒪^{ULift}_{X'/S'} = 𝒪^{ULift}_{X/S}`, in the two stages, both `rfl`.
* `crisModuleDirectImage_comp_toAbelianSheaf` — **the abelian sheaf underlying `f_{cris, *}F` is
  the abelian `f_{cris, *}` of the abelian sheaf underlying `F`**, as an equality of functors.
* `toAbelianSheaf_obj_crisModuleDirectImage` and
  `toAbelianSheaf_obj_crisModuleDirectImage_moduleULift` — the same read on a single sheaf of
  modules, the second at the universe at which the chapter's crystal and quasi-coherence
  predicates are stated.
* `isZero_higherCrisModuleDirectImage_of_injective` — `R^i f_{cris, *}` kills injectives in
  positive degree.
* `Quasicoherence07MP.isLocallyQuasiCoherent_moduleULift` and
  `Boundedness07MQ.isZero_moduleULift` — each of the two statements implies its counterpart for
  the modules at the universe `SheafOfModules.{u} (structureSheaf S)` of the chapter's other
  statements.

## Implementation notes

For the inclusion `ι : Cris(X/S) ⥤ CRIS(X/S)` the right Kan extension of
`Crystalline.GlobalCrystallineSituation.SmallSite.crisRing` along `(ι S).op` is computed by limits
indexed by `StructuredArrow (op A) (CrystallineThickening.ι S).op`, whose objects lie in
`Type (u + 1)` and whose morphisms in `Type u`; so it needs
`CategoryTheory.Limits.HasLimitsOfSize.{u, u + 1} RingCat.{u}`, that is `max u (u + 1) ≤ u`, which
is false. The same holds for `(changeBase S S' fS fX hf).op`. So
`Crystalline.GlobalCrystallineSituation.SmallSite.HasCrisRingDirectImage` is not proved here, and
the Kan extensions are formed **one ring universe up**: `hasCrisRingDirectImageULift` is the same
conjunction with `RingCat.{u}` replaced by `RingCat.{u + 1}` and the structure presheaves by their
universe lifts `crisRingULift` and `bigCrisRingULift`, where
`HasLimitsOfSize.{u, u + 1} RingCat.{u + 1}` holds.

The lifted structure sheaf `structureSheafULift` is not
`Crystalline.GlobalCrystallineSituation.SmallSite.structureSheaf`: its sections over `(U, T, δ)`
are `ULift.{u + 1} Γ(T, 𝒪_T)`. Restriction of scalars along the ring isomorphism `ULift.ringEquiv`
is an isomorphism of categories `SheafOfModules.{u + 1} (structureSheafULift S) ≌ ModuleSheaf S`
which changes neither the underlying presheaf of abelian groups nor the morphisms
(`Stacks.Modules.sheafRingULiftEquiv`). The module-valued direct image is bracketed by its two
halves, so `crisModuleDirectImage` is a functor `ModuleSheaf S ⥤ ModuleSheaf S'` between the
categories of sheaves of modules over `𝒪_{X/S}` and `𝒪_{X'/S'}` themselves, at the module universe
`u + 1`; the universe lift of the rings occurs only inside the construction, and the
`𝒪_{X'/S'}`-action on the sections of `f_{cris, *}F` is the genuine one, `r` acting as `ULift.up r`
does on the module over the lift.

## References

* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07MK](https://stacks.math.columbia.edu/tag/07MK)
* [Stacks Project, Tag 07ML](https://stacks.math.columbia.edu/tag/07ML)
* [Stacks Project, Tag 07MP](https://stacks.math.columbia.edu/tag/07MP)
* [Stacks Project, Tag 07MQ](https://stacks.math.columbia.edu/tag/07MQ)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IU](https://stacks.math.columbia.edu/tag/07IU)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 01T0](https://stacks.math.columbia.edu/tag/01T0)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

universe u

variable (S S' : GlobalCrystallineSituation.{u}) (fS : S.S ⟶ S'.S) (fX : S.X ⟶ S'.X)
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-! ### The structure sheaf read on sets of sections

Lifting the universe of the rings needs the sheaf condition on the *sets* of sections, which the
sheaf condition in `RingCat.{u}` does not imply for a site whose objects lie in `Type (u + 1)`:
the latter is a universal property tested against rings with sections in `Type u`.  It is
available all the same, because the forgetful functor of rings is corepresented by the free ring
on one generator, `AlgebraicGeometry.Stack.ringForgetIsoCoyoneda`, so the set-valued sheaf
condition is the ring-valued one at that single test object. -/

/-- A presheaf of rings which is a sheaf is a sheaf of sets of sections, by corepresentability of
the forgetful functor of rings (`AlgebraicGeometry.Stack.ringForgetIsoCoyoneda`). -/
private theorem isSheaf_comp_forget_of_isSheaf {C : Type*} [Category C]
    {J : GrothendieckTopology C} {P : Cᵒᵖ ⥤ RingCat.{u}} (h : Presheaf.IsSheaf J P) :
    Presheaf.IsSheaf J (P ⋙ CategoryTheory.forget RingCat.{u}) :=
  (isSheaf_iff_isSheaf_of_type _ _).2
    (Presieve.isSheaf_iso _
      (Functor.isoWhiskerLeft P AlgebraicGeometry.Stack.ringForgetIsoCoyoneda) (h _))

/-- **The structure presheaf of the big crystalline site is a sheaf of sets of sections.**  This
is [Stacks, Tag 07IX] read at the free ring on one generator, transported along
`AlgebraicGeometry.Stack.ringForgetIsoCoyoneda`. -/
theorem isSheafType_bigCrisRing :
    Presheaf.IsSheaf (topology S)
      (GlobalCrystallineSituation.crisRing S ⋙ CategoryTheory.forget RingCat.{u}) :=
  isSheaf_comp_forget_of_isSheaf (GlobalCrystallineSituation.crisRing_isSheaf S)

/-- **The structure presheaf of the small crystalline site is a sheaf of sets of sections**, by
the same argument as `isSheafType_bigCrisRing`. -/
theorem isSheafType_crisRing :
    Presheaf.IsSheaf (smallTopology S) (crisRing S ⋙ CategoryTheory.forget RingCat.{u}) :=
  isSheaf_comp_forget_of_isSheaf (isSheaf_crisRing S)

/-! ### The universe lift of the structure sheaf of rings -/

/-- **The universe lift of the structure presheaf of rings of the big crystalline site**, valued
in `RingCat.{u + 1}`: its sections over `(U, T, δ)` are `ULift.{u + 1} Γ(T, 𝒪_T)`, with the ring
structure of `Γ(T, 𝒪_T)` transported along `ULift.ringEquiv`.  This is `Stacks.Modules.ringULift`
at the universes of the site, so the lifting amount is `max (u + 1) u u = u + 1`, the universe
containing the objects and the morphisms of the site and the original rings. -/
abbrev bigCrisRingULift : (Thickening S)ᵒᵖ ⥤ RingCat.{u + 1} :=
  Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
    (Stacks.Modules.ringULift.{u + 1, u, u, u} (GlobalCrystallineSituation.structureSheaf S))

/-- **The universe lift of the structure presheaf of rings of the small crystalline site**, the
same lift applied to `Crystalline.GlobalCrystallineSituation.SmallSite.structurePresheaf`. -/
abbrev crisRingULift : (CrystallineThickening S)ᵒᵖ ⥤ RingCat.{u + 1} :=
  Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
    (Stacks.Modules.ringULift.{u + 1, u, u, u} (structurePresheaf S))

/-- **`𝒪^{ULift}_{X/S}` on the big crystalline site**, the universe lift of the structure
presheaf of rings packaged as a sheaf of rings. -/
def bigStructureSheafULift : Sheaf (topology S) RingCat.{u + 1} :=
  Stacks.Modules.structureSheafRingULift.{u + 1, u, u, u}
    (𝒪 := GlobalCrystallineSituation.structureSheaf S) (isSheafType_bigCrisRing S)

/-- **`𝒪^{ULift}_{X/S}` on the small crystalline site.** -/
def structureSheafULift : Sheaf (smallTopology S) RingCat.{u + 1} :=
  Stacks.Modules.structureSheafRingULift.{u + 1, u, u, u}
    (𝒪 := structurePresheaf S) (isSheafType_crisRing S)

/-- The presheaf underlying `𝒪^{ULift}_{X/S}` on the big crystalline site is the universe lift of
the structure presheaf of rings. -/
@[simp]
theorem bigStructureSheafULift_obj : (bigStructureSheafULift S).obj = bigCrisRingULift S := rfl

/-- The presheaf underlying `𝒪^{ULift}_{X/S}` on the small crystalline site is the universe lift
of the structure presheaf of rings. -/
@[simp]
theorem structureSheafULift_obj : (structureSheafULift S).obj = crisRingULift S := rfl

/-! ### `f_cris^{-1}𝒪^{ULift}_{X'/S'} = 𝒪^{ULift}_{X/S}` -/

/-- **Restricting the lifted structure sheaf of `CRIS(X/S)` along the inclusion
`Cris(X/S) ⥤ CRIS(X/S)` gives the lifted structure sheaf of `Cris(X/S)` on the nose**, one half of
`f_cris^{-1}𝒪^{ULift}_{X'/S'} = 𝒪^{ULift}_{X/S}`. -/
theorem ι_op_comp_bigCrisRingULift :
    (CrystallineThickening.ι S).op ⋙ bigCrisRingULift S = crisRingULift S :=
  rfl

/-- **Restricting the structure presheaf of commutative rings of `CRIS(X'/S')` along change of
divided power base gives that of `CRIS(X/S)` on the nose.**  Change of base leaves the divided
power thickening of an object alone and the structure presheaf depends only on that thickening. -/
theorem changeBase_op_comp_bigStructureSheaf :
    (changeBase S S' fS fX hf).op ⋙ GlobalCrystallineSituation.structureSheaf S' =
      GlobalCrystallineSituation.structureSheaf S :=
  rfl

/-- **Restricting the lifted structure sheaf of `CRIS(X'/S')` along change of divided power base
gives the lifted structure sheaf of `CRIS(X/S)` on the nose**, the other half of
`f_cris^{-1}𝒪^{ULift}_{X'/S'} = 𝒪^{ULift}_{X/S}`. -/
theorem changeBase_op_comp_bigCrisRingULift :
    (changeBase S S' fS fX hf).op ⋙ bigCrisRingULift S' = bigCrisRingULift S :=
  rfl

/-! ### The two Kan extensions exist at `RingCat.{u + 1}` -/

/-- **The limits that compute the right Kan extension along the inclusion
`Cris(X/S) ⥤ CRIS(X/S)` exist at the coefficients `RingCat.{u + 1}`.**  They are indexed by
`StructuredArrow (op A) (CrystallineThickening.ι S).op`, whose objects lie in `Type (u + 1)` and
whose morphisms in `Type u`, and `RingCat.{u + 1}` has limits of that size because
`max u (u + 1) = u + 1`. -/
instance instHasPointwiseRightKanExtensionιRing
    (F : (CrystallineThickening S)ᵒᵖ ⥤ RingCat.{u + 1}) :
    (CrystallineThickening.ι S).op.HasPointwiseRightKanExtension F :=
  fun _ ↦ inferInstance

include hf in
/-- **The limits that compute the right Kan extension along change of divided power base
`CRIS(X/S) ⥤ CRIS(X'/S')` exist at the coefficients `RingCat.{u + 1}`**, the index categories
being of the same size as for the inclusion. -/
instance instHasPointwiseRightKanExtensionChangeBaseRing
    (F : (Thickening S)ᵒᵖ ⥤ RingCat.{u + 1}) :
    (changeBase S S' fS fX hf).op.HasPointwiseRightKanExtension F :=
  fun _ ↦ inferInstance

include hf in
/-- **The requirement of
`Crystalline.GlobalCrystallineSituation.SmallSite.HasCrisRingDirectImage`, discharged at the
ring universe `u + 1`.**  Verbatim the conjunction that definition states, with `RingCat.{u}`
replaced by `RingCat.{u + 1}` and the two structure presheaves by their universe lifts: the
lifted structure sheaf of rings admits a right Kan extension along the inclusion of the small
crystalline site and along change of divided power base. -/
theorem hasCrisRingDirectImageULift :
    Functor.HasRightKanExtension (CrystallineThickening.ι S).op (crisRingULift S) ∧
      Functor.HasRightKanExtension (changeBase S S' fS fX hf).op (bigCrisRingULift S) :=
  ⟨inferInstance, inferInstance⟩

/-! ### The structure maps `f^♯` -/

/-- **The structure map `𝒪^{ULift}_{X/S} ⟶ i_{X, *}𝒪^{ULift}_{X/S}` of sheaves of rings.**  It is
the universal map into the right Kan extension attached to the identity of `𝒪^{ULift}_{X/S}`,
which is a legitimate datum precisely because restricting the big lifted structure sheaf along the
inclusion gives the small one on the nose, `ι_op_comp_bigCrisRingULift`. -/
def bigRingStructureMapULift :
    bigStructureSheafULift S ⟶
      ((CrystallineThickening.ι S).sheafPushforwardCocontinuous RingCat.{u + 1}
        (smallTopology S) (topology S)).obj (structureSheafULift S) :=
  ObjectProperty.homMk (Functor.liftOfIsRightKanExtension _
    (Functor.rightKanExtensionCounit (CrystallineThickening.ι S).op (crisRingULift S))
    (bigCrisRingULift S) (𝟙 _))

include hf in
/-- **The structure map `𝒪^{ULift}_{X'/S'} ⟶ f_{CRIS, *}𝒪^{ULift}_{X/S}` of sheaves of rings.**
As for `bigRingStructureMapULift`, the universal map into the right Kan extension attached to the
identity, available because of `changeBase_op_comp_bigCrisRingULift`. -/
def changeBaseRingStructureMapULift :
    bigStructureSheafULift S' ⟶
      ((changeBase S S' fS fX hf).sheafPushforwardCocontinuous RingCat.{u + 1}
        (topology S) (topology S')).obj (bigStructureSheafULift S) :=
  ObjectProperty.homMk (Functor.liftOfIsRightKanExtension _
    (Functor.rightKanExtensionCounit (changeBase S S' fS fX hf).op (bigCrisRingULift S))
    (bigCrisRingULift S') (𝟙 _))

/-- **The structure map for restriction to the small crystalline site**, an identity: the
restriction of the lifted structure sheaf of `CRIS(X/S)` along the continuous inclusion is the
lifted structure sheaf of `Cris(X/S)`, by `ι_op_comp_bigCrisRingULift`. -/
def smallRestrictionRingMapULift :
    structureSheafULift S ⟶
      ((CrystallineThickening.ι S).sheafPushforwardContinuous RingCat.{u + 1}
        (smallTopology S) (topology S)).obj (bigStructureSheafULift S) :=
  ObjectProperty.homMk (𝟙 (crisRingULift S))

/-! ### The ring-universe isomorphism on modules -/

/-- **Sheaves of `𝒪_{X/S}`-modules, read as sheaves of modules over the universe lift of
`𝒪_{X/S}`.**  Restriction of scalars along the ring isomorphism `ULift.ringEquiv` changes neither
the underlying presheaf of abelian groups nor the morphisms, so this is an isomorphism of
categories with inverse `moduleRingULiftDown`; it is `Stacks.Modules.sheafRingULiftUp`.  The
module universe is the chapter's `u + 1` throughout: only the *ring* moves. -/
def moduleRingULiftUp : ModuleSheaf S ⥤ SheafOfModules.{u + 1} (structureSheafULift S) :=
  Stacks.Modules.sheafRingULiftUp.{u + 1, u, u, u, u + 1} (𝒪 := structurePresheaf S)
    (isSheaf_crisRing S) (isSheafType_crisRing S)

/-- **Sheaves of modules over the universe lift of `𝒪_{X/S}`, read as sheaves of
`𝒪_{X/S}`-modules**, the inverse of `moduleRingULiftUp`; it is
`Stacks.Modules.sheafRingULiftDown`.  A section `r` of `𝒪_{X/S}` acts as `ULift.up r` does, so
the `𝒪_{X/S}`-module obtained is the genuine one. -/
def moduleRingULiftDown : SheafOfModules.{u + 1} (structureSheafULift S) ⥤ ModuleSheaf S :=
  Stacks.Modules.sheafRingULiftDown.{u + 1, u, u, u, u + 1} (𝒪 := structurePresheaf S)
    (isSheaf_crisRing S) (isSheafType_crisRing S)

/-- Raising and then lowering the universe of the coefficient rings is the identity. -/
theorem moduleRingULiftUp_comp_down :
    moduleRingULiftUp S ⋙ moduleRingULiftDown S = Functor.id _ :=
  rfl

/-- Lowering and then raising the universe of the coefficient rings is the identity. -/
theorem moduleRingULiftDown_comp_up :
    moduleRingULiftDown S ⋙ moduleRingULiftUp S = Functor.id _ :=
  rfl

/-- Raising the universe of the coefficient rings does not change the underlying abelian sheaf. -/
theorem moduleRingULiftUp_comp_toSheaf :
    moduleRingULiftUp S ⋙ SheafOfModules.toSheaf.{u + 1} (structureSheafULift S) =
      toAbelianSheaf S :=
  rfl

/-- Lowering the universe of the coefficient rings does not change the underlying abelian
sheaf. -/
theorem moduleRingULiftDown_comp_toSheaf :
    moduleRingULiftDown S ⋙ toAbelianSheaf S =
      SheafOfModules.toSheaf.{u + 1} (structureSheafULift S) :=
  rfl

/-- Raising the universe of the coefficient rings is additive: it changes neither the sections nor
the maps between them. -/
instance additive_moduleRingULiftUp : (moduleRingULiftUp S).Additive where
  map_add := rfl

/-- Lowering the universe of the coefficient rings is additive. -/
instance additive_moduleRingULiftDown : (moduleRingULiftDown S).Additive where
  map_add := rfl

/-! ### The three module-valued factors of `f_{cris, *}` -/

/-- **The module-valued direct image `i_{X, *}` along the inclusion of the small crystalline
site**, [Stacks, Tag 07IJ], at the lifted ring coefficients.  It is
`Stacks.SheafOfModules.pushforwardCocontinuous` of [Stacks, Tag 0FN3] for the structure map
`bigRingStructureMapULift`, so its underlying abelian sheaf is the abelian `i_{X, *}` of the
underlying abelian sheaf. -/
def bigModuleDirectImage :
    SheafOfModules.{u + 1} (structureSheafULift S) ⥤
      SheafOfModules.{u + 1} (bigStructureSheafULift S) :=
  Stacks.SheafOfModules.pushforwardCocontinuous.{u + 1} (CrystallineThickening.ι S)
    (bigRingStructureMapULift S)

/-- The underlying abelian sheaf of the module-valued `i_{X, *}` is the abelian `i_{X, *}`, as an
equality of functors. -/
theorem bigModuleDirectImage_comp_toSheaf :
    bigModuleDirectImage S ⋙ SheafOfModules.toSheaf.{u + 1} (bigStructureSheafULift S) =
      SheafOfModules.toSheaf.{u + 1} (structureSheafULift S) ⋙ bigDirectImage S :=
  Stacks.SheafOfModules.pushforwardCocontinuous_comp_toSheaf.{u + 1} _ _

/-- The module-valued `i_{X, *}` is additive. -/
instance additive_bigModuleDirectImage : (bigModuleDirectImage S).Additive := by
  have h : (bigModuleDirectImage S ⋙
      SheafOfModules.toSheaf.{u + 1} (bigStructureSheafULift S)).Additive := by
    rw [bigModuleDirectImage_comp_toSheaf]
    infer_instance
  exact Functor.additive_of_comp_faithful _
    (SheafOfModules.toSheaf.{u + 1} (bigStructureSheafULift S))

/-- **The module-valued restriction `π_{X, *} = i_X^{-1}` to the small crystalline site**, the
formula `π_* = i^{-1}` of [Stacks, Tag 07IJ] carried on modules.  It is
`SheafOfModules.pushforward` along the continuous inclusion for the identity structure map
`smallRestrictionRingMapULift`; no Kan extension and no sheafification is involved. -/
def smallModuleRestrictionULift :
    SheafOfModules.{u + 1} (bigStructureSheafULift S) ⥤
      SheafOfModules.{u + 1} (structureSheafULift S) :=
  SheafOfModules.pushforward.{u + 1} (smallRestrictionRingMapULift S)

/-- The underlying abelian sheaf of the module-valued restriction to the small crystalline site is
the abelian restriction, as an equality of functors: on underlying presheaves both are restriction
along `(CrystallineThickening.ι S).op`. -/
theorem smallModuleRestrictionULift_comp_toSheaf :
    smallModuleRestrictionULift S ⋙ SheafOfModules.toSheaf.{u + 1} (structureSheafULift S) =
      SheafOfModules.toSheaf.{u + 1} (bigStructureSheafULift S) ⋙ smallRestriction S :=
  rfl

/-- The module-valued restriction to the small crystalline site is additive: on underlying
presheaves of abelian groups it is restriction along `(CrystallineThickening.ι S).op`. -/
instance additive_smallModuleRestrictionULift : (smallModuleRestrictionULift S).Additive :=
  inferInstanceAs (SheafOfModules.pushforward.{u + 1} (smallRestrictionRingMapULift S)).Additive

section ChangeBase

include hf

/-- **The module-valued direct image `f_{CRIS, *}` along change of divided power base**,
[Stacks, Tag 07IC], at the lifted ring coefficients: again
`Stacks.SheafOfModules.pushforwardCocontinuous`, for the structure map
`changeBaseRingStructureMapULift`. -/
def changeBaseModuleDirectImage :
    SheafOfModules.{u + 1} (bigStructureSheafULift S) ⥤
      SheafOfModules.{u + 1} (bigStructureSheafULift S') :=
  Stacks.SheafOfModules.pushforwardCocontinuous.{u + 1} (changeBase S S' fS fX hf)
    (changeBaseRingStructureMapULift S S' fS fX hf)

/-- The underlying abelian sheaf of the module-valued `f_{CRIS, *}` is the abelian
`f_{CRIS, *}`. -/
theorem changeBaseModuleDirectImage_comp_toSheaf :
    changeBaseModuleDirectImage S S' fS fX hf ⋙
        SheafOfModules.toSheaf.{u + 1} (bigStructureSheafULift S') =
      SheafOfModules.toSheaf.{u + 1} (bigStructureSheafULift S) ⋙
        changeBaseDirectImage S S' fS fX hf :=
  Stacks.SheafOfModules.pushforwardCocontinuous_comp_toSheaf.{u + 1} _ _

/-- The module-valued `f_{CRIS, *}` is additive. -/
instance additive_changeBaseModuleDirectImage :
    (changeBaseModuleDirectImage S S' fS fX hf).Additive := by
  have h : (changeBaseModuleDirectImage S S' fS fX hf ⋙
      SheafOfModules.toSheaf.{u + 1} (bigStructureSheafULift S')).Additive := by
    rw [changeBaseModuleDirectImage_comp_toSheaf]
    infer_instance
  exact Functor.additive_of_comp_faithful _
    (SheafOfModules.toSheaf.{u + 1} (bigStructureSheafULift S'))

/-! ### `f_{cris, *}` and `R^i f_{cris, *}` on modules -/

/-- **The module-valued direct image
`f_{cris, *} : Mod(𝒪_{X/S}) ⥤ Mod(𝒪_{X'/S'})`** along the morphism of small crystalline topoi
of [Stacks, Tag 07IK].

Read the module over the universe lift of `𝒪_{X/S}`, which is an isomorphism of categories
(`moduleRingULiftUp`); push forward through the three factors `i_{X, *}`, `f_{CRIS, *}` and
`π_{X', *}` of `f_cris`; and read the result back as a module over `𝒪_{X'/S'}`
(`moduleRingULiftDown`).  Both ends are the chapter's own categories of sheaves of modules, over
the chapter's own structure sheaves and at its own module universe `u + 1`: the universe lift of
the rings is confined to the middle, where the two right Kan extensions are formed, and is what
makes them exist. -/
def crisModuleDirectImage : ModuleSheaf S ⥤ ModuleSheaf S' :=
  moduleRingULiftUp S ⋙ bigModuleDirectImage S ⋙
    changeBaseModuleDirectImage S S' fS fX hf ⋙ smallModuleRestrictionULift S' ⋙
      moduleRingULiftDown S'

/-- **The abelian sheaf underlying `f_{cris, *}F` is the abelian direct image of the abelian sheaf
underlying `F`**, as an equality of functors
`Mod(𝒪_{X/S}) ⥤ Ab(Cris(X'/S'))`. -/
theorem crisModuleDirectImage_comp_toAbelianSheaf :
    crisModuleDirectImage S S' fS fX hf ⋙ toAbelianSheaf S' =
      toAbelianSheaf S ⋙ crisDirectImage S S' fS fX hf := by
  change moduleRingULiftUp S ⋙ bigModuleDirectImage S ⋙
      changeBaseModuleDirectImage S S' fS fX hf ⋙ smallModuleRestrictionULift S' ⋙
        moduleRingULiftDown S' ⋙ toAbelianSheaf S' = _
  rw [moduleRingULiftDown_comp_toSheaf, smallModuleRestrictionULift_comp_toSheaf,
    ← Functor.assoc (changeBaseModuleDirectImage S S' fS fX hf)
      (SheafOfModules.toSheaf.{u + 1} (bigStructureSheafULift S')) (smallRestriction S'),
    changeBaseModuleDirectImage_comp_toSheaf, Functor.assoc,
    ← Functor.assoc (bigModuleDirectImage S)
      (SheafOfModules.toSheaf.{u + 1} (bigStructureSheafULift S))
      (changeBaseDirectImage S S' fS fX hf ⋙ smallRestriction S'),
    bigModuleDirectImage_comp_toSheaf, Functor.assoc,
    ← Functor.assoc (moduleRingULiftUp S)
      (SheafOfModules.toSheaf.{u + 1} (structureSheafULift S))
      (bigDirectImage S ⋙ changeBaseDirectImage S S' fS fX hf ⋙ smallRestriction S'),
    moduleRingULiftUp_comp_toSheaf]
  rfl

/-- **The abelian sheaf underlying `f_{cris, *}F` is the abelian direct image of the abelian sheaf
underlying `F`**, read on a single sheaf of modules. -/
theorem toAbelianSheaf_obj_crisModuleDirectImage (F : ModuleSheaf S) :
    (toAbelianSheaf S').obj ((crisModuleDirectImage S S' fS fX hf).obj F) =
      (crisDirectImage S S' fS fX hf).obj ((toAbelianSheaf S).obj F) :=
  Functor.congr_obj (crisModuleDirectImage_comp_toAbelianSheaf S S' fS fX hf) F

/-- `f_{cris, *}` on modules is additive, being a composite of additive functors. -/
instance additive_crisModuleDirectImage : (crisModuleDirectImage S S' fS fX hf).Additive :=
  inferInstanceAs ((moduleRingULiftUp S ⋙ bigModuleDirectImage S ⋙
    changeBaseModuleDirectImage S S' fS fX hf ⋙ smallModuleRestrictionULift S' ⋙
      moduleRingULiftDown S').Additive)

/-- **The module-valued higher direct image
`R^i f_{cris, *} : Mod(𝒪_{X/S}) ⥤ Mod(𝒪_{X'/S'})`**, the `i`-th right derived functor of
`crisModuleDirectImage`.  It exists because that functor is additive and sheaves of
`𝒪_{X/S}`-modules on the small crystalline site are abelian with enough injectives, by
`Crystalline.GlobalCrystallineSituation.SmallSite.instAbelianModuleSheaf` and
`...instEnoughInjectivesModuleSheaf`. -/
def higherCrisModuleDirectImage (i : ℕ) : ModuleSheaf S ⥤ ModuleSheaf S' :=
  (crisModuleDirectImage S S' fS fX hf).rightDerived i

/-- **`R^i f_{cris, *} I = 0` for `i > 0` and `I` an injective sheaf of `𝒪_{X/S}`-modules.** -/
theorem isZero_higherCrisModuleDirectImage_of_injective (F : ModuleSheaf S) [Injective F]
    (i : ℕ) :
    IsZero ((higherCrisModuleDirectImage S S' fS fX hf (i + 1)).obj F) :=
  (crisModuleDirectImage S S' fS fX hf).isZero_rightDerived_obj_injective_succ i F

/-- The abelian sheaf underlying `f_{cris, *}` of the lift of a sheaf of `𝒪_{X/S}`-modules at the
module universe at which the chapter's crystal and quasi-coherence predicates are stated is the
abelian `f_{cris, *}` of the abelian sheaf
`Crystalline.GlobalCrystallineSituation.SmallSite.abelianSheaf`. -/
theorem toAbelianSheaf_obj_crisModuleDirectImage_moduleULift
    (F : SheafOfModules.{u} (structureSheaf S)) :
    (toAbelianSheaf S').obj
        ((crisModuleDirectImage S S' fS fX hf).obj ((moduleULift S).obj F)) =
      (crisDirectImage S S' fS fX hf).obj (abelianSheaf F) :=
  toAbelianSheaf_obj_crisModuleDirectImage S S' fS fX hf ((moduleULift S).obj F)

/-! ### The statements of [Stacks, Tag 07MP] and [Stacks, Tag 07MQ]

Both remarks are about the sheaves `R^i f_{cris, *}F` for `F` a crystal in quasi-coherent
`𝒪_{X/S}`-modules, and the source reads them as `𝒪_{X'/S'}`-modules — [Stacks, Tag 07MP] has to,
local quasi-coherence being a condition on the restrictions of a *module*.  That is the functor
`higherCrisModuleDirectImage` built above, so both are stated about it, with no circumlocution
and nothing quantified over module structures on an abelian sheaf.

How "a crystal in quasi-coherent `𝒪_{X/S}`-modules" is spelled, and why nothing is conjoined to
it.  [Stacks, Tag 07IT] gives two equivalent conditions, (1) quasi-coherence in the sense of
[Stacks, Tag 03DL] and (2) local quasi-coherence together with the crystal condition, and
[Stacks, Tag 07IU] defines a crystal in quasi-coherent modules to be a module satisfying them.
This library takes the notion in form (1), as `SheafOfModules.IsQuasicoherentOnSite`; that is the
reading of
`Crystalline.GlobalCrystallineSituation.SmallSite.IsFiniteLocallyFreeQuasicoherentCrystal` and of
the `07IU` registration of `SheafOfModules.IsQuasicoherentOnSite`, and it is what both statements
below use, alone.  Adding
`Crystalline.GlobalCrystallineSituation.SmallSite.IsSheafCrystal` as a second hypothesis would
make each statement strictly *weaker* than its tag: [Stacks, Tag 07IT] makes that conjunct
redundant mathematically, but this library does not have the equivalence — only the half
implication "quasi-coherent implies locally quasi-coherent", which is
`Crystalline.GlobalCrystallineSituation.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` on the
big site and `Crystalline.GlobalCrystallineSituation.SmallSite`
`.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` on this one, and neither of those produces the
crystal condition — so in Lean it is an extra hypothesis and the claim would cover fewer modules
than the source's.

`F` ranges over all of `Crystalline.GlobalCrystallineSituation.SmallSite.ModuleSheaf S`, the
sheaves of `𝒪_{X/S}`-modules at the chapter's module universe `u + 1`.  That includes the lifts
of the modules at the universe `SheafOfModules.{u} (structureSheaf S)` at which the chapter's
other statements quantify, so each statement implies its counterpart there; those implications
are `Quasicoherence07MP.isLocallyQuasiCoherent_moduleULift` and
`Boundedness07MQ.isZero_moduleULift`. -/

/-- **The statement of [Stacks, Tag 07MP].**  In the situation of [Stacks, Tag 07MJ], assume that
`S ⟶ S'` is quasi-compact and quasi-separated and that `X ⟶ S₀` is quasi-compact and
quasi-separated.  Then for a crystal in quasi-coherent `𝒪_{X/S}`-modules `F` the sheaves
`R^i f_{cris, *}F` are locally quasi-coherent.

The hypotheses, and their spellings.  "`S ⟶ S'` is quasi-compact and quasi-separated" is those
two conditions on the underlying morphism of schemes `fS.hom`, a morphism of divided power
schemes being one of schemes together with compatibility of the divided power structures.
"`X ⟶ S₀` is quasi-compact and quasi-separated" is those two conditions on `S.toClosedFiber`.
"`F` is a crystal in quasi-coherent `𝒪_{X/S}`-modules" is `SheafOfModules.IsQuasicoherentOnSite F`
and nothing else; see the discussion above for why nothing is conjoined to it.

The conclusion is `Crystalline.GlobalCrystallineSituation.SmallSite.ModuleSheaf`
`.IsLocallyQuasiCoherent`, the [Stacks, Tag 07IS] part (1) predicate at the chapter's module
universe, asserted of `R^i f_{cris, *}F` itself, and for every degree `i`, as in the source. -/
def Quasicoherence07MP : Prop :=
  QuasiCompact fS.hom → QuasiSeparated fS.hom →
    QuasiCompact S.toClosedFiber → QuasiSeparated S.toClosedFiber →
      ∀ F : ModuleSheaf S, F.IsQuasicoherentOnSite → ∀ i : ℕ,
        ModuleSheaf.IsLocallyQuasiCoherent
          ((higherCrisModuleDirectImage S S' fS fX hf i).obj F)

/-- **The statement of [Stacks, Tag 07MQ].**  In the situation of [Stacks, Tag 07MJ], assume that
`S ⟶ S'` is quasi-compact and quasi-separated and that `X ⟶ S₀` is of finite type and
quasi-separated.  Then there exists an integer `i₀` such that for any crystal in quasi-coherent
`𝒪_{X/S}`-modules `F` we have `R^i f_{cris, *}F = 0` for all `i > i₀`.

The hypotheses, and their spellings.  `S ⟶ S'` is as in `Quasicoherence07MP`.  "`X ⟶ S₀` is of
finite type" is `AlgebraicGeometry.LocallyOfFiniteType` together with
`AlgebraicGeometry.QuasiCompact` on `S.toClosedFiber`, [Stacks, Tag 01T0] defining a morphism of
finite type to be one that is locally of finite type and quasi-compact; Mathlib has the two
conditions separately and no single class for their conjunction.  "`F` is a crystal in
quasi-coherent `𝒪_{X/S}`-modules" is as in `Quasicoherence07MP`.

The bound `i₀` is a natural number, the degrees of a higher direct image being indexed by `ℕ`,
and it is chosen before `F` and depends only on the situation, as in the source: the existential
is the source's own, which asserts one `i₀` serving every crystal at once.  The vanishing is of
the module-valued `R^i f_{cris, *}`, the sheaf the source writes. -/
def Boundedness07MQ : Prop :=
  QuasiCompact fS.hom → QuasiSeparated fS.hom →
    LocallyOfFiniteType S.toClosedFiber → QuasiCompact S.toClosedFiber →
      QuasiSeparated S.toClosedFiber →
        ∃ i₀ : ℕ, ∀ F : ModuleSheaf S, F.IsQuasicoherentOnSite → ∀ i : ℕ, i₀ < i →
          IsZero ((higherCrisModuleDirectImage S S' fS fX hf i).obj F)

/-- **[Stacks, Tag 07MP] reaches the modules at the universe of the chapter's other statements.**
A quasi-coherent sheaf of `𝒪_{X/S}`-modules with sections in `Type u` has a quasi-coherent lift to
`Crystalline.GlobalCrystallineSituation.SmallSite.ModuleSheaf S`, by
`Crystalline.GlobalCrystallineSituation.SmallSite.isQuasicoherentOnSite_moduleULift`, so
`Quasicoherence07MP` applies to it. -/
theorem Quasicoherence07MP.isLocallyQuasiCoherent_moduleULift
    (h : Quasicoherence07MP S S' fS fX hf) (hc : QuasiCompact fS.hom)
    (hs : QuasiSeparated fS.hom) (hc' : QuasiCompact S.toClosedFiber)
    (hs' : QuasiSeparated S.toClosedFiber) {F : SheafOfModules.{u} (structureSheaf S)}
    (hF : F.IsQuasicoherentOnSite) (i : ℕ) :
    ModuleSheaf.IsLocallyQuasiCoherent
      ((higherCrisModuleDirectImage S S' fS fX hf i).obj ((moduleULift S).obj F)) :=
  h hc hs hc' hs' _ (isQuasicoherentOnSite_moduleULift hF) i

/-- **[Stacks, Tag 07MQ] reaches the modules at the universe of the chapter's other statements.**
The bound `i₀` of `Boundedness07MQ` kills `R^i f_{cris, *}` of the lift of every quasi-coherent
sheaf of `𝒪_{X/S}`-modules with sections in `Type u`, the lift being quasi-coherent by
`Crystalline.GlobalCrystallineSituation.SmallSite.isQuasicoherentOnSite_moduleULift`. -/
theorem Boundedness07MQ.isZero_moduleULift (h : Boundedness07MQ S S' fS fX hf)
    (hc : QuasiCompact fS.hom) (hs : QuasiSeparated fS.hom)
    (hft : LocallyOfFiniteType S.toClosedFiber) (hc' : QuasiCompact S.toClosedFiber)
    (hs' : QuasiSeparated S.toClosedFiber) :
    ∃ i₀ : ℕ, ∀ F : SheafOfModules.{u} (structureSheaf S), F.IsQuasicoherentOnSite →
      ∀ i : ℕ, i₀ < i →
        IsZero ((higherCrisModuleDirectImage S S' fS fX hf i).obj ((moduleULift S).obj F)) := by
  obtain ⟨i₀, hi₀⟩ := h hc hs hft hc' hs'
  exact ⟨i₀, fun F hF i hi ↦ hi₀ _ (isQuasicoherentOnSite_moduleULift hF) i hi⟩

end ChangeBase

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
