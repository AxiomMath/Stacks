module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import StacksFrontier.AlgebraicGeometry.Crystalline.DeRhamComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictedSiteSections

/-!
# Restriction to the small crystalline site of a restricted situation

Fix a global crystalline situation `(p, (S, I, γ), X)` ([Stacks, Tag 07MF]), an open `W` of `S`
and an open `V` of `X` whose image lies in `W`. The restricted situation is `(p, S|_W, V)`, and
change of divided power base along the two open immersions is a functor
`smallExtend : Cris(V/S|_W) ⥤ Cris(X/S)` ([Stacks, Tag 07KL]), continuous and cocontinuous.
Restriction along it is precomposition with `smallExtend.op`.

This file shows that restriction along `smallExtend` commutes with the three constructions applied
to coefficients in [Stacks, Tag 07LM]:

* sheafification of abelian presheaves, an instance of [Stacks, Tag 00XR];
* the tensor product of presheaves of modules, definitionally, since the structure sheaf of
  `Cris(V/S|_W)` is the structure sheaf of `Cris(X/S)` precomposed with `smallExtend.op`;
* the exterior powers `Ω^i_{X/S}` of the sheaf of differentials ([Stacks, Tag 07J4]),
  definitionally.

Names below not starting with `PresheafOfModules` are in the namespace
`Crystalline.GlobalCrystallineSituation`.

## Main definitions

* `SmallSite.smallExtendModuleRestriction`: restriction of presheaves of `𝒪_{X/S}`-modules along
  `smallExtend`.
* `SmallSite.smallExtendAbelianRestrictionCompPresheafToSheafIso`: restriction to the restricted
  site commutes with sheafification of abelian presheaves.

## Main results

* `PresheafOfModules.pushforward₀OfCommRingCat_obj_tensorObj` and
  `PresheafOfModules.pushforward₀OfCommRingCat_obj_tensorUnit`: precomposition of presheaves of
  modules along a functor carries the tensor product to the tensor product and the unit to the
  unit, definitionally.
* `smallExtend_isContinuous`, `smallExtend_isCocontinuous` and
  `smallExtend_hasPointwiseRightKanExtension`: `smallExtend` is a continuous and cocontinuous
  functor of sites, and right Kan extensions along it exist.
* `SmallSite.toSheafify_smallExtendAbelianRestrictionCompPresheafToSheafIso`: the comparison
  isomorphism is compatible with the units of the two sheafifications.
* `SmallSite.smallExtendModuleRestriction_obj_tensorObj` and
  `SmallSite.smallExtendModuleRestriction_obj_tensorUnit`: restriction carries the tensor product
  to the tensor product and `𝒪_{X/S}` to `𝒪_{V/S|_W}`.
* `SmallSite.smallExtendModuleRestriction_obj_crysDifferentialForms`: the restriction of
  `Ω^i_{X/S}` is the `i`-th exterior power of the restriction of `Ω_{X/S}`.

## Implementation notes

The exterior-power compatibility is stated for `Ω_{X/S}`. For an arbitrary presheaf of modules
`M` it holds definitionally as well, but checking that definitional equality for an opaque `M`
unfolds `ExteriorAlgebra` and exceeds the default heartbeat budget.

## References

* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
* [Stacks Project, Tag 07J4](https://stacks.math.columbia.edu/tag/07J4)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite

universe u

noncomputable section

/-! ### Precomposition of presheaves of modules is monoidal -/

namespace PresheafOfModules

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (G : C ⥤ D)
  (O : Dᵒᵖ ⥤ CommRingCat.{u})

/-- Precomposition of presheaves of modules with `G` carries the tensor product `M ⊗ N` to the
tensor product of the precomposed presheaves, definitionally. -/
theorem pushforward₀OfCommRingCat_obj_tensorObj
    (M N : PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)) :
    (pushforward₀OfCommRingCat G O).obj (M ⊗ N) =
      (pushforward₀OfCommRingCat G O).obj M ⊗ (pushforward₀OfCommRingCat G O).obj N := rfl

/-- Precomposition of presheaves of modules with `G` carries the unit object, `O` as a module
over itself, to the unit object `G.op ⋙ O`, definitionally. -/
theorem pushforward₀OfCommRingCat_obj_tensorUnit :
    (pushforward₀OfCommRingCat G O).obj (𝟙_ (PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat))) =
      𝟙_ (PresheafOfModules.{u} ((G.op ⋙ O) ⋙ forget₂ _ RingCat)) := rfl

end PresheafOfModules

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u}) (W : S.S.scheme.Opens) (V : S.X.Opens)
  (hVW : V ≤ sourceToBase S ⁻¹ᵁ W)

/-! ### `smallExtend` as a continuous and cocontinuous functor of sites -/

/-- Change of divided power base along the two open immersions of a restricted situation,
`smallExtend` ([Stacks, Tag 07KL]), is a continuous functor of sites. -/
instance smallExtend_isContinuous :
    (smallExtend S W V hVW).IsContinuous (smallTopology (restrict S W V hVW))
      (smallTopology S) :=
  inferInstanceAs ((smallChangeBase (restrict S W V hVW) S (restrictSι S W V hVW)
    (restrictXι S W V hVW) (restrict_changeBase_condition' S W V hVW)).IsContinuous _ _)

/-- Change of divided power base along the two open immersions of a restricted situation,
`smallExtend`, is a cocontinuous functor of sites; with `smallExtend_isContinuous`, restriction
along it is both a direct and an inverse image ([Stacks, Tag 00XR]). -/
instance smallExtend_isCocontinuous :
    (smallExtend S W V hVW).IsCocontinuous (smallTopology (restrict S W V hVW))
      (smallTopology S) :=
  inferInstanceAs ((smallChangeBase (restrict S W V hVW) S (restrictSι S W V hVW)
    (restrictXι S W V hVW) (restrict_changeBase_condition' S W V hVW)).IsCocontinuous _ _)

/-- Every presheaf on the restricted site with values in a category with limits of size
`(u, u + 1)` has a pointwise right Kan extension along `(smallExtend S W V hVW).op`. -/
instance smallExtend_hasPointwiseRightKanExtension (E : Type (u + 2)) [Category.{u + 1} E]
    [HasLimitsOfSize.{u, u + 1} E]
    (F : (CrystallineThickening (restrict S W V hVW))ᵒᵖ ⥤ E) :
    (smallExtend S W V hVW).op.HasPointwiseRightKanExtension F :=
  fun _ ↦ inferInstance

/-- Restriction of abelian sheaves along `smallExtend` is the direct image
`Functor.sheafPushforwardContinuous` of the continuous functor `smallExtend`. -/
theorem SmallSite.smallExtendAbelianRestriction_eq_sheafPushforwardContinuous :
    SmallSite.smallExtendAbelianRestriction S W V hVW =
      (smallExtend S W V hVW).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (smallTopology (restrict S W V hVW)) (smallTopology S) := rfl

namespace SmallSite

/-! ### Restriction to the restricted site commutes with sheafification -/

/-- **Restriction to the small crystalline site of a restricted situation commutes with
sheafification**: sheafifying an abelian presheaf on `Cris(X/S)` and then restricting to
`Cris(V/S|_W)` is naturally isomorphic to restricting first, by precomposition with
`(smallExtend S W V hVW).op`, and sheafifying on `Cris(V/S|_W)`. This is [Stacks, Tag 00XR] for
the functor of sites `smallExtend`. -/
def smallExtendAbelianRestrictionCompPresheafToSheafIso :
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj (smallExtend S W V hVW).op ⋙
        presheafToSheaf (smallTopology (restrict S W V hVW)) AddCommGrpCat.{u + 1} ≅
      presheafToSheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        smallExtendAbelianRestriction S W V hVW :=
  (smallExtend S W V hVW).pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat.{u + 1} (smallTopology (restrict S W V hVW)) (smallTopology S)

/-- The isomorphism `smallExtendAbelianRestrictionCompPresheafToSheafIso` is compatible with the
units of sheafification: for an abelian presheaf `F` on `Cris(X/S)`, the unit of sheafification of
the restriction of `F` followed by the isomorphism is the restriction of the unit `F ⟶ F^#`. -/
theorem toSheafify_smallExtendAbelianRestrictionCompPresheafToSheafIso
    (F : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    toSheafify (smallTopology (restrict S W V hVW)) ((smallExtend S W V hVW).op ⋙ F) ≫
        ((smallExtendAbelianRestrictionCompPresheafToSheafIso S W V hVW).hom.app F).hom =
      Functor.whiskerLeft (smallExtend S W V hVW).op (toSheafify (smallTopology S) F) :=
  (smallExtend S W V hVW).toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat.{u + 1} (smallTopology (restrict S W V hVW)) (smallTopology S) F

/-! ### Restriction of presheaves of modules -/

/-- The structure sheaf of the restricted site is, definitionally, the structure sheaf of
`Cris(X/S)` precomposed with `(smallExtend S W V hVW).op`: both send an object `(U, T, δ)` to
`Γ(T, 𝒪_T)`. -/
theorem structurePresheaf_restrict :
    structurePresheaf (restrict S W V hVW) =
      (smallExtend S W V hVW).op ⋙ structurePresheaf S := rfl

/-- The underlying presheaf of the structure sheaf of the restricted site is that of
`Cris(X/S)` precomposed with `(smallExtend S W V hVW).op`. -/
theorem structureSheaf_obj_restrict :
    (structureSheaf (restrict S W V hVW)).obj =
      (smallExtend S W V hVW).op ⋙ (structureSheaf S).obj := rfl

/-- Restriction of presheaves of `𝒪_{X/S}`-modules to the small crystalline site of a
restricted situation: precomposition with `(smallExtend S W V hVW).op`, that is,
`PresheafOfModules.pushforward₀OfCommRingCat` at `smallExtend`. -/
abbrev smallExtendModuleRestriction :
    PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u}
        (structurePresheaf (restrict S W V hVW) ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.pushforward₀OfCommRingCat (smallExtend S W V hVW) (structurePresheaf S)

/-- Restriction to the restricted site carries the tensor product of presheaves of
`𝒪_{X/S}`-modules to the tensor product, definitionally. -/
theorem smallExtendModuleRestriction_obj_tensorObj
    (M N : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) :
    (smallExtendModuleRestriction S W V hVW).obj (M ⊗ N) =
      (smallExtendModuleRestriction S W V hVW).obj M ⊗
        (smallExtendModuleRestriction S W V hVW).obj N :=
  PresheafOfModules.pushforward₀OfCommRingCat_obj_tensorObj _ _ M N

/-- Restriction to the restricted site carries the unit `𝒪_{X/S}` to the unit `𝒪_{V/S|_W}`,
definitionally. -/
theorem smallExtendModuleRestriction_obj_tensorUnit :
    (smallExtendModuleRestriction S W V hVW).obj
        (𝟙_ (PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat))) =
      𝟙_ (PresheafOfModules.{u}
        (structurePresheaf (restrict S W V hVW) ⋙ forget₂ CommRingCat RingCat)) :=
  PresheafOfModules.pushforward₀OfCommRingCat_obj_tensorUnit _ _

/-- **Forming exterior powers commutes with restricting to the small crystalline site of a
restricted situation**: the restriction of `Ω^i_{X/S}` ([Stacks, Tag 07J4]) is the `i`-th
exterior power of the restriction of `Ω_{X/S}`. -/
theorem smallExtendModuleRestriction_obj_crysDifferentialForms (i : ℕ) :
    (smallExtendModuleRestriction S W V hVW).obj (crysDifferentialForms S i) =
      PresheafOfModules.extPow i
        ((smallExtendModuleRestriction S W V hVW).obj (crysDifferentials S)) := rfl

end SmallSite

end Crystalline.GlobalCrystallineSituation

end

end
