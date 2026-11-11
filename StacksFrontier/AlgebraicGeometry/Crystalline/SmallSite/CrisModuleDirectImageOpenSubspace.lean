module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanAdjunction
public import StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenSubspaceRestrictionInjective

/-!
# The direct image along the restriction of `f` to an open of `X`

Work in the situation of [Stacks, Tag 07MJ]: `f : X ⟶ X'` over a morphism of divided power schemes
`S ⟶ S'`, with direct image `f_{cris, *} : Mod(𝒪_{X/S}) ⥤ Mod(𝒪_{X'/S'})`
(`...SmallSite.crisModuleDirectImage`).  For an open `V` of `X` the restriction `f|_V : V ⟶ X'`
is again a morphism of situations, from `V/S`
(`Crystalline.GlobalCrystallineSituation.openSubspace`) to `X'/S'`, and this file identifies its
direct image:

`(f|_V)_{cris, *} ≅ f_{cris, *} ∘ j_{V, *}`,

where `j_{V, *} : Mod(𝒪_{V/S}) ⥤ Mod(𝒪_{X/S})` is the direct image along the inclusion of
`Cris(V/S)` (`...SmallSite.openSubspaceDirectImage`, whose sections over `A` are the sections over
`A|_V`).  This is the step of [Stacks, Tag 07ML] that turns the direct images of the restrictions
`F'`, `F''`, `F'''` into direct images along `f` of sheaves on `Cris(X/S)`.

## The argument

Both sides are right adjoints, and their left adjoints are restrictions of modules, which compose
on the nose.  `f_{cris, *}` is built in three stages, `i_{X, *}`, `f_{CRIS, *}` and `π_{X', *}`
(`...SmallSite.crisModuleDirectImage`); the first two are direct images along cocontinuous functors
of sites, right adjoint to restriction along them by
`Stacks.SheafOfModules.RestrictRan.sheafAdjunction`, the structure maps of this chapter being the
units of the Kan extension adjunction on the nose.  The left adjoint of
`i_{V, *}` followed by `(f|_V)_{CRIS, *}` is restriction along `Cris(V/S) ⥤ CRIS(X'/S')`, and that
of `j_{V, *}` followed by `i_{X, *}` and `f_{CRIS, *}` is restriction along
`Cris(V/S) ⥤ Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X'/S')`.  The two functors of sites agree up to the
identity of the underlying divided power thickenings, so the left adjoints are isomorphic, and
hence so are the right adjoints.  The last stage `π_{X', *}` is common to both sides.

No geometric input is needed beyond the coreflection of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/OpenSubspaceCoreflection.lean`: in particular
nothing like the domination argument of `SmallSite/CrisDirectImageCompositionIso.lean` enters,
because `j_{V, *}` lands in the *small* site and the composite never passes through
`π_{X, *}` followed by `i_{X, *}`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `bigModuleDirectImageAdjunction` and `changeBaseModuleDirectImageAdjunction` — the two module
  direct images of the big site as right adjoints to restriction.
* `openSubspaceRestrictCondition` — the compatibility of `f|_V` with the closed fibres.
* `openSubspaceChangeBaseIso` — the two functors `Cris(V/S) ⥤ CRIS(X'/S')`.
* `crisModuleDirectImageOpenSubspaceIso` — **`(f|_V)_{cris, *} ≅ f_{cris, *} ∘ j_{V, *}`**.

## References

* [Stacks Project, Tag 07ML](https://stacks.math.columbia.edu/tag/07ML)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Stacks.SheafOfModules.RestrictRan

/-! ### The big-site module direct images are right adjoint to restriction -/

section Adjunctions

variable (T T' : GlobalCrystallineSituation.{u}) (fS : T.S ⟶ T'.S) (fX : T.X ⟶ T'.X)
  (hf : T.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ T'.toClosedFiber)

/-- The structure map of the module-valued `i_{X, *}` is the unit of the Kan extension
adjunction. -/
theorem bigRingStructureMapULift_eq_sheafUnit :
    bigRingStructureMapULift T =
      sheafUnit (CrystallineThickening.ι T) (smallTopology T) (topology T)
        (bigStructureSheafULift T) :=
  rfl

/-- **The module-valued `i_{X, *}` is right adjoint to restriction of modules to the small
crystalline site.** -/
def bigModuleDirectImageAdjunction :
    SheafOfModules.pushforward.{u + 1} (𝟙 (Stacks.SheafOfModules.RestrictRan.ringSheaf
      (CrystallineThickening.ι T) (smallTopology T)
      (topology T) (bigStructureSheafULift T))) ⊣ bigModuleDirectImage T :=
  sheafAdjunction.{u + 1} (CrystallineThickening.ι T) (smallTopology T) (topology T)
    (bigStructureSheafULift T)

include hf in
/-- The structure map of the module-valued `f_{CRIS, *}` is the unit of the Kan extension
adjunction. -/
theorem changeBaseRingStructureMapULift_eq_sheafUnit :
    changeBaseRingStructureMapULift T T' fS fX hf =
      sheafUnit (changeBase T T' fS fX hf) (topology T) (topology T')
        (bigStructureSheafULift T') :=
  rfl

/-- **The module-valued `f_{CRIS, *}` is right adjoint to restriction of modules along change of
divided power base.** -/
def changeBaseModuleDirectImageAdjunction :
    SheafOfModules.pushforward.{u + 1} (𝟙 (Stacks.SheafOfModules.RestrictRan.ringSheaf
      (changeBase T T' fS fX hf) (topology T)
      (topology T') (bigStructureSheafULift T'))) ⊣ changeBaseModuleDirectImage T T' fS fX hf :=
  sheafAdjunction.{u + 1} (changeBase T T' fS fX hf) (topology T) (topology T')
    (bigStructureSheafULift T')

end Adjunctions

/-! ### The restriction of `f` to an open of `X` -/

variable {S S' : GlobalCrystallineSituation.{u}} {fS : S.S ⟶ S'.S} {fX : S.X ⟶ S'.X}
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)
  (V : S.X.Opens)

include hf in
/-- **The restriction `f|_V : V ⟶ X'` is a morphism of situations `V/S ⟶ X'/S'`**, over the same
morphism of divided power bases: the square of closed fibres of [Stacks, Tag 07MJ] restricts. -/
theorem openSubspaceRestrictCondition :
    (openSubspace S V).toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS =
      (V.ι ≫ fX) ≫ S'.toClosedFiber := by
  change (V.ι ≫ S.toClosedFiber) ≫ _ = _
  rw [Category.assoc, hf, Category.assoc]

/-- The comparison between the two readings of an object of `Cris(V/S)` in `CRIS(X'/S')`: the
identity of the underlying divided power thickening. -/
def openSubspaceChangeBaseHom (C : CrystallineThickening (openSubspace S V)) :
    (CrystallineThickening.ι (openSubspace S V) ⋙
        changeBase (openSubspace S V) S' fS (V.ι ≫ fX) (openSubspaceRestrictCondition hf V)).obj C ⟶
      (openSubspaceInclusion S V ⋙ CrystallineThickening.ι S ⋙ changeBase S S' fS fX hf).obj C where
  sourceHom := 𝟙 _
  targetHom := 𝟙 _
  immersion_naturality := by simp
  base_naturality := by
    change 𝟙 _ ≫ ((C.obj.toBase ≫ 𝟙 S.S) ≫ fS) = C.obj.toBase ≫ fS
    simp
  toX_naturality := by
    change 𝟙 _ ≫ ((C.obj.toX ≫ V.ι) ≫ fX) = C.obj.toX ≫ V.ι ≫ fX
    simp

/-- The inverse of `openSubspaceChangeBaseHom`, again the identity of the underlying divided power
thickening. -/
def openSubspaceChangeBaseInv (C : CrystallineThickening (openSubspace S V)) :
    (openSubspaceInclusion S V ⋙ CrystallineThickening.ι S ⋙ changeBase S S' fS fX hf).obj C ⟶
      (CrystallineThickening.ι (openSubspace S V) ⋙
        changeBase (openSubspace S V) S' fS (V.ι ≫ fX) (openSubspaceRestrictCondition hf V)).obj C
    where
  sourceHom := 𝟙 _
  targetHom := 𝟙 _
  immersion_naturality := by simp
  base_naturality := by
    change 𝟙 _ ≫ (C.obj.toBase ≫ fS) = (C.obj.toBase ≫ 𝟙 S.S) ≫ fS
    simp
  toX_naturality := by
    change 𝟙 _ ≫ (C.obj.toX ≫ V.ι ≫ fX) = (C.obj.toX ≫ V.ι) ≫ fX
    simp

/-- **The two functors `Cris(V/S) ⥤ CRIS(X'/S')`** — the inclusion of the small site of `V/S`
followed by change of base along `f|_V`, and the inclusion into `Cris(X/S)` followed by the
inclusion of the small site of `X/S` and change of base along `f` — agree up to the identity of
the underlying divided power thickenings. -/
def openSubspaceChangeBaseIso :
    CrystallineThickening.ι (openSubspace S V) ⋙
        changeBase (openSubspace S V) S' fS (V.ι ≫ fX) (openSubspaceRestrictCondition hf V) ≅
      openSubspaceInclusion S V ⋙ CrystallineThickening.ι S ⋙ changeBase S S' fS fX hf :=
  NatIso.ofComponents
    (fun C ↦
      { hom := openSubspaceChangeBaseHom hf V C
        inv := openSubspaceChangeBaseInv hf V C
        hom_inv_id := by
          apply Thickening.Hom.ext <;> simp [openSubspaceChangeBaseHom, openSubspaceChangeBaseInv]
        inv_hom_id := by
          apply Thickening.Hom.ext <;>
            simp [openSubspaceChangeBaseHom, openSubspaceChangeBaseInv] })
    (fun k ↦ by apply Thickening.Hom.ext <;> simp [openSubspaceChangeBaseHom])

/-! ### The left adjoints -/

/-- The composite `Cris(V/S) ⥤ CRIS(X'/S')` through `CRIS(V/S)` is continuous. -/
instance isContinuous_ι_comp_changeBase_openSubspace :
    (CrystallineThickening.ι (openSubspace S V) ⋙
      changeBase (openSubspace S V) S' fS (V.ι ≫ fX)
        (openSubspaceRestrictCondition hf V)).IsContinuous
      (smallTopology (openSubspace S V)) (topology S') :=
  Functor.isContinuous_comp _ _ _ (topology (openSubspace S V)) _

/-- The composite `CRIS(X/S) ⥤ CRIS(X'/S')` through `CRIS(X/S)` is continuous. -/
instance isContinuous_ι_comp_changeBase' :
    (CrystallineThickening.ι S ⋙ changeBase S S' fS fX hf).IsContinuous
      (smallTopology S) (topology S') :=
  Functor.isContinuous_comp _ _ _ (topology S) _

/-- The composite `Cris(V/S) ⥤ CRIS(X'/S')` through `Cris(X/S)` and `CRIS(X/S)` is continuous. -/
instance isContinuous_openSubspaceInclusion_comp_ι_comp_changeBase :
    (openSubspaceInclusion S V ⋙ CrystallineThickening.ι S ⋙ changeBase S S' fS fX hf).IsContinuous
      (smallTopology (openSubspace S V)) (topology S') :=
  Functor.isContinuous_comp _ _ _ (smallTopology S) _

/-- Restriction of modules from `CRIS(X'/S')` to `Cris(V/S)` along the inclusion of the small site
of `V/S` followed by change of base along `f|_V`. -/
abbrev openSubspaceRestrictAlongFirst :
    SheafOfModules.{u + 1} (bigStructureSheafULift S') ⥤
      SheafOfModules.{u + 1} (structureSheafULift (openSubspace S V)) :=
  SheafOfModules.pushforward.{u + 1}
    (F := CrystallineThickening.ι (openSubspace S V) ⋙
      changeBase (openSubspace S V) S' fS (V.ι ≫ fX) (openSubspaceRestrictCondition hf V))
    (R := bigStructureSheafULift S') (S := structureSheafULift (openSubspace S V)) ⟨𝟙 _⟩

/-- Restriction of modules from `CRIS(X'/S')` to `Cris(V/S)` along the inclusion into `Cris(X/S)`,
the inclusion of the small site of `X/S` and change of base along `f`. -/
abbrev openSubspaceRestrictAlongSecond :
    SheafOfModules.{u + 1} (bigStructureSheafULift S') ⥤
      SheafOfModules.{u + 1} (structureSheafULift (openSubspace S V)) :=
  SheafOfModules.pushforward.{u + 1}
    (F := openSubspaceInclusion S V ⋙ CrystallineThickening.ι S ⋙ changeBase S S' fS fX hf)
    (R := bigStructureSheafULift S') (S := structureSheafULift (openSubspace S V)) ⟨𝟙 _⟩

/-- The two restrictions along the functors of `openSubspaceChangeBaseIso` agree. -/
def openSubspaceRestrictAlongIso :
    openSubspaceRestrictAlongFirst hf V ≅ openSubspaceRestrictAlongSecond hf V :=
  SheafOfModules.pushforwardNatIso _ (openSubspaceChangeBaseIso hf V).symm ≪≫
    SheafOfModules.pushforwardCongr (by
      have key : ∀ C : CrystallineThickening (openSubspace S V),
          (GlobalCrystallineSituation.structureSheaf S').map
            (openSubspaceChangeBaseInv hf V C).op = 𝟙 _ := fun C ↦ by
        rw [GlobalCrystallineSituation.structureSheaf_map]
        simp [openSubspaceChangeBaseInv]
        rfl
      ext C x
      change ((forget₂ CommRingCat RingCat).map (SheafOfModules.commRingCatULift.map
        ((GlobalCrystallineSituation.structureSheaf S').map
          (openSubspaceChangeBaseInv hf V C.unop).op))) x = x
      rw [key]
      rfl)

/-- Restriction of modules along `CRIS(V/S) ⥤ CRIS(X'/S')` and then along the inclusion of the
small site of `V/S` is restriction along the composite. -/
def openSubspaceRestrictAlongFirstIso :
    SheafOfModules.pushforward.{u + 1} (𝟙 (Stacks.SheafOfModules.RestrictRan.ringSheaf
        (changeBase (openSubspace S V) S' fS (V.ι ≫ fX) (openSubspaceRestrictCondition hf V))
        (topology (openSubspace S V)) (topology S') (bigStructureSheafULift S'))) ⋙
      SheafOfModules.pushforward.{u + 1} (𝟙 (Stacks.SheafOfModules.RestrictRan.ringSheaf
        (CrystallineThickening.ι (openSubspace S V)) (smallTopology (openSubspace S V))
        (topology (openSubspace S V)) (bigStructureSheafULift (openSubspace S V)))) ≅
      openSubspaceRestrictAlongFirst hf V :=
  SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.pushforwardCongr (by ext C x; rfl)

/-- Restriction of modules along `CRIS(X/S) ⥤ CRIS(X'/S')`, then along the inclusion of the small
site of `X/S`, then to `Cris(V/S)`, is restriction along the composite. -/
def openSubspaceRestrictAlongSecondIso :
    openSubspaceRestrictAlongSecond hf V ≅
      SheafOfModules.pushforward.{u + 1} (𝟙 (Stacks.SheafOfModules.RestrictRan.ringSheaf
          (changeBase S S' fS fX hf) (topology S) (topology S') (bigStructureSheafULift S'))) ⋙
        SheafOfModules.pushforward.{u + 1} (𝟙 (Stacks.SheafOfModules.RestrictRan.ringSheaf
          (CrystallineThickening.ι S) (smallTopology S) (topology S) (bigStructureSheafULift S))) ⋙
        openSubspaceModuleRestrictionULift V :=
  SheafOfModules.pushforwardCongr (by ext C x; rfl) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm ≪≫
    Functor.isoWhiskerRight (SheafOfModules.pushforwardComp _ _).symm _

/-- **The left adjoints of the two sides agree**: restricting a module on `CRIS(X'/S')` to
`Cris(V/S)` along the two functors of `openSubspaceChangeBaseIso` gives isomorphic modules, read as
modules over the structure sheaf of `Cris(V/S)` itself. -/
def openSubspaceLeftAdjointIso :
    (SheafOfModules.pushforward.{u + 1} (𝟙 (Stacks.SheafOfModules.RestrictRan.ringSheaf
        (changeBase (openSubspace S V) S' fS (V.ι ≫ fX) (openSubspaceRestrictCondition hf V))
        (topology (openSubspace S V)) (topology S') (bigStructureSheafULift S'))) ⋙
      SheafOfModules.pushforward.{u + 1} (𝟙 (Stacks.SheafOfModules.RestrictRan.ringSheaf
        (CrystallineThickening.ι (openSubspace S V)) (smallTopology (openSubspace S V))
        (topology (openSubspace S V)) (bigStructureSheafULift (openSubspace S V))))) ⋙
        moduleRingULiftDown (openSubspace S V) ≅
    ((SheafOfModules.pushforward.{u + 1} (𝟙 (Stacks.SheafOfModules.RestrictRan.ringSheaf
        (changeBase S S' fS fX hf) (topology S) (topology S') (bigStructureSheafULift S'))) ⋙
      SheafOfModules.pushforward.{u + 1} (𝟙 (Stacks.SheafOfModules.RestrictRan.ringSheaf
        (CrystallineThickening.ι S) (smallTopology S) (topology S) (bigStructureSheafULift S)))) ⋙
        moduleRingULiftDown S) ⋙ openSubspaceModuleRestriction S V :=
  Functor.isoWhiskerRight (openSubspaceRestrictAlongFirstIso hf V ≪≫
      openSubspaceRestrictAlongIso hf V ≪≫ openSubspaceRestrictAlongSecondIso hf V)
    (moduleRingULiftDown (openSubspace S V)) ≪≫ eqToIso rfl

/-! ### The direct image along `f|_V` -/

/-- **`(f|_V)_{cris, *} ≅ f_{cris, *} ∘ j_{V, *}`**: the direct image of sheaves of modules along
the restriction of `f` to an open `V` of `X` is the direct image along `f` of the direct image along
the inclusion of `Cris(V/S)` into `Cris(X/S)`.  Both are right adjoints whose left adjoints are
isomorphic by `openSubspaceLeftAdjointIso`; the last stage `π_{X', *}` is common to both. -/
def crisModuleDirectImageOpenSubspaceIso :
    crisModuleDirectImage (openSubspace S V) S' fS (V.ι ≫ fX) (openSubspaceRestrictCondition hf V) ≅
      openSubspaceDirectImage V ⋙ crisModuleDirectImage S S' fS fX hf :=
  Functor.isoWhiskerRight (Adjunction.rightAdjointUniq
      ((((changeBaseModuleDirectImageAdjunction (openSubspace S V) S' fS (V.ι ≫ fX)
          (openSubspaceRestrictCondition hf V)).comp
          (bigModuleDirectImageAdjunction (openSubspace S V))).comp
          (moduleRingULiftEquivalence (openSubspace S V)).symm.toAdjunction).ofNatIsoLeft
        (openSubspaceLeftAdjointIso hf V))
      ((((changeBaseModuleDirectImageAdjunction S S' fS fX hf).comp
          (bigModuleDirectImageAdjunction S)).comp
          (moduleRingULiftEquivalence S).symm.toAdjunction).comp
          (openSubspaceRestrictionAdjunction V)))
    (smallModuleRestrictionULift S' ⋙ moduleRingULiftDown S')

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
