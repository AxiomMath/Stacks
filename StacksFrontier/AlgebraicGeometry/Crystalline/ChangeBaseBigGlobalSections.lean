module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleDirectImageInclusion

/-!
# Global sections over `CRIS(X/S)` and change of divided power base

Let `(S, I, γ) ⟶ (S', I', γ')` be a morphism of affine divided power bases, carried by
`f : S.S ⟶ S'.S`, and let `g : X ⟶ Y` be compatible with it over the closed fibres.  Change of
divided power base is the functor `u = changeBase S S' f g h : CRIS(X/S) ⥤ CRIS(Y/S')` of
[Stacks, Tag 07IC]; it leaves the underlying divided power thickening of an object untouched and
only composes the structure maps `T ⟶ S` and `U ⟶ X` with `f` and with `g`.  Because of that the
structure sheaf is preserved on the nose,
`Crystalline.GlobalCrystallineSituation.changeBase_op_comp_crisRing`, and the pullback of sheaves
of modules along `u` is plain restriction,
`Crystalline.GlobalCrystallineSituation.changeBaseModulePullback`.

This file reads what `u` does to **global sections of modules** on the big crystalline site: for a
sheaf `N` of `𝒪_{Y/S'}`-modules on `CRIS(Y/S')` there is a map

`Γ(CRIS(Y/S'), N) ⟶ Γ(CRIS(X/S), u^* N)`,

a compatible family `(s_B)` of sections of `N` going to the family `(s_{u(A)})`, and it is
**semilinear** over the ring map `Γ(CRIS(Y/S'), 𝒪_{Y/S'}) ⟶ Γ(CRIS(X/S), 𝒪_{X/S})` obtained the
same way from the structure sheaf.  Over the base rings that semilinearity is semilinearity over
`A' = Γ(S', 𝒪_{S'}) ⟶ A = Γ(S, 𝒪_S)`:
`changeBaseSectionRingHom_comp_bigBaseRingHom` says the square of ring maps commutes.

## Why this is wanted

It is the underived shape of the first arrow of [Stacks, Tag 07N5] — and of the base change map
(07MT) of [Stacks, Tag 07MS].  `...SmallSite.FrobeniusMap07N5` is the type of that first arrow and
`...SmallSite.SigmaSemilinearAction07N5` measures it exactly as a `σ`-semilinear endomorphism of
`RΓ(Cris(X/S), E)`; no term of either type is constructed in the library, and the module
documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusSemilinearAction.lean` records why:
the `σ`-semilinear bookkeeping on global sections that
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMap.lean` carries
(`smallChangeBaseSectionRingHom`, `smallChangeBaseSectionsMap`,
`baseChangeGlobalSectionsTrans`) is built from `...GlobalCrystallineSituation.smallChangeBase` and
therefore assumes `g` is an open immersion, which the absolute Frobenius of `X` is not.

The bookkeeping below assumes nothing about `g`.  It is possible on the **big** site precisely
because `u` is an endofunctor of a single category there, with the structure sheaf preserved on the
nose, so no open immersion and no comparison of structure sheaves is involved.  The Frobenius case
is `StacksFrontier/AlgebraicGeometry/Crystalline/FrobeniusBigGlobalSections.lean`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation`.

* `crystalModuleGlobalSections` — `Γ(CRIS(X/S), -)` at the module universe `u` of this chapter's
  crystals, as a functor to modules over `Γ(CRIS(X/S), 𝒪_{X/S})`.  It is
  `Stacks.Cohomology.SiteModules.globalSectionsFunctor` instantiated at
  `crystallineStructureSheaf`, and differs from
  `...SmallSite.bigModuleGlobalSections` only in that module universe: that one is at `u + 1`,
  the universe of `...SmallSite.BigModuleSheaf`, and `Crystalline.FCrystal.crystal` lives at `u`.
* `crystalBaseModuleGlobalSections` — the same functor with the scalars restricted to
  `A = Γ(S, 𝒪_S)` along `...SmallSite.bigBaseRingHom`.
* `changeBaseSectionRingHom` — the ring map `Γ(CRIS(Y/S'), 𝒪_{Y/S'}) ⟶ Γ(CRIS(X/S), 𝒪_{X/S})`
  induced by change of divided power base.
* `changeBaseSections` — the comparison on global sections of a module.
* `changeBaseGlobalSectionsMap` and `changeBaseGlobalSectionsTrans` — that comparison as a
  morphism of modules over `Γ(CRIS(Y/S'), 𝒪_{Y/S'})` into the restriction of scalars of its
  target, and as a natural transformation of functors.
* `changeBaseBaseGlobalSectionsMap` and `changeBaseBaseGlobalSectionsTrans` — the same over the
  base rings, semilinear over `...SmallSite.baseChangeRingHom f`.

## Main results

* `changeBaseSections_smul` — the comparison is semilinear over `changeBaseSectionRingHom`.
* `changeBaseSectionRingHom_comp_bigBaseRingHom` — **the two base scalars agree**: the ring map on
  `Γ(CRIS, 𝒪)` composed with the base scalars of `S'` is the base scalars of `S` composed with
  `A' ⟶ A`.  This is what makes the comparison semilinear over `A' ⟶ A` and, in the Frobenius
  case, over `σ`.
* `changeBaseSections_val` — the value of the pulled back section at an object is the value of the
  original one at its image, which pins the comparison down completely.

## What is and is not proved

No `@[stacks]` attribute is placed here.  The comparison on global sections is infrastructure: it
is a construction and its semilinearity, not an assertion of the chapter.  In particular this file
proves nothing about [Stacks, Tag 07MS], [Stacks, Tag 07MU] or [Stacks, Tag 07N5], and nothing
about derived global sections — `RΓ` is where the first arrow of [Stacks, Tag 07N5] has to live,
and passing from `Γ(CRIS(X/S), -)` to `RΓ(Cris(X/S), -)` needs the comparison of derived global
sections across the inclusion `i : Cris(X/S) ⥤ CRIS(X/S)`.  Of that comparison the library has the
direction `RΓ(Cris(X/S), M) ≅ RΓ(CRIS(X/S), R i_* M)`
(`...SmallSite.derivedModuleGlobalSectionsObjIsoDirectImage`) and the underived
`Γ(CRIS(X/S), N) ≅ Γ(Cris(X/S), i^{-1} N)` (`...SmallSite.restrictModuleGlobalSectionsIso`, at the
module universe `u + 1`); what it does not have is `RΓ(CRIS(X/S), N) ≅ RΓ(Cris(X/S), i^{-1} N)`,
which needs `Γ(Cris(X/S), -)`-acyclicity of `i^{-1} I` for `I` injective on `CRIS(X/S)` and is
open.  Injectivity-preservation by `i^{-1}` would give it and is **false**, being equivalent to
exactness of the module-level `i_!`
(`Stacks.SheafOfModules.lowerShriek_not_preservesFiniteLimits`).

## References

* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IX](https://stacks.math.columbia.edu/tag/07IX)
* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

/-! ### Global sections on `CRIS(X/S)` at the crystals' module universe -/

/-- **`Γ(CRIS(X/S), -)` at the module universe `u` of this chapter's crystals**, valued in modules
over the ring `Γ(CRIS(X/S), 𝒪_{X/S})` of global sections of the structure sheaf.

This is `Stacks.Cohomology.SiteModules.globalSectionsFunctor` at
`Crystalline.GlobalCrystallineSituation.crystallineStructureSheaf`.  It is the same construction as
`Crystalline.GlobalCrystallineSituation.SmallSite.bigModuleGlobalSections`, at a different module
universe: that one is at `u + 1`, the universe of `...SmallSite.BigModuleSheaf`, while
`Crystalline.FCrystal.crystal` and `...SmallSite.FrobeniusMap07N5` live at `u`. -/
abbrev crystalModuleGlobalSections (S : GlobalCrystallineSituation.{u}) :
    SheafOfModules.{u} (crystallineStructureSheaf S) ⥤
      ModuleCat.{u + 1} ↥(SmallSite.bigCrystallineSectionRing S) :=
  Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
    (crystallineStructureSheaf S)

/-- **`Γ(CRIS(X/S), -)` as a functor to `A`-modules**, `A = Γ(S, 𝒪_S)`: the scalars of
`crystalModuleGlobalSections` restricted along `...SmallSite.bigBaseRingHom`. -/
abbrev crystalBaseModuleGlobalSections (S : GlobalCrystallineSituation.{u}) :
    SheafOfModules.{u} (crystallineStructureSheaf S) ⥤ ModuleCat.{u + 1} Γ(S.S.scheme, ⊤) :=
  crystalModuleGlobalSections S ⋙ ModuleCat.restrictScalars (SmallSite.bigBaseRingHom S)

section ChangeBase

variable (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)

/-- **The ring map `Γ(CRIS(Y/S'), 𝒪_{Y/S'}) ⟶ Γ(CRIS(X/S), 𝒪_{X/S})` induced by change of divided
power base.**  A compatible family of sections of the structure sheaf of `CRIS(Y/S')` is read at
the images of the objects of `CRIS(X/S)`; the values live in the same rings, change of base leaving
the ambient scheme of an object untouched, and compatibility is inherited because change of base is
a functor. -/
def changeBaseSectionRingHom :
    ↥(SmallSite.bigCrystallineSectionRing S') →+* ↥(SmallSite.bigCrystallineSectionRing S) where
  toFun a := ⟨fun A => a.val (op ((changeBase S S' f g h).obj A.unop)),
    fun {_ _} k => a.2 ((changeBase S S' f g h).op.map k)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The comparison on global sections of a module**: a compatible family of sections of a sheaf
of `𝒪_{Y/S'}`-modules on `CRIS(Y/S')`, read at the images of the objects of `CRIS(X/S)`, is a
global section of the pullback `u^* N` along change of divided power base — the pullback being
plain restriction along `u`, `changeBaseModulePullback`. -/
def changeBaseSections (N : SheafOfModules.{u} (crystallineStructureSheaf S'))
    (x : N.sections) : ((changeBaseModulePullback S S' f g h).obj N).sections :=
  ⟨fun A => x.val (op ((changeBase S S' f g h).obj A.unop)),
    fun {_ _} k => x.2 ((changeBase S S' f g h).op.map k)⟩

variable {S S' f g h}

/-- The value of the pulled back scalar at an object is the value of the original one at its
image. -/
@[simp]
theorem changeBaseSectionRingHom_apply_val (a : ↥(SmallSite.bigCrystallineSectionRing S'))
    (A : (Thickening S)ᵒᵖ) :
    (changeBaseSectionRingHom S S' f g h a).val A =
      a.val (op ((changeBase S S' f g h).obj A.unop)) := rfl

/-- The value of the pulled back section at an object is the value of the original one at its
image. -/
@[simp]
theorem changeBaseSections_val (N : SheafOfModules.{u} (crystallineStructureSheaf S'))
    (x : N.sections) (A : (Thickening S)ᵒᵖ) :
    (changeBaseSections S S' f g h N x).val A =
      x.val (op ((changeBase S S' f g h).obj A.unop)) := rfl

/-- The comparison on global sections is additive. -/
theorem changeBaseSections_add (N : SheafOfModules.{u} (crystallineStructureSheaf S'))
    (x y : N.sections) :
    changeBaseSections S S' f g h N (x + y) =
      changeBaseSections S S' f g h N x + changeBaseSections S S' f g h N y := rfl

/-- **The comparison on global sections is semilinear over `changeBaseSectionRingHom`.**  Both
sides are the family whose value at an object is the product, in the ring of the ambient scheme of
that object, of the two values at its image. -/
theorem changeBaseSections_smul (N : SheafOfModules.{u} (crystallineStructureSheaf S'))
    (a : ↥(SmallSite.bigCrystallineSectionRing S')) (x : N.sections) :
    changeBaseSections S S' f g h N (a • x) =
      changeBaseSectionRingHom S S' f g h a • changeBaseSections S S' f g h N x := rfl

/-- The comparison on global sections is natural in the module. -/
theorem changeBaseSections_sectionsMap {N N' : SheafOfModules.{u} (crystallineStructureSheaf S')}
    (ψ : N ⟶ N') (x : N.sections) :
    changeBaseSections S S' f g h N' (SheafOfModules.sectionsMap ψ x) =
      SheafOfModules.sectionsMap ((changeBaseModulePullback S S' f g h).map ψ)
        (changeBaseSections S S' f g h N x) := rfl

/-- **The comparison on global sections as a semilinear morphism of modules**: a map from
`Γ(CRIS(Y/S'), N)` to the restriction of scalars of `Γ(CRIS(X/S), u^* N)` along
`changeBaseSectionRingHom`. -/
def changeBaseGlobalSectionsMap (N : SheafOfModules.{u} (crystallineStructureSheaf S')) :
    (crystalModuleGlobalSections S').obj N ⟶
      (ModuleCat.restrictScalars (changeBaseSectionRingHom S S' f g h)).obj
        ((crystalModuleGlobalSections S).obj
          ((changeBaseModulePullback S S' f g h).obj N)) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (changeBaseSectionRingHom S S' f g h)).obj
      ((crystalModuleGlobalSections S).obj ((changeBaseModulePullback S S' f g h).obj N)))
    { toFun := changeBaseSections S S' f g h N
      map_add' := changeBaseSections_add N
      map_smul' := changeBaseSections_smul N }

/-- **The comparison on global sections as a natural transformation of functors.** -/
def changeBaseGlobalSectionsTrans :
    crystalModuleGlobalSections S' ⟶
      changeBaseModulePullback S S' f g h ⋙ crystalModuleGlobalSections S ⋙
        ModuleCat.restrictScalars (changeBaseSectionRingHom S S' f g h) where
  app N := changeBaseGlobalSectionsMap N
  naturality _ _ ψ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact changeBaseSections_sectionsMap ψ x

/-! ### Compatibility with the base rings -/

/-- **The two base scalars agree.**  Pulling the base scalar attached to `a ∈ A'` back along change
of divided power base gives the base scalar attached to its image in `A`: the structure morphism to
`S'` of the image of an object is its structure morphism to `S` followed by `f`, so both families
have as value at an object the pullback of `a` along that composite. -/
theorem changeBaseSectionRingHom_comp_bigBaseRingHom :
    (changeBaseSectionRingHom S S' f g h).comp (SmallSite.bigBaseRingHom S') =
      (SmallSite.bigBaseRingHom S).comp (SmallSite.baseChangeRingHom f) := by
  refine RingHom.ext fun a => Subtype.ext (funext fun A => ?_)
  change (Scheme.Γ.map (A.unop.toBase ≫ f).hom.op).hom a =
    (Scheme.Γ.map A.unop.toBase.hom.op).hom ((Scheme.Γ.map f.hom.op).hom a)
  rw [DividedPowerScheme.Hom.comp_hom, op_comp, Functor.map_comp]
  rfl

/-- The comparison on global sections is semilinear over `A' ⟶ A`, a restatement of
`changeBaseSections_smul` through `changeBaseSectionRingHom_comp_bigBaseRingHom`. -/
theorem changeBaseSections_smul_base (N : SheafOfModules.{u} (crystallineStructureSheaf S'))
    (a : Γ(S'.S.scheme, ⊤)) (x : N.sections) :
    changeBaseSections S S' f g h N (SmallSite.bigBaseRingHom S' a • x) =
      SmallSite.bigBaseRingHom S (SmallSite.baseChangeRingHom f a) •
        changeBaseSections S S' f g h N x := by
  rw [changeBaseSections_smul]
  exact congrArg (fun b => b • changeBaseSections S S' f g h N x)
    (congrFun (congrArg (fun φ : Γ(S'.S.scheme, ⊤) →+* _ => (φ : Γ(S'.S.scheme, ⊤) → _))
      changeBaseSectionRingHom_comp_bigBaseRingHom) a)

/-- **The comparison on global sections, over the base rings**: a map from `Γ(CRIS(Y/S'), N)` as an
`A'`-module to the restriction of scalars along `A' ⟶ A` of `Γ(CRIS(X/S), u^* N)` as an
`A`-module. -/
def changeBaseBaseGlobalSectionsMap (N : SheafOfModules.{u} (crystallineStructureSheaf S')) :
    (crystalBaseModuleGlobalSections S').obj N ⟶
      (ModuleCat.restrictScalars (SmallSite.baseChangeRingHom f)).obj
        ((crystalBaseModuleGlobalSections S).obj
          ((changeBaseModulePullback S S' f g h).obj N)) :=
  ModuleCat.ofHom
    (X := (crystalBaseModuleGlobalSections S').obj N)
    (Y := (ModuleCat.restrictScalars (SmallSite.baseChangeRingHom f)).obj
      ((crystalBaseModuleGlobalSections S).obj ((changeBaseModulePullback S S' f g h).obj N)))
    { toFun := changeBaseSections S S' f g h N
      map_add' := changeBaseSections_add N
      map_smul' := changeBaseSections_smul_base N }

/-- **The comparison on global sections over the base rings, as a natural transformation.** -/
def changeBaseBaseGlobalSectionsTrans :
    crystalBaseModuleGlobalSections S' ⟶
      changeBaseModulePullback S S' f g h ⋙ crystalBaseModuleGlobalSections S ⋙
        ModuleCat.restrictScalars (SmallSite.baseChangeRingHom f) where
  app N := changeBaseBaseGlobalSectionsMap N
  naturality _ _ ψ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact changeBaseSections_sectionsMap ψ x

end ChangeBase

end Crystalline.GlobalCrystallineSituation

end

end
