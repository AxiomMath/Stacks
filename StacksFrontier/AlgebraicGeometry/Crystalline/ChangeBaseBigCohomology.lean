module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ChangeBaseBigGlobalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleRestrictionCohomologyULift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactCocontinuous

/-!
# Change of divided power base on `CRIS(X/S)` at the module universe of the cohomology

For change of divided power base `u = changeBase S S' f g h : CRIS(X/S) ⥤ CRIS(Y/S')`, this file
builds the pullback `u^*` and the comparison on global sections

`Γ(CRIS(Y/S'), N) ⟶ Γ(CRIS(X/S), u^* N)`,

semilinear over `A' ⟶ A`, at the module universe `u + 1` of `...SmallSite.BigModuleSheaf`, and
records that the pullback agrees with the one at the module universe `u` through the universe
lift `...SmallSite.bigModuleULift`, on the nose.  No hypothesis is placed on `g` or on `N`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation`.

* `changeBaseBigModulePullback` — **`u^* : BigModuleSheaf S' ⥤ BigModuleSheaf S`**, restriction
  along change of divided power base at the module universe of the cohomology.
* `changeBaseBigSections` and `changeBaseBigBaseGlobalSectionsMap` — the comparison on global
  sections and its bundling as a map of `A'`-modules into a restriction of scalars along
  `...SmallSite.baseChangeRingHom f`, which is what a semilinear map is.
* `changeBaseBigBaseGlobalSectionsTrans` — **the comparison as a natural transformation**
  `Γ_{S'} ⟶ u^* ⋙ Γ_S ⋙ res`.

## Main results

* `changeBaseBigModulePullback_preservesFiniteLimits` and
  `changeBaseBigModulePullback_preservesFiniteColimits` — **`u^*` is exact**, being the direct
  image of sheaves of modules along a continuous and cocontinuous functor of sites,
  [Stacks, Tag 04BD](2).
* `bigModuleULift_comp_changeBaseBigModulePullback` — raising the module universe commutes with
  the pullback, definitionally.

## References

* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 04BD](https://stacks.math.columbia.edu/tag/04BD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

section ChangeBase

variable (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)

/-- **The pullback `u^*` along change of divided power base, at the module universe `u + 1`.**
Its sections over an object `(U, T, δ)` of `CRIS(X/S)` are the sections of `N` over the image of
`(U, T, δ)` under change of base — the same ambient scheme `T`, with `U ⟶ X ⟶ Y` and
`T ⟶ S ⟶ S'` as its structure maps.

No tensor product and no sheafification occur: the comparison of structure sheaves is the identity
`changeBaseStructureHom`, change of base leaving the ambient scheme of an object untouched, and
change of base is continuous. -/
def changeBaseBigModulePullback :
    SmallSite.BigModuleSheaf S' ⥤ SmallSite.BigModuleSheaf S :=
  SheafOfModules.pushforward.{u + 1} (changeBaseStructureHom S S' f g h)

/-- The pullback acts on sections by restriction, which is additive on the nose. -/
instance changeBaseBigModulePullback_additive :
    (changeBaseBigModulePullback S S' f g h).Additive where
  map_add := by intros; rfl

/-- **The pullback preserves finite limits**, being a direct image of sheaves of modules along a
continuous functor of sites and hence a right adjoint: the left exact half of
[Stacks, Tag 04BD](2). -/
instance changeBaseBigModulePullback_preservesFiniteLimits :
    PreservesFiniteLimits (changeBaseBigModulePullback S S' f g h) :=
  SheafOfModules.preservesFiniteLimits_pushforward _

/-- **The pullback preserves finite colimits**, change of divided power base being cocontinuous
as well as continuous: the right exact half of [Stacks, Tag 04BD](2). -/
instance changeBaseBigModulePullback_preservesFiniteColimits :
    PreservesFiniteColimits (changeBaseBigModulePullback S S' f g h) :=
  (SheafOfModules.exactFunctor_pushforward_of_isCocontinuous (changeBase S S' f g h)
    (changeBaseStructureHom S S' f g h)).2

/-- **Raising the module universe commutes with the pullback, on the nose.**  Both composites send
`N` to the sheaf whose sections over an object of `CRIS(X/S)` are `ULift` of the sections of `N`
over the image of that object, and the two sheaves of modules are definitionally equal. -/
theorem bigModuleULift_comp_changeBaseBigModulePullback :
    changeBaseModulePullback S S' f g h ⋙ SmallSite.bigModuleULift S =
      SmallSite.bigModuleULift S' ⋙ changeBaseBigModulePullback S S' f g h :=
  rfl

/-- **The comparison on global sections at the module universe of the cohomology**: a compatible
family of sections of a sheaf of `𝒪_{Y/S'}`-modules on `CRIS(Y/S')`, read at the images of the
objects of `CRIS(X/S)`, is a global section of the pullback `u^* N`. -/
def changeBaseBigSections (N : SmallSite.BigModuleSheaf S') (x : N.sections) :
    ((changeBaseBigModulePullback S S' f g h).obj N).sections :=
  ⟨fun A => x.val (op ((changeBase S S' f g h).obj A.unop)),
    fun {_ _} k => x.2 ((changeBase S S' f g h).op.map k)⟩

variable {S S' f g h}

/-- The value of the pulled back section at an object is the value of the original one at its
image. -/
@[simp]
theorem changeBaseBigSections_val (N : SmallSite.BigModuleSheaf S') (x : N.sections)
    (A : (Thickening S)ᵒᵖ) :
    (changeBaseBigSections S S' f g h N x).val A =
      x.val (op ((changeBase S S' f g h).obj A.unop)) := rfl

/-- The comparison on global sections is additive. -/
theorem changeBaseBigSections_add (N : SmallSite.BigModuleSheaf S') (x y : N.sections) :
    changeBaseBigSections S S' f g h N (x + y) =
      changeBaseBigSections S S' f g h N x + changeBaseBigSections S S' f g h N y := rfl

/-- The comparison on global sections is semilinear over `changeBaseSectionRingHom`. -/
theorem changeBaseBigSections_smul (N : SmallSite.BigModuleSheaf S')
    (a : ↥(SmallSite.bigCrystallineSectionRing S')) (x : N.sections) :
    changeBaseBigSections S S' f g h N (a • x) =
      changeBaseSectionRingHom S S' f g h a • changeBaseBigSections S S' f g h N x := rfl

/-- **The comparison on global sections is semilinear over `A' ⟶ A`.** -/
theorem changeBaseBigSections_smul_base (N : SmallSite.BigModuleSheaf S')
    (a : Γ(S'.S.scheme, ⊤)) (x : N.sections) :
    changeBaseBigSections S S' f g h N (SmallSite.bigBaseRingHom S' a • x) =
      SmallSite.bigBaseRingHom S (SmallSite.baseChangeRingHom f a) •
        changeBaseBigSections S S' f g h N x := by
  rw [changeBaseBigSections_smul]
  exact congrArg (fun b => b • changeBaseBigSections S S' f g h N x)
    (congrFun (congrArg (fun φ : Γ(S'.S.scheme, ⊤) →+* _ => (φ : Γ(S'.S.scheme, ⊤) → _))
      changeBaseSectionRingHom_comp_bigBaseRingHom) a)

/-- The comparison on global sections is natural in the module. -/
theorem changeBaseBigSections_sectionsMap
    {N N' : SmallSite.BigModuleSheaf S'} (ψ : N ⟶ N') (x : N.sections) :
    changeBaseBigSections S S' f g h N' (SheafOfModules.sectionsMap ψ x) =
      SheafOfModules.sectionsMap ((changeBaseBigModulePullback S S' f g h).map ψ)
        (changeBaseBigSections S S' f g h N x) := rfl

/-- **The comparison on global sections over the base rings**, a map from `Γ(CRIS(Y/S'), N)` as an
`A'`-module to the restriction of scalars along `A' ⟶ A` of `Γ(CRIS(X/S), u^* N)` as an
`A`-module.  A map into such a restriction of scalars is exactly a semilinear map, by Mathlib's
`ModuleCat.semilinearMapAddEquiv`. -/
def changeBaseBigBaseGlobalSectionsMap (N : SmallSite.BigModuleSheaf S') :
    (SmallSite.bigBaseModuleGlobalSections S').obj N ⟶
      (ModuleCat.restrictScalars (SmallSite.baseChangeRingHom f)).obj
        ((SmallSite.bigBaseModuleGlobalSections S).obj
          ((changeBaseBigModulePullback S S' f g h).obj N)) :=
  ModuleCat.ofHom
    (X := (SmallSite.bigBaseModuleGlobalSections S').obj N)
    (Y := (ModuleCat.restrictScalars (SmallSite.baseChangeRingHom f)).obj
      ((SmallSite.bigBaseModuleGlobalSections S).obj
        ((changeBaseBigModulePullback S S' f g h).obj N)))
    { toFun := changeBaseBigSections S S' f g h N
      map_add' := changeBaseBigSections_add N
      map_smul' := changeBaseBigSections_smul_base N }

/-- **The comparison on global sections as a natural transformation**

`Γ(CRIS(Y/S'), -) ⟶ u^* ⋙ Γ(CRIS(X/S), -) ⋙ res`,

semilinear over `...SmallSite.baseChangeRingHom f`. -/
def changeBaseBigBaseGlobalSectionsTrans (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    SmallSite.bigBaseModuleGlobalSections S' ⟶
      changeBaseBigModulePullback S S' f g h ⋙ SmallSite.bigBaseModuleGlobalSections S ⋙
        ModuleCat.restrictScalars (SmallSite.baseChangeRingHom f) where
  app N := changeBaseBigBaseGlobalSectionsMap N
  naturality _ _ ψ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    exact changeBaseBigSections_sectionsMap ψ x

end ChangeBase

end Crystalline.GlobalCrystallineSituation

end

end
