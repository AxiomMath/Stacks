module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationOfPresentation

/-!
# The universe lift of a presheaf of modules, and the tensor product

`SheafOfModules.uliftForPresentation` raises the universe of the sections of a sheaf of modules
while keeping its coefficient ring sheaf; it is the operation in whose target
`SheafOfModules.HasGlobalPresentation` states a global presentation.  This file provides the
same operation for *presheaves* of modules, together with two facts about it: it commutes with
the objectwise tensor product of presheaves of modules, and it preserves local bijectivity, hence
sheafification.

The comparison with the tensor product is linear over the ring of sections rather than
semilinear, because the ring sheaf is not lifted: only the module sections are.

## Main definitions

* `Stacks.SheafOfModules.UliftTensor.presheafUlift` and
  `Stacks.SheafOfModules.UliftTensor.presheafUliftMap`: the objectwise universe lift of a
  presheaf of modules and of a morphism of such.
* `Stacks.SheafOfModules.UliftTensor.presheafUliftTensorIso`: the universe lift of an objectwise
  tensor product is the objectwise tensor product of the universe lifts.
* `Stacks.SheafOfModules.UliftTensor.sheafifyUnit`: the sheafification unit of a presheaf of
  modules, at a module universe independent of the ring universe.
* `Stacks.SheafOfModules.UliftTensor.isoOfLocallyBijective`: two sheaves of modules receiving
  locally bijective maps from isomorphic presheaves of modules are isomorphic.

## Implementation notes

`presheafUlift` is written out with the same objectwise formula as
`SheafOfModules.uliftForPresentation`, so that `uliftForPresentation_val` holds by `rfl` and
the two operations can be used interchangeably.

`sheafifyUnit` is `Stacks.SheafOfModules.TensorLocalProperties.sheafificationUnit` with the module
universe freed from the ring universe, and `isoOfLocallyBijective` is the statement of
`Stacks.SheafOfModules.TensorLocalProperties.iso_of_locallyBijective`, which is available only
when the module universe equals the ring universe; here the two are independent, so the
extension principle is taken from Mathlib's `PresheafOfModules.homEquivOfIsLocallyBijective`
instead.  That needs `J.WEqualsLocallyBijective AddCommGrpCat` at the module universe, which at
the raised universe of a global presentation comes free from
`AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat`.

The local-bijectivity statements here, and the four hypotheses of `isoOfLocallyBijective`, are
explicit arguments rather than instances.  Instance resolution cannot find them at the universes
this file is used in: the module universe of a universe lift is a `max`, and unifying `max t z`
against the `max u v w` of a global presentation is not a problem the level unifier solves.

## References

* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct

universe u v w z z₁ t

namespace Stacks.SheafOfModules.UliftTensor

variable {C : Type u} [Category.{v} C]

variable {C : Type u} [Category.{v} C]

section Presheaf

variable {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- The objectwise universe lift of a presheaf of modules.  This is the underlying presheaf of
`SheafOfModules.uliftForPresentation`, available for presheaves and for a presheaf of rings. -/
noncomputable def presheafUlift (M : PresheafOfModules.{z} R) :
    PresheafOfModules.{max t z} R :=
  { obj := fun X ↦ ModuleCat.of (R.obj X) (ULift.{t} (M.obj X))
    map := fun {X Y} f ↦ ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
        (ModuleCat.of (R.obj Y) (ULift.{t} (M.obj Y)))) {
      toFun := fun x ↦ ULift.up (M.map f x.down)
      map_add' := fun x y ↦ congrArg ULift.up (map_add (M.map f).hom x.down y.down)
      map_smul' := fun a x ↦ congrArg ULift.up (M.map_smul f a x.down) }
    map_id := fun X ↦ by ext x; exact congrArg ULift.up (by simp)
    map_comp := fun f g ↦ by ext x; exact congrArg ULift.up (M.map_comp_apply f g x.down) }

/-- The objectwise universe lift of a morphism of presheaves of modules. -/
noncomputable def presheafUliftMap {M N : PresheafOfModules.{z} R} (φ : M ⟶ N) :
    presheafUlift.{u, v, w, z, t} M ⟶ presheafUlift.{u, v, w, z, t} N :=
  { app := fun X ↦ ModuleCat.ofHom
      (X := ModuleCat.of (R.obj X) (ULift.{t} (M.obj X)))
      (Y := ModuleCat.of (R.obj X) (ULift.{t} (N.obj X))) {
      toFun := fun x ↦ ULift.up (φ.app X x.down)
      map_add' := fun x y ↦ congrArg ULift.up (map_add (φ.app X).hom x.down y.down)
      map_smul' := fun a x ↦ congrArg ULift.up (map_smul (φ.app X).hom a x.down) }
    naturality := fun {X Y} f ↦ by
      ext x
      exact congrArg ULift.up (PresheafOfModules.naturality_apply φ f x.down) }

variable {J : GrothendieckTopology C}

/-- The universe lift of a locally injective morphism of presheaves of modules is locally
injective. -/
theorem isLocallyInjective_presheafUliftMap {M N : PresheafOfModules.{z} R} (φ : M ⟶ N)
    (h : PresheafOfModules.IsLocallyInjective J φ) :
    PresheafOfModules.IsLocallyInjective J (presheafUliftMap.{u, v, w, z, t} φ) :=
  have := h
  Stacks.Sheaves.UniverseLift.isLocallyInjective_uliftFunctor.{u, v, z, t}
    ((PresheafOfModules.toPresheaf R).map φ)

/-- The universe lift of a locally surjective morphism of presheaves of modules is locally
surjective. -/
theorem isLocallySurjective_presheafUliftMap {M N : PresheafOfModules.{z} R} (φ : M ⟶ N)
    (h : PresheafOfModules.IsLocallySurjective J φ) :
    PresheafOfModules.IsLocallySurjective J (presheafUliftMap.{u, v, w, z, t} φ) :=
  have := h
  Stacks.Sheaves.UniverseLift.isLocallySurjective_uliftFunctor.{u, v, z, t}
    ((PresheafOfModules.toPresheaf R).map φ)

end Presheaf

section Sheaf

variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The universe lift of `SheafOfModules.uliftForPresentation` is the objectwise one. -/
theorem uliftForPresentation_val (M : SheafOfModules.{z} R) :
    (SheafOfModules.uliftForPresentation.{u, v, w, z, t} M).val =
      presheafUlift.{u, v, w, z, t} M.val := rfl

end Sheaf

section Tensor

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- Raising the universe of the sections of a presheaf of modules commutes with the objectwise
tensor product.  The comparison is linear over the ring of sections, not semilinear, because the
ring is not lifted. -/
noncomputable def tensorPresheafUliftIso
    (F : PresheafOfModules.{z} (O ⋙ forget₂ _ RingCat))
    (G : PresheafOfModules.{z₁} (O ⋙ forget₂ _ RingCat)) :
    PresheafOfModules.tensorObj (presheafUlift.{u, v, w, z, t} F)
        (presheafUlift.{u, v, w, z₁, t} G) ≅
      presheafUlift.{u, v, w, max z z₁, t} (PresheafOfModules.tensorObj F G) :=
  PresheafOfModules.isoMk
    (fun X ↦ ((TensorProduct.congr ULift.moduleEquiv ULift.moduleEquiv).trans
      ULift.moduleEquiv.symm).toModuleIso)
    (by
      intro X Y f
      refine ModuleCat.tensor_ext fun x y ↦ ?_
      rfl)

/-- Raising the universe of the sections commutes with the objectwise tensor product. -/
noncomputable def presheafUliftTensorIso
    (F : PresheafOfModules.{z} (O ⋙ forget₂ _ RingCat))
    (G : PresheafOfModules.{z₁} (O ⋙ forget₂ _ RingCat)) :
    presheafUlift.{u, v, w, max z z₁, t} (PresheafOfModules.tensorObj F G) ≅
      PresheafOfModules.tensorObj (presheafUlift.{u, v, w, z, t} F)
        (presheafUlift.{u, v, w, z₁, t} G) :=
  (tensorPresheafUliftIso.{u, v, w, z, z₁, t} F G).symm

end Tensor


section Sheafify

variable {J : GrothendieckTopology C}

/-- The sheafification unit of a presheaf of modules, as a morphism of presheaves of modules
over the same presheaf of rings, at a module universe independent of the ring universe. -/
noncomputable def sheafifyUnit [HasWeakSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    {R : Sheaf J RingCat.{w}} (P : PresheafOfModules.{z} R.obj) :
    P ⟶ ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P).val where
  app U := ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P).app U
  naturality {U V} f := by
    ext x
    exact PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P) f x

/-- The sheafification unit is locally injective. -/
theorem isLocallyInjective_sheafifyUnit [HasWeakSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    {R : Sheaf J RingCat.{w}} (P : PresheafOfModules.{z} R.obj) :
    PresheafOfModules.IsLocallyInjective J (sheafifyUnit (R := R) P) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P.presheaf))

/-- The sheafification unit is locally surjective. -/
theorem isLocallySurjective_sheafifyUnit [HasWeakSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    {R : Sheaf J RingCat.{w}} (P : PresheafOfModules.{z} R.obj) :
    PresheafOfModules.IsLocallySurjective J (sheafifyUnit (R := R) P) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P.presheaf))

/-- Two sheaves of modules receiving locally bijective maps from isomorphic presheaves of
modules are isomorphic.  The module universe is independent of the ring universe. -/
noncomputable def isoOfLocallyBijective [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
    {R : Sheaf J RingCat.{w}} {P Q : PresheafOfModules.{z} R.obj}
    {M N : SheafOfModules.{z} R} (f : P ⟶ M.val) (g : Q ⟶ N.val)
    (hfi : PresheafOfModules.IsLocallyInjective J f)
    (hfs : PresheafOfModules.IsLocallySurjective J f)
    (hgi : PresheafOfModules.IsLocallyInjective J g)
    (hgs : PresheafOfModules.IsLocallySurjective J g)
    (e : P ≅ Q) : M ≅ N := by
  have := hfi
  have := hfs
  have := hgi
  have := hgs
  let ef (T : SheafOfModules.{z} R) :=
    PresheafOfModules.homEquivOfIsLocallyBijective f (N := T.val) T.isSheaf
  let eg (T : SheafOfModules.{z} R) :=
    PresheafOfModules.homEquivOfIsLocallyBijective g (N := T.val) T.isSheaf
  let a := (ef N).symm (e.hom ≫ g)
  let b := (eg M).symm (e.inv ≫ f)
  have ha : f ≫ a = e.hom ≫ g := (ef N).apply_symm_apply _
  have hb : g ≫ b = e.inv ≫ f := (eg M).apply_symm_apply _
  refine ⟨⟨a⟩, ⟨b⟩, ?_, ?_⟩
  · apply SheafOfModules.hom_ext
    apply (ef M).injective
    change f ≫ (a ≫ b) = f ≫ 𝟙 _
    rw [← Category.assoc, ha, Category.assoc, hb]
    simp
  · apply SheafOfModules.hom_ext
    apply (eg N).injective
    change g ≫ (b ≫ a) = g ≫ 𝟙 _
    rw [← Category.assoc, hb, Category.assoc, ha]
    simp

end Sheafify

end Stacks.SheafOfModules.UliftTensor

end
