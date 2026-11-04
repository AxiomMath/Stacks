module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.RingTheory.Flat.Basic

/-!
# The free module and the free presheaf of modules at split universes

For a ring `R : Type w` and a type `X : Type t`, the free `R`-module `X →₀ R` lives in
`Type (max t w)`. We define the free module functor `Type t ⥤ ModuleCat.{max t w} R`, and, for a
presheaf of rings `R : Cᵒᵖ ⥤ RingCat.{w}`, the free presheaf of modules functor
`(Cᵒᵖ ⥤ Type (max t w)) ⥤ PresheafOfModules.{max t w} R`, generalising `ModuleCat.free` and
`PresheafOfModules.free`, in which the ring universe and the module universe agree.

## Main definitions

* `ModuleCat.toRestrictScalars`: the identity map from an `S`-module to its restriction of
  scalars along `R →+* S`.
* `ModuleCat.freeSplit`: the free module functor `Type t ⥤ ModuleCat.{max t w} R` for a ring
  `R : Type w`, with `ModuleCat.freeSplitMk` and `ModuleCat.freeSplitDesc`.
* `PresheafOfModules.freeSplitObj`: the free presheaf of modules on a presheaf of types
  `F : Cᵒᵖ ⥤ Type (max t w)` over `R : Cᵒᵖ ⥤ RingCat.{w}`, an object of
  `PresheafOfModules.{max t w} R`, with the morphism `PresheafOfModules.freeSplitObjDesc` it
  induces to a presheaf of modules.
* `PresheafOfModules.freeSplit`: the free presheaf of modules functor.

## Main results

* `ModuleCat.freeSplitHomEquiv`: morphisms from the free module on `X` to `M` are the maps
  `X → M`.
* `PresheafOfModules.freeSplitObj_hom_ext'`: two morphisms out of `freeSplitObj F` agreeing on
  the generators are equal.
* `PresheafOfModules.module_free_freeSplitObj_obj`: the free presheaf of modules is sectionwise
  free.
-/

@[expose] public section

universe t w v v₁ u₁

open CategoryTheory

namespace ModuleCat

/-- The identity map from an `S`-module `M` to its restriction of scalars along `ρ : R →+* S`,
which has the same underlying type. -/
def toRestrictScalars {R S : Type*} [Ring R] [Ring S] (ρ : R →+* S) {M : ModuleCat.{v} S}
    (m : M) : (restrictScalars ρ).obj M := m

/-- Restriction of scalars of a morphism `φ` commutes with `toRestrictScalars`. -/
@[simp]
lemma restrictScalars_map_toRestrictScalars {R S : Type*} [Ring R] [Ring S] (ρ : R →+* S)
    {M N : ModuleCat.{v} S} (φ : M ⟶ N) (m : M) :
    (restrictScalars ρ).map φ (toRestrictScalars ρ m) = toRestrictScalars ρ (φ m) :=
  rfl

variable (R : Type w) [Ring R]

/-- The free module functor `Type t ⥤ ModuleCat.{max t w} R` for a ring `R : Type w`, sending
a type `X` to the module `X →₀ R` of finitely supported functions. -/
noncomputable def freeSplit : Type t ⥤ ModuleCat.{max t w} R where
  obj X := ModuleCat.of R (X →₀ R)
  map {_ _} f := ofHom <| Finsupp.lmapDomain R R f
  map_id X :=
    ModuleCat.hom_ext <| Finsupp.lhom_ext' fun x ↦ LinearMap.ext_ring <| by
      simp [Finsupp.mapDomain_single]
  map_comp {X Y Z} f g :=
    ModuleCat.hom_ext <| Finsupp.lhom_ext' fun x ↦ LinearMap.ext_ring <| by
      simp [Finsupp.mapDomain_single]

variable {R}

/-- The generator of `(ModuleCat.freeSplit R).obj X` attached to `x : X`. -/
noncomputable def freeSplitMk {X : Type t} (x : X) : (freeSplit.{t, w} R).obj X :=
  Finsupp.single x 1

/-- Two morphisms out of `(ModuleCat.freeSplit R).obj X` agreeing on the generators are
equal. -/
@[ext 1200]
lemma freeSplit_hom_ext {X : Type t} {M : ModuleCat.{max t w} R}
    {f g : (freeSplit.{t, w} R).obj X ⟶ M}
    (h : ∀ x : X, f (freeSplitMk x) = g (freeSplitMk x)) : f = g :=
  ModuleCat.hom_ext (Finsupp.lhom_ext' fun x ↦ LinearMap.ext_ring (h x))

/-- The morphism of modules `(ModuleCat.freeSplit R).obj X ⟶ M` determined by a
map `X → M`. -/
noncomputable def freeSplitDesc {X : Type t} {M : ModuleCat.{max t w} R} (f : X → M) :
    (freeSplit.{t, w} R).obj X ⟶ M :=
  ofHom <| Finsupp.lift M R X f

/-- `ModuleCat.freeSplitDesc f` sends the generator attached to `x` to `f x`. -/
@[simp]
lemma freeSplitDesc_apply {X : Type t} {M : ModuleCat.{max t w} R} (f : X → M) (x : X) :
    freeSplitDesc f (freeSplitMk x) = f x := by
  show Finsupp.lift M R X f (Finsupp.single x 1) = f x
  rw [Finsupp.lift_apply, Finsupp.sum_single_index] <;> simp

/-- `(ModuleCat.freeSplit R).map f` sends the generator attached to `x` to the generator
attached to `f x`. -/
@[simp]
lemma freeSplit_map_apply {X Y : Type t} (f : X ⟶ Y) (x : X) :
    (freeSplit.{t, w} R).map f (freeSplitMk x) = freeSplitMk (f x) :=
  Finsupp.mapDomain_single

/-- Morphisms from the free module on `X : Type t` over a ring `R : Type w` to `M` are in
bijection with the maps `X → M`, by evaluation at the generators. -/
noncomputable def freeSplitHomEquiv {X : Type t} {M : ModuleCat.{max t w} R} :
    ((freeSplit.{t, w} R).obj X ⟶ M) ≃ (X → M) where
  toFun φ := fun x ↦ φ (freeSplitMk x)
  invFun ψ := freeSplitDesc ψ
  left_inv _ := freeSplit_hom_ext fun x ↦ by simp
  right_inv _ := funext fun x ↦ by simp

/-- The free module on a type is a free module. -/
instance module_free_freeSplit_obj (X : Type t) :
    Module.Free R ((freeSplit.{t, w} R).obj X) :=
  inferInstanceAs (Module.Free R (X →₀ R))

end ModuleCat

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{w})

variable {R} in
/-- Given a presheaf of types `F : Cᵒᵖ ⥤ Type (max t w)`, this is the presheaf of modules over
`R : Cᵒᵖ ⥤ RingCat.{w}` sending `X : Cᵒᵖ` to the free `R.obj X`-module on `F.obj X`. -/
noncomputable def freeSplitObj (F : Cᵒᵖ ⥤ Type max t w) : PresheafOfModules.{max t w} R where
  obj X := (ModuleCat.freeSplit.{max t w, w} (R.obj X)).obj (F.obj X)
  map {X Y} f := ModuleCat.freeSplitDesc
    (fun x ↦ ModuleCat.toRestrictScalars (R.map f).hom (ModuleCat.freeSplitMk (F.map f x)))
  map_id X := ModuleCat.freeSplit_hom_ext fun x ↦ by
    simp only [ModuleCat.freeSplitDesc_apply, Functor.map_id_apply,
      ModuleCat.restrictScalarsId', NatIso.ofComponents_inv_app,
      ModuleCat.restrictScalarsId'App_inv_apply]
    rfl
  map_comp {X Y Z} f g := ModuleCat.freeSplit_hom_ext fun x ↦ by
    simp only [ModuleCat.freeSplitDesc_apply, Functor.map_comp_apply, ModuleCat.comp_apply,
      ModuleCat.restrictScalars_map_toRestrictScalars, ModuleCat.restrictScalarsComp',
      NatIso.ofComponents_inv_app]
    rfl

variable (F G : Cᵒᵖ ⥤ Type max t w)

/-- The generator of `(freeSplitObj F).obj X` attached to a section `x : F.obj X`. -/
noncomputable def freeSplitObjMk {X : Cᵒᵖ} (x : F.obj X) : (freeSplitObj (R := R) F).obj X :=
  ModuleCat.freeSplitMk x

/-- Two morphisms out of `(freeSplitObj F).obj X` agreeing on the generators are equal. -/
lemma freeSplitObj_hom_ext {X : Cᵒᵖ} {M : ModuleCat.{max t w} (R.obj X)}
    {f g : (freeSplitObj (R := R) F).obj X ⟶ M}
    (h : ∀ x : F.obj X, f (freeSplitObjMk R F x) = g (freeSplitObjMk R F x)) : f = g :=
  ModuleCat.freeSplit_hom_ext h

/-- The restriction map of `freeSplitObj F` along `f` sends the generator attached to `x` to
the generator attached to `F.map f x`. -/
@[simp]
lemma freeSplitObj_map_freeSplitObjMk {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X) :
    (freeSplitObj (R := R) F).map f (freeSplitObjMk R F x) =
      ModuleCat.toRestrictScalars (R.map f).hom (freeSplitObjMk R F (F.map f x)) :=
  ModuleCat.freeSplitDesc_apply _ _

/-- Each module of sections of `freeSplitObj F` is free. -/
instance module_free_freeSplitObj_obj (X : Cᵒᵖ) :
    Module.Free (R.obj X) ((freeSplitObj (R := R) F).obj X) :=
  ModuleCat.module_free_freeSplit_obj (R := (R.obj X : Type w)) (F.obj X)

section Desc

variable {R F} {G' : PresheafOfModules.{max t w} R}

/-- The component at `X` of the morphism out of `freeSplitObj F` determined by a
family of maps on sections. -/
noncomputable def freeSplitObjDescApp (φ : ∀ X : Cᵒᵖ, F.obj X → G'.obj X) (X : Cᵒᵖ) :
    (freeSplitObj (R := R) F).obj X ⟶ G'.obj X :=
  ModuleCat.freeSplitDesc (φ X)

/-- `freeSplitObjDescApp φ X` sends the generator attached to `x` to `φ X x`. -/
@[simp]
lemma freeSplitObjDescApp_freeSplitObjMk (φ : ∀ X : Cᵒᵖ, F.obj X → G'.obj X) (X : Cᵒᵖ)
    (x : F.obj X) : freeSplitObjDescApp φ X (freeSplitObjMk R F x) = φ X x :=
  ModuleCat.freeSplitDesc_apply _ _

/-- The morphism of presheaves of modules `freeSplitObj F ⟶ G'` determined by a
family of maps on sections commuting with the restriction maps. -/
noncomputable def freeSplitObjDesc (φ : ∀ X : Cᵒᵖ, F.obj X → G'.obj X)
    (hφ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X), φ Y (F.map f x) = G'.map f (φ X x)) :
    freeSplitObj F ⟶ G' where
  app X := freeSplitObjDescApp φ X
  naturality {X Y} f := by
    refine freeSplitObj_hom_ext _ _ fun x ↦ ?_
    simp only [ModuleCat.comp_apply, freeSplitObj_map_freeSplitObjMk,
      ModuleCat.restrictScalars_map_toRestrictScalars, freeSplitObjDescApp_freeSplitObjMk]
    exact hφ f x

/-- `(freeSplitObjDesc φ hφ).app X` sends the generator attached to `x` to `φ X x`. -/
@[simp]
lemma freeSplitObjDesc_app_freeSplitObjMk (φ : ∀ X : Cᵒᵖ, F.obj X → G'.obj X)
    (hφ : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X), φ Y (F.map f x) = G'.map f (φ X x))
    (X : Cᵒᵖ) (x : F.obj X) :
    (freeSplitObjDesc φ hφ).app X (freeSplitObjMk R F x) = φ X x :=
  ModuleCat.freeSplitDesc_apply _ _

end Desc

variable {F G} in
/-- The morphism of free presheaves of modules induced by a morphism of
presheaves of types. -/
noncomputable def freeSplitMap (φ : F ⟶ G) :
    freeSplitObj (R := R) F ⟶ freeSplitObj (R := R) G :=
  freeSplitObjDesc (fun X x ↦ freeSplitObjMk R G (φ.app X x)) fun {X Y} f x ↦
    (congrArg (freeSplitObjMk R G (X := Y)) (NatTrans.naturality_apply φ f x)).trans
      (freeSplitObj_map_freeSplitObjMk R G f (φ.app X x)).symm

variable {F G} in
/-- `(freeSplitMap R φ).app X` sends the generator attached to `x` to the generator attached to
`φ.app X x`. -/
@[simp]
lemma freeSplitMap_app_freeSplitObjMk (φ : F ⟶ G) (X : Cᵒᵖ) (x : F.obj X) :
    (freeSplitMap R φ).app X (freeSplitObjMk R F x) = freeSplitObjMk R G (φ.app X x) :=
  ModuleCat.freeSplitDesc_apply _ _

/-- The free presheaf of modules functor
`(Cᵒᵖ ⥤ Type (max t w)) ⥤ PresheafOfModules.{max t w} R` for a presheaf of rings
`R : Cᵒᵖ ⥤ RingCat.{w}`. -/
noncomputable def freeSplit : (Cᵒᵖ ⥤ Type max t w) ⥤ PresheafOfModules.{max t w} R where
  obj := freeSplitObj
  map {F G} φ := freeSplitMap R φ
  map_id F := by
    refine PresheafOfModules.hom_ext fun X ↦ freeSplitObj_hom_ext R F fun x ↦ ?_
    simp
  map_comp {F G H} φ ψ :=
    PresheafOfModules.hom_ext fun X ↦ freeSplitObj_hom_ext R F fun x ↦ by simp

/-- The free presheaf of modules functor sends `F` to `freeSplitObj F`. -/
@[simp]
lemma freeSplit_obj : (freeSplit R).obj F = freeSplitObj F := rfl

variable {F G} in
/-- The free presheaf of modules functor sends `φ` to `freeSplitMap R φ`. -/
@[simp]
lemma freeSplit_map (φ : F ⟶ G) : (freeSplit R).map φ = freeSplitMap R φ := rfl

section UniversalProperty

variable {R F} {G' : PresheafOfModules.{max t w} R}

/-- Two morphisms out of the free presheaf of modules `freeSplitObj F` agreeing on the
generators are equal. -/
lemma freeSplitObj_hom_ext' {f g : freeSplitObj (R := R) F ⟶ G'}
    (h : ∀ (X : Cᵒᵖ) (x : F.obj X),
      f.app X (freeSplitObjMk R F x) = g.app X (freeSplitObjMk R F x)) : f = g :=
  PresheafOfModules.hom_ext (fun X ↦ freeSplitObj_hom_ext R F (h X))

end UniversalProperty

end PresheafOfModules
