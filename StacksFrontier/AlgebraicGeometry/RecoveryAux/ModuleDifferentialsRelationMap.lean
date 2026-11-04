module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksCore.Tactic.StacksAttribute

/-!
# The relation map defining the module of differentials

For a morphism `φ : O₁ ⟶ O₂` of sheaves of rings, we construct the morphism of
sheaves of `O₂`-modules whose cokernel is the module of relative differentials.

## Main definitions

* `moduleDifferentialsRelationMap` is the relation map with additive, Leibniz, and
  base-ring summands.
* `sheafifiedFreeGenerator` is the image of a free generator under the
  sheafification unit.

## Main results

The three generator equations identify the additive, Leibniz, and base-ring
components of the relation morphism.

## References

* [Stacks Project, Tag 04BM](https://stacks.math.columbia.edu/tag/04BM)
-/

@[expose] public section

open CategoryTheory Limits
open PresheafOfModules

namespace AlgebraicGeometry.SheafOfModules

universe v₁ u₁ u

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

attribute [local implicit_reducible] PresheafOfModules.freeObj

/-- The presheaf of underlying sets of a sheaf of rings. -/
noncomputable abbrev ringElements (R : Sheaf J RingCat.{u}) : Cᵒᵖ ⥤ Type u :=
  R.obj ⋙ forget _

/-- The pointwise product of the underlying presheaf of a sheaf of rings with itself. -/
noncomputable abbrev ringElementPairs (R : Sheaf J RingCat.{u}) : Cᵒᵖ ⥤ Type u where
  obj X := R.obj.obj X × R.obj.obj X
  map f := ↾ (fun p ↦ (R.obj.map f p.1, R.obj.map f p.2))

section FreeObj

variable {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- The value on a free generator of the map out of a free module described by a
plain function. -/
lemma freeDesc_ofHom_apply {S : Type u} [Ring S] {α : Type u} {M : ModuleCat.{u} S}
    (h : α → M) (a : α) : ModuleCat.freeDesc (↾ h) (ModuleCat.freeMk a) = h a :=
  ModuleCat.freeDesc_apply (↾ h) a

/-- The restriction maps of a free presheaf of modules, on free generators. -/
lemma freeObj_map_freeMk {F : Cᵒᵖ ⥤ Type u} {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X) :
    (freeObj (R := R) F).map f (ModuleCat.freeMk x) = ModuleCat.freeMk (F.map f x) := by
  rw [freeObj_map]
  exact freeDesc_ofHom_apply _ x

/-- A morphism `freeObj F ⟶ G` of presheaves of modules described by its values on the
free generators.

This is the pointwise form of `PresheafOfModules.freeObjDesc`: the values are taken in
`G.obj X` rather than in `(G.presheaf ⋙ forget _).obj X`, so that the module structure
they are written with is the syntactic one. -/
noncomputable def freeObjMk {F : Cᵒᵖ ⥤ Type u} {G : PresheafOfModules.{u} R}
    (g : ∀ X : Cᵒᵖ, F.obj X → G.obj X)
    (hg : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X), g Y (F.map f x) = G.map f (g X x)) :
    freeObj F ⟶ G where
  app X := ModuleCat.freeDesc (↾ g X)
  naturality {X Y} f := by
    refine ModuleCat.free_hom_ext (fun x ↦ ?_)
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, freeObj_map_freeMk,
      freeDesc_ofHom_apply]
    exact (freeDesc_ofHom_apply (g Y) (F.map f x)).trans (hg f x)

/-- The morphism `freeObjMk g hg` sends the free generator of `x : F.obj X` to `g X x`. -/
@[simp]
lemma freeObjMk_app_freeMk {F : Cᵒᵖ ⥤ Type u} {G : PresheafOfModules.{u} R}
    (g : ∀ X : Cᵒᵖ, F.obj X → G.obj X)
    (hg : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj X), g Y (F.map f x) = G.map f (g X x))
    (X : Cᵒᵖ) (x : F.obj X) :
    (freeObjMk g hg).app X (ModuleCat.freeMk x) = g X x :=
  freeDesc_ofHom_apply (g X) x

end FreeObj

/-- The additive summand of the relation map: `[(a, b)] ↦ [a + b] - [a] - [b]`. -/
noncomputable def relationAddSummand (O₂ : Sheaf J RingCat.{u}) :
    freeObj (R := O₂.obj) (ringElementPairs O₂) ⟶ freeObj (R := O₂.obj) (ringElements O₂) :=
  freeObjMk
    (fun _ p ↦ ModuleCat.freeMk (p.1 + p.2) - ModuleCat.freeMk p.1 - ModuleCat.freeMk p.2)
    (fun {X Y} f p ↦ by
      rw [map_sub, map_sub, freeObj_map_freeMk, freeObj_map_freeMk, freeObj_map_freeMk]
      exact congrArg (fun z ↦ ModuleCat.freeMk z - ModuleCat.freeMk (O₂.obj.map f p.1) -
        ModuleCat.freeMk (O₂.obj.map f p.2)) (map_add (O₂.obj.map f).hom p.1 p.2).symm)

/-- The Leibniz summand of the relation map: `[(f, g)] ↦ [f * g] - g • [f] - f • [g]`. -/
noncomputable def relationLeibnizSummand (O₂ : Sheaf J RingCat.{u}) :
    freeObj (R := O₂.obj) (ringElementPairs O₂) ⟶ freeObj (R := O₂.obj) (ringElements O₂) :=
  freeObjMk
    (fun _ p ↦ ModuleCat.freeMk (p.1 * p.2) - p.2 • ModuleCat.freeMk p.1 -
      p.1 • ModuleCat.freeMk p.2)
    (fun {X Y} f p ↦ by
      rw [map_sub, map_sub, PresheafOfModules.map_smul, PresheafOfModules.map_smul,
        freeObj_map_freeMk, freeObj_map_freeMk, freeObj_map_freeMk]
      exact congrArg (fun z ↦ ModuleCat.freeMk z -
        O₂.obj.map f p.2 • ModuleCat.freeMk (O₂.obj.map f p.1) -
        O₂.obj.map f p.1 • ModuleCat.freeMk (O₂.obj.map f p.2))
        (map_mul (O₂.obj.map f).hom p.1 p.2).symm)

/-- The base-ring summand of the relation map: `[h] ↦ [φ h]`. -/
noncomputable def relationBaseSummand {O₁ O₂ : Sheaf J RingCat.{u}} (φ : O₁ ⟶ O₂) :
    freeObj (R := O₂.obj) (ringElements O₁) ⟶ freeObj (R := O₂.obj) (ringElements O₂) :=
  freeObjMk (fun X h ↦ ModuleCat.freeMk (φ.hom.app X h))
    (fun {X Y} f h ↦ by
      rw [freeObj_map_freeMk]
      exact congrArg ModuleCat.freeMk
        (congrArg (fun k ↦ k.hom h) (φ.hom.naturality f)))

/-- The additive summand on a free generator. -/
@[simp]
lemma relationAddSummand_app_freeMk (O₂ : Sheaf J RingCat.{u}) (X : Cᵒᵖ)
    (a b : O₂.obj.obj X) :
    (relationAddSummand O₂).app X (ModuleCat.freeMk (a, b)) =
      ModuleCat.freeMk (a + b) - ModuleCat.freeMk a - ModuleCat.freeMk b :=
  freeObjMk_app_freeMk (F := ringElementPairs O₂) _ _ X (a, b)

/-- The Leibniz summand on a free generator. -/
@[simp]
lemma relationLeibnizSummand_app_freeMk (O₂ : Sheaf J RingCat.{u}) (X : Cᵒᵖ)
    (a b : O₂.obj.obj X) :
    (relationLeibnizSummand O₂).app X (ModuleCat.freeMk (a, b)) =
      ModuleCat.freeMk (a * b) - b • ModuleCat.freeMk a - a • ModuleCat.freeMk b :=
  freeObjMk_app_freeMk (F := ringElementPairs O₂) _ _ X (a, b)

/-- The base-ring summand on a free generator. -/
@[simp]
lemma relationBaseSummand_app_freeMk {O₁ O₂ : Sheaf J RingCat.{u}} (φ : O₁ ⟶ O₂) (X : Cᵒᵖ)
    (h : (ringElements O₁).obj X) :
    (relationBaseSummand φ).app X (ModuleCat.freeMk h) =
      ModuleCat.freeMk (φ.hom.app X h) :=
  freeObjMk_app_freeMk _ _ X h

/-- The map
`O₂[O₂ × O₂] ⊕ O₂[O₂ × O₂] ⊕ O₂[O₁] ⟶ O₂[O₂]`
whose three components send generators respectively to
`[a+b]-[a]-[b]`, `[fg]-g[f]-f[g]`, and `[φ(h)]`.

Here every free module presheaf and the displayed morphism have been sheafified. -/
@[stacks 04BM]
noncomputable def moduleDifferentialsRelationMap
    (O₁ O₂ : Sheaf J RingCat.{u}) (φ : O₁ ⟶ O₂)
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}] :
    (sheafification (𝟙 O₂.obj)).obj
      ((freeObj (R := O₂.obj) (ringElementPairs O₂) ⨿
        freeObj (R := O₂.obj) (ringElementPairs O₂)) ⨿
        freeObj (R := O₂.obj) (ringElements O₁)) ⟶
    (sheafification (𝟙 O₂.obj)).obj
      (freeObj (R := O₂.obj) (ringElements O₂)) :=
  (PresheafOfModules.sheafification (𝟙 O₂.obj)).map
    (coprod.desc (coprod.desc (relationAddSummand O₂) (relationLeibnizSummand O₂))
      (relationBaseSummand φ))

/-- The generator of the sheafified free module associated to a section of `F`. -/
noncomputable def sheafifiedFreeGenerator (O : Sheaf J RingCat.{u})
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (F : Cᵒᵖ ⥤ Type u) (X : Cᵒᵖ) (x : F.obj X) :
    (((SheafOfModules.forget O).obj
      ((sheafification (𝟙 O.obj)).obj (freeObj (R := O.obj) F))).obj X) :=
  ((sheafificationAdjunction (𝟙 O.obj)).unit.app (freeObj (R := O.obj) F)).app X
    (ModuleCat.freeMk x)

/-- Evaluating the adjunction transpose of a precomposed relation map. -/
private lemma sheafificationHomEquiv_relationMap_apply
    (O₁ O₂ : Sheaf J RingCat.{u}) (φ : O₁ ⟶ O₂)
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}] {P : PresheafOfModules O₂.obj}
    (k : P ⟶ (freeObj (R := O₂.obj) (ringElementPairs O₂) ⨿
        freeObj (R := O₂.obj) (ringElementPairs O₂)) ⨿ freeObj (R := O₂.obj) (ringElements O₁))
    (X : Cᵒᵖ) (m : P.obj X) :
    ((sheafificationHomEquiv (𝟙 O₂.obj)
      ((sheafification (𝟙 O₂.obj)).map k ≫ moduleDifferentialsRelationMap O₁ O₂ φ)).app X) m =
        ((sheafificationAdjunction (𝟙 O₂.obj)).unit.app
          (freeObj (R := O₂.obj) (ringElements O₂))).app X
          ((k ≫ coprod.desc (coprod.desc (relationAddSummand O₂) (relationLeibnizSummand O₂))
            (relationBaseSummand φ)).app X m) := by
  rw [moduleDifferentialsRelationMap, ← Functor.map_comp, ← sheafificationAdjunction_homEquiv_apply,
    ← Category.comp_id ((PresheafOfModules.sheafification (𝟙 O₂.obj)).map _),
    Adjunction.homEquiv_naturality_left]
  rfl

/-- The additive summand sends `[(a,b)]` to `[a+b]-[a]-[b]`. -/
@[stacks 04BM "additive summand"]
theorem moduleDifferentialsRelationMap_additive
    (O₁ O₂ : Sheaf J RingCat.{u}) (φ : O₁ ⟶ O₂)
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (X : Cᵒᵖ) (a b : O₂.obj.obj X) :
    ((sheafificationHomEquiv (𝟙 O₂.obj)
      ((sheafification (𝟙 O₂.obj)).map (coprod.inl ≫ coprod.inl) ≫
        moduleDifferentialsRelationMap O₁ O₂ φ)).app X) (ModuleCat.freeMk (a, b)) =
      sheafifiedFreeGenerator O₂ (ringElements O₂) X (a + b) -
        sheafifiedFreeGenerator O₂ (ringElements O₂) X a -
        sheafifiedFreeGenerator O₂ (ringElements O₂) X b := by
  rw [sheafificationHomEquiv_relationMap_apply]
  simp only [Category.assoc, coprod.inl_desc]
  rw [relationAddSummand_app_freeMk]
  simp only [sheafifiedFreeGenerator, map_sub]
  rfl

/-- The multiplicative summand sends `[(f,g)]` to `[fg]-g[f]-f[g]`. -/
@[stacks 04BM "Leibniz summand"]
theorem moduleDifferentialsRelationMap_leibniz
    (O₁ O₂ : Sheaf J RingCat.{u}) (φ : O₁ ⟶ O₂)
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (X : Cᵒᵖ) (f g : O₂.obj.obj X) :
    ((sheafificationHomEquiv (𝟙 O₂.obj)
      ((sheafification (𝟙 O₂.obj)).map (coprod.inr ≫ coprod.inl) ≫
        moduleDifferentialsRelationMap O₁ O₂ φ)).app X) (ModuleCat.freeMk (f, g)) =
      sheafifiedFreeGenerator O₂ (ringElements O₂) X (f * g) -
        g • sheafifiedFreeGenerator O₂ (ringElements O₂) X f -
        f • sheafifiedFreeGenerator O₂ (ringElements O₂) X g := by
  rw [sheafificationHomEquiv_relationMap_apply]
  simp only [Category.assoc, coprod.inl_desc, coprod.inr_desc]
  rw [relationLeibnizSummand_app_freeMk]
  simp only [sheafifiedFreeGenerator, map_sub, map_smul]
  rfl

/-- The base-ring summand sends `[h]` to `[φ(h)]`. -/
@[stacks 04BM "base-ring summand"]
theorem moduleDifferentialsRelationMap_base
    (O₁ O₂ : Sheaf J RingCat.{u}) (φ : O₁ ⟶ O₂)
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    (X : Cᵒᵖ) (h : O₁.obj.obj X) :
    ((sheafificationHomEquiv (𝟙 O₂.obj)
      ((sheafification (𝟙 O₂.obj)).map coprod.inr ≫
        moduleDifferentialsRelationMap O₁ O₂ φ)).app X) (ModuleCat.freeMk h) =
      sheafifiedFreeGenerator O₂ (ringElements O₂) X (φ.hom.app X h) := by
  rw [sheafificationHomEquiv_relationMap_apply]
  simp only [coprod.inr_desc, relationBaseSummand_app_freeMk, sheafifiedFreeGenerator]

end AlgebraicGeometry.SheafOfModules
