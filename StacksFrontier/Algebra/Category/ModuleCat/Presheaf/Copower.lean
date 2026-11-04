module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Copower

/-!
# The copower of a presheaf of modules by a presheaf of types

Let `R` be a presheaf of rings on a category `C`, `M` a presheaf of `R`-modules and `E` a presheaf
of types. The *copower* of `M` by `E` is the presheaf of `R`-modules whose sections over `X` are
the direct sum `⨁_{e ∈ E(X)} M(X)`, realized as the finitely supported functions `E(X) →₀ M(X)`
(`ModuleCat.copower`). Restriction along `f : X ⟶ Y` restricts each summand along `M.map f` and
moves the summand indexed by `e` to the one indexed by `E.map f e`.

## Main definitions

* `PresheafOfModules.copowerObj`: the copower of `M` by `E`.
* `PresheafOfModules.copowerMap`: the morphism of copowers induced by a morphism of presheaves of
  types, which relabels the summands.
* `PresheafOfModules.copowerFunctor`: the copower of `M` as a functor of the presheaf of labels.

## Main results

* `PresheafOfModules.copowerMk_comp_copowerObj_map`: restriction carries the summand at `e` to the
  summand at `E.map f e`.
* `PresheafOfModules.copowerMk_comp_copowerMap_app`: relabelling carries the summand at `e` to the
  summand at `g.app X e`.

## Implementation notes

The restriction maps are written with `ModuleCat.copowerDesc`, so that every equation between
them is checked one summand at a time by `ModuleCat.copower_hom_ext`; the sections of the copower
are never manipulated elementwise.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v v₁ u₁ u

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- **The copower of a presheaf of modules by a presheaf of types**: over `X` it is the direct sum
`⨁_{e ∈ E(X)} M(X)`, and restriction along `f` restricts each summand along `M.map f` and moves
the summand at `e` to the summand at `E.map f e`. -/
abbrev copowerObj (M : PresheafOfModules.{v} R) (E : Cᵒᵖ ⥤ Type v) : PresheafOfModules.{v} R where
  obj X := (ModuleCat.copower (M.obj X)).obj (E.obj X)
  map {X Y} f := ModuleCat.copowerDesc fun e =>
    M.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (ModuleCat.copowerMk (E.map f e))
  map_id X := by
    refine ModuleCat.copower_hom_ext fun e => ?_
    rw [ModuleCat.copowerMk_comp_desc, M.map_id, E.map_id]
    ext m
    rfl
  map_comp {X Y Z} f g := by
    refine ModuleCat.copower_hom_ext fun e => ?_
    rw [ModuleCat.copowerMk_comp_desc, reassoc_of% (ModuleCat.copowerMk_comp_desc
      (fun e => M.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map
        (ModuleCat.copowerMk (E.map f e))) e), M.map_comp, E.map_comp]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, ModuleCat.copowerMk_comp_desc, Functor.map_comp_assoc]
    congr 2

variable (M : PresheafOfModules.{v} R)

/-- The sections of the copower over `X` are the copower of the sections of `M` by `E(X)`. -/
@[simp] lemma copowerObj_obj (E : Cᵒᵖ ⥤ Type v) (X : Cᵒᵖ) :
    (copowerObj M E).obj X = (ModuleCat.copower (M.obj X)).obj (E.obj X) := rfl

/-- Restriction in the copower carries the summand at `e` to the summand at `E.map f e`. -/
@[reassoc]
lemma copowerMk_comp_copowerObj_map (E : Cᵒᵖ ⥤ Type v) {X Y : Cᵒᵖ} (f : X ⟶ Y) (e : E.obj X) :
    ModuleCat.copowerMk e ≫ (copowerObj M E).map f =
      M.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (ModuleCat.copowerMk (E.map f e)) :=
  ModuleCat.copowerMk_comp_desc _ e

/-- Restriction in the copower, on a section: it restricts the coefficients along `M.map f` and
relabels along `E.map f`. -/
lemma copowerObj_map_apply (E : Cᵒᵖ ⥤ Type v) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : E.obj X →₀ M.obj X) :
    (copowerObj M E).map f x =
      Finsupp.mapDomain (E.map f) (Finsupp.mapRange (M.map f) (map_zero _) x) := by
  show (Finsupp.lsum ℕ fun e => (M.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map
    (ModuleCat.copowerMk (E.map f e))).hom) x = _
  rw [Finsupp.lsum_apply, Finsupp.mapDomain,
    Finsupp.sum_mapRange_index (fun _ => Finsupp.single_zero _)]
  rfl

/-- The morphism of copowers induced by a morphism of presheaves of types: it relabels the
summands. -/
def copowerMap {E E' : Cᵒᵖ ⥤ Type v} (g : E ⟶ E') : copowerObj M E ⟶ copowerObj M E' where
  app X := (ModuleCat.copower (M.obj X)).map (g.app X)
  naturality {X Y} f := by
    refine ModuleCat.copower_hom_ext fun e => ?_
    rw [← Category.assoc, ← Category.assoc, copowerMk_comp_copowerObj_map, Category.assoc,
      ← Functor.map_comp, ModuleCat.copowerMk_comp_map, ModuleCat.copowerMk_comp_map,
      copowerMk_comp_copowerObj_map]
    rw [NatTrans.naturality_apply g f e]

/-- Relabelling carries the summand at `e` to the summand at `g.app X e`. -/
@[reassoc]
lemma copowerMk_comp_copowerMap_app {E E' : Cᵒᵖ ⥤ Type v} (g : E ⟶ E') (X : Cᵒᵖ) (e : E.obj X) :
    ModuleCat.copowerMk e ≫ (copowerMap M g).app X = ModuleCat.copowerMk (g.app X e) :=
  ModuleCat.copowerMk_comp_map _ e

/-- The copower of a presheaf of modules, as a functor of the presheaf of labels. -/
def copowerFunctor : (Cᵒᵖ ⥤ Type v) ⥤ PresheafOfModules.{v} R where
  obj E := copowerObj M E
  map g := copowerMap M g
  map_id E := by
    ext X : 1
    exact (ModuleCat.copower (M.obj X)).map_id (E.obj X)
  map_comp g h := by
    ext X : 1
    exact (ModuleCat.copower (M.obj X)).map_comp (g.app X) (h.app X)

/-- The morphism out of the copower which sums the summands. -/
def copowerSum (E : Cᵒᵖ ⥤ Type v) : copowerObj M E ⟶ M where
  app X := ModuleCat.copowerDesc fun _ => 𝟙 (M.obj X)
  naturality {X Y} f := by
    refine ModuleCat.copower_hom_ext fun e => ?_
    rw [← Category.assoc, ← Category.assoc, copowerMk_comp_copowerObj_map, Category.assoc,
      ← Functor.map_comp, ModuleCat.copowerMk_comp_desc, CategoryTheory.Functor.map_id,
      Category.comp_id]
    have h2 : ModuleCat.copowerMk e ≫ ModuleCat.copowerDesc (fun _ => 𝟙 (M.obj X)) ≫ M.map f =
        M.map f := by
      rw [← Category.assoc, ModuleCat.copowerMk_comp_desc, Category.id_comp]
    exact h2.symm

/-- Summing the summands includes each summand by the identity. -/
@[reassoc (attr := simp)]
lemma copowerMk_comp_copowerSum_app (E : Cᵒᵖ ⥤ Type v) (X : Cᵒᵖ) (e : E.obj X) :
    ModuleCat.copowerMk e ≫ (copowerSum M E).app X = 𝟙 _ :=
  ModuleCat.copowerMk_comp_desc _ e

/-- Relabelling does not change the sum of the summands. -/
@[reassoc (attr := simp)]
lemma copowerMap_comp_copowerSum {E E' : Cᵒᵖ ⥤ Type v} (g : E ⟶ E') :
    copowerMap M g ≫ copowerSum M E' = copowerSum M E := by
  ext X : 1
  refine ModuleCat.copower_hom_ext fun e => ?_
  show ModuleCat.copowerMk e ≫ (copowerMap M g).app X ≫ (copowerSum M E').app X =
    ModuleCat.copowerMk e ≫ (copowerSum M E).app X
  rw [copowerMk_comp_copowerMap_app_assoc, copowerMk_comp_copowerSum_app,
    copowerMk_comp_copowerSum_app]

end PresheafOfModules

end
