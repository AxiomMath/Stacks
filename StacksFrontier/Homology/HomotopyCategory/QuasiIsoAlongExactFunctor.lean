module

public import Mathlib.Algebra.Homology.Localization

/-!
# Quasi-isomorphisms in the homotopy category along a functor preserving homology

An additive functor `F` which preserves homology acts on homotopy categories of complexes of a
fixed shape, and that action carries quasi-isomorphisms to quasi-isomorphisms. If `F` moreover
reflects isomorphisms — as an equivalence does — the converse holds, so the class of
quasi-isomorphisms of the source is the inverse image of the class of quasi-isomorphisms of the
target.

## Main results

* `CategoryTheory.Functor.quasiIso_mapHomotopyCategory_map`: the action on homotopy categories
  of an additive functor preserving homology carries `HomotopyCategory.quasiIso` into
  `HomotopyCategory.quasiIso`.
* `CategoryTheory.Functor.quasiIso_mapHomotopyCategory_map_iff` and
  `CategoryTheory.Functor.inverseImage_quasiIso_mapHomotopyCategory`: if the functor also
  reflects isomorphisms, `HomotopyCategory.quasiIso` of the source is exactly the inverse image
  of `HomotopyCategory.quasiIso` of the target.

## Implementation notes

The statements are reduced to the corresponding ones for complexes,
`HomologicalComplex.quasiIso_map_of_preservesHomology` and
`HomologicalComplex.quasiIso_map_iff_of_preservesHomology`, by replacing a morphism of the
homotopy category by the chosen representative `CategoryTheory.HomotopyCategory.quotient_map_out`
of its homotopy class, along which the action on homotopy categories is the action on complexes.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {V : Type u₁} {W : Type u₂} [Category.{v₁} V] [Category.{v₂} W]
  [Preadditive V] [Preadditive W] [CategoryWithHomology V] [CategoryWithHomology W]
  {ι : Type*} (c : ComplexShape ι) (F : V ⥤ W) [F.Additive] [F.PreservesHomology]

/-- A morphism of the homotopy category is a quasi-isomorphism exactly when the chosen
representative of its homotopy class is one. -/
private lemma mem_quasiIso_iff_out {X Y : HomotopyCategory V c} (f : X ⟶ Y) :
    HomotopyCategory.quasiIso V c f ↔ HomologicalComplex.quasiIso V c f.out := by
  conv_lhs => rw [← HomotopyCategory.quotient_map_out f]
  exact HomotopyCategory.quotient_map_mem_quasiIso_iff _

omit [CategoryWithHomology V] [CategoryWithHomology W] [F.PreservesHomology] in
/-- The action on homotopy categories of an additive functor is the action on complexes of the
chosen representative of a homotopy class. -/
private lemma mapHomotopyCategory_map_eq_quotient_map_out {X Y : HomotopyCategory V c}
    (f : X ⟶ Y) :
    (F.mapHomotopyCategory c).map f =
      (HomotopyCategory.quotient W c).map ((F.mapHomologicalComplex c).map f.out) := by
  conv_lhs => rw [← HomotopyCategory.quotient_map_out f]
  exact Functor.mapHomotopyCategory_map F f.out

/-- **An additive functor preserving homology carries quasi-isomorphisms of the homotopy
category to quasi-isomorphisms.** -/
lemma quasiIso_mapHomotopyCategory_map {X Y : HomotopyCategory V c} (f : X ⟶ Y)
    (hf : HomotopyCategory.quasiIso V c f) :
    HomotopyCategory.quasiIso W c ((F.mapHomotopyCategory c).map f) := by
  rw [mem_quasiIso_iff_out c f, HomologicalComplex.mem_quasiIso_iff] at hf
  rw [mapHomotopyCategory_map_eq_quotient_map_out c F f]
  refine (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr ?_
  rw [HomologicalComplex.mem_quasiIso_iff]
  have : QuasiIso f.out := hf
  infer_instance

/-- An additive functor which preserves homology and reflects isomorphisms detects
quasi-isomorphisms of the homotopy category. -/
lemma quasiIso_mapHomotopyCategory_map_iff [F.ReflectsIsomorphisms]
    {X Y : HomotopyCategory V c} (f : X ⟶ Y) :
    HomotopyCategory.quasiIso W c ((F.mapHomotopyCategory c).map f) ↔
      HomotopyCategory.quasiIso V c f := by
  have h2 : HomotopyCategory.quasiIso W c ((F.mapHomotopyCategory c).map f) ↔
      HomologicalComplex.quasiIso W c ((F.mapHomologicalComplex c).map f.out) := by
    rw [mapHomotopyCategory_map_eq_quotient_map_out c F f]
    exact HomotopyCategory.quotient_map_mem_quasiIso_iff _
  rw [mem_quasiIso_iff_out c f, h2, HomologicalComplex.mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff]
  exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ F

/-- **The quasi-isomorphisms of a homotopy category are the inverse image of those of the
target** along the action of an additive functor which preserves homology and reflects
isomorphisms. -/
lemma inverseImage_quasiIso_mapHomotopyCategory [F.ReflectsIsomorphisms] :
    (HomotopyCategory.quasiIso W c).inverseImage (F.mapHomotopyCategory c) =
      HomotopyCategory.quasiIso V c := by
  ext X Y f
  rw [MorphismProperty.inverseImage_iff]
  exact quasiIso_mapHomotopyCategory_map_iff c F f

end CategoryTheory.Functor

end
