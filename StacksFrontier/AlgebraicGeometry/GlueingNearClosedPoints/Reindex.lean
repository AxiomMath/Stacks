module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Peeling
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.SquareGlueing

/-!
# Reindexing the glueing data of a family of commutative squares

The induction which proves [Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q) runs
over the index type of the family of closed points, peeling off one point at a time.  An
induction over an arbitrary finite index type proceeds by `Finite.induction_empty_option`, whose
first obligation is that the statement is stable under an equivalence of index types.

This file supplies that stability for the canonical functor of a family of commutative squares:
reindexing the family along an equivalence `I' ≃ I` reindexes its glueing data, by an equivalence
of categories which carries the canonical functor of the family, on the nose, to the canonical
functor of the reindexed family.

## Main definitions

* `AlgebraicGeometry.piReindex`: reindexing an indexed family of categories of schemes of finite
  presentation along an equivalence of index types.
* `AlgebraicGeometry.glueingDataOfReindex`: the reindexing of glueing data along an equivalence
  of index types.

## Main results

* `AlgebraicGeometry.restrictionFunctorOf_comp_glueingDataOfReindex`: reindexing carries the
  canonical functor of the family to the canonical functor of the reindexed family, by `rfl`.
* `AlgebraicGeometry.restrictionFunctorOf_isEquivalence_of_reindex`: if the canonical functor of
  the reindexed family is an equivalence, so is the canonical functor of the family.

## Implementation notes

Reindexing an indexed family along an equivalence is not a definitional operation: the component
of the reindexed family at `i'` sits over `e i'`, so recovering the component at `i` from the
reindexed family requires transporting along `e (e.symm i) = i`.  That transport is exactly what
`CategoryTheory.Pi.equivalenceOfEquiv` packages, so `AlgebraicGeometry.piReindex` is its inverse
rather than a hand-written functor, and no equality of index elements is ever rewritten here: the
full faithfulness and essential surjectivity of the reindexing of glueing data are deduced from
those of `AlgebraicGeometry.piReindex`, and the index-wise arguments only ever use that every
index is of the form `e i'`.

Reindexing the glueing data is *defined* as the evident assignment rather than obtained from
`AlgebraicGeometry.isoCommaMap`, so that the compatibility with the canonical functors holds by
`rfl`; the price is that its being an equivalence is proved by hand.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section Reindex

variable {T U : Scheme.{u}} {I I' : Type u} {L O : I → Scheme.{u}} (a : ∀ i, O i ⟶ U)
  (b : ∀ i, O i ⟶ L i) (e : I' ≃ I)

/-- Reindexing an indexed family of categories of schemes of finite presentation along an
equivalence of index types. -/
noncomputable def piReindex (M : I → Scheme.{u}) :
    ((i : I) → FinitePresentationOver (M i)) ⥤
      ((i' : I') → FinitePresentationOver (M (e i'))) :=
  (Pi.equivalenceOfEquiv (fun i ↦ FinitePresentationOver (M i)) e).inverse

/-- Reindexing a family of categories of schemes of finite presentation along an equivalence of
index types is an equivalence of categories. -/
instance (M : I → Scheme.{u}) : (piReindex e M).IsEquivalence :=
  (Pi.equivalenceOfEquiv (fun i ↦ FinitePresentationOver (M i)) e).isEquivalence_inverse

/-- The component over `i'` of the reindexing of a family of objects is its component over
`e i'`. -/
@[simp]
theorem piReindex_obj_apply (M : I → Scheme.{u})
    (X : (i : I) → FinitePresentationOver (M i)) (i' : I') :
    (piReindex e M).obj X i' = X (e i') :=
  rfl

/-- The component over `i'` of the reindexing of a family of morphisms is its component over
`e i'`. -/
@[simp]
theorem piReindex_map_apply (M : I → Scheme.{u})
    {X Y : (i : I) → FinitePresentationOver (M i)} (f : X ⟶ Y) (i' : I') :
    (piReindex e M).map f i' = f (e i') :=
  rfl

/-- The reindexing of the comma category underlying glueing data of a family of commutative
squares: the component over `i'` is the component over `e i'`. -/
noncomputable def glueingDataOfReindexComma :
    Comma (Functor.pi' fun i ↦ finitePresentationBaseChange (a i))
        (Functor.pi fun i ↦ finitePresentationBaseChange (b i)) ⥤
      Comma (Functor.pi' fun i' ↦ finitePresentationBaseChange (a (e i')))
        (Functor.pi fun i' ↦ finitePresentationBaseChange (b (e i'))) where
  obj Z := ⟨Z.left, (piReindex e L).obj Z.right, (piReindex e O).map Z.hom⟩
  map {_ _} f := ⟨f.left, (piReindex e L).map f.right, funext fun i' ↦ congrFun f.w (e i')⟩
  map_id _ := Comma.hom_ext _ _ rfl (by simp)
  map_comp _ _ := Comma.hom_ext _ _ rfl (by simp)

/-- The reindexing of glueing data of a family of commutative squares along an equivalence of
index types: the component over `i'` is the component over `e i'`. -/
noncomputable def glueingDataOfReindex :
    glueingDataOf a b ⥤ glueingDataOf (fun i' ↦ a (e i')) (fun i' ↦ b (e i')) :=
  (show ObjectProperty (Comma (Functor.pi' fun i' ↦ finitePresentationBaseChange (a (e i')))
      (Functor.pi fun i' ↦ finitePresentationBaseChange (b (e i')))) from
    fun X ↦ IsIso X.hom).lift
    ((show ObjectProperty (Comma (Functor.pi' fun i ↦ finitePresentationBaseChange (a i))
        (Functor.pi fun i ↦ finitePresentationBaseChange (b i))) from fun X ↦ IsIso X.hom).ι ⋙
      glueingDataOfReindexComma a b e)
    (fun Z ↦ by
      have : IsIso Z.obj.hom := Z.property
      change IsIso ((piReindex e O).map Z.obj.hom)
      infer_instance)

/-- The reindexing of glueing data along an equivalence of index types is faithful. -/
instance : (glueingDataOfReindex a b e).Faithful where
  map_injective {_ _} f g hfg := by
    refine ObjectProperty.hom_ext _ (Comma.hom_ext _ _ (congrArg (fun k ↦ k.hom.left) hfg) ?_)
    refine funext fun i ↦ ?_
    obtain ⟨i', rfl⟩ := e.surjective i
    exact congrFun (congrArg (fun k ↦ k.hom.right) hfg) i'

/-- The reindexing of glueing data along an equivalence of index types is full. -/
instance : (glueingDataOfReindex a b e).Full where
  map_surjective {Z Z'} φ := by
    refine ⟨ObjectProperty.homMk
      ⟨φ.hom.left, (piReindex e L).preimage φ.hom.right, ?_⟩, ?_⟩
    · refine funext fun i ↦ ?_
      obtain ⟨i', rfl⟩ := e.surjective i
      have hw : (piReindex e L).preimage φ.hom.right (e i') = φ.hom.right i' :=
        congrFun ((piReindex e L).map_preimage φ.hom.right) i'
      have hsq := congrFun φ.hom.w i'
      change (Functor.pi' fun i ↦ finitePresentationBaseChange (a i)).map φ.hom.left (e i') ≫
          Z'.obj.hom (e i') =
        Z.obj.hom (e i') ≫ (finitePresentationBaseChange (b (e i'))).map
          ((piReindex e L).preimage φ.hom.right (e i'))
      rw [hw]
      exact hsq
    · exact ObjectProperty.hom_ext _
        (Comma.hom_ext _ _ rfl ((piReindex e L).map_preimage φ.hom.right))

/-- The reindexing of glueing data along an equivalence of index types is essentially
surjective. -/
instance : (glueingDataOfReindex a b e).EssSurj where
  mem_essImage Z' := by
    have : IsIso Z'.obj.hom := Z'.property
    obtain ⟨Y, ⟨κ⟩⟩ : ∃ Y : (i : I) → FinitePresentationOver (L i),
        Nonempty ((piReindex e L).obj Y ≅ Z'.obj.right) :=
      ⟨_, ⟨(piReindex e L).objObjPreimageIso Z'.obj.right⟩⟩
    obtain ⟨g, hg⟩ : ∃ g : (Functor.pi' fun i ↦ finitePresentationBaseChange (a i)).obj
          Z'.obj.left ⟶ (Functor.pi fun i ↦ finitePresentationBaseChange (b i)).obj Y,
        (piReindex e O).map g = Z'.obj.hom ≫
          (Functor.pi fun i' ↦ finitePresentationBaseChange (b (e i'))).map κ.inv :=
      ⟨(piReindex e O).preimage _, (piReindex e O).map_preimage _⟩
    have : IsIso ((piReindex e O).map g) := by
      rw [hg]
      exact IsIso.comp_isIso' Z'.property (CategoryTheory.Functor.map_isIso _ κ.inv)
    refine ⟨⟨⟨Z'.obj.left, Y, g⟩, isIso_of_reflects_iso _ (piReindex e O)⟩, ⟨?_⟩⟩
    refine ObjectProperty.isoMk _ (Comma.isoMk (Iso.refl _) κ ?_)
    have step : (Z'.obj.hom ≫
          (Functor.pi fun i' ↦ finitePresentationBaseChange (b (e i'))).map κ.inv) ≫
        (Functor.pi fun i' ↦ finitePresentationBaseChange (b (e i'))).map κ.hom =
        Z'.obj.hom := by
      rw [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.comp_id]
    change (Functor.pi' fun i' ↦ finitePresentationBaseChange (a (e i'))).map (𝟙 Z'.obj.left) ≫
        Z'.obj.hom =
      (piReindex e O).map g ≫
        (Functor.pi fun i' ↦ finitePresentationBaseChange (b (e i'))).map κ.hom
    rw [hg, CategoryTheory.Functor.map_id, Category.id_comp]
    exact step.symm

/-- The reindexing of glueing data along an equivalence of index types is an equivalence of
categories. -/
instance : (glueingDataOfReindex a b e).IsEquivalence where

variable (c : U ⟶ T) (d : ∀ i, L i ⟶ T) (h : ∀ i, a i ≫ c = b i ≫ d i)

/-- Reindexing carries the canonical functor of a family of commutative squares to the canonical
functor of the reindexed family. -/
theorem restrictionFunctorOf_comp_glueingDataOfReindex :
    restrictionFunctorOf c d a b h ⋙ glueingDataOfReindex a b e =
      restrictionFunctorOf c (fun i' ↦ d (e i')) (fun i' ↦ a (e i'))
        (fun i' ↦ b (e i')) (fun i' ↦ h (e i')) :=
  rfl

/-- If the canonical functor of the reindexed family of commutative squares is an equivalence,
so is the canonical functor of the family itself. -/
theorem restrictionFunctorOf_isEquivalence_of_reindex
    (hequiv : (restrictionFunctorOf c (fun i' ↦ d (e i')) (fun i' ↦ a (e i'))
      (fun i' ↦ b (e i')) (fun i' ↦ h (e i'))).IsEquivalence) :
    (restrictionFunctorOf c d a b h).IsEquivalence := by
  have : (restrictionFunctorOf c d a b h ⋙ glueingDataOfReindex a b e).IsEquivalence := by
    rw [restrictionFunctorOf_comp_glueingDataOfReindex]
    exact hequiv
  exact Functor.isEquivalence_of_comp_right (restrictionFunctorOf c d a b h)
    (glueingDataOfReindex a b e)

end Reindex

end AlgebraicGeometry

end
