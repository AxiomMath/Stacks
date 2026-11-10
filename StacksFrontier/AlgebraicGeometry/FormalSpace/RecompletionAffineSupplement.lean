module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffine
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Localization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.MorphismOfAffines
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineOverAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSetTheoretic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionPointTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedQuasiCompactPoints
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautRepresentability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedColimitSupplement
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas

/-!
# Completions of directed colimits and of affine stages

The completion subfunctor of the vertex of a directed colimit of fppf sheaves is locally
isomorphic to the colimit of the completion subfunctors of the stages. For a stage represented
by an affine object of the big fppf site over `S`, the completion along a closed set of points
is an affine formal algebraic space, and along a constructible closed set it is countably
indexed.

These results are stated next to `StacksFrontier.AlgebraicGeometry.FormalSpace.RecompletionAffine`
but kept in a module of their own, so that that module stays as it is.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphisms of completion subfunctors induced by two equal morphisms of presheaves
agree. -/
theorem completionMapULift_congr {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {f g : X' ⟶ X}
    (hfg : f = g) (T' : Set (Space.pointsULift.{u + 1} B S hS X'))
    (T : Set (Space.pointsULift.{u + 1} B S hS X))
    (h : T' ⊆ Space.pointsMapULift.{u + 1} B S hS X' f ⁻¹' T) :
    Space.completionMapULift B S hS f T' T h =
      Space.completionMapULift B S hS g T' T (hfg ▸ h) := by
  subst hfg
  rfl

/-- The diagram of completion subfunctors of the stages of a cocone: the sections of a stage
`E i` whose point-set image lies over `W`. Sheafifying it stagewise gives
`AlgebraicGeometry.FormalSpace.completionDiagram`. -/
def completionSubfunctorDiagram {I : Type (u + 1)} [Preorder I] (E : I ⥤ FppfSheaf B S hS)
    (Y : FppfSheaf B S hS) (c : ∀ i, E.obj i ⟶ Y)
    (hc : ∀ ⦃i j : I⦄ (f : i ⟶ j), E.map f ≫ c j = c i)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) :
    I ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) where
  obj i := (Space.completionSubfunctorULift B S hS (E.obj i).obj
    (Space.pointsMapULift.{u + 1} B S hS (E.obj i).obj (c i).hom ⁻¹' W)).toFunctor
  map {_i _j} f := Space.completionMapULift B S hS (E.map f).hom _ _
    (preimage_pointsMapULift_cocone B S hS E Y c hc W f).subset
  map_id i :=
    (completionMapULift_congr B S hS
        (congrArg (fun φ : E.obj i ⟶ E.obj i => φ.hom) (E.map_id i)) _ _ _).trans
      (completionMapULift_id B S hS (E.obj i).obj _ _)
  map_comp {i j k} f g :=
    (completionMapULift_congr B S hS
        (congrArg (fun φ : E.obj i ⟶ E.obj k => φ.hom) (E.map_comp f g)) _ _ _).trans
      (completionMapULift_comp B S hS (E.map f).hom (E.map g).hom _
        (Space.pointsMapULift.{u + 1} B S hS (E.obj j).obj (c j).hom ⁻¹' W) _
        (preimage_pointsMapULift_cocone B S hS E Y c hc W f).subset
        (preimage_pointsMapULift_cocone B S hS E Y c hc W g).subset _)

/-- The value of `AlgebraicGeometry.FormalSpace.completionDiagram` at a stage `i` is the
completion of `E i` along the preimage of `W`. -/
@[simp]
theorem completionDiagram_obj {I : Type (u + 1)} [Preorder I] (E : I ⥤ FppfSheaf B S hS)
    (Y : FppfSheaf B S hS) (c : ∀ i, E.obj i ⟶ Y)
    (hc : ∀ ⦃i j : I⦄ (f : i ⟶ j), E.map f ≫ c j = c i)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) (i : I) :
    (completionDiagram B S hS E Y c hc W).obj i = Space.completionSheafULift B S hS (E.obj i)
      (Space.pointsMapULift.{u + 1} B S hS (E.obj i).obj (c i).hom ⁻¹' W) :=
  rfl

/-- The value of `AlgebraicGeometry.FormalSpace.completionDiagram` on a transition morphism is
the induced morphism of completions. -/
@[simp]
theorem completionDiagram_map {I : Type (u + 1)} [Preorder I] (E : I ⥤ FppfSheaf B S hS)
    (Y : FppfSheaf B S hS) (c : ∀ i, E.obj i ⟶ Y)
    (hc : ∀ ⦃i j : I⦄ (f : i ⟶ j), E.map f ≫ c j = c i)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) {i j : I} (f : i ⟶ j) :
    (completionDiagram B S hS E Y c hc W).map f =
      Space.completionSheafMapULift B S hS (E.map f) _ _
        (preimage_pointsMapULift_cocone B S hS E Y c hc W f).subset :=
  rfl

/-- The diagram of completion subfunctors of the stages of a directed colimit presentation of
`Y`. Sheafifying it stagewise is `AlgebraicGeometry.FormalSpace.completionColimitDiagram`. -/
abbrev completionColimitSubfunctorDiagram {I : Type (u + 1)} [Preorder I]
    (E : I ⥤ FppfSheaf B S hS) (Y : FppfSheaf B S hS) (e : Y ≅ colimit E)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) :
    I ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
  completionSubfunctorDiagram B S hS E Y (fun i ↦ colimit.ι E i ≫ e.inv)
    (fun {_ _} f ↦ by rw [← Category.assoc, colimit.w]) W

/-! ### Completion commutes with directed colimits -/

/-- The cocone on the diagram of completion subfunctors of the stages of a cocone whose vertex
is the completion subfunctor of the vertex: a section of a stage whose point-set image lies
over `W` is carried to a section of the vertex with point-set image in `W`. -/
def completionSubfunctorCocone {I : Type (u + 1)} [Preorder I] (E : I ⥤ FppfSheaf B S hS)
    (Y : FppfSheaf B S hS) (c : ∀ i, E.obj i ⟶ Y)
    (hc : ∀ ⦃i j : I⦄ (f : i ⟶ j), E.map f ≫ c j = c i)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) :
    Cocone (completionSubfunctorDiagram B S hS E Y c hc W) where
  pt := (Space.completionSubfunctorULift B S hS Y.obj W).toFunctor
  ι :=
    { app i := Space.completionMapULift B S hS (c i).hom _ W (Set.Subset.refl _)
      naturality := fun {i j} f ↦ by
        have hhom : (E.map f).hom ≫ (c j).hom = (c i).hom :=
          congrArg (fun φ : E.obj i ⟶ Y => φ.hom) (hc f)
        have h₃ : Space.pointsMapULift.{u + 1} B S hS (E.obj i).obj (c i).hom ⁻¹' W ⊆
            Space.pointsMapULift.{u + 1} B S hS (E.obj i).obj
              ((E.map f).hom ≫ (c j).hom) ⁻¹' W := by
          rw [hhom]
        simp only [Functor.const_obj_map]
        exact (completionMapULift_comp B S hS (E.map f).hom (c j).hom _
            (Space.pointsMapULift.{u + 1} B S hS (E.obj j).obj (c j).hom ⁻¹' W) W
            (preimage_pointsMapULift_cocone B S hS E Y c hc W f).subset
            (Set.Subset.refl _) h₃).symm.trans
          (completionMapULift_congr B S hS hhom _ W h₃) }

/-- The comparison morphism from the colimit of the diagram of completion subfunctors of the
stages of a cocone to the completion subfunctor of the vertex. -/
def completionSubfunctorColimitComparison {I : Type (u + 1)} [Preorder I]
    (E : I ⥤ FppfSheaf B S hS) (Y : FppfSheaf B S hS) (c : ∀ i, E.obj i ⟶ Y)
    (hc : ∀ ⦃i j : I⦄ (f : i ⟶ j), E.map f ≫ c j = c i)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) :
    colimit (completionSubfunctorDiagram B S hS E Y c hc W) ⟶
      (Space.completionSubfunctorULift B S hS Y.obj W).toFunctor :=
  colimit.desc _ (completionSubfunctorCocone B S hS E Y c hc W)

/-- The comparison morphism restricted to the colimit injection of a stage `i` is the morphism
of completion subfunctors induced by `c i`. -/
@[reassoc (attr := simp)]
theorem ι_comp_completionSubfunctorColimitComparison {I : Type (u + 1)} [Preorder I]
    (E : I ⥤ FppfSheaf B S hS) (Y : FppfSheaf B S hS) (c : ∀ i, E.obj i ⟶ Y)
    (hc : ∀ ⦃i j : I⦄ (f : i ⟶ j), E.map f ≫ c j = c i)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) (i : I) :
    colimit.ι (completionSubfunctorDiagram B S hS E Y c hc W) i ≫
        completionSubfunctorColimitComparison B S hS E Y c hc W =
      Space.completionMapULift B S hS (c i).hom _ W (Set.Subset.refl _) :=
  colimit.ι_desc _ i

/-- A section of a presheaf whose image under `f` has point-set image in `T` has point-set image
in the preimage of `T`. -/
private theorem hasImageInULift_preimage_of_hasImageInULift_map
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : X' ⟶ X)
    (T : Set (Space.pointsULift.{u + 1} B S hS X)) (V : BigFppfOver B S hS)
    (y : X'.obj (Opposite.op V))
    (hy : Space.HasImageInULift B S hS X T V (f.app (Opposite.op V) y)) :
    Space.HasImageInULift B S hS X' (Space.pointsMapULift.{u + 1} B S hS X' f ⁻¹' T) V y := by
  intro p
  rw [Set.mem_preimage, Space.pointsMapULift_class,
    Space.fieldValuedPointULift_map_restrict' B S hS f V p y]
  exact hy p

/-- A section of a stage of a cocone whose image in the vertex has point-set image in `W` has
itself point-set image in the set of points of the stage lying over `W`: a field-valued point
of the test object restricts the section at the stage to a field-valued point whose image in
the points of the vertex is the restriction of the image section, by
`AlgebraicGeometry.Space.fieldValuedPointULift_map_restrict`. -/
theorem hasImageInULift_of_hasImageInULift_image {I : Type (u + 1)} [Preorder I]
    (E : I ⥤ FppfSheaf B S hS) (Y : FppfSheaf B S hS) (c : ∀ i, E.obj i ⟶ Y)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) (i : I) (V : BigFppfOver B S hS)
    (y : (E.obj i).obj.obj (Opposite.op V))
    (hy : Space.HasImageInULift B S hS Y.obj W V ((c i).hom.app (Opposite.op V) y)) :
    Space.HasImageInULift B S hS (E.obj i).obj
      (Space.pointsMapULift.{u + 1} B S hS (E.obj i).obj (c i).hom ⁻¹' W) V y :=
  hasImageInULift_preimage_of_hasImageInULift_map B S hS (c i).hom W V y hy

/-- The comparison morphism carries the image of a section of a stage to the image of that
section under the structure morphism of the cocone. -/
theorem val_completionSubfunctorColimitComparison_ι {I : Type (u + 1)} [Preorder I]
    (E : I ⥤ FppfSheaf B S hS) (Y : FppfSheaf B S hS) (c : ∀ i, E.obj i ⟶ Y)
    (hc : ∀ ⦃i j : I⦄ (f : i ⟶ j), E.map f ≫ c j = c i)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) (i : I) (V : BigFppfOver B S hS)
    (z : ((completionSubfunctorDiagram B S hS E Y c hc W).obj i).obj (Opposite.op V)) :
    ((completionSubfunctorColimitComparison B S hS E Y c hc W).app (Opposite.op V)
        ((colimit.ι (completionSubfunctorDiagram B S hS E Y c hc W) i).app
          (Opposite.op V) z)).1 =
      (c i).hom.app (Opposite.op V) z.1 :=
  congrArg Subtype.val (ConcreteCategory.congr_hom (NatTrans.congr_app
    (ι_comp_completionSubfunctorColimitComparison B S hS E Y c hc W i) (Opposite.op V)) z)

/-- The structure morphism of a stage of a directed colimit presentation, read on sections, is
the component of the colimit cocone followed by the inverse of the presenting isomorphism. -/
theorem hom_app_apply_of_eq_colimit_ι {I : Type (u + 1)} [Preorder I]
    (E : I ⥤ FppfSheaf B S hS) (Y : FppfSheaf B S hS) (c : ∀ i, E.obj i ⟶ Y)
    (e : Y ≅ colimit E) (hce : ∀ i, c i = colimit.ι E i ≫ e.inv) (i : I)
    (V : BigFppfOver B S hS) (z : (E.obj i).obj.obj (Opposite.op V)) :
    (c i).hom.app (Opposite.op V) z =
      e.inv.hom.app (Opposite.op V) ((colimit.ι E i).hom.app (Opposite.op V) z) :=
  ConcreteCategory.congr_hom
    (congrArg (fun φ : E.obj i ⟶ Y => φ.hom.app (Opposite.op V)) (hce i) :
      (c i).hom.app (Opposite.op V) =
        (colimit.ι E i).hom.app (Opposite.op V) ≫ e.inv.hom.app (Opposite.op V)) z

/-- **Completion commutes with a directed colimit, locally and on subfunctors: surjectivity.**
Every section of the completion subfunctor of a directed colimit is, fppf-locally, the image
of a section of the completion subfunctor of a stage.

A section of the colimit sheaf comes fppf-locally from a stage, by
`Stacks.Sites.FilteredColimitSections.exists_local_section`, and the section of the stage it
comes from lies in the completion subfunctor of that stage, by
`AlgebraicGeometry.FormalSpace.hasImageInULift_of_hasImageInULift_image`, since its image in
the colimit is the restriction of the given section. -/
theorem isLocallySurjective_completionSubfunctorColimitComparison {I : Type (u + 1)}
    [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] (E : I ⥤ FppfSheaf B S hS)
    (Y : FppfSheaf B S hS) (c : ∀ i, E.obj i ⟶ Y)
    (hc : ∀ ⦃i j : I⦄ (f : i ⟶ j), E.map f ≫ c j = c i)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) (e : Y ≅ colimit E)
    (hce : ∀ i, c i = colimit.ι E i ≫ e.inv) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (completionSubfunctorColimitComparison B S hS E Y c hc W) := by
  constructor
  intro U s
  obtain ⟨Sv, hSv, hall⟩ := Stacks.Sites.FilteredColimitSections.exists_local_section' E U
    (e.hom.hom.app (Opposite.op U) s.1)
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hSv
  intro V g hg
  obtain ⟨k, y, hy⟩ := hall g hg
  have hunit : e.inv.hom.app (Opposite.op U) (e.hom.hom.app (Opposite.op U) s.1) = s.1 :=
    ConcreteCategory.congr_hom
      (congrArg (fun φ : Y ⟶ Y => φ.hom.app (Opposite.op U)) e.hom_inv_id :
        e.hom.hom.app (Opposite.op U) ≫ e.inv.hom.app (Opposite.op U) = 𝟙 _) s.1
  have hck : (c k).hom.app (Opposite.op V) y = Y.obj.map g.op s.1 := by
    rw [hom_app_apply_of_eq_colimit_ι B S hS E Y c e hce k V y, hy,
      NatTrans.naturality_apply e.inv.hom g.op, hunit]
  have hyimg : Space.HasImageInULift B S hS Y.obj W V ((c k).hom.app (Opposite.op V) y) := by
    rw [hck]
    exact (Space.completionSubfunctorULift B S hS Y.obj W).map g.op s.2
  exact ⟨(colimit.ι (completionSubfunctorDiagram B S hS E Y c hc W) k).app (Opposite.op V)
      ⟨y, hasImageInULift_of_hasImageInULift_image B S hS E Y c W k V y hyimg⟩,
    Subtype.ext ((val_completionSubfunctorColimitComparison_ι B S hS E Y c hc W k V _).trans hck)⟩

/-- **Completion commutes with a directed colimit, locally and on subfunctors: injectivity.**
Two sections of the colimit of the diagram of completion subfunctors of the stages with the
same image in the completion subfunctor of the colimit agree fppf-locally.

The index category being filtered, the two sections come from one stage; their underlying
sections of that stage have the same image in the colimit sheaf, so they agree fppf-locally
after a transition morphism by
`Stacks.Sites.FilteredColimitSections.exists_local_transition`, and that transition morphism
then identifies the two sections of the colimit of the completion subfunctors. -/
theorem isLocallyInjective_completionSubfunctorColimitComparison {I : Type (u + 1)}
    [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] (E : I ⥤ FppfSheaf B S hS)
    (Y : FppfSheaf B S hS) (c : ∀ i, E.obj i ⟶ Y)
    (hc : ∀ ⦃i j : I⦄ (f : i ⟶ j), E.map f ≫ c j = c i)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) (e : Y ≅ colimit E)
    (hce : ∀ i, c i = colimit.ι E i ≫ e.inv) :
    Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      (completionSubfunctorColimitComparison B S hS E Y c hc W) := by
  constructor
  intro Uop x y hxy
  obtain ⟨U⟩ := Uop
  obtain ⟨k, a, b, ha, hb⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves
      ((evaluation ((BigFppfOver B S hS)ᵒᵖ) (Type (u + 1))).obj (Opposite.op U))
      (colimit.isColimit (completionSubfunctorDiagram B S hS E Y c hc W))) x y
  have ha' : (colimit.ι (completionSubfunctorDiagram B S hS E Y c hc W) k).app
      (Opposite.op U) a = x := ha
  have hb' : (colimit.ι (completionSubfunctorDiagram B S hS E Y c hc W) k).app
      (Opposite.op U) b = y := hb
  have hstage : (c k).hom.app (Opposite.op U) a.1 = (c k).hom.app (Opposite.op U) b.1 := by
    rw [← val_completionSubfunctorColimitComparison_ι B S hS E Y c hc W k U a,
      ← val_completionSubfunctorColimitComparison_ι B S hS E Y c hc W k U b, ha', hb', hxy]
  have hunit : ∀ z, e.hom.hom.app (Opposite.op U) (e.inv.hom.app (Opposite.op U) z) = z :=
    fun z ↦ ConcreteCategory.congr_hom
      (congrArg (fun φ : colimit E ⟶ colimit E => φ.hom.app (Opposite.op U)) e.inv_hom_id :
        e.inv.hom.app (Opposite.op U) ≫ e.hom.hom.app (Opposite.op U) = 𝟙 _) z
  have hcolim : (colimit.ι E k).hom.app (Opposite.op U) a.1 =
      (colimit.ι E k).hom.app (Opposite.op U) b.1 := by
    rw [← hunit ((colimit.ι E k).hom.app (Opposite.op U) a.1),
      ← hunit ((colimit.ι E k).hom.app (Opposite.op U) b.1)]
    refine congrArg (e.hom.hom.app (Opposite.op U)) ?_
    rwa [← hom_app_apply_of_eq_colimit_ι B S hS E Y c e hce k U a.1,
      ← hom_app_apply_of_eq_colimit_ι B S hS E Y c e hce k U b.1]
  obtain ⟨Sv, hSv, hall⟩ := Stacks.Sites.FilteredColimitSections.exists_local_transition' E U k
    a.1 b.1 hcolim
  refine (BigFppfOver.topology B S hS).superset_covering ?_ hSv
  intro V g hg
  obtain ⟨l, w, hw⟩ := hall g hg
  have key : ∀ z : ((completionSubfunctorDiagram B S hS E Y c hc W).obj k).obj (Opposite.op U),
      (colimit (completionSubfunctorDiagram B S hS E Y c hc W)).map g.op
          ((colimit.ι (completionSubfunctorDiagram B S hS E Y c hc W) k).app
            (Opposite.op U) z) =
        (colimit.ι (completionSubfunctorDiagram B S hS E Y c hc W) l).app (Opposite.op V)
          (((completionSubfunctorDiagram B S hS E Y c hc W).map w).app (Opposite.op V)
            (((completionSubfunctorDiagram B S hS E Y c hc W).obj k).map g.op z)) := by
    intro z
    rw [← NatTrans.naturality_apply
      (colimit.ι (completionSubfunctorDiagram B S hS E Y c hc W) k) g.op z]
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app
      (colimit.w (completionSubfunctorDiagram B S hS E Y c hc W) w) (Opposite.op V)) _).symm
  change (colimit (completionSubfunctorDiagram B S hS E Y c hc W)).map g.op x =
    (colimit (completionSubfunctorDiagram B S hS E Y c hc W)).map g.op y
  rw [← ha', ← hb', key a, key b]
  exact congrArg _ (Subtype.ext hw)

/-- The fppf sheafification of `Type (u + 1)`-valued presheaves is a left adjoint, so it
preserves colimits. -/
local instance isLeftAdjoint_plusPlusSheaf :
    (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).IsLeftAdjoint :=
  ⟨_, ⟨CategoryTheory.plusPlusAdjunction (BigFppfOver.topology B S hS) (Type (u + 1))⟩⟩

/-- The comparison morphism from the colimit of the completions of the stages of a directed
colimit presentation to the completion of the presented sheaf, at the level of the completion
subfunctors. -/
abbrev completionColimitSubfunctorComparison {I : Type (u + 1)} [Preorder I]
    (E : I ⥤ FppfSheaf B S hS) (Y : FppfSheaf B S hS) (e : Y ≅ colimit E)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) :
    colimit (completionColimitSubfunctorDiagram B S hS E Y e W) ⟶
      (Space.completionSubfunctorULift B S hS Y.obj W).toFunctor :=
  completionSubfunctorColimitComparison B S hS E Y (fun i ↦ colimit.ι E i ≫ e.inv)
    (fun {_ _} f ↦ by rw [← Category.assoc, colimit.w]) W

/-- For a directed index category, the comparison morphism of completion subfunctors of a
directed colimit presentation is locally surjective. -/
instance isLocallySurjective_completionColimitSubfunctorComparison {I : Type (u + 1)}
    [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] (E : I ⥤ FppfSheaf B S hS)
    (Y : FppfSheaf B S hS) (e : Y ≅ colimit E)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (completionColimitSubfunctorComparison B S hS E Y e W) :=
  isLocallySurjective_completionSubfunctorColimitComparison B S hS E Y _ _ W e fun _ ↦ rfl

/-- For a directed index category, the comparison morphism of completion subfunctors of a
directed colimit presentation is locally injective. -/
instance isLocallyInjective_completionColimitSubfunctorComparison {I : Type (u + 1)}
    [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] (E : I ⥤ FppfSheaf B S hS)
    (Y : FppfSheaf B S hS) (e : Y ≅ colimit E)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) :
    Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS)
      (completionColimitSubfunctorComparison B S hS E Y e W) :=
  isLocallyInjective_completionSubfunctorColimitComparison B S hS E Y _ _ W e fun _ ↦ rfl

/-- **The comparison morphism of completion subfunctors is a local isomorphism**, being
locally injective and locally surjective, so it becomes an isomorphism after fppf
sheafification. -/
instance isIso_plusPlusSheaf_map_completionColimitSubfunctorComparison {I : Type (u + 1)}
    [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] (E : I ⥤ FppfSheaf B S hS)
    (Y : FppfSheaf B S hS) (e : Y ≅ colimit E)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) :
    IsIso ((CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
      (completionColimitSubfunctorComparison B S hS E Y e W)) := by
  rw [NatIso.isIso_map_iff (plusPlusSheafIsoPresheafToSheaf
    (BigFppfOver.topology B S hS) (Type (u + 1)))]
  exact ((BigFppfOver.topology B S hS).W_iff _).mp
    (GrothendieckTopology.W_of_isLocallyBijective (BigFppfOver.topology B S hS)
      (completionColimitSubfunctorComparison B S hS E Y e W))

/-- **Completion commutes with directed colimits of fppf sheaves.** For a directed colimit
presentation `Y ≅ colim E` of an fppf sheaf over `S` and a set `W` of points of `Y`, the
completion of `Y` along `W` is the colimit of the completions of the stages along the sets of
their points lying over `W`.

Both sides are fppf sheafifications of one presheaf colimit: a completion is by definition the
sheafification of the subfunctor of sections with the prescribed point-set image, and the
colimit of the completions of the stages is the sheafification of the colimit of those
subfunctors, the sheafification functor being a left adjoint and so preserving colimits. The
comparison morphism of presheaves between them is a local isomorphism, by
`AlgebraicGeometry.FormalSpace.isLocallySurjective_completionSubfunctorColimitComparison` and
`AlgebraicGeometry.FormalSpace.isLocallyInjective_completionSubfunctorColimitComparison`. -/
def completionSheafULiftIsoColimitCompletion {I : Type (u + 1)} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (E : I ⥤ FppfSheaf B S hS) (Y : FppfSheaf B S hS)
    (e : Y ≅ colimit E) (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) :
    Space.completionSheafULift B S hS Y W ≅
      colimit (completionColimitDiagram B S hS E Y e W) :=
  (asIso ((CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).map
        (completionColimitSubfunctorComparison B S hS E Y e W))).symm ≪≫
    preservesColimitIso
      (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
      (completionColimitSubfunctorDiagram B S hS E Y e W)

/-- The completion of a sheaf presented as a directed colimit is a directed colimit of affine
schemes along thickenings, as soon as the completions of the stages are affine formal
algebraic spaces, the transition morphisms of the presentation are relative thickenings, and
the completion is the colimit of the completions of the stages: the transition morphisms of
the diagram of completions are then relative thickenings as base changes, and Stacks 0GVM
applies. -/
theorem exists_affinePresentation_completionSheafULift_of_colimit' {I : Type (u + 1)}
    [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] (E : I ⥤ FppfSheaf B S hS)
    (Y : FppfSheaf B S hS) (e : Y ≅ colimit E)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj))
    (hstage : ∀ i, IsAffineFormalAlgebraicSpace B S hS
      ((completionColimitDiagram B S hS E Y e W).obj i))
    (hEthick : ∀ ⦃i j : I⦄ (f : i ⟶ j),
      MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) (E.map f))
    (ecompletion : Space.completionSheafULift B S hS Y W ≅
      colimit (completionColimitDiagram B S hS E Y e W)) :
    ∃ (K : Type (u + 1)) (pre : Preorder K), letI := pre
      Nonempty K ∧ IsDirected K (· ≤ ·) ∧
      (Countable I → (∀ i, IsCountablyIndexed B S hS
          ((completionColimitDiagram B S hS E Y e W).obj i)) → Countable K) ∧
      ∃ F : K ⥤ BigAffineFppf B S hS,
        (∀ ⦃p q : K⦄ (f : p ⟶ q), Stacks.Thickenings.IsThickening
          ((BigAffineFppf.toScheme B S hS).map (F.map f))) ∧
        Nonempty (Space.completionSheafULift B S hS Y W ≅ colimit (F ⋙
          BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) :=
  exists_affinePresentation_of_colimit' B S hS (completionColimitDiagram B S hS E Y e W)
    hstage
    (fun {_ _} f ↦ relative_completionDiagram_map B S hS E Y _ _ W _ f (hEthick f)) _
    ecompletion

/-! ### The point space of a stage of an affine presentation -/

/-- **A stage of an affine presentation is a homeomorphism on points.** The stage map
`X_i ⟶ X` is a relative thickening by **Stacks 0AI9**
(`AlgebraicGeometry.FormalSpace.isThickening_colimitι`), which for the universe-lifted Yoneda
embedding of presheaves is `AlgebraicGeometry.Space.IsRepresentableThickeningULift`
(`AlgebraicGeometry.FormalSpace.relative_sheafifiedYoneda_iff_uliftYoneda`), and a representable
thickening is a homeomorphism on points
(`AlgebraicGeometry.FormalSpace.isHomeomorph_pointsMapULift_of_isRepresentableThickeningULift`).

So `|X_i| = |X|` for every stage, and a closed subset of `|X|` with quasi-compact complement
pulls back to one of `|X_i|`, which is what identifies the stagewise completions with
completions along *finitely generated* ideals.

Note that this does **not** go through the factorization hypothesis `hfac` of
`isRepresentableThickeningULift_colimitι` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitStageThickening`, which nothing discharges: a
non-quasi-compact point of a filtered colimit need not factor through a single stage. Stacks
0AI9 avoids that hypothesis for an *affine* presentation, by the diagonal argument instead. -/
theorem isHomeomorph_pointsMapULift_colimitι {I : Type (u + 1)} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : I ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j), Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    (X : FppfSheaf B S hS)
    (e : colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ X) (i : I) :
    @IsHomeomorph _ _
      (Space.pointTopologyULift.{u + 1} B S hS
        ((D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj i).obj)
      (Space.pointTopologyULift.{u + 1} B S hS X.obj)
      (Space.pointsMapULift.{u + 1} B S hS
        ((D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj i).obj
        (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.hom).hom) :=
  isHomeomorph_pointsMapULift_of_isRepresentableThickeningULift
    ((relative_sheafifiedYoneda_iff_uliftYoneda' B S hS _ _).mp
      (isThickening_colimitι B S hS D hD X e i))

/-! ### Stacks 0AIY at a represented fppf sheaf of large sets

Stacks 0AIY is proved in this library for `AlgebraicGeometry.Space.completionSheaf`, the
completion formed inside presheaves of `Type u`, of a presheaf represented by an affine object
of the site. The completions of formal algebraic spaces are
`AlgebraicGeometry.Space.completionSheafULift`, formed inside fppf sheaves of `Type (u + 1)`.
This section identifies the two at a represented sheaf and so proves 0AIY in the form the
completions of formal algebraic spaces need it.
-/

/-- Pulling a set of points of the target of an isomorphism of fppf sheaves back along the
isomorphism and then along its inverse returns that set. -/
theorem preimage_pointsMapULift_inv_preimage_hom {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (T : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) :
    Space.pointsMapULift.{u + 1} B S hS Y.obj e.inv.hom ⁻¹'
        (Space.pointsMapULift.{u + 1} B S hS X.obj e.hom.hom ⁻¹' T) = T := by
  rw [← Set.preimage_comp, ← Space.pointsMapULift_comp,
    show e.inv.hom ≫ e.hom.hom = 𝟙 Y.obj from
      congrArg (fun φ : Y ⟶ Y => φ.hom) e.inv_hom_id,
    Space.pointsMapULift_id, Set.preimage_id]

/-- Pulling a set of points of the source of an isomorphism of fppf sheaves back along the
composite of the isomorphism with its inverse returns that set. -/
theorem preimage_pointsMapULift_hom_comp_inv {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (W : Set (Space.pointsULift.{u + 1} B S hS X.obj)) :
    Space.pointsMapULift.{u + 1} B S hS X.obj (e.hom ≫ e.inv).hom ⁻¹' W = W := by
  rw [show (e.hom ≫ e.inv).hom = 𝟙 X.obj from
      congrArg (fun φ : X ⟶ X => φ.hom) e.hom_inv_id,
    Space.pointsMapULift_id, Set.preimage_id]

/-- **A completion is carried along an isomorphism of the ambient fppf sheaves.** For an
isomorphism `e : X ≅ Y` and a set `T` of points of `Y`, the completion of `X` along the
preimage of `T` is isomorphic to the completion of `Y` along `T`: the morphisms of completions
induced by `e` and by its inverse are mutually inverse, by the identity and composition laws
for morphisms of completions. -/
def completionSheafULiftIsoOfIso {X Y : FppfSheaf B S hS} (e : X ≅ Y)
    (T : Set (Space.pointsULift.{u + 1} B S hS Y.obj)) :
    Space.completionSheafULift B S hS X
        (Space.pointsMapULift.{u + 1} B S hS X.obj e.hom.hom ⁻¹' T) ≅
      Space.completionSheafULift B S hS Y T where
  hom := Space.completionSheafMapULift B S hS e.hom _ T (Set.Subset.refl _)
  inv := Space.completionSheafMapULift B S hS e.inv T _
    (preimage_pointsMapULift_inv_preimage_hom B S hS e T).ge
  hom_inv_id := by
    rw [← completionSheafMapULift_comp B S hS e.hom e.inv _ T _ (Set.Subset.refl _)
      (preimage_pointsMapULift_inv_preimage_hom B S hS e T).ge
      (preimage_pointsMapULift_hom_comp_inv B S hS e _).ge,
      completionSheafMapULift_congr B S hS e.hom_inv_id _ _
        (preimage_pointsMapULift_hom_comp_inv B S hS e _).ge]
    exact completionSheafMapULift_id B S hS X _ _
  inv_hom_id := by
    rw [← completionSheafMapULift_comp B S hS e.inv e.hom T _ T
      (preimage_pointsMapULift_inv_preimage_hom B S hS e T).ge (Set.Subset.refl _)
      (preimage_pointsMapULift_hom_comp_inv B S hS e.symm _).ge,
      completionSheafMapULift_congr B S hS e.inv_hom_id _ _
        (preimage_pointsMapULift_hom_comp_inv B S hS e.symm _).ge]
    exact completionSheafMapULift_id B S hS Y _ _

/-- **The completion formed inside presheaves of `Type u` is the completion of the represented
fppf sheaf of `Type (u + 1)`.** For an object `U` of the big fppf site of `S` and a set `T` of
points of the presheaf `h_U` represented by `U`, the completion
`AlgebraicGeometry.Space.completionSheaf` of `h_U` along `T`, formed inside presheaves of
`Type u`, is the completion `AlgebraicGeometry.Space.completionSheafULift` of the fppf sheaf
`CategoryTheory.GrothendieckTopology.uliftYoneda` represented by `U` in `Type (u + 1)`, along
the set of points corresponding to `T` under
`AlgebraicGeometry.Space.pointsULiftEquiv`. The site being subcanonical, that sheaf is the
sheafified representable `h_U^#` of `CategoryTheory.Sheaf.sheafifiedYoneda`, by
`CategoryTheory.Sheaf.sheafifiedYonedaIsoUliftYoneda'`.

The two completions are literally the same sheaf: both are the fppf sheafification of the one
subfunctor of sections with point-set image in `T`, which is
`AlgebraicGeometry.FormalSpace.completionSubfunctor_eq_completionSubfunctorULift`. -/
theorem completionSheaf_eq_completionSheafULift_uliftYoneda (U : BigFppfOver B S hS)
    (T : Set (Space.points B S hS (yoneda.obj U))) :
    Space.completionSheaf B S hS (yoneda.obj U) T =
      Space.completionSheafULift B S hS
        ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U)
        ((Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U)).symm ⁻¹' T) :=
  congrArg (fun P : Subfunctor (yoneda.obj U ⋙ uliftFunctor.{u + 1}) =>
      (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))).obj
        P.toFunctor)
    (completionSubfunctor_eq_completionSubfunctorULift B S hS (yoneda.obj U) T)

/-- A closed set of points of the fppf sheaf represented by an object `U₀` of the site, in the
form of `uliftFunctor` applied to `h_U₀`, is carried to a closed set of points of `h_U₀` whose
completion is the completion of the sheaf; its complement stays quasi-compact if that of the
given set is. -/
private theorem exists_isClosed_completionSheaf_eq_completionSheafULift (U₀ : BigFppfOver B S hS)
    (Y : FppfSheaf B S hS)
    (hY : Y = ⟨yoneda.obj U₀ ⋙ uliftFunctor.{u + 1},
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U₀).isSheaf⟩)
    (W : Set (Space.pointsULift.{u + 1} B S hS Y.obj))
    (hW : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Y.obj) W) :
    ∃ T : Set (Space.points B S hS (yoneda.obj U₀)),
      @IsClosed _ (Space.pointTopology B S hS (yoneda.obj U₀)) T ∧
      (@IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS Y.obj) Wᶜ →
        @IsCompact _ (Space.pointTopology B S hS (yoneda.obj U₀)) Tᶜ) ∧
      Space.completionSheaf B S hS (yoneda.obj U₀) T = Space.completionSheafULift B S hS Y W := by
  subst hY
  let _ := Space.pointTopologyULift.{u + 1} B S hS (yoneda.obj U₀ ⋙ uliftFunctor.{u + 1})
  let _ := Space.pointTopology B S hS (yoneda.obj U₀)
  let H := Space.pointsHomeomorphPointsULift.{u + 1} B S hS (yoneda.obj U₀)
  refine ⟨Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U₀) ⁻¹' W,
    hW.preimage H.continuous, fun hWqc ↦ ?_, ?_⟩
  · rw [← Set.preimage_compl]
    exact H.isCompact_preimage.mpr hWqc
  · have := completionSheaf_eq_completionSheafULift_uliftYoneda B S hS U₀
      (Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U₀) ⁻¹' W)
    have hWeq : (Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U₀)).symm ⁻¹'
        (Space.pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U₀) ⁻¹' W) = W :=
      Set.ext fun x ↦ by simp
    exact this.trans (congrArg (Space.completionSheafULift B S hS _) hWeq)

/-- For an affine object `U` of the site, a closed set of points of the represented sheaf `h_U^#`
is carried to a closed set of points of the presheaf represented by the affine object
`affineOver` attached to `U`, whose completion is isomorphic to the completion of `h_U^#`; its
complement stays quasi-compact if that of the given set is. -/
private theorem exists_isClosed_nonempty_iso_completionSheaf
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (W : Set (Space.pointsULift.{u + 1} B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U).obj))
    (hW : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U).obj) W) :
    ∃ T : Set (Space.points B S hS (yoneda.obj (affineOver B S hS
        (contains_spec_globalSections B S hS U) (globalSectionsStructureMap B S hS U)))),
      @IsClosed _ (Space.pointTopology B S hS (yoneda.obj (affineOver B S hS
        (contains_spec_globalSections B S hS U) (globalSectionsStructureMap B S hS U)))) T ∧
      (@IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U).obj) Wᶜ →
        @IsCompact _ (Space.pointTopology B S hS (yoneda.obj (affineOver B S hS
          (contains_spec_globalSections B S hS U) (globalSectionsStructureMap B S hS U)))) Tᶜ) ∧
      Nonempty (Space.completionSheafULift B S hS
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U) W ≅
        Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS
          (contains_spec_globalSections B S hS U) (globalSectionsStructureMap B S hS U))) T) := by
  let J := BigFppfOver.topology B S hS
  let U₀ : BigFppfOver B S hS := affineOver B S hS (contains_spec_globalSections B S hS U)
    (globalSectionsStructureMap B S hS U)
  let Yg : FppfSheaf B S hS := ⟨yoneda.obj U₀ ⋙ uliftFunctor.{u + 1},
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U₀).isSheaf⟩
  let e : (Sheaf.sheafifiedYoneda J).obj U ≅ Yg :=
    ((Sheaf.sheafifiedYoneda J).mapIso (affineOverGlobalSectionsIso B S hS U)).symm ≪≫
      (Sheaf.sheafifiedYonedaIsoUliftYoneda' J).app U₀
  let _ := Space.pointTopologyULift.{u + 1} B S hS ((Sheaf.sheafifiedYoneda J).obj U).obj
  let _ := Space.pointTopologyULift.{u + 1} B S hS Yg.obj
  -- the point map of the isomorphism is a homeomorphism
  let eP : ((Sheaf.sheafifiedYoneda J).obj U).obj ≅ Yg.obj :=
    { hom := e.hom.hom, inv := e.inv.hom,
      hom_inv_id := congrArg (fun φ : (Sheaf.sheafifiedYoneda J).obj U ⟶
        (Sheaf.sheafifiedYoneda J).obj U => φ.hom) e.hom_inv_id,
      inv_hom_id := congrArg (fun φ : Yg ⟶ Yg => φ.hom) e.inv_hom_id }
  obtain ⟨T, hT, hTqc, hbridge⟩ := exists_isClosed_completionSheaf_eq_completionSheafULift B S hS
    U₀ Yg rfl (Space.pointsMapULift.{u + 1} B S hS Yg.obj e.inv.hom ⁻¹' W)
    (hW.preimage (Space.continuous_pointsMapULift.{u + 1} B S hS e.inv.hom))
  refine ⟨T, hT, fun hWqc ↦ hTqc ?_,
    ⟨(completionSheafULiftIsoOfIso B S hS e.symm W).symm ≪≫ eqToIso hbridge.symm⟩⟩
  rw [← Set.preimage_compl]
  exact (Space.pointsULiftHomeomorphOfIso.{u + 1} B S hS eP).symm.isCompact_preimage.mpr hWqc

/-- **Stacks 0AIY for the completion of a represented fppf sheaf of `Type (u + 1)`.** Let `U`
be an affine object of the big fppf site of `S` and let `W` be a closed set of points of the
fppf sheaf `h_U^#` of `Type (u + 1)` it represents. Then the completion of `h_U^#` along `W`
is a McQuillan affine formal algebraic space.

This is `AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionSheaf_of_isClosed`
(Stacks 0AIY), which is stated for `AlgebraicGeometry.Space.completionSheaf`, the completion
formed inside presheaves of `Type u`, carried across
`AlgebraicGeometry.FormalSpace.completionSheaf_eq_completionSheafULift_uliftYoneda`, the
identification of that completion with `AlgebraicGeometry.Space.completionSheafULift` of the
represented fppf sheaf. Three further steps bring the two statements into the same shape: the
sheafified representable is isomorphic to the universe lift of the represented presheaf, the
site being subcanonical, and the completion is carried along that isomorphism by
`AlgebraicGeometry.FormalSpace.completionSheafULiftIsoOfIso`; the closed set of points
transports along the homeomorphism
`AlgebraicGeometry.Space.pointsHomeomorphPointsULift` of the two point spaces; and a closed
set of points of a represented presheaf is the set of points supported in a closed subset of
the representing scheme, by
`AlgebraicGeometry.FormalSpace.exists_isClosed_supportedPoints_eq`, which is the shape
Stacks 0AIY takes its closed subset in. The affine object of the site is written as the
spectrum of its ring of global sections by
`AlgebraicGeometry.FormalSpace.affineOverGlobalSectionsIso`, which is the shape Stacks 0AIY
takes its affine scheme in. -/
theorem hasSomeSurjectivePresentation_completionSheafULift_represented
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (W : Set (Space.pointsULift.{u + 1} B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U).obj))
    (hW : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U).obj) W) :
    HasSomeSurjectivePresentation B S hS
      (Space.completionSheafULift B S hS
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U) W) := by
  let hA := contains_spec_globalSections B S hS U
  let fS := globalSectionsStructureMap B S hS U
  let U₀ : BigFppfOver B S hS := affineOver B S hS hA fS
  obtain ⟨T, hT, -, ⟨i⟩⟩ := exists_isClosed_nonempty_iso_completionSheaf B S hS U W hW
  obtain ⟨Ti, hTi, hpts⟩ :=
    exists_isClosed_supportedPoints_eq B S hS U₀ (𝟙 (yoneda.obj U₀)) T hT
  rw [Space.pointsMap_id, Set.preimage_id] at hpts
  refine hasSomeSurjectivePresentation_of_iso B S hS i.symm ?_
  rw [hpts]
  exact hasSomeSurjectivePresentation_completionSheaf_of_isClosed B S hS hA fS Ti hTi

/-- **Stacks 0AIY at the affine stages.** The completion of the fppf sheaf represented by an
object of the big affine fppf site over `S`, along a closed set of its points, is a McQuillan
affine formal algebraic space. This is
`AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionSheafULift_represented`
at the object of the big fppf site underlying an object of the big affine one. -/
theorem hasSomeSurjectivePresentation_completionSheafULift_affineStageSheaf
    (V : BigAffineFppf B S hS)
    (V' : Set (Space.pointsULift.{u + 1} B S hS (affineStageSheaf B S hS V).obj))
    (hV' : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS
      (affineStageSheaf B S hS V).obj) V') :
    HasSomeSurjectivePresentation B S hS
      (Space.completionSheafULift B S hS (affineStageSheaf B S hS V) V') :=
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj V)) := V.property
  hasSomeSurjectivePresentation_completionSheafULift_represented B S hS
    ((BigAffineFppf.inclusion B S hS).obj V) V' hV'

/-- **Stacks 0AIY at the affine stages**, in the form the completions of formal algebraic
spaces consume it: the completion of the fppf sheaf represented by an object of the big affine
fppf site over `S`, along a closed set of its points, is an affine formal algebraic space. This
is the first clause of `hasSomeSurjectivePresentation_completionSheafULift_affineStageSheaf`. -/
theorem isAffineFormalAlgebraicSpace_completionSheafULift_affineStageSheaf
    (V : BigAffineFppf B S hS)
    (V' : Set (Space.pointsULift.{u + 1} B S hS (affineStageSheaf B S hS V).obj))
    (hV' : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS
      (affineStageSheaf B S hS V).obj) V') :
    IsAffineFormalAlgebraicSpace B S hS
      (Space.completionSheafULift B S hS (affineStageSheaf B S hS V) V') :=
  (hasSomeSurjectivePresentation_completionSheafULift_affineStageSheaf B S hS V V' hV').1

/-- **The completion of a represented affine fppf sheaf along a constructible closed set is a
completion along a finitely generated ideal.** For an affine object `U` of the site and a closed
set `W` of points of `h_U^#` whose complement is quasi-compact, the completion is isomorphic to
`AlgebraicGeometry.FormalSpace.completionAlongIdeal` of `Spec Γ(U)` along a finitely generated
ideal.

The plumbing is that of
`AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionSheafULift_represented`
— the represented sheaf is rewritten as the universe lift of `Spec Γ(U)`, and the closed set of
points is carried across the two point-space homeomorphisms — but it ends differently: the
quasi-compactness of the complement makes the closed set the zero locus of a *finitely
generated* ideal, by
`AlgebraicGeometry.FormalSpace.exists_fg_zeroLocusPoints_eq_of_isClosed_of_isCompact_compl`,
and for a finitely generated ideal the completion along its zero locus is the completion along
the ideal, by
`AlgebraicGeometry.FormalSpace.nonempty_completionAlongIdealIsoCompletionSheaf`. -/
theorem exists_fg_nonempty_completionSheafULift_represented_iso_completionAlongIdeal
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (W : Set (Space.pointsULift.{u + 1} B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U).obj))
    (hW : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U).obj) W)
    (hWqc : @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U).obj) Wᶜ) :
    ∃ I : Ideal ↥Γ((BigFppfOver.toScheme B S hS).obj U, ⊤), I.FG ∧
      Nonempty (Space.completionSheafULift B S hS
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U) W ≅
        completionAlongIdeal B S hS (globalSectionsStructureMap B S hS U)
          (contains_spec_globalSections B S hS U) I) := by
  let hA := contains_spec_globalSections B S hS U
  let fS := globalSectionsStructureMap B S hS U
  obtain ⟨T, hT, hTqc, ⟨i⟩⟩ := exists_isClosed_nonempty_iso_completionSheaf B S hS U W hW
  obtain ⟨I, hIfg, hIeq⟩ :=
    exists_fg_zeroLocusPoints_eq_of_isClosed_of_isCompact_compl B S hS hA fS T hT (hTqc hWqc)
  obtain ⟨k⟩ := nonempty_completionAlongIdealIsoCompletionSheaf B S hS hA fS I hIfg
  refine ⟨I, hIfg, ⟨i ≪≫ ?_⟩⟩
  rw [hIeq]
  exact k.symm

/-- **The completion of an affine stage along a constructible closed set is countably
indexed.** By `exists_fg_nonempty_completionSheafULift_represented_iso_completionAlongIdeal`
it is a completion along a finitely generated ideal, and such a completion is the colimit of
the infinitesimal neighbourhoods of that ideal, a diagram indexed by `ULift ℕ`
(`AlgebraicGeometry.FormalSpace.isCountablyIndexed_completionAlongIdeal`). -/
theorem isCountablyIndexed_completionSheafULift_affineStageSheaf
    (V : BigAffineFppf B S hS)
    (V' : Set (Space.pointsULift.{u + 1} B S hS (affineStageSheaf B S hS V).obj))
    (hV' : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS
      (affineStageSheaf B S hS V).obj) V')
    (hV'qc : @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS
      (affineStageSheaf B S hS V).obj) V'ᶜ) :
    IsCountablyIndexed B S hS
      (Space.completionSheafULift B S hS (affineStageSheaf B S hS V) V') := by
  let _ : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((BigAffineFppf.inclusion B S hS).obj V)) := V.property
  obtain ⟨I, hIfg, ⟨k⟩⟩ :=
    exists_fg_nonempty_completionSheafULift_represented_iso_completionAlongIdeal B S hS
      ((BigAffineFppf.inclusion B S hS).obj V) V' hV' hV'qc
  obtain ⟨D, hD, ⟨m⟩⟩ := isCountablyIndexed_completionAlongIdeal B S hS _ _ I
  exact ⟨D, hD, ⟨k ≪≫ m⟩⟩

/-- **The geometric half of Stacks 0GVQ.** Let `X` be an affine formal algebraic space over `S`
and let `W` be a closed subset of the points of `X`. Then the completion `X_{/W}` of `X` along
`W` is a directed colimit of affine schemes over `S` whose transition morphisms are
thickenings, that is it has an affine presentation as in Definition 0AI7.

Nothing here is assumed about `X_{/W}`: the completion of the presenting colimit is the
colimit of the completions of its stages, by
`AlgebraicGeometry.FormalSpace.completionSheafULiftIsoColimitCompletion`. What Stacks 0GVQ
asserts beyond this conclusion is the set-theoretic condition of Stacks 0AIS. Stacks 0AIY at
the affine stages is supplied by
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_completionSheafULift_affineStageSheaf`.
-/
theorem exists_affinePresentation_completionSheafULift' (X : FppfSheaf B S hS)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (W : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hW : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) W) :
    ∃ (K : Type (u + 1)) (pre : Preorder K), letI := pre
      Nonempty K ∧ IsDirected K (· ≤ ·) ∧
      ∃ F : K ⥤ BigAffineFppf B S hS,
        (∀ ⦃p q : K⦄ (f : p ⟶ q), Stacks.Thickenings.IsThickening
          ((BigAffineFppf.toScheme B S hS).map (F.map f))) ∧
        Nonempty (Space.completionSheafULift B S hS X W ≅ colimit (F ⋙
          BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))) := by
  obtain ⟨-, I, pre, hne, hdir, D, hthickD, ⟨e⟩⟩ := hX
  let _ : Preorder I := pre
  let _ : Nonempty I := hne
  let _ : IsDirected I (· ≤ ·) := hdir
  let E : I ⥤ FppfSheaf B S hS := D ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  obtain ⟨K, preK, hneK, hdirK, -, F, hF, heF⟩ :=
    exists_affinePresentation_completionSheafULift_of_colimit' B S hS E X e W
      (fun i ↦ isAffineFormalAlgebraicSpace_completionSheafULift_affineStageSheaf B S hS
        (D.obj i) _ (isClosed_preimage_pointsMapULift _ W hW))
      (fun {_ _} f ↦ relative_isThickening_sheafifiedYoneda_map B S hS (D.map f) (hthickD f))
      (completionSheafULiftIsoColimitCompletion B S hS E X e W)
  exact ⟨K, preK, hneK, hdirK, F, hF, heF⟩

/-- **The completion of a countably indexed affine formal algebraic space along a constructible
closed set is countably indexed.** This is the geometric half of clause (3) of Stacks 0GVV.

`X` is a colimit of affine schemes indexed by `ℕ`, so the completion is the colimit of the
stagewise completions over the same `ℕ`
(`AlgebraicGeometry.FormalSpace.completionSheafULiftIsoColimitCompletion`). Each stage is a
represented affine and its point space is that of `X`
(`AlgebraicGeometry.FormalSpace.isHomeomorph_pointsMapULift_colimitι`), so the closed set pulls
back with its complement still quasi-compact and the stagewise completion is countably indexed
(`AlgebraicGeometry.FormalSpace.isCountablyIndexed_completionSheafULift_affineStageSheaf`).
The combined presentation of a colimit then has a countable index, by the guarded conjunct of
`AlgebraicGeometry.FormalSpace.exists_affinePresentation_of_colimit`, and a countable directed
presentation is a sequential one by **Stacks 0AII**. -/
theorem isCountablyIndexed_completionSheafULift (X : FppfSheaf B S hS)
    (hX : IsCountablyIndexed B S hS X)
    (W : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hW : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) W)
    (hWqc : @IsCompact _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) Wᶜ) :
    IsCountablyIndexed B S hS (Space.completionSheafULift B S hS X W) := by
  obtain ⟨I, pre, hne, hdir, hcntI, D, hthickD, ⟨e⟩⟩ :=
    (isCountablyIndexed_iff_exists_countable_presentation B S hS X).mp hX
  let _ : Preorder I := pre
  let _ : Nonempty I := hne
  let _ : IsDirected I (· ≤ ·) := hdir
  let _ : Countable I := hcntI
  let E : I ⥤ FppfSheaf B S hS := D ⋙ BigAffineFppf.inclusion B S hS ⋙
    Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  have hstagecnt : ∀ n : I, IsCountablyIndexed B S hS
      ((completionColimitDiagram B S hS E X e W).obj n) := by
    intro n
    let _ := Space.pointTopologyULift.{u + 1} B S hS (E.obj n).obj
    let _ := Space.pointTopologyULift.{u + 1} B S hS X.obj
    refine isCountablyIndexed_completionSheafULift_affineStageSheaf B S hS (D.obj n) _
      (isClosed_preimage_pointsMapULift _ W hW) ?_
    rw [← Set.preimage_compl]
    exact ((isHomeomorph_pointsMapULift_colimitι B S hS D hthickD X e.symm n).homeomorph
      _).isCompact_preimage.mpr hWqc
  obtain ⟨K, preK, hneK, hdirK, hcntK, F, hF, heF⟩ :=
    exists_affinePresentation_completionSheafULift_of_colimit' B S hS E X e W
      (fun i ↦ isAffineFormalAlgebraicSpace_completionSheafULift_affineStageSheaf B S hS
        (D.obj i) _ (isClosed_preimage_pointsMapULift _ W hW))
      (fun {_ _} f ↦ relative_isThickening_sheafifiedYoneda_map B S hS (D.map f) (hthickD f))
      (completionSheafULiftIsoColimitCompletion B S hS E X e W)
  exact (isCountablyIndexed_iff_exists_countable_presentation B S hS _).mpr
    ⟨K, preK, hneK, hdirK, hcntK inferInstance hstagecnt, F, hF, heF⟩

/-! ### The set-theoretic condition of Stacks 0AIS for a completion -/

/-- A locally surjective morphism of presheaves of `Type (u + 1)` induces a locally surjective
morphism of completion subfunctors, the source being completed along the *full* inverse image
of the set of points of the target.

A section of the completion subfunctor of the target lifts, on a covering, to a section of the
source; such a lift has point-set image in the inverse image of the given set of points because
its own image does, so it is a section of the completion subfunctor of the source. -/
theorem isLocallySurjective_completionMapULift
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : X' ⟶ X)
    (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f)
    (T : Set (Space.pointsULift.{u + 1} B S hS X)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Space.completionMapULift B S hS f
        (Space.pointsMapULift B S hS X' f ⁻¹' T) T (Set.Subset.refl _)) := by
  refine ⟨fun {V} x ↦ ?_⟩
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (Presheaf.imageSieve_mem (BigFppfOver.topology B S hS) f x.val)
  intro V' h hh
  obtain ⟨y, hy⟩ := hh
  exact ⟨⟨y, hasImageInULift_preimage_of_hasImageInULift_map B S hS f T V' y
    (hy ▸ (Space.completionSubfunctorULift B S hS X T).map h.op x.property)⟩, Subtype.ext hy⟩

/-- **A surjection of fppf sheaves induces a surjection of completions**, the source being
completed along the full inverse image of the set of points of the target. This is
`AlgebraicGeometry.FormalSpace.isLocallySurjective_completionMapULift` after sheafification:
surjections of sheaves of sets are the locally surjective morphisms, and sheafification
preserves local surjectivity. -/
theorem epi_completionSheafMapULift {X' X : FppfSheaf B S hS} (f : X' ⟶ X) (hf : Epi f)
    (T : Set (Space.pointsULift.{u + 1} B S hS X.obj)) :
    Epi (Space.completionSheafMapULift B S hS f
      (Space.pointsMapULift B S hS X'.obj f.hom ⁻¹' T) T (Set.Subset.refl _)) := by
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f.hom :=
    (Sheaf.isLocallySurjective_iff_epi f).mpr hf
  have := isLocallySurjective_completionMapULift B S hS f.hom hls T
  have hts : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      ((BigFppfOver.topology B S hS).toSheafify
        (Space.completionSubfunctorULift B S hS X.obj T).toFunctor) := inferInstance
  have hcomp : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS)
      (Space.completionMapULift B S hS f.hom
          (Space.pointsMapULift B S hS X'.obj f.hom ⁻¹' T) T (Set.Subset.refl _) ≫
        (BigFppfOver.topology B S hS).toSheafify
          (Space.completionSubfunctorULift B S hS X.obj T).toFunctor) :=
    Presheaf.isLocallySurjective_comp _ _ _
  have hsub : Sheaf.IsLocallySurjective (Space.completionSheafMapULift B S hS f
      (Space.pointsMapULift B S hS X'.obj f.hom ⁻¹' T) T (Set.Subset.refl _)) :=
    (Presheaf.isLocallySurjective_iff_of_fac (BigFppfOver.topology B S hS)
      ((BigFppfOver.topology B S hS).toSheafify_naturality
        (Space.completionMapULift B S hS f.hom
          (Space.pointsMapULift B S hS X'.obj f.hom ⁻¹' T) T (Set.Subset.refl _))).symm).mp hcomp
  exact Sheaf.epi_of_isLocallySurjective' _

/-- **Stacks 0AIS for the completion of an affine formal algebraic space.** Let `X` be an
affine formal algebraic space over `S` and let `W` be a closed set of points of `X`. Then the
completion `X_{/W}` satisfies the set-theoretic condition of Stacks 0AIS.

The condition does not follow from the affine presentation of `X_{/W}`: that presentation is
indexed by a disjoint union of the indices of the presentations of the stages, which is why
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit` (Stacks 0GVM) carries the
condition as a hypothesis. It follows instead from the condition *for `X`*, which an affine
formal algebraic space satisfies by definition. That condition gives a surjection onto `X` from
the fppf sheaf `h_U` of an object `U` of the site;
`AlgebraicGeometry.FormalSpace.epi_completionSheafMapULift` turns it into a surjection of the
completion of `h_U` along the inverse image of `W` onto `X_{/W}`; the completion of `h_U`
satisfies the condition by Stacks 0AIS for an algebraic space
(`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_completionSheaf`, read across
`AlgebraicGeometry.FormalSpace.completionSheaf_eq_completionSheafULift_uliftYoneda`), so
`X_{/W}` receives a surjection from the sheaf of an object of the site; and a directed colimit
of affine schemes along thickenings which receives such a surjection satisfies the condition,
by `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_colimit_of_representable_epi`,
whose kernel-pair half comes from the representability of the diagonal (Stacks 0AI8). The
colimit presentation is `exists_affinePresentation_completionSheafULift`. -/
theorem satisfiesSetTheoreticCondition_completionSheafULift (X : FppfSheaf B S hS)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (W : Set (Space.pointsULift.{u + 1} B S hS X.obj))
    (hW : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS X.obj) W) :
    SatisfiesSetTheoreticCondition B S hS (Space.completionSheafULift B S hS X W) := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let G := Sheaf.sheafifiedYoneda J
  let Fp := sheafToPresheaf J (Type (u + 1))
  let eG := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
  -- the representable surjection onto `X` given by the set-theoretic condition for `X`
  obtain ⟨U₀, -, hU₀, -, hU₀rep, -, p, hp, -, -⟩ := hX.1
  let Y : FppfSheaf B S hS := ⟨yoneda.obj U₀ ⋙ uliftFunctor.{u + 1},
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS U₀).isSheaf⟩
  let eU : hU₀ ≅ Y :=
    (Functor.FullyFaithful.ofFullyFaithful Fp).preimageIso (Classical.choice hU₀rep)
  let g : Y ⟶ X := eU.inv ≫ p
  have hg : Epi g := by
    have := hp
    dsimp only [g]
    infer_instance
  let _ := Space.pointTopologyULift.{u + 1} B S hS X.obj
  let _ := Space.pointTopologyULift.{u + 1} B S hS Y.obj
  let _ := Space.pointTopology B S hS (yoneda.obj U₀)
  -- the inverse image of `W` on the chart, as a closed set of points of the chart
  have hW'closed : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Y.obj)
      (Space.pointsMapULift B S hS Y.obj g.hom ⁻¹' W) :=
    hW.preimage (Space.continuous_pointsMapULift.{u + 1} B S hS g.hom)
  obtain ⟨T₀, hT₀, -, hbridge⟩ := exists_isClosed_completionSheaf_eq_completionSheafULift B S hS
    U₀ Y rfl _ hW'closed
  -- Stacks 0AIS for the completion of the chart, a represented sheaf
  have hcond :
      SatisfiesSetTheoreticCondition B S hS (Space.completionSheafULift B S hS Y
        (Space.pointsMapULift B S hS Y.obj g.hom ⁻¹' W)) := by
    rw [← hbridge]
    exact satisfiesSetTheoreticCondition_completionSheaf
      (isAlgebraicSpace_yoneda B S hS U₀) T₀ hT₀
  obtain ⟨V, -, hV, -, hVrep, -, q, hq, -, -⟩ := hcond
  have hm : Epi (Space.completionSheafMapULift B S hS g
      (Space.pointsMapULift B S hS Y.obj g.hom ⁻¹' W) W (Set.Subset.refl _)) :=
    epi_completionSheafMapULift B S hS g hg W
  obtain ⟨K, pre, hne, hdir, Fd, hthick, ⟨eK⟩⟩ :=
    exists_affinePresentation_completionSheafULift' B S hS X hX W hW
  let _ : Preorder K := pre
  let _ : Nonempty K := hne
  let _ : IsDirected K (· ≤ ·) := hdir
  let eV : hV ≅ G.obj V :=
    (Functor.FullyFaithful.ofFullyFaithful Fp).preimageIso
      (Classical.choice hVrep ≪≫ (Fp.mapIso (eG.app V)).symm)
  let fV : G.obj V ⟶ Space.completionSheafULift B S hS X W :=
    eV.inv ≫ q ≫ Space.completionSheafMapULift B S hS g
      (Space.pointsMapULift B S hS Y.obj g.hom ⁻¹' W) W (Set.Subset.refl _)
  have hfV : Epi fV := by
    have := hq
    have := hm
    dsimp only [fV]
    infer_instance
  exact satisfiesSetTheoreticCondition_of_colimit_of_representable_epi B S hS Fd hthick
    (Space.completionSheafULift B S hS X W) ⟨eK⟩ V fV hfV

/-- **Stacks 0GVQ.** Let `S` be a scheme, let `X` be an affine formal algebraic space over `S`,
let `i : X_red ⟶ X` be a reduction of `X` and let `T ⊆ |X_red|` be a closed subset. Then the
completion `X_{/T}` of `X` along `T` — the fppf sheaf whose sections over an object `U` of the
big fppf site of `S` are the morphisms `f : U ⟶ X` with `f(|U|) ⊆ T` — is an affine formal
algebraic space over `S`.

Nothing is assumed beyond the tag's own hypotheses. The affine presentation is
`exists_affinePresentation_completionSheafULift` and the set-theoretic condition of Stacks 0AIS
is `satisfiesSetTheoreticCondition_completionSheafULift`.

The two steps the source cites in general form are proved here: that a closed subset of
`|X_red|` is a closed subset of `|X|` is
`AlgebraicGeometry.FormalSpace.IsReduction.isClosed_image_pointsMapULift`, and that
`X_{/T} = colim (X_λ)_{/T}` is
`AlgebraicGeometry.FormalSpace.completionSheafULiftIsoColimitCompletion`.

The reduction is supplied as data satisfying `AlgebraicGeometry.FormalSpace.IsReduction`
rather than constructed, since Stacks 0AIN — the existence of a reduction — is not available
in this library; this is how Stacks 0GVT is stated here as well, and it needs no choice. -/
@[stacks 0GVQ]
theorem isAffineFormalAlgebraicSpace_completionAlong' {X Xred : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (T : Set (Space.pointsULift.{u + 1} B S hS Xred.obj))
    (hT : @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Xred.obj) T) :
    IsAffineFormalAlgebraicSpace B S hS (completionAlong i T) :=
  ⟨satisfiesSetTheoreticCondition_completionSheafULift B S hS X hX _
      (hi.isClosed_image_pointsMapULift (T := T) hT),
    exists_affinePresentation_completionSheafULift' B S hS X hX _
      (hi.isClosed_image_pointsMapULift (T := T) hT)⟩

/-! ### Clause (1) of Stacks 0GVV in the ambient spelling -/

/-- **Clause (1) of Stacks 0GVV**, in the ambient spelling: the completion of an affine formal
algebraic space `Y` over `S` along a closed set of points of `Y` is again an affine formal
algebraic space. Through the bijection `|Y_red| = |Y|` given by the inclusion of a reduction
this is the source's statement about a closed subset of `|Y_red|`, and no reduction enters the
statement. -/
abbrev CompletionOfAffineIsAffine' : Prop :=
  ∀ Y : FppfSheaf B S hS, IsAffineFormalAlgebraicSpace B S hS Y →
    ∀ T : Set (Space.pointsULift.{u + 1} B S hS Y.obj),
      @IsClosed _ (Space.pointTopologyULift.{u + 1} B S hS Y.obj) T →
      IsAffineFormalAlgebraicSpace B S hS (Space.completionSheafULift B S hS Y T)

/-- **Clause (1) of Stacks 0GVV**, in the ambient spelling
`AlgebraicGeometry.FormalSpace.CompletionOfAffineIsAffine`: the completion of an affine formal
algebraic space over `S` along a closed set of its points is again an affine formal algebraic
space, for every such space and every such set at once. It is
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_completionAlong'` (Stacks 0GVQ) with
the reduction removed from the statement: the completion is formed along a closed set of points
of the space itself, which is what the consumers of clause (1) in this library — the
base-changed charts of Stacks 0GVR and Stacks 0GVW — supply, and so no `hred` is needed.

Nothing is assumed. The affine presentation is
`AlgebraicGeometry.FormalSpace.exists_affinePresentation_completionSheafULift` and the
set-theoretic condition of Stacks 0AIS is
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_completionSheafULift`. -/
@[stacks 0GVV "clause (1), in the ambient spelling `CompletionOfAffineIsAffine`, quantified \
over the affine formal algebraic space and over the closed subset of its own points. No \
hypotheses beyond the tag's own: the set-theoretic condition of Stacks 0AIS on the completions \
is proved — `satisfiesSetTheoreticCondition_completionSheafULift`; the commutation of \
completion with directed colimits of fppf sheaves is proved — \
`completionSheafULiftIsoColimitCompletion`; Stacks 0AIY at the affine stages is \
`isAffineFormalAlgebraicSpace_completionSheafULift_affineStageSheaf`. No `hred` is needed, the \
ambient spelling mentioning no reduction. Clause (1) is Stacks 0GVQ, whose registration stays \
on `isAffineFormalAlgebraicSpace_completionAlong'` above"]
theorem completionOfAffineIsAffine : CompletionOfAffineIsAffine' B S hS := fun Y hY W hW ↦
  ⟨satisfiesSetTheoreticCondition_completionSheafULift B S hS Y hY W hW,
    exists_affinePresentation_completionSheafULift' B S hS Y hY W hW⟩

end AlgebraicGeometry.FormalSpace

end
