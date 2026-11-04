module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom

/-!
# The composition law for the structure map of a morphism of algebraic spaces

A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` induces a morphism
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` of their small étale ringed topoi. For
composable `f` and `g`, the structure map of the composite morphism of ringed topoi, followed by
the comparison `AlgebraicGeometry.Space.smallEtaleRingedToposHom_compRingIso` of the direct
images of sheaves of commutative rings, is the structure map of `f ≫ g`:

`(g ∘ f)♯ ≫ (comparison) = (f ≫ g)♯`.

The structure map is transported to the spaces-étale site, where a section of a sheaf over an
object is determined by its restrictions to the étale scheme charts above that object
(`AlgebraicGeometry.Space.spacesEtale_section_ext`), and the equation becomes the chartwise
statement that pulling a regular function back from a chart of `Z` to a chart of `X` in one step
is the same as pulling it back through a chart of `Y`.

## Main definitions

* `AlgebraicGeometry.Space.ranProj` is the projection of the right Kan extension along the
  comparison functor, at a spaces-étale object, to a chart above it.
* `AlgebraicGeometry.Space.comparisonUnitIso` is the unit of the Kan-extension adjunction, as an
  isomorphism.
* `AlgebraicGeometry.Space.structureSharpSpaces` is the structure map of `f`, transported to the
  spaces-étale site of `Y`.

## Main results

* `AlgebraicGeometry.Space.spacesEtale_section_ext`: a section of a sheaf on the spaces-étale
  site is determined by its restrictions to the étale scheme charts above its object.
* `AlgebraicGeometry.Space.restriction_map_structureSharpSpaces`: restricting
  `structureSharpSpaces` along the comparison functor gives back the structure map.
* `AlgebraicGeometry.Space.chartBaseChangeMap_comp_chart`: the chart morphism of a composite is
  the composite of the chart morphisms.
* `AlgebraicGeometry.Space.structureSharpRanSet_comp`: the composition law for the structure map
  of sheaves of sets.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHom_comp_fSharp`: the composition law for the
  structure map of the morphism of ringed topoi.
* `AlgebraicGeometry.Space.exists_compRingIso_isCartesianComposition_comp_fSharp`: there is an
  isomorphism of the direct images of sheaves of commutative rings of a composite which is
  induced by cartesian composition and carries the composite structure map to the structure map
  of the composite.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The right Kan extension along the comparison functor -/

/-- The adjunction between restriction along the comparison functor and the right Kan extension
along it. -/
noncomputable abbrev comparisonAdjunction (X : AlgebraicSpaces B S hS) :
    smallEtaleComparisonRestriction B S hS X ⊣ smallEtaleComparisonRan B S hS X :=
  (comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)

/-- The projection of the right Kan extension at a spaces-étale object to an étale scheme chart
above it, as a natural transformation of sections functors. -/
noncomputable def ranProj (X : AlgebraicSpaces B S hS) (A : SpacesEtale B S hS X)
    (j : StructuredArrow (op A) (comparisonFunctor B S hS X).op) :
    smallEtaleComparisonRan B S hS X ⋙
        sectionsFunctor (SpacesEtale.topology B S hS X) (op A) ⟶
      sectionsFunctor (SmallEtale.topology B S hS X.1) j.right :=
  Functor.whiskerLeft (smallEtaleComparisonRan B S hS X) (sectionsRestrict j.hom) ≫
    Functor.whiskerRight (comparisonAdjunction B S hS X).counit
      (sectionsFunctor (SmallEtale.topology B S hS X.1) j.right)

/-- The sections of the right Kan extension at a spaces-étale object are the limit of the sections
over the étale scheme charts above it. -/
noncomputable def ranIsLimit (X : AlgebraicSpaces B S hS) (A : SpacesEtale B S hS X)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    IsLimit ((Functor.RightExtension.mk _
      ((comparisonFunctor B S hS X).op.ranCounit.app F.obj)).coneAt (op A)) :=
  (comparisonFunctor B S hS X).op.isPointwiseRightKanExtensionRanCounit F.obj (op A)

/-- The projection natural transformation is the projection of the limit cone. -/
theorem ranProj_app_apply (X : AlgebraicSpaces B S hS) (A : SpacesEtale B S hS X)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (j : StructuredArrow (op A) (comparisonFunctor B S hS X).op)
    (a : ((comparisonFunctor B S hS X).op.ran.obj F.obj).obj (op A)) :
    (ranProj B S hS X A j).app F a =
      ((Functor.RightExtension.mk _
        ((comparisonFunctor B S hS X).op.ranCounit.app F.obj)).coneAt (op A)).π.app j a := by
  have h : ((comparisonAdjunction B S hS X).counit.app F).hom =
      (comparisonFunctor B S hS X).op.ranCounit.app F.obj := by
    rw [Functor.sheafAdjunctionCocontinuous_counit_app_hom, Functor.ranAdjunction_counit]
  show ((comparisonAdjunction B S hS X).counit.app F).hom.app j.right
      (((comparisonFunctor B S hS X).op.ran.obj F.obj).map j.hom a) = _
  rw [h]
  rfl

/-- Two sections of the right Kan extension over a spaces-étale object agree as soon as all their
chart projections agree. -/
theorem ranProj_ext (X : AlgebraicSpaces B S hS) (A : SpacesEtale B S hS X)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    {a b : ((comparisonFunctor B S hS X).op.ran.obj F.obj).obj (op A)}
    (h : ∀ j, (ranProj B S hS X A j).app F a = (ranProj B S hS X A j).app F b) :
    a = b := by
  exact (Types.isLimitEquivSections (ranIsLimit B S hS X A F)).injective
    (Subtype.ext (funext fun j ↦ (ranProj_app_apply B S hS X A F j a).symm.trans
      ((h j).trans (ranProj_app_apply B S hS X A F j b))))

/-- Restricting a section of the right Kan extension and projecting to a chart is projecting
along the composite. -/
theorem ranProj_map (X : AlgebraicSpaces B S hS) {A A' : SpacesEtale B S hS X} (n : A ⟶ A')
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (j : StructuredArrow (op A) (comparisonFunctor B S hS X).op)
    (a : ((comparisonFunctor B S hS X).op.ran.obj F.obj).obj (op A')) :
    (ranProj B S hS X A j).app F
        (((comparisonFunctor B S hS X).op.ran.obj F.obj).map n.op a) =
      (ranProj B S hS X A' (StructuredArrow.mk (n.op ≫ j.hom))).app F a := by
  rw [ranProj_app_apply, ranProj_app_apply]
  simp only [Functor.RightExtension.coneAt_π_app, types_comp_apply, Functor.RightExtension.mk_left,
    Functor.RightExtension.mk_hom, StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self,
    ← Functor.map_comp_apply]
  rfl

/-- The chart projection `AlgebraicGeometry.Space.chartProjection` is the projection of the right
Kan extension at the cartesian spaces-étale chart. -/
theorem chartProjection_eq_ranProj {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    chartProjection B S hS f V j = ranProj B S hS X (chartBaseChange B S hS f V) j := rfl

/-! ### Sections on the spaces-étale site are determined on charts -/

/-- If `φ ≫ ψ` is the identity of sheaves of types, then `ψ` undoes `φ` on sections. -/
private theorem sheaf_hom_app_comp_eq_self {C : Type*} [Category C] {J : GrothendieckTopology C}
    {P Q : Sheaf J (Type u)} (φ : P ⟶ Q) (ψ : Q ⟶ P) (h : φ ≫ ψ = 𝟙 P) (U : Cᵒᵖ)
    (y : P.obj.obj U) : ψ.hom.app U (φ.hom.app U y) = y :=
  congrArg (fun m : P ⟶ P ↦ m.hom.app U y) h

section Unit

variable (X : AlgebraicSpaces B S hS)

/-- Projecting the unit of the Kan-extension adjunction to a chart is restriction. -/
theorem ranProj_unit_app (A : SpacesEtale B S hS X)
    (Q : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (j : StructuredArrow (op A) (comparisonFunctor B S hS X).op)
    (q : Q.obj.obj (op A)) :
    (ranProj B S hS X A j).app ((smallEtaleComparisonRestriction B S hS X).obj Q)
        (((comparisonAdjunction B S hS X).unit.app Q).hom.app (op A) q) =
      Q.obj.map j.hom q := by
  have htri := sheaf_hom_app_comp_eq_self
    ((smallEtaleComparisonRestriction B S hS X).map ((comparisonAdjunction B S hS X).unit.app Q))
    ((comparisonAdjunction B S hS X).counit.app ((smallEtaleComparisonRestriction B S hS X).obj Q))
    ((comparisonAdjunction B S hS X).left_triangle_components Q) j.right
  have hnat := NatTrans.naturality_apply
    ((comparisonAdjunction B S hS X).unit.app Q).hom j.hom q
  exact (congrArg (fun y ↦ ((comparisonAdjunction B S hS X).counit.app
      ((smallEtaleComparisonRestriction B S hS X).obj Q)).hom.app j.right y)
    hnat).symm.trans (htri _)

/-- The unit of the Kan-extension adjunction as an isomorphism: a sheaf on the spaces-étale site
is the right Kan extension of its restriction. -/
noncomputable def comparisonUnitIso (Q : Sheaf (SpacesEtale.topology B S hS X) (Type u)) :
    Q ≅ (smallEtaleComparisonRan B S hS X).obj
      ((smallEtaleComparisonRestriction B S hS X).obj Q) :=
  (smallEtaleComparisonRestriction B S hS X).asEquivalence.unitIso.app Q ≪≫
    (smallEtaleComparisonRanIso B S hS X).app
      ((smallEtaleComparisonRestriction B S hS X).obj Q)

/-- The isomorphism is the unit of the Kan-extension adjunction. -/
theorem comparisonUnitIso_hom (Q : Sheaf (SpacesEtale.topology B S hS X) (Type u)) :
    (comparisonUnitIso B S hS X Q).hom = (comparisonAdjunction B S hS X).unit.app Q := by
  show (smallEtaleComparisonRestriction B S hS X).asEquivalence.toAdjunction.unit.app Q ≫
    _ = _
  exact Adjunction.unit_rightAdjointUniq_hom_app
    (smallEtaleComparisonRestriction B S hS X).asEquivalence.toAdjunction
    (comparisonAdjunction B S hS X) Q

/-- Two sections of a sheaf on the spaces-étale site over an object agree as soon as their
restrictions to all étale scheme charts above that object agree. -/
theorem spacesEtale_section_ext (A : SpacesEtale B S hS X)
    (Q : Sheaf (SpacesEtale.topology B S hS X) (Type u)) {a b : Q.obj.obj (op A)}
    (h : ∀ j : StructuredArrow (op A) (comparisonFunctor B S hS X).op,
      Q.obj.map j.hom a = Q.obj.map j.hom b) :
    a = b := by
  have key : (comparisonUnitIso B S hS X Q).hom.hom.app (op A) a =
      (comparisonUnitIso B S hS X Q).hom.hom.app (op A) b := by
    rw [comparisonUnitIso_hom]
    exact ranProj_ext B S hS X A _ fun j ↦ by rw [ranProj_unit_app, ranProj_unit_app]; exact h j
  have hinv := sheaf_hom_app_comp_eq_self _ _ (comparisonUnitIso B S hS X Q).hom_inv_id (op A)
  exact ((hinv a).symm.trans (congrArg
    (fun y ↦ (comparisonUnitIso B S hS X Q).inv.hom.app (op A) y) key)).trans (hinv b)

end Unit

/-! ### The structure map on the spaces-étale site -/

section Spaces

variable {X Y : AlgebraicSpaces B S hS}

/-- The spaces-étale direct image at the universe of the structure rings. -/
noncomputable abbrev spacesDirectImage (f : X ⟶ Y) :
    Sheaf (SpacesEtale.topology B S hS X) (Type u) ⥤
      Sheaf (SpacesEtale.topology B S hS Y) (Type u) :=
  (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)

/-- The structure map at the level of sheaves of sets, with the direct image in its Kan-extension
form. -/
noncomputable abbrev structureSharpRanSet (f : X ⟶ Y) :
    structureSetSheaf B S hS Y ⟶
      (smallEtaleDirectImageRan B S hS f).obj (structureSetSheaf B S hS X) :=
  (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
    (structureSharpRan B S hS f)

/-- The structure map at the level of sheaves of sets. -/
noncomputable abbrev structureSharpSet (f : X ⟶ Y) :
    structureSetSheaf B S hS Y ⟶
      (smallEtaleDirectImage B S hS f).obj (structureSetSheaf B S hS X) :=
  (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
    (structureSharp B S hS f)

/-- On sections over an étale scheme chart, the Kan-extension form of the structure map is the
chartwise family of pullbacks of regular functions. -/
theorem structureSharpRanSet_app (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (x : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    (structureSharpRanSet B S hS f).hom.app (op V) x = structureMapApp B S hS f V x := rfl

/-- The structure map is its Kan-extension form, read through the Kan-extension comparison. -/
theorem structureSharpSet_eq (f : X ⟶ Y) :
    structureSharpSet B S hS f =
      structureSharpRanSet B S hS f ≫
        (smallEtaleDirectImageRanIso B S hS f).inv.app (structureSetSheaf B S hS X) :=
  congrArg (fun m ↦ structureSharpRanSet B S hS f ≫ m)
    (ringSheafMap_pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
      (structureRingSheaf B S hS X) (smallEtaleDirectImageRanIso B S hS f).inv)

/-- The two forms of the structure map agree through the Kan-extension comparison. -/
theorem structureSharpSet_comp_ranIso (f : X ⟶ Y) :
    structureSharpSet B S hS f ≫
        (smallEtaleDirectImageRanIso B S hS f).hom.app (structureSetSheaf B S hS X) =
      structureSharpRanSet B S hS f := by
  rw [structureSharpSet_eq, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- The transposed structure map, before the Kan-extension comparisons: the structure map read
through the quasi-inverse of the comparison equivalence. -/
noncomputable def structureSharpSpacesAux (f : X ⟶ Y) :
    (smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.obj
        (structureSetSheaf B S hS Y) ⟶
      (spacesDirectImage B S hS f).obj
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
          (structureSetSheaf B S hS X)) :=
  (smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.map
      (structureSharpSet B S hS f) ≫
    (smallEtaleComparisonRestriction B S hS Y).asEquivalence.unitIso.inv.app
      ((spacesDirectImage B S hS f).obj
        ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
          (structureSetSheaf B S hS X)))

/-- The structure map of `f`, transported to the spaces-étale site of `Y`. -/
noncomputable def structureSharpSpaces (f : X ⟶ Y) :
    (smallEtaleComparisonRan B S hS Y).obj (structureSetSheaf B S hS Y) ⟶
      (spacesDirectImage B S hS f).obj
        ((smallEtaleComparisonRan B S hS X).obj (structureSetSheaf B S hS X)) :=
  ((smallEtaleComparisonRanIso B S hS Y).inv.app (structureSetSheaf B S hS Y) ≫
      structureSharpSpacesAux B S hS f) ≫
    (spacesDirectImage B S hS f).map
      ((smallEtaleComparisonRanIso B S hS X).hom.app (structureSetSheaf B S hS X))

/-- Restricting the inverse unit of the comparison equivalence is its counit. -/
theorem restriction_map_unitIso_inv (W : AlgebraicSpaces B S hS)
    (Q : Sheaf (SpacesEtale.topology B S hS W) (Type u)) :
    (smallEtaleComparisonRestriction B S hS W).map
        ((smallEtaleComparisonRestriction B S hS W).asEquivalence.unitIso.inv.app Q) =
      (smallEtaleComparisonRestriction B S hS W).asEquivalence.counitIso.hom.app
        ((smallEtaleComparisonRestriction B S hS W).obj Q) := by
  have h1 := (smallEtaleComparisonRestriction B S hS W).asEquivalence.functor_unitIso_comp Q
  have h2 : (smallEtaleComparisonRestriction B S hS W).map
        ((smallEtaleComparisonRestriction B S hS W).asEquivalence.unitIso.hom.app Q) ≫
      (smallEtaleComparisonRestriction B S hS W).map
        ((smallEtaleComparisonRestriction B S hS W).asEquivalence.unitIso.inv.app Q) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  exact (IsIso.inv_eq_of_hom_inv_id h2).symm.trans (IsIso.inv_eq_of_hom_inv_id h1)

/-- Restricting the inverse Kan-extension comparison, followed by the counit of the comparison
equivalence, is the counit of the Kan-extension adjunction. -/
theorem restriction_map_ranIso_inv_comp_counitIso (W : AlgebraicSpaces B S hS)
    (F : Sheaf (SmallEtale.topology B S hS W.1) (Type u)) :
    (smallEtaleComparisonRestriction B S hS W).map
          ((smallEtaleComparisonRanIso B S hS W).inv.app F) ≫
        (smallEtaleComparisonRestriction B S hS W).asEquivalence.counitIso.hom.app F =
      (comparisonAdjunction B S hS W).counit.app F := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (smallEtaleComparisonRestriction B S hS W).asEquivalence.toAdjunction
    (comparisonAdjunction B S hS W) F
  rw [show (smallEtaleComparisonRestriction B S hS W).asEquivalence.counitIso.hom.app F =
      (smallEtaleComparisonRestriction B S hS W).map
          ((smallEtaleComparisonRanIso B S hS W).hom.app F) ≫
        (comparisonAdjunction B S hS W).counit.app F from h.symm,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- Restricting the transposed structure map gives the structure map. -/
theorem restriction_map_structureSharpSpacesAux (f : X ⟶ Y) :
    (smallEtaleComparisonRestriction B S hS Y).map (structureSharpSpacesAux B S hS f) =
      (smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.app
          (structureSetSheaf B S hS Y) ≫
        structureSharpSet B S hS f :=
  (CategoryTheory.Functor.map_comp _ _ _).trans
    ((congrArg (fun m ↦ (smallEtaleComparisonRestriction B S hS Y).map
        ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.map
          (structureSharpSet B S hS f)) ≫ m)
      (restriction_map_unitIso_inv B S hS Y _)).trans
      ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.naturality
        (structureSharpSet B S hS f)))

/-- Restricting `structureSharpSpaces` along the comparison functor gives back the Kan-extension
form of the structure map, read through the counit of the Kan-extension adjunction. -/
theorem restriction_map_structureSharpSpaces (f : X ⟶ Y) :
    (smallEtaleComparisonRestriction B S hS Y).map (structureSharpSpaces B S hS f) =
      (comparisonAdjunction B S hS Y).counit.app (structureSetSheaf B S hS Y) ≫
        structureSharpRanSet B S hS f := by
  have e2 := congrArg
    (fun m ↦ ((smallEtaleComparisonRestriction B S hS Y).map
          ((smallEtaleComparisonRanIso B S hS Y).inv.app (structureSetSheaf B S hS Y)) ≫ m) ≫
        (smallEtaleComparisonRestriction B S hS Y).map
          ((spacesDirectImage B S hS f).map
            ((smallEtaleComparisonRanIso B S hS X).hom.app (structureSetSheaf B S hS X))))
    (restriction_map_structureSharpSpacesAux B S hS f)
  have e4 := congrArg₂ (fun p q ↦ p ≫ q)
    (restriction_map_ranIso_inv_comp_counitIso B S hS Y (structureSetSheaf B S hS Y))
    (structureSharpSet_comp_ranIso B S hS f)
  exact e2.trans e4

/-- On sections over an étale scheme chart, the spaces-étale structure map is the chartwise
family of pullbacks of regular functions. -/
theorem structureSharpSpaces_app_chart (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (q : ((smallEtaleComparisonRan B S hS Y).obj (structureSetSheaf B S hS Y)).obj.obj
      (op ((comparisonFunctor B S hS Y).obj V))) :
    (structureSharpSpaces B S hS f).hom.app
        (op ((comparisonFunctor B S hS Y).obj V)) q =
      structureMapApp B S hS f V
        (((comparisonAdjunction B S hS Y).counit.app
          (structureSetSheaf B S hS Y)).hom.app (op V) q) :=
  congrArg (fun m ↦ m.hom.app (op V) q) (restriction_map_structureSharpSpaces B S hS f)

end Spaces

/-! ### The composition law -/

section Comp

variable {X Y Z : AlgebraicSpaces B S hS}

/-- The chart of `X` above `X ×_Z W` determined by a chart `V` of `Y` above `Y ×_Z W`: base
change of the structure morphism of `V`, followed by the composition comparison of base
changes. -/
noncomputable def chartBaseChangeComp (f : X ⟶ Y) (g : Y ⟶ Z) (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g W)) (comparisonFunctor B S hS Y).op) :
    chartBaseChange B S hS f j.right.unop ⟶ chartBaseChange B S hS (f ≫ g) W :=
  (spacesBaseChange B S hS f).functor.map j.hom.unop ≫
    (spacesBaseChange_comp B S hS f g).hom.app ((comparisonFunctor B S hS Z).obj W)

/-- The chart morphism of a composite: pulling back from a chart `W` of `Z` to a chart of `X`
above `X ×_Z W` obtained from a chart `V` of `Y` above `Y ×_Z W` is pulling back through `V`. -/
theorem chartBaseChangeMap_comp_chart (f : X ⟶ Y) (g : Y ⟶ Z) (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g W)) (comparisonFunctor B S hS Y).op)
    (k : StructuredArrow (op (chartBaseChange B S hS f j.right.unop))
      (comparisonFunctor B S hS X).op) :
    chartBaseChangeMap B S hS (f ≫ g) W
        (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom)) =
      chartBaseChangeMap B S hS f j.right.unop k ≫ chartBaseChangeMap B S hS g W j := by
  apply yoneda.map_injective
  rw [CategoryTheory.Functor.map_comp, yoneda_map_chartBaseChangeMap,
    yoneda_map_chartBaseChangeMap, yoneda_map_chartBaseChangeMap]
  have hproj : (SpacesEtale.toSpaces B S hS X).map
        ((spacesBaseChange_comp B S hS f g).hom.app
          ((comparisonFunctor B S hS Z).obj W)) ≫
      (spacesBaseChange B S hS (f ≫ g)).projection.app
        ((comparisonFunctor B S hS Z).obj W) =
      (spacesBaseChange B S hS f).projection.app
          ((spacesBaseChange B S hS g).functor.obj ((comparisonFunctor B S hS Z).obj W)) ≫
        (spacesBaseChange B S hS g).projection.app ((comparisonFunctor B S hS Z).obj W) :=
    spacesBaseChange_comp_projection B S hS f g ((comparisonFunctor B S hS Z).obj W)
  have hnat := (spacesBaseChange B S hS f).projection.naturality j.hom.unop
  have key := (congrArg (fun m ↦ (SpacesEtale.toSpaces B S hS X).map k.hom.unop ≫
      (SpacesEtale.toSpaces B S hS X).map
        ((spacesBaseChange B S hS f).functor.map j.hom.unop) ≫ m) hproj).trans
    (congrArg (fun m ↦ (SpacesEtale.toSpaces B S hS X).map k.hom.unop ≫ m ≫
      (spacesBaseChange B S hS g).projection.app
        ((comparisonFunctor B S hS Z).obj W)) hnat)
  exact congrArg (fun m ↦ m.hom) key

/-- Pulling a regular function back from a chart of `Z` to a chart of `X` in one step is pulling
it back through a chart of `Y`. -/
theorem chartPullback_comp_chart (f : X ⟶ Y) (g : Y ⟶ Z) (W : SmallEtale B S hS Z.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g W)) (comparisonFunctor B S hS Y).op)
    (k : StructuredArrow (op (chartBaseChange B S hS f j.right.unop))
      (comparisonFunctor B S hS X).op)
    (x : (structureSetSheaf B S hS Z).obj.obj (op W)) :
    chartPullback B S hS (f ≫ g) W
        (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom)) x =
      chartPullback B S hS f j.right.unop k (chartPullback B S hS g W j x) := by
  have key : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (chartBaseChangeMap B S hS (f ≫ g) W
          (StructuredArrow.mk ((chartBaseChangeComp B S hS f g W j).op ≫ k.hom)))).op =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (chartBaseChangeMap B S hS g W j)).op ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (chartBaseChangeMap B S hS f j.right.unop k)).op := by
    rw [chartBaseChangeMap_comp_chart, CategoryTheory.Functor.map_comp, op_comp,
      CategoryTheory.Functor.map_comp]
  exact congrArg (fun φ ↦ φ x) ((congrArg (forget CommRingCat.{u}).map key).trans
    ((forget CommRingCat.{u}).map_comp _ _))

/-- The composition law for the structure map, at the level of sheaves of sets and with the
direct images in their Kan-extension form. -/
theorem structureSharpRanSet_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureSharpRanSet B S hS g ≫
        (smallEtaleComparisonRestriction B S hS Z).map
          ((spacesDirectImage B S hS g).map (structureSharpSpaces B S hS f) ≫
            (spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app
              ((smallEtaleComparisonRan B S hS X).obj (structureSetSheaf B S hS X))) =
      structureSharpRanSet B S hS (f ≫ g) := by
  refine Sheaf.hom_ext_sections (fun W x ↦ ?_)
  have hG1 : (structureSharpSpaces B S hS f).hom.app
        (op (chartBaseChange B S hS g W.unop)) (structureMapApp B S hS g W.unop x) =
      ((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj).map
        ((spacesBaseChange_comp B S hS f g).hom.app
          ((comparisonFunctor B S hS Z).obj W.unop)).op
        (structureMapApp B S hS (f ≫ g) W.unop x) := by
    refine spacesEtale_section_ext B S hS Y (chartBaseChange B S hS g W.unop)
      ((spacesDirectImage B S hS f).obj
        ((smallEtaleComparisonRan B S hS X).obj (structureSetSheaf B S hS X))) (fun j ↦ ?_)
    refine ranProj_ext B S hS X (chartBaseChange B S hS f j.right.unop)
      (structureSetSheaf B S hS X) (fun k ↦ ?_)
    have hL : ((spacesDirectImage B S hS f).obj
            ((smallEtaleComparisonRan B S hS X).obj
              (structureSetSheaf B S hS X))).obj.map j.hom
          ((structureSharpSpaces B S hS f).hom.app
            (op (chartBaseChange B S hS g W.unop))
            (structureMapApp B S hS g W.unop x)) =
        structureMapApp B S hS f j.right.unop (chartPullback B S hS g W.unop j x) :=
      ((NatTrans.naturality_apply (structureSharpSpaces B S hS f).hom j.hom
          (structureMapApp B S hS g W.unop x)).symm.trans
        (structureSharpSpaces_app_chart B S hS f j.right.unop
          (((comparisonFunctor B S hS Y).op.ran.obj (structureSetSheaf B S hS Y).obj).map
            j.hom (structureMapApp B S hS g W.unop x)))).trans
        (congrArg (structureMapApp B S hS f j.right.unop)
          (chartProjection_structureMapApp B S hS g W.unop j x))
    have hR : ((spacesDirectImage B S hS f).obj
            ((smallEtaleComparisonRan B S hS X).obj
              (structureSetSheaf B S hS X))).obj.map j.hom
          (((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj).map
            ((spacesBaseChange_comp B S hS f g).hom.app
              ((comparisonFunctor B S hS Z).obj W.unop)).op
            (structureMapApp B S hS (f ≫ g) W.unop x)) =
        ((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj).map
          (chartBaseChangeComp B S hS f g W.unop j).op
          (structureMapApp B S hS (f ≫ g) W.unop x) :=
      (Functor.map_comp_apply
        ((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj)
        ((spacesBaseChange_comp B S hS f g).hom.app
          ((comparisonFunctor B S hS Z).obj W.unop)).op
        ((spacesBaseChange B S hS f).functor.map j.hom.unop).op
        (structureMapApp B S hS (f ≫ g) W.unop x)).symm
    rw [hL, hR, ranProj_map]
    exact ((chartProjection_structureMapApp B S hS f j.right.unop k
        (chartPullback B S hS g W.unop j x)).trans
      (chartPullback_comp_chart B S hS f g W.unop j k x).symm).trans
      (chartProjection_structureMapApp B S hS (f ≫ g) W.unop _ x).symm
  have hcancel : ((comparisonFunctor B S hS X).op.ran.obj
        (structureSetSheaf B S hS X).obj).map
      ((spacesBaseChange_comp B S hS f g).inv.app
        ((comparisonFunctor B S hS Z).obj W.unop)).op
      (((comparisonFunctor B S hS X).op.ran.obj (structureSetSheaf B S hS X).obj).map
        ((spacesBaseChange_comp B S hS f g).hom.app
          ((comparisonFunctor B S hS Z).obj W.unop)).op
        (structureMapApp B S hS (f ≫ g) W.unop x)) =
      structureMapApp B S hS (f ≫ g) W.unop x := by
    rw [← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id_app, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  exact (congrArg (fun y ↦ ((comparisonFunctor B S hS X).op.ran.obj
      (structureSetSheaf B S hS X).obj).map
      ((spacesBaseChange_comp B S hS f g).inv.app
        ((comparisonFunctor B S hS Z).obj W.unop)).op y) hG1).trans hcancel

/-- The composite of the two structure maps of ringed topoi, followed by the composition
comparison, is the spaces-étale composite transported along the comparison functor. -/
theorem forgetRing_comp_structure_formula (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleDirectImageRanIso B S hS g).inv.app (structureSetSheaf B S hS Y) ≫
        (smallEtaleRingedToposHom B S hS g).toToposHom.pushforward.map
          (structureSharpSet B S hS f) ≫
        (smallToposMorphismTypeU_comp B S hS f g).hom.app (structureSetSheaf B S hS X) ≫
        (smallEtaleDirectImageRanIso B S hS (f ≫ g)).hom.app (structureSetSheaf B S hS X) =
      (smallEtaleComparisonRestriction B S hS Z).map
        ((spacesDirectImage B S hS g).map (structureSharpSpaces B S hS f) ≫
          (spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app
            ((smallEtaleComparisonRan B S hS X).obj (structureSetSheaf B S hS X))) :=
  congrArg (fun m ↦ (smallEtaleComparisonRestriction B S hS Z).map
      ((spacesDirectImage B S hS g).map
          ((smallEtaleComparisonRanIso B S hS Y).inv.app (structureSetSheaf B S hS Y)) ≫
        (spacesDirectImage B S hS g).map
          ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.inverse.map
            (structureSharpSet B S hS f)) ≫
        (spacesDirectImage B S hS g).map
          ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.unitIso.inv.app
            ((spacesDirectImage B S hS f).obj
              ((smallEtaleComparisonRestriction B S hS X).asEquivalence.inverse.obj
                (structureSetSheaf B S hS X)))) ≫ m))
    ((spacesBaseChange_pushforward_compTypeU B S hS f g).hom.naturality
      ((smallEtaleComparisonRanIso B S hS X).hom.app (structureSetSheaf B S hS X))).symm

/-- The structure map of the morphism of ringed topoi, with the ring operations forgotten, is the
structure map of sheaves of sets. -/
theorem forgetRing_map_fSharp {W W' : AlgebraicSpaces B S hS} (h : W ⟶ W') :
    (smallEtaleRingedTopos B S hS W').forgetRing.map
        (smallEtaleRingedToposHom B S hS h).fSharp =
      structureSharpSet B S hS h := by
  show (sheafCompose (SmallEtale.topology B S hS W'.1) (forget RingCat.{u})).map
    ((sheafCompose (SmallEtale.topology B S hS W'.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).map
        (smallEtaleRingedToposHom B S hS h).fSharp) = _
  rw [forgetCommRingSheaf_map_fSharp]
  rfl

/-- The composite of the structure maps, read against the Kan-extension form. -/
theorem structureSharpSet_comp_formula (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureSharpSet B S hS g ≫
        (smallEtaleRingedToposHom B S hS g).toToposHom.pushforward.map
          (structureSharpSet B S hS f) ≫
        (smallToposMorphismTypeU_comp B S hS f g).hom.app (structureSetSheaf B S hS X) ≫
        (smallEtaleDirectImageRanIso B S hS (f ≫ g)).hom.app (structureSetSheaf B S hS X) =
      structureSharpRanSet B S hS g ≫
        (smallEtaleComparisonRestriction B S hS Z).map
          ((spacesDirectImage B S hS g).map (structureSharpSpaces B S hS f) ≫
            (spacesBaseChange_pushforward_compTypeU B S hS f g).hom.app
              ((smallEtaleComparisonRan B S hS X).obj (structureSetSheaf B S hS X))) := by
  rw [structureSharpSet_eq B S hS g]
  exact congrArg (fun m ↦ structureSharpRanSet B S hS g ≫ m)
    (forgetRing_comp_structure_formula B S hS f g)

/-- The structure map of the composite morphism of small étale ringed topoi, followed by the
comparison of the direct images of sheaves of commutative rings, is the structure map of the
composite morphism of algebraic spaces. -/
@[stacks 03G8 "compatibility with composition"]
theorem smallEtaleRingedToposHom_comp_fSharp (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((smallEtaleRingedToposHom B S hS g).comp
        (smallEtaleRingedToposHom B S hS f)).fSharp ≫
        (smallEtaleRingedToposHom_compRingIso B S hS f g).hom.app
          (smallEtaleRingedTopos B S hS X).O =
      (smallEtaleRingedToposHom B S hS (f ≫ g)).fSharp := by
  apply (smallEtaleRingedTopos B S hS Z).forgetRing.map_injective
  have h1 := RingedToposHom.comp_fSharp_forget
    (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS f)
  have h2 : (smallEtaleRingedTopos B S hS Z).forgetRing.map
      ((smallEtaleRingedToposHom_compRingIso B S hS f g).hom.app
        (smallEtaleRingedTopos B S hS X).O) =
      (smallToposMorphismTypeU_comp B S hS f g).hom.app (structureSetSheaf B S hS X) :=
    underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
      (SmallEtale.topology B S hS Z.1) _ (smallToposMorphismTypeU_comp B S hS f g)
  refine Eq.trans ((CategoryTheory.Functor.map_comp _ _ _).trans
    (congrArg₂ (fun p q ↦ p ≫ q)
      (h1.trans (congrArg₂ (fun p q ↦ p ≫ q) (forgetRing_map_fSharp B S hS g)
        (congrArg (fun m ↦ (smallEtaleRingedToposHom B S hS g).toToposHom.pushforward.map m)
          (forgetRing_map_fSharp B S hS f)))) h2)) ?_
  refine Eq.trans ?_ (forgetRing_map_fSharp B S hS (f ≫ g)).symm
  refine (Iso.cancel_iso_hom_right _ _
    ((smallEtaleDirectImageRanIso B S hS (f ≫ g)).app
      (structureSetSheaf B S hS X))).mp ?_
  refine Eq.trans ?_ (structureSharpSet_comp_ranIso B S hS (f ≫ g)).symm
  refine Eq.trans (Category.assoc _ _ _) (Eq.trans (Category.assoc _ _ _) ?_)
  exact (structureSharpSet_comp_formula B S hS f g).trans
    (structureSharpRanSet_comp B S hS f g)

/-- There is an isomorphism between the direct images of sheaves of commutative rings of the
composite of morphisms of ringed topoi and of the composite morphism of algebraic spaces which is
induced by cartesian composition and carries the structure map of the composite to the structure
map of the composite morphism. -/
@[stacks 03G8 "existence of the cartesian ring comparison"]
theorem exists_compRingIso_isCartesianComposition_comp_fSharp (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃ i : pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        ((smallEtaleRingedToposHom B S hS g).comp
          (smallEtaleRingedToposHom B S hS f)).toToposHom ≅
      pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS (f ≫ g)).toToposHom,
      IsCartesianComposition B S hS f g i ∧
        ((smallEtaleRingedToposHom B S hS g).comp
            (smallEtaleRingedToposHom B S hS f)).fSharp ≫
            i.hom.app (smallEtaleRingedTopos B S hS X).O =
          (smallEtaleRingedToposHom B S hS (f ≫ g)).fSharp :=
  ⟨smallEtaleRingedToposHom_compRingIso B S hS f g,
    smallEtaleRingedToposHom_compRingIso_isCartesianComposition B S hS f g,
    smallEtaleRingedToposHom_comp_fSharp B S hS f g⟩

end Comp

end AlgebraicGeometry.Space

end
