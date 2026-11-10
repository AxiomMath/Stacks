module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapComp

/-!
# The chart correspondence at the universe of the structure rings

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  Stacks 03G8 constructs the morphism
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` of small étale ringed topoi of `X` and `Y`
out of a bijection between the `f`-maps of Stacks 03G3 and the homomorphisms into the direct
image of the underlying geometric morphism, and asserts that the bijection is the canonical
one, in the sense of `AlgebraicGeometry.Space.IsChartCorrespondence`.  This file constructs
that bijection, at `Type u`, the universe in which a ringed topos declares its structure
rings and therefore its underlying topos.

The construction is the one of Stacks 03G4: a commutative diagram of étale scheme charts over
`f` with lower chart `V` is the same datum as an arrow of the spaces-étale site of `X` from an
étale scheme chart into the cartesian base change `X ×_Y V`, and the sections of a
spaces-étale sheaf over `X ×_Y V` are the limit of its sections over the étale scheme charts
above it; so an `f`-map is exactly a compatible family of sections of the direct image, that
is, a homomorphism into the direct image.

Both halves of that are already available at `Type u` and are used rather than repeated.  The
identification of arrows into the cartesian base change with diagrams of charts does not
mention the sheaves at all, so
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartCorrespondence.lean` serves it verbatim
(`AlgebraicGeometry.Space.chartDiagramOfBaseChangeArrow`,
`AlgebraicGeometry.Space.baseChangeArrowOfChartDiagram`,
`AlgebraicGeometry.Space.chartDiagram_square_iff`).  The limit description of the sections is
`AlgebraicGeometry.Space.ranIsLimit` together with
`AlgebraicGeometry.Space.comparisonUnitIso`, and the extensionality it gives is
`AlgebraicGeometry.Space.spacesEtale_section_ext`, all in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleStructureMapComp.lean`.

## Main definitions

* `AlgebraicGeometry.Space.fMapDescendedSectionTypeU` is the section of a spaces-étale sheaf
  over `X ×_Y V` attached by an `f`-map to a section over `V`, and
  `AlgebraicGeometry.Space.descendedHomTypeU` is the resulting homomorphism of sheaves;
  `AlgebraicGeometry.Space.fMapOfPushforwardHomTypeU` is the inverse construction and
  `AlgebraicGeometry.Space.descendedHomEquivTypeU` the bijection they make up, for a sheaf on
  the small étale site of `X` presented as the restriction of a spaces-étale sheaf.
* `AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse` is the chart correspondence
  itself: the bijection between `f`-maps and homomorphisms into the direct image of
  `AlgebraicGeometry.Space.smallEtaleRingedToposHom`.

## Main results

* `AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_chart`: **Stacks 03G8** — the
  bijection is the canonical one, in the sense of
  `AlgebraicGeometry.Space.IsChartCorrespondence`.
* `AlgebraicGeometry.Space.exists_fMapEquivPushforwardHom_ringUniverse`: the two together, in
  the existential form the construction of the structure map consumes.

## Implementation notes

`AlgebraicGeometry.Space.descendedHomEquivTypeU` is stated relative to a presentation of the
source sheaf as the restriction of a spaces-étale sheaf; the chart correspondence is obtained
from it by taking the preimage of the source sheaf under the comparison equivalence of Stacks
03G1, and `AlgebraicGeometry.Space.descendedHomTypeU_map` is what makes that independent of
the chosen presentation.

The suffix `TypeU` is the one this tree already uses for the instantiation at the universe of
the structure rings, as against the universe of the objects of the two étale sites: compare
`AlgebraicGeometry.Space.smallToposMorphismTypeU` and
`AlgebraicGeometry.Space.smallEtaleToposEquivTypeU`.  The declarations without the suffix, in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartCorrespondence.lean`, are the same
construction for sheaves valued in the universe of the sites; neither instantiates the other,
because the direct images they compare are different functors on different categories.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- An `f`-map depends on the vertical morphism of each diagram of charts and not on the proof
that the diagram commutes.  This is the universe-polymorphic form: the sheaves of sections of
the source and of the target may be valued in any two universes, as
`AlgebraicGeometry.Space.FMap` allows. -/
theorem FMap.app_congr {P : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type v}
    {Q : (SmallEtale B S hS Y.1)ᵒᵖ ⥤ Type w}
    (ξ : FMap B S hS X.1 Y.1 f.hom P Q)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    {g g' : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V}
    {hc : U.1.hom ≫ f.hom = yoneda.map g ≫ V.1.hom}
    {hc' : U.1.hom ≫ f.hom = yoneda.map g' ≫ V.1.hom}
    (hg : g = g') (s : Q.obj (op V)) :
    ξ.app ⟨U, V, g, hc⟩ s = ξ.app ⟨U, V, g', hc'⟩ s := by
  cases hg
  rfl

/-- Two `f`-maps with the same maps of sections are equal: the compatibility is a proof. -/
theorem FMap.ext_app {P : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type v}
    {Q : (SmallEtale B S hS Y.1)ᵒᵖ ⥤ Type w}
    {ξ η : FMap B S hS X.1 Y.1 f.hom P Q} (h : ξ.app = η.app) : ξ = η := by
  cases ξ
  cases η
  cases h
  rfl

/-- Two sections of a sheaf on the spaces-étale site of an algebraic space over an object étale
over it agree as soon as their restrictions to all étale scheme charts above that object agree.
This is `AlgebraicGeometry.Space.spacesEtale_section_ext` with the charts presented as arrows
out of the comparison functor of Stacks 03G1 rather than as objects of a structured-arrow
category. -/
theorem spacesEtale_section_ext_charts (Z : AlgebraicSpaces B S hS) (A : SpacesEtale B S hS Z)
    (Q : Sheaf (SpacesEtale.topology B S hS Z) (Type u)) {a b : Q.obj.obj (op A)}
    (h : ∀ (U : SmallEtale B S hS Z.1) (k : (comparisonFunctor B S hS Z).obj U ⟶ A),
      Q.obj.map k.op a = Q.obj.map k.op b) : a = b :=
  spacesEtale_section_ext B S hS Z A Q fun k ↦ h k.right.unop k.hom.unop

/-- Equal morphisms of sheaves of types have equal components on every section. -/
private theorem sheaf_hom_app_congr {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A A' : Sheaf J (Type u)} {φ ψ : A ⟶ A'} (h : φ = ψ) (U : Cᵒᵖ) (x : A.obj.obj U) :
    φ.hom.app U x = ψ.hom.app U x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun k ↦ k.hom) h) U) x

/-- The spaces-étale direct image along `f` followed by restriction to the étale scheme charts
of `Y`, at the universe of the structure rings: the functor through which the direct image of
`AlgebraicGeometry.Space.smallEtaleRingedToposHom` is computed, by
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforward`.  Precomposing it with the right
Kan extension along the comparison functor of Stacks 03G1 is
`AlgebraicGeometry.Space.smallEtaleDirectImageRan`. -/
noncomputable abbrev spacesDirectImageRestrictionTypeU :
    Sheaf (SpacesEtale.topology B S hS X) (Type u) ⥤
      Sheaf (SmallEtale.topology B S hS Y.1) (Type u) :=
  spacesDirectImage B S hS f ⋙ smallEtaleComparisonRestriction B S hS Y

/-! ### The section of a spaces-étale sheaf attached to an `f`-map -/

section Descend

variable (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
  (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
  (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
  (i : F ≅ (smallEtaleComparisonRestriction B S hS X).obj H)
  (ξ : FMap B S hS X.1 Y.1 f.hom F.obj G.obj)

/-- The cone on the diagram of sections over the étale scheme charts above `X ×_Y V` whose
component at a chart is the `f`-map applied to the diagram of charts that chart determines.
Its limit is the sections of the spaces-étale sheaf over `X ×_Y V`. -/
noncomputable def fMapSectionConeTypeU (V : SmallEtale B S hS Y.1) :
    Cone (StructuredArrow.proj (op (chartBaseChange B S hS f V))
      (comparisonFunctor B S hS X).op ⋙
        ((smallEtaleComparisonRestriction B S hS X).obj H).obj) where
  pt := G.obj.obj (op V)
  π :=
    { app := fun k ↦ TypeCat.ofHom (fun s ↦ i.hom.hom.app k.right
        (ξ.app (chartDiagramOfBaseChangeArrow B S hS f k.right.unop V k.hom.unop) s))
      naturality := by
        intro k k' m
        apply TypeCat.homEquiv.injective
        funext s
        have hw : (comparisonFunctor B S hS X).map m.right.unop ≫ k.hom.unop =
            k'.hom.unop := congrArg Quiver.Hom.unop m.w
        have hc := (chartDiagram_square_iff B S hS f k.hom.unop k'.hom.unop
          m.right.unop (𝟙 V)).mp (by
            refine hw.trans ((Category.comp_id _).symm.trans
              (congrArg (fun a ↦ k'.hom.unop ≫ a) ?_))
            exact ((congrArg ((spacesBaseChange B S hS f).functor.map)
              ((comparisonFunctor B S hS Y).map_id V)).trans
                ((spacesBaseChange B S hS f).functor.map_id
                  ((comparisonFunctor B S hS Y).obj V))).symm)
        have hξ := ξ.naturality
          (chartDiagramOfBaseChangeArrow B S hS f k.right.unop V k.hom.unop)
          (chartDiagramOfBaseChangeArrow B S hS f k'.right.unop V k'.hom.unop)
          m.right.unop (𝟙 V) hc s
        have hGid : G.obj.map (𝟙 V).op s = s :=
          ConcreteCategory.congr_hom (G.obj.map_id (op V)) s
        have hξ' : ξ.app
              (chartDiagramOfBaseChangeArrow B S hS f k'.right.unop V k'.hom.unop) s =
            F.obj.map m.right (ξ.app
              (chartDiagramOfBaseChangeArrow B S hS f k.right.unop V k.hom.unop) s) :=
          (congrArg (ξ.app
            (chartDiagramOfBaseChangeArrow B S hS f k'.right.unop V k'.hom.unop))
              hGid).symm.trans hξ
        have hη := ConcreteCategory.congr_hom (i.hom.hom.naturality m.right)
          (ξ.app (chartDiagramOfBaseChangeArrow B S hS f k.right.unop V k.hom.unop) s)
        change i.hom.hom.app k'.right (ξ.app
            (chartDiagramOfBaseChangeArrow B S hS f k'.right.unop V k'.hom.unop) s) =
          H.obj.map ((comparisonFunctor B S hS X).op.map m.right)
            (i.hom.hom.app k.right (ξ.app
              (chartDiagramOfBaseChangeArrow B S hS f k.right.unop V k.hom.unop) s))
        exact (congrArg (fun t ↦ i.hom.hom.app k'.right t) hξ').trans hη }

/-- The section of a spaces-étale sheaf over `X ×_Y V` attached by an `f`-map to a section over
the étale scheme chart `V` of `Y`: the compatible family of the chartwise images, read through
the limit description of the sections over `X ×_Y V`. -/
noncomputable def fMapDescendedSectionTypeU (V : SmallEtale B S hS Y.1) :
    G.obj.obj (op V) → H.obj.obj (op (chartBaseChange B S hS f V)) := fun s ↦
  (comparisonUnitIso B S hS X H).inv.hom.app (op (chartBaseChange B S hS f V))
    ((ranIsLimit B S hS X (chartBaseChange B S hS f V)
        ((smallEtaleComparisonRestriction B S hS X).obj H)).lift
      (fMapSectionConeTypeU B S hS f F G H i ξ V) s)

/-- The restriction of the descended section to an étale scheme chart `U` of `X` above
`X ×_Y V` is the `f`-map applied to the diagram of charts that arrow determines. -/
theorem descendedSectionTypeU_restrict (U : SmallEtale B S hS X.1)
    (V : SmallEtale B S hS Y.1)
    (k : (comparisonFunctor B S hS X).obj U ⟶ chartBaseChange B S hS f V)
    (s : G.obj.obj (op V)) :
    H.obj.map k.op (fMapDescendedSectionTypeU B S hS f F G H i ξ V s) =
      i.hom.hom.app (op U)
        (ξ.app (chartDiagramOfBaseChangeArrow B S hS f U V k) s) := by
  have hcone : (ranProj B S hS X (chartBaseChange B S hS f V)
        (StructuredArrow.mk k.op)).app ((smallEtaleComparisonRestriction B S hS X).obj H)
        ((ranIsLimit B S hS X (chartBaseChange B S hS f V)
          ((smallEtaleComparisonRestriction B S hS X).obj H)).lift
            (fMapSectionConeTypeU B S hS f F G H i ξ V) s) =
      i.hom.hom.app (op U)
        (ξ.app (chartDiagramOfBaseChangeArrow B S hS f U V k) s) := by
    rw [ranProj_app_apply]
    exact ConcreteCategory.congr_hom ((ranIsLimit B S hS X (chartBaseChange B S hS f V)
      ((smallEtaleComparisonRestriction B S hS X).obj H)).fac
        (fMapSectionConeTypeU B S hS f F G H i ξ V) (StructuredArrow.mk k.op)) s
  have hkey : ((comparisonAdjunction B S hS X).unit.app H).hom.app
        (op (chartBaseChange B S hS f V))
        (fMapDescendedSectionTypeU B S hS f F G H i ξ V s) =
      (ranIsLimit B S hS X (chartBaseChange B S hS f V)
        ((smallEtaleComparisonRestriction B S hS X).obj H)).lift
          (fMapSectionConeTypeU B S hS f F G H i ξ V) s := by
    rw [← comparisonUnitIso_hom]
    exact sheaf_hom_app_congr (comparisonUnitIso B S hS X H).inv_hom_id _ _
  refine (ranProj_unit_app B S hS X (chartBaseChange B S hS f V) H (StructuredArrow.mk k.op)
    (fMapDescendedSectionTypeU B S hS f F G H i ξ V s)).symm.trans ?_
  rw [hkey]
  exact hcone

/-- The descended sections are compatible with étale restriction of the chart of `Y`: they are
the components of a homomorphism of sheaves. -/
theorem descendedSectionTypeU_naturality {V V' : SmallEtale B S hS Y.1} (j : V' ⟶ V)
    (s : G.obj.obj (op V)) :
    fMapDescendedSectionTypeU B S hS f F G H i ξ V' (G.obj.map j.op s) =
      H.obj.map ((spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS Y).map j)).op
          (fMapDescendedSectionTypeU B S hS f F G H i ξ V s) := by
  refine spacesEtale_section_ext B S hS X (chartBaseChange B S hS f V') H (fun k ↦ ?_)
  have hc := (chartDiagram_square_iff B S hS f
    (k.hom.unop ≫ (spacesBaseChange B S hS f).functor.map
      ((comparisonFunctor B S hS Y).map j)) k.hom.unop (𝟙 k.right.unop) j).mp
    ((congrArg (fun a ↦ a ≫ k.hom.unop ≫ (spacesBaseChange B S hS f).functor.map
      ((comparisonFunctor B S hS Y).map j))
        ((comparisonFunctor B S hS X).map_id k.right.unop)).trans (Category.id_comp _))
  have hn := ξ.naturality
    (chartDiagramOfBaseChangeArrow B S hS f k.right.unop V
      (k.hom.unop ≫ (spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS Y).map j)))
    (chartDiagramOfBaseChangeArrow B S hS f k.right.unop V' k.hom.unop)
    (𝟙 k.right.unop) j hc s
  have hn' : ξ.app (chartDiagramOfBaseChangeArrow B S hS f k.right.unop V' k.hom.unop)
        (G.obj.map j.op s) =
      ξ.app (chartDiagramOfBaseChangeArrow B S hS f k.right.unop V
        (k.hom.unop ≫ (spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map j))) s :=
    hn.trans (ConcreteCategory.congr_hom (F.obj.map_id (op k.right.unop)) _)
  have hr : H.obj.map k.hom (H.obj.map ((spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS Y).map j)).op
          (fMapDescendedSectionTypeU B S hS f F G H i ξ V s)) =
      H.obj.map (k.hom.unop ≫ (spacesBaseChange B S hS f).functor.map
        ((comparisonFunctor B S hS Y).map j)).op
          (fMapDescendedSectionTypeU B S hS f F G H i ξ V s) := by
    simp
  rw [hr]
  exact (descendedSectionTypeU_restrict B S hS f F G H i ξ k.right.unop V' k.hom.unop
      (G.obj.map j.op s)).trans
    ((congrArg (fun x ↦ i.hom.hom.app (op k.right.unop) x) hn').trans
      (descendedSectionTypeU_restrict B S hS f F G H i ξ k.right.unop V
        (k.hom.unop ≫ (spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map j)) s).symm)

/-- The homomorphism of sheaves attached to an `f`-map: on sections over an étale scheme chart
`V` of `Y` it is `AlgebraicGeometry.Space.fMapDescendedSectionTypeU`. -/
noncomputable def descendedHomTypeU :
    G ⟶ (spacesDirectImageRestrictionTypeU B S hS f).obj H :=
  ⟨{ app := fun V ↦ TypeCat.ofHom (fMapDescendedSectionTypeU B S hS f F G H i ξ V.unop)
     naturality := by
       intro V V' j
       apply TypeCat.homEquiv.injective
       funext s
       exact descendedSectionTypeU_naturality B S hS f F G H i ξ j.unop s }⟩

end Descend

/-! ### The bijection, for a presented source sheaf -/

section Equiv

variable (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
  (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))
  (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
  (i : F ≅ (smallEtaleComparisonRestriction B S hS X).obj H)

/-- The `f`-map attached to a homomorphism of sheaves into the direct image: on a diagram of
étale scheme charts it is restriction of the section of the direct image along the arrow into
the cartesian base change that the diagram determines. -/
noncomputable def fMapOfPushforwardHomTypeU
    (ψ : G ⟶ (spacesDirectImageRestrictionTypeU B S hS f).obj H) :
    FMap B S hS X.1 Y.1 f.hom F.obj G.obj where
  app d s := i.inv.hom.app (op d.U)
    (H.obj.map (baseChangeArrowOfChartDiagram B S hS f d).op (ψ.hom.app (op d.V) s))
  naturality d d' a b hab s := by
    have hs := (chartDiagram_square_iff B S hS f
      (baseChangeArrowOfChartDiagram B S hS f d)
      (baseChangeArrowOfChartDiagram B S hS f d') a b).mpr (by
        rw [chartDiagramOfBaseChangeArrow_baseChangeArrow_g,
          chartDiagramOfBaseChangeArrow_baseChangeArrow_g]
        exact hab)
    have key : H.obj.map (baseChangeArrowOfChartDiagram B S hS f d').op
          (H.obj.map ((spacesBaseChange B S hS f).functor.map
            ((comparisonFunctor B S hS Y).map b)).op (ψ.hom.app (op d.V) s)) =
        H.obj.map ((comparisonFunctor B S hS X).map a).op
          (H.obj.map (baseChangeArrowOfChartDiagram B S hS f d).op
            (ψ.hom.app (op d.V) s)) := by
      refine (H.obj.map_comp_apply
        ((spacesBaseChange B S hS f).functor.map
          ((comparisonFunctor B S hS Y).map b)).op
        (baseChangeArrowOfChartDiagram B S hS f d').op
        (ψ.hom.app (op d.V) s)).symm.trans (Eq.trans ?_
          (H.obj.map_comp_apply (baseChangeArrowOfChartDiagram B S hS f d).op
            ((comparisonFunctor B S hS X).map a).op (ψ.hom.app (op d.V) s)))
      exact congrArg
        (fun k : (comparisonFunctor B S hS X).obj d'.U ⟶ chartBaseChange B S hS f d.V ↦
          H.obj.map k.op (ψ.hom.app (op d.V) s)) hs.symm
    change i.inv.hom.app (op d'.U)
      (H.obj.map (baseChangeArrowOfChartDiagram B S hS f d').op
        (ψ.hom.app (op d'.V) (G.obj.map b.op s))) =
      F.obj.map a.op (i.inv.hom.app (op d.U)
        (H.obj.map (baseChangeArrowOfChartDiagram B S hS f d).op
          (ψ.hom.app (op d.V) s)))
    rw [NatTrans.naturality_apply ψ.hom b.op s]
    refine Eq.trans (congrArg (fun y ↦ i.inv.hom.app (op d'.U) y) key) ?_
    exact NatTrans.naturality_apply i.inv.hom a.op _

/-- For a sheaf on the small étale site of `X` presented as the restriction of a spaces-étale
sheaf, the `f`-maps into it are the homomorphisms of sheaves into the direct image of that
spaces-étale sheaf. -/
noncomputable def descendedHomEquivTypeU :
    FMap B S hS X.1 Y.1 f.hom F.obj G.obj ≃
      (G ⟶ (spacesDirectImageRestrictionTypeU B S hS f).obj H) where
  toFun := descendedHomTypeU B S hS f F G H i
  invFun := fMapOfPushforwardHomTypeU B S hS f F G H i
  left_inv ξ := by
    refine FMap.ext_app B S hS f ?_
    funext d s
    change i.inv.hom.app (op d.U)
      (H.obj.map (baseChangeArrowOfChartDiagram B S hS f d).op
        (fMapDescendedSectionTypeU B S hS f F G H i ξ d.V s)) = _
    rw [descendedSectionTypeU_restrict]
    have hx : ξ.app (chartDiagramOfBaseChangeArrow B S hS f d.U d.V
        (baseChangeArrowOfChartDiagram B S hS f d)) s = ξ.app d s := by
      obtain ⟨U, V, g, hc⟩ := d
      exact FMap.app_congr B S hS f ξ
        (chartDiagramOfBaseChangeArrow_baseChangeArrow_g B S hS f ⟨U, V, g, hc⟩) s
    rw [hx]
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun k ↦ k.hom) i.hom_inv_id) (op d.U)) (ξ.app d s)
  right_inv ψ := by
    apply Sheaf.hom_ext
    ext V s
    obtain ⟨V⟩ := V
    refine spacesEtale_section_ext_charts B S hS X (chartBaseChange B S hS f V) H
      (fun U k ↦ ?_)
    change H.obj.map k.op
      (fMapDescendedSectionTypeU B S hS f F G H i
        (fMapOfPushforwardHomTypeU B S hS f F G H i ψ) V s) =
      H.obj.map k.op (ψ.hom.app (op V) s)
    refine (descendedSectionTypeU_restrict B S hS f F G H i
      (fMapOfPushforwardHomTypeU B S hS f F G H i ψ) U V k s).trans ?_
    change i.hom.hom.app (op U)
      (i.inv.hom.app (op U)
        (H.obj.map (baseChangeArrowOfChartDiagram B S hS f
          (chartDiagramOfBaseChangeArrow B S hS f U V k)).op
            (ψ.hom.app (op V) s))) = _
    rw [baseChangeArrowOfChartDiagram_chartDiagram]
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun k ↦ k.hom) i.inv_hom_id) (op U)) _

/-- The homomorphism attached to an `f`-map does not depend on the chosen presentation of the
source sheaf: a homomorphism of spaces-étale sheaves compatible with two presentations carries
one descended homomorphism to the other. -/
theorem descendedHomTypeU_map (ξ : FMap B S hS X.1 Y.1 f.hom F.obj G.obj)
    (H' : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (i' : F ≅ (smallEtaleComparisonRestriction B S hS X).obj H')
    (α : H ⟶ H')
    (hα : (smallEtaleComparisonRestriction B S hS X).map α = i.inv ≫ i'.hom) :
    descendedHomTypeU B S hS f F G H i ξ ≫
        (spacesDirectImageRestrictionTypeU B S hS f).map α =
      descendedHomTypeU B S hS f F G H' i' ξ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply TypeCat.homEquiv.injective
  funext s
  obtain ⟨V⟩ := V
  refine spacesEtale_section_ext_charts B S hS X (chartBaseChange B S hS f V) H'
    (fun U k ↦ ?_)
  change H'.obj.map k.op
    (α.hom.app _ (fMapDescendedSectionTypeU B S hS f F G H i ξ V s)) =
      H'.obj.map k.op (fMapDescendedSectionTypeU B S hS f F G H' i' ξ V s)
  rw [← NatTrans.naturality_apply α.hom k.op
    (fMapDescendedSectionTypeU B S hS f F G H i ξ V s)]
  refine (congrArg (fun t ↦ α.hom.app (op ((comparisonFunctor B S hS X).obj U)) t)
    (descendedSectionTypeU_restrict B S hS f F G H i ξ U V k s)).trans ?_
  refine Eq.trans ?_ (descendedSectionTypeU_restrict B S hS f F G H' i' ξ U V k s).symm
  have he : i.hom ≫ (smallEtaleComparisonRestriction B S hS X).map α = i'.hom := by
    rw [hα]
    simp
  exact sheaf_hom_app_congr he _ _

end Equiv

/-! ### The chart correspondence -/

section Main

variable (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
  (G : Sheaf (SmallEtale.topology B S hS Y.1) (Type u))

/-- **Stacks 03G8, the chart correspondence.** A map on sections over every commutative
diagram of étale scheme charts over `f` is equivalently a homomorphism of sheaves into the
direct image of the morphism of small étale ringed topoi.  This is the bijection out of which
the structure map of `AlgebraicGeometry.Space.smallEtaleRingedToposHom` is read off; that it
is the canonical one is
`AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse_chart`. -/
noncomputable def fMapEquivPushforwardHom_ringUniverse :
    FMap B S hS X.1 Y.1 f.hom F.obj G.obj ≃
      (G ⟶ (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F) :=
  (descendedHomEquivTypeU B S hS f F G
      ((smallEtaleComparisonRestriction B S hS X).objPreimage F)
      ((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F).symm).trans
    ((Iso.refl G).homCongr
      ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.mapIso
          ((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F).symm ≪≫
        (smallEtaleRingedToposHom_pushforward B S hS f).app
          ((smallEtaleComparisonRestriction B S hS X).objPreimage F)).symm)

/-- The homomorphism attached to an `f`-map by the chart correspondence is, after the geometric
comparison of Stacks 03G2, part (3) at any presentation of the source sheaf, the descended
homomorphism `AlgebraicGeometry.Space.descendedHomTypeU`.  This is independence of the
presentation chosen in `AlgebraicGeometry.Space.fMapEquivPushforwardHom_ringUniverse`, by
`AlgebraicGeometry.Space.descendedHomTypeU_map`. -/
theorem fMapEquivPushforwardHom_ringUniverse_comparison
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type u))
    (i : F ≅ (smallEtaleComparisonRestriction B S hS X).obj H)
    (ξ : FMap B S hS X.1 Y.1 f.hom F.obj G.obj) :
    fMapEquivPushforwardHom_ringUniverse B S hS f F G ξ ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i.hom ≫
        (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H =
      descendedHomTypeU B S hS f F G H i ξ := by
  set α := (smallEtaleComparisonRestriction B S hS X).preimage
    (((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F).symm.inv ≫ i.hom)
  have hα : (smallEtaleComparisonRestriction B S hS X).map α =
      ((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F).symm.inv ≫ i.hom :=
    (smallEtaleComparisonRestriction B S hS X).map_preimage _
  have hnat : (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
          ((smallEtaleComparisonRestriction B S hS X).map α) ≫
        (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H =
      (smallEtaleRingedToposHom_pushforward B S hS f).hom.app
          ((smallEtaleComparisonRestriction B S hS X).objPreimage F) ≫
        (spacesDirectImageRestrictionTypeU B S hS f).map α :=
    (smallEtaleRingedToposHom_pushforward B S hS f).hom.naturality _
  change (𝟙 G ≫ descendedHomTypeU B S hS f F G
        ((smallEtaleComparisonRestriction B S hS X).objPreimage F)
        ((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F).symm ξ ≫
      ((smallEtaleRingedToposHom_pushforward B S hS f).inv.app
          ((smallEtaleComparisonRestriction B S hS X).objPreimage F) ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
          ((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F).symm.inv)) ≫
    (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i.hom ≫
      (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H = _
  simp only [Category.id_comp]
  calc _ = descendedHomTypeU B S hS f F G
            ((smallEtaleComparisonRestriction B S hS X).objPreimage F)
            ((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F).symm ξ ≫
          (smallEtaleRingedToposHom_pushforward B S hS f).inv.app
            ((smallEtaleComparisonRestriction B S hS X).objPreimage F) ≫
          (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
            ((smallEtaleComparisonRestriction B S hS X).map α) ≫
          (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H := by
        rw [hα, CategoryTheory.Functor.map_comp]
        simp only [Category.assoc]
    _ = descendedHomTypeU B S hS f F G
            ((smallEtaleComparisonRestriction B S hS X).objPreimage F)
            ((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F).symm ξ ≫
          (spacesDirectImageRestrictionTypeU B S hS f).map α := by
        rw [hnat]
        simp
    _ = _ := descendedHomTypeU_map B S hS f F G
        ((smallEtaleComparisonRestriction B S hS X).objPreimage F)
        ((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso F).symm ξ H i _ hα

/-- **Stacks 03G8.** The chart correspondence is the canonical one.  Transport a sheaf `F` on
the small étale site of `X` through an isomorphism with the restriction of a spaces-étale sheaf
`H`; then on a diagram `d` of étale scheme charts over `f` the transported `f`-map is
restriction of the section of the direct image along any arrow from the chart of `X` into the
cartesian base change of the chart of `Y` whose composite with the cartesian projection is the
Yoneda morphism of the vertical morphism of `d`. -/
theorem fMapEquivPushforwardHom_ringUniverse_chart :
    IsChartCorrespondence B S hS f F G
      (fMapEquivPushforwardHom_ringUniverse B S hS f F G) := by
  intro H i ξ d h hh s
  dsimp only
  change i.hom.hom.app (op d.U) (ξ.app d s) = H.obj.map h.op
    ((fMapEquivPushforwardHom_ringUniverse B S hS f F G ξ ≫
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map i.hom ≫
      (smallEtaleRingedToposHom_pushforward B S hS f).hom.app H).hom.app (op d.V) s)
  rw [fMapEquivPushforwardHom_ringUniverse_comparison]
  change i.hom.hom.app (op d.U) (ξ.app d s) = H.obj.map h.op
    (fMapDescendedSectionTypeU B S hS f F G H i ξ d.V s)
  rw [descendedSectionTypeU_restrict]
  congr 1
  obtain ⟨U, V, g, hc⟩ := d
  exact (FMap.app_congr B S hS f ξ
    (chartDiagramOfBaseChangeArrow_g_eq B S hS f ⟨U, V, g, hc⟩ h (eq_of_heq hh)) s).symm

/-- **Stacks 03G8.** Existence of the sectionwise characterized chart correspondence at the
universe of the structure rings, in the form the construction of the structure map of a
morphism of small étale ringed topoi consumes. -/
theorem exists_fMapEquivPushforwardHom_ringUniverse :
    ∃ e : FMap B S hS X.1 Y.1 f.hom F.obj G.obj ≃
      (G ⟶ (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.obj F),
      IsChartCorrespondence B S hS f F G e :=
  ⟨fMapEquivPushforwardHom_ringUniverse B S hS f F G,
    fMapEquivPushforwardHom_ringUniverse_chart B S hS f F G⟩

end Main

end AlgebraicGeometry.Space

end
