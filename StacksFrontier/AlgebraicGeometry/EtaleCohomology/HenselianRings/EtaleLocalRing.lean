module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.HenselizationTower
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf
public import StacksFrontier.RingTheory.Henselian.StrictHenselizationColimit
public import StacksFrontier.RingTheory.Henselian.EtaleLifting
import StacksFrontier.Cotangent.Henselization
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
import all StacksFrontier.RingTheory.Henselian.StrictHenselizationColimit

/-!
# The étale local ring at a geometric point

The stalk of the structure sheaf on the small étale site at a geometric point
is the strict henselization of the ordinary local ring at its image.

## Main definitions

* `AlgebraicGeometry.structureSheafStalkFromLocalRing` and
  `AlgebraicGeometry.structureSheafStalkToGeometricField` are the canonical maps on
  the ring-valued stalk of the structure sheaf.
* `AlgebraicGeometry.zariskiNeighborhood` and `AlgebraicGeometry.zariskiNeighborhoodMap` read
  an ordinary open neighborhood of the image point, and an inclusion between two of them, as an
  étale neighborhood of the geometric point and a morphism of such.

## Main results

* `AlgebraicGeometry.structureSheafStalkFromLocalRing_germ` characterizes the map from
  the ordinary local ring on germs of sections.
* `AlgebraicGeometry.structureSheafStalkToGeometricField_ι` characterizes evaluation
  on every étale neighborhood.
* `AlgebraicGeometry.etaleLocalRing_strictHenselization_canonical` is the comparison
  of the structure-sheaf stalk with the strict henselization formed using the
  relative separable closure inside the geometric point's field.
* `AlgebraicGeometry.etaleLocalRing_strictHenselization_unique` expresses its
  uniqueness among comparisons with the same geometric maps.

## Implementation notes

The comparison and both canonical maps are stated directly for the ring-valued
stalk of the structure sheaf of Tag 04HS. The germ and evaluation compatibility
lemmas specify the two maps; the comparison respects both of them, and the
uniqueness lemma expresses its canonicity.
The separable closure is the relative separable closure *inside* the geometric
point's field, rather than an abstract copy thereof.

## References

* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

open scoped TensorProduct

namespace AlgebraicGeometry

/-- An open neighborhood of the image of a geometric point, regarded as an étale
neighborhood inside the chosen site. -/
public noncomputable def zariskiNeighborhood
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (x : S) (hx : s.hom (closedPoint s.residueField) = x)
    (U : TopologicalSpace.OpenNhds x) :
    (geometricPointFiber B S hS s).Elements := by
  let hU : B.Contains (Scheme.Opens.toScheme (X := S) U.1) :=
    (Scheme.size_le_of_mono_locallyOfFinitePresentation
      (Scheme.Opens.ι (X := S) U.1)).trans_lt hS
  let V : SmallEtale B S hS :=
    ⟨Over.mk (ObjectProperty.homMk (Scheme.Opens.ι (X := S) U.1) :
      B.obj (Scheme.Opens.toScheme (X := S) U.1) hU ⟶ B.obj S hS), by
        change Etale (Scheme.Opens.ι (X := S) U.1)
        infer_instance⟩
  let p : s.source ⟶ Scheme.Opens.toScheme (X := S) U.1 :=
    IsOpenImmersion.lift (Scheme.Opens.ι (X := S) U.1) s.hom (by
    rintro _ ⟨a, rfl⟩
    obtain rfl : a = closedPoint s.residueField := Subsingleton.elim _ _
    change s.hom (closedPoint s.residueField) ∈
      Set.range (Scheme.Opens.ι (X := S) U.1).base
    exact ⟨⟨x, U.2⟩, hx.symm⟩)
  refine (geometricPointFiber B S hS s).elementsMk V ⟨p, ?_⟩
  change p ≫ Scheme.Opens.ι (X := S) U.1 = s.hom
  exact IsOpenImmersion.lift_fac (Scheme.Opens.ι (X := S) U.1) s.hom _

/-- Shrinking an open neighborhood of the image of a geometric point is a morphism of
étale neighborhoods. -/
public noncomputable def zariskiNeighborhoodMap
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (x : S) (hx : s.hom (closedPoint s.residueField) = x)
    {U V : TopologicalSpace.OpenNhds x} (i : U ⟶ V) :
    zariskiNeighborhood B S hS s x hx U ⟶ zariskiNeighborhood B S hS s x hx V := by
  have hle : U.1 ≤ V.1 := (TopologicalSpace.OpenNhds.le_def U V).mp i.le
  let f : Scheme.Opens.toScheme (X := S) U.1 ⟶ Scheme.Opens.toScheme (X := S) V.1 :=
    S.homOfLE hle
  have hf : f ≫ Scheme.Opens.ι (X := S) V.1 = Scheme.Opens.ι (X := S) U.1 :=
    Scheme.homOfLE_ι S hle
  let fOver : (zariskiNeighborhood B S hS s x hx U).fst.obj ⟶
      (zariskiNeighborhood B S hS s x hx V).fst.obj :=
    Over.homMk (ObjectProperty.homMk f) (ObjectProperty.hom_ext _ hf)
  let fSmall := ObjectProperty.homMk fOver
  refine Functor.Elements.homMk fSmall ?_
  dsimp [geometricPointFiber, zariskiNeighborhood]
  apply Subtype.ext
  change (IsOpenImmersion.lift (Scheme.Opens.ι (X := S) U.1) s.hom _ ≫ f) =
    IsOpenImmersion.lift (Scheme.Opens.ι (X := S) V.1) s.hom _
  apply (cancel_mono (Scheme.Opens.ι (X := S) V.1)).1
  rw [Category.assoc, hf, IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac]

/-- Restriction of sections commutes with the identification of sections over an open
subscheme with sections of the ambient scheme. -/
public theorem opens_topIso_homOfLE (S : Scheme.{u})
    {U V : S.Opens} (h : V ≤ U) :
    S.presheaf.map (homOfLE h).op ≫ V.topIso.inv =
      U.topIso.inv ≫ (S.homOfLE h).appTop := by
  have hn := (Scheme.restrictFunctorΓ (X := S)).hom.naturality (homOfLE h).op
  change (S.homOfLE h).appTop ≫ V.topIso.hom =
    U.topIso.hom ≫ S.presheaf.map (homOfLE h).op at hn
  rw [Iso.comp_inv_eq, Category.assoc, hn, Iso.inv_hom_id_assoc]

/-- The cocone of étale germs of Zariski sections, over the diagram of ordinary open
neighborhoods of the image of a geometric point. -/
public noncomputable def zariskiGermCocone
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) :
    Cocone (((TopologicalSpace.OpenNhds.inclusion
      (s.hom (closedPoint s.residueField))).op ⋙ S.presheaf) ⋙
        forget₂ CommRingCat RingCat) := by
  let x := s.hom (closedPoint s.residueField)
  let G := geometricPointFiber B S hS s
  let F := (Functor.Elements.π G).op ⋙
    (SmallEtale.structureSheaf B S hS).obj
  let Q := forget₂ CommRingCat RingCat
  let D := ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ S.presheaf) ⋙ Q
  let stage : TopologicalSpace.OpenNhds x → G.Elements := fun V =>
    zariskiNeighborhood B S hS s x rfl V
  let stageMap : {V W : TopologicalSpace.OpenNhds x} → (i : V ⟶ W) →
      stage V ⟶ stage W := fun {V W} i =>
    zariskiNeighborhoodMap B S hS s x rfl i
  let eStage (V : TopologicalSpace.OpenNhds x) :
      D.obj (Opposite.op V) ≅ F.obj (Opposite.op (stage V)) :=
    (Q.mapIso (Scheme.Opens.topIso (X := S) V.1)).symm
  exact {
    pt := etaleStalk B S hS s
      (SmallEtale.structureSheaf B S hS).obj
    ι := {
      app := fun V => (eStage (unop V)).hom ≫
        colimit.ι F (Opposite.op (stage (unop V)))
      naturality := by
        intro V W f
        let i : (unop W) ⟶ (unop V) := f.unop
        have hle := (TopologicalSpace.OpenNhds.le_def (unop W) (unop V)).mp i.le
        have hFmap : F.map (Opposite.op (stageMap i)) =
            Q.map ((S.homOfLE hle).appTop) := by
          dsimp [F, G, SmallEtale.structureSheaf_obj,
            Stacks.Sites.structurePresheaf, stageMap, zariskiNeighborhoodMap]
          rfl
        have hnat : D.map f ≫ (eStage (unop W)).hom =
            (eStage (unop V)).hom ≫ F.map (Opposite.op (stageMap i)) := by
          change Q.map (S.presheaf.map (homOfLE hle).op) ≫
              Q.map ((Scheme.Opens.topIso (X := S) (unop W).1).inv) =
            Q.map ((Scheme.Opens.topIso (X := S) (unop V).1).inv) ≫
              F.map (Opposite.op (stageMap i))
          rw [hFmap]
          exact congrArg Q.map (opens_topIso_homOfLE S hle)
        calc
          D.map f ≫ ((eStage (unop W)).hom ≫
              colimit.ι F (Opposite.op (stage (unop W)))) =
              ((eStage (unop V)).hom ≫ F.map (Opposite.op (stageMap i))) ≫
                colimit.ι F (Opposite.op (stage (unop W))) := by
              rw [← Category.assoc, hnat]
              rfl
          _ = (eStage (unop V)).hom ≫
              (F.map (Opposite.op (stageMap i)) ≫
                colimit.ι F (Opposite.op (stage (unop W)))) := Category.assoc _ _ _
          _ = (eStage (unop V)).hom ≫
              colimit.ι F (Opposite.op (stage (unop V))) :=
            congrArg ((eStage (unop V)).hom ≫ ·) (colimit.w F (Opposite.op (stageMap i)))
    }
  }

/-- The canonical map from the ordinary local ring to the stalk of the
ring-valued étale structure sheaf. -/
@[stacks 04HX "the ordinary-to-étale germ map"]
public noncomputable def structureSheafStalkFromLocalRing
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) :
    S.presheaf.stalk (s.hom (closedPoint s.residueField)) →+*
      ↥(etaleStalk B S hS s
        (SmallEtale.structureSheaf B S hS).obj) := by
  let D₀ := (TopologicalSpace.OpenNhds.inclusion
    (s.hom (closedPoint s.residueField))).op ⋙ S.presheaf
  let Q := forget₂ CommRingCat RingCat
  change ↑(Q.obj (S.presheaf.stalk (s.hom (closedPoint s.residueField)))) →+*
    ↑(etaleStalk B S hS s (SmallEtale.structureSheaf B S hS).obj)
  exact ((isColimitOfPreserves Q (colimit.isColimit D₀)).desc
    (zariskiGermCocone B S hS s)).hom

/-- The canonical map from the ordinary local ring sends the germ of a section over a
Zariski open to its class in the étale stalk. -/
private theorem structureSheafStalkFromLocalRing_open_germ
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) (U : S.Opens)
    (hx : s.hom (closedPoint s.residueField) ∈ U)
    (a : Γ(S, U)) :
    structureSheafStalkFromLocalRing B S hS s
      (S.presheaf.germ U (s.hom (closedPoint s.residueField)) hx a) =
        (colimit.ι
          ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
            (SmallEtale.structureSheaf B S hS).obj)
          (Opposite.op (zariskiNeighborhood B S hS s
            (s.hom (closedPoint s.residueField)) rfl ⟨U, hx⟩))).hom
          ((Scheme.Opens.topIso (X := S) U).inv a) := by
  let D₀ := (TopologicalSpace.OpenNhds.inclusion
    (s.hom (closedPoint s.residueField))).op ⋙ S.presheaf
  let Q := forget₂ CommRingCat RingCat
  let c := zariskiGermCocone B S hS s
  let hc := isColimitOfPreserves Q (colimit.isColimit D₀)
  change (hc.desc c).hom ((Q.map
    (colimit.ι D₀ (Opposite.op ⟨U, hx⟩))).hom a) =
      (c.ι.app (Opposite.op ⟨U, hx⟩)).hom a
  exact ConcreteCategory.congr_hom (hc.fac c (Opposite.op ⟨U, hx⟩)) a

/-- The cocone of values at the chosen geometric lifts, over the diagram of étale
neighborhoods of a geometric point. -/
public noncomputable def geometricFieldCocone
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) :
    Cocone ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
      (SmallEtale.structureSheaf B S hS).obj) where
  pt := RingCat.of s.residueField
  ι := {
    app := fun U => RingCat.ofHom
      (((U.unop.2.1).appTop ≫ (Scheme.ΓSpecIso (.of s.residueField)).hom).hom)
    naturality := by
      intro U V f
      dsimp [SmallEtale.structureSheaf_obj,
        Stacks.Sites.structurePresheaf, Functor.Elements.π]
      apply RingCat.hom_ext
      ext a
      let g : (SmallEtale.toScheme B S hS).obj V.unop.1 ⟶
          (SmallEtale.toScheme B S hS).obj U.unop.1 :=
        Over.Hom.left ((Over.post B.inclusion).map f.unop.1.hom)
      change (Scheme.ΓSpecIso (.of s.residueField)).hom.hom
          ((g.appTop ≫ (V.unop.2.1).appTop) a) =
        (Scheme.ΓSpecIso (.of s.residueField)).hom.hom ((U.unop.2.1).appTop a)
      have hp : V.unop.2.1 ≫ g = U.unop.2.1 := by
        simpa [geometricPointFiber, g] using congrArg Subtype.val f.unop.2
      rw [← Scheme.Hom.comp_appTop, hp] }

/-- Evaluation of a structure-sheaf stalk germ in the geometric residue field. -/
@[stacks 04HX "the geometric evaluation map"]
public noncomputable def structureSheafStalkToGeometricField
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S) :
    ↥(etaleStalk B S hS s
      (SmallEtale.structureSheaf B S hS).obj) →+* s.residueField :=
  (colimit.desc _ (geometricFieldCocone B S hS s)).hom

/-- The canonical algebra structure on the field of a geometric point. -/
public noncomputable instance geometricResidueAlgebra
    (S : Scheme.{u}) (s : GeometricPoint S) :
    Algebra (ResidueField (S.presheaf.stalk (s.hom (closedPoint s.residueField))))
      s.residueField :=
  (S.descResidueField (Scheme.stalkClosedPointTo s.hom)).hom.toAlgebra

/-- A morphism of étale neighborhoods from a morphism of the underlying schemes over `S`
compatible with the chosen lifts. -/
private def neighborhoodHom
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (U V : (geometricPointFiber B S hS s).Elements)
    (f : (SmallEtale.toScheme B S hS).obj U.1 ⟶
      (SmallEtale.toScheme B S hS).obj V.1)
    (hf : f ≫ B.inclusion.map V.1.obj.hom = B.inclusion.map U.1.obj.hom)
    (hp : U.2.1 ≫ f = V.2.1) : U ⟶ V :=
  ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk f) (ObjectProperty.hom_ext _ hf)),
    Subtype.ext hp⟩

/-- Morphisms of étale neighborhoods are equal when their underlying scheme maps are. -/
private lemma neighborhoodHom_ext
    {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {s : GeometricPoint S}
    {U V : (geometricPointFiber B S hS s).Elements} {f g : U ⟶ V}
    (h : (SmallEtale.toScheme B S hS).map f.1 = (SmallEtale.toScheme B S hS).map g.1) :
    f = g := by
  apply Functor.Elements.hom_ext
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact h

/-- Germs along a morphism of étale neighborhoods agree. -/
private lemma colimit_ι_neighborhoodHom
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (U V : (geometricPointFiber B S hS s).Elements)
    (f : (SmallEtale.toScheme B S hS).obj U.1 ⟶
      (SmallEtale.toScheme B S hS).obj V.1)
    (hf : f ≫ B.inclusion.map V.1.obj.hom = B.inclusion.map U.1.obj.hom)
    (hp : U.2.1 ≫ f = V.2.1)
    (a : Γ((SmallEtale.toScheme B S hS).obj V.1, ⊤)) :
    (colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
      (SmallEtale.structureSheaf B S hS).obj) (op U)).hom (f.appTop a) =
    (colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
      (SmallEtale.structureSheaf B S hS).obj) (op V)).hom a :=
  ConcreteCategory.congr_hom
    (colimit.w ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
      (SmallEtale.structureSheaf B S hS).obj)
      (neighborhoodHom B S hS s U V f hf hp).op) a

/-- An open subscheme of an étale neighborhood containing the chosen lift, as an étale
neighborhood. -/
private def openNeighborhood
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (U : (geometricPointFiber B S hS s).Elements)
    (W : ((SmallEtale.toScheme B S hS).obj U.1).Opens)
    (hx : U.2.1 (closedPoint s.residueField) ∈ W) :
    (geometricPointFiber B S hS s).Elements := by
  let f := B.inclusion.map U.1.obj.hom
  have : Etale f := U.1.property
  have hW : B.Contains W.toScheme :=
    (Scheme.size_le_of_mono_locallyOfFinitePresentation W.ι).trans_lt U.1.obj.left.property
  let q := IsOpenImmersion.lift W.ι U.2.1 (by
    rintro _ ⟨a, rfl⟩
    obtain rfl : a = closedPoint s.residueField := Subsingleton.elim _ _
    exact ⟨⟨_, hx⟩, rfl⟩)
  exact (geometricPointFiber B S hS s).elementsMk ⟨Over.mk (ObjectProperty.homMk (W.ι ≫ f) :
    B.obj W.toScheme hW ⟶ B.obj S hS), by
      change Etale (W.ι ≫ f)
      infer_instance⟩
    ⟨q, (Category.assoc q W.ι f).symm.trans
      ((congrArg (fun z => z ≫ f) (IsOpenImmersion.lift_fac W.ι U.2.1 _)).trans U.2.2)⟩

/-- The lift chosen on an open subneighborhood is the given one. -/
private lemma openNeighborhood_point
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (U : (geometricPointFiber B S hS s).Elements)
    (W : ((SmallEtale.toScheme B S hS).obj U.1).Opens)
    (hx : U.2.1 (closedPoint s.residueField) ∈ W) :
    (openNeighborhood B S hS s U W hx).2.1 ≫ W.ι = U.2.1 := by
  change IsOpenImmersion.lift W.ι U.2.1 _ ≫ W.ι = U.2.1
  exact IsOpenImmersion.lift_fac W.ι U.2.1 _

/-- Sections along an open immersion of an open subscheme are restriction followed by the
identification of its global sections. -/
private lemma opens_ι_appTop (Y : Scheme.{u}) (W : Y.Opens) :
    W.ι.appTop = Y.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op ≫
      W.topIso.inv := by
  change Y.presheaf.map _ = Y.presheaf.map _ ≫ Y.presheaf.map _
  exact (congrArg Y.presheaf.map (Subsingleton.elim _ _)).trans (Y.presheaf.map_comp _ _)

/-- The base change of an open affine of the base along an étale augmented algebra, as an
étale neighborhood. -/
private def augmentedNeighborhood
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (A : Type u) [CommRing A] [Algebra A s.residueField]
    (j : Spec (.of A) ⟶ S) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap A s.residueField)) ≫ j = s.hom)
    (C : CommAlgCat.AugmentedEtale A s.residueField) :
    (geometricPointFiber B S hS s).Elements := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A C.left.obj)) ≫ j
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap A C.left.obj))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact (RingHom.etale_algebraMap).mpr inferInstance
  have hC : B.Contains (Spec (.of C.left.obj)) :=
    (Scheme.size_le_of_locallyOfFiniteType f).trans_lt hS
  refine (geometricPointFiber B S hS s).elementsMk ⟨Over.mk (ObjectProperty.homMk f :
    B.obj (Spec (.of C.left.obj)) hC ⟶ B.obj S hS), by
      change Etale f
      infer_instance⟩
    ⟨Spec.map (CommRingCat.ofHom C.hom.hom.toRingHom), ?_⟩
  change Spec.map (CommRingCat.ofHom C.hom.hom.toRingHom) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap A C.left.obj)) ≫ j) = s.hom
  rw [← Category.assoc, ← Spec.map_comp]
  convert hj using 2
  exact congrArg Spec.map (CommRingCat.hom_ext C.hom.hom.comp_algebraMap)

/-- The diagram of étale neighborhoods indexed by augmented étale algebras over an open
affine of the base. -/
private def augmentedNeighborhoodFunctor
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (A : Type u) [CommRing A] [Algebra A s.residueField]
    (j : Spec (.of A) ⟶ S) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap A s.residueField)) ≫ j = s.hom) :
    (CommAlgCat.AugmentedEtale A s.residueField)ᵒᵖ ⥤
      (geometricPointFiber B S hS s).Elements where
  obj C := augmentedNeighborhood B S hS s A j hj C.unop
  map {C D} f := neighborhoodHom B S hS s _ _
    (Spec.map (CommRingCat.ofHom (CommAlgCat.AugmentedEtale.map f.unop).toRingHom))
    (by
      change Spec.map _ ≫ (Spec.map _ ≫ j) = Spec.map _ ≫ j
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      exact CommRingCat.hom_ext (CommAlgCat.AugmentedEtale.map f.unop).comp_algebraMap)
    (by
      change Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]
      apply congrArg Spec.map
      ext x
      exact CommAlgCat.AugmentedEtale.hom_map f.unop x)
  map_id C := by
    apply neighborhoodHom_ext
    simp only [neighborhoodHom]
    exact Spec.map_id _
  map_comp f g := by
    apply neighborhoodHom_ext
    change Spec.map (CommRingCat.ofHom
      (CommAlgCat.AugmentedEtale.map (g.unop ≫ f.unop)).toRingHom) =
      Spec.map (CommRingCat.ofHom (CommAlgCat.AugmentedEtale.map f.unop).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (CommAlgCat.AugmentedEtale.map g.unop).toRingHom)
    rw [CommAlgCat.AugmentedEtale.map_comp, ← Spec.map_comp]
    congr 1

/-- The diagram of augmented étale neighborhoods is full. -/
private theorem augmentedNeighborhoodFunctor_full
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (A : Type u) [CommRing A] [Algebra A s.residueField]
    (j : Spec (.of A) ⟶ S) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap A s.residueField)) ≫ j = s.hom) :
    (augmentedNeighborhoodFunctor B S hS s A j hj).Full where
  map_surjective {C D} f := by
    let ff : Spec (.of C.unop.left.obj) ⟶ Spec (.of D.unop.left.obj) :=
      (SmallEtale.toScheme B S hS).map f.1
    have hf : ff ≫ Spec.map (CommRingCat.ofHom (algebraMap A D.unop.left.obj)) =
        Spec.map (CommRingCat.ofHom (algebraMap A C.unop.left.obj)) :=
      (cancel_mono j).1 <| (Category.assoc _ _ j).trans
        ((B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w f.1.hom)))
    let g : D.unop.left.obj →ₐ[A] C.unop.left.obj :=
      { toRingHom := (Spec.preimage ff).hom
        commutes' := fun a => by
          have h := congrArg Spec.preimage hf
          simp only [Spec.preimage_comp, Spec.preimage_map] at h
          exact ConcreteCategory.congr_hom h a }
    have hg : Spec.map (CommRingCat.ofHom g.toRingHom) = ff := Spec.map_preimage ff
    have hp : Spec.map (CommRingCat.ofHom C.unop.hom.hom.toRingHom) ≫ ff =
        Spec.map (CommRingCat.ofHom D.unop.hom.hom.toRingHom) :=
      congrArg Subtype.val f.2
    let t : D.unop ⟶ C.unop := CostructuredArrow.homMk
      (ObjectProperty.homMk (CommAlgCat.ofHom g)) (by
        have he : CommRingCat.ofHom g.toRingHom ≫
            CommRingCat.ofHom C.unop.hom.hom.toRingHom =
            CommRingCat.ofHom D.unop.hom.hom.toRingHom :=
          Spec.map_injective (by rwa [Spec.map_comp, hg])
        ext x
        exact ConcreteCategory.congr_hom he x)
    refine ⟨t.op, ?_⟩
    apply neighborhoodHom_ext
    exact hg

/-- The diagram of augmented étale neighborhoods is faithful. -/
private theorem augmentedNeighborhoodFunctor_faithful
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (A : Type u) [CommRing A] [Algebra A s.residueField]
    (j : Spec (.of A) ⟶ S) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap A s.residueField)) ≫ j = s.hom) :
    (augmentedNeighborhoodFunctor B S hS s A j hj).Faithful where
  map_injective {C D} f g h := by
    have he := congrArg (fun k => (SmallEtale.toScheme B S hS).map k.1) h
    have he' : CommAlgCat.AugmentedEtale.map f.unop =
        CommAlgCat.AugmentedEtale.map g.unop :=
      AlgHom.coe_ringHom_injective (CommRingCat.hom_ext_iff.mp (Spec.map_injective he))
    apply Quiver.Hom.unop_inj
    apply CostructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    exact CommAlgCat.hom_ext he'

/-- Every étale neighborhood is refined by one of the augmented étale neighborhoods. -/
private lemma exists_augmentedNeighborhood_refinement
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (A : Type u) [CommRing A] [Algebra A s.residueField]
    (j : Spec (.of A) ⟶ S) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap A s.residueField)) ≫ j = s.hom)
    (U : (geometricPointFiber B S hS s).Elements) :
    ∃ C, Nonempty ((augmentedNeighborhoodFunctor B S hS s A j hj).obj C ⟶ U) := by
  let Y := (SmallEtale.toScheme B S hS).obj U.1
  let f : Y ⟶ S := B.inclusion.map U.1.obj.hom
  have : Etale f := U.1.property
  let p : s.source ⟶ Y := U.2.1
  let x := p (closedPoint s.residueField)
  have hx : x ∈ f ⁻¹ᵁ j.opensRange := by
    change f x ∈ Set.range j
    refine ⟨Spec.map (CommRingCat.ofHom (algebraMap A s.residueField))
      (closedPoint s.residueField), ?_⟩
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans
      ((congrArg (fun q : s.source ⟶ S => q (closedPoint s.residueField))
        (hj.trans U.2.2.symm)).trans (Scheme.Hom.comp_apply _ _ _))
  obtain ⟨C, i, hi, hxC, hC⟩ := Scheme.exists_affine_mem_range_and_range_subset hx
  let g : Spec C ⟶ Spec (.of A) := IsOpenImmersion.lift j (i ≫ f) (by
    rintro _ ⟨z, rfl⟩
    exact hC ⟨z, rfl⟩)
  have hg : g ≫ j = i ≫ f := IsOpenImmersion.lift_fac _ _ _
  have : Etale (g ≫ j) := hg ▸ inferInstance
  have : Etale g := Etale.of_comp g j
  let : Algebra A C := (Spec.preimage g).hom.toAlgebra
  have hga : Spec.map (CommRingCat.ofHom (algebraMap A C)) = g := Spec.map_preimage g
  have : Algebra.Etale A C := by
    apply RingHom.etale_algebraMap.mp
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    exact hga.symm ▸ inferInstance
  let q : s.source ⟶ Spec C := IsOpenImmersion.lift i p (by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = closedPoint s.residueField := Subsingleton.elim _ _
    exact hxC)
  have hq : q ≫ i = p := IsOpenImmersion.lift_fac _ _ _
  have hqg : q ≫ g = Spec.map (CommRingCat.ofHom (algebraMap A s.residueField)) := by
    apply (cancel_mono j).1
    rw [Category.assoc, hg, ← Category.assoc, hq]
    exact U.2.2.trans hj.symm
  let a : C →ₐ[A] s.residueField :=
    { toRingHom := (Spec.preimage q).hom
      commutes' := fun r => by
        have he := congrArg Spec.preimage hqg
        simp only [Spec.preimage_comp, Spec.preimage_map] at he
        exact ConcreteCategory.congr_hom he r }
  let D : CommAlgCat.AugmentedEtale A s.residueField :=
    CostructuredArrow.mk (Y := ⟨CommAlgCat.of A C, inferInstance⟩) (CommAlgCat.ofHom a)
  refine ⟨op D, ⟨neighborhoodHom B S hS s _ U i ?_ ?_⟩⟩
  · change i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ j
    rw [hga, hg]
  · change Spec.map (Spec.preimage q) ≫ i = p
    rw [Spec.map_preimage, hq]

/-- The diagram of augmented étale neighborhoods is initial. -/
private theorem augmentedNeighborhoodFunctor_initial
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (A : Type u) [CommRing A] [Algebra A s.residueField]
    (j : Spec (.of A) ⟶ S) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap A s.residueField)) ≫ j = s.hom) :
    (augmentedNeighborhoodFunctor B S hS s A j hj).Initial := by
  have := augmentedNeighborhoodFunctor_full B S hS s A j hj
  have := augmentedNeighborhoodFunctor_faithful B S hS s A j hj
  exact Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _
    (exists_augmentedNeighborhood_refinement B S hS s A j hj)

/-- Global sections of an augmented étale neighborhood are the underlying algebra. -/
private def augmentedNeighborhoodSectionsIso
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (A : Type u) [CommRing A] [Algebra A s.residueField]
    (j : Spec (.of A) ⟶ S) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap A s.residueField)) ≫ j = s.hom) :
    (augmentedNeighborhoodFunctor B S hS s A j hj).rightOp ⋙
      ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.structureSheaf B S hS).obj) ≅
    CommAlgCat.AugmentedEtale.forget A s.residueField ⋙
      forget₂ (CommAlgCat A) CommRingCat ⋙ forget₂ CommRingCat RingCat :=
  NatIso.ofComponents (fun C => (forget₂ CommRingCat RingCat).mapIso
    (Scheme.ΓSpecIso (.of C.left.obj))) (by
      intro C D f
      exact congrArg (fun t => (forget₂ CommRingCat RingCat).map t)
        (Scheme.ΓSpecIso_naturality
          (CommRingCat.ofHom (CommAlgCat.AugmentedEtale.map f).toRingHom)))

/-- Transporting a germ along an equality of base points. -/
private lemma germ_transport (S : Scheme.{u}) (V : S.Opens)
    {x y : S} (h : x = y) (hy : y ∈ V) (a : Γ(S, V)) :
    (h.symm ▸ S.presheaf.germ V y hy a) =
      S.presheaf.germ V x (h.symm ▸ hy) a := by
  cases h
  rfl

/-- The canonical ordinary-to-étale germ map is characterized at every
étale neighborhood by ordinary restriction of sections. -/
@[stacks 04HX "compatibility with ordinary germs"]
public theorem structureSheafStalkFromLocalRing_germ
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (U : (geometricPointFiber B S hS s).Elementsᵒᵖ)
    (r : S.presheaf.stalk (s.hom (closedPoint s.residueField)))
    (a : Γ((SmallEtale.toScheme B S hS).obj U.unop.1, ⊤)) :
    let f : ((SmallEtale.toScheme B S hS).obj U.unop.1) ⟶ S :=
      B.inclusion.map U.unop.1.obj.hom
    let p := U.unop.2.1
    let x := p (closedPoint s.residueField)
    let h : f x = s.hom (closedPoint s.residueField) :=
      (Scheme.Hom.comp_apply p f (closedPoint s.residueField)).symm.trans
        (congrArg (fun q : s.source ⟶ S => q (closedPoint s.residueField)) U.unop.2.2)
    (f.stalkMap x).hom (h.symm ▸ r) =
        ((SmallEtale.toScheme B S hS).obj U.unop.1).presheaf.germ
          ⊤ x trivial a →
      structureSheafStalkFromLocalRing B S hS s r = (colimit.ι
        ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
          (SmallEtale.structureSheaf B S hS).obj) U).hom a := by
  classical
  intro f p x hx ha
  let Y := (SmallEtale.toScheme B S hS).obj U.unop.1
  obtain ⟨V, hV, b, hb⟩ := S.presheaf.exists_germ_eq r
  have hV' : f x ∈ V := hx.symm ▸ hV
  change (f.stalkMap x).hom (hx.symm ▸ r) = Y.presheaf.germ ⊤ x trivial a at ha
  have hg : Y.presheaf.germ (f ⁻¹ᵁ V) x hV' (f.app V b) =
      Y.presheaf.germ ⊤ x trivial a := by
    rw [← hb, germ_transport S V hx hV b] at ha
    simpa only [Scheme.Hom.germ_stalkMap_apply] using ha
  obtain ⟨W, hW, iV, iTop, heq⟩ := Y.presheaf.germ_eq
    (U := f ⁻¹ᵁ V) (V := ⊤) x hV' trivial _ _ hg
  let N := openNeighborhood B S hS s U.unop W hW
  let Z := zariskiNeighborhood B S hS s (s.hom (closedPoint s.residueField))
    rfl ⟨V, hV⟩
  have hNU : N.2.1 ≫ Scheme.Opens.ι (X := Y) W = p :=
    openNeighborhood_point B S hS s U.unop W hW
  have hNZ : N.2.1 ≫ f.resLE V W iV.le = Z.2.1 := by
    refine (cancel_mono (Scheme.Opens.ι (X := S) V)).1 ?_
    refine (Category.assoc _ _ _).trans
      ((congrArg (fun z => N.2.1 ≫ z) (Scheme.Hom.resLE_comp_ι f iV.le)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun z => z ≫ f) hNU).trans (U.unop.2.2.trans Z.2.2.symm))))
  have hleft := colimit_ι_neighborhoodHom B S hS s N Z (f.resLE V W iV.le)
    (Scheme.Hom.resLE_comp_ι f iV.le) hNZ ((Scheme.Opens.topIso (X := S) V).inv b)
  have hright :=
    colimit_ι_neighborhoodHom B S hS s N U.unop (Scheme.Opens.ι (X := Y) W) rfl hNU a
  rw [← hb, structureSheafStalkFromLocalRing_open_germ]
  rw [← hleft, ← hright]
  congr 1
  change (f.resLE V W iV.le).appTop ((Scheme.Opens.topIso (X := S) V).inv b) =
    (Scheme.Opens.ι (X := Y) W).appTop a
  have happ : (f.resLE V W iV.le).appTop =
      (Scheme.Opens.topIso (X := S) V).hom ≫ f.appLE V W iV.le ≫
        (Scheme.Opens.topIso (X := Y) W).inv := by
    simpa only [Scheme.Hom.appTop, Scheme.Hom.resLE_preimage,
      Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top] using
      Scheme.Hom.resLE_app_top (f := f) (e := iV.le)
  rw [happ, opens_ι_appTop]
  change (Scheme.Opens.topIso (X := Y) W).inv
      (f.appLE V W iV.le ((Scheme.Opens.topIso (X := S) V).hom
        ((Scheme.Opens.topIso (X := S) V).inv b))) = _
  rw [show (Scheme.Opens.topIso (X := S) V).hom
      ((Scheme.Opens.topIso (X := S) V).inv b) = b from
    ConcreteCategory.congr_hom (Scheme.Opens.topIso (X := S) V).inv_hom_id b]
  exact congrArg (Scheme.Opens.topIso (X := Y) W).inv heq

/-- Evaluation of a germ of the structure sheaf is its value at the chosen
geometric lift on every étale neighborhood. -/
@[stacks 04HX "geometric evaluation of germs"]
public theorem structureSheafStalkToGeometricField_ι
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (U : (geometricPointFiber B S hS s).Elementsᵒᵖ) :
    (structureSheafStalkToGeometricField B S hS s).comp ((colimit.ι
      ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.structureSheaf B S hS).obj) U).hom) =
      ((U.unop.2.1).appTop ≫ (Scheme.ΓSpecIso (.of s.residueField)).hom).hom := by
  change ((colimit.desc _ (geometricFieldCocone B S hS s)).hom.comp (colimit.ι
    ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
      (SmallEtale.structureSheaf B S hS).obj) U).hom) =
    (((U.unop.2.1).appTop ≫ (Scheme.ΓSpecIso (.of s.residueField)).hom).hom)
  rw [← RingCat.hom_comp, colimit.ι_desc]
  rfl

/-- Values of an augmentation of an étale algebra are separable over any intermediate
field. -/
private lemma etale_augmentation_isSeparable
    {A C k K : Type u} [CommRing A] [CommRing C] [Field k] [Field K]
    [Algebra A C] [Algebra.Etale A C] [Algebra A k] [Algebra A K]
    [Algebra k K] [IsScalarTower A k K] (f : C →ₐ[A] K) (x : C) :
    IsSeparable k (f x) := by
  let D := k ⊗[A] C
  let g : D →ₐ[k] K := AlgHom.liftEquiv A k C K f
  let p := RingHom.ker g
  have : p.IsPrime := RingHom.ker_isPrime g
  let t : D ⧸ p →ₐ[k] K := Ideal.Quotient.liftₐ p g (fun a ha => ha)
  have ht : Function.Injective t := RingHom.kerLift_injective g.toRingHom
  have h := IsSeparable.map t ht (Algebra.IsSeparable.isSeparable k
    (Ideal.Quotient.mk p (Algebra.TensorProduct.includeRight x)))
  change IsSeparable k (g (1 ⊗ₜ[A] x)) at h
  exact (AlgHom.liftEquiv_tmul f 1 x).trans (one_smul k (f x)) ▸ h

/-- The forgetful functor to rings preserves filtered colimits of algebras. -/
private alias preservesColimitsOfShape_forgetCommAlg :=
  CommAlgCat.preservesColimitsOfShape_forget₂CommRingCat

/-- A ring presented as an ind-étale algebra with a compatible augmentation is the colimit of
the augmented étale algebras. -/
public lemma exists_isColimit_augmentedEtale_of_ind_etale
    {A H K : Type u} [CommRing A] [CommRing H] [Field K]
    [Algebra A H] [Algebra A K] (π : H →ₐ[A] K)
    (hind : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A H))
    (hlift : ∀ C : CommAlgCat.AugmentedEtale A K,
      ∃! f : C.left.obj →ₐ[A] H, π.comp f = C.hom.hom) :
    ∃ ι : (CommAlgCat.AugmentedEtale.forget A K ⋙
        forget₂ (CommAlgCat A) CommRingCat ⋙ forget₂ CommRingCat RingCat) ⟶
          (Functor.const _).obj (RingCat.of H),
      (∀ C x, π ((ι.app C).hom x) = C.hom.hom x) ∧
      (∀ C a, (ι.app C).hom (algebraMap A C.left.obj a) = algebraMap A H a) ∧
      Nonempty (IsColimit (Cocone.mk _ ι)) := by
  classical
  choose leg hleg huniq using hlift
  have hcomp {C D : CommAlgCat.AugmentedEtale A K} (f : C ⟶ D) :
      (leg D).comp (CommAlgCat.AugmentedEtale.map f) = leg C := by
    apply huniq C
    ext x
    change π (leg D (CommAlgCat.AugmentedEtale.map f x)) = C.hom.hom x
    rw [← AlgHom.comp_apply, hleg]
    exact CommAlgCat.AugmentedEtale.hom_map f x
  let ι : (CommAlgCat.AugmentedEtale.forget A K ⋙
      forget₂ (CommAlgCat A) CommRingCat ⋙ forget₂ CommRingCat RingCat) ⟶
      (Functor.const _).obj (RingCat.of H) := {
    app C := RingCat.ofHom (leg C).toRingHom
    naturality C D f := RingCat.hom_ext (congrArg AlgHom.toRingHom (hcomp f)) }
  refine ⟨ι, fun C => AlgHom.congr_fun (hleg C),
    fun C a => (leg C).commutes a, ?_⟩
  obtain ⟨J, _, _, pres, hpres⟩ := hind
  let Q := forget₂ (CommAlgCat A) CommRingCat ⋙ forget₂ CommRingCat RingCat
  have : PreservesColimitsOfShape J (forget₂ (CommAlgCat A) CommRingCat) :=
    preservesColimitsOfShape_forgetCommAlg A J
  let hc := isColimitOfPreserves Q pres.isColimit
  let obj (j : J) : CommAlgCat.AugmentedEtale A K :=
    CostructuredArrow.mk (Y := ⟨pres.diag.obj j, hpres j⟩)
      (CommAlgCat.ofHom (π.comp (pres.ι.app j).hom))
  have hstage (j : J) : ι.app (obj j) = Q.map (pres.ι.app j) :=
    RingCat.hom_ext (congrArg AlgHom.toRingHom (huniq (obj j) (pres.ι.app j).hom rfl).symm)
  let mapj {i j : J} (f : i ⟶ j) : obj i ⟶ obj j :=
    CostructuredArrow.homMk (ObjectProperty.homMk (pres.diag.map f))
      (CommAlgCat.hom_ext (AlgHom.ext fun x =>
        congrArg π (ConcreteCategory.congr_hom (pres.w f) x)))
  let d (s : Cocone (CommAlgCat.AugmentedEtale.forget A K ⋙ Q)) :
      Cocone (pres.diag ⋙ Q) :=
    { pt := s.pt
      ι := { app j := s.ι.app (obj j), naturality i j f := s.w (mapj f) } }
  refine ⟨{ desc s := hc.desc (d s), fac s C := ?_, uniq s m hm := ?_ }⟩
  · have : IsFinitelyPresentable.{u} C.left.obj :=
      CommAlgCat.isFinitelyPresentable_of_etale C.left.obj
    obtain ⟨j, g, hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit pres.isColimit
      (CommAlgCat.ofHom (leg C))
    let a : C ⟶ obj j := CostructuredArrow.homMk (ObjectProperty.homMk g) (by
      ext x
      change π ((pres.ι.app j).hom (g.hom x)) = C.hom.hom x
      exact (congrArg π (ConcreteCategory.congr_hom hg x)).trans
        (AlgHom.congr_fun (hleg C) x))
    have hg' : Q.map g ≫ Q.map (pres.ι.app j) = ι.app C := by
      rw [← Q.map_comp, hg]
      rfl
    rw [← hg', Category.assoc]
    have hfac : Q.map (pres.ι.app j) ≫ hc.desc (d s) = s.ι.app (obj j) := hc.fac (d s) j
    rw [hfac]
    exact s.w a
  · refine hc.hom_ext fun j => ?_
    rw [hc.fac]
    change Q.map (pres.ι.app j) ≫ m = s.ι.app (obj j)
    rw [← hstage]
    exact hm (obj j)

/-- An augmented étale algebra lifts uniquely to a henselian local ring whose residue field is
identified with the separable closure. -/
public theorem existsUnique_lift_augmentedEtale
    {A H k K : Type u} [CommRing A] [CommRing H] [HenselianLocalRing H]
    [Field k] [Field K] [Algebra A H] [Algebra A k] [Algebra A K]
    [Algebra k K] [IsScalarTower A k K]
    (e : separableClosure k K ≃+* ResidueField H)
    (π : H →ₐ[A] K)
    (hπ : ∀ x, π x = (e.symm (residue H x) : K))
    (C : CommAlgCat.AugmentedEtale A K) :
    ∃! f : C.left.obj →ₐ[A] H, π.comp f = C.hom.hom := by
  have : Algebra.Etale A C.left.obj := C.left.property
  let L := separableClosure k K
  let fL : C.left.obj →+* L := C.hom.hom.toRingHom.codRestrict L.toSubring
    (fun x => mem_separableClosure_iff.mpr
      (etale_augmentation_isSeparable (C := C.left.obj) C.hom.hom x))
  let η : ResidueField H →+* K := L.subtype.comp e.symm.toRingHom
  let ρ : C.left.obj →ₐ[A] ResidueField H :=
    { toRingHom := e.toRingHom.comp fL
      commutes' a := by
        apply η.injective
        change (e.symm (e (fL (algebraMap A C.left.obj a))) : K) =
          (e.symm (algebraMap A (ResidueField H) a) : K)
        rw [e.symm_apply_apply]
        change C.hom.hom (algebraMap A C.left.obj a) = _
        calc
          _ = algebraMap A K a := C.hom.hom.commutes a
          _ = _ := by
            rw [IsScalarTower.algebraMap_apply A H (ResidueField H),
              ResidueField.algebraMap_eq, ← hπ, π.commutes] }
  obtain ⟨f, hf, hu⟩ := HenselianLocalRing.existsUnique_algHom_residue_of_etale ρ
  refine ⟨f, ?_, ?_⟩
  · ext x
    change π (f x) = C.hom.hom x
    rw [hπ, hf]
    exact congrArg Subtype.val (e.symm_apply_apply (fL x))
  · refine fun g hg => hu g fun x => η.injective ?_
    change (e.symm (residue H (g x)) : K) = (e.symm (e (fL x)) : K)
    rw [e.symm_apply_apply, ← hπ]
    exact AlgHom.congr_fun hg x

/-- The étale stalk is the ring presented by the augmented étale algebras over an open affine
of the base. -/
private theorem exists_stalk_equiv_of_augmentedEtale
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (A H : Type u) [CommRing A] [CommRing H] [Algebra A H] [Algebra A s.residueField]
    (j : Spec (.of A) ⟶ S) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap A s.residueField)) ≫ j = s.hom)
    (π : H →ₐ[A] s.residueField)
    (hind : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A H))
    (hlift : ∀ C : CommAlgCat.AugmentedEtale A s.residueField,
      ∃! f : C.left.obj →ₐ[A] H, π.comp f = C.hom.hom) :
    ∃ e : H ≃+* ↥(etaleStalk B S hS s
        (SmallEtale.structureSheaf B S hS).obj),
      (∀ (C : CommAlgCat.AugmentedEtale A s.residueField) a, e (algebraMap A H a) =
        (colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
          (SmallEtale.structureSheaf B S hS).obj)
          (op (augmentedNeighborhood B S hS s A j hj C))).hom
            ((Scheme.ΓSpecIso (.of C.left.obj)).inv (algebraMap A C.left.obj a))) ∧
      (∀ x, structureSheafStalkToGeometricField B S hS s (e x) = π x) := by
  classical
  dsimp only
  obtain ⟨ι, hι, hbase, ⟨hc⟩⟩ :=
    exists_isColimit_augmentedEtale_of_ind_etale π hind hlift
  let F := (Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
    (SmallEtale.structureSheaf B S hS).obj
  let G := augmentedNeighborhoodFunctor B S hS s A j hj
  have : G.Initial := augmentedNeighborhoodFunctor_initial B S hS s A j hj
  let α := augmentedNeighborhoodSectionsIso B S hS s A j hj
  let c : Cocone (G.rightOp ⋙ F) := (Cocone.precompose α.hom).obj (Cocone.mk _ ι)
  let hc' : IsColimit c := (IsColimit.precomposeHomEquiv α _).symm hc
  let hd : IsColimit ((colimit.cocone F).whisker G.rightOp) :=
    (Functor.Final.isColimitWhiskerEquiv G.rightOp _).symm (colimit.isColimit F)
  let i := hc'.coconePointUniqueUpToIso hd
  let e : H ≃+* ↥(etaleStalk B S hS s
      (SmallEtale.structureSheaf B S hS).obj) := i.ringCatIsoToRingEquiv
  have he (C : CommAlgCat.AugmentedEtale A s.residueField) (x : C.left.obj) :
      e ((ι.app C).hom x) = (colimit.ι F (op (augmentedNeighborhood B S hS s A j hj C))).hom
        ((Scheme.ΓSpecIso (.of C.left.obj)).inv x) := by
    have h := ConcreteCategory.congr_hom
      (hc'.comp_coconePointUniqueUpToIso_hom hd C)
      ((Scheme.ΓSpecIso (.of C.left.obj)).inv x)
    change e ((ι.app C).hom ((Scheme.ΓSpecIso (.of C.left.obj)).hom
      ((Scheme.ΓSpecIso (.of C.left.obj)).inv x))) =
        (colimit.ι F (op (augmentedNeighborhood B S hS s A j hj C))).hom
          ((Scheme.ΓSpecIso (.of C.left.obj)).inv x) at h
    simpa only [Iso.inv_hom_id_apply] using h
  refine ⟨e, ?_, ?_⟩
  · intro C a
    rw [← hbase C a]
    exact he C (algebraMap A C.left.obj a)
  · have hmaps : i.hom ≫ RingCat.ofHom (structureSheafStalkToGeometricField B S hS s) =
        RingCat.ofHom π.toRingHom := by
      apply hc.hom_ext
      intro C
      ext x
      change structureSheafStalkToGeometricField B S hS s (e ((ι.app C).hom x)) =
        π ((ι.app C).hom x)
      rw [he, hι]
      have heval := RingHom.congr_fun
        (structureSheafStalkToGeometricField_ι B S hS s
          (op (augmentedNeighborhood B S hS s A j hj C)))
          ((Scheme.ΓSpecIso (.of C.left.obj)).inv x)
      change structureSheafStalkToGeometricField B S hS s
        ((colimit.ι F (op (augmentedNeighborhood B S hS s A j hj C))).hom
          ((Scheme.ΓSpecIso (.of C.left.obj)).inv x)) = _ at heval
      rw [heval]
      change ((Spec.map (CommRingCat.ofHom C.hom.hom.toRingHom)).appTop ≫
        (Scheme.ΓSpecIso (.of s.residueField)).hom)
          ((Scheme.ΓSpecIso (.of C.left.obj)).inv x) = C.hom.hom x
      rw [Scheme.ΓSpecIso_naturality]
      simp
    exact ConcreteCategory.congr_hom hmaps

/-- The `R`-algebra map to a field factoring through the residue field of a henselian local
`R`-algebra whose residue field is identified with the relative separable closure. -/
private def henselianResidueLift {R H K : Type u} [CommRing R] [IsLocalRing R]
    [CommRing H] [IsLocalRing H] [Field K]
    [Algebra R H] [Algebra (ResidueField R) K] [Algebra R K]
    (e : separableClosure (ResidueField R) K ≃+* ResidueField H)
    (hRK : ∀ r : R, algebraMap R K r = algebraMap (ResidueField R) K (residue R r))
    (he : ∀ r : R, e (algebraMap (ResidueField R)
        (separableClosure (ResidueField R) K) (residue R r)) =
      residue H (algebraMap R H r)) :
    H →ₐ[R] K where
  toRingHom := (separableClosure (ResidueField R) K).subtype.comp
    (e.symm.toRingHom.comp (residue H))
  commutes' r := by
    change ((e.symm (residue H (algebraMap R H r)) :
      separableClosure (ResidueField R) K) : K) = algebraMap R K r
    rw [← he r, e.symm_apply_apply, hRK r]
    rfl

/-- An `R`-algebra endomorphism of a henselian local ring which is the identity on residues
agrees with every `R`-algebra map from an étale `R`-algebra. -/
private theorem algHom_comp_eq_of_residue_eq {R A H : Type u} [CommRing R] [CommRing A]
    [CommRing H] [HenselianLocalRing H] [Algebra R A] [Algebra R H] [Algebra.Etale R A]
    (φ : H →ₐ[R] H) (hφ : ∀ y, residue H (φ y) = residue H y) (leg : A →ₐ[R] H) :
    φ.comp leg = leg := by
  let ρ : A →ₐ[R] ResidueField H :=
    { toRingHom := (residue H).comp leg.toRingHom
      commutes' := fun r => by
        change residue H (leg (algebraMap R A r)) = algebraMap R (ResidueField H) r
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R H (ResidueField H),
          IsLocalRing.ResidueField.algebraMap_eq] }
  obtain ⟨g, hg, huniq⟩ := HenselianLocalRing.existsUnique_algHom_residue_of_etale ρ
  exact (huniq (φ.comp leg) (fun x => hφ (leg x))).trans (huniq leg (fun _ => rfl)).symm

/-- Every point of a scheme lies in an affine open. -/
private theorem exists_isAffineOpen_containing (X : Scheme.{u}) (z : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ z ∈ U := by
  obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := z) (U := ⊤) (by trivial)
  exact ⟨U, hU, hz⟩

/-- The canonical map from the ordinary local ring sends the germ at the geometric point of a
section over an affine open to the class of that section on the augmented étale neighborhood
given by the affine open itself. -/
private theorem structureSheafStalkFromLocalRing_germ_augmentedNeighborhood
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
    (U : S.Opens) (hU : IsAffineOpen U)
    (hx : s.hom (closedPoint s.residueField) ∈ U)
    [Algebra Γ(S, U) s.residueField]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) s.residueField)) ≫ hU.fromSpec =
      s.hom)
    (a : Γ(S, U)) :
    structureSheafStalkFromLocalRing B S hS s
        (S.presheaf.germ U (s.hom (closedPoint s.residueField)) hx a) =
      (colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.structureSheaf B S hS).obj)
        (op (augmentedNeighborhood B S hS s Γ(S, U) hU.fromSpec hj
          (CostructuredArrow.mk (Y := ⟨CommAlgCat.of Γ(S, U) Γ(S, U), inferInstance⟩)
            (CommAlgCat.ofHom (Algebra.ofId Γ(S, U) s.residueField)))))).hom
        ((Scheme.ΓSpecIso (.of Γ(S, U))).inv a) := by
  classical
  let A := Γ(S, U)
  let x := s.hom (closedPoint s.residueField)
  let j : Spec (.of A) ⟶ S := hU.fromSpec
  let C₀ : CommAlgCat.AugmentedEtale A s.residueField :=
    CostructuredArrow.mk (Y := ⟨CommAlgCat.of A A, inferInstance⟩)
      (CommAlgCat.ofHom (Algebra.ofId A s.residueField))
  rw [structureSheafStalkFromLocalRing_open_germ]
  let W := zariskiNeighborhood B S hS s x rfl ⟨U, hx⟩
  let N := augmentedNeighborhood B S hS s A j hj C₀
  have hf : hU.isoSpec.inv ≫ B.inclusion.map W.1.obj.hom =
      B.inclusion.map N.1.obj.hom := by
    change hU.isoSpec.inv ≫ U.ι = Spec.map (CommRingCat.ofHom (algebraMap A A)) ≫ j
    rw [show CommRingCat.ofHom (algebraMap A A) = 𝟙 (CommRingCat.of A) from rfl,
      Spec.map_id, Category.id_comp]
    exact hU.isoSpec_inv_ι
  have hp : N.2.1 ≫ hU.isoSpec.inv = W.2.1 :=
    (cancel_mono U.ι).1 <| (Category.assoc _ _ _).trans
      ((congrArg (fun z => N.2.1 ≫ z) hU.isoSpec_inv_ι).trans
        (hj.trans W.2.2.symm))
  have hw := colimit_ι_neighborhoodHom B S hS s N W hU.isoSpec.inv hf hp
    (U.topIso.inv a)
  have hv : hU.isoSpec.inv.appTop (U.topIso.inv a) =
      (Scheme.ΓSpecIso (.of A)).inv a := by
    rw [hU.isoSpec_inv_appTop]
    change (Scheme.ΓSpecIso (.of A)).inv (U.topIso.hom (U.topIso.inv a)) = _
    rw [Iso.inv_hom_id_apply]
  exact hw.symm.trans (congrArg
    ((colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
      (SmallEtale.structureSheaf B S hS).obj) (op N)).hom) hv)

private theorem Spec_map_germ_stalkClosedPointTo_fromSpec (S : Scheme.{u})
    (s : GeometricPoint S) {U : S.Opens} (hU : IsAffineOpen U)
    (hx : s.hom (closedPoint s.residueField) ∈ U) :
    Spec.map (S.presheaf.germ U _ hx ≫ Scheme.stalkClosedPointTo s.hom) ≫ hU.fromSpec =
      s.hom := by
  rw [Spec.map_comp, Category.assoc]
  change Spec.map (Scheme.stalkClosedPointTo s.hom) ≫ hU.fromSpecStalk hx = s.hom
  rw [hU.fromSpecStalk_eq_fromSpecStalk hx]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk s.hom

/-- The étale stalk is canonically the strict henselization of the ordinary
local ring, with its residue field identified with the separable subextension
of the geometric point's field. -/
@[stacks 04HX "the strict-henselization identification"]
public noncomputable def etaleLocalRing_strictHenselization_canonical
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (T : IsLocalRing.HenselizationTower
        (S.presheaf.stalk (s.hom (closedPoint s.residueField)))
        (separableClosure (ResidueField
          (S.presheaf.stalk (s.hom (closedPoint s.residueField))))
          s.residueField)) :
    { e : T.strictHenselization ≃+*
        ↥(etaleStalk B S hS s
          (SmallEtale.structureSheaf B S hS).obj) //
      (∀ r, e (algebraMap
        (S.presheaf.stalk (s.hom (closedPoint s.residueField)))
        T.strictHenselization r) = structureSheafStalkFromLocalRing B S hS s r) ∧
      (∀ a, structureSheafStalkToGeometricField B S hS s (e a) =
        ((T.strictHenselizationResidueEquiv.symm
          (residue T.strictHenselization a) :
            separableClosure (ResidueField
              (S.presheaf.stalk (s.hom (closedPoint s.residueField))))
              s.residueField) : s.residueField)) } := by
  classical
  exact Classical.choice (by
    let x := s.hom (closedPoint s.residueField)
    let hUex := exists_isAffineOpen_containing S x
    let U := hUex.choose
    have hU : IsAffineOpen U := hUex.choose_spec.1
    have hx : x ∈ U := hUex.choose_spec.2
    let R := S.presheaf.stalk x
    let k := ResidueField R
    let K := s.residueField
    let L := separableClosure k K
    let H := T.strictHenselization
    let eL : L ≃+* ResidueField H := T.strictHenselizationResidueEquiv
    let : Algebra R K := ((algebraMap k K).comp (residue R)).toAlgebra
    let πR : H →ₐ[R] K := henselianResidueLift eL (fun _ => rfl)
      T.strictHenselizationResidueEquiv_residue
    let A := Γ(S, U)
    let : Algebra A R := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨x, hx⟩
    let : Algebra A k := ((residue R).comp (algebraMap A R)).toAlgebra
    let : Algebra A H := ((algebraMap R H).comp (algebraMap A R)).toAlgebra
    let : Algebra A K := ((algebraMap R K).comp (algebraMap A R)).toAlgebra
    have : IsScalarTower A R H := .of_algebraMap_eq fun _ => rfl
    have : IsScalarTower A R K := .of_algebraMap_eq fun _ => rfl
    have : IsScalarTower A k K := .of_algebraMap_eq fun _ => rfl
    let p := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    have : IsLocalization.AtPrime R p := hU.isLocalization_stalk ⟨x, hx⟩
    let j : Spec (.of A) ⟶ S := hU.fromSpec
    have hj : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ j = s.hom := by
      rw [show CommRingCat.ofHom (algebraMap A K) =
          S.presheaf.germ U x hx ≫ Scheme.stalkClosedPointTo s.hom by
        rw [← S.residue_descResidueField (Scheme.stalkClosedPointTo s.hom)]
        rfl]
      exact Spec_map_germ_stalkClosedPointTo_fromSpec S s hU hx
    let π : H →ₐ[A] K := πR.restrictScalars A
    have hind : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A H) :=
      CommAlgCat.ind_etale_comp (CommAlgCat.ind_etale_atPrime A R p)
        (IsHenselization.ind_etale_of_universe_le L)
    obtain ⟨e, he, hπ⟩ := exists_stalk_equiv_of_augmentedEtale B S hS s A H j hj π hind
      (existsUnique_lift_augmentedEtale eL π fun _ => rfl)
    let C₀ : CommAlgCat.AugmentedEtale A K :=
      CostructuredArrow.mk (Y := ⟨CommAlgCat.of A A, inferInstance⟩)
        (CommAlgCat.ofHom (Algebra.ofId A K))
    have hbase : e.toRingHom.comp (algebraMap R H) =
        structureSheafStalkFromLocalRing B S hS s := by
      apply IsLocalization.ringHom_ext p.primeCompl
      ext a
      change e (algebraMap R H (algebraMap A R a)) =
        structureSheafStalkFromLocalRing B S hS s (algebraMap A R a)
      rw [← IsScalarTower.algebraMap_apply A R H, he C₀]
      exact (structureSheafStalkFromLocalRing_germ_augmentedNeighborhood B S hS s U hU hx hj a).symm
    exact ⟨⟨e, RingHom.congr_fun hbase, hπ⟩⟩)

/-- The comparison is uniquely determined by the map from the ordinary local
ring and by the inclusion of the relative separable closure in the geometric
point's field. -/
@[stacks 04HX "uniqueness of the canonical identification"]
public theorem etaleLocalRing_strictHenselization_unique
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (s : GeometricPoint S)
    (T : IsLocalRing.HenselizationTower
      (S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (separableClosure (ResidueField
        (S.presheaf.stalk (s.hom (closedPoint s.residueField)))) s.residueField))
    (e : T.strictHenselization ≃+*
      ↥(etaleStalk B S hS s
        (SmallEtale.structureSheaf B S hS).obj))
    (hbase : ∀ r, e (algebraMap
      (S.presheaf.stalk (s.hom (closedPoint s.residueField)))
      T.strictHenselization r) = structureSheafStalkFromLocalRing B S hS s r)
    (hres : ∀ a, structureSheafStalkToGeometricField B S hS s (e a) =
      ((T.strictHenselizationResidueEquiv.symm
        (residue T.strictHenselization a) :
          separableClosure (ResidueField
            (S.presheaf.stalk (s.hom (closedPoint s.residueField))))
            s.residueField) : s.residueField)) :
    e = (etaleLocalRing_strictHenselization_canonical B S hS s T).val := by
  classical
  let R := S.presheaf.stalk (s.hom (closedPoint s.residueField))
  let K := separableClosure (ResidueField R) s.residueField
  let e₀ := (etaleLocalRing_strictHenselization_canonical B S hS s T).val
  let α : T.strictHenselization ≃+* T.strictHenselization := e.trans e₀.symm
  have hbase₀ : ∀ r : R, e₀ (algebraMap R T.strictHenselization r) =
      structureSheafStalkFromLocalRing B S hS s r :=
    (etaleLocalRing_strictHenselization_canonical B S hS s T).property.1
  have hres₀ : ∀ a : T.strictHenselization,
      structureSheafStalkToGeometricField B S hS s (e₀ a) =
        ((T.strictHenselizationResidueEquiv.symm
          (residue T.strictHenselization a) : K) : s.residueField) :=
    (etaleLocalRing_strictHenselization_canonical B S hS s T).property.2
  have hαbase (r : R) : α (algebraMap R T.strictHenselization r) =
      algebraMap R T.strictHenselization r := by
    change e₀.symm (e (algebraMap R T.strictHenselization r)) = _
    rw [hbase r, ← hbase₀ r, e₀.symm_apply_apply]
  have hαres (a : T.strictHenselization) :
      residue T.strictHenselization (α a) = residue T.strictHenselization a :=
    T.strictHenselizationResidueEquiv.symm.injective (Subtype.val_injective
      ((hres₀ (α a)).symm.trans
        ((congrArg (structureSheafStalkToGeometricField B S hS s)
          (e₀.apply_symm_apply (e a))).trans (hres a))))
  let φ : T.strictHenselization →ₐ[R] T.strictHenselization :=
    { toRingHom := α.toRingHom
      commutes' := hαbase }
  let : IsLocalRing.IsHenselization R K T.strictHenselization :=
    T.strictHenselizationIsHenselization
  obtain ⟨J, _, _, pres, hpres⟩ := IsLocalRing.IsHenselization.ind_etale_of_universe_le
    (R := R) (L := K) (Rh := T.strictHenselization)
  have hlegs (j : J) :
      φ.comp (pres.cocone.ι.app j).hom = (pres.cocone.ι.app j).hom := by
    have : Algebra.Etale R (pres.diag.obj j : Type u) := hpres j
    exact algHom_comp_eq_of_residue_eq φ hαres _
  have hφid' : φ = AlgHom.id R T.strictHenselization := by
    have h : CommAlgCat.ofHom φ = 𝟙 (CommAlgCat.of R T.strictHenselization) := by
      refine pres.isColimit.hom_ext fun j => ?_
      apply CommAlgCat.hom_ext
      ext x
      exact AlgHom.congr_fun (hlegs j) x
    exact AlgHom.ext fun a => ConcreteCategory.congr_hom h a
  refine RingEquiv.ext fun a => ?_
  have ha : α a = a := by simpa [φ, α] using AlgHom.congr_fun hφid' a
  exact (e₀.apply_symm_apply (e a)).symm.trans (congrArg e₀ ha)

end AlgebraicGeometry

end
