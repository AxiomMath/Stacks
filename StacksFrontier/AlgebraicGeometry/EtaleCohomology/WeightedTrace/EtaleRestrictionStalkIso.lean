module

public import StacksFrontier.AlgebraicGeometry.Etale.EtaleUpperShriekRestriction
public import StacksFrontier.AlgebraicGeometry.Etale.UpperShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CoefficientsGerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleRestrictionStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceConstruction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves
public import StacksCore.Tactic.StacksAttribute

/-!
# The two spellings of the inverse image along an étale morphism agree on stalks

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`. The
inverse image of abelian étale sheaves along `j` has two descriptions: as the sheaf pullback
along base change, which is where Stacks 03Q1 computes its stalks
(`AlgebraicGeometry.etaleStalkSmallEtalePullObjIso`), and as restriction along composition with
`j`, which is where the extension-by-zero adjunction of Stacks 03S3 lives. They agree, by
`AlgebraicGeometry.smallEtaleSheafPullbackIsoPostcompose`, both being left adjoint to the direct
image along base change.

This file proves that the comparison of the two is compatible with the two descriptions of the
stalk at a point of the geometric fibre: the identification of Stacks 03Q1 is the comparison
followed by the elementary map `AlgebraicGeometry.restrictionStalkMap`, which simply reads an
étale neighbourhood of the fibre point as an étale neighbourhood of the point below.

## Main results

* `AlgebraicGeometry.colimit_ι_comp_eqToHom` — moving a germ across an equality of geometric
  points with the same residue field.
* `AlgebraicGeometry.pullbackSectionAlongHom_comp_etaleRestrictionIso` — the comparison of the
  two inverse images, on sections: it carries the pullback of a section along the unit of
  `j^{-1} ⊣ j_*` to its restriction along the counit of the site-level adjunction between
  composition with `j` and base change along `j`, namely the projection `V ×_X U ⟶ V`.
* `AlgebraicGeometry.restrictionStalkMap_comp_etaleRestrictionIso` — **the two stalk
  comparisons agree.** The identification of Stacks 03Q1 of the stalk of `j^{-1}ℱ` at a point of
  the geometric fibre with the stalk of `ℱ` below is the comparison of the two inverse images
  followed by `AlgebraicGeometry.restrictionStalkMap`.

## Implementation notes

The proof is the universal property of the comparison. It is `leftAdjointUniq` of two
adjunctions with the same right adjoint, so
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` computes it on sections against the two
units, and the unit of the sheaf-level adjunction coming from the site-level adjunction is
restriction along the site-level counit. The identification of Stacks 03Q1 is characterised on
germs of pulled-back sections by `AlgebraicGeometry.etaleStalkSmallEtalePullObjIso_germ`, applied
to the base change `V ×_X U` of an étale neighbourhood `V` of the point below with the lift
`AlgebraicGeometry.SmallEtale.fiberPointLift` determined by the two lifts.

The geometric point `p ∘ j` of `X` below a point `p` of the geometric fibre above `s` is `s`
itself, but only propositionally. `AlgebraicGeometry.colimit_ι_comp_eqToHom` is the one lemma
needed to move a germ along that equality; it is stated for two geometric points with a common
residue field and proved by cases on the equality of their morphisms, so no reasoning about
`eqToHom` is left in the proof below.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- Moving a germ across an equality of geometric points with a common residue field: the germ
of a section over an étale neighbourhood at one of two equal geometric points is its germ at the
other, the lift being unchanged. -/
public theorem colimit_ι_comp_eqToHom (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (r : Type u) [Field r] [IsAlgClosed r]
    {m m' : Spec (CommRingCat.of r) ⟶ S} (h : m = m')
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (V : SmallEtale B S hS)
    (q : (geometricPointFiber B S hS { residueField := r, hom := m }).obj V)
    (q' : (geometricPointFiber B S hS { residueField := r, hom := m' }).obj V)
    (hq : q'.1 = q.1) :
    colimit.ι (SmallEtale.etaleStalkDiagram B S hS { residueField := r, hom := m } P)
          (op ⟨V, q⟩) ≫
        eqToHom (congrArg
          (fun n => etaleStalk B S hS { residueField := r, hom := n } P) h) =
      colimit.ι (SmallEtale.etaleStalkDiagram B S hS { residueField := r, hom := m' } P)
        (op ⟨V, q'⟩) := by
  cases h
  obtain rfl : q' = q := Subtype.ext hq
  exact Category.comp_id _

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)
  (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1})

/-- The comparison of the two spellings of the inverse image of abelian étale sheaves along the
étale morphism `U ⟶ X`: the sheaf pullback along base change, and restriction along composition
with the structure morphism. -/
public abbrev etaleRestrictionIso :
    SmallEtale.abPullback.{u, u + 1} B U.obj.hom ≅ abelianRestriction B X hX U :=
  smallEtaleSheafPullbackIsoPostcompose B X hX U AddCommGrpCat.{u + 1}

/-- The unit of the sheaf-level adjunction attached to the site-level adjunction between
composition with `U ⟶ X` and base change along it is restriction along the site-level counit. -/
public theorem sheafPushforwardAdjunction_unit_hom_app (V : SmallEtale B X hX) :
    (((smallEtalePostcomposeBaseChangeAdjunction_structureMorphism B X hX U
          ).sheafPushforwardAdjunction
            (J := SmallEtale.topology B U.obj.left.1 U.obj.left.property)
            (K := SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}).unit.app F).hom.app (op V) =
      F.obj.map ((smallEtalePostcomposeBaseChangeAdjunction_structureMorphism
        B X hX U).counit.app V).op :=
  rfl

/-- **The comparison of the two inverse images, on sections.** Pulling a section of `ℱ` over `V`
back along the unit of `j^{-1} ⊣ j_*` and comparing to the restriction spelling returns the
restriction of the section along the projection `V ×_X U ⟶ V`, the counit of the site-level
adjunction. -/
public theorem pullbackSectionAlongHom_comp_etaleRestrictionIso (V : SmallEtale B X hX) :
    pullbackSectionAlongHom B U.obj.hom AddCommGrpCat.{u + 1} F V
          ((smallEtaleBaseChange B U.obj.hom).obj V) (𝟙 _) ≫
        ((etaleRestrictionIso B X hX U).hom.app F).hom.app
          (op ((smallEtaleBaseChange B U.obj.hom).obj V)) =
      F.obj.map ((smallEtalePostcomposeBaseChangeAdjunction_structureMorphism
        B X hX U).counit.app V).op := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((smallEtaleBaseChange B U.obj.hom).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B X hX)
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property))
    ((smallEtalePostcomposeBaseChangeAdjunction_structureMorphism B X hX U
      ).sheafPushforwardAdjunction
        (J := SmallEtale.topology B U.obj.left.1 U.obj.left.property)
        (K := SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) F
  have h2 := congrArg (fun k : F ⟶ _ => k.hom.app (op V)) h
  have hpsa : pullbackSectionAlongHom B U.obj.hom AddCommGrpCat.{u + 1} F V
        ((smallEtaleBaseChange B U.obj.hom).obj V) (𝟙 _) =
      (((smallEtaleBaseChange B U.obj.hom).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X hX)
        (SmallEtale.topology B U.obj.left.1 U.obj.left.property)).unit.app F).hom.app (op V) :=
    (congrArg (fun z => (((smallEtaleBaseChange B U.obj.hom).sheafAdjunctionContinuous
          AddCommGrpCat.{u + 1} (SmallEtale.topology B X hX)
          (SmallEtale.topology B U.obj.left.1 U.obj.left.property)).unit.app F).hom.app
        (op V) ≫ z)
      (CategoryTheory.Functor.map_id
        (((SmallEtale.abPullback.{u, u + 1} B U.obj.hom).obj F).obj)
        (op ((smallEtaleBaseChange B U.obj.hom).obj V)))).trans (Category.comp_id _)
  rw [hpsa]
  exact h2.trans (sheafPushforwardAdjunction_unit_hom_app B X hX U F V)

/-- The counit of the site-level adjunction between composition with the structure morphism of
`U` and base change along it is the projection `V ×_X U ⟶ V`. -/
public theorem structureMorphism_counit_app_left (V : SmallEtale B X hX) :
    ((SmallEtale.inclusion B X hX).map
        ((smallEtalePostcomposeBaseChangeAdjunction_structureMorphism B X hX U).counit.app
          V)).left = pullback.fst V.obj.hom U.obj.hom := by
  dsimp only [smallEtalePostcomposeBaseChangeAdjunction_structureMorphism]
  rw [Adjunction.map_restrictFullyFaithful_counit_app,
    show (eqToIso (smallEtalePostcompose_comp_inclusion B X hX U).symm).inv = 𝟙 _ from rfl,
    show (eqToIso (smallEtaleBaseChange_comp_inclusion B U.obj.hom).symm).inv = 𝟙 _ from rfl]
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj,
    smallEtaleBaseChange_obj_obj, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Over.mapPullbackAdj_counit_app, Category.id_comp]
  exact congrArg (fun k : ((smallEtalePostcompose B X hX U).obj
      ((smallEtaleBaseChange B U.obj.hom).obj V)).obj ⟶ V.obj => k.left)
    (Category.id_comp _)

/-- The counit of the site-level adjunction between composition with the structure morphism of
`U` and base change along it is the projection `V ×_X U ⟶ V`. -/
public theorem toScheme_map_structureMorphism_counit (V : SmallEtale B X hX) :
    (SmallEtale.toScheme B X hX).map
        ((smallEtalePostcomposeBaseChangeAdjunction_structureMorphism B X hX U).counit.app V) =
      B.inclusion.map (pullback.fst V.obj.hom U.obj.hom) :=
  congrArg B.inclusion.map (structureMorphism_counit_app_left B X hX U V)

section Fibre

variable (s : GeometricPoint X) (x : SmallEtale.GeometricFiberPoint B U.obj.hom s)

/-- The lift to the base change `V ×_X U` of the geometric point of `U` determined by a point
`x` of the geometric fibre above `s`, given a lift of `s` to an étale neighbourhood `V`. -/
public def fibreBaseChangeLift (V : SmallEtale B X hX)
    (q : (geometricPointFiber B X hX s).obj V) :
    (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s)).obj ((smallEtaleBaseChange B U.obj.hom).obj V) :=
  ⟨SmallEtale.fiberPointLift B U.obj.hom s V q x,
    SmallEtale.fiberPointLift_comp_snd B U.obj.hom s V q x⟩

/-- **The two stalk comparisons agree.** The identification of Stacks 03Q1 of the stalk of
`j^{-1}ℱ` at a point `x` of the geometric fibre of `j` above `s` with the stalk of `ℱ` at `s` is
the comparison of the two spellings of the inverse image, followed by the elementary map
`AlgebraicGeometry.restrictionStalkMap` which reads an étale neighbourhood of `x` in `U` as an
étale neighbourhood of `s` in `X`. -/
public theorem restrictionStalkMap_comp_etaleRestrictionIso :
    colim.map (Functor.whiskerLeft (CategoryOfElements.π (geometricPointFiber B U.obj.left.1
            U.obj.left.property (x.toGeometricPoint B U.obj.hom s))).op
          ((etaleRestrictionIso B X hX U).hom.app F).1) ≫
        restrictionStalkMap B X hX U s x F =
      (SmallEtale.fiberPointPullbackStalkIso.{u, u + 1} B U.obj.hom s F x).hom := by
  refine (Iso.inv_comp_eq _).1 ?_
  refine colimit.hom_ext fun N => ?_
  let hs : (geometricPointFiber B X hX s).obj N.unop.1 :=
    ⟨N.unop.2.1, N.unop.2.2.trans x.2⟩
  let W : SmallEtale B U.obj.left.1 U.obj.left.property :=
    (smallEtaleBaseChange B U.obj.hom).obj N.unop.1
  let Wlift : (geometricPointFiber B U.obj.left.1 U.obj.left.property
      (x.toGeometricPoint B U.obj.hom s)).obj W :=
    fibreBaseChangeLift B X hX U s x N.unop.1 hs
  let A : (geometricPointFiber B X hX s).Elements :=
    ⟨(smallEtalePostcompose B X hX U).obj W, pushLift B X hX U s W x Wlift⟩
  let A' : (geometricPointFiber B X hX s).Elements := ⟨N.unop.1, hs⟩
  let m : A ⟶ A' :=
    ⟨(smallEtalePostcomposeBaseChangeAdjunction_structureMorphism B X hX U).counit.app
        N.unop.1, by
      refine Subtype.ext ?_
      show SmallEtale.fiberPointLift B U.obj.hom s N.unop.1 hs x ≫
        (SmallEtale.toScheme B X hX).map
          ((smallEtalePostcomposeBaseChangeAdjunction_structureMorphism B X hX U).counit.app
            N.unop.1) = N.unop.2.1
      rw [toScheme_map_structureMorphism_counit B X hX U N.unop.1]
      exact SmallEtale.fiberPointLift_comp_fst B U.obj.hom s N.unop.1 hs x⟩
  have hgerm := etaleStalkSmallEtalePullObjIso_germ B U.obj.hom
    (x.toGeometricPoint B U.obj.hom s) AddCommGrpCat.{u + 1} F ⟨W, Wlift⟩ N.unop (𝟙 W) (by
      show SmallEtale.fiberPointLift B U.obj.hom s N.unop.1 hs x ≫
          (SmallEtale.toScheme B U.obj.left.1 U.obj.left.property).map (𝟙 W) ≫
          B.inclusion.map (pullback.fst N.unop.1.obj.hom U.obj.hom) = N.unop.2.1
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
      exact SmallEtale.fiberPointLift_comp_fst B U.obj.hom s N.unop.1 hs x)
  have h1 : colimit.ι (SmallEtale.etaleStalkDiagram B X hX
          ((x.toGeometricPoint B U.obj.hom s).map (B.inclusion.map U.obj.hom)) F.obj)
          (op N.unop) ≫
        (etaleStalkSmallEtalePullObjIso B U.obj.hom (x.toGeometricPoint B U.obj.hom s)
          AddCommGrpCat.{u + 1} F).inv =
      pullbackSectionAlongHom B U.obj.hom AddCommGrpCat.{u + 1} F N.unop.1 W (𝟙 W) ≫
        colimit.ι (SmallEtale.etaleStalkDiagram B U.obj.left.1 U.obj.left.property
          (x.toGeometricPoint B U.obj.hom s)
          ((SmallEtale.abPullback.{u, u + 1} B U.obj.hom).obj F).obj) (op ⟨W, Wlift⟩) :=
    (Iso.comp_inv_eq _).2 ((Category.assoc _ _ _).trans hgerm).symm
  have hmid : colimit.ι (SmallEtale.etaleStalkDiagram B U.obj.left.1 U.obj.left.property
          (x.toGeometricPoint B U.obj.hom s)
          ((SmallEtale.abPullback.{u, u + 1} B U.obj.hom).obj F).obj) (op ⟨W, Wlift⟩) ≫
        colim.map (Functor.whiskerLeft (CategoryOfElements.π
            (geometricPointFiber B U.obj.left.1 U.obj.left.property
              (x.toGeometricPoint B U.obj.hom s))).op
            ((etaleRestrictionIso B X hX U).hom.app F).1) ≫
          restrictionStalkMap B X hX U s x F =
      ((etaleRestrictionIso B X hX U).hom.app F).1.app (op W) ≫
        colimit.ι (SmallEtale.etaleStalkDiagram B X hX s F.obj) (op A) :=
    by
    erw [← Category.assoc, colimit.ι_map, Category.assoc,
      restrictionStalkMap_germ B X hX U s x F W Wlift]
    rfl

  have h4 : pullbackSectionAlongHom B U.obj.hom AddCommGrpCat.{u + 1} F N.unop.1 W (𝟙 W) ≫
        ((etaleRestrictionIso B X hX U).hom.app F).1.app (op W) =
      F.obj.map ((smallEtalePostcomposeBaseChangeAdjunction_structureMorphism B X hX U
        ).counit.app N.unop.1).op :=
    pullbackSectionAlongHom_comp_etaleRestrictionIso B X hX U F N.unop.1
  have h5 : F.obj.map ((smallEtalePostcomposeBaseChangeAdjunction_structureMorphism B X hX U
            ).counit.app N.unop.1).op ≫
        colimit.ι (SmallEtale.etaleStalkDiagram B X hX s F.obj) (op A) =
      colimit.ι (SmallEtale.etaleStalkDiagram B X hX s F.obj) (op A') :=
    colimit.w (SmallEtale.etaleStalkDiagram B X hX s F.obj) m.op
  have h6 : colimit.ι (SmallEtale.etaleStalkDiagram B X hX
          ((x.toGeometricPoint B U.obj.hom s).map (B.inclusion.map U.obj.hom)) F.obj)
          (op N.unop) ≫
        eqToHom (congrArg (fun r => etaleStalk B X hX r F.obj)
          (SmallEtale.toGeometricPoint_map B U.obj.hom s x)) =
      colimit.ι (SmallEtale.etaleStalkDiagram B X hX s F.obj) (op A') :=
    colimit_ι_comp_eqToHom B X hX s.residueField x.2 F.obj N.unop.1 N.unop.2 hs rfl
  show colimit.ι (SmallEtale.etaleStalkDiagram B X hX
        ((x.toGeometricPoint B U.obj.hom s).map (B.inclusion.map U.obj.hom)) F.obj)
        (op N.unop) ≫
      ((etaleStalkSmallEtalePullObjIso B U.obj.hom (x.toGeometricPoint B U.obj.hom s)
            AddCommGrpCat.{u + 1} F).inv ≫
        colim.map (Functor.whiskerLeft (CategoryOfElements.π
            (geometricPointFiber B U.obj.left.1 U.obj.left.property
              (x.toGeometricPoint B U.obj.hom s))).op
            ((etaleRestrictionIso B X hX U).hom.app F).1) ≫
          restrictionStalkMap B X hX U s x F) =
    colimit.ι (SmallEtale.etaleStalkDiagram B X hX
        ((x.toGeometricPoint B U.obj.hom s).map (B.inclusion.map U.obj.hom)) F.obj)
        (op N.unop) ≫
      eqToHom (congrArg (fun r => etaleStalk B X hX r F.obj)
        (SmallEtale.toGeometricPoint_map B U.obj.hom s x))
  erw [← Category.assoc, h1, Category.assoc, hmid, ← Category.assoc, h4, h5, ← h6]

end Fibre

end AlgebraicGeometry

end
