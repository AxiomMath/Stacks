module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Widesubcategory
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RT
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGlobal
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
import Mathlib.AlgebraicGeometry.PullbackCarrier
import StacksFrontier.AlgebraicGeometry.Spaces.Category
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
import StacksFrontier.AlgebraicGeometry.Spaces.Points
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesRimSchlessinger.BaseChange
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesRimSchlessinger.ProperFibres
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesRimSchlessinger.BoundedProperCore
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesRimSchlessinger.BaseChange

/-!
# Stacks 0D56: gluing families of curves across an affine thickening pushout

The canonical restriction functor for curves across an affine thickening pushout, its
equivalence property deduced from that of Stacks 0D1J, the overlap comparisons, and
`AlgebraicGeometry.curvePushoutEquivalence`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- An isomorphism between the images of two objects under `CategoricalPullback.map` lifts to the
source when `M` is faithful and isomorphisms lift along `L` and `N` by the given `l` and `n`. -/
private def categoricalPullbackMap_preimageIso
    {A B C A' B' C' : Type*} [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    {F : A ⥤ B} {G : C ⥤ B} {F' : A' ⥤ B'} {G' : C' ⥤ B'}
    (L : A ⥤ A') (M : B ⥤ B') (N : C ⥤ C')
    (a : F ⋙ M ≅ L ⋙ F') (b : G ⋙ M ≅ N ⋙ G')
    [M.Faithful]
    (l : ∀ {X Y}, (L.obj X ≅ L.obj Y) → (X ≅ Y))
    (hl : ∀ {X Y} (e : L.obj X ≅ L.obj Y), L.map (l e).hom = e.hom)
    (n : ∀ {X Y}, (N.obj X ≅ N.obj Y) → (X ≅ Y))
    (hn : ∀ {X Y} (e : N.obj X ≅ N.obj Y), N.map (n e).hom = e.hom)
    {X Y : CategoricalPullback F G}
    (e : (CategoricalPullback.map F G L N M F' G' b.symm a).obj X ≅
      (CategoricalPullback.map F G L N M F' G' b.symm a).obj Y) :
    X ≅ Y := by
  let el : L.obj X.fst ≅ L.obj Y.fst := (CategoricalPullback.π₁ _ _).mapIso e
  let er : N.obj X.snd ≅ N.obj Y.snd := (CategoricalPullback.π₂ _ _).mapIso e
  refine CategoricalPullback.mkIso (l el) (n er) ?_
  apply M.map_injective
  have hw := e.hom.w
  dsimp at hw
  have hl' : L.map (l el).hom = e.hom.fst := hl el
  have hn' : N.map (n er).hom = e.hom.snd := hn er
  have ha : F'.map e.hom.fst ≫ a.inv.app Y.fst =
      a.inv.app X.fst ≫ M.map (F.map (l el).hom) := by
    rw [← hl']
    exact a.inv.naturality (l el).hom
  have hb : M.map (G.map (n er).hom) ≫ b.hom.app Y.snd =
      b.hom.app X.snd ≫ G'.map e.hom.snd := by
    rw [← hn']
    exact b.hom.naturality (n er).hom
  simp only [Functor.map_comp]
  apply (cancel_mono (b.hom.app Y.snd)).1
  apply (cancel_epi (a.inv.app X.fst)).1
  simp only [Category.assoc] at hw ⊢
  have hgoalL : a.inv.app X.fst ≫
        M.map (F.map (l el).hom) ≫ M.map Y.iso.hom ≫ b.hom.app Y.snd =
      a.inv.app X.fst ≫ M.map X.iso.hom ≫ b.hom.app X.snd ≫ G'.map e.hom.snd := by
    rw [← Category.assoc, ← ha]
    exact (Category.assoc _ _ _).trans hw
  have hgoalR : a.inv.app X.fst ≫
        M.map X.iso.hom ≫ M.map (G.map (n er).hom) ≫ b.hom.app Y.snd =
      a.inv.app X.fst ≫ M.map X.iso.hom ≫ b.hom.app X.snd ≫ G'.map e.hom.snd :=
    congrArg (fun k => a.inv.app X.fst ≫ M.map X.iso.hom ≫ k) hb
  exact hgoalL.trans hgoalR.symm

private def liftNatIso
    {A C D : Type*} [Category A] [Category C] [Category D]
    (I : C ⥤ D) [I.Faithful]
    (li : ∀ {x x'}, (I.obj x ≅ I.obj x') → (x ≅ x'))
    (hli : ∀ {x x'} (e : I.obj x ≅ I.obj x'), I.map (li e).hom = e.hom)
    {F G : A ⥤ C} (e : F ⋙ I ≅ G ⋙ I) : F ≅ G :=
  NatIso.ofComponents (fun x => li (e.app x)) (by
    intro x y f
    apply I.map_injective
    simp only [Functor.map_comp, hli]
    exact e.hom.naturality f)

private theorem isEquivalence_of_iso_lifts
    {X Y A D : Type*} [Category X] [Category Y] [Category A] [Category D]
    (R : X ⥤ Y) (I : X ⥤ A) (J : Y ⥤ D) (K : A ⥤ D)
    [I.Faithful] [J.Faithful] [K.IsEquivalence]
    (hY : ∀ {y y' : Y} (f : y ⟶ y'), IsIso f)
    (li : ∀ {x x'}, (I.obj x ≅ I.obj x') → (x ≅ x'))
    (hli : ∀ {x x'} (e : I.obj x ≅ I.obj x'), I.map (li e).hom = e.hom)
    (lj : ∀ {y y'}, (J.obj y ≅ J.obj y') → (y ≅ y'))
    (c : R ⋙ J ≅ I ⋙ K)
    (hs : ∀ y, ∃ x, Nonempty (I.obj x ≅ K.objPreimage (J.obj y))) :
    R.IsEquivalence := by
  have : R.Faithful := ⟨by
    intro x x' f g he
    apply I.map_injective
    apply K.map_injective
    have hf := c.hom.naturality f
    have hg := c.hom.naturality g
    dsimp at hf hg
    rw [he] at hf
    exact (cancel_epi (c.hom.app x)).1 (hf.symm.trans hg)⟩
  have : R.Full := ⟨by
    intro x x' f
    let := hY f
    let e := K.preimageIso ((c.app x).symm ≪≫ J.mapIso (asIso f) ≪≫ c.app x')
    refine ⟨(li e).hom, ?_⟩
    apply J.map_injective
    apply (cancel_mono (c.hom.app x')).1
    have hc := c.hom.naturality (li e).hom
    dsimp at hc
    rw [hc, hli]
    simp [e]⟩
  have : R.EssSurj := ⟨by
    intro y
    obtain ⟨x, ⟨e⟩⟩ := hs y
    exact ⟨x, ⟨lj (c.app x ≪≫ K.mapIso e ≪≫ K.objObjPreimageIso (J.obj y))⟩⟩⟩
  exact { }

private abbrev curveFiberToProper (U : B.Schemes) :=
  curveFiberToBoundedProperCore B hZ U ⋙ ObjectProperty.ι _ ⋙ wideSubcategoryInclusion _

private theorem curveFiberToProper_faithful (U : B.Schemes) :
    (curveFiberToProper B hZ U).Faithful := by
  let := curveFiberToBoundedProperCore_faithful B hZ U
  infer_instance

private def curveFiberToProper_preimageIso {U : B.Schemes}
    {X Y : (curvesProjection B hZ).Fiber U}
    (e : (curveFiberToProper B hZ U).obj X ≅ (curveFiberToProper B hZ U).obj Y) :
    X ≅ Y := by
  letI := curveFiberToBoundedProperCore_faithful B hZ U
  letI := curveFiberToBoundedProperCore_full B hZ U
  exact (curveFiberToBoundedProperCore B hZ U).preimageIso
    (ObjectProperty.isoMk _ (WideSubcategory.isoMk e
      (MorphismProperty.isomorphisms.infer_property e.hom)
      (MorphismProperty.isomorphisms.infer_property e.inv)))

private theorem curveFiberToProper_map_preimageIso {U : B.Schemes}
    {X Y : (curvesProjection B hZ).Fiber U}
    (e : (curveFiberToProper B hZ U).obj X ≅ (curveFiberToProper B hZ U).obj Y) :
    (curveFiberToProper B hZ U).map (curveFiberToProper_preimageIso B hZ e).hom =
      e.hom := by
  let := curveFiberToBoundedProperCore_faithful B hZ U
  let := curveFiberToBoundedProperCore_full B hZ U
  change (ObjectProperty.ι _ ⋙ wideSubcategoryInclusion _).map
    ((curveFiberToBoundedProperCore B hZ U).map
      ((curveFiberToBoundedProperCore B hZ U).preimage _)) = _
  rw [Functor.map_preimage]
  rfl

private def curveBaseChangeProperIso
    {U V : B.Schemes} (f : U ⟶ V)
    (bc : Space.ProperPushoutBaseChange B integerBase hZ
      (siteLiftMap B hZ f)) :
    (curvesBaseChangeOfProper B hZ f bc).functor ⋙ curveFiberToProper B hZ U ≅
      curveFiberToProper B hZ V ⋙ bc.functor :=
  isoWhiskerRight (curveBaseChange_transportIso B hZ f bc)
    (ObjectProperty.ι _ ⋙ wideSubcategoryInclusion _)

private def curveBaseChangeTwiceProperIso
    {U V W : B.Schemes} (f : U ⟶ V) (g : V ⟶ W)
    (bf : Space.ProperPushoutBaseChange B integerBase hZ (siteLiftMap B hZ f))
    (bg : Space.ProperPushoutBaseChange B integerBase hZ (siteLiftMap B hZ g)) :
    ((curvesBaseChangeOfProper B hZ g bg).functor ⋙
      (curvesBaseChangeOfProper B hZ f bf).functor) ⋙ curveFiberToProper B hZ U ≅
      curveFiberToProper B hZ W ⋙ (bg.functor ⋙ bf.functor) :=
  isoWhiskerLeft (curvesBaseChangeOfProper B hZ g bg).functor
      (curveBaseChangeProperIso B hZ f bf) ≪≫
    isoWhiskerRight (curveBaseChangeProperIso B hZ g bg) bf.functor

/-- A composite with two cancelling pairs on the right collapses to its left part. -/
private theorem overlap_cancel' {𝒞 : Type*} [Category 𝒞] {V W X Y Z Z' : 𝒞}
    (a : V ⟶ W) (m : W ⟶ X) (cc : X ⟶ Y) (p : Y ⟶ Z) (u : Z ⟶ Z') (v : Z' ⟶ Z) (q : Z ⟶ Y)
    (huv : u ≫ v = 𝟙 Z) (hpq : p ≫ q = 𝟙 Y) :
    (a ≫ m ≫ cc ≫ p ≫ u) ≫ v ≫ q = a ≫ m ≫ cc := by
  simp only [Category.assoc]
  rw [← Category.assoc u v q, huv, Category.id_comp, hpq, Category.comp_id]

private def curveOverlapProperIso
    {T T' S S' : B.Schemes} {i : T ⟶ T'} {f : T ⟶ S}
    {g : T' ⟶ S'} {h : S ⟶ S'}
    (d : Space.ProperPushoutEquivalenceData B integerBase hZ
      (siteLiftMap B hZ i) (siteLiftMap B hZ f)
      (siteLiftMap B hZ g) (siteLiftMap B hZ h)) :
    ((curvesBaseChangeOfProper B hZ h d.fromPushoutToS).functor ⋙
      (curvesBaseChangeOfProper B hZ f d.toOverlapFromS).functor) ⋙
        curveFiberToProper B hZ T ≅
    ((curvesBaseChangeOfProper B hZ g d.fromPushoutToT').functor ⋙
      (curvesBaseChangeOfProper B hZ i d.toOverlapFromT').functor) ⋙
        curveFiberToProper B hZ T :=
  curveBaseChangeTwiceProperIso B hZ f h d.toOverlapFromS d.fromPushoutToS ≪≫
    isoWhiskerLeft (curveFiberToProper B hZ S') d.overlapComparison ≪≫
    (curveBaseChangeTwiceProperIso B hZ i g d.toOverlapFromT' d.fromPushoutToT').symm

private def curveOverlapIso
    {T T' S S' : B.Schemes} {i : T ⟶ T'} {f : T ⟶ S}
    {g : T' ⟶ S'} {h : S ⟶ S'}
    (d : Space.ProperPushoutEquivalenceData B integerBase hZ
      (siteLiftMap B hZ i) (siteLiftMap B hZ f)
      (siteLiftMap B hZ g) (siteLiftMap B hZ h)) :
    (curvesBaseChangeOfProper B hZ h d.fromPushoutToS).functor ⋙
      (curvesBaseChangeOfProper B hZ f d.toOverlapFromS).functor ≅
    (curvesBaseChangeOfProper B hZ g d.fromPushoutToT').functor ⋙
      (curvesBaseChangeOfProper B hZ i d.toOverlapFromT').functor := by
  letI := curveFiberToProper_faithful B hZ T
  exact liftNatIso (curveFiberToProper B hZ T)
    (curveFiberToProper_preimageIso B hZ) (curveFiberToProper_map_preimageIso B hZ)
    (curveOverlapProperIso B hZ d)

private def curveRestriction
    {T T' S S' : B.Schemes} {i : T ⟶ T'} {f : T ⟶ S}
    {g : T' ⟶ S'} {h : S ⟶ S'}
    (d : Space.ProperPushoutEquivalenceData B integerBase hZ
      (siteLiftMap B hZ i) (siteLiftMap B hZ f)
      (siteLiftMap B hZ g) (siteLiftMap B hZ h)) :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
    (⟨(curvesBaseChangeOfProper B hZ h d.fromPushoutToS).functor,
      (curvesBaseChangeOfProper B hZ g d.fromPushoutToT').functor,
      curveOverlapIso B hZ d⟩)

private def curvePullbackToProper
    {T T' S S' : B.Schemes} {i : T ⟶ T'} {f : T ⟶ S}
    {g : T' ⟶ S'} {h : S ⟶ S'}
    (d : Space.ProperPushoutEquivalenceData B integerBase hZ
      (siteLiftMap B hZ i) (siteLiftMap B hZ f)
      (siteLiftMap B hZ g) (siteLiftMap B hZ h)) :=
  CategoricalPullback.map _ _ (curveFiberToProper B hZ S) (curveFiberToProper B hZ T')
    (curveFiberToProper B hZ T) _ _
    (curveBaseChangeProperIso B hZ i d.toOverlapFromT').symm
    (curveBaseChangeProperIso B hZ f d.toOverlapFromS)

private def properCanonicalRestriction
    {T T' S S' : B.Schemes} {i : T ⟶ T'} {f : T ⟶ S}
    {g : T' ⟶ S'} {h : S ⟶ S'}
    (d : Space.ProperPushoutEquivalenceData B integerBase hZ
      (siteLiftMap B hZ i) (siteLiftMap B hZ f)
      (siteLiftMap B hZ g) (siteLiftMap B hZ h)) :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
    (⟨d.fromPushoutToS.functor, d.fromPushoutToT'.functor, d.overlapComparison⟩)

private def properCanonicalRestrictionIso
    {T T' S S' : B.Schemes} {i : T ⟶ T'} {f : T ⟶ S}
    {g : T' ⟶ S'} {h : S ⟶ S'}
    (d : Space.ProperPushoutEquivalenceData B integerBase hZ
      (siteLiftMap B hZ i) (siteLiftMap B hZ f)
      (siteLiftMap B hZ g) (siteLiftMap B hZ h)) :
    d.restrictionFunctor ≅ properCanonicalRestriction B hZ d :=
  NatIso.ofComponents (fun X => CategoricalPullback.mkIso
      (d.restriction_toS.app X) (d.restriction_toT'.app X)
      (d.restriction_overlap X)) (by
    intro X Y a
    apply CategoricalPullback.hom_ext
    · exact d.restriction_toS.hom.naturality a
    · exact d.restriction_toT'.hom.naturality a)

private theorem curveOverlap_map_fac
    {T T' S S' : B.Schemes} {i : T ⟶ T'} {f : T ⟶ S}
    {g : T' ⟶ S'} {h : S ⟶ S'}
    (d : Space.ProperPushoutEquivalenceData B integerBase hZ
      (siteLiftMap B hZ i) (siteLiftMap B hZ f)
      (siteLiftMap B hZ g) (siteLiftMap B hZ h))
    (X : (curvesProjection B hZ).Fiber S') :
    (curveFiberToProper B hZ T).map ((curveOverlapIso B hZ d).hom.app X) ≫
      (curveBaseChangeProperIso B hZ i d.toOverlapFromT').hom.app
        ((curvesBaseChangeOfProper B hZ g d.fromPushoutToT').functor.obj X) ≫
      d.toOverlapFromT'.functor.map
        ((curveBaseChangeProperIso B hZ g d.fromPushoutToT').hom.app X) =
    (curveBaseChangeProperIso B hZ f d.toOverlapFromS).hom.app
        ((curvesBaseChangeOfProper B hZ h d.fromPushoutToS).functor.obj X) ≫
      d.toOverlapFromS.functor.map
        ((curveBaseChangeProperIso B hZ h d.fromPushoutToS).hom.app X) ≫
      d.overlapComparison.hom.app ((curveFiberToProper B hZ S').obj X) := by
  have hm := curveFiberToProper_map_preimageIso B hZ
    ((curveOverlapProperIso B hZ d).app X)
  change (curveFiberToProper B hZ T).map ((curveOverlapIso B hZ d).hom.app X) =
    (curveOverlapProperIso B hZ d).hom.app X at hm
  rw [hm]
  have hexp : (curveOverlapProperIso B hZ d).hom.app X =
      (curveBaseChangeProperIso B hZ f d.toOverlapFromS).hom.app
          ((curvesBaseChangeOfProper B hZ h d.fromPushoutToS).functor.obj X) ≫
        d.toOverlapFromS.functor.map
            ((curveBaseChangeProperIso B hZ h d.fromPushoutToS).hom.app X) ≫
          d.overlapComparison.hom.app ((curveFiberToProper B hZ S').obj X) ≫
            d.toOverlapFromT'.functor.map
                ((curveBaseChangeProperIso B hZ g d.fromPushoutToT').inv.app X) ≫
              (curveBaseChangeProperIso B hZ i d.toOverlapFromT').inv.app
                ((curvesBaseChangeOfProper B hZ g d.fromPushoutToT').functor.obj X) := by
    simp [curveOverlapProperIso, curveBaseChangeTwiceProperIso]
  rw [hexp]
  exact overlap_cancel'
    ((curveBaseChangeProperIso B hZ f d.toOverlapFromS).hom.app
      ((curvesBaseChangeOfProper B hZ h d.fromPushoutToS).functor.obj X))
    (d.toOverlapFromS.functor.map
      ((curveBaseChangeProperIso B hZ h d.fromPushoutToS).hom.app X))
    (d.overlapComparison.hom.app ((curveFiberToProper B hZ S').obj X))
    (d.toOverlapFromT'.functor.map
      ((curveBaseChangeProperIso B hZ g d.fromPushoutToT').inv.app X))
    ((curveBaseChangeProperIso B hZ i d.toOverlapFromT').inv.app
      ((curvesBaseChangeOfProper B hZ g d.fromPushoutToT').functor.obj X))
    ((curveBaseChangeProperIso B hZ i d.toOverlapFromT').hom.app
      ((curvesBaseChangeOfProper B hZ g d.fromPushoutToT').functor.obj X))
    (d.toOverlapFromT'.functor.map
      ((curveBaseChangeProperIso B hZ g d.fromPushoutToT').hom.app X))
    (Iso.inv_hom_id_app _ _)
    (by
      rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app]
      exact d.toOverlapFromT'.functor.map_id _)

private def curveRestrictionToProperIso
    {T T' S S' : B.Schemes} {i : T ⟶ T'} {f : T ⟶ S}
    {g : T' ⟶ S'} {h : S ⟶ S'}
    (d : Space.ProperPushoutEquivalenceData B integerBase hZ
      (siteLiftMap B hZ i) (siteLiftMap B hZ f)
      (siteLiftMap B hZ g) (siteLiftMap B hZ h)) :
    curveRestriction B hZ d ⋙ curvePullbackToProper B hZ d ≅
      curveFiberToProper B hZ S' ⋙ d.restrictionFunctor := by
  let kh := curveBaseChangeProperIso B hZ h d.fromPushoutToS
  let kg := curveBaseChangeProperIso B hZ g d.fromPushoutToT'
  let e : curveRestriction B hZ d ⋙ curvePullbackToProper B hZ d ≅
      curveFiberToProper B hZ S' ⋙ properCanonicalRestriction B hZ d :=
    NatIso.ofComponents (fun X => CategoricalPullback.mkIso
      (kh.app X) (kg.app X) (by
        change d.toOverlapFromS.functor.map (kh.hom.app X) ≫
            d.overlapComparison.hom.app _ =
          _ ≫ d.toOverlapFromT'.functor.map (kg.hom.app X)
        change d.toOverlapFromS.functor.map (kh.hom.app X) ≫
            d.overlapComparison.hom.app ((curveFiberToProper B hZ S').obj X) =
          ((curveBaseChangeProperIso B hZ f d.toOverlapFromS).inv.app
            ((curvesBaseChangeOfProper B hZ h d.fromPushoutToS).functor.obj X) ≫
            (curveFiberToProper B hZ T).map ((curveOverlapIso B hZ d).hom.app X) ≫
            (curveBaseChangeProperIso B hZ i d.toOverlapFromT').hom.app
              ((curvesBaseChangeOfProper B hZ g d.fromPushoutToT').functor.obj X)) ≫
            d.toOverlapFromT'.functor.map (kg.hom.app X)
        simp only [Category.assoc]
        rw [curveOverlap_map_fac, Iso.inv_hom_id_app_assoc])) (by
            intro X Y a
            apply CategoricalPullback.hom_ext
            · exact kh.hom.naturality a
            · exact kg.hom.naturality a)
  exact e ≪≫ isoWhiskerLeft (curveFiberToProper B hZ S')
    (properCanonicalRestrictionIso B hZ d).symm

private theorem curveRestriction_isEquivalence
    {T T' S S' : B.Schemes} {i : T ⟶ T'} {f : T ⟶ S}
    {g : T' ⟶ S'} {h : S ⟶ S'}
    (d : Space.ProperPushoutEquivalenceData B integerBase hZ
      (siteLiftMap B hZ i) (siteLiftMap B hZ f)
      (siteLiftMap B hZ g) (siteLiftMap B hZ h))
    (hthick : Stacks.Thickenings.IsThickening (B.inclusion.map h)) :
    (curveRestriction B hZ d).IsEquivalence := by
  let := curveFiberToProper_faithful B hZ S
  let := curveFiberToProper_faithful B hZ T
  let := curveFiberToProper_faithful B hZ T'
  let := curveFiberToProper_faithful B hZ S'
  let : (curvePullbackToProper B hZ d).Faithful :=
    CategoryTheory.induced_faithful_of_faithful (curveFiberToProper B hZ S)
    (curveFiberToProper B hZ T') (curveFiberToProper B hZ T)
    (curveBaseChangeProperIso B hZ i d.toOverlapFromT').symm
    (curveBaseChangeProperIso B hZ f d.toOverlapFromS)
  let := d.equivalence
  refine isEquivalence_of_iso_lifts (curveRestriction B hZ d)
    (curveFiberToProper B hZ S') (curvePullbackToProper B hZ d) d.restrictionFunctor
    (fun a => ?_)
    (curveFiberToProper_preimageIso B hZ) (curveFiberToProper_map_preimageIso B hZ)
    (categoricalPullbackMap_preimageIso _ _ _ _ _
      (curveFiberToProper_preimageIso B hZ) (curveFiberToProper_map_preimageIso B hZ)
      (curveFiberToProper_preimageIso B hZ) (curveFiberToProper_map_preimageIso B hZ))
    (curveRestrictionToProperIso B hZ d) ?_
  · let : IsGroupoid ((curvesProjection B hZ).Fiber S) :=
      (curvesProjection_isFiberedInGroupoids B hZ).fiber_isGroupoid S
    let : IsGroupoid ((curvesProjection B hZ).Fiber T') :=
      (curvesProjection_isFiberedInGroupoids B hZ).fiber_isGroupoid T'
    exact (CategoricalPullback.isIso_iff _ _ a).2 ⟨inferInstance, inferInstance⟩
  · intro W
    let Z := d.restrictionFunctor.objPreimage ((curvePullbackToProper B hZ d).obj W)
    let e := d.restrictionFunctor.objObjPreimageIso
      ((curvePullbackToProper B hZ d).obj W)
    have hdimW := curveFiberAsProperOver_relativeDimensionLE B hZ W.fst
    have hdimZ : Space.HasRelativeDimensionLE 1 B integerBase hZ
        Z.obj.hom.hom :=
      (properPushout_relativeDimensionLE_iff B hZ d hthick Z).2 <|
        relativeDimensionLE_of_overIso B hZ
          ((ObjectProperty.ι _).mapIso ((CategoricalPullback.π₁ _ _).mapIso e).symm) hdimW
    refine ⟨curveFiberOfProperOver B hZ Z hdimZ, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _ (curveFiberOfProperOver_asProperOver_iso B hZ Z hdimZ)


/-- In a category, the identities `Mi ≫ C₂ = Ci ≫ Bg`, `A ≫ Bi ≫ Mi = Bf ≫ Mf ≫ Lc`,
`Lc ≫ C₂ ≫ Cg = C₂' ≫ Ch` and `Mf ≫ C₂' = Cf ≫ Bh` give
`A ≫ (Bi ≫ Ci) ≫ Bg ≫ Cg = (Bf ≫ Cf) ≫ Bh ≫ Ch`. -/
private theorem overlap_canonical_aux {𝒞 : Type*} [Category 𝒞]
    {X₀ X₁ X₂ X₃ X₄ X₅ Y Z₁ Z₂ W V : 𝒞}
    (A : X₀ ⟶ X₁) (Bi : X₁ ⟶ X₂) (Ci : X₂ ⟶ X₃) (Bg : X₃ ⟶ X₄) (Cg : X₄ ⟶ X₅)
    (Mi : X₂ ⟶ Y) (C₂ : Y ⟶ X₄) (Bf : X₀ ⟶ Z₁) (Mf : Z₁ ⟶ Z₂) (Lc : Z₂ ⟶ Y)
    (C₂' : Z₂ ⟶ W) (Ch : W ⟶ X₅) (Cf : Z₁ ⟶ V) (Bh : V ⟶ W)
    (hi : Mi ≫ C₂ = Ci ≫ Bg)
    (hm : A ≫ Bi ≫ Mi = Bf ≫ Mf ≫ Lc)
    (hc : Lc ≫ C₂ ≫ Cg = C₂' ≫ Ch)
    (hf : Mf ≫ C₂' = Cf ≫ Bh) :
    A ≫ (Bi ≫ Ci) ≫ Bg ≫ Cg = (Bf ≫ Cf) ≫ Bh ≫ Ch := by
  simp only [Category.assoc]
  rw [← reassoc_of% hi, reassoc_of% hm, hc, reassoc_of% hf]

private theorem curveBaseChange_comparison_total
    {U V : B.Schemes} (f : U ⟶ V)
    (bc : Space.ProperPushoutBaseChange B integerBase hZ (siteLiftMap B hZ f))
    (X : (curvesProjection B hZ).Fiber V) :
    ((curvesBaseChangeOfProper B hZ f bc).comparison.app X).totalMap =
      ((curveBaseChangeProperIso B hZ f bc).hom.app X).hom.left ≫
      bc.comparison.app ((curveFiberToProper B hZ V).obj X) := by
  rfl

private theorem curveFiberToProper_map_total
    {U : B.Schemes} {X Y : (curvesProjection B hZ).Fiber U}
    (a : X ⟶ Y) :
    a.1.totalMap = ((curveFiberToProper B hZ U).map a).hom.left := by
  have ha : ((curveFiberToProper B hZ U).map a).hom.left ≫
      (curveFiberAsProperOver_iso B hZ Y).hom.left =
    (curveFiberAsProperOver_iso B hZ X).hom.left ≫ a.1.totalMap :=
    congrArg Over.Hom.left (curveFiberAsProperOver_iso_naturality B hZ U a)
  exact ha.symm

private theorem overIso_hom_inv_id_assoc
    {C : Type*} [Category C] {S : C} {X Y : Over S} (e : X ≅ Y)
    {Z : C} (f : X.left ⟶ Z) : e.hom.left ≫ e.inv.left ≫ f = f := by
  rw [← Category.assoc, ← Over.comp_left, e.hom_inv_id, Over.id_left, Category.id_comp]

private theorem curveOverlap_canonical
    {T T' S S' : B.Schemes} {i : T ⟶ T'} {f : T ⟶ S}
    {g : T' ⟶ S'} {h : S ⟶ S'}
    (d : Space.ProperPushoutEquivalenceData B integerBase hZ
      (siteLiftMap B hZ i) (siteLiftMap B hZ f)
      (siteLiftMap B hZ g) (siteLiftMap B hZ h))
    (hw : siteLiftMap B hZ i ≫ siteLiftMap B hZ g =
      siteLiftMap B hZ f ≫ siteLiftMap B hZ h)
    (X : (curvesProjection B hZ).Fiber S') :
    Functor.Fiber.fiberInclusion.map ((curveOverlapIso B hZ d).hom.app X) ≫
      (curvesBaseChangeOfProper B hZ i d.toOverlapFromT').comparison.app
        ((curvesBaseChangeOfProper B hZ g d.fromPushoutToT').functor.obj X) ≫
      (curvesBaseChangeOfProper B hZ g d.fromPushoutToT').comparison.app X =
    (curvesBaseChangeOfProper B hZ f d.toOverlapFromS).comparison.app
        ((curvesBaseChangeOfProper B hZ h d.fromPushoutToS).functor.obj X) ≫
      (curvesBaseChangeOfProper B hZ h d.fromPushoutToS).comparison.app X := by
  let L := (curvesBaseChangeOfProper B hZ h d.fromPushoutToS).functor.obj X
  let R := (curvesBaseChangeOfProper B hZ g d.fromPushoutToT').functor.obj X
  let LL := (curvesBaseChangeOfProper B hZ f d.toOverlapFromS).functor.obj L
  let RR := (curvesBaseChangeOfProper B hZ i d.toOverlapFromT').functor.obj R
  let a : LL ⟶ RR := (curveOverlapIso B hZ d).hom.app X
  apply CurveFamily.Hom.ext
  · change a.1.baseMap ≫
        ((fiberBaseIso B hZ RR).hom ≫ siteLiftMap B hZ i ≫ (fiberBaseIso B hZ R).inv) ≫
        ((fiberBaseIso B hZ R).hom ≫ siteLiftMap B hZ g ≫ (fiberBaseIso B hZ X).inv) =
      ((fiberBaseIso B hZ LL).hom ≫ siteLiftMap B hZ f ≫ (fiberBaseIso B hZ L).inv) ≫
        ((fiberBaseIso B hZ L).hom ≫ siteLiftMap B hZ h ≫ (fiberBaseIso B hZ X).inv)
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have hb : a.1.baseMap ≫ (fiberBaseIso B hZ RR).hom =
        (fiberBaseIso B hZ LL).hom := fiberBaseIso_naturality B hZ a
    rw [← Category.assoc a.1.baseMap (fiberBaseIso B hZ RR).hom, hb]
    simpa only [Category.assoc] using congrArg
      (fun k => (fiberBaseIso B hZ LL).hom ≫ k ≫ (fiberBaseIso B hZ X).inv) hw
  · change a.1.totalMap ≫
        ((curvesBaseChangeOfProper B hZ i d.toOverlapFromT').comparison.app R).totalMap ≫
        ((curvesBaseChangeOfProper B hZ g d.fromPushoutToT').comparison.app X).totalMap =
      ((curvesBaseChangeOfProper B hZ f d.toOverlapFromS).comparison.app L).totalMap ≫
        ((curvesBaseChangeOfProper B hZ h d.fromPushoutToS).comparison.app X).totalMap
    rw [curveFiberToProper_map_total B hZ a]
    rw [curveBaseChange_comparison_total B hZ i d.toOverlapFromT' R,
      curveBaseChange_comparison_total B hZ g d.fromPushoutToT' X,
      curveBaseChange_comparison_total B hZ f d.toOverlapFromS L,
      curveBaseChange_comparison_total B hZ h d.fromPushoutToS X]
    have hm : ((curveFiberToProper B hZ T).map a).hom.left ≫
        ((curveBaseChangeProperIso B hZ i d.toOverlapFromT').hom.app R).hom.left ≫
          (d.toOverlapFromT'.functor.map
            ((curveBaseChangeProperIso B hZ g d.fromPushoutToT').hom.app X)).hom.left =
        ((curveBaseChangeProperIso B hZ f d.toOverlapFromS).hom.app L).hom.left ≫
          (d.toOverlapFromS.functor.map
            ((curveBaseChangeProperIso B hZ h d.fromPushoutToS).hom.app X)).hom.left ≫
            (d.overlapComparison.hom.app ((curveFiberToProper B hZ S').obj X)).hom.left :=
      congrArg (fun k => k.hom.left) (curveOverlap_map_fac B hZ d X)
    have hi := d.toOverlapFromT'.comparison.naturality
      ((curveBaseChangeProperIso B hZ g d.fromPushoutToT').hom.app X)
    have hf := d.toOverlapFromS.comparison.naturality
      ((curveBaseChangeProperIso B hZ h d.fromPushoutToS).hom.app X)
    have hc := d.overlapComparison_canonical ((curveFiberToProper B hZ S').obj X)
    exact overlap_canonical_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ hi hm hc hf


/-- The data of Stacks 0D1J for the four base schemes of an affine thickening pushout, read in
the slice category over `integerBase`. -/
private noncomputable def properPushoutData
    (rs : Space.ProperPushoutRS B integerBase hZ)
    {T T' S S' : B.Schemes}
    (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
    (hi : Stacks.Thickenings.IsThickening (B.inclusion.map i))
    [IsAffineHom (B.inclusion.map f)]
    (hsq : IsPushout (B.inclusion.map i) (B.inclusion.map f)
      (B.inclusion.map g) (B.inclusion.map h)) :
    Space.ProperPushoutEquivalenceData B integerBase hZ
      (siteLiftMap B hZ i) (siteLiftMap B hZ f)
      (siteLiftMap B hZ g) (siteLiftMap B hZ h) :=
  rs (siteLiftMap B hZ i) (siteLiftMap B hZ f) (siteLiftMap B hZ g) (siteLiftMap B hZ h)
    hi (by change IsAffineHom (B.inclusion.map f); infer_instance) hsq

/-- **Stacks 0D56 from Stacks 0D1J.** For a pushout of schemes along a thickening
`i : T ⟶ T'` and an affine morphism `f : T ⟶ S`, the canonical restriction functor from the
families of curves over the pushout `S'` to the compatible pairs of families over `S` and `T'`
is an equivalence, given the statement `rs` of Stacks 0D1J — the same assertion for finitely
presented, flat and proper algebraic spaces. -/
@[no_expose]
noncomputable def curvePushoutEquivalence
    (rs : Space.ProperPushoutRS B integerBase hZ)
    {T T' S S' : B.Schemes}
    (i : T ⟶ T') (f : T ⟶ S) (g : T' ⟶ S') (h : S ⟶ S')
    (hi : Stacks.Thickenings.IsThickening (B.inclusion.map i))
    [IsAffineHom (B.inclusion.map f)]
    (hsq : IsPushout (B.inclusion.map i) (B.inclusion.map f)
      (B.inclusion.map g) (B.inclusion.map h)) :
    CurvePushoutEquivalenceData B hZ i f g h := by
  let d := properPushoutData B hZ rs i f g h hi hsq
  refine {
    toOverlapFromS := curvesBaseChangeOfProper B hZ f d.toOverlapFromS
    toOverlapFromT' := curvesBaseChangeOfProper B hZ i d.toOverlapFromT'
    fromPushoutToS := curvesBaseChangeOfProper B hZ h d.fromPushoutToS
    fromPushoutToT' := curvesBaseChangeOfProper B hZ g d.fromPushoutToT'
    overlapComparison := curveOverlapIso B hZ d
    overlapComparison_canonical :=
      curveOverlap_canonical B hZ d (siteLift_isPushout B hZ i f g h hsq).w
    restrictionFunctor := curveRestriction B hZ d
    equivalence :=
      curveRestriction_isEquivalence B hZ d (pushout_map_isThickening B i f g h hi hsq)
    restriction_toS := Iso.refl _
    restriction_toT' := Iso.refl _
    restriction_overlap := ?_ }
  intro X
  change (curvesBaseChangeOfProper B hZ f d.toOverlapFromS).functor.map (𝟙 _) ≫
      (curveOverlapIso B hZ d).hom.app X =
    (curveOverlapIso B hZ d).hom.app X ≫
      (curvesBaseChangeOfProper B hZ i d.toOverlapFromT').functor.map (𝟙 _)
  simp

end AlgebraicGeometry

end
