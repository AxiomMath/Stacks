module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.Deformation.CofiberedPresentation.Groupoid
public import StacksFrontier.Deformation.Cofibered.Over

/-!
# The morphism from the quotient of a presentation

A presentation of a category cofibered in groupoids gives a canonical morphism from the
quotient of its groupoid in functors — the Grothendieck construction of the evaluated
groupoids — to the category being presented. The morphism is fully faithful, and it is an
equivalence exactly when the original morphism from the category of elements is essentially
surjective.

The morphism is built fibrewise: over `T`, an arrow of the evaluated groupoid is an element of
the arrow functor, which the presentation identifies with a vertical isomorphism between the
images in `F` of its source and target. Fullness uses cofiberedness of `p` to factor a given
morphism through the image of a chosen lift and then recognizes the remaining vertical
isomorphism as an arrow of the presentation; faithfulness reduces to triviality of the
stabilizer, which follows from the identification of the arrow functor with the two-fibre
product.

## Main definitions

* `Deformation.presentationMorphism`: the morphism from the quotient, together with the
  equations saying that it lies over the base and recovers the original morphism.

## Main results

* `Deformation.presentationMorphism_full` and `Deformation.presentationMorphism_faithful`:
  full faithfulness.
* `Deformation.presentationMorphism_isEquivalence_iff`: the morphism is an equivalence exactly
  when the original morphism is essentially surjective.

## Implementation notes

The morphism is specified to lie over the base and to agree with the original functor after
the canonical map from the category of elements, including the universe lift used in the
construction of the presentation groupoid. These equations record the naturality of the
construction. A presentation is passed explicitly, so the results apply in particular to the
presentation produced by `Deformation.presentationGroupoid`. Fullness and the equivalence
criterion require the target to be cofibered in groupoids; faithfulness holds for any target
category.

## References

* [Stacks Project, Tag 06KZ](https://stacks.math.columbia.edu/tag/06KZ)
-/

@[expose] public section

open CategoryTheory

universe u v w u₁ uU

namespace Deformation

attribute [local implicit_reducible]
  CategoryTheory.uliftFunctor PresentationGroupoid.toGroupoidInFunctors
  PresentationArrow.comp TwoFibreProductOver.fst TwoFibreProductOver.snd

variable {C : Type u} [Category.{v} C]
variable {F : Type u₁} [Category.{w} F]
variable (p : F ⥤ C) (U : C ⥤ Type uU)
variable (f : U.Elements ⥤ F)
variable (over : f ⋙ p = Functor.Elements.π U)
variable (P : PresentationGroupoid p U f over)

private lemma elements_eqToHom_val {X Y : U.Elements} (h : X = Y) :
    (eqToHom h).hom = eqToHom (congrArg (fun z : U.Elements => z.obj) h) := by
  cases h
  rfl

/-- If a functor sends `e.hom` to `g` and `g ≫ g' = 𝟙 _`, then it sends `e.inv` to `g'`. -/
private lemma map_inv_eq_of_map_hom {D : Type*} [Category D] {E : Type*} [Category E]
    (G : D ⥤ E) {A B : D} (e : A ≅ B) {g : G.obj A ⟶ G.obj B} {g' : G.obj B ⟶ G.obj A}
    (he : G.map e.hom = g) (hg : g ≫ g' = 𝟙 _) : G.map e.inv = g' := by
  apply (cancel_epi (G.map e.hom)).mp
  rw [← G.map_comp, e.hom_inv_id, G.map_id, he, hg]

@[implicit_reducible]
private def normalizedIso {T : C} (r : PresentationArrow p U f over T)
    {x y : U.obj T} (hs : r.source = x) (ht : r.target = y) :
    f.obj (U.elementsMk T x) ≅ f.obj (U.elementsMk T y) :=
  eqToIso (congrArg (fun z => f.obj (U.elementsMk T z)) hs.symm) ≪≫ r.iso.symm ≪≫
    eqToIso (congrArg (fun z => f.obj (U.elementsMk T z)) ht)

private lemma normalizedIso_comp {T : C}
    (a b : PresentationArrow p U f over T)
    {x y z : U.obj T} (ha : a.source = y) (ha' : a.target = z)
    (hb : b.source = x) (hb' : b.target = y)
    (hs : (PresentationArrow.comp p U f over a b
      (ha.trans hb'.symm)).source = x)
    (ht : (PresentationArrow.comp p U f over a b
      (ha.trans hb'.symm)).target = z) :
    normalizedIso p U f over (PresentationArrow.comp p U f over a b
      (ha.trans hb'.symm)) hs ht =
      normalizedIso p U f over b hb hb' ≪≫ normalizedIso p U f over a ha ha' := by
  cases a; cases b
  dsimp only at ha ha' hb hb'
  subst_vars
  ext
  simp [normalizedIso, PresentationArrow.comp]

@[implicit_reducible]
private noncomputable def arrowIso (T : C) (a : P.arrows.obj T)
    {x y : P.toGroupoidInFunctors.Evaluation T}
    (hs : P.source.app T a = x) (ht : P.target.app T a = y) :
    f.obj (U.elementsMk T x.down) ≅ f.obj (U.elementsMk T y.down) :=
  normalizedIso p U f over (P.arrowEquiv T a)
    ((P.arrowEquiv_source T a).trans (congrArg ULift.down hs))
    ((P.arrowEquiv_target T a).trans (congrArg ULift.down ht))

private lemma arrowIso_comp (T : C) (a b : P.arrows.obj T)
    {x y z : P.toGroupoidInFunctors.Evaluation T}
    (ha : P.source.app T a = y) (ha' : P.target.app T a = z)
    (hb : P.source.app T b = x) (hb' : P.target.app T b = y)
    (hc : P.source.app T a = P.target.app T b)
    (hs : P.source.app T (P.comp.app T ⟨(a, b), hc⟩) = x)
    (ht : P.target.app T (P.comp.app T ⟨(a, b), hc⟩) = z) :
    arrowIso p U f over P T (P.comp.app T ⟨(a, b), hc⟩) hs ht =
      arrowIso p U f over P T b hb hb' ≪≫ arrowIso p U f over P T a ha ha' := by
  simp only [arrowIso, P.arrowEquiv_comp]
  apply normalizedIso_comp

@[implicit_reducible]
private noncomputable def fiberIso (T : C)
    {x y : P.toGroupoidInFunctors.Evaluation T} (a : x ⟶ y) :
    f.obj (U.elementsMk T x.down) ≅ f.obj (U.elementsMk T y.down) :=
  arrowIso p U f over P T (P.toGroupoidInFunctors.evaluationArrowEquiv T x y a).1
    (P.toGroupoidInFunctors.evaluationArrowEquiv T x y a).2.1
    (P.toGroupoidInFunctors.evaluationArrowEquiv T x y a).2.2

private lemma fiberIso_comp (T : C)
    {x y z : P.toGroupoidInFunctors.Evaluation T} (a : x ⟶ y) (b : y ⟶ z) :
    fiberIso p U f over P T (a ≫ b) =
      fiberIso p U f over P T a ≪≫ fiberIso p U f over P T b := by
  simp only [fiberIso, P.toGroupoidInFunctors.evaluationArrowEquiv_comp]
  apply arrowIso_comp

private lemma fiberIso_id (T : C) (x : P.toGroupoidInFunctors.Evaluation T) :
    fiberIso p U f over P T (𝟙 x) = Iso.refl _ := by
  have h := congrArg Iso.hom (fiberIso_comp p U f over P T (𝟙 x) (𝟙 x))
  simp only [Category.id_comp, Iso.trans_hom] at h
  apply Iso.ext
  apply (cancel_epi (fiberIso p U f over P T (𝟙 x)).hom).mp
  simpa using h.symm

@[implicit_reducible]
private noncomputable def presentationFiberFunctor (T : C) :
    P.toGroupoidInFunctors.Evaluation T ⥤ F where
  obj x := f.obj (U.elementsMk T x.down)
  map a := (fiberIso p U f over P T a).hom
  map_id x := by rw [fiberIso_id]; rfl
  map_comp a b := by rw [fiberIso_comp]; rfl

private lemma presentationFiberFunctor_map_eqToHom (T : C)
    {x y : P.toGroupoidInFunctors.Evaluation T} (h : x = y) :
    (presentationFiberFunctor p U f over P T).map (eqToHom h) =
      eqToHom (congrArg
        (fun z : P.toGroupoidInFunctors.Evaluation T => f.obj (U.elementsMk T z.down)) h) := by
  cases h
  exact (presentationFiberFunctor p U f over P T).map_id x

@[implicit_reducible]
private def relationIso :
    (NatTrans.mapElements P.source ⋙ (uliftElementsEquivalence U).inverse) ⋙ f ≅
    (NatTrans.mapElements P.target ⋙ (uliftElementsEquivalence U).inverse) ⋙ f :=
  Functor.isoWhiskerRight P.sourceProjectionIso.symm f ≪≫
    Functor.isoWhiskerLeft P.fibreProductEquivalence.functor
      (TwoFibreProductOver.psiIso (Functor.Elements.π U) (Functor.Elements.π U) p f f).symm ≪≫
    Functor.isoWhiskerRight P.targetProjectionIso f

private lemma arrowIso_eq (T : C) (a : P.arrows.obj T)
    {x y : P.toGroupoidInFunctors.Evaluation T}
    (hs : P.source.app T a = x) (ht : P.target.app T a = y) :
    arrowIso p U f over P T a hs ht =
      eqToIso (congrArg (fun z : ULift.{w} (U.obj T) => f.obj (U.elementsMk T z.down)) hs.symm) ≪≫
        (relationIso p U f over P).app (P.arrows.elementsMk T a) ≪≫
      eqToIso (congrArg (fun z : ULift.{w} (U.obj T) => f.obj (U.elementsMk T z.down)) ht) := by
  subst x; subst y
  ext
  simp only [arrowIso, normalizedIso, P.arrowEquiv_iso, relationIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    eqToIso.hom, eqToIso.inv, Functor.mapIso_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    TwoFibreProductOver.psiIso_inv_app,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

private lemma arrowIso_naturality {T S : C} (k : T ⟶ S) (a : P.arrows.obj T)
    {x y : P.toGroupoidInFunctors.Evaluation T}
    (hs : P.source.app T a = x) (ht : P.target.app T a = y)
    (hs' : P.source.app S (P.arrows.map k a) = P.toGroupoidInFunctors.objects.map k x)
    (ht' : P.target.app S (P.arrows.map k a) = P.toGroupoidInFunctors.objects.map k y) :
    f.map (⟨k, rfl⟩ : U.elementsMk T x.down ⟶ U.elementsMk S (U.map k x.down)) ≫
      (arrowIso p U f over P S (P.arrows.map k a) hs' ht').hom =
    (arrowIso p U f over P T a hs ht).hom ≫
      f.map (⟨k, rfl⟩ : U.elementsMk T y.down ⟶ U.elementsMk S (U.map k y.down)) := by
  subst x; subst y
  simp only [arrowIso_eq, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  have h : f.map ((NatTrans.mapElements P.source ⋙ (uliftElementsEquivalence U).inverse).map
        (⟨k, rfl⟩ : P.arrows.elementsMk T a ⟶ P.arrows.elementsMk S (P.arrows.map k a))) ≫
      ((relationIso p U f over P).app (P.arrows.elementsMk S (P.arrows.map k a))).hom =
      ((relationIso p U f over P).app (P.arrows.elementsMk T a)).hom ≫
        f.map ((NatTrans.mapElements P.target ⋙ (uliftElementsEquivalence U).inverse).map
          (⟨k, rfl⟩ : P.arrows.elementsMk T a ⟶ P.arrows.elementsMk S (P.arrows.map k a))) :=
    (relationIso p U f over P).hom.naturality _
  have hmap (n : P.arrows ⟶ U ⋙ uliftFunctor.{w})
      (hn : n.app S (P.arrows.map k a) = (U ⋙ uliftFunctor.{w}).map k (n.app T a)) :
      f.map (⟨k, rfl⟩ : U.elementsMk T (n.app T a).down ⟶
        U.elementsMk S (U.map k (n.app T a).down)) ≫
        eqToHom (congrArg (fun z : ULift.{w} (U.obj S) => f.obj (U.elementsMk S z.down)) hn.symm) =
      f.map ((NatTrans.mapElements n ⋙
        (uliftElementsEquivalence U).inverse).map
          (⟨k, rfl⟩ : P.arrows.elementsMk T a ⟶ P.arrows.elementsMk S (P.arrows.map k a))) := by
    rw [← eqToHom_map f (congrArg (fun z : ULift.{w} (U.obj S) => U.elementsMk S z.down) hn.symm),
      ← f.map_comp]
    congr 1
    apply Functor.Elements.hom_ext
    simp only [Functor.Elements.comp_hom, elements_eqToHom_val]
    show k ≫ eqToHom (_ : S = S) = k
    simp
  rw [← Category.assoc, hmap P.source hs', ← Category.assoc]
  rw [h]
  rw [Category.assoc]
  rw [← hmap P.target ht']
  simp

@[implicit_reducible]
private noncomputable def fiberTransition {T S : C} (k : T ⟶ S) :
    presentationFiberFunctor p U f over P T ⟶
      evaluationMap P.toGroupoidInFunctors k ⋙ presentationFiberFunctor p U f over P S where
  app x := f.map ⟨k, rfl⟩
  naturality x y a := by
    dsimp only [presentationFiberFunctor, Functor.comp_map]
    unfold fiberIso
    simp only [evaluationMap_map_arrow]
    exact (arrowIso_naturality p U f over P k _ _ _ _ _).symm

private lemma fiberTransition_id (T : C) :
    fiberTransition p U f over P (𝟙 T) = eqToHom (by
      have h := (evaluationFunctor P.toGroupoidInFunctors).map_id T
      have h' := congrArg Cat.Hom.toFunctor h
      change evaluationMap P.toGroupoidInFunctors (𝟙 T) = 𝟭 _ at h'
      rw [h', Functor.id_comp]) := by
  ext x
  dsimp [fiberTransition]
  simp only [eqToHom_app]
  rw [← eqToHom_map f (show U.elementsMk T x.down =
      U.elementsMk T (U.map (𝟙 T) x.down) by simp)]
  congr 1
  apply Functor.Elements.hom_ext
  simp [elements_eqToHom_val]

private lemma fiberTransition_comp {T S V : C} (k : T ⟶ S) (l : S ⟶ V) :
    fiberTransition p U f over P (k ≫ l) =
      fiberTransition p U f over P k ≫
        Functor.whiskerLeft (evaluationMap P.toGroupoidInFunctors k)
          (fiberTransition p U f over P l) ≫ eqToHom (by
            have h := (evaluationFunctor P.toGroupoidInFunctors).map_comp k l
            have h' := congrArg Cat.Hom.toFunctor h
            change evaluationMap P.toGroupoidInFunctors (k ≫ l) =
              evaluationMap P.toGroupoidInFunctors k ⋙
                evaluationMap P.toGroupoidInFunctors l at h'
            rw [h']; rfl) := by
  ext x
  dsimp [fiberTransition]
  simp only [eqToHom_app]
  rw [← eqToHom_map f (show U.elementsMk V (U.map l (U.map k x.down)) =
      U.elementsMk V (U.map (k ≫ l) x.down) by simp)]
  simp only [← f.map_comp]
  congr 1
  apply Functor.Elements.hom_ext
  simp [elements_eqToHom_val]

@[implicit_reducible]
private noncomputable def presentationFunctor :
    Grothendieck (evaluationFunctor P.toGroupoidInFunctors) ⥤ F where
  obj X := (presentationFiberFunctor p U f over P X.base).obj X.fiber
  map {X Y} k := (fiberTransition p U f over P k.base).app X.fiber ≫
    (presentationFiberFunctor p U f over P Y.base).map k.fiber
  map_id X := by
    have hid : (evaluationMap P.toGroupoidInFunctors (𝟙 X.base)).obj X.fiber = X.fiber := by
      simp [evaluationMap]
    change (fiberTransition p U f over P (𝟙 X.base)).app X.fiber ≫
        (presentationFiberFunctor p U f over P X.base).map (eqToHom hid) =
      𝟙 ((presentationFiberFunctor p U f over P X.base).obj X.fiber)
    rw [presentationFiberFunctor_map_eqToHom, fiberTransition_id]
    simp
  map_comp {X Y Z} k l := by
    have hc : (evaluationMap P.toGroupoidInFunctors (k.base ≫ l.base)).obj X.fiber =
        (evaluationMap P.toGroupoidInFunctors l.base).obj
          ((evaluationMap P.toGroupoidInFunctors k.base).obj X.fiber) := by
      simp [evaluationMap]
    change (fiberTransition p U f over P (k.base ≫ l.base)).app X.fiber ≫
        (presentationFiberFunctor p U f over P Z.base).map
          (eqToHom hc ≫ (evaluationMap P.toGroupoidInFunctors l.base).map k.fiber ≫ l.fiber) =
      ((fiberTransition p U f over P k.base).app X.fiber ≫
          (presentationFiberFunctor p U f over P Y.base).map k.fiber) ≫
        ((fiberTransition p U f over P l.base).app Y.fiber ≫
          (presentationFiberFunctor p U f over P Z.base).map l.fiber)
    have hnat : (presentationFiberFunctor p U f over P Y.base).map k.fiber ≫
          (fiberTransition p U f over P l.base).app Y.fiber =
        (fiberTransition p U f over P l.base).app
            ((evaluationMap P.toGroupoidInFunctors k.base).obj X.fiber) ≫
          (presentationFiberFunctor p U f over P Z.base).map
            ((evaluationMap P.toGroupoidInFunctors l.base).map k.fiber) :=
      (fiberTransition p U f over P l.base).naturality k.fiber
    rw [Functor.map_comp, Functor.map_comp, presentationFiberFunctor_map_eqToHom,
      fiberTransition_comp]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [reassoc_of% hnat]

private lemma normalizedIso_vertical {T : C}
    (r : PresentationArrow p U f over T)
    {x y : U.obj T} (hs : r.source = x) (ht : r.target = y) :
    p.map (normalizedIso p U f over r hs ht).hom =
      eqToHom (elementBaseEq p U f over T x) ≫
        eqToHom (elementBaseEq p U f over T y).symm := by
  subst x; subst y
  dsimp [normalizedIso]
  simp only [Category.id_comp, Category.comp_id]
  exact map_inv_eq_of_map_hom p r.iso r.vertical (by simp)

private lemma fiberIso_vertical (T : C)
    {x y : P.toGroupoidInFunctors.Evaluation T} (a : x ⟶ y) :
    p.map (fiberIso p U f over P T a).hom =
      eqToHom (elementBaseEq p U f over T x.down) ≫
        eqToHom (elementBaseEq p U f over T y.down).symm := by
  unfold fiberIso arrowIso
  apply normalizedIso_vertical

private lemma presentationFunctor_over : presentationFunctor p U f over P ⋙ p =
    Grothendieck.forget (evaluationFunctor P.toGroupoidInFunctors) := by
  refine Functor.ext (fun X => elementBaseEq p U f over X.base X.fiber.down) ?_
  intro X Y k
  show p.map (f.map (⟨k.base, rfl⟩ : U.elementsMk X.base X.fiber.down ⟶
    U.elementsMk Y.base (U.map k.base X.fiber.down)) ≫
      (fiberIso p U f over P Y.base k.fiber).hom) = _
  rw [p.map_comp, fiberIso_vertical]
  have h := Functor.congr_hom over
    (⟨k.base, rfl⟩ : U.elementsMk X.base X.fiber.down ⟶
      U.elementsMk Y.base (U.map k.base X.fiber.down))
  dsimp only [Functor.comp_map] at h
  rw [h]
  simp
  rfl

private lemma presentationFunctor_comp_quotient :
    (uliftElementsEquivalence U).functor ⋙
      quotientMorphism P.toGroupoidInFunctors ⋙
        presentationFunctor p U f over P = f := by
  refine Functor.ext (F := _) (G := f) (fun _ => rfl) ?_
  intro X Y k
  show f.map (⟨k.hom, rfl⟩ : U.elementsMk X.1 X.2 ⟶
    U.elementsMk Y.1 (U.map k.hom X.2)) ≫
    (presentationFiberFunctor p U f over P Y.1).map (eqToHom (congrArg ULift.up k.map_val)) = _
  rw [eqToHom_map]
  show f.map (⟨k.hom, rfl⟩ : U.elementsMk X.1 X.2 ⟶
    U.elementsMk Y.1 (U.map k.hom X.2)) ≫ eqToHom _ = _
  rw [← eqToHom_map f (congrArg (U.elementsMk Y.1) k.map_val), ← f.map_comp]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  congr 1
  apply Functor.Elements.hom_ext
  simp [elements_eqToHom_val]

private lemma fiberIso_surjective (T : C)
    {x y : P.toGroupoidInFunctors.Evaluation T} (e : f.obj (U.elementsMk T x.down) ≅ f.obj (U.elementsMk T y.down))
    (he : p.map e.hom = eqToHom (elementBaseEq p U f over T x.down) ≫
      eqToHom (elementBaseEq p U f over T y.down).symm) :
    ∃ a : x ⟶ y, fiberIso p U f over P T a = e := by
  have hei : p.map e.inv = eqToHom (elementBaseEq p U f over T y.down) ≫
      eqToHom (elementBaseEq p U f over T x.down).symm :=
    map_inv_eq_of_map_hom p e he (by simp)
  let r : PresentationArrow p U f over T := ⟨y.down, x.down, e.symm, hei⟩
  let a := (P.arrowEquiv T).symm r
  have hs : P.source.app T a = x := by
    apply ULift.ext
    rw [← P.arrowEquiv_source]
    simp [a, r]
  have ht : P.target.app T a = y := by
    apply ULift.ext
    rw [← P.arrowEquiv_target]
    simp [a, r]
  refine ⟨(P.toGroupoidInFunctors.evaluationArrowEquiv T x y).symm ⟨a, hs, ht⟩, ?_⟩
  simp only [fiberIso, Equiv.apply_symm_apply]
  simp only [arrowIso, a, Equiv.apply_symm_apply]
  ext
  simp [normalizedIso, r]

private lemma cofibered_isIso (hp : IsCofiberedInGroupoids p)
    {a b : F} (t : a ⟶ b) [IsIso (p.map t)] : IsIso t := by
  have : p.op.IsStronglyCartesian (p.map t).op t.op := hp.isStronglyCartesian t.op
  have : IsIso t.op := Functor.IsStronglyCartesian.isIso_of_base_isIso p.op (p.map t).op t.op
  exact isIso_of_op t

private lemma presentationFunctor_full (hp : IsCofiberedInGroupoids p) :
    (presentationFunctor p U f over P).Full := by
  constructor
  intro X Y m
  let hx := elementBaseEq p U f over X.base X.fiber.down
  let hy := elementBaseEq p U f over Y.base Y.fiber.down
  let k : X.base ⟶ Y.base := eqToHom hx.symm ≫ p.map m ≫ eqToHom hy
  let b : U.elementsMk X.base X.fiber.down ⟶
      U.elementsMk Y.base (U.map k X.fiber.down) := ⟨k, rfl⟩
  let hz := elementBaseEq p U f over Y.base (U.map k X.fiber.down)
  have hb : p.map (f.map b) = eqToHom hx ≫ k ≫ eqToHom hz.symm :=
    Functor.congr_hom over b
  obtain ⟨t, ⟨ht, ht'⟩, _⟩ := exists_unique_cofibered_factor hp (f.map b) m
    (eqToHom hz ≫ eqToHom hy.symm) (by rw [hb]; simp [k])
  have : IsIso (p.map t) := by rw [ht]; infer_instance
  have : IsIso t := cofibered_isIso p hp t
  obtain ⟨a, ha⟩ := fiberIso_surjective p U f over P Y.base
    (x := (evaluationMap P.toGroupoidInFunctors k).obj X.fiber)
    (y := Y.fiber) (asIso t) ht
  refine ⟨⟨k, a⟩, ?_⟩
  show f.map b ≫ (fiberIso p U f over P Y.base a).hom = m
  rw [ha]
  exact ht'

private lemma relation_lift {A B : P.arrows.Elements}
    (a : (NatTrans.mapElements P.target ⋙ (uliftElementsEquivalence U).inverse).obj A ⟶
      (NatTrans.mapElements P.target ⋙ (uliftElementsEquivalence U).inverse).obj B)
    (b : (NatTrans.mapElements P.source ⋙ (uliftElementsEquivalence U).inverse).obj A ⟶
      (NatTrans.mapElements P.source ⋙ (uliftElementsEquivalence U).inverse).obj B)
    (hab : a.hom = b.hom)
    (hw : f.map b ≫ (relationIso p U f over P).hom.app B =
      (relationIso p U f over P).hom.app A ≫ f.map a) :
    ∃ k : A ⟶ B, k.hom = a.hom := by
  let α := P.targetProjectionIso
  let β := P.sourceProjectionIso
  let E := P.fibreProductEquivalence.functor
  let a' := α.hom.app A ≫ a ≫ α.inv.app B
  let b' := β.hom.app A ≫ b ≫ β.inv.app B
  have hα (X : P.arrows.Elements) : (Functor.Elements.π U).map (α.hom.app X) =
      eqToHom ((E.obj X).hx.trans (Functor.congr_obj P.fibreProductOverBase X)) :=
    P.targetProjectionIso_vertical X
  have hβ (X : P.arrows.Elements) : (Functor.Elements.π U).map (β.hom.app X) =
      eqToHom ((E.obj X).hy.trans (Functor.congr_obj P.fibreProductOverBase X)) :=
    P.sourceProjectionIso_vertical X
  have hα' (X : P.arrows.Elements) : (Functor.Elements.π U).map (α.inv.app X) =
      eqToHom ((E.obj X).hx.trans (Functor.congr_obj P.fibreProductOverBase X)).symm :=
    map_inv_eq_of_map_hom _ (α.app X) (hα X) (by simp)
  have hβ' (X : P.arrows.Elements) : (Functor.Elements.π U).map (β.inv.app X) =
      eqToHom ((E.obj X).hy.trans (Functor.congr_obj P.fibreProductOverBase X)).symm :=
    map_inv_eq_of_map_hom _ (β.app X) (hβ X) (by simp)
  have hbase : eqToHom (E.obj A).hy.symm ≫ (Functor.Elements.π U).map b' ≫
      eqToHom (E.obj B).hy =
      eqToHom (E.obj A).hx.symm ≫ (Functor.Elements.π U).map a' ≫
      eqToHom (E.obj B).hx := by
    simp only [a', b', Functor.map_comp, hα, hβ, hα', hβ',
      Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    exact congrArg (fun t => eqToHom (Functor.congr_obj P.fibreProductOverBase A) ≫ t ≫
      eqToHom (Functor.congr_obj P.fibreProductOverBase B).symm) hab.symm
  have hwi := congrArg (fun t => (relationIso p U f over P).inv.app A ≫ t ≫
    (relationIso p U f over P).inv.app B) hw
  simp only [Category.assoc, Iso.hom_inv_id_app, Iso.inv_hom_id_app_assoc] at hwi
  have hw' : f.map a' ≫ (E.obj B).iso.hom = (E.obj A).iso.hom ≫ f.map b' := by
    have hh := congrArg (fun t => f.map (α.hom.app A) ≫ t ≫ f.map (β.inv.app B)) hwi.symm
    simp only [relationIso, Iso.trans_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.symm_inv, TwoFibreProductOver.psiIso_hom_app] at hh
    have hA : f.map (α.hom.app A) ≫ f.map (α.inv.app A) = 𝟙 _ := by
      rw [← f.map_comp]; simp
    have hB : f.map (β.hom.app B) ≫ f.map (β.inv.app B) = 𝟙 _ := by
      rw [← f.map_comp]; simp
    dsimp only [α, β, E, a', b'] at *
    simp only [Functor.map_comp, Category.assoc] at hh ⊢
    simp only [reassoc_of% hA, hB] at hh
    dsimp only [Functor.comp_obj, TwoFibreProductOver.snd_obj,
      NatTrans.mapElements, NatTrans.mapElements, uliftElementsEquivalence] at hh
    simp only [Category.id_comp, Category.comp_id] at hh
    exact hh
  let r : E.obj A ⟶ E.obj B := TwoFibreProductOver.Hom.mk' a' b' hbase hw'
  obtain ⟨k, hk⟩ := E.map_surjective r
  refine ⟨k, ?_⟩
  have hnat := α.hom.naturality k
  change (E.map k).a ≫ α.hom.app B =
    α.hom.app A ≫ (NatTrans.mapElements P.target ⋙
      (uliftElementsEquivalence U).inverse).map k at hnat
  rw [hk] at hnat
  change (α.hom.app A ≫ a ≫ α.inv.app B) ≫ α.hom.app B = _ at hnat
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hnat
  have hh := (cancel_epi (α.hom.app A)).mp hnat
  exact (congrArg Functor.Elements.Hom.hom hh).symm

private lemma arrow_map_of_square {T S : C} (a : P.arrows.obj T) (b : P.arrows.obj S)
    {x y : P.toGroupoidInFunctors.Evaluation T} {x' y' : P.toGroupoidInFunctors.Evaluation S}
    (ha : P.source.app T a = x) (ha' : P.target.app T a = y)
    (hb : P.source.app S b = x') (hb' : P.target.app S b = y')
    (u : U.elementsMk T y.down ⟶ U.elementsMk S y'.down)
    (v : U.elementsMk T x.down ⟶ U.elementsMk S x'.down)
    (huv : u.hom = v.hom)
    (hw : f.map v ≫ (arrowIso p U f over P S b hb hb').hom =
      (arrowIso p U f over P T a ha ha').hom ≫ f.map u) :
    P.arrows.map u.hom a = b := by
  subst x; subst y; subst x'; subst y'
  have h : f.map v ≫ (relationIso p U f over P).hom.app (P.arrows.elementsMk S b) =
      (relationIso p U f over P).hom.app (P.arrows.elementsMk T a) ≫ f.map u := by
    simp only [arrowIso_eq, eqToIso_refl, Iso.refl_trans, Iso.trans_refl] at hw
    exact hw
  obtain ⟨k, hk⟩ := relation_lift p U f over P (A := P.arrows.elementsMk T a)
    (B := P.arrows.elementsMk S b) u v huv h
  exact hk ▸ k.map_val

private lemma fiber_stabilizer_trivial {T S : C} (k : T ⟶ S)
    (x : P.toGroupoidInFunctors.Evaluation T)
    (d : (evaluationMap P.toGroupoidInFunctors k).obj x ⟶
      (evaluationMap P.toGroupoidInFunctors k).obj x)
    (h : f.map (⟨k, rfl⟩ : U.elementsMk T x.down ⟶ U.elementsMk S (U.map k x.down)) ≫
        (fiberIso p U f over P S d).hom =
      f.map (⟨k, rfl⟩ : U.elementsMk T x.down ⟶ U.elementsMk S (U.map k x.down))) :
    d = 𝟙 _ := by
  let G := P.toGroupoidInFunctors
  let a := G.evaluationArrowEquiv T x x (𝟙 x)
  let b := G.evaluationArrowEquiv S _ _ d
  have hh : P.arrows.map k a.1 = b.1 := by
    apply arrow_map_of_square p U f over P a.1 b.1 a.2.1 a.2.2 b.2.1 b.2.2
      (⟨k, rfl⟩ : U.elementsMk T x.down ⟶ U.elementsMk S (U.map k x.down))
      (⟨k, rfl⟩ : U.elementsMk T x.down ⟶ U.elementsMk S (U.map k x.down)) rfl
    show _ ≫ (fiberIso p U f over P S d).hom = (fiberIso p U f over P T (𝟙 x)).hom ≫ _
    rw [fiberIso_id]
    simpa using h
  apply (G.evaluationArrowEquiv S _ _).injective
  apply Subtype.ext
  show b.1 = _
  rw [← hh]
  have hm := evaluationMap_map_arrow G k (𝟙 x)
  simp only [Functor.map_id] at hm
  exact hm.symm

private lemma presentationFunctor_faithful : (presentationFunctor p U f over P).Faithful := by
  constructor
  intro X Y a b hab
  have hbase : a.base = b.base := by
    have h := congrArg p.map hab
    have ha := Functor.congr_hom (presentationFunctor_over p U f over P) a
    have hb := Functor.congr_hom (presentationFunctor_over p U f over P) b
    change p.map ((presentationFunctor p U f over P).map a) = _ at ha
    change p.map ((presentationFunctor p U f over P).map b) = _ at hb
    rw [ha, hb] at h
    have hX := Functor.congr_obj (presentationFunctor_over p U f over P) X
    have hY := Functor.congr_obj (presentationFunctor_over p U f over P) Y
    have h' := congrArg (fun t => eqToHom hX.symm ≫ t ≫ eqToHom hY) h
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id] at h'
    exact h'
  cases a with
  | mk k a =>
    cases b with
    | mk l b =>
      change k = l at hbase
      subst l
      apply Grothendieck.ext (⟨k, a⟩ : X ⟶ Y) (⟨k, b⟩ : X ⟶ Y) rfl
      simp only [eqToHom_refl, Category.id_comp]
      have hh : a ≫ inv b = 𝟙 _ := by
        apply fiber_stabilizer_trivial p U f over P k X.fiber (a ≫ inv b)
        show f.map (⟨k, rfl⟩ : U.elementsMk X.base X.fiber.down ⟶
          U.elementsMk Y.base (U.map k X.fiber.down)) ≫
          (presentationFiberFunctor p U f over P Y.base).map (a ≫ inv b) = _
        rw [Functor.map_comp, ← Category.assoc]
        change f.map (⟨k, rfl⟩ : U.elementsMk X.base X.fiber.down ⟶
          U.elementsMk Y.base (U.map k X.fiber.down)) ≫
          (presentationFiberFunctor p U f over P Y.base).map a =
          f.map (⟨k, rfl⟩ : U.elementsMk X.base X.fiber.down ⟶
          U.elementsMk Y.base (U.map k X.fiber.down)) ≫
          (presentationFiberFunctor p U f over P Y.base).map b at hab
        rw [hab, Category.assoc, ← Functor.map_comp]
        simp only [evaluationFunctor_obj, Cat.of_α, IsIso.hom_inv_id, Functor.map_id]
        exact Category.comp_id _
      have := congrArg (fun t => t ≫ b) hh
      simpa [Category.assoc] using this

private theorem exists_presentationFunctor :
    ∃ g : Grothendieck (evaluationFunctor P.toGroupoidInFunctors) ⥤ F,
      ((g ⋙ p = Grothendieck.forget (evaluationFunctor P.toGroupoidInFunctors)) ∧
        ((uliftElementsEquivalence U).functor ⋙
          quotientMorphism P.toGroupoidInFunctors ⋙ g = f)) ∧
      (∀ _ : IsCofiberedInGroupoids p, g.Full) ∧ g.Faithful :=
  ⟨presentationFunctor p U f over P,
    ⟨presentationFunctor_over p U f over P, presentationFunctor_comp_quotient p U f over P⟩,
    presentationFunctor_full p U f over P, presentationFunctor_faithful p U f over P⟩

/-- The canonical morphism from the quotient of a presentation to the category
being presented, together with its compatibility with the projection and the
original presentation functor. -/
@[stacks 06KZ "natural morphism"]
noncomputable def presentationMorphism :
    {g : Grothendieck (evaluationFunctor P.toGroupoidInFunctors) ⥤ F //
      (g ⋙ p = Grothendieck.forget
        (evaluationFunctor P.toGroupoidInFunctors)) ∧
      ((uliftElementsEquivalence U).functor ⋙
        quotientMorphism P.toGroupoidInFunctors ⋙ g = f)} :=
  let h : ∃ g : Grothendieck (evaluationFunctor P.toGroupoidInFunctors) ⥤ F,
      ((g ⋙ p = Grothendieck.forget (evaluationFunctor P.toGroupoidInFunctors)) ∧
        ((uliftElementsEquivalence U).functor ⋙
          quotientMorphism P.toGroupoidInFunctors ⋙ g = f)) ∧
      (∀ _ : IsCofiberedInGroupoids p, g.Full) ∧ g.Faithful := by
    exact exists_presentationFunctor p U f over P
  ⟨h.choose, h.choose_spec.1⟩

/-- The morphism from a presentation quotient is full. -/
@[stacks 06KZ "full"]
theorem presentationMorphism_full
    (hp : IsCofiberedInGroupoids p) :
    (presentationMorphism p U f over P).1.Full := by
  exact (exists_presentationFunctor p U f over P).choose_spec.2.1 hp

/-- The morphism from a presentation quotient is faithful. -/
@[stacks 06KZ "faithful"]
theorem presentationMorphism_faithful :
    (presentationMorphism p U f over P).1.Faithful := by
  exact (exists_presentationFunctor p U f over P).choose_spec.2.2

/-- The quotient morphism is an equivalence exactly when the original
presentation functor is essentially surjective. -/
@[stacks 06KZ "equivalence criterion"]
theorem presentationMorphism_isEquivalence_iff
    (hp : IsCofiberedInGroupoids p) :
    (presentationMorphism p U f over P).1.IsEquivalence ↔ f.EssSurj := by
  let g := (presentationMorphism p U f over P).1
  have : g.Full := presentationMorphism_full p U f over P hp
  have : g.Faithful := presentationMorphism_faithful p U f over P
  have hobj (X : Grothendieck (evaluationFunctor P.toGroupoidInFunctors)) :
      g.obj X = f.obj (U.elementsMk X.base X.fiber.down) :=
    Functor.congr_obj (presentationMorphism p U f over P).2.2 (U.elementsMk X.base X.fiber.down)
  constructor
  · intro hg
    refine ⟨fun Y => ?_⟩
    obtain ⟨X, ⟨e⟩⟩ := hg.essSurj.mem_essImage Y
    exact ⟨U.elementsMk X.base X.fiber.down, ⟨(eqToIso (hobj X)).symm ≪≫ e⟩⟩
  · intro hf
    have : g.EssSurj := ⟨fun Y => by
      obtain ⟨X, ⟨e⟩⟩ := hf.mem_essImage Y
      exact ⟨⟨X.1, ULift.up X.2⟩, ⟨eqToIso (hobj ⟨X.1, ULift.up X.2⟩) ≪≫ e⟩⟩⟩
    exact Functor.IsEquivalence.mk

end Deformation

end
