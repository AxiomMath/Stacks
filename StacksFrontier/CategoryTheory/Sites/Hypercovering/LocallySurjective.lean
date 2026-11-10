module

public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Presheaf
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SectionsComplexOver
public import StacksFrontier.CategoryTheory.Sites.Representable.CoproductYonedaDesc

/-!
# Local surjectivity of the matching maps of a hypercovering

Let `C` be a site given by a pretopology `J`, let `C` have fibre products, let `X : C` and let `K`
be a hypercovering of `X`. Applying the representable-presheaf functor degreewise to `K` gives an
augmented simplicial presheaf over the presheaf represented by `X`. This file proves that its
degree-zero augmentation, its degree-one matching map to the fibre product of the two
degree-zero augmentations, and all of its higher matching maps are locally surjective.

## Main definitions

* `associatedPresheafFunctorOver`: the functor sending a semi-representable object over `X` to
  the corresponding coproduct of representable presheaves on `C`.
* `associatedPresheafAugmentationOver`: the canonical morphism from that presheaf to the
  presheaf represented by `X`.
* `associatedAugmentedSimplicialPresheafOver`: the simplicial presheaf obtained degreewise from
  a simplicial semi-representable object over `X`, together with its canonical augmentation.

## Main results

* `locallySurjective_augmentation_of_isHypercovering` is Tag 01G9 (1): local surjectivity in
  degree zero.
* `locallySurjective_oneMatchingMap_of_isHypercovering` is Tag 01G9 (2): local surjectivity of
  the degree-one matching map.
* `locallySurjective_higherMatchingMap_of_isHypercovering` is Tag 01G9 (3): local surjectivity
  of every matching map in degree at least two.

## Implementation notes

`FormalCoproduct (Over X)` models the semi-representable objects over `X`, `SR(C, X)` in the
source. The presheaf functor is the universe-lifted Yoneda embedding after forgetting the
structure maps to `X`, extended over formal coproducts; the structure maps themselves assemble
into the canonical augmentation. The index, hom and object universes are independent and the
presheaves take values in their common maximum. Local surjectivity is Mathlib's
`Presheaf.IsLocallySurjective`.

## References

* [Stacks Project, Tag 01G9](https://stacks.math.columbia.edu/tag/01G9)
-/

@[expose] public section

universe w v u t s

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryTheory.Hypercovering


variable {C : Type u} [Category.{v} C]

/-- Send a formal coproduct of objects over `X` to the corresponding coproduct of representable
presheaves on `C`, in a universe containing the object, morphism, and index universes. -/
noncomputable abbrev associatedPresheafFunctorOver {X : C} :
    FormalCoproduct.{w} (Over X) ⥤ Cᵒᵖ ⥤ Type (max u v w) :=
  (FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max u v w))).obj
    (Over.forget X ⋙ uliftYoneda.{max u w})

/-- The canonical natural transformation from the presheaf associated to a formal coproduct over
`X` to the representable presheaf of `X`. -/
noncomputable def associatedPresheafAugmentationOver {X : C} :
    associatedPresheafFunctorOver.{w} (X := X) ⟶
      (Functor.const _).obj (uliftYoneda.{max u w}.obj X) where
  app U := Sigma.desc fun i ↦ uliftYoneda.map (U.obj i).hom
  naturality U V f := by
    apply Sigma.hom_ext
    intro i
    simp only [Functor.comp_obj, Over.forget_obj, Functor.const_obj_obj,
      associatedPresheafFunctorOver, FormalCoproduct.eval, Functor.comp_map, Over.forget_map,
      colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app,
      Category.assoc, Functor.const_obj_map, Category.comp_id, colimit.ι_desc]
    rw [Sigma.ι_comp_desc, ← Functor.map_comp, Over.w]

/-- The simplicial presheaf associated to `K`, together with its canonical augmentation to the
representable presheaf of `X`. -/
noncomputable def associatedAugmentedSimplicialPresheafOver {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    SimplicialObject.Augmented (Cᵒᵖ ⥤ Type (max u v w)) where
  left := SectionsOver.associatedSimplicialPresheaf K
  right := uliftYoneda.{max u w}.obj X
  hom :=
    { app n := associatedPresheafAugmentationOver.app (K.obj n)
      naturality _ _ f := associatedPresheafAugmentationOver.naturality (K.map f) }

variable [HasPullbacks C]

private noncomputable def associatedSectionEquiv {X : C}
    (T : FormalCoproduct.{w} (Over X)) (Y : Cᵒᵖ) :
    ((associatedPresheafFunctorOver (X := X)).obj T).obj Y ≃
      Σ i : T.I, ULift (Y.unop ⟶ (T.obj i).left) := by
  let e₁ := (SectionsOver.formalEvalCoproductIso (X := X) T).app Y
  let e₂ := sigmaObjIso (fun i : T.I ↦ uliftYoneda.{max u w}.obj ((T.obj i).left)) Y
  let e₃ := Types.coproductIso (fun i : T.I ↦
    (uliftYoneda.{max u w}.obj ((T.obj i).left)).obj Y)
  exact (e₁.toEquiv.trans e₂.toEquiv).trans e₃.toEquiv

omit [HasPullbacks C] in
private lemma uliftYoneda_map_app {X Y : C} (f : X ⟶ Y)
    (Z : Cᵒᵖ) (g : Z.unop ⟶ X) :
    (uliftYoneda.map f).app Z (ULift.up g) = ULift.up (g ≫ f) :=
  rfl

omit [HasPullbacks C] in
private lemma formalEvalι_app_equiv {X : C} (T : FormalCoproduct.{w} (Over X))
    (Y : Cᵒᵖ) (i : T.I) (g : Y.unop ⟶ (T.obj i).left) :
    associatedSectionEquiv T Y
      ((SectionsOver.formalEvalι T i).app Y (ULift.up.{max u w, v} g)) =
      ⟨i, ULift.up.{max u w, v} g⟩ := by
  let e₁ := (SectionsOver.formalEvalCoproductIso (X := X) T).app Y
  let e₂ := sigmaObjIso (fun j : T.I ↦ uliftYoneda.{max u w}.obj ((T.obj j).left)) Y
  let e₃ := Types.coproductIso (fun j : T.I ↦
    (uliftYoneda.{max u w}.obj ((T.obj j).left)).obj Y)
  have hcomp : SectionsOver.formalEvalι T i ≫ (SectionsOver.formalEvalCoproductIso (X := X) T).hom =
      Sigma.ι (fun j : T.I ↦ uliftYoneda.{max u w}.obj ((T.obj j).left)) i := by
    dsimp [SectionsOver.formalEvalι]
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hcompAll : (SectionsOver.formalEvalι T i).app Y ≫ e₁.hom ≫ e₂.hom ≫ e₃.hom =
      (↾fun x => ⟨i, x⟩) := by
    calc
      _ = (Sigma.ι (fun j : T.I ↦ uliftYoneda.{max u w}.obj ((T.obj j).left)) i).app Y ≫
          e₂.hom ≫ e₃.hom := by
            dsimp [e₁]
            rw [← Category.assoc, ← NatTrans.comp_app, hcomp]
      _ = (Sigma.ι (fun j : T.I ↦ (uliftYoneda.{max u w}.obj ((T.obj j).left)).obj Y) i) ≫
          e₃.hom := by rw [← Category.assoc, ι_comp_sigmaObjIso_hom]
      _ = _ := Types.coproductIso_ι_comp_hom _ i
  change e₃.toEquiv (e₂.toEquiv (e₁.toEquiv
    ((SectionsOver.formalEvalι T i).app Y (ULift.up.{max u w, v} g)))) = _
  simp only [Iso.toEquiv_apply]
  convert congrArg (fun q => q (ULift.up.{max u w, v} g)) hcompAll using 1
  rfl

/-- Every section of the presheaf of a formal coproduct is an injection of a representable
section. -/
private lemma exists_formalEvalι_eq {D : Type u} [Category.{v} D] {X : D}
    (T : FormalCoproduct.{w} (Over X)) (Y : Dᵒᵖ)
    (s : ((associatedPresheafFunctorOver (X := X)).obj T).obj Y) :
    ∃ (i : T.I) (g : Y.unop ⟶ (T.obj i).left),
      s = (SectionsOver.formalEvalι T i).app Y (ULift.up.{max u w, v} g) :=
  ⟨_, _, (associatedSectionEquiv T Y).injective (formalEvalι_app_equiv T Y _ _).symm⟩

omit [HasPullbacks C] in
private lemma formalEval_map_app_equiv {X : C}
    {U T : FormalCoproduct.{w} (Over X)} (f : U ⟶ T)
    (Y : Cᵒᵖ) (i : U.I) (g : Y.unop ⟶ (U.obj i).left) :
    associatedSectionEquiv T Y
      (((associatedPresheafFunctorOver (X := X)).map f).app Y
        ((SectionsOver.formalEvalι U i).app Y (ULift.up g))) =
      ⟨f.f i, ULift.up (g ≫ (f.φ i).left)⟩ := by
  have hn := congrArg (fun η => η.app Y) (SectionsOver.formalEvalι_naturality (X := X) f i)
  have hn'' : ((associatedPresheafFunctorOver (X := X)).map f).app Y
        ((SectionsOver.formalEvalι U i).app Y (ULift.up.{max u w, v} g)) =
      (SectionsOver.formalEvalι T (f.f i)).app Y
        (ULift.up.{max u w, v} (g ≫ (f.φ i).left)) := by
    have hcomp : (SectionsOver.formalEvalι U i).app Y ≫
          ((associatedPresheafFunctorOver (X := X)).map f).app Y =
        (uliftYoneda.map ((Over.forget X).map (f.φ i))).app Y ≫
          (SectionsOver.formalEvalι T (f.f i)).app Y := by
      simpa only [NatTrans.comp_app] using hn
    have hcomp' := congrArg (fun q => q (ULift.up.{max u w, v} g)) hcomp
    have hleft : ((associatedPresheafFunctorOver (X := X)).map f).app Y
          ((SectionsOver.formalEvalι U i).app Y (ULift.up.{max u w, v} g)) =
        (ConcreteCategory.hom ((SectionsOver.formalEvalι U i).app Y ≫
          ((associatedPresheafFunctorOver (X := X)).map f).app Y))
          (ULift.up.{max u w, v} g) :=
      (ConcreteCategory.comp_apply _ _ _).symm
    have hright : (ConcreteCategory.hom
          ((uliftYoneda.map ((Over.forget X).map (f.φ i))).app Y ≫
            (SectionsOver.formalEvalι T (f.f i)).app Y)) (ULift.up.{max u w, v} g) =
        (SectionsOver.formalEvalι T (f.f i)).app Y
          (ULift.up.{max u w, v} (g ≫ (f.φ i).left)) := by
      change ((SectionsOver.formalEvalι T (f.f i)).app Y)
          (((uliftYoneda.map ((Over.forget X).map (f.φ i))).app Y)
            (ULift.up.{max u w, v} g)) = _
      rw [uliftYoneda_map_app]
      simp only [Over.forget_map]
    rw [hleft, hcomp', hright]
  rw [hn'']
  exact formalEvalι_app_equiv T Y (f.f i) (g ≫ (f.φ i).left)

omit [HasPullbacks C] in
private lemma associatedSectionEquiv_map {X : C}
    {U T : FormalCoproduct.{w} (Over X)} (f : U ⟶ T) (Y : Cᵒᵖ)
    (s : ((associatedPresheafFunctorOver (X := X)).obj U).obj Y) :
    associatedSectionEquiv T Y (((associatedPresheafFunctorOver (X := X)).map f).app Y s) =
      let q := associatedSectionEquiv U Y s
      ⟨f.f q.1, ULift.up (q.2.down ≫ (f.φ q.1).left)⟩ := by
  obtain ⟨i, g, rfl⟩ := exists_formalEvalι_eq U Y s
  rw [formalEvalι_app_equiv]
  exact formalEval_map_app_equiv f Y i g

omit [HasPullbacks C] in
private lemma associatedSectionEquiv_map_restrict {X : C}
    (T : FormalCoproduct.{w} (Over X)) {Y Z : C} (g : Z ⟶ Y)
    (s : ((associatedPresheafFunctorOver (X := X)).obj T).obj (Opposite.op Y)) :
    associatedSectionEquiv T (Opposite.op Z)
        (((associatedPresheafFunctorOver (X := X)).obj T).map g.op s) =
      let q := associatedSectionEquiv T (Opposite.op Y) s
      ⟨q.1, ULift.up (g ≫ q.2.down)⟩ := by
  obtain ⟨i, f, rfl⟩ := exists_formalEvalι_eq T (Opposite.op Y) s
  have hres : ((associatedPresheafFunctorOver (X := X)).obj T).map g.op
        ((SectionsOver.formalEvalι T i).app (Opposite.op Y) (ULift.up.{max u w, v} f)) =
      (SectionsOver.formalEvalι T i).app (Opposite.op Z) (ULift.up.{max u w, v} (g ≫ f)) := by
    rw [← NatTrans.naturality_apply (SectionsOver.formalEvalι T i) g.op (ULift.up.{max u w, v} f)]
    rfl
  rw [hres, formalEvalι_app_equiv T (Opposite.op Y) i f,
    formalEvalι_app_equiv T (Opposite.op Z) i (g ≫ f)]

private lemma ulift_heq {α β : Type t} {a : α} {b : β} (h : HEq a b) :
    HEq (ULift.up.{s, t} a) (ULift.up.{s, t} b) := by
  cases h
  rfl

private lemma locallySurjective_map_of_coveringOver {X : C} (J : Pretopology C)
    {U T : FormalCoproduct.{w} (Over X)} (f : U ⟶ T)
    (hf : IsCoveringOver J f) :
    Presheaf.IsLocallySurjective J.toGrothendieck
      ((associatedPresheafFunctorOver (X := X)).map f) := by
  classical
  constructor
  intro Y s
  obtain ⟨j, g, rfl⟩ := exists_formalEvalι_eq T (Opposite.op Y) s
  let Uj : {i : U.I // f.f i = j} → C := fun i ↦ (U.obj i.1).left
  let aj : (i : {i : U.I // f.f i = j}) → Uj i ⟶ (T.obj j).left :=
    fun i ↦ (f.φ i.1).left ≫ eqToHom (congrArg (fun k ↦ (T.obj k).left) i.2)
  let S := Sieve.ofArrows Uj aj
  have hS : S ∈ J.toGrothendieck (T.obj j).left := by
    rw [Pretopology.mem_toGrothendieck]
    exact ⟨Presieve.ofArrows Uj aj, hf j, Sieve.le_generate _⟩
  have hpull := J.toGrothendieck.pullback_stable g hS
  apply J.toGrothendieck.superset_covering _ hpull
  intro Z h hh
  rw [Sieve.pullback_apply] at hh
  obtain ⟨i, k, hk⟩ := (Sieve.mem_ofArrows_iff Uj aj _).mp hh
  refine ⟨(SectionsOver.formalEvalι U i.1).app (Opposite.op Z) (ULift.up.{max u w, v} k), ?_⟩
  apply (associatedSectionEquiv T (Opposite.op Z)).injective
  rw [formalEval_map_app_equiv]
  rw [associatedSectionEquiv_map_restrict, formalEvalι_app_equiv T (Opposite.op Y) j g]
  apply Sigma.ext
  · exact i.2
  · let hobj := congrArg (fun a => (T.obj a).left) i.2
    have hk' : h ≫ g = k ≫ (f.φ i.1).left ≫ eqToHom hobj := by
      simpa [aj, Uj, Category.assoc] using hk
    have hval : ((k ≫ (f.φ i.1).left) ≫ eqToHom hobj) ≍ h ≫ g := by
      rw [Category.assoc, hk'.symm]
    exact ulift_heq ((CategoryTheory.comp_eqToHom_heq
      (k ≫ (f.φ i.1).left) hobj).symm.trans hval)

private lemma locallySurjective_comp_of_pointwiseSurjective_right
    {F G H : Cᵒᵖ ⥤ Type (max u v w)}
    (J : Pretopology C) (f : F ⟶ G) (g : G ⟶ H)
    (hf : Presheaf.IsLocallySurjective J.toGrothendieck f)
    (hg : ∀ (Y : Cᵒᵖ) (s : H.obj Y), ∃ t : G.obj Y, g.app Y t = s) :
    Presheaf.IsLocallySurjective J.toGrothendieck (f ≫ g) := by
  classical
  constructor
  intro Y s
  obtain ⟨t, rfl⟩ := hg (Opposite.op Y) s
  let : Presheaf.IsLocallySurjective J.toGrothendieck f := hf
  let t' : ToType (G.obj (Opposite.op Y)) := t
  apply J.toGrothendieck.superset_covering _
    (Presheaf.IsLocallySurjective.imageSieve_mem (f := f) (U := Y) t')
  intro Z h hh
  rcases hh with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, hx]
  exact NatTrans.naturality_apply g h.op t

private noncomputable abbrev singletonTerminalFormalCoproduct (X : C) :
    FormalCoproduct.{w} (Over X) :=
  (FormalCoproduct.incl (Over X)).obj (Over.mk (𝟙 X))

private noncomputable def singletonTerminalFormalCoproductIso {X : C} :
    singletonTerminalFormalCoproduct X ≅
      ⊤_ (FormalCoproduct.{w} (Over X)) := by
  let hO : IsTerminal (Over.mk (𝟙 X)) :=
    IsTerminal.ofUniqueHom (fun Y ↦ Over.homMk Y.hom) fun Y m ↦
      Over.OverMorphism.ext (by simpa using m.w)
  exact (FormalCoproduct.isTerminalIncl (Over.mk (𝟙 X)) hO).uniqueUpToIso terminalIsTerminal

omit [HasPullbacks C] in
/-- The injection of the `i`-th component into the presheaf of a formal coproduct over `X`,
followed by the canonical augmentation, is the morphism represented by the structure map of that
component. -/
lemma formalEvalι_comp_associatedPresheafAugmentationOver {X : C}
    (T : FormalCoproduct.{w} (Over X)) (i : T.I) :
    SectionsOver.formalEvalι T i ≫ (associatedPresheafAugmentationOver (X := X)).app T =
      uliftYoneda.{max u w}.map (T.obj i).hom := by
  dsimp [SectionsOver.formalEvalι, SectionsOver.formalEvalCoproductIso]
  cases FormalCoproduct.eval_obj_obj (C := Over X)
    (A := Cᵒᵖ ⥤ Type (max u v w))
    (F := Over.forget X ⋙ uliftYoneda.{max u w}) (X := T)
  simp [associatedPresheafAugmentationOver, associatedPresheafFunctorOver, FormalCoproduct.eval]

omit [HasPullbacks C] in
private alias formalEvalι_comp_augmentation := formalEvalι_comp_associatedPresheafAugmentationOver

omit [HasPullbacks C] in
private lemma associatedPresheafAugmentationOver_formalEvalι {X : C}
    (T : FormalCoproduct.{w} (Over X)) (Y : Cᵒᵖ) (i : T.I)
    (g : Y.unop ⟶ (T.obj i).left) :
    ((associatedPresheafAugmentationOver (X := X)).app T).app Y
      ((SectionsOver.formalEvalι T i).app Y (ULift.up g)) = ULift.up (g ≫ (T.obj i).hom) := by
  have h := congrArg (fun η => η.app Y) (formalEvalι_comp_augmentation T i)
  rw [NatTrans.comp_app] at h
  change (ConcreteCategory.hom ((SectionsOver.formalEvalι T i).app Y ≫
      ((associatedPresheafAugmentationOver (X := X)).app T).app Y)) (ULift.up g) = _
  rw [h, uliftYoneda_map_app]

omit [HasPullbacks C] in
private lemma associatedPresheafAugmentationOver_sectionEquiv {X : C}
    (T : FormalCoproduct.{w} (Over X)) (Y : Cᵒᵖ)
    (s : ((associatedPresheafFunctorOver (X := X)).obj T).obj Y) :
    let q := associatedSectionEquiv T Y s
    ((associatedPresheafAugmentationOver (X := X)).app T).app Y s =
      ULift.up (q.2.down ≫ (T.obj q.1).hom) := by
  obtain ⟨i, g, rfl⟩ := exists_formalEvalι_eq T Y s
  rw [formalEvalι_app_equiv]
  exact associatedPresheafAugmentationOver_formalEvalι T Y i g

private noncomputable def associatedSectionToOverHom {X : C}
    (T : FormalCoproduct.{w} (Over X)) (Y : Cᵒᵖ) (gY : Y.unop ⟶ X)
    (s : ((associatedPresheafFunctorOver (X := X)).obj T).obj Y)
    (hs : ((associatedPresheafAugmentationOver (X := X)).app T).app Y s = ULift.up gY) :
    (FormalCoproduct.incl (Over X)).obj (Over.mk gY) ⟶ T := by
  let e := associatedSectionEquiv T Y
  let q := e s
  let i := q.1
  let g := q.2.down
  have hcomm : g ≫ (T.obj i).hom = gY := by
    have h : ((associatedPresheafAugmentationOver (X := X)).app T).app Y s =
        ULift.up (g ≫ (T.obj i).hom) := by
      simpa [e, q, g, i] using associatedPresheafAugmentationOver_sectionEquiv T Y s
    exact congrArg ULift.down (h.symm.trans hs)
  exact FormalCoproduct.Hom.fromIncl i (Over.homMk g hcomm)

omit [HasPullbacks C] in
private lemma associatedSectionToOverHom_eval {X : C}
    (T : FormalCoproduct.{w} (Over X)) (Y : Cᵒᵖ) (gY : Y.unop ⟶ X)
    (s : ((associatedPresheafFunctorOver (X := X)).obj T).obj Y)
    (hs : ((associatedPresheafAugmentationOver (X := X)).app T).app Y s = ULift.up gY) :
    ((associatedPresheafFunctorOver (X := X)).map
      (associatedSectionToOverHom T Y gY s hs)).app Y
        ((SectionsOver.formalEvalι ((FormalCoproduct.incl (Over X)).obj (Over.mk gY))
          (PUnit.unit : ((FormalCoproduct.incl (Over X)).obj (Over.mk gY)).I)).app Y
          (ULift.up.{max u w, v} (𝟙 Y.unop))) = s := by
  let S := (FormalCoproduct.incl (Over X)).obj (Over.mk gY)
  let i : S.I := PUnit.unit
  let z := (SectionsOver.formalEvalι S i).app Y (ULift.up.{max u w, v} (𝟙 Y.unop))
  have hgen : associatedSectionEquiv S Y z = ⟨i, ULift.up (𝟙 Y.unop)⟩ :=
    formalEvalι_app_equiv S Y i (𝟙 Y.unop)
  have hmap := associatedSectionEquiv_map (X := X)
    (associatedSectionToOverHom T Y gY s hs) Y z
  rw [hgen] at hmap
  have hsection : (associatedSectionEquiv T Y)
      (((associatedPresheafFunctorOver (X := X)).map
        (associatedSectionToOverHom T Y gY s hs)).app Y z) =
      associatedSectionEquiv T Y s := by
    calc
      _ = ⟨(associatedSectionEquiv T Y s).1,
          ULift.up ((associatedSectionEquiv T Y s).2.down)⟩ := by
        simpa only [S, i, z, associatedSectionToOverHom,
          FormalCoproduct.Hom.fromIncl, FormalCoproduct.incl,
          Over.homMk_left, Category.id_comp] using hmap
      _ = associatedSectionEquiv T Y s := by
        cases associatedSectionEquiv T Y s with
        | mk i g => cases g; rfl
  exact (associatedSectionEquiv T Y).injective hsection

private abbrev matchingShape (n m : ℕ) :=
  StructuredArrow (Opposite.op (SimplexCategory.mk m)) (SimplexCategory.Truncated.inclusion n).op

@[implicit_reducible]
private def matchingShapeObj (n m : ℕ) (k : SimplexCategory) (hk : k.len ≤ n)
    (a : k ⟶ SimplexCategory.mk m) : matchingShape n m := by
  refine StructuredArrow.mk (T := (SimplexCategory.Truncated.inclusion n).op)
    (Y := Opposite.op (⟨k, hk⟩ : SimplexCategory.Truncated n)) ?_
  exact a.op

private def matchingVertexObj (n m : ℕ) (x : Fin (m + 1)) : matchingShape n m :=
  matchingShapeObj n m (SimplexCategory.mk 0) (by simp)
    (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m) x)

/-- For `1 ≤ n`, the category of morphisms `[k] ⟶ [m]` with `k ≤ n`, which indexes the limit
defining the `n`-coskeleton in degree `m`, is connected. -/
private theorem matchingShape_isConnected (n m : ℕ) (hn : 1 ≤ n) :
    IsConnected (matchingShape n m) := by
  let d0 := matchingVertexObj n m ⟨0, by omega⟩
  let : Nonempty (matchingShape n m) := ⟨d0⟩
  apply IsConnected.of_constant_of_preserves_morphisms
  intro α F h d d'
  let x : Fin (m + 1) := d.hom.unop ⟨0, by omega⟩
  let y : Fin (m + 1) := d'.hom.unop ⟨0, by omega⟩
  let vx := matchingVertexObj n m x
  let vy := matchingVertexObj n m y
  let v0 := matchingVertexObj n m ⟨0, by omega⟩
  let edgeHom (z : Fin (m + 1)) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk m :=
    SimplexCategory.Hom.mk ⟨fun i => if i.val = 0 then ⟨0, by omega⟩ else z,
      by
        intro a b hab
        simp only [Fin.le_def] at *
        by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
        all_goals simp [ha, hb]
        all_goals omega⟩
  have toVertex (q : matchingShape n m) :
      q ⟶ matchingVertexObj n m (q.hom.unop ⟨0, by omega⟩) := StructuredArrow.homMk
    (ObjectProperty.homMk (SimplexCategory.const (SimplexCategory.mk 0)
      q.right.unop.obj ⟨0, by omega⟩)).op (by
      apply Quiver.Hom.unop_inj
      change (SimplexCategory.const (SimplexCategory.mk 0) q.right.unop.obj ⟨0, by omega⟩ ≫
          q.hom.unop) =
        SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m)
          (q.hom.unop ⟨0, by omega⟩)
      rw [SimplexCategory.const_comp]
      apply congrArg (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m))
      rfl)
  have hmap {a b : matchingShape n m} (f : a ⟶ b) : F a = F b := h f
  have vertex_eq_zero (z : Fin (m + 1)) : F (matchingVertexObj n m z) = F v0 := by
    let eObj := matchingShapeObj n m (SimplexCategory.mk 1)
      (by simpa [SimplexCategory.mk] using hn) (edgeHom z)
    have toVertex : eObj ⟶ matchingVertexObj n m z := StructuredArrow.homMk
      (ObjectProperty.homMk (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk 1) ⟨1, by decide⟩)).op (by
        apply Quiver.Hom.unop_inj
        change (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1)
          ⟨1, by decide⟩ ≫ edgeHom z) =
          SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m) z
        rw [SimplexCategory.const_comp]
        simp [edgeHom])
    have toZero : eObj ⟶ v0 := StructuredArrow.homMk
      (ObjectProperty.homMk (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk 1) ⟨0, by decide⟩)).op (by
        apply Quiver.Hom.unop_inj
        change (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 1)
          ⟨0, by decide⟩ ≫ edgeHom z) =
          SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk m) ⟨0, by omega⟩
        rw [SimplexCategory.const_comp]
        simp [edgeHom])
    exact (hmap toVertex).symm.trans (hmap toZero)
  calc
    F d = F vx := hmap (toVertex d)
    _ = F v0 := vertex_eq_zero x
    _ = F vy := (vertex_eq_zero y).symm
    _ = F d' := (hmap (toVertex d')).symm

private noncomputable def matchingComparison {X : C} (n m : ℕ)
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    (associatedPresheafFunctorOver (X := X)).obj
      (((SimplicialObject.Truncated.cosk n).obj
        ((SimplicialObject.truncation n).obj K)).obj
        (Opposite.op (SimplexCategory.mk m))) ⟶
    (((SimplicialObject.Truncated.cosk n).obj
      (((SimplicialObject.truncation n).obj K) ⋙
        associatedPresheafFunctorOver (X := X))).obj
      (Opposite.op (SimplexCategory.mk m))) := by
  let L := (SimplexCategory.Truncated.inclusion n).op
  let T := (SimplicialObject.truncation n).obj K
  let x := Opposite.op (SimplexCategory.mk m)
  let D := StructuredArrow.proj x L ⋙ T
  let eD := L.ranObjObjIsoLimit T x
  let eP := L.ranObjObjIsoLimit (T ⋙ associatedPresheafFunctorOver (X := X)) x
  let c : Cone (D ⋙ associatedPresheafFunctorOver (X := X)) := {
    pt := (associatedPresheafFunctorOver (X := X)).obj ((L.ran.obj T).obj x)
    π := {
      app := fun d => (associatedPresheafFunctorOver (X := X)).map
        (eD.hom ≫ limit.π D d)
      naturality := by
        intro d d' f
        simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map,
          Functor.const_obj_map, Category.id_comp, ← Functor.map_comp]
        simpa only [Category.assoc] using
          congrArg (associatedPresheafFunctorOver (X := X)).map
            (congrArg (fun q => eD.hom ≫ q) (limit.w D f).symm)
    }
  }
  exact limit.lift (D ⋙ associatedPresheafFunctorOver (X := X)) c ≫ eP.inv

/-- Projecting the matching comparison to the `d`-th factor of the limit is the image under the
presheaf functor of the projection to the `d`-th factor. -/
private lemma matchingComparison_comp_π {X : C} (n m : ℕ)
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (d : matchingShape n m) :
    matchingComparison n m K ≫
      ((SimplexCategory.Truncated.inclusion n).op.ranObjObjIsoLimit
        ((SimplicialObject.truncation n).obj K ⋙ associatedPresheafFunctorOver (X := X))
        (Opposite.op (SimplexCategory.mk m))).hom ≫ limit.π _ d =
      associatedPresheafFunctorOver.map
        (((SimplexCategory.Truncated.inclusion n).op.ranObjObjIsoLimit
          ((SimplicialObject.truncation n).obj K) (Opposite.op (SimplexCategory.mk m))).hom ≫
          limit.π _ d) := by
  let L := (SimplexCategory.Truncated.inclusion n).op
  let T := (SimplicialObject.truncation n).obj K
  let x := Opposite.op (SimplexCategory.mk m)
  let eP := L.ranObjObjIsoLimit (T ⋙ associatedPresheafFunctorOver (X := X)) x
  dsimp [matchingComparison]
  change (limit.lift (StructuredArrow.proj x L ⋙ T ⋙ associatedPresheafFunctorOver (X := X)) ?c ≫
    eP.inv) ≫ eP.hom ≫ limit.π _ d = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, limit.lift_π]

private lemma coskUnit_comp_projection {A : Type t} [Category.{s} A]
    (n m : ℕ) (K : SimplicialObject A)
    [∀ F : SimplicialObject.Truncated A n,
      (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]
    [(SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension
      ((SimplicialObject.truncation n).obj K)]
    (d : matchingShape n m) :
    ((SimplicialObject.coskAdj n).unit.app K).app (Opposite.op (SimplexCategory.mk m)) ≫
      ((SimplexCategory.Truncated.inclusion n).op.ranObjObjIsoLimit
        ((SimplicialObject.truncation n).obj K) (Opposite.op (SimplexCategory.mk m))).hom ≫
      limit.π _ d = K.map d.hom := by
  let L := (SimplexCategory.Truncated.inclusion n).op
  let η := (L.ranAdjunction A).unit.app K
  have hn : η.app (Opposite.op (SimplexCategory.mk m)) ≫
      (L.ran.obj (L ⋙ K)).map d.hom = K.map d.hom ≫ η.app (L.obj d.right) :=
    (η.naturality d.hom).symm
  rw [Functor.ranObjObjIsoLimit_hom_π]
  change η.app _ ≫ (L.ran.obj (L ⋙ K)).map d.hom ≫
    (L.ranCounit.app (L ⋙ K)).app d.right = _
  rw [← Category.assoc, hn, Category.assoc]
  exact (congrArg (K.map d.hom ≫ ·)
    (L.ranCounit_app_app_ranAdjunction_unit_app_app K d.right)).trans (Category.comp_id _)

private lemma matchingComparison_unit {X : C} (n m : ℕ)
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    associatedPresheafFunctorOver.map
      (((SimplicialObject.coskAdj n).unit.app K).app (Opposite.op (SimplexCategory.mk m))) ≫
      matchingComparison n m K =
    ((SimplicialObject.coskAdj n).unit.app (SectionsOver.associatedSimplicialPresheaf K)).app
      (Opposite.op (SimplexCategory.mk m)) := by
  let L := (SimplexCategory.Truncated.inclusion n).op
  let T := (SimplicialObject.truncation n).obj K
  let x := Opposite.op (SimplexCategory.mk m)
  let D := StructuredArrow.proj x L ⋙ T
  let eD := L.ranObjObjIsoLimit T x
  let eP := L.ranObjObjIsoLimit (T ⋙ associatedPresheafFunctorOver (X := X)) x
  apply (cancel_mono eP.hom).mp
  apply limit.hom_ext
  intro d
  rw [Category.assoc, Category.assoc, matchingComparison_comp_π, ← Functor.map_comp,
    coskUnit_comp_projection n m K d]
  exact (coskUnit_comp_projection n m (SectionsOver.associatedSimplicialPresheaf K) d).symm

omit [HasPullbacks C] in
private lemma overHomSigma_injective {X : C} (Y : Over X)
    (T : FormalCoproduct.{w} (Over X)) :
    Function.Injective (fun q : Σ i : T.I, Y ⟶ T.obj i =>
      (⟨q.1, ULift.up.{max u w} q.2.left⟩ : Σ i : T.I, ULift (Y.left ⟶ (T.obj i).left))) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl : a = b := Over.OverMorphism.ext (congrArg ULift.down (eq_of_heq h))
  rfl

omit [HasPullbacks C] in
private lemma associatedSectionToOverHom_comp {X : C} {Y : Cᵒᵖ}
    (gY : Y.unop ⟶ X) {U V : FormalCoproduct.{w} (Over X)} (f : U ⟶ V)
    (sU : ((associatedPresheafFunctorOver (X := X)).obj U).obj Y)
    (sV : ((associatedPresheafFunctorOver (X := X)).obj V).obj Y)
    (hcompat : ((associatedPresheafFunctorOver (X := X)).map f).app Y sU = sV)
    (hU : ((associatedPresheafAugmentationOver (X := X)).app U).app Y sU = ULift.up gY)
    (hV : ((associatedPresheafAugmentationOver (X := X)).app V).app Y sV = ULift.up gY) :
    associatedSectionToOverHom U Y gY sU hU ≫ f =
      associatedSectionToOverHom V Y gY sV hV := by
  have hq := associatedSectionEquiv_map f Y sU
  rw [hcompat] at hq
  exact (FormalCoproduct.inclHomEquiv (Over.mk gY) V).injective
    (overHomSigma_injective _ _ hq.symm)

private lemma matchingComparison_pointwise_surjective {X : C} (n m : ℕ)
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    [IsConnected (matchingShape n m)] (Y : Cᵒᵖ) :
    Function.Surjective (ConcreteCategory.hom ((matchingComparison n m K).app Y)) := by
  classical
  let L := (SimplexCategory.Truncated.inclusion n).op
  let T := (SimplicialObject.truncation n).obj K
  let x := Opposite.op (SimplexCategory.mk m)
  let D := StructuredArrow.proj x L ⋙ T
  let D' := D ⋙ associatedPresheafFunctorOver (X := X)
  let eD := L.ranObjObjIsoLimit T x
  let eP := L.ranObjObjIsoLimit (T ⋙ associatedPresheafFunctorOver (X := X)) x
  intro s
  let sLim := (eP.hom.app Y) s
  let sD (d : matchingShape n m) := ((limit.π D' d).app Y) sLim
  have hcompatD (d d' : matchingShape n m) (f : d ⟶ d') :
      (D'.map f).app Y (sD d) = sD d' := by
    simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using
      congrArg (fun η => (η.app Y) sLim) (limit.w D' f)
  have hcompat (d d' : matchingShape n m) (f : d ⟶ d') :
      ((associatedPresheafFunctorOver (X := X)).map (D.map f)).app Y (sD d) = sD d' := by
    simpa [D'] using hcompatD d d' f
  let r (d : matchingShape n m) : Y.unop ⟶ X :=
    ULift.down (((associatedPresheafAugmentationOver (X := X)).app (D.obj d)).app Y (sD d))
  have hr (d d' : matchingShape n m) (f : d ⟶ d') : r d = r d' := by
    have h' :
        (ConcreteCategory.hom
              (((associatedPresheafAugmentationOver (X := X)).app (D.obj d')).app Y))
            ((ConcreteCategory.hom (((associatedPresheafFunctorOver (X := X)).map (D.map f)).app Y))
              (sD d)) =
        (ConcreteCategory.hom (((associatedPresheafAugmentationOver (X := X)).app (D.obj d)).app Y))
            (sD d) :=
      congrArg (fun η => (ConcreteCategory.hom (η.app Y)) (sD d))
        ((associatedPresheafAugmentationOver (X := X)).naturality (D.map f))
    rw [hcompat d d' f] at h'
    exact (congrArg ULift.down h').symm
  let d₀ : matchingShape n m := Classical.arbitrary _
  let gY := r d₀
  have hgY (d : matchingShape n m) : r d = gY :=
    constant_of_preserves_morphisms r hr d d₀
  have haug (d : matchingShape n m) :
      ((associatedPresheafAugmentationOver (X := X)).app (D.obj d)).app Y (sD d) = ULift.up gY :=
    ULift.ext (hgY d)
  let S := (FormalCoproduct.incl (Over X)).obj (Over.mk gY)
  let iS : S.I := PUnit.unit
  let cone : Cone D := {
    pt := S
    π := {
      app := fun d => associatedSectionToOverHom (D.obj d) Y gY (sD d) (haug d)
      naturality := by
        intro d d' f
        simpa using (associatedSectionToOverHom_comp gY (D.map f) (sD d) (sD d')
          (hcompat d d' f) (haug d) (haug d')).symm
    }
  }
  let h := limit.lift D cone ≫ eD.inv
  let gen := (SectionsOver.formalEvalι S iS).app Y (ULift.up (𝟙 Y.unop))
  refine ⟨((associatedPresheafFunctorOver (X := X)).map h).app Y gen, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (eP.hom.app Y)).injective
  apply (ConcreteCategory.bijective_of_isIso
    (limitObjIsoLimitCompEvaluation D' Y).hom).injective
  apply Types.limit_ext
  intro d
  have hπ' (z : (limit D').obj Y) :
      (ConcreteCategory.hom (limit.π (D' ⋙ (evaluation Cᵒᵖ (Type (max u v w))).obj Y) d))
          ((ConcreteCategory.hom (limitObjIsoLimitCompEvaluation D' Y).hom) z) =
        (ConcreteCategory.hom ((limit.π D' d).app Y)) z := by
    simpa only [ConcreteCategory.comp_apply] using
      congrArg (fun k => (ConcreteCategory.hom k) z) (limitObjIsoLimitCompEvaluation_hom_π D' d Y)
  have hcompareπ :
      (associatedPresheafFunctorOver (X := X)).map h ≫ matchingComparison n m K ≫
          eP.hom ≫ limit.π D' d =
        (associatedPresheafFunctorOver (X := X)).map (cone.π.app d) := by
    erw [matchingComparison_comp_π, ← Functor.map_comp]
    congr 1
    simp only [h, eD, L, T, x, Category.assoc]
    erw [Iso.inv_hom_id_assoc]
    exact limit.lift_π cone d
  have hcompareπ_app := congrArg
    (fun η => (ConcreteCategory.hom (η.app Y)) gen) hcompareπ
  change ((limit.π (D' ⋙ (evaluation Cᵒᵖ (Type (max u v w))).obj Y) d)
      ((limitObjIsoLimitCompEvaluation D' Y).hom
        ((eP.hom.app Y) ((matchingComparison n m K).app Y
          (((associatedPresheafFunctorOver (X := X)).map h).app Y gen))))) =
    ((limit.π (D' ⋙ (evaluation Cᵒᵖ (Type (max u v w))).obj Y) d)
      ((limitObjIsoLimitCompEvaluation D' Y).hom ((eP.hom.app Y) s)))
  rw [hπ', hπ']
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using
    hcompareπ_app.trans (associatedSectionToOverHom_eval (D.obj d) Y gY (sD d) (haug d))

@[implicit_reducible]
private def zeroMatchingConePresheaf {A : Type t} [Category.{s} A]
    (K : SimplicialObject A) (S : A)
    (p : Fin 2 → (S ⟶ K.obj (Opposite.op (SimplexCategory.mk 0)))) :
    Cone (StructuredArrow.proj (Opposite.op (SimplexCategory.mk 1))
      (SimplexCategory.Truncated.inclusion 0).op ⋙ (SimplicialObject.truncation 0).obj K) where
  pt := S
  π :=
    { app := fun d => p (d.hom.unop ⟨0, by omega⟩) ≫
        K.map (SimplexCategory.const d.right.unop.obj (SimplexCategory.mk 0) 0).op
      naturality := by
        intro d d' f
        have h0 : ((SimplexCategory.Truncated.inclusion 0).op.map f.right).unop
            ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
          apply Fin.ext
          have h := d.right.unop.property
          have hb := (((SimplexCategory.Truncated.inclusion 0).op.map f.right).unop
            ⟨0, by omega⟩).isLt
          dsimp at h hb ⊢
          omega
        have hi : d.hom.unop ⟨0, by omega⟩ = d'.hom.unop ⟨0, by omega⟩ := by
          have h := congrArg (fun a => a.unop ⟨0, by omega⟩) (StructuredArrow.w f)
          simpa only [unop_comp, ConcreteCategory.comp_apply, h0] using h
        change 𝟙 S ≫ (p (d'.hom.unop ⟨0, by omega⟩) ≫
          K.map (SimplexCategory.const d'.right.unop.obj (SimplexCategory.mk 0) 0).op) =
          (p (d.hom.unop ⟨0, by omega⟩) ≫
            K.map (SimplexCategory.const d.right.unop.obj (SimplexCategory.mk 0) 0).op) ≫
          K.map ((SimplexCategory.Truncated.inclusion 0).op.map f.right)
        rw [Category.id_comp, Category.assoc, ← K.map_comp, hi]
        rw [← Quiver.Hom.op_unop ((SimplexCategory.Truncated.inclusion 0).op.map f.right),
          ← op_comp]
        congr 2 }

private noncomputable def zeroMatchingProjection {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (i : Fin 2) :
    ((SimplicialObject.cosk 0).obj K).obj (Opposite.op (SimplexCategory.mk 1)) ⟶
      K.obj (Opposite.op (SimplexCategory.mk 0)) :=
  ((SimplexCategory.Truncated.inclusion 0).op.ranObjObjIsoLimit
    ((SimplicialObject.truncation 0).obj K) (Opposite.op (SimplexCategory.mk 1))).hom ≫
    limit.π _ (matchingShapeObj 0 1 (SimplexCategory.mk 0) (by simp) (SimplexCategory.δ i))

private lemma zeroMatchingProjection_unit {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (i : Fin 2) :
    ((SimplicialObject.coskAdj 0).unit.app K).app (Opposite.op (SimplexCategory.mk 1)) ≫
      zeroMatchingProjection K i = K.δ i :=
  coskUnit_comp_projection 0 1 K _

private noncomputable def zeroMatchingLift {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (S : FormalCoproduct.{w} (Over X))
    (p : Fin 2 → (S ⟶ K.obj (Opposite.op (SimplexCategory.mk 0)))) :
    S ⟶ ((SimplicialObject.cosk 0).obj K).obj (Opposite.op (SimplexCategory.mk 1)) :=
  limit.lift _ (zeroMatchingConePresheaf K S p) ≫
    ((SimplexCategory.Truncated.inclusion 0).op.ranObjObjIsoLimit
      ((SimplicialObject.truncation 0).obj K) (Opposite.op (SimplexCategory.mk 1))).inv

private lemma zeroMatchingLift_projection {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (S : FormalCoproduct.{w} (Over X))
    (p : Fin 2 → (S ⟶ K.obj (Opposite.op (SimplexCategory.mk 0)))) (i : Fin 2) :
    zeroMatchingLift K S p ≫ zeroMatchingProjection K i = p ((SimplexCategory.δ i) 0) := by
  let D := StructuredArrow.proj (Opposite.op (SimplexCategory.mk 1))
    (SimplexCategory.Truncated.inclusion 0).op ⋙ (SimplicialObject.truncation 0).obj K
  let d := matchingShapeObj 0 1 (SimplexCategory.mk 0) (by simp) (SimplexCategory.δ i)
  let e := (SimplexCategory.Truncated.inclusion 0).op.ranObjObjIsoLimit
    ((SimplicialObject.truncation 0).obj K) (Opposite.op (SimplexCategory.mk 1))
  have hh : (limit.lift D (zeroMatchingConePresheaf K S p) ≫ e.inv) ≫ e.hom ≫ limit.π D d =
      (zeroMatchingConePresheaf K S p).π.app d := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, limit.lift_π]
  change (limit.lift D (zeroMatchingConePresheaf K S p) ≫ e.inv) ≫ e.hom ≫ limit.π D d = _
  refine hh.trans ?_
  change p ((SimplexCategory.δ i) 0) ≫
    K.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0).op = _
  have h : SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0 = 𝟙 _ :=
    Subsingleton.elim _ _
  rw [h, op_id, K.map_id, Category.comp_id]

private noncomputable def oneMatchingComparison {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    associatedPresheafFunctorOver.obj
      (((SimplicialObject.cosk 0).obj K).obj (Opposite.op (SimplexCategory.mk 1))) ⟶
    pullback
      (associatedPresheafAugmentationOver.app (K.obj (Opposite.op (SimplexCategory.mk 0))))
      (associatedPresheafAugmentationOver.app (K.obj (Opposite.op (SimplexCategory.mk 0)))) :=
  pullback.lift (associatedPresheafFunctorOver.map (zeroMatchingProjection K 0))
    (associatedPresheafFunctorOver.map (zeroMatchingProjection K 1)) (by
      simpa using (associatedPresheafAugmentationOver.naturality
        (zeroMatchingProjection K 0)).trans
          (associatedPresheafAugmentationOver.naturality (zeroMatchingProjection K 1)).symm)

private lemma oneMatchingComparison_unit {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) :
    associatedPresheafFunctorOver.map
      (((SimplicialObject.coskAdj 0).unit.app K).app (Opposite.op (SimplexCategory.mk 1))) ≫
      oneMatchingComparison K =
    oneMatchingMap (associatedAugmentedSimplicialPresheafOver K).left
      (associatedAugmentedSimplicialPresheafOver K).right
      (associatedAugmentedSimplicialPresheafOver K).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, oneMatchingComparison, pullback.lift_fst,
      ← Functor.map_comp, zeroMatchingProjection_unit]
    exact (oneMatchingMap_fst
      (associatedAugmentedSimplicialPresheafOver K).left
      (associatedAugmentedSimplicialPresheafOver K).right
      (associatedAugmentedSimplicialPresheafOver K).hom).symm
  · simp only [Category.assoc, oneMatchingComparison, pullback.lift_snd,
      ← Functor.map_comp, zeroMatchingProjection_unit]
    exact (oneMatchingMap_snd
      (associatedAugmentedSimplicialPresheafOver K).left
      (associatedAugmentedSimplicialPresheafOver K).right
      (associatedAugmentedSimplicialPresheafOver K).hom).symm

private lemma oneMatchingComparison_pointwise_surjective {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X))) (Y : Cᵒᵖ) :
    Function.Surjective (ConcreteCategory.hom ((oneMatchingComparison K).app Y)) := by
  classical
  intro z
  let T := K.obj (Opposite.op (SimplexCategory.mk 0))
  let a := associatedPresheafAugmentationOver.app T
  let t₀ := (pullback.fst a a).app Y z
  let t₁ := (pullback.snd a a).app Y z
  have ht : a.app Y t₀ = a.app Y t₁ :=
    congrArg (fun f => f.app Y z) (pullback.condition (f := a) (g := a))
  let gY := (a.app Y t₀).down
  have h₀ : a.app Y t₀ = ULift.up gY := rfl
  have h₁ : a.app Y t₁ = ULift.up gY := ht.symm.trans h₀
  let S := (FormalCoproduct.incl (Over X)).obj (Over.mk gY)
  let f₀ : S ⟶ T := associatedSectionToOverHom T Y gY t₀ h₀
  let f₁ : S ⟶ T := associatedSectionToOverHom T Y gY t₁ h₁
  let p : Fin 2 → (S ⟶ T) := ![f₁, f₀]
  let h := zeroMatchingLift K S p
  let gen := (SectionsOver.formalEvalι S PUnit.unit).app Y (ULift.up (𝟙 Y.unop))
  have hp₀ : h ≫ zeroMatchingProjection K 0 = f₀ :=
    zeroMatchingLift_projection K S p 0
  have hp₁ : h ≫ zeroMatchingProjection K 1 = f₁ :=
    zeroMatchingLift_projection K S p 1
  refine ⟨(associatedPresheafFunctorOver.map h).app Y gen, ?_⟩
  apply Types.ext_of_isPullback
    ((IsPullback.of_hasPullback a a).map ((evaluation _ _).obj Y))
  · have he : associatedPresheafFunctorOver.map h ≫ oneMatchingComparison K ≫
        pullback.fst a a = associatedPresheafFunctorOver.map f₀ := by
      dsimp only [oneMatchingComparison]
      rw [pullback.lift_fst, ← Functor.map_comp, hp₀]
    exact (congrArg (fun f => f.app Y gen) he).trans (associatedSectionToOverHom_eval T Y gY t₀ h₀)
  · have he : associatedPresheafFunctorOver.map h ≫ oneMatchingComparison K ≫
        pullback.snd a a = associatedPresheafFunctorOver.map f₁ := by
      dsimp only [oneMatchingComparison]
      rw [pullback.lift_snd, ← Functor.map_comp, hp₁]
    exact (congrArg (fun f => f.app Y gen) he).trans (associatedSectionToOverHom_eval T Y gY t₁ h₁)

omit [HasPullbacks C] in
private lemma associatedPresheafAugmentationOver_terminal_surjective {X : C} (Y : Cᵒᵖ) :
    Function.Surjective
      (ConcreteCategory.hom
        (((associatedPresheafAugmentationOver (X := X)).app
          (⊤_ (FormalCoproduct.{w} (Over X)))).app Y)) := by
  classical
  intro s
  rcases s with ⟨s⟩
  let T₀ := singletonTerminalFormalCoproduct X
  let e := singletonTerminalFormalCoproductIso (X := X)
  let i : T₀.I := PUnit.unit
  let s₀ := (SectionsOver.formalEvalι T₀ i).app Y (ULift.up s)
  refine ⟨((associatedPresheafFunctorOver (X := X)).map e.hom).app Y s₀, ?_⟩
  have hn : (associatedPresheafFunctorOver (X := X)).map e.hom ≫
      (associatedPresheafAugmentationOver (X := X)).app (⊤_ _) =
        (associatedPresheafAugmentationOver (X := X)).app T₀ := by
    simpa using (associatedPresheafAugmentationOver (X := X)).naturality e.hom
  have h' : (ConcreteCategory.hom (((associatedPresheafAugmentationOver (X := X)).app
      (⊤_ _)).app Y)) (((associatedPresheafFunctorOver (X := X)).map e.hom).app Y s₀) =
        (ConcreteCategory.hom
          (((associatedPresheafAugmentationOver (X := X)).app T₀).app Y)) s₀ := by
    simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using
      congrArg (fun η => (ConcreteCategory.hom (η.app Y)) s₀) hn
  have h₀' : (ConcreteCategory.hom
        (((associatedPresheafAugmentationOver (X := X)).app T₀).app Y)) s₀ =
      ULift.up s := by
    simpa [s₀, T₀, singletonTerminalFormalCoproduct,
      FormalCoproduct.incl, Over.mk] using associatedPresheafAugmentationOver_formalEvalι T₀ Y i s
  exact h'.trans h₀'

/-- The degree-zero augmentation of the simplicial presheaf associated to a hypercovering is
locally surjective. -/
@[stacks 01G9 "part (1)"]
theorem locallySurjective_augmentation_of_isHypercovering
    (J : Pretopology C) {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hK : IsHypercovering J K) :
    Presheaf.IsLocallySurjective J.toGrothendieck
      ((associatedAugmentedSimplicialPresheafOver K).hom.app
        (Opposite.op (SimplexCategory.mk 0))) := by
  let T : FormalCoproduct.{w} (Over X) := ⊤_ (FormalCoproduct.{w} (Over X))
  let f : K.obj (Opposite.op (SimplexCategory.mk 0)) ⟶ T := terminal.from _
  change Presheaf.IsLocallySurjective J.toGrothendieck
      ((associatedPresheafAugmentationOver (X := X)).app
        (K.obj (Opposite.op (SimplexCategory.mk 0))))
  have hnat : (associatedPresheafFunctorOver (X := X)).map f ≫
      (associatedPresheafAugmentationOver (X := X)).app T =
      (associatedPresheafAugmentationOver (X := X)).app
        (K.obj (Opposite.op (SimplexCategory.mk 0))) := by
    simpa using (associatedPresheafAugmentationOver (X := X)).naturality f
  rw [← hnat]
  let := locallySurjective_map_of_coveringOver J f hK.1
  let := Presheaf.isLocallySurjective_of_surjective J.toGrothendieck
    ((associatedPresheafAugmentationOver (X := X)).app T)
    (fun Y ↦ associatedPresheafAugmentationOver_terminal_surjective (X := X) Y)
  infer_instance

/-- The map from one-simplices to the fibre product of two copies of the presheaf of vertices
over the representable presheaf of `X` is locally surjective. -/
@[stacks 01G9 "part (2)"]
theorem locallySurjective_oneMatchingMap_of_isHypercovering
    (J : Pretopology C) {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hK : IsHypercovering J K) :
    Presheaf.IsLocallySurjective J.toGrothendieck
      (oneMatchingMap (associatedAugmentedSimplicialPresheafOver K).left
        (associatedAugmentedSimplicialPresheafOver K).right
        (associatedAugmentedSimplicialPresheafOver K).hom) := by
  rw [← oneMatchingComparison_unit K]
  exact locallySurjective_comp_of_pointwiseSurjective_right J _ _
    (locallySurjective_map_of_coveringOver J _ (hK.2 0))
    (oneMatchingComparison_pointwise_surjective K)

/-- Every higher matching map of the simplicial presheaf associated to a hypercovering is
locally surjective. -/
@[stacks 01G9 "part (3)"]
theorem locallySurjective_higherMatchingMap_of_isHypercovering
    (J : Pretopology C) {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hK : IsHypercovering J K) (n : ℕ) (hn : 1 ≤ n) :
    Presheaf.IsLocallySurjective J.toGrothendieck
      (((SimplicialObject.coskAdj n).unit.app
        (associatedAugmentedSimplicialPresheafOver K).left).app
          (Opposite.op (SimplexCategory.mk (n + 1)))) := by
  let := matchingShape_isConnected n (n + 1) hn
  change Presheaf.IsLocallySurjective J.toGrothendieck
    (((SimplicialObject.coskAdj n).unit.app (SectionsOver.associatedSimplicialPresheaf K)).app _)
  rw [← matchingComparison_unit n (n + 1) K]
  exact locallySurjective_comp_of_pointwiseSurjective_right J _ _
    (locallySurjective_map_of_coveringOver J _ (hK.2 n))
    (matchingComparison_pointwise_surjective n (n + 1) K)

end Stacks.CategoryTheory.Hypercovering

end
