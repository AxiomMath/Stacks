module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.EqToHomAbsorption
public import StacksFrontier.CategoryTheory.TwoFibreProductOver
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Groupoid.Basic

/-!
# The groupoid in functors associated to a presentation

Let `p : F ⥤ C` be cofibered in groupoids and let `f : U.Elements ⥤ F` be a morphism over `C`
from the category of elements of a set-valued functor `U : C ⥤ Type _`. The two-fibre product
`U ×_F U` is then the arrow functor of a groupoid in functors on `C`, with source and target
the second and first projections and composition the projection onto the first and last factor
of the triple fibre product.

Fibrewise over `T`, an arrow is a pair of elements of `U(T)` together with a vertical
isomorphism between their images in `F`, and the groupoid structure is that of the fibre of `p`
over `T`.

## Main definitions

* `Deformation.uliftElementsEquivalence`: lifting the values of a set-valued functor does not
  change its category of elements over the base.
* `Deformation.elementBaseEq`: the image in `F` of an element of `U(T)` lies over `T`.
* `Deformation.PresentationArrow`: a fibrewise arrow of the presentation — two elements of
  `U(T)` and a vertical isomorphism between their images.
* `Deformation.PresentationArrow.comp`: composition of fibrewise arrows.
* `Deformation.PresentationGroupoid`: the groupoid in functors produced by the construction,
  together with its identification with the two-fibre product and the identification of its
  source, target and composition with the prescribed projections.
* `Deformation.PresentationGroupoid.toGroupoidInFunctors`: the underlying groupoid in functors.

## Main results

* `Deformation.presentationGroupoid`: the construction, for `p` cofibered in groupoids.

## References

* [Stacks Project, Tag 06KY](https://stacks.math.columbia.edu/tag/06KY)
-/

@[expose] public section

open CategoryTheory

universe v u w u₁ uU

namespace Deformation

variable {C : Type u} [Category.{v} C]
variable {F : Type u₁} [Category.{w} F]
variable (p : Functor F C) (U : Functor C (Type uU))
variable (f : Functor U.Elements F)
variable (over : f ⋙ p = CategoryOfElements.π U)

/-- Lifting the values of a functor does not change its category of elements
over the base. -/
@[implicit_reducible]
def uliftElementsEquivalence :
    U.Elements ≌ (U ⋙ uliftFunctor.{w, uU}).Elements where
  functor :=
    { obj x := ⟨x.1, ULift.up x.2⟩
      map g := ⟨g.1, congrArg ULift.up g.2⟩ }
  inverse :=
    { obj x := ⟨x.1, x.2.down⟩
      map g := ⟨g.1, congrArg ULift.down g.2⟩ }
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intros
    apply Subtype.ext
    exact Category.comp_id _ |>.trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intros
    apply Subtype.ext
    exact Category.comp_id _ |>.trans (Category.id_comp _).symm)
  functor_unitIso_comp x := by
    apply Subtype.ext
    exact Category.id_comp _

/-- The equality saying that the image in `F` of an element `x ∈ U(T)`
lies over `T`. -/
abbrev elementBaseEq (T : C) (x : U.obj T) :
    p.obj (f.obj ⟨T, x⟩) = T :=
  Functor.congr_obj over ⟨T, x⟩

/-- An arrow of the presentation over `T`: two elements of `U(T)`, the target and the source,
and a vertical isomorphism between their images in `F`. -/
structure PresentationArrow (T : C) where
  /-- The first projection. -/
  target : U.obj T
  /-- The second projection. -/
  source : U.obj T
  /-- The isomorphism in the two-fibre product. -/
  iso : f.obj ⟨T, target⟩ ≅ f.obj ⟨T, source⟩
  /-- The isomorphism is vertical over `T`. -/
  vertical : p.map iso.hom =
    eqToHom (elementBaseEq p U f over T target) ≫
      eqToHom (elementBaseEq p U f over T source).symm

namespace PresentationArrow

/-- Composition of presentation arrows is projection onto the first and last
factors of the corresponding triple fibre product. -/
def comp {T : C} (a b : PresentationArrow p U f over T)
    (h : a.source = b.target) : PresentationArrow p U f over T := by
  rcases a with ⟨aTarget, aSource, aIso, aVertical⟩
  rcases b with ⟨bTarget, bSource, bIso, bVertical⟩
  dsimp at h
  subst bTarget
  refine
    { target := aTarget
      source := bSource
      iso := aIso.trans bIso
      vertical := ?_ }
  rw [Iso.trans_hom, Functor.map_comp, aVertical, bVertical]
  simp

end PresentationArrow

private lemma presentationArrow_ext {T : C}
    {a b : PresentationArrow p U f over T}
    (ht : a.target = b.target) (hs : a.source = b.source)
    (hi : HEq a.iso b.iso) : a = b := by
  cases a with
  | mk targetA sourceA isoA verticalA =>
    cases b with
    | mk targetB sourceB isoB verticalB =>
      dsimp at ht hs
      cases ht; cases hs; cases hi; rfl

private lemma stronglyCocartesian_of_opIsFiberedInGroupoids
    {F : Type u₁} [Category.{w} F] {C : Type u} [Category.{v} C]
    {p : Functor F C} (hp : IsCofiberedInGroupoids p)
    {A B : C} {x y : F} (g : A ⟶ B) (φ : x ⟶ y)
    (hφ : p.IsHomLift g φ) : p.IsStronglyCocartesian g φ := by
  cases hφ
  refine ⟨fun {z} g ψ hψ ↦ ?_⟩
  have hcomm : g.op ≫ p.op.map φ.op = p.op.map ψ.op := by
    change (p.map φ ≫ g).op = (p.map ψ).op
    exact congrArg Quiver.Hom.op (IsHomLift.eq_of_isHomLift p _ ψ)
  obtain ⟨χ, ⟨hχ, hfac⟩, huniq⟩ := hp.unique_lift φ.op ψ.op g.op hcomm
  refine ⟨χ.unop, ⟨?_, ?_⟩, ?_⟩
  · have heq : p.map χ.unop = g := congrArg Quiver.Hom.unop hχ
    rw [← heq]
    infer_instance
  · exact congrArg Quiver.Hom.unop hfac
  · intro θ ⟨hθ, hθfac⟩
    let : p.IsHomLift g θ := hθ
    have heq : p.op.map θ.op = g.op :=
      congrArg Quiver.Hom.op (IsHomLift.eq_of_isHomLift p g θ).symm
    exact congrArg Quiver.Hom.unop (huniq θ.op ⟨heq, congrArg Quiver.Hom.op hθfac⟩)

private def elementArrow {C : Type u} [Category.{v} C]
    (U : Functor C (Type uU)) {T T' : C} (g : T ⟶ T') (x : U.obj T) :
    (Functor.elementsMk U T x : U.Elements) ⟶ Functor.elementsMk U T' (U.map g x) :=
  CategoryOfElements.homMk _ _ g rfl

private def elementImageArrow {C : Type u} [Category.{v} C]
    (U : Functor C (Type uU)) (f : U.Elements ⥤ F) {T T' : C} (g : T ⟶ T')
    (x : U.obj T) : f.obj ⟨T, x⟩ ⟶ f.obj ⟨T', U.map g x⟩ :=
  f.map (elementArrow U g x)

private lemma elementImageArrow_id {C : Type u} [Category.{v} C]
    (U : Functor C (Type uU)) (f : U.Elements ⥤ F) {T : C}
    (x : U.obj T) :
    elementImageArrow U f (𝟙 T) x =
      eqToHom (congrArg f.obj (Functor.Elements.ext
        (U.elementsMk T x) (U.elementsMk T (U.map (𝟙 T) x)) rfl (by simp))) := by
  let e := Functor.Elements.ext (U.elementsMk T x)
    (U.elementsMk T (U.map (𝟙 T) x)) rfl (by simp)
  have he : elementArrow U (𝟙 T) x = eqToHom e := by
    apply CategoryOfElements.ext
    change (𝟙 T : T ⟶ T) = (CategoryOfElements.π U).map (eqToHom e)
    rw [eqToHom_map]
    rfl
  change f.map (elementArrow U (𝟙 T) x) = _
  rw [he]
  exact eqToHom_map f e

private lemma elementImageArrow_comp {C : Type u} [Category.{v} C]
    (U : Functor C (Type uU)) (f : U.Elements ⥤ F) {T T' T'' : C}
    (g : T ⟶ T') (h : T' ⟶ T'') (x : U.obj T)
    (e : (U.elementsMk T'' (U.map (g ≫ h) x) : U.Elements) =
      U.elementsMk T'' (U.map h (U.map g x))) :
    elementImageArrow U f (g ≫ h) x ≫
        eqToHom (congrArg f.obj e) =
      elementImageArrow U f g x ≫ elementImageArrow U f h (U.map g x) := by
  have he : elementArrow U (g ≫ h) x ≫
      eqToHom e =
        elementArrow U g x ≫ elementArrow U h (U.map g x) := by
    have hval : (eqToHom e :
        (U.elementsMk T'' (U.map (g ≫ h) x) : U.Elements) ⟶
          U.elementsMk T'' (U.map h (U.map g x))).val = 𝟙 T'' := by
      change (CategoryOfElements.π U).map (eqToHom e) = 𝟙 T''
      rw [eqToHom_map]
      rfl
    apply CategoryOfElements.ext
    simp only [CategoryOfElements.comp_val, elementArrow,
      CategoryOfElements.homMk]
    rw [hval]
    simp
  dsimp [elementImageArrow]
  have hmapcast : f.map (eqToHom e) = eqToHom (congrArg f.obj e) := eqToHom_map f e
  simpa only [hmapcast, Functor.map_comp] using congrArg f.map he

private lemma elementImageArrow_map {C : Type u} [Category.{v} C]
    (U : Functor C (Type uU)) (p : F ⥤ C) (f : U.Elements ⥤ F)
    (over : f ⋙ p = CategoryOfElements.π U)
    {T T' : C} (g : T ⟶ T') (x : U.obj T) :
    p.map (elementImageArrow U f g x) =
      eqToHom (elementBaseEq p U f over T x) ≫ g ≫
        eqToHom (elementBaseEq p U f over T' (U.map g x)).symm := by
  simpa [elementArrow, elementImageArrow] using Functor.congr_hom over (elementArrow U g x)

/-- The image of `elementArrow U g x` in `F` lies over the corresponding base map. -/
private lemma elementImageArrow_isHomLift
    (T T' : C) (g : T ⟶ T') (x : U.obj T) :
    p.IsHomLift (eqToHom (elementBaseEq p U f over T x) ≫ g ≫
      eqToHom (elementBaseEq p U f over T' (U.map g x)).symm) (elementImageArrow U f g x) :=
  IsHomLift.of_fac' p _ _ rfl rfl (by simpa using elementImageArrow_map U p f over g x)

private lemma elementImageArrow_stronglyCocartesian
    (hp : IsCofiberedInGroupoids p) (T T' : C) (g : T ⟶ T') (x : U.obj T) :
    p.IsStronglyCocartesian (eqToHom (elementBaseEq p U f over T x) ≫ g ≫
      eqToHom (elementBaseEq p U f over T' (U.map g x)).symm) (elementImageArrow U f g x) :=
  stronglyCocartesian_of_opIsFiberedInGroupoids hp _ _
    (elementImageArrow_isHomLift p U f over T T' g x)

/-- A vertical presentation arrow lifts the canonical identification of the base objects. -/
private lemma presentationArrow_isHomLift_base {T : C} (a : PresentationArrow p U f over T) :
    p.IsHomLift (eqToHom (elementBaseEq p U f over T a.target) ≫
      eqToHom (elementBaseEq p U f over T a.source).symm) a.iso.hom :=
  IsHomLift.of_fac' p _ _ rfl rfl (by simp [a.vertical])

private noncomputable def mapPresentationArrow
    (hp : IsCofiberedInGroupoids p)
    {T T' : C} (g : T ⟶ T') (a : PresentationArrow p U f over T) :
    PresentationArrow p U f over T' := by
  let ut := elementImageArrow U f g a.target
  let us := elementImageArrow U f g a.source
  let baseTarget := eqToHom (elementBaseEq p U f over T a.target) ≫ g ≫
      eqToHom (elementBaseEq p U f over T' (U.map g a.target)).symm
  let baseSource := eqToHom (elementBaseEq p U f over T a.source) ≫ g ≫
      eqToHom (elementBaseEq p U f over T' (U.map g a.source)).symm
  have : p.IsHomLift baseTarget ut := elementImageArrow_isHomLift p U f over T T' g a.target
  have : p.IsStronglyCocartesian baseTarget ut :=
    elementImageArrow_stronglyCocartesian p U f over hp T T' g a.target
  have : p.IsHomLift baseSource us := elementImageArrow_isHomLift p U f over T T' g a.source
  let alpha := a.iso.hom ≫ us
  let baseVertical := eqToHom (elementBaseEq p U f over T a.target) ≫
      eqToHom (elementBaseEq p U f over T a.source).symm
  let baseAlpha := baseTarget ≫
      eqToHom (elementBaseEq p U f over T' (U.map g a.target)) ≫
      eqToHom (elementBaseEq p U f over T' (U.map g a.source)).symm
  have : p.IsHomLift baseVertical a.iso.hom := presentationArrow_isHomLift_base p U f over a
  have : p.IsHomLift baseAlpha alpha := by
    have hcomp : baseVertical ≫ baseSource = baseAlpha := by
      simp [baseVertical, baseSource, baseAlpha, baseTarget, eqToHom_trans_assoc]
    rw [← hcomp]
    infer_instance
  let baseIso : p.obj (f.obj ⟨T', U.map g a.target⟩) ≅
      p.obj (f.obj ⟨T', U.map g a.source⟩) :=
    eqToIso (elementBaseEq p U f over T' (U.map g a.target) |>.trans
      (elementBaseEq p U f over T' (U.map g a.source)).symm)
  have hbase : baseAlpha = baseTarget ≫ baseIso.hom := by
    dsimp [baseAlpha, baseTarget, baseIso]
    simp
  have : p.IsStronglyCocartesian baseAlpha alpha :=
    stronglyCocartesian_of_opIsFiberedInGroupoids hp baseAlpha alpha inferInstance
  let comparisonIso :=
    Functor.IsStronglyCocartesian.codomainIsoOfBaseIso (p := p) hbase ut alpha
  have hLift : p.IsHomLift baseIso.hom comparisonIso.hom := by
    dsimp [comparisonIso, Functor.IsStronglyCocartesian.codomainIsoOfBaseIso]
    exact Functor.IsStronglyCocartesian.map_isHomLift p baseTarget ut hbase alpha
  refine ⟨U.map g a.target, U.map g a.source, comparisonIso, ?_⟩
  simpa [baseIso] using (IsHomLift.eq_of_isHomLift p baseIso.hom comparisonIso.hom).symm

private lemma mapPresentationArrow_fac
    (hp : IsCofiberedInGroupoids p)
    {T T' : C} (g : T ⟶ T') (a : PresentationArrow p U f over T) :
    elementImageArrow U f g a.target ≫ (mapPresentationArrow p U f over hp g a).iso.hom =
      a.iso.hom ≫ elementImageArrow U f g a.source := by
  simp [mapPresentationArrow, Functor.IsStronglyCocartesian.codomainIsoOfBaseIso]

private lemma mapPresentationArrow_unique
    (hp : IsCofiberedInGroupoids p)
    {T T' : C} (g : T ⟶ T') (a : PresentationArrow p U f over T)
    (b : PresentationArrow p U f over T')
    (ht : b.target = U.map g a.target) (hs : b.source = U.map g a.source)
    (hfac : elementImageArrow U f g a.target ≫
      eqToHom (congrArg (fun x ↦ f.obj ⟨T', x⟩) ht).symm ≫ b.iso.hom ≫
      eqToHom (congrArg (fun x ↦ f.obj ⟨T', x⟩) hs) =
      a.iso.hom ≫ elementImageArrow U f g a.source) :
    b = mapPresentationArrow p U f over hp g a := by
  cases b with
  | mk target source iso vertical =>
    dsimp at ht hs
    subst target
    subst source
    apply presentationArrow_ext
    · rfl
    · rfl
    · apply heq_of_eq
      apply Iso.ext
      have := elementImageArrow_stronglyCocartesian p U f over hp T T' g a.target
      let baseIso := eqToHom (elementBaseEq p U f over T' (U.map g a.target)) ≫
        eqToHom (elementBaseEq p U f over T' (U.map g a.source)).symm
      have : p.IsHomLift baseIso (show f.obj ⟨T', U.map g a.target⟩ ⟶ f.obj ⟨T', U.map g a.source⟩
          from (mapPresentationArrow p U f over hp g a).iso.hom) :=
        presentationArrow_isHomLift_base p U f over (mapPresentationArrow p U f over hp g a)
      have : p.IsHomLift baseIso iso.hom :=
        presentationArrow_isHomLift_base p U f over ⟨_, _, iso, vertical⟩
      refine Functor.IsStronglyCocartesian.ext p
        (eqToHom (elementBaseEq p U f over T a.target) ≫ g ≫
          eqToHom (elementBaseEq p U f over T' (U.map g a.target)).symm)
        (elementImageArrow U f g a.target) baseIso ?_
      have hfac' : elementImageArrow U f g a.target ≫ iso.hom =
          a.iso.hom ≫ elementImageArrow U f g a.source := by simpa using hfac
      exact hfac'.trans (mapPresentationArrow_fac p U f over hp g a).symm

@[implicit_reducible]
private noncomputable def presentationArrowFunctor
    (hp : IsCofiberedInGroupoids p) : Functor C (Type (max w uU)) where
  obj T := PresentationArrow p U f over T
  map {T T'} g := ConcreteCategory.ofHom (TypeCat.Fun.mk fun a =>
    mapPresentationArrow p U f over hp g a)
  map_id T := by
    apply ConcreteCategory.ext
    apply TypeCat.Fun.ext
    funext a
    simp only [ConcreteCategory.hom_ofHom,
      TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk]
    change mapPresentationArrow p U f over hp (𝟙 T) a = a
    symm
    have ht : a.target = U.map (𝟙 T) a.target := by simp
    have hs : a.source = U.map (𝟙 T) a.source := by simp
    exact mapPresentationArrow_unique p U f over hp (𝟙 T) a a
      ht hs (by
        have hT := elementImageArrow_id U f a.target
        have hS := elementImageArrow_id U f a.source
        simp [hT, hS, eqToHom_trans_assoc])
  map_comp g h := by
    apply ConcreteCategory.ext
    apply TypeCat.Fun.ext
    funext a
    simp only [ConcreteCategory.hom_ofHom,
      TypeCat.Fun.toFun_apply, TypeCat.Fun.coe_mk]
    symm
    change mapPresentationArrow p U f over hp h
        (mapPresentationArrow p U f over hp g a) =
      mapPresentationArrow p U f over hp (g ≫ h) a
    let ha := mapPresentationArrow p U f over hp g a
    let hb := mapPresentationArrow p U f over hp h ha
    have ht : hb.target = U.map (g ≫ h) a.target := by simp [hb, ha, mapPresentationArrow]
    have hs : hb.source = U.map (g ≫ h) a.source := by simp [hb, ha, mapPresentationArrow]
    exact mapPresentationArrow_unique p U f over hp (g ≫ h) a hb ht hs (by
      have h₁ := mapPresentationArrow_fac (p := p) (U := U) (f := f)
        (over := over) (hp := hp) g a
      have h₂ := mapPresentationArrow_fac (p := p) (U := U) (f := f)
        (over := over) (hp := hp) h ha
      have targetEq : (U.elementsMk _ (U.map (g ≫ h) a.target) : U.Elements) =
          U.elementsMk _ (U.map h ha.target) :=
        Functor.Elements.ext _ _ rfl (by simp [ha, mapPresentationArrow])
      have sourceEq : (U.elementsMk _ (U.map (g ≫ h) a.source) : U.Elements) =
          U.elementsMk _ (U.map h ha.source) :=
        Functor.Elements.ext _ _ rfl (by simp [ha, mapPresentationArrow])
      have htarget := elementImageArrow_comp U f g h a.target targetEq
      have hsource := elementImageArrow_comp U f g h a.source sourceEq
      have htCast : eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) ht).symm =
          eqToHom (congrArg f.obj targetEq) := by
        congr 1
      have hsCast : eqToHom (congrArg f.obj sourceEq) =
          eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs).symm := by
        congr 1
      have htarget' : elementImageArrow U f (g ≫ h) a.target ≫
          eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) ht).symm =
            elementImageArrow U f g a.target ≫ elementImageArrow U f h ha.target := by
        simpa [htCast, ht, ha, hb, mapPresentationArrow] using htarget
      have hsource' : elementImageArrow U f (g ≫ h) a.source ≫
          eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs).symm =
            elementImageArrow U f g a.source ≫ elementImageArrow U f h ha.source := by
        simpa [hsCast, hs, ha, hb, mapPresentationArrow] using hsource
      have h₂' : elementImageArrow U f h ha.target ≫ hb.iso.hom =
          ha.iso.hom ≫ elementImageArrow U f h ha.source := by
        simpa [hb] using h₂
      have hsourceComp :
          (elementImageArrow U f g a.source ≫ elementImageArrow U f h ha.source) ≫
            eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs) =
          elementImageArrow U f (g ≫ h) a.source := by
        rw [hsource'.symm]
        exact comp_eqToHom_comp_eqToHom_symm _ _
      calc
        elementImageArrow U f (g ≫ h) a.target ≫
            eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) ht).symm ≫ hb.iso.hom ≫
              eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs) =
            ((elementImageArrow U f (g ≫ h) a.target ≫
              eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) ht).symm) ≫
              hb.iso.hom) ≫ eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs) := by
                simp only [Category.assoc]
        _ = ((elementImageArrow U f g a.target ≫ elementImageArrow U f h ha.target) ≫
              hb.iso.hom) ≫ eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs) := by
                with_unfolding_all
                exact congrArg (fun q ↦ (q ≫ hb.iso.hom) ≫
                  eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs)) htarget'
        _ = (elementImageArrow U f g a.target ≫
              (elementImageArrow U f h ha.target ≫ hb.iso.hom)) ≫
              eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs) := by
                exact congrArg (fun q ↦ q ≫ eqToHom
                  (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs))
                  (Category.assoc (elementImageArrow U f g a.target)
                    (elementImageArrow U f h ha.target) hb.iso.hom)
        _ = (elementImageArrow U f g a.target ≫
              (ha.iso.hom ≫ elementImageArrow U f h ha.source)) ≫
              eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs) := by
                with_unfolding_all
                exact congrArg (fun q ↦ (elementImageArrow U f g a.target ≫ q) ≫
                  eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs)) h₂'
        _ = ((elementImageArrow U f g a.target ≫ ha.iso.hom) ≫
              elementImageArrow U f h ha.source) ≫
              eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs) := by
                exact congrArg (fun q ↦ q ≫ eqToHom
                  (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs))
                  (Category.assoc (elementImageArrow U f g a.target) ha.iso.hom
                    (elementImageArrow U f h ha.source)).symm
        _ = ((a.iso.hom ≫ elementImageArrow U f g a.source) ≫
              elementImageArrow U f h ha.source) ≫
              eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs) := by
                with_unfolding_all
                exact congrArg (fun q ↦ (q ≫ elementImageArrow U f h ha.source) ≫
                  eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs)) h₁
        _ = (a.iso.hom ≫
              (elementImageArrow U f g a.source ≫ elementImageArrow U f h ha.source)) ≫
              eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs) := by
                exact congrArg (fun q ↦ q ≫
                  eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs))
                  (Category.assoc a.iso.hom (elementImageArrow U f g a.source)
                    (elementImageArrow U f h ha.source))
        _ = a.iso.hom ≫
              ((elementImageArrow U f g a.source ≫ elementImageArrow U f h ha.source) ≫
                eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs)) := by
                exact Category.assoc a.iso.hom
                  (elementImageArrow U f g a.source ≫ elementImageArrow U f h ha.source)
                  (eqToHom (congrArg (fun x ↦ f.obj (U.elementsMk _ x)) hs))
        _ = a.iso.hom ≫ elementImageArrow U f (g ≫ h) a.source := by
                with_unfolding_all
                exact congrArg (fun q ↦ a.iso.hom ≫ q) hsourceComp)

private lemma presentationArrow_vertical_lift {T : C}
    (a : PresentationArrow p U f over T) :
    p.IsHomLift (𝟙 T) a.iso.hom := by
  apply IsHomLift.of_fac' p (𝟙 T) a.iso.hom
    (elementBaseEq p U f over T a.target)
    (elementBaseEq p U f over T a.source)
  simpa using a.vertical

@[implicit_reducible]
private def presentationTwoFibreObject {T : C}
    (a : PresentationArrow p U f over T) :
    TwoFibreProductOver (CategoryOfElements.π U)
      (CategoryOfElements.π U) p f f := {
  base := T
  x := U.elementsMk T a.target
  y := U.elementsMk T a.source
  hx := rfl
  hy := rfl
  iso := a.iso
  vertical := presentationArrow_vertical_lift p U f over a
}

private noncomputable def presentationToTwoFibreHom {T T' : C}
    (hp : IsCofiberedInGroupoids p)
    (a : PresentationArrow p U f over T) (b : PresentationArrow p U f over T')
    (g : T ⟶ T') (hR : mapPresentationArrow p U f over hp g a = b) :
    presentationTwoFibreObject p U f over a ⟶ presentationTwoFibreObject p U f over b := by
  have ht : U.map g a.target = b.target := by
    simpa [mapPresentationArrow] using congrArg PresentationArrow.target hR
  have hs : U.map g a.source = b.source := by
    simpa [mapPresentationArrow] using congrArg PresentationArrow.source hR
  let eTarget := CategoryOfElements.homMk
    (U.elementsMk T a.target) (U.elementsMk T' b.target) g ht
  let eSource := CategoryOfElements.homMk
    (U.elementsMk T a.source) (U.elementsMk T' b.source) g hs
  refine {
    hbase := g
    a := eTarget
    b := eSource
    ha := IsHomLift.of_fac' (CategoryOfElements.π U) g eTarget rfl rfl (by simp [eTarget])
    hb := IsHomLift.of_fac' (CategoryOfElements.π U) g eSource rfl rfl (by simp [eSource])
    w := by
      cases hR
      change f.map eTarget ≫
          (mapPresentationArrow p U f over hp g a).iso.hom =
        a.iso.hom ≫ f.map eSource
      simpa [eTarget, eSource, elementArrow, elementImageArrow,
        mapPresentationArrow] using
        (mapPresentationArrow_fac (p := p) (U := U) (f := f)
          (over := over) (hp := hp) g a)
  }

private lemma presentationToTwoFibreHom_hbase {T T' : C}
    (hp : IsCofiberedInGroupoids p)
    (a : PresentationArrow p U f over T) (b : PresentationArrow p U f over T')
    (g : T ⟶ T') (hR : mapPresentationArrow p U f over hp g a = b) :
    (presentationToTwoFibreHom p U f over hp a b g hR).hbase = g := by
  cases hR; rfl

private lemma presentationToTwoFibreHom_a_val {T T' : C}
    (hp : IsCofiberedInGroupoids p)
    (a : PresentationArrow p U f over T) (b : PresentationArrow p U f over T')
    (g : T ⟶ T') (hR : mapPresentationArrow p U f over hp g a = b) :
    (presentationToTwoFibreHom p U f over hp a b g hR).a.val = g := by
  cases hR; rfl

private lemma presentationToTwoFibreHom_b_val {T T' : C}
    (hp : IsCofiberedInGroupoids p)
    (a : PresentationArrow p U f over T) (b : PresentationArrow p U f over T')
    (g : T ⟶ T') (hR : mapPresentationArrow p U f over hp g a = b) :
    (presentationToTwoFibreHom p U f over hp a b g hR).b.val = g := by
  cases hR; rfl

attribute [local simp] presentationToTwoFibreHom_hbase
  presentationToTwoFibreHom_a_val presentationToTwoFibreHom_b_val

@[implicit_reducible]
private noncomputable def presentationToTwoFibreFunctor
    (hp : IsCofiberedInGroupoids p) :
    (presentationArrowFunctor p U f over hp).Elements ⥤
      TwoFibreProductOver (CategoryOfElements.π U)
        (CategoryOfElements.π U) p f f where
  obj q := presentationTwoFibreObject p U f over q.2
  map {P Q} e := presentationToTwoFibreHom p U f over hp P.2 Q.2 e.val (by
    have h := CategoryOfElements.map_snd e
    change mapPresentationArrow p U f over hp e.val P.2 = Q.2 at h
    exact h)
  map_id P := by
    cases P
    apply TwoFibreProductOver.Hom.ext
    · exact CategoryOfElements.id_val
    · apply CategoryOfElements.ext; exact CategoryOfElements.id_val
    · apply CategoryOfElements.ext; exact CategoryOfElements.id_val
  map_comp {X Y Z} e₁ e₂ := by
    cases X; cases Y; cases Z
    apply TwoFibreProductOver.Hom.ext
    · exact CategoryOfElements.comp_val
    · apply CategoryOfElements.ext; exact CategoryOfElements.comp_val
    · apply CategoryOfElements.ext; exact CategoryOfElements.comp_val

private noncomputable def presentationArrowOfTwoFibreProduct
    (Q : TwoFibreProductOver (CategoryOfElements.π U)
      (CategoryOfElements.π U) p f f) : PresentationArrow p U f over Q.base := by
  let target := U.map (eqToHom Q.hx) Q.x.2
  let source := U.map (eqToHom Q.hy) Q.y.2
  have htarget : (Q.x : U.Elements) = U.elementsMk Q.base target :=
    Functor.Elements.ext Q.x (U.elementsMk Q.base target) Q.hx (by simp [target])
  have hsource : (Q.y : U.Elements) = U.elementsMk Q.base source :=
    Functor.Elements.ext Q.y (U.elementsMk Q.base source) Q.hy (by simp [source])
  let targetIso : f.obj Q.x ≅ f.obj (U.elementsMk Q.base target) :=
    eqToIso (congrArg f.obj htarget)
  let sourceIso : f.obj Q.y ≅ f.obj (U.elementsMk Q.base source) :=
    eqToIso (congrArg f.obj hsource)
  let targetBase := elementBaseEq p U f over Q.base target
  let sourceBase := elementBaseEq p U f over Q.base source
  let targetOldBase := (Functor.congr_obj over Q.x).trans Q.hx
  let sourceOldBase := (Functor.congr_obj over Q.y).trans Q.hy
  have hTargetCast : p.map targetIso.symm.hom =
      eqToHom (targetBase.trans targetOldBase.symm) := by
    simp [targetIso, eqToHom_map]
  have hSourceCast : p.map sourceIso.hom =
      eqToHom (sourceOldBase.trans sourceBase.symm) := by
    simp [sourceIso, eqToHom_map]
  let imageIso := targetIso.symm ≪≫ Q.iso ≪≫ sourceIso
  have hq : p.map Q.iso.hom = eqToHom
      targetOldBase ≫ eqToHom sourceOldBase.symm := by
    let := Q.vertical
    simpa using (IsHomLift.fac' p (𝟙 Q.base) Q.iso.hom)
  refine ⟨target, source, imageIso, ?_⟩
  change p.map (targetIso.symm.hom ≫ Q.iso.hom ≫ sourceIso.hom) = _
  rw [Functor.map_comp, Functor.map_comp, hTargetCast, hq, hSourceCast]
  simp

private abbrev PresentationFibreProduct :=
  TwoFibreProductOver (CategoryOfElements.π U)
    (CategoryOfElements.π U) p f f

private def presentationFibreTarget (Q : PresentationFibreProduct p U f) : U.obj Q.base :=
  U.map (eqToHom Q.hx) Q.x.2

private def presentationFibreSource (Q : PresentationFibreProduct p U f) : U.obj Q.base :=
  U.map (eqToHom Q.hy) Q.y.2

private lemma presentationFibreTargetEq (Q : PresentationFibreProduct p U f) :
    Q.x = U.elementsMk Q.base (presentationFibreTarget p U f Q) :=
  Functor.Elements.ext Q.x _ Q.hx (by simp [presentationFibreTarget])

private lemma presentationFibreSourceEq (Q : PresentationFibreProduct p U f) :
    Q.y = U.elementsMk Q.base (presentationFibreSource p U f Q) :=
  Functor.Elements.ext Q.y _ Q.hy (by simp [presentationFibreSource])

private def presentationFibreTargetIso (Q : PresentationFibreProduct p U f) :
    f.obj Q.x ≅ f.obj (U.elementsMk Q.base (presentationFibreTarget p U f Q)) :=
  eqToIso (congrArg f.obj (presentationFibreTargetEq p U f Q))

private def presentationFibreSourceIso (Q : PresentationFibreProduct p U f) :
    f.obj Q.y ≅ f.obj (U.elementsMk Q.base (presentationFibreSource p U f Q)) :=
  eqToIso (congrArg f.obj (presentationFibreSourceEq p U f Q))

/-- The underlying map of the comparison isomorphism coming from an equality of elements. -/
private lemma elements_eqToHom_val {V : C ⥤ Type*} {x y : V.Elements} (h : x = y) :
    (eqToHom h).val = eqToHom (congrArg Sigma.fst h) :=
  eqToHom_map (CategoryOfElements.π V) h

private lemma presentationFibreHom_a_val
    {Q Q' : PresentationFibreProduct p U f} (e : Q ⟶ Q') :
    e.a.val = eqToHom Q.hx ≫ e.hbase ≫ eqToHom Q'.hx.symm := by
  have := e.ha
  exact IsHomLift.fac' (CategoryOfElements.π U) e.hbase e.a

private lemma presentationFibreHom_b_val
    {Q Q' : PresentationFibreProduct p U f} (e : Q ⟶ Q') :
    e.b.val = eqToHom Q.hy ≫ e.hbase ≫ eqToHom Q'.hy.symm := by
  have := e.hb
  exact IsHomLift.fac' (CategoryOfElements.π U) e.hbase e.b

/-- A morphism of elements over `g` relates the points of the fibres over `T` and `T'`. -/
private lemma map_eqToHom_snd_eq {T T' : C} (g : T ⟶ T') {x x' : U.Elements}
    (hx : x.1 = T) (hx' : x'.1 = T') (a : x ⟶ x')
    (ha : a.val = eqToHom hx ≫ g ≫ eqToHom hx'.symm) :
    U.map (eqToHom hx') x'.2 = U.map g (U.map (eqToHom hx) x.2) := by
  rw [← CategoryOfElements.map_snd a, ha]
  simp [Functor.map_comp]

private lemma presentationFibreTarget_map
    {Q Q' : PresentationFibreProduct p U f} (e : Q ⟶ Q') :
    (presentationArrowOfTwoFibreProduct p U f over Q').target =
      U.map e.hbase (presentationArrowOfTwoFibreProduct p U f over Q).target :=
  map_eqToHom_snd_eq U e.hbase Q.hx Q'.hx e.a (presentationFibreHom_a_val p U f e)

private lemma presentationFibreSource_map
    {Q Q' : PresentationFibreProduct p U f} (e : Q ⟶ Q') :
    (presentationArrowOfTwoFibreProduct p U f over Q').source =
      U.map e.hbase (presentationArrowOfTwoFibreProduct p U f over Q).source :=
  map_eqToHom_snd_eq U e.hbase Q.hy Q'.hy e.b (presentationFibreHom_b_val p U f e)

/-- The image in `F` of `elementArrow U g t`, normalized by comparison isomorphisms. -/
private lemma elementImageArrow_conj {T T' : C} (g : T ⟶ T') {x x' : U.Elements}
    (t : U.obj T) (t' : U.obj T') (ex : x = U.elementsMk T t) (ex' : x' = U.elementsMk T' t')
    (cast : U.elementsMk T' t' = U.elementsMk T' (U.map g t)) (a : x ⟶ x')
    (ha : a.val = eqToHom (congrArg Sigma.fst ex) ≫ g ≫ eqToHom (congrArg Sigma.fst ex').symm) :
    elementImageArrow U f g t ≫ eqToHom (congrArg f.obj cast.symm) =
      (eqToIso (congrArg f.obj ex)).symm.hom ≫ f.map a ≫ (eqToIso (congrArg f.obj ex')).hom := by
  have key : elementArrow U g t ≫ eqToHom cast.symm = eqToHom ex.symm ≫ a ≫ eqToHom ex' := by
    apply CategoryOfElements.ext
    simp [elementArrow, elements_eqToHom_val, ha]
  simpa [elementImageArrow, eqToHom_map] using congrArg f.map key

private lemma conjugated_square {D : Type*} [Category D]
    {A B A' B' X Y X' Y' S T : D}
    (i : A ≅ X) (j : B ≅ Y) (i' : A' ≅ X') (j' : B' ≅ Y')
    (α : A ⟶ B) (β : A' ⟶ B') (l : A ⟶ A') (r : B ⟶ B')
    (ut : X ⟶ S) (kt : S ⟶ X') (us : Y ⟶ T) (ks : T ⟶ Y') (ks' : Y' ⟶ T)
    (ht : ut ≫ kt = i.inv ≫ l ≫ i'.hom)
    (hs : us ≫ ks = j.inv ≫ r ≫ j'.hom) (hk : ks ≫ ks' = 𝟙 T)
    (hw : l ≫ β = α ≫ r) :
    ut ≫ kt ≫ (i'.inv ≫ β ≫ j'.hom) ≫ ks' =
      (i.inv ≫ α ≫ j.hom) ≫ us := by
  have hs' : r ≫ j'.hom = j.hom ≫ us ≫ ks := by rw [hs]; simp
  calc
    _ = (ut ≫ kt) ≫ i'.inv ≫ β ≫ j'.hom ≫ ks' := by simp only [Category.assoc]
    _ = i.inv ≫ l ≫ β ≫ j'.hom ≫ ks' := by rw [ht]; simp
    _ = i.inv ≫ α ≫ (r ≫ j'.hom) ≫ ks' := by rw [← Category.assoc l, hw]; simp
    _ = _ := by rw [hs']; simp only [Category.assoc, hk, Category.comp_id]

@[implicit_reducible]
private noncomputable def presentationFromTwoFibreFunctor
    (hp : IsCofiberedInGroupoids p) :
    PresentationFibreProduct p U f ⥤
      (presentationArrowFunctor p U f over hp).Elements where
  obj Q := ⟨Q.base, presentationArrowOfTwoFibreProduct p U f over Q⟩
  map {Q Q'} e := CategoryOfElements.homMk _ _ e.hbase (by
    let a := presentationArrowOfTwoFibreProduct p U f over Q
    let b := presentationArrowOfTwoFibreProduct p U f over Q'
    have ht : b.target = U.map e.hbase a.target := presentationFibreTarget_map p U f over e
    have hs : b.source = U.map e.hbase a.source := presentationFibreSource_map p U f over e
    have htn := elementImageArrow_conj U f e.hbase a.target b.target
      (presentationFibreTargetEq p U f Q) (presentationFibreTargetEq p U f Q')
      (congrArg (U.elementsMk Q'.base) ht) e.a (presentationFibreHom_a_val p U f e)
    have hsn := elementImageArrow_conj U f e.hbase a.source b.source
      (presentationFibreSourceEq p U f Q) (presentationFibreSourceEq p U f Q')
      (congrArg (U.elementsMk Q'.base) hs) e.b (presentationFibreHom_b_val p U f e)
    exact (mapPresentationArrow_unique p U f over hp e.hbase a b ht hs
      (conjugated_square (presentationFibreTargetIso p U f Q) (presentationFibreSourceIso p U f Q)
        (presentationFibreTargetIso p U f Q') (presentationFibreSourceIso p U f Q')
        Q.iso.hom Q'.iso.hom (f.map e.a) (f.map e.b) _ _ _ _ _ htn hsn
        ((eqToHom_trans _ _).trans (eqToHom_refl _ _)) e.w)).symm)
  map_id Q := by
    apply CategoryOfElements.ext
    rfl
  map_comp e₁ e₂ := by
    apply CategoryOfElements.ext
    rfl

private lemma iso_conjugation_heq {D : Type*} [Category D]
    {A B A' B' : D} (hA : A = A') (hB : B = B') (i : A ≅ B) :
    HEq ((eqToIso hA).symm ≪≫ i ≪≫ eqToIso hB) i := by
  cases hA
  cases hB
  simp

private lemma presentationFibreObject_ext
    {Q Q' : PresentationFibreProduct p U f}
    (hb : Q.base = Q'.base) (hx : Q.x = Q'.x) (hy : Q.y = Q'.y)
    (hi : HEq Q.iso Q'.iso) : Q = Q' := by
  cases Q; cases Q'; cases hb; cases hx; cases hy; cases hi; rfl

private lemma presentationArrowOfTwoFibreProduct_toObject {T : C}
    (a : PresentationArrow p U f over T) :
    presentationArrowOfTwoFibreProduct p U f over
      (presentationTwoFibreObject p U f over a) = a := by
  apply presentationArrow_ext
  · change U.map (𝟙 T) a.target = a.target
    simp
  · change U.map (𝟙 T) a.source = a.source
    simp
  · exact iso_conjugation_heq _ _ a.iso

private lemma presentationTwoFibreObject_fromObject
    (Q : PresentationFibreProduct p U f) :
    presentationTwoFibreObject p U f over
      (presentationArrowOfTwoFibreProduct p U f over Q) = Q :=
  presentationFibreObject_ext p U f rfl (presentationFibreTargetEq p U f Q).symm
    (presentationFibreSourceEq p U f Q).symm (iso_conjugation_heq _ _ Q.iso)

private lemma presentationFibreHom_ext
    {Q Q' : PresentationFibreProduct p U f} {g h : Q ⟶ Q'}
    (he : g.hbase = h.hbase) : g = h := by
  apply TwoFibreProductOver.Hom.ext he
  · apply Subtype.ext
    rw [presentationFibreHom_a_val, presentationFibreHom_a_val, he]
  · apply Subtype.ext
    rw [presentationFibreHom_b_val, presentationFibreHom_b_val, he]

private lemma fibreProduct_eqToHom_hbase {Q Q' : PresentationFibreProduct p U f}
    (h : Q = Q') : (eqToHom h).hbase =
      eqToHom (congrArg TwoFibreProductOver.base h) :=
  eqToHom_map (TwoFibreProductOver.structureFunctor _ _ p f f) h

private lemma presentationUnitObjectEq
    (hp : IsCofiberedInGroupoids p)
    (x : (presentationArrowFunctor p U f over hp).Elements) :
    x = (presentationToTwoFibreFunctor p U f over hp ⋙
      presentationFromTwoFibreFunctor p U f over hp).obj x :=
  congrArg (fun a => (presentationArrowFunctor p U f over hp).elementsMk x.1 a)
    (presentationArrowOfTwoFibreProduct_toObject p U f over x.2).symm

private lemma presentationUnitObjectEq_base
    (hp : IsCofiberedInGroupoids p)
    (x : (presentationArrowFunctor p U f over hp).Elements) :
    ((eqToIso (presentationUnitObjectEq p U f over hp x)).hom).val = 𝟙 x.1 :=
  (elements_eqToHom_val (presentationUnitObjectEq p U f over hp x)).trans (eqToHom_refl _ _)

private lemma presentationTwoFibreObject_fromObject_base
    (Q : PresentationFibreProduct p U f) :
    ((eqToIso (presentationTwoFibreObject_fromObject p U f over Q)).hom).hbase =
      𝟙 Q.base :=
  (fibreProduct_eqToHom_hbase p U f
    (presentationTwoFibreObject_fromObject p U f over Q)).trans (eqToHom_refl _ _)

private noncomputable def presentationFibreEquivalence
    (hp : IsCofiberedInGroupoids p) :
    (presentationArrowFunctor p U f over hp).Elements ≌ PresentationFibreProduct p U f where
  functor := presentationToTwoFibreFunctor p U f over hp
  inverse := presentationFromTwoFibreFunctor p U f over hp
  unitIso := NatIso.ofComponents (fun x => eqToIso (presentationUnitObjectEq p U f over hp x))
    (by
      intro x y g
      apply Subtype.ext
      simp only [Functor.id_map, Functor.comp_map, CategoryOfElements.comp_val]
      have hx := presentationUnitObjectEq_base p U f over hp x
      have hy := presentationUnitObjectEq_base p U f over hp y
      rw [hx, hy]
      change g.val ≫ 𝟙 _ = 𝟙 _ ≫ g.val
      simp)
  counitIso := NatIso.ofComponents (fun Q =>
    eqToIso (presentationTwoFibreObject_fromObject p U f over Q)) (by
      intro Q Q' g
      apply presentationFibreHom_ext p U f
      simp only [Functor.id_map, Functor.comp_map, eqToIso.hom,
        presentationFromTwoFibreFunctor, presentationToTwoFibreFunctor]
      simp only [TwoFibreProductOver.comp_hbase, presentationToTwoFibreHom_hbase,
        fibreProduct_eqToHom_hbase, CategoryOfElements.homMk]
      change g.hbase ≫ 𝟙 _ = 𝟙 _ ≫ g.hbase
      simp)
  functor_unitIso_comp x := by
    have h1 := presentationUnitObjectEq_base p U f over hp x
    have h2 := presentationTwoFibreObject_fromObject_base p U f over
      (presentationTwoFibreObject p U f over x.2)
    apply presentationFibreHom_ext p U f
    simp only [TwoFibreProductOver.comp_hbase, TwoFibreProductOver.id_hbase,
      presentationToTwoFibreFunctor, NatIso.ofComponents_hom_app,
      presentationToTwoFibreHom_hbase, h1, h2]
    exact Category.id_comp _

private def presentationVerticalIsoHom (T : C) (x y : U.obj T) :=
  {i : f.obj ⟨T, y⟩ ≅ f.obj ⟨T, x⟩ //
    p.map i.hom = eqToHom (elementBaseEq p U f over T y) ≫
      eqToHom (elementBaseEq p U f over T x).symm}

@[implicit_reducible]
private def presentationVerticalIsoCategory (T : C) : Category (U.obj T) where
  Hom x y := presentationVerticalIsoHom p U f over T x y
  id x := ⟨Iso.refl _, by simp⟩
  comp g h := ⟨h.1.trans g.1, by
    rw [Iso.trans_hom, Functor.map_comp, h.2, g.2]
    simp⟩
  id_comp g := by
    apply Subtype.ext; apply Iso.ext
    simp
  comp_id g := by
    apply Subtype.ext; apply Iso.ext
    simp
  assoc f g h := by
    apply Subtype.ext; apply Iso.ext
    simp

private lemma presentationVerticalIso_symm {T : C} {x y : U.obj T}
    (i : presentationVerticalIsoHom p U f over T x y) :
    p.map i.1.symm.hom = eqToHom (elementBaseEq p U f over T x) ≫
      eqToHom (elementBaseEq p U f over T y).symm := by
  have hIso : p.mapIso i.1 = eqToIso
      ((elementBaseEq p U f over T y).trans
        (elementBaseEq p U f over T x).symm) := by
    apply Iso.ext
    simpa using i.2
  calc
    p.map i.1.symm.hom = (p.mapIso i.1).inv := by simp
    _ = (eqToIso ((elementBaseEq p U f over T y).trans
        (elementBaseEq p U f over T x).symm)).inv := congrArg Iso.inv hIso
    _ = eqToHom (elementBaseEq p U f over T x) ≫
        eqToHom (elementBaseEq p U f over T y).symm := by simp

@[implicit_reducible]
private noncomputable def presentationArrowGroupoid (T : C) : Groupoid (U.obj T) := by
  exact {
    toCategory := presentationVerticalIsoCategory p U f over T
    inv := fun a => ⟨a.1.symm, presentationVerticalIso_symm p U f over a⟩
    inv_comp := by
      intro x y a
      apply Subtype.ext; apply Iso.ext
      change (a.1.trans a.1.symm).hom = (Iso.refl _).hom
      simp
    comp_inv := by
      intro x y a
      apply Subtype.ext; apply Iso.ext
      change (a.1.symm.trans a.1).hom = (Iso.refl _).hom
      simp
  }

private def presentationArrowHomEquiv (T : C) (x y : U.obj T) :
    presentationVerticalIsoHom p U f over T x y ≃
      {a : PresentationArrow p U f over T // a.source = x ∧ a.target = y} where
  toFun a := ⟨⟨y, x, a.1, a.2⟩, rfl, rfl⟩
  invFun a := by
    rcases a with ⟨⟨target, source, iso, vertical⟩, hs, ht⟩
    change source = x at hs
    change target = y at ht
    subst source; subst target
    exact ⟨iso, vertical⟩
  left_inv _ := rfl
  right_inv a := by
    rcases a with ⟨⟨target, source, iso, vertical⟩, hs, ht⟩
    change source = x at hs
    change target = y at ht
    cases hs; cases ht; rfl

private lemma presentationPointwiseGroupoid (T : C) :
    Nonempty (PointwiseGroupoid
      (fun a : PresentationArrow p U f over T => ULift.up.{w, uU} a.source)
      (fun a => ULift.up.{w, uU} a.target)
      (fun q => PresentationArrow.comp (p := p) (U := U) (f := f) (over := over)
        q.1.1 q.1.2 (congrArg (ULift.down.{w, uU}) q.2))) := by
  let : Category (U.obj T) := presentationVerticalIsoCategory p U f over T
  let : Groupoid (U.obj T) := presentationArrowGroupoid p U f over T
  let : CategoryTheory.Category.{max w uU} (ULift.{w, uU} (U.obj T)) := {
    Hom x y := ULift.{max w uU, w} (x.down ⟶ y.down)
    id x := ULift.up (𝟙 x.down)
    comp g h := ULift.up (g.down ≫ h.down)
    id_comp g := by apply ULift.ext; simp
    comp_id g := by apply ULift.ext; simp
    assoc f g h := by apply ULift.ext; simp [Category.assoc]
  }
  let : Groupoid.{max w uU} (ULift.{w, uU} (U.obj T)) := {
    toCategory := inferInstance
    inv := fun g => ULift.up ((presentationArrowGroupoid p U f over T).inv g.down)
    inv_comp := by
      intro x y g
      apply ULift.ext
      exact (presentationArrowGroupoid p U f over T).inv_comp g.down
    comp_inv := by
      intro x y g
      apply ULift.ext
      exact (presentationArrowGroupoid p U f over T).comp_inv g.down
  }
  refine ⟨{
    groupoid := inferInstance
    arrowEquiv := fun x y => by
      cases x with
      | up x =>
        cases y with
        | up y =>
          let e := presentationArrowHomEquiv p U f over T x y
          exact {
            toFun := fun k =>
              let z := e k.down
              ⟨z.1, ⟨congrArg (ULift.up.{w, uU}) z.2.1,
                congrArg (ULift.up.{w, uU}) z.2.2⟩⟩
            invFun := fun z => ULift.up (e.symm ⟨z.1, by
              constructor
              · exact congrArg (ULift.down.{w, uU}) z.2.1
              · exact congrArg (ULift.down.{w, uU}) z.2.2⟩)
            left_inv := by
              intro k
              apply ULift.ext
              dsimp
              let q : { a : PresentationArrow p U f over T //
                    a.source = x ∧ a.target = y } := ⟨(e k.down).1, by
                constructor
                · exact congrArg (ULift.down.{w, uU})
                    (congrArg (ULift.up.{w, uU}) (e k.down).2.1)
                · exact congrArg (ULift.down.{w, uU})
                    (congrArg (ULift.up.{w, uU}) (e k.down).2.2)⟩
              change e.symm q = k.down
              have hq : q = e k.down := by
                apply Subtype.ext
                rfl
              rw [hq]
              exact e.left_inv k.down
            right_inv := by
              intro z
              apply Subtype.ext
              simp [e]
          }
    comp_eq := ?_
  }⟩
  intro x y z g h
  apply presentationArrow_ext
  · rfl
  · rfl
  · apply heq_of_eq
    apply Iso.ext
    rfl

private lemma comp_square {D : Type*} [Category D]
    {A B C A' B' C' : D} (u : A ⟶ A') (v : B ⟶ B') (w : C ⟶ C')
    (a : A ⟶ B) (b : B ⟶ C) (a' : A' ⟶ B') (b' : B' ⟶ C')
    (ha : u ≫ a' = a ≫ v) (hb : v ≫ b' = b ≫ w) :
    u ≫ (a' ≫ b') = (a ≫ b) ≫ w := by
  rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc]

private lemma mapPresentationArrow_comp
    (hp : IsCofiberedInGroupoids p)
    {T T' : C} (g : T ⟶ T') (a b : PresentationArrow p U f over T)
    (h : a.source = b.target) :
    mapPresentationArrow p U f over hp g
      (PresentationArrow.comp p U f over a b h) =
      PresentationArrow.comp p U f over (mapPresentationArrow p U f over hp g a)
        (mapPresentationArrow p U f over hp g b) (congrArg (U.map g) h) := by
  rcases a with ⟨x, y, i, hi⟩
  rcases b with ⟨z, t, j, hj⟩
  change y = z at h
  subst z
  symm
  refine mapPresentationArrow_unique p U f over hp g _ _ ?_ ?_ ?_
  · rfl
  · rfl
  change elementImageArrow U f g x ≫ 𝟙 _ ≫
      ((mapPresentationArrow p U f over hp g ⟨x, y, i, hi⟩).iso.hom ≫
        (mapPresentationArrow p U f over hp g ⟨y, t, j, hj⟩).iso.hom) ≫ 𝟙 _ =
      (i.hom ≫ j.hom) ≫ elementImageArrow U f g t
  simp only [Category.id_comp, Category.comp_id]
  with_unfolding_all
    exact comp_square (elementImageArrow U f g x) (elementImageArrow U f g y)
      (elementImageArrow U f g t) i.hom j.hom _ _
      (mapPresentationArrow_fac p U f over hp g ⟨x, y, i, hi⟩)
      (mapPresentationArrow_fac p U f over hp g ⟨y, t, j, hj⟩)

private noncomputable def presentationSource
    (hp : IsCofiberedInGroupoids p) :
    presentationArrowFunctor p U f over hp ⟶ U ⋙ uliftFunctor.{w, uU} where
  app T := ↾fun a => ULift.up a.source
  naturality := by intros; rfl

private noncomputable def presentationTarget
    (hp : IsCofiberedInGroupoids p) :
    presentationArrowFunctor p U f over hp ⟶ U ⋙ uliftFunctor.{w, uU} where
  app T := ↾fun a => ULift.up a.target
  naturality := by intros; rfl

private noncomputable def presentationComp
    (hp : IsCofiberedInGroupoids p) :
    composableArrows (U ⋙ uliftFunctor.{w, uU})
      (presentationArrowFunctor p U f over hp)
      (presentationSource p U f over hp) (presentationTarget p U f over hp) ⟶
      presentationArrowFunctor p U f over hp where
  app T := ↾fun q =>
    PresentationArrow.comp p U f over q.1.1 q.1.2 (congrArg ULift.down q.2)
  naturality := by
    intro X Y g
    ext q
    exact (mapPresentationArrow_comp p U f over hp g q.1.1 q.1.2
      (congrArg ULift.down q.2)).symm

/-- The presentation data attached to a morphism from `U` to `F`: a groupoid in functors whose
arrow functor is the two-fibre product, and whose source, target, and composition are the
prescribed projections. -/
structure PresentationGroupoid where
  /-- The functor `R = U ×_F U`. -/
  arrows : Functor C (Type (max w uU))
  /-- The second projection `s : R ⟶ U`. -/
  source : NatTrans arrows (U ⋙ uliftFunctor.{w, uU})
  /-- The first projection `t : R ⟶ U`. -/
  target : NatTrans arrows (U ⋙ uliftFunctor.{w, uU})
  /-- Projection onto the first and last factors. -/
  comp : NatTrans
    (composableArrows (U ⋙ uliftFunctor.{w, uU}) arrows source target) arrows
  /-- The resulting operations give a groupoid in every fibre. -/
  pointwiseGroupoid : ∀ T, Nonempty
    (PointwiseGroupoid
      (source.app T) (target.app T) (fun q ↦ comp.app T q))
  /-- The category of elements of `R` is the two-fibre product category. -/
  fibreProductEquivalence : arrows.Elements ≌
    TwoFibreProductOver (CategoryOfElements.π U) (CategoryOfElements.π U) p f f
  /-- The equivalence respects the structure functors to the base category. -/
  fibreProductOverBase :
    fibreProductEquivalence.functor ⋙
        TwoFibreProductOver.structureFunctor (CategoryOfElements.π U)
          (CategoryOfElements.π U) p f f = CategoryOfElements.π arrows
  /-- Under the preceding equivalence, the first projection is `t`. -/
  targetProjectionIso :
    fibreProductEquivalence.functor ⋙
        TwoFibreProductOver.fst (CategoryOfElements.π U)
          (CategoryOfElements.π U) p f f ≅
      CategoryOfElements.map target ⋙ (uliftElementsEquivalence U).inverse
  /-- The first projection comparison lifts the identity in the base. -/
  targetProjectionIso_vertical : ∀ x : arrows.Elements,
    (CategoryOfElements.π U).map (targetProjectionIso.hom.app x) =
      eqToHom ((fibreProductEquivalence.functor.obj x).hx.trans
        (Functor.congr_obj fibreProductOverBase x))
  /-- Under the preceding equivalence, the second projection is `s`. -/
  sourceProjectionIso :
    fibreProductEquivalence.functor ⋙
        TwoFibreProductOver.snd (CategoryOfElements.π U)
          (CategoryOfElements.π U) p f f ≅
      CategoryOfElements.map source ⋙ (uliftElementsEquivalence U).inverse
  /-- The second projection comparison lifts the identity in the base. -/
  sourceProjectionIso_vertical : ∀ x : arrows.Elements,
    (CategoryOfElements.π U).map (sourceProjectionIso.hom.app x) =
      eqToHom ((fibreProductEquivalence.functor.obj x).hy.trans
        (Functor.congr_obj fibreProductOverBase x))
  /-- Fibrewise, the arrows are exactly vertical isomorphisms between the two
  images in `F`. -/
  arrowEquiv : ∀ T, arrows.obj T ≃ PresentationArrow p U f over T
  arrowEquiv_source : ∀ T (a : arrows.obj T),
    (arrowEquiv T a).source = (source.app T a).down
  arrowEquiv_target : ∀ T (a : arrows.obj T),
    (arrowEquiv T a).target = (target.app T a).down
  /-- The fibrewise description is the one induced by the equivalence with
  the two-fibre product. -/
  arrowEquiv_iso : ∀ T (a : arrows.obj T),
    (arrowEquiv T a).iso =
      eqToIso (congrArg (fun x ↦ f.obj ⟨T, x⟩) (arrowEquiv_target T a)) ≪≫
        f.mapIso ((targetProjectionIso.app ⟨T, a⟩).symm) ≪≫
        (fibreProductEquivalence.functor.obj ⟨T, a⟩).iso ≪≫
        f.mapIso (sourceProjectionIso.app ⟨T, a⟩) ≪≫
        eqToIso (congrArg (fun x ↦ f.obj ⟨T, x⟩) (arrowEquiv_source T a).symm)
  /-- Under the fibrewise description, composition is the first-and-last
  projection from the triple fibre product. -/
  arrowEquiv_comp : ∀ T (a b : arrows.obj T)
      (h : source.app T a = target.app T b),
    arrowEquiv T (comp.app T ⟨(a, b), h⟩) =
      PresentationArrow.comp (p := p) (U := U) (f := f) (over := over)
        (arrowEquiv T a) (arrowEquiv T b)
        ((arrowEquiv_source T a).trans
          ((congrArg ULift.down h).trans (arrowEquiv_target T b).symm))

namespace PresentationGroupoid

/-- The groupoid in functors underlying a presentation. -/
def toGroupoidInFunctors (P : PresentationGroupoid p U f over) :
    GroupoidInFunctors C where
  objects := U ⋙ uliftFunctor.{w, uU}
  arrows := P.arrows
  source := P.source
  target := P.target
  comp := P.comp
  pointwiseGroupoid := P.pointwiseGroupoid

end PresentationGroupoid

/-- A morphism from a set-valued functor to a category cofibered in groupoids canonically
produces a groupoid in functors, whose arrows are the two-fibre product with source, target, and
composition given by the second, first, and first-and-last projections respectively. -/
@[stacks 06KY]
noncomputable def presentationGroupoid
    (hp : IsCofiberedInGroupoids p) : PresentationGroupoid p U f over := private_decl% (by
  exact {
    arrows := presentationArrowFunctor p U f over hp
    source := presentationSource p U f over hp
    target := presentationTarget p U f over hp
    comp := presentationComp p U f over hp
    pointwiseGroupoid T := presentationPointwiseGroupoid p U f over T
    fibreProductEquivalence := presentationFibreEquivalence p U f over hp
    fibreProductOverBase := by rfl
    targetProjectionIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro x y g; apply Subtype.ext
      change g.val ≫ 𝟙 _ = 𝟙 _ ≫ g.val
      simp)
    targetProjectionIso_vertical x := by rfl
    sourceProjectionIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro x y g; apply Subtype.ext
      change g.val ≫ 𝟙 _ = 𝟙 _ ≫ g.val
      simp)
    sourceProjectionIso_vertical x := by rfl
    arrowEquiv T := Equiv.refl _
    arrowEquiv_source T a := rfl
    arrowEquiv_target T a := rfl
    arrowEquiv_iso T a := by
      apply Iso.ext
      change a.iso.hom = 𝟙 _ ≫ f.map (𝟙 _) ≫ a.iso.hom ≫ f.map (𝟙 _) ≫ 𝟙 _
      rw [f.map_id (U.elementsMk T a.target), f.map_id (U.elementsMk T a.source)]
      simp
    arrowEquiv_comp T a b h := rfl
  })

end Deformation

end
