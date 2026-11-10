module

public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatStages
public import StacksFrontier.Deformation.Artin.LimitPreserving

/-!
# Stage descent for the colimit comparison of Stacks 07XL

For a fibred category `p : Y ⥤ C` and a cofiltered diagram `D` in `C` with a cone `c`, the
colimit comparison of Stacks 07XL compares the colimit of the fibres over the stages with the
fibre over the cone point. This file characterises its being an equivalence by three descent
conditions, stated directly in terms of cartesian arrows and vertical morphisms and involving no
colimit: `Deformation.Artin.DescentObj`, that every object over the cone point is the pullback of
an object over a stage; `Deformation.Artin.DescentHom`, that every vertical morphism between such
pullbacks comes from a vertical morphism at a later stage; and `Deformation.Artin.DescentEq`, that
two vertical morphisms of a stage which agree over the cone point already agree at a later stage.
The three correspond to essential surjectivity, fullness and faithfulness.

## Main definitions

* `Deformation.Artin.DescentObj`
* `Deformation.Artin.DescentHom`
* `Deformation.Artin.DescentEq`

## Main results

* `Deformation.Artin.descentObj_of_essSurj` and `Deformation.Artin.essSurj_of_descentObj`
* `Deformation.Artin.descentHom_of_full` and `Deformation.Artin.full_of_descentHom`
* `Deformation.Artin.descentEq_of_faithful` and `Deformation.Artin.faithful_of_descentEq`

## Implementation notes

The colimit of Stacks 07XL is taken over the *split* fibres of Stacks 004A, whose restriction
functors compose on the nose, so each statement is first established for split-fibre objects
`(V, x, V ⟶ D i)` and then transported along the equivalence
`Deformation.Artin.evaluateSplitFiber` to the fibre itself; the transport is where the pullback
comparisons `Functor.pullbackFiberCompIso` and the cartesian-arrow extensionality lemmas enter.
Reading a morphism or an equality of the colimit back at a stage is the content of
`StacksFrontier.CategoryTheory.Limits.FilteredColimitCatStages`, applied to the opposite of the
cofiltered index category.

Being fibred in groupoids is needed for the three converse directions and for descent of
equalities: it turns a morphism lying over a transition into a cartesian one, which is what lets
an identity proved for one such morphism be transferred to any other.

## References

* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
* [Stacks Project, Tag 0CMS](https://stacks.math.columbia.edu/tag/0CMS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Deformation.Artin

universe uC vC uY vY vI wI

/-- Two parallel morphisms agree as soon as their conjugates by one and the same
pair of canonical identifications agree.

Named for what it does -- cancellation -- to keep it distinct from
`Deformation.Artin.eq_of_eqToHom_conj` (`StacksFrontier.Deformation.Artin.ChangeOfField`:194),
which is public, lives in this same namespace, and states transposition instead: it solves a
conjugated equation for the inner morphism rather than cancelling a shared conjugation. The two
were spelled with one name until this round, which nothing caught only because neither file
imports the other. -/
private lemma eq_of_conj_eqToHom_eq {Z : Type*} [Category Z] {a a' b b' : Z}
    (ha : a = a') (hb : b' = b) {f g : a' ⟶ b'}
    (h : eqToHom ha ≫ f ≫ eqToHom hb = eqToHom ha ≫ g ≫ eqToHom hb) : f = g := by
  subst ha hb
  simpa using h

/-- Collapsing a doubly conjugated morphism into a single conjugation. -/
private lemma eqToHom_conj_eq {Z : Type*} [Category Z] {a1 a2 a3 b1 b2 b3 : Z}
    (h1 : a1 = a2) (h2 : a2 = a3) (h3 : b3 = b2) (h4 : b2 = b1)
    (h5 : a1 = a3) (h6 : b3 = b1) (f : a3 ⟶ b3) :
    eqToHom h1 ≫ (eqToHom h2 ≫ f ≫ eqToHom h3) ≫ eqToHom h4 =
      eqToHom h5 ≫ f ≫ eqToHom h6 := by
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]


/-- Parallel morphisms with equal images under a functor have equal images under any equal
functor. -/
private lemma map_eq_map_of_functor_eq {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (H : F = G) {X Y : A} {f g : X ⟶ Y} (h : F.map f = F.map g) : G.map f = G.map g := by
  subst H
  exact h

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

private lemma splitFiber_essSurj_descent
    {C : Type uC} [Category.{vC} C] {Y : Type uY} [Category.{vY} Y]
    (p : Y ⥤ C) [p.IsFibered]
    {I : Type vI} [Category.{wI} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D)
    [(colimitComparison p D c).EssSurj]
    (x : p.Fiber c.pt) :
    ∃ (i : I) (a : p.SplitFiber (D.obj i)),
      Nonempty ((evaluateSplitFiber p c.pt).obj
        ((Functor.SplitFiber.restrict p (c.π.app i)).obj a) ≅ x) := by
  let F := fiberDiagram p D
  let K := colimitComparison p D c
  obtain ⟨j, a, ⟨e⟩⟩ := Cat.exists_stage_obj_of_essSurj.{max uC uY vC vY, vI, wI, _, _} F K x
  refine ⟨j.unop,
    AsSmall.down.{vY, max uC uY vC, max vI wI}.obj a, ⟨?_⟩⟩
  exact eqToIso (Functor.congr_obj (colimitComparison_ι p D c j.unop) a).symm ≪≫ e

/-- **Fullness of the colimit comparison of Stacks 07XL, read in the split fibre at a stage.**
A morphism between the restrictions to the cone point of two split-fibre objects of a stage is,
at some later stage, the restriction of a morphism of split-fibre objects of that stage. -/
lemma splitFiber_full_descent_same_stage
    {C : Type uC} [Category.{vC} C] {Y : Type uY} [Category.{vY} Y]
    (p : Y ⥤ C) [p.IsFibered]
    {I : Type vI} [Category.{wI} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D)
    [(colimitComparison p D c).Full]
    (i : I) (a b : p.SplitFiber (D.obj i))
    (f : (Functor.SplitFiber.restrict p (c.π.app i)).obj a ⟶
      (Functor.SplitFiber.restrict p (c.π.app i)).obj b) :
    ∃ (k : I) (s : k ⟶ i)
      (g : (Functor.SplitFiber.restrict p (D.map s)).obj a ⟶
        (Functor.SplitFiber.restrict p (D.map s)).obj b),
      HEq ((Functor.SplitFiber.restrict p (c.π.app k)).map g) f := by
  let F := fiberDiagram p D
  let K := colimitComparison p D c
  let e := colimitComparison_ι p D c i
  let ai := AsSmall.up.{vY, max uC uY vC, max vI wI}.obj a
  let bi := AsSmall.up.{vY, max uC uY vC, max vI wI}.obj b
  let f' : K.obj ((colimit.ι F (op i)).toFunctor.obj ai) ⟶
      K.obj ((colimit.ι F (op i)).toFunctor.obj bi) :=
    eqToHom (Functor.congr_obj e ai) ≫ f ≫
      eqToHom (Functor.congr_obj e bi).symm
  obtain ⟨j, s, g, hg⟩ :=
    Cat.exists_stage_map_of_full.{max uC uY vC vY, vI, wI, _, _} F K (op i) ai bi f'
  refine ⟨j.unop, s.unop,
    AsSmall.down.{vY, max uC uY vC, max vI wI}.map g, ?_⟩
  have hh : HEq (K.map ((colimit.ι F j).toFunctor.map g)) f' := hg
  exact ((Functor.hcongr_hom (colimitComparison_ι p D c j.unop) g).symm.trans hh).trans (by
    dsimp only [f']
    exact (eqToHom_comp_heq _ _).trans
      (comp_eqToHom_heq (C := p.Fiber c.pt) _ _))

private lemma splitFiber_faithful_descent_same_stage
    {C : Type uC} [Category.{vC} C] {Y : Type uY} [Category.{vY} Y]
    (p : Y ⥤ C) [p.IsFibered]
    {I : Type vI} [Category.{wI} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D)
    [(colimitComparison p D c).Faithful]
    (i : I) {a b : p.SplitFiber (D.obj i)} (f g : a ⟶ b)
    (h : (Functor.SplitFiber.restrict p (c.π.app i)).map f =
      (Functor.SplitFiber.restrict p (c.π.app i)).map g) :
    ∃ (k : I) (s : k ⟶ i),
      (Functor.SplitFiber.restrict p (D.map s)).map f =
        (Functor.SplitFiber.restrict p (D.map s)).map g := by
  let F := fiberDiagram p D
  let K := colimitComparison p D c
  let e := colimitComparison_ι p D c i
  let uf := AsSmall.up.{vY, max uC uY vC, max vI wI}.map f
  let ug := AsSmall.up.{vY, max uC uY vC, max vI wI}.map g
  have hK : K.map ((colimit.ι F (op i)).toFunctor.map uf) =
      K.map ((colimit.ι F (op i)).toFunctor.map ug) :=
    map_eq_map_of_functor_eq e.symm (congrArg (evaluateSplitFiber p c.pt).map h)
  obtain ⟨j, s, hs⟩ :=
    Cat.exists_common_stage_eq_of_colimit_ι_map_eq F (op i) uf ug (K.map_injective hK)
  exact ⟨j.unop, s.unop,
    congrArg AsSmall.down.{vY, max uC uY vC, max vI wI}.map hs⟩

/-- Two parallel morphisms of a stage of a diagram in `Cat` have equal images in the colimit as
soon as their images at a later stage agree. -/
private lemma colimit_ι_map_eq_of_map_eq.{w₀, w₁, w₂} {J : Type w₀} [Category J]
    (F : J ⥤ Cat.{w₁, w₂}) [HasColimit F] {i k : J} (s : i ⟶ k) {A B : F.obj i}
    {f g : A ⟶ B} (h : (F.map s).toFunctor.map f = (F.map s).toFunctor.map g) :
    (colimit.ι F i).toFunctor.map f = (colimit.ι F i).toFunctor.map g :=
  map_eq_map_of_functor_eq (congrArg Cat.Hom.toFunctor (colimit.w F s))
    (congrArg (colimit.ι F k).toFunctor.map h)

section StageDescent

variable {C : Type uC} [Category.{vC} C] {Y : Type uY} [Category.{vY} Y]
  {I : Type vI} [Category.{wI} I]

/-- Every object of the fibre over the cone point is the pullback of an object
living over one of the stages. -/
def DescentObj (p : Y ⥤ C) (D : I ⥤ C) (c : Cone D) : Prop :=
  ∀ x : p.Fiber c.pt, ∃ (i : I) (xi : p.Fiber (D.obj i)) (δ : x.1 ⟶ xi.1),
    p.IsHomLift (c.π.app i) δ

/-- Every vertical morphism between pullbacks of stage objects already comes
from a vertical morphism at a later stage. -/
def DescentHom (p : Y ⥤ C) (D : I ⥤ C) (c : Cone D) : Prop :=
  ∀ (i : I) (xi yi : p.Fiber (D.obj i)) (x y : p.Fiber c.pt)
    (δ : x.1 ⟶ xi.1) (ε : y.1 ⟶ yi.1),
    p.IsHomLift (c.π.app i) δ → p.IsHomLift (c.π.app i) ε →
    ∀ φ : x.1 ⟶ y.1, p.IsHomLift (𝟙 c.pt) φ →
    ∃ (k : I) (s : k ⟶ i) (xk yk : p.Fiber (D.obj k))
      (dx : xk.1 ⟶ xi.1) (dy : yk.1 ⟶ yi.1)
      (δk : x.1 ⟶ xk.1) (ψ : xk.1 ⟶ yk.1),
      p.IsHomLift (D.map s) dx ∧ p.IsHomLift (D.map s) dy ∧
      p.IsHomLift (c.π.app k) δk ∧ p.IsHomLift (𝟙 (D.obj k)) ψ ∧
      δk ≫ dx = δ ∧ δk ≫ ψ ≫ dy = φ ≫ ε

/-- Two vertical morphisms at a stage which agree over the cone point already
agree after passing to a later stage. -/
def DescentEq (p : Y ⥤ C) (D : I ⥤ C) (c : Cone D) : Prop :=
  ∀ (i : I) (xi yi : p.Fiber (D.obj i)) (x : p.Fiber c.pt) (δ : x.1 ⟶ xi.1),
    p.IsHomLift (c.π.app i) δ →
    ∀ ψ ψ' : xi.1 ⟶ yi.1, p.IsHomLift (𝟙 (D.obj i)) ψ →
      p.IsHomLift (𝟙 (D.obj i)) ψ' → δ ≫ ψ = δ ≫ ψ' →
      ∃ (k : I) (s : k ⟶ i) (xk : p.Fiber (D.obj k)) (dx : xk.1 ⟶ xi.1),
        p.IsHomLift (D.map s) dx ∧ dx ≫ ψ = dx ≫ ψ'

variable (p : Y ⥤ C) [p.IsFibered] (hp : p.IsFiberedInGroupoids)
  [IsCofiltered I] (D : I ⥤ C) (c : Cone D)

/-- Essential surjectivity of the colimit comparison of Stacks 07XL gives descent of
objects. -/
lemma descentObj_of_essSurj
    [(colimitComparison p D c).EssSurj] : DescentObj p D c := by
  intro x
  obtain ⟨i, a, ⟨e⟩⟩ := splitFiber_essSurj_descent p D c x
  have e' : Functor.pullbackFiber p a.obj (c.π.app i ≫ a.hom) ≅ x := e
  refine ⟨i, Functor.pullbackFiber p a.obj a.hom,
    e'.inv.1 ≫ Functor.pullbackFiberProj a.obj a.hom (c.π.app i), ?_⟩
  let := e'.inv.2
  infer_instance

omit [IsCofiltered I] in
include hp in
/-- Descent of objects makes the colimit comparison of Stacks 07XL essentially surjective. -/
lemma essSurj_of_descentObj (h : DescentObj p D c) :
    (colimitComparison p D c).EssSurj := by
  constructor
  intro x
  obtain ⟨i, xi, δ, hδ⟩ := h x
  let : p.IsStronglyCartesian (c.π.app i) δ :=
    hp.isStronglyCartesian_homLift (c.π.app i) δ
  let : p.IsCartesian (c.π.app i) δ := inferInstance
  refine ⟨(colimit.ι (fiberDiagram p D) (op i)).toFunctor.obj
      (AsSmall.up.{vY, max uC uY vC, max vI wI}.obj ⟨D.obj i, xi, 𝟙 (D.obj i)⟩),
    ⟨?_⟩⟩
  have hK : (colimitComparison p D c).obj
      ((colimit.ι (fiberDiagram p D) (op i)).toFunctor.obj
        (AsSmall.up.{vY, max uC uY vC, max vI wI}.obj
          ⟨D.obj i, xi, 𝟙 (D.obj i)⟩)) =
      Functor.pullbackFiber p xi (c.π.app i ≫ 𝟙 (D.obj i)) :=
    Functor.congr_obj (colimitComparison_ι p D c i) _
  refine (eqToIso hK).trans ?_
  refine (eqToIso (congrArg (Functor.pullbackFiber p xi)
    (Category.comp_id (c.π.app i)))).trans ?_
  exact Functor.fiberIsoOfCartesian (c.π.app i)
    (Functor.IsPreFibered.pullbackMap xi.2 (c.π.app i)) δ inferInstance
    inferInstance

/-- The split-fibre object `(x, 𝟙)` attached to an object of the fibre. -/
private def idSplit {V : C} (xi : p.Fiber V) : p.SplitFiber V := ⟨V, xi, 𝟙 V⟩

/-- A vertical morphism of the fibre over `V`, read as a morphism between the
corresponding split-fibre objects. -/
private noncomputable def splitHomOfVertical {V : C} (xi yi : p.Fiber V)
    (ψ : xi.1 ⟶ yi.1) (hψ : p.IsHomLift (𝟙 V) ψ) :
    idSplit p xi ⟶ idSplit p yi :=
  Functor.SplitFiber.ofFiberHom
    (Functor.pullbackFiberHom (⟨ψ, hψ⟩ : xi ⟶ yi) (𝟙 V))

private lemma splitHomOfVertical_fac {V : C} (xi yi : p.Fiber V)
    (ψ : xi.1 ⟶ yi.1) (hψ : p.IsHomLift (𝟙 V) ψ) :
    Functor.Fiber.fiberInclusion.map (splitHomOfVertical p xi yi ψ hψ) ≫
        Functor.IsPreFibered.pullbackMap yi.2 (𝟙 V) =
      Functor.IsPreFibered.pullbackMap xi.2 (𝟙 V) ≫ ψ :=
  Functor.pullbackFiberHom_fac (⟨ψ, hψ⟩ : xi ⟶ yi) (𝟙 V)

private lemma splitHomOfVertical_restrict_fac {V W : C} (g : W ⟶ V)
    (xi yi : p.Fiber V) (ψ : xi.1 ⟶ yi.1) (hψ : p.IsHomLift (𝟙 V) ψ) :
    Functor.Fiber.fiberInclusion.map
        ((Functor.SplitFiber.restrict p g).map
          (splitHomOfVertical p xi yi ψ hψ)) ≫
        Functor.IsPreFibered.pullbackMap yi.2 (g ≫ 𝟙 V) =
      Functor.IsPreFibered.pullbackMap xi.2 (g ≫ 𝟙 V) ≫ ψ := by
  have h : Functor.Fiber.fiberInclusion.map
        ((Functor.SplitFiber.restrict p g).map
          (splitHomOfVertical p xi yi ψ hψ)) ≫
        Functor.IsPreFibered.pullbackMap yi.2 (g ≫ 𝟙 V) =
      Functor.pullbackFiberProj xi (𝟙 V) g ≫
        Functor.Fiber.fiberInclusion.map (splitHomOfVertical p xi yi ψ hψ) ≫
        Functor.IsPreFibered.pullbackMap yi.2 (𝟙 V) :=
    Functor.SplitFiber.restrictHom_fac (p := p) g
      (o := idSplit p xi) (o' := idSplit p yi)
      (splitHomOfVertical p xi yi ψ hψ)
  refine h.trans ?_
  refine (congrArg (fun t => Functor.pullbackFiberProj xi (𝟙 V) g ≫ t)
    (splitHomOfVertical_fac p xi yi ψ hψ)).trans ?_
  exact (Category.assoc (Functor.pullbackFiberProj xi (𝟙 V) g)
      (Functor.IsPreFibered.pullbackMap xi.2 (𝟙 V)) ψ).symm.trans
    (congrArg (fun t => t ≫ ψ) (Functor.pullbackFiberProj_fac xi (𝟙 V) g))

private lemma restrict_splitHom_eq {V W : C} (g : W ⟶ V) (xi yi : p.Fiber V)
    (ψ ψ' : xi.1 ⟶ yi.1) (hψ : p.IsHomLift (𝟙 V) ψ)
    (hψ' : p.IsHomLift (𝟙 V) ψ')
    (hg : Functor.IsPreFibered.pullbackMap xi.2 (g ≫ 𝟙 V) ≫ ψ =
      Functor.IsPreFibered.pullbackMap xi.2 (g ≫ 𝟙 V) ≫ ψ') :
    (Functor.SplitFiber.restrict p g).map (splitHomOfVertical p xi yi ψ hψ) =
      (Functor.SplitFiber.restrict p g).map
        (splitHomOfVertical p xi yi ψ' hψ') := by
  refine Functor.fiber_hom_ext_of_cartesian (g ≫ 𝟙 V)
    (Functor.IsPreFibered.pullbackMap yi.2 (g ≫ 𝟙 V))
    (Functor.IsPreFibered.pullbackMap.IsCartesian yi.2 (g ≫ 𝟙 V)) _ _ ?_
  exact ((splitHomOfVertical_restrict_fac p g xi yi ψ hψ).trans hg).trans
    (splitHomOfVertical_restrict_fac p g xi yi ψ' hψ').symm

include hp in
/-- Faithfulness of the colimit comparison of Stacks 07XL gives descent of equalities of
vertical morphisms. -/
lemma descentEq_of_faithful
    [(colimitComparison p D c).Faithful] : DescentEq p D c := by
  intro i xi yi x δ hδ ψ ψ' hψ hψ' hδψ
  let : p.IsStronglyCartesian (c.π.app i) δ :=
    hp.isStronglyCartesian_homLift (c.π.app i) δ
  let : p.IsCartesian (c.π.app i) δ := inferInstance
  have hcart : p.IsCartesian (c.π.app i)
      (Functor.IsPreFibered.pullbackMap xi.2 (c.π.app i ≫ 𝟙 (D.obj i))) := by
    simpa using Functor.IsPreFibered.pullbackMap.IsCartesian xi.2
      (c.π.app i ≫ 𝟙 (D.obj i))
  have hcpt : Functor.IsPreFibered.pullbackMap xi.2
        (c.π.app i ≫ 𝟙 (D.obj i)) ≫ ψ =
      Functor.IsPreFibered.pullbackMap xi.2
        (c.π.app i ≫ 𝟙 (D.obj i)) ≫ ψ' := by
    have hw := Functor.fiberIsoOfCartesian_hom_fac (p := p) (c.π.app i)
      (z := Functor.pullbackFiber p xi (c.π.app i ≫ 𝟙 (D.obj i))) (z' := x)
      (Functor.IsPreFibered.pullbackMap xi.2 (c.π.app i ≫ 𝟙 (D.obj i))) δ
      hcart inferInstance
    rw [← hw, Category.assoc, Category.assoc, hδψ]
  obtain ⟨k, s, hks⟩ := splitFiber_faithful_descent_same_stage p D c i
    (a := idSplit p xi) (b := idSplit p yi)
    (splitHomOfVertical p xi yi ψ hψ) (splitHomOfVertical p xi yi ψ' hψ')
    (restrict_splitHom_eq p (c.π.app i) xi yi ψ ψ' hψ hψ' hcpt)
  refine ⟨k, s, Functor.pullbackFiber p xi (D.map s ≫ 𝟙 (D.obj i)),
    Functor.IsPreFibered.pullbackMap xi.2 (D.map s ≫ 𝟙 (D.obj i)), ?_, ?_⟩
  · simpa using (Functor.IsPreFibered.pullbackMap.IsCartesian xi.2
      (D.map s ≫ 𝟙 (D.obj i))).toIsHomLift
  · have h := congrArg Functor.Fiber.fiberInclusion.map hks
    exact (((splitHomOfVertical_restrict_fac p (D.map s) xi yi ψ hψ).symm.trans
      (congrArg (fun t => t ≫ Functor.IsPreFibered.pullbackMap yi.2
        (D.map s ≫ 𝟙 (D.obj i))) h)).trans
      (splitHomOfVertical_restrict_fac p (D.map s) xi yi ψ' hψ'))

omit [p.IsFibered] in
include hp in
/-- In a category fibred in groupoids, an equality of composites with one
morphism lying over a transition of the diagram holds for every morphism lying
over that same transition. -/
private lemma eq_comp_of_isHomLift {V W : C} (g : W ⟶ V) {t xk xk' bb : Y}
    (dx : xk ⟶ t) (hdx : p.IsHomLift g dx) (d : xk' ⟶ t) (hd : p.IsHomLift g d)
    {ψ ψ' : t ⟶ bb} (hres : dx ≫ ψ = dx ≫ ψ') : d ≫ ψ = d ≫ ψ' := by
  let := hdx
  let := hd
  let : p.IsStronglyCartesian g dx := hp.isStronglyCartesian_homLift g dx
  have hfac : Functor.IsStronglyCartesian.map p g dx
      (g := 𝟙 W) (Category.id_comp g).symm d ≫ dx = d :=
    Functor.IsStronglyCartesian.fac p g dx _ d
  rw [← hfac, Category.assoc, Category.assoc, hres]

omit [IsCofiltered I] in
include hp in
/-- The converse of `splitFiber_faithful_descent_same_stage`: descent of
equalities makes two parallel split-fibre morphisms agree at a later stage as
soon as their restrictions to the cone point agree. -/
private lemma splitFiber_eq_of_descentEq (h : DescentEq p D c) (i : I)
    {a b : p.SplitFiber (D.obj i)} (f g : a ⟶ b)
    (hfg : (Functor.SplitFiber.restrict p (c.π.app i)).map f =
      (Functor.SplitFiber.restrict p (c.π.app i)).map g) :
    ∃ (k : I) (s : k ⟶ i),
      (Functor.SplitFiber.restrict p (D.map s)).map f =
        (Functor.SplitFiber.restrict p (D.map s)).map g := by
  have hvert : p.IsHomLift (𝟙 (D.obj i))
      (Functor.Fiber.fiberInclusion.map (Functor.SplitFiber.toFiberHom f)) :=
    (Functor.SplitFiber.toFiberHom f).2
  have hvert' : p.IsHomLift (𝟙 (D.obj i))
      (Functor.Fiber.fiberInclusion.map (Functor.SplitFiber.toFiberHom g)) :=
    (Functor.SplitFiber.toFiberHom g).2
  have hres : Functor.SplitFiber.restrictHom (c.π.app i)
        (Functor.SplitFiber.toFiberHom f) =
      Functor.SplitFiber.restrictHom (c.π.app i)
        (Functor.SplitFiber.toFiberHom g) :=
    congrArg Functor.SplitFiber.toFiberHom hfg
  have key : Functor.pullbackFiberProj a.obj a.hom (c.π.app i) ≫
        Functor.Fiber.fiberInclusion.map (Functor.SplitFiber.toFiberHom f) =
      Functor.pullbackFiberProj a.obj a.hom (c.π.app i) ≫
        Functor.Fiber.fiberInclusion.map (Functor.SplitFiber.toFiberHom g) := by
    rw [← Functor.SplitFiber.restrictHom_comp_pullbackFiberProj (p := p) (c.π.app i),
      ← Functor.SplitFiber.restrictHom_comp_pullbackFiberProj (p := p) (c.π.app i),
      hres]
  obtain ⟨k, s, xk, dx, hdx, hdxres⟩ := h i a.toFiber b.toFiber
    (Functor.pullbackFiber p a.obj (c.π.app i ≫ a.hom))
    (Functor.pullbackFiberProj a.obj a.hom (c.π.app i)) inferInstance _ _
    hvert hvert' key
  refine ⟨k, s, Functor.SplitFiber.toFiberHom_injective ?_⟩
  change Functor.SplitFiber.restrictHom (D.map s) (Functor.SplitFiber.toFiberHom f) =
    Functor.SplitFiber.restrictHom (D.map s) (Functor.SplitFiber.toFiberHom g)
  refine Functor.fiber_hom_ext_of_cartesian (D.map s ≫ b.hom)
    (Functor.IsPreFibered.pullbackMap b.obj.2 (D.map s ≫ b.hom))
    (Functor.IsPreFibered.pullbackMap.IsCartesian b.obj.2 (D.map s ≫ b.hom)) _ _ ?_
  rw [Functor.SplitFiber.restrictHom_fac, Functor.SplitFiber.restrictHom_fac,
    ← Category.assoc, ← Category.assoc,
    eq_comp_of_isHomLift p hp (D.map s) dx hdx
      (Functor.pullbackFiberProj a.obj a.hom (D.map s)) inferInstance hdxres]

include hp in
/-- The converse of `descentEq_of_faithful`: descent of equalities of vertical
morphisms makes the colimit comparison faithful. -/
lemma faithful_of_descentEq (h : DescentEq p D c) :
    (colimitComparison p D c).Faithful := by
  constructor
  intro X Z f g hfg
  obtain ⟨j, A, B, f', g', hx, hz, hf', hg'⟩ :=
    Cat.exists_stage_hom_pair_of_colimit.{max uC uY vC vY, vI, wI} (fiberDiagram p D) f g
  obtain ⟨i⟩ := j
  have hKfg : (colimitComparison p D c).map
        ((colimit.ι (fiberDiagram p D) (op i)).toFunctor.map f') =
      (colimitComparison p D c).map
        ((colimit.ι (fiberDiagram p D) (op i)).toFunctor.map g') := by
    rw [hf', hg']
    simp only [Functor.map_comp, hfg]
  have hstage : (Functor.SplitFiber.restrict p (c.π.app i)).map
        (AsSmall.down.{vY, max uC uY vC, max vI wI}.map f') =
      (Functor.SplitFiber.restrict p (c.π.app i)).map
        (AsSmall.down.{vY, max uC uY vC, max vI wI}.map g') :=
    map_eq_map_of_functor_eq (colimitComparison_ι p D c i) hKfg
  obtain ⟨k, s, hks⟩ := splitFiber_eq_of_descentEq p hp D c h i
    (AsSmall.down.{vY, max uC uY vC, max vI wI}.map f')
    (AsSmall.down.{vY, max uC uY vC, max vI wI}.map g') hstage
  have hF : ((fiberDiagram p D).map s.op).toFunctor.map f' =
      ((fiberDiagram p D).map s.op).toFunctor.map g' :=
    congrArg AsSmall.up.{vY, max uC uY vC, max vI wI}.map hks
  have hι := colimit_ι_map_eq_of_map_eq (fiberDiagram p D) s.op hF
  rw [hf', hg'] at hι
  exact eq_of_conj_eqToHom_eq hx hz.symm hι

section FullConverse

/- Instance synthesis and `rw` work at a transparency that does not see through
the split-fibre restriction functor, so the two spellings
`((SplitFiber.restrict p g).obj a).toFiber` and `pullbackFiber p a.obj (g ≫ a.hom)`
are not identified and the `IsHomLift` instances below are not found. -/
attribute [local implicit_reducible] Functor.SplitFiber.restrict

/-- The fibre morphism underlying a conjugate of a split-fibre morphism by canonical
identifications is the conjugate of the underlying fibre morphism. -/
private lemma toFiberHom_eqToHom_comp_comp_eqToHom {V : C} {o₁ o₂ o₃ o₄ : p.SplitFiber V}
    (ha : o₁ = o₂) (φ : o₂ ⟶ o₃) (hb : o₃ = o₄) :
    Functor.SplitFiber.toFiberHom (eqToHom ha ≫ φ ≫ eqToHom hb) =
      eqToHom (congrArg Functor.SplitFiber.toFiber ha) ≫ Functor.SplitFiber.toFiberHom φ ≫
        eqToHom (congrArg Functor.SplitFiber.toFiber hb) := by
  rw [Functor.SplitFiber.toFiberHom_comp, Functor.SplitFiber.toFiberHom_comp,
    Functor.SplitFiber.toFiberHom_eqToHom ha _, Functor.SplitFiber.toFiberHom_eqToHom hb _]

omit [IsCofiltered I] in
include hp in
/-- The converse of `splitFiber_full_descent_same_stage`: descent of vertical
morphisms realizes a morphism between the restrictions to the cone point by a
morphism at a later stage. -/
private lemma splitFiber_full_of_descentHom (h : DescentHom p D c) (i : I)
    (a b : p.SplitFiber (D.obj i))
    (φ : (Functor.SplitFiber.restrict p (c.π.app i)).obj a ⟶
      (Functor.SplitFiber.restrict p (c.π.app i)).obj b) :
    ∃ (k : I) (s : k ⟶ i)
      (g : (Functor.SplitFiber.restrict p (D.map s)).obj a ⟶
        (Functor.SplitFiber.restrict p (D.map s)).obj b)
      (ha : (Functor.SplitFiber.restrict p (c.π.app k)).obj
          ((Functor.SplitFiber.restrict p (D.map s)).obj a) =
        (Functor.SplitFiber.restrict p (c.π.app i)).obj a)
      (hb : (Functor.SplitFiber.restrict p (c.π.app k)).obj
          ((Functor.SplitFiber.restrict p (D.map s)).obj b) =
        (Functor.SplitFiber.restrict p (c.π.app i)).obj b),
      (Functor.SplitFiber.restrict p (c.π.app k)).map g =
        eqToHom ha ≫ φ ≫ eqToHom hb.symm := by
  set Φ := Functor.Fiber.fiberInclusion.map (Functor.SplitFiber.toFiberHom φ)
    with hΦdef
  have hΦ : p.IsHomLift (𝟙 c.pt) Φ := (Functor.SplitFiber.toFiberHom φ).2
  obtain ⟨k, s, xk, yk, dx, dy, δk, ψ, hdx, hdy, hδk, hψ, e₁, e₂⟩ :=
    h i a.toFiber b.toFiber
      (Functor.pullbackFiber p a.obj (c.π.app i ≫ a.hom))
      (Functor.pullbackFiber p b.obj (c.π.app i ≫ b.hom))
      (Functor.pullbackFiberProj a.obj a.hom (c.π.app i))
      (Functor.pullbackFiberProj b.obj b.hom (c.π.app i))
      inferInstance inferInstance _ hΦ
  have hf : ∀ z : p.SplitFiber (D.obj i), c.π.app k ≫ D.map s ≫ z.hom = c.π.app i ≫ z.hom := by
    intro z
    rw [← Category.assoc, c.w s]
  have hz : ∀ z : p.SplitFiber (D.obj i), (Functor.SplitFiber.restrict p (c.π.app k)).obj
        ((Functor.SplitFiber.restrict p (D.map s)).obj z) =
      (Functor.SplitFiber.restrict p (c.π.app i)).obj z := by
    intro z
    change (⟨z.base, z.obj, c.π.app k ≫ D.map s ≫ z.hom⟩ : p.SplitFiber c.pt) =
      ⟨z.base, z.obj, c.π.app i ≫ z.hom⟩
    rw [hf]
  let : p.IsStronglyCartesian (D.map s) dx :=
    hp.isStronglyCartesian_homLift (D.map s) dx
  let : p.IsStronglyCartesian (D.map s) dy :=
    hp.isStronglyCartesian_homLift (D.map s) dy
  have hcartx : p.IsCartesian (D.map s ≫ a.hom)
      (dx ≫ Functor.IsPreFibered.pullbackMap a.obj.2 a.hom) := inferInstance
  have hcarty : p.IsCartesian (D.map s ≫ b.hom)
      (dy ≫ Functor.IsPreFibered.pullbackMap b.obj.2 b.hom) := inferInstance
  set u := Functor.fiberIsoOfCartesian (p := p) (D.map s ≫ a.hom)
    (z := xk) (z' := Functor.pullbackFiber p a.obj (D.map s ≫ a.hom))
    (dx ≫ Functor.IsPreFibered.pullbackMap a.obj.2 a.hom)
    (Functor.IsPreFibered.pullbackMap a.obj.2 (D.map s ≫ a.hom)) hcartx
    (Functor.IsPreFibered.pullbackMap.IsCartesian a.obj.2 (D.map s ≫ a.hom))
  set v := Functor.fiberIsoOfCartesian (p := p) (D.map s ≫ b.hom)
    (z := yk) (z' := Functor.pullbackFiber p b.obj (D.map s ≫ b.hom))
    (dy ≫ Functor.IsPreFibered.pullbackMap b.obj.2 b.hom)
    (Functor.IsPreFibered.pullbackMap b.obj.2 (D.map s ≫ b.hom)) hcarty
    (Functor.IsPreFibered.pullbackMap.IsCartesian b.obj.2 (D.map s ≫ b.hom))
  have hufac : Functor.Fiber.fiberInclusion.map u.inv ≫
      dx ≫ Functor.IsPreFibered.pullbackMap a.obj.2 a.hom =
    Functor.IsPreFibered.pullbackMap a.obj.2 (D.map s ≫ a.hom) :=
    Functor.fiberIsoOfCartesian_inv_fac _ _ _ _ _
  have hvfac : Functor.Fiber.fiberInclusion.map v.hom ≫
      Functor.IsPreFibered.pullbackMap b.obj.2 (D.map s ≫ b.hom) =
    dy ≫ Functor.IsPreFibered.pullbackMap b.obj.2 b.hom :=
    Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have ha := hz a
  have hb := hz b
  have eA : (Functor.pullbackFiber p a.obj (c.π.app k ≫ D.map s ≫ a.hom)).1 =
      (Functor.pullbackFiber p a.obj (c.π.app i ≫ a.hom)).1 :=
    congrArg (fun o : p.SplitFiber c.pt => o.toFiber.1) ha
  have eB : (Functor.pullbackFiber p b.obj (c.π.app i ≫ b.hom)).1 =
      (Functor.pullbackFiber p b.obj (c.π.app k ≫ D.map s ≫ b.hom)).1 :=
    congrArg (fun o : p.SplitFiber c.pt => o.toFiber.1) hb.symm
  let := u.inv.2
  have hkey : Functor.pullbackFiberProj a.obj (D.map s ≫ a.hom) (c.π.app k) ≫
      Functor.Fiber.fiberInclusion.map u.inv = eqToHom eA ≫ δk := by
    let : p.IsHomLift (𝟙 c.pt) (eqToHom eA) :=
      IsHomLift.eqToHom_domain_lift_id eA
        (Functor.pullbackFiber p a.obj (c.π.app k ≫ D.map s ≫ a.hom)).2
    let : p.IsHomLift (c.π.app k) (eqToHom eA ≫ δk) :=
      IsHomLift.comp_lift_id_left' p c.pt (eqToHom eA) (c.π.app k) δk
    refine Functor.IsStronglyCartesian.ext p (D.map s ≫ a.hom)
      (dx ≫ Functor.IsPreFibered.pullbackMap a.obj.2 a.hom) (c.π.app k) ?_
    rw [Category.assoc, hufac,
      Functor.pullbackFiberProj_fac a.obj (D.map s ≫ a.hom) (c.π.app k),
      Category.assoc, ← Category.assoc δk dx, e₁,
      Functor.pullbackFiberProj_fac a.obj a.hom (c.π.app i),
      Functor.eqToHom_comp_pullbackMap a.obj (hf a) eA]
  set g : (Functor.SplitFiber.restrict p (D.map s)).obj a ⟶
      (Functor.SplitFiber.restrict p (D.map s)).obj b :=
    Functor.SplitFiber.ofFiberHom
      (u.inv ≫ (⟨ψ, hψ⟩ : xk ⟶ yk) ≫ v.hom)
  have h1 : Functor.Fiber.fiberInclusion.map
        (Functor.SplitFiber.toFiberHom
          ((Functor.SplitFiber.restrict p (c.π.app k)).map g)) ≫
        Functor.IsPreFibered.pullbackMap b.obj.2
          (c.π.app k ≫ D.map s ≫ b.hom) =
      Functor.pullbackFiberProj a.obj (D.map s ≫ a.hom) (c.π.app k) ≫
        Functor.Fiber.fiberInclusion.map (Functor.SplitFiber.toFiberHom g) ≫
        Functor.IsPreFibered.pullbackMap b.obj.2 (D.map s ≫ b.hom) :=
    Functor.SplitFiber.restrictHom_fac (p := p) (c.π.app k)
      (o := (Functor.SplitFiber.restrict p (D.map s)).obj a)
      (o' := (Functor.SplitFiber.restrict p (D.map s)).obj b)
      (Functor.SplitFiber.toFiberHom g)
  have h2 : Functor.Fiber.fiberInclusion.map (Functor.SplitFiber.toFiberHom g) ≫
        Functor.IsPreFibered.pullbackMap b.obj.2 (D.map s ≫ b.hom) =
      Functor.Fiber.fiberInclusion.map u.inv ≫ ψ ≫ dy ≫
        Functor.IsPreFibered.pullbackMap b.obj.2 b.hom := by
    change (Functor.Fiber.fiberInclusion.map u.inv ≫ ψ ≫
        Functor.Fiber.fiberInclusion.map v.hom) ≫
        Functor.IsPreFibered.pullbackMap b.obj.2 (D.map s ≫ b.hom) = _
    rw [Category.assoc, Category.assoc, hvfac]
  have e₂' : δk ≫ ψ ≫ dy ≫
        Functor.IsPreFibered.pullbackMap b.obj.2 b.hom =
      Φ ≫ Functor.pullbackFiberProj b.obj b.hom (c.π.app i) ≫
        Functor.IsPreFibered.pullbackMap b.obj.2 b.hom := by
    simpa only [Category.assoc] using
      congrArg (fun t => t ≫ Functor.IsPreFibered.pullbackMap b.obj.2 b.hom) e₂
  have h4 : Functor.Fiber.fiberInclusion.map
        (Functor.SplitFiber.toFiberHom (eqToHom ha ≫ φ ≫ eqToHom hb.symm)) =
      eqToHom eA ≫ Φ ≫ eqToHom eB := by
    rw [hΦdef, toFiberHom_eqToHom_comp_comp_eqToHom, Functor.map_comp, Functor.map_comp,
      eqToHom_map, eqToHom_map]
  have hL : Functor.Fiber.fiberInclusion.map
        (Functor.SplitFiber.toFiberHom
          ((Functor.SplitFiber.restrict p (c.π.app k)).map g)) ≫
        Functor.IsPreFibered.pullbackMap b.obj.2
          (c.π.app k ≫ D.map s ≫ b.hom) =
      eqToHom eA ≫ Φ ≫
        Functor.IsPreFibered.pullbackMap b.obj.2 (c.π.app i ≫ b.hom) := by
    rw [h1, h2, ← Category.assoc, hkey, Category.assoc, e₂',
      Functor.pullbackFiberProj_fac b.obj b.hom (c.π.app i)]
  have hR : Functor.Fiber.fiberInclusion.map
        (Functor.SplitFiber.toFiberHom (eqToHom ha ≫ φ ≫ eqToHom hb.symm)) ≫
        Functor.IsPreFibered.pullbackMap b.obj.2
          (c.π.app k ≫ D.map s ≫ b.hom) =
      eqToHom eA ≫ Φ ≫
        Functor.IsPreFibered.pullbackMap b.obj.2 (c.π.app i ≫ b.hom) := by
    rw [h4]
    simp only [Category.assoc]
    rw [Functor.eqToHom_comp_pullbackMap b.obj (hf b).symm eB]
  refine ⟨k, s, g, ha, hb, Functor.SplitFiber.toFiberHom_injective ?_⟩
  refine Functor.fiber_hom_ext_of_cartesian (c.π.app k ≫ D.map s ≫ b.hom)
    (z' := ((Functor.SplitFiber.restrict p (c.π.app k)).obj
      ((Functor.SplitFiber.restrict p (D.map s)).obj b)).toFiber)
    (Functor.IsPreFibered.pullbackMap b.obj.2 (c.π.app k ≫ D.map s ≫ b.hom))
    (Functor.IsPreFibered.pullbackMap.IsCartesian b.obj.2
      (c.π.app k ≫ D.map s ≫ b.hom)) _ _ ?_
  exact hL.trans hR.symm

include hp in
/-- The converse of `descentHom_of_full`: descent of vertical morphisms makes
the colimit comparison full. -/
lemma full_of_descentHom (h : DescentHom p D c) :
    (colimitComparison p D c).Full := by
  constructor
  intro X Z φ
  obtain ⟨j, A, B, hA, hB⟩ :=
    Cat.exists_common_stage_obj_of_colimit.{max uC uY vC vY, vI, wI} (fiberDiagram p D) X Z
  obtain ⟨i⟩ := j
  set a := AsSmall.down.{vY, max uC uY vC, max vI wI}.obj A
  set b := AsSmall.down.{vY, max uC uY vC, max vI wI}.obj B
  have eX : (colimitComparison p D c).obj X =
      ((Functor.SplitFiber.restrict p (c.π.app i)).obj a).toFiber :=
    (congrArg (colimitComparison p D c).obj hA).symm.trans
      (Functor.congr_obj (colimitComparison_ι p D c i) A)
  have eZ : (colimitComparison p D c).obj Z =
      ((Functor.SplitFiber.restrict p (c.π.app i)).obj b).toFiber :=
    (congrArg (colimitComparison p D c).obj hB).symm.trans
      (Functor.congr_obj (colimitComparison_ι p D c i) B)
  set φ' : ((Functor.SplitFiber.restrict p (c.π.app i)).obj a).toFiber ⟶
      ((Functor.SplitFiber.restrict p (c.π.app i)).obj b).toFiber :=
    eqToHom eX.symm ≫ φ ≫ eqToHom eZ with hφ'def
  obtain ⟨k, s, g, ha, hb, hg⟩ :=
    splitFiber_full_of_descentHom p hp D c h i a b φ'
  set gu : ((fiberDiagram p D).map s.op).toFunctor.obj A ⟶
      ((fiberDiagram p D).map s.op).toFunctor.obj B :=
    AsSmall.up.{vY, max uC uY vC, max vI wI}.map g
  have hwA : (colimit.ι (fiberDiagram p D) (op k)).toFunctor.obj
      (((fiberDiagram p D).map s.op).toFunctor.obj A) = X :=
    (Functor.congr_obj (congrArg Cat.Hom.toFunctor
      (colimit.w (fiberDiagram p D) s.op)) A).trans hA
  have hwB : (colimit.ι (fiberDiagram p D) (op k)).toFunctor.obj
      (((fiberDiagram p D).map s.op).toFunctor.obj B) = Z :=
    (Functor.congr_obj (congrArg Cat.Hom.toFunctor
      (colimit.w (fiberDiagram p D) s.op)) B).trans hB
  have hsrc : (colimitComparison p D c).obj
        ((colimit.ι (fiberDiagram p D) (op k)).toFunctor.obj
          (((fiberDiagram p D).map s.op).toFunctor.obj A)) =
      ((Functor.SplitFiber.restrict p (c.π.app i)).obj a).toFiber :=
    (Functor.congr_obj (colimitComparison_ι p D c k)
      (((fiberDiagram p D).map s.op).toFunctor.obj A)).trans
      (congrArg (fun o : p.SplitFiber c.pt => o.toFiber) ha)
  have htgt : ((Functor.SplitFiber.restrict p (c.π.app i)).obj b).toFiber =
      (colimitComparison p D c).obj
        ((colimit.ι (fiberDiagram p D) (op k)).toFunctor.obj
          (((fiberDiagram p D).map s.op).toFunctor.obj B)) :=
    ((Functor.congr_obj (colimitComparison_ι p D c k)
      (((fiberDiagram p D).map s.op).toFunctor.obj B)).trans
      (congrArg (fun o : p.SplitFiber c.pt => o.toFiber) hb)).symm
  have hgF : (AsSmall.down.{vY, max uC uY vC, max vI wI} ⋙
        Functor.SplitFiber.restrict p (c.π.app k) ⋙
        evaluateSplitFiber p c.pt).map gu =
      eqToHom (congrArg (fun o : p.SplitFiber c.pt => o.toFiber) ha) ≫ φ' ≫
        eqToHom (congrArg (fun o : p.SplitFiber c.pt => o.toFiber) hb.symm) :=
    (congrArg Functor.SplitFiber.toFiberHom hg).trans
      (toFiberHom_eqToHom_comp_comp_eqToHom p ha φ' hb.symm)
  have hKgu : (colimitComparison p D c).map
        ((colimit.ι (fiberDiagram p D) (op k)).toFunctor.map gu) =
      eqToHom hsrc ≫ φ' ≫ eqToHom htgt := by
    have hco := Functor.congr_hom (colimitComparison_ι p D c k) gu
    rw [hgF] at hco
    exact hco.trans (eqToHom_conj_eq _ _ _ _ hsrc htgt φ')
  refine ⟨eqToHom hwA.symm ≫
    (colimit.ι (fiberDiagram p D) (op k)).toFunctor.map gu ≫
      eqToHom hwB, ?_⟩
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map, hKgu,
    hφ'def]
  simp

end FullConverse

/-- The canonical morphism into a pullback fibre is unchanged, up to the identification of
the two pullback fibres, when the morphism pulled back along is replaced by an equal one. -/
lemma toPullbackFiber_heq {U V : C} (xx : p.Fiber U) (yy : p.Fiber V)
    (f g : U ⟶ V) (e : f = g) (ν : xx.1 ⟶ yy.1)
    [p.IsHomLift f ν] [p.IsHomLift g ν] :
    HEq (Functor.toPullbackFiber p xx yy f ν)
      (Functor.toPullbackFiber p xx yy g ν) := by
  subst e
  rfl

/-- For a cartesian morphism `δ` over `b`, the canonical morphism into the chosen pullback
fibre is inverse to the comparison isomorphism out of it. -/
private lemma toPullbackFiber_comp_fiberIsoOfCartesian_hom {W U : C} (b : W ⟶ U) (x : p.Fiber W)
    (y : p.Fiber U) (δ : x.1 ⟶ y.1) [p.IsCartesian b δ] :
    Functor.toPullbackFiber p x y b δ ≫
      (Functor.fiberIsoOfCartesian (p := p) b (Functor.IsPreFibered.pullbackMap y.2 b) δ
        (Functor.IsPreFibered.pullbackMap.IsCartesian y.2 b) inferInstance).hom = 𝟙 x := by
  refine Functor.fiber_hom_ext_of_cartesian b δ inferInstance _ _ ?_
  rw [Functor.map_comp, Category.assoc, Functor.fiberIsoOfCartesian_hom_fac,
    Functor.toPullbackFiber_fac]
  simp

include hp in
/-- Fullness of the colimit comparison of Stacks 07XL gives descent of vertical
morphisms. -/
lemma descentHom_of_full
    [(colimitComparison p D c).Full] : DescentHom p D c := by
  intro i xi yi x y δ ε hδ hε φ hφ
  have hγ : p.IsHomLift (c.π.app i) (φ ≫ ε) :=
    IsHomLift.comp_lift_id_left' p c.pt φ (c.π.app i) ε
  let hδ1 : p.IsHomLift (c.π.app i ≫ 𝟙 (D.obj i)) δ := by simpa using hδ
  let hγ1 : p.IsHomLift (c.π.app i ≫ 𝟙 (D.obj i)) (φ ≫ ε) := by simpa using hγ
  have hδcart : p.IsCartesian (c.π.app i ≫ 𝟙 (D.obj i)) δ := by
    let : p.IsStronglyCartesian (c.π.app i ≫ 𝟙 (D.obj i)) δ := by
      simpa using hp.isStronglyCartesian_homLift (c.π.app i) δ
    infer_instance
  set η := Functor.toPullbackFiber p x xi (c.π.app i ≫ 𝟙 (D.obj i)) δ
  set θ := Functor.toPullbackFiber p x yi (c.π.app i ≫ 𝟙 (D.obj i)) (φ ≫ ε)
  set u := (Functor.fiberIsoOfCartesian (p := p) (c.π.app i ≫ 𝟙 (D.obj i))
    (z := Functor.pullbackFiber p xi (c.π.app i ≫ 𝟙 (D.obj i))) (z' := x)
    (Functor.IsPreFibered.pullbackMap xi.2 (c.π.app i ≫ 𝟙 (D.obj i))) δ
    (Functor.IsPreFibered.pullbackMap.IsCartesian xi.2
      (c.π.app i ≫ 𝟙 (D.obj i))) hδcart).hom
  have hηu : η ≫ u = 𝟙 x := toPullbackFiber_comp_fiberIsoOfCartesian_hom p _ x xi δ
  obtain ⟨k, s, g, hg⟩ := splitFiber_full_descent_same_stage p D c i
    (idSplit p xi) (idSplit p yi)
    (Functor.SplitFiber.ofFiberHom (u ≫ θ))
  have hg' : HEq (Functor.SplitFiber.toFiberHom
      ((Functor.SplitFiber.restrict p (c.π.app k)).map g)) (u ≫ θ) := hg
  have hi : c.π.app k ≫ D.map s ≫ 𝟙 (D.obj i) = c.π.app i ≫ 𝟙 (D.obj i) := by
    simp [c.w s]
  let hδ2 : p.IsHomLift (c.π.app k ≫ D.map s ≫ 𝟙 (D.obj i)) δ := by rwa [hi]
  let hγ2 : p.IsHomLift (c.π.app k ≫ D.map s ≫ 𝟙 (D.obj i)) (φ ≫ ε) := by rwa [hi]
  set ηk := Functor.toPullbackFiber p x xi (c.π.app k ≫ D.map s ≫ 𝟙 (D.obj i)) δ
  set θk := Functor.toPullbackFiber p x yi (c.π.app k ≫ D.map s ≫ 𝟙 (D.obj i)) (φ ≫ ε)
  have hη : HEq ηk η := toPullbackFiber_heq p x xi _ _ hi δ
  have hθ : HEq θk θ := toPullbackFiber_heq p x yi _ _ hi (φ ≫ ε)
  have hηg : ηk ≫ Functor.SplitFiber.toFiberHom
      ((Functor.SplitFiber.restrict p (c.π.app k)).map g) = θk := by
    refine eq_of_heq ?_
    refine (Cat.comp_heq_of_eq (rfl : x = x)
      (congrArg (Functor.pullbackFiber p xi) hi)
      (congrArg (Functor.pullbackFiber p yi) hi) hη hg').trans ?_
    have hcomp : η ≫ u ≫ θ = θ := by
      rw [← Category.assoc, hηu, Category.id_comp]
    exact (heq_of_eq hcomp).trans hθ.symm
  have hfac : Functor.Fiber.fiberInclusion.map
        (Functor.SplitFiber.toFiberHom
          ((Functor.SplitFiber.restrict p (c.π.app k)).map g)) ≫
        Functor.IsPreFibered.pullbackMap yi.2
          (c.π.app k ≫ D.map s ≫ 𝟙 (D.obj i)) =
      Functor.pullbackFiberProj xi (D.map s ≫ 𝟙 (D.obj i)) (c.π.app k) ≫
        Functor.Fiber.fiberInclusion.map (Functor.SplitFiber.toFiberHom g) ≫
        Functor.IsPreFibered.pullbackMap yi.2 (D.map s ≫ 𝟙 (D.obj i)) :=
    Functor.SplitFiber.restrictHom_fac (p := p) (c.π.app k) g
  have hθfac : Functor.Fiber.fiberInclusion.map θk ≫
      Functor.IsPreFibered.pullbackMap yi.2
        (c.π.app k ≫ D.map s ≫ 𝟙 (D.obj i)) = φ ≫ ε :=
    Functor.toPullbackFiber_fac p x yi _ (φ ≫ ε)
  refine ⟨k, s, Functor.pullbackFiber p xi (D.map s ≫ 𝟙 (D.obj i)),
    Functor.pullbackFiber p yi (D.map s ≫ 𝟙 (D.obj i)),
    Functor.IsPreFibered.pullbackMap xi.2 (D.map s ≫ 𝟙 (D.obj i)),
    Functor.IsPreFibered.pullbackMap yi.2 (D.map s ≫ 𝟙 (D.obj i)),
    Functor.Fiber.fiberInclusion.map ηk ≫
      Functor.pullbackFiberProj xi (D.map s ≫ 𝟙 (D.obj i)) (c.π.app k),
    Functor.Fiber.fiberInclusion.map (Functor.SplitFiber.toFiberHom g),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using (Functor.IsPreFibered.pullbackMap.IsCartesian xi.2
      (D.map s ≫ 𝟙 (D.obj i))).toIsHomLift
  · simpa using (Functor.IsPreFibered.pullbackMap.IsCartesian yi.2
      (D.map s ≫ 𝟙 (D.obj i))).toIsHomLift
  · let := ηk.2
    infer_instance
  · exact (Functor.SplitFiber.toFiberHom g).2
  · rw [Category.assoc, Functor.pullbackFiberProj_fac]
    exact Functor.toPullbackFiber_fac p x xi _ δ
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun t => Functor.Fiber.fiberInclusion.map ηk ≫ t)
      hfac.symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun t => t ≫ Functor.IsPreFibered.pullbackMap yi.2
      (c.π.app k ≫ D.map s ≫ 𝟙 (D.obj i)))
      (((Functor.map_comp Functor.Fiber.fiberInclusion ηk _).symm).trans
        (congrArg Functor.Fiber.fiberInclusion.map hηg))).trans hθfac

end StageDescent

end Deformation.Artin

end
