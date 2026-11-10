module

public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSite
public import StacksFrontier.AlgebraicGeometry.Stacks.FormallySmoothOnObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.InfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectMorphismFactor
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver
public import StacksFrontier.CategoryTheory.DottedArrows.Defs
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.LocallyGroupoid
public import StacksFrontier.CategoryTheory.TwoYoneda.OverBase
public import StacksFrontier.CategoryTheory.TwoYoneda.PullbackComparison
public import StacksFrontier.CategoryTheory.TwoYoneda.RepresentedPoint

/-!
# Formal smoothness of a morphism of algebraic stacks by dotted arrows (Stacks 0DNY)

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is formally smooth exactly when every
infinitesimal lifting diagram for it — a first-order thickening `i : T ⟶ T'` of affine objects of
the site, a point `x` of `𝒳` over `T`, a point `y` of `𝒴` over `T'` and a 2-morphism `γ`
witnessing 2-commutativity, i.e. the solid diagram 0DNX — admits a dotted arrow, i.e. the
category `CategoryTheory.DottedArrow` of Stacks 0H18 for that square is nonempty.

The two sides say the same thing in two languages. Formal smoothness
(`AlgebraicGeometry.Stack.IsFormallySmoothOnObjects`, Stacks 06D0) is a lifting condition on
*objects of the fibres* of the two structure functors, with the compatibility written through the
chosen pullbacks of a prefibered structure. A dotted arrow is a lifting datum for *1-morphisms*
out of the represented fibred categories, with the compatibility written as a pasting of
2-morphisms. The 2-Yoneda lemma (Stacks 004B) translates between them: a point of `𝒳` over `T` is
an object of the fibre of `𝒳` over `T`, and a 2-morphism of such points is a morphism of those
fibre objects.

## Main results

* `AlgebraicGeometry.Stack.isFormallySmoothOnObjects_iff_nonempty_dottedArrow`: **Stacks 0DNY**.

## Implementation notes

The translation is carried out through the 2-Yoneda evaluation functor
`CategoryTheory.Functor.twoYonedaEvaluation`, which is an equivalence, with its three halves
available as data: `CategoryTheory.Functor.TwoYoneda.liftBased` and
`AlgebraicGeometry.Stack.objectMorphism` turn an object of a fibre into a 1-morphism out of the
represented fibred category, `CategoryTheory.Functor.TwoYoneda.liftBasedEvaluationIso` compares
the two, and `CategoryTheory.Functor.TwoYoneda.hom₂OfFiberHom` turns a morphism of fibre objects
into a 2-morphism, with `AlgebraicGeometry.Stack.pointHom₂` the same read in the 2-category of
categories fibred in groupoids.

Two further comparisons do the bookkeeping that the source's "translation between different
languages omitted" hides. The value of a 1-morphism out of the category represented by `T'` at the
object `(T, i)` of the slice is a chosen pullback along `i` of its value at the terminal object:
that is `CategoryTheory.Functor.TwoYoneda.pullbackFiberTwoYonedaIso`, and the component at
`(T, i)` of a 2-morphism is read through it by
`CategoryTheory.Functor.TwoYoneda.twoYonedaEvaluation_app_eq_comp`. And the image under `f` of a
chosen pullback is a chosen pullback of the image, which is the comparison already built into
`AlgebraicGeometry.Stack.IsFormallySmoothOnObjects`.

Every 2-morphism of categories fibred in groupoids is invertible, so a 2-morphism is upgraded to
an isomorphism of the underlying functors over the site by
`CategoryTheory.CatFiberedInGroupoids.basedIsoOfHom₂` wherever an inverse is needed; no
invertibility hypothesis is ever required of the data.

The comparisons below are morphisms of the fibres of the two structure functors, and their
objects are built from definitions the `implicit` transparency level does not unfold —
`CategoryTheory.Bicategory.InducedBicategory`, so that `𝒳.val` is a subtype at all;
`CategoryTheory.Functor.Fiber` with its inclusion and induced functors; the 2-Yoneda evaluation
functor — so the goals are not type-correct at that level and `rw` and `simp` decline to act on
them. Naming the unfolding chain in the `attribute` line below is what lets the ordinary tactics
see through it, exactly as in `AlgebraicGeometry.BigFppfOver`'s rendering of Stacks 06D0; where
even that is not enough, the composite is reassociated by `exact` against one of the abstract
bookkeeping lemmas at the head of the file, and every object of a fibre is named by a single
spelling, fixed by an explicit type ascription on the `let` that introduces it.

## References

* [Stacks Project, Tag 0DNY](https://stacks.math.columbia.edu/tag/0DNY)
* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 0H18](https://stacks.math.columbia.edu/tag/0H18)
-/

@[expose] public section

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.BasedCategory.ofFunctor CategoryTheory.BasedFunctor.comp
  CategoryTheory.Functor.Fiber.mapOfComp CategoryTheory.Functor.twoYonedaEvaluation
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.instCategoryObj CategoryTheory.Functor.Fiber.inducedFunctor
  CategoryTheory.Bicategory.InducedBicategory.categoryStruct
  CategoryTheory.Bicategory.InducedBicategory.bicategory
  CategoryTheory.BasedCategory.bicategory CategoryTheory.BasedCategory.instCategory
  AlgebraicGeometry.Stack.overMapBased
  AlgebraicGeometry.Stack.schemeFibredCategoryMap AlgebraicGeometry.Stack.objectMorphism

namespace AlgebraicGeometry.Stack

universe u w

/-- A three-fold composite evaluated by two successive factorisations. Separated out for the
same reason as `AlgebraicGeometry.Stack.comp_five_eq_of_factorisations`. -/
private theorem comp_three_eq_of_factorisations {C : Type*} [Category C] {a b c d : C}
    (A : a ⟶ b) (Bm : b ⟶ c) (Cm : c ⟶ d) (u : b ⟶ d) (r : a ⟶ d)
    (h1 : Bm ≫ Cm = u) (h2 : A ≫ u = r) : (A ≫ Bm) ≫ Cm = r := by
  rw [Category.assoc, h1, h2]

/-- The square of **Stacks 06D0** read off from two factorisations and a cancellation: the
bookkeeping of the backward half of Stacks 0DNY, in an abstract category for the reason given
on `AlgebraicGeometry.Stack.comp_five_eq_of_factorisations`. -/
private theorem comp_eq_of_cancel_iso {C : Type*} [Category C] {P Q R S₁ S₂ W V : C}
    (CI : P ⟶ Q) (m₁ : Q ⟶ R) (m₂ : R ⟶ S₁) (m₃ : S₁ ≅ S₂) (g : S₂ ≅ W)
    (cA : P ⟶ R) (pbI : P ⟶ V) (pbB : V ⟶ P) (pbH : V ⟶ W)
    (h5 : pbI ≫ pbB = 𝟙 P) (hcore : CI ≫ m₁ = cA)
    (hkey : pbH ≫ g.inv ≫ m₃.inv = pbB ≫ cA ≫ m₂) :
    (CI ≫ m₁ ≫ m₂ ≫ m₃.hom) ≫ g.hom = pbI ≫ pbH := by
  refine (cancel_mono (g.inv ≫ m₃.inv)).mp ?_
  simp [reassoc_of% hcore, hkey, reassoc_of% h5]

/-- A five-fold composite evaluated by four successive factorisations, the last of which is
cancelled by an inverse: if `E ≫ P = u ≫ v`, `D ≫ u = t`, `C ≫ t = q`, `A ≫ q = r ≫ w` and
`w ≫ v = 𝟙`, then `A ≫ C ≫ D ≫ E ≫ P = r`.

This is pure associativity bookkeeping, separated out because the composites it is applied to
are not type-correct at the `implicit` transparency level — their objects agree only after
`CategoryTheory.Functor.Fiber.fiberInclusion_obj_mapOfComp_obj` — so the rewriting tactics
decline to reassociate them in place, while `exact` against an abstract statement does not
care. -/
private theorem comp_five_eq_of_factorisations {C : Type*} [Category C] {a b c d e g k : C}
    (A : a ⟶ b) (Cm : b ⟶ c) (D : c ⟶ d) (E : d ⟶ e) (P : e ⟶ g)
    (u : d ⟶ k) (v : k ⟶ g) (t : c ⟶ k) (q : b ⟶ k) (r : a ⟶ g) (w : g ⟶ k)
    (h1 : E ≫ P = u ≫ v) (h2 : D ≫ u = t) (h3 : Cm ≫ t = q)
    (h4 : A ≫ q = r ≫ w) (h5 : w ≫ v = 𝟙 g) :
    A ≫ Cm ≫ D ≫ E ≫ P = r := by
  rw [h1, ← Category.assoc D u v, h2, ← Category.assoc Cm t v, h3,
    ← Category.assoc A q v, h4, Category.assoc, h5, Category.comp_id]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The 2-morphism between two 1-morphisms out of the fibred category represented by `U` induced,
through fullness of the 2-Yoneda evaluation functor, by a morphism of the fibre objects they
evaluate to. -/
noncomputable def pointHom₂ (U : BigFppfOver B S hS)
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    {a b : schemeFibredCategory B S hS U ⟶ 𝒴}
    (φ : (Functor.twoYonedaEvaluation 𝒴.val.p U).obj a.hom ⟶
      (Functor.twoYonedaEvaluation 𝒴.val.p U).obj b.hom) : a ⟶ b :=
  (CatFiberedInGroupoids.homEquivBasedNatTrans a b).symm
    (Functor.TwoYoneda.hom₂OfFiberHom 𝒴.val.p 𝒴.isFiberedInGroupoids U φ)

/-- The component at the terminal object of the slice of
`AlgebraicGeometry.Stack.pointHom₂` is the morphism of fibre objects it was built from. -/
theorem pointHom₂_app_unit (U : BigFppfOver B S hS)
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    {a b : schemeFibredCategory B S hS U ⟶ 𝒴}
    (φ : (Functor.twoYonedaEvaluation 𝒴.val.p U).obj a.hom ⟶
      (Functor.twoYonedaEvaluation 𝒴.val.p U).obj b.hom) :
    (pointHom₂ B S hS U 𝒴 φ).hom.toNatTrans.app (Over.mk (𝟙 U)) =
      Functor.Fiber.fiberInclusion.map φ :=
  Functor.TwoYoneda.hom₂OfFiberHom_app_unit 𝒴.val.p 𝒴.isFiberedInGroupoids U φ

variable {B S hS}

/-- The functor between the fibres over `U` induced by a 1-morphism of categories fibred in
groupoids: on objects and on morphisms it is the underlying functor.

This is `CategoryTheory.Functor.Fiber.mapOfComp` for the compatibility
`CategoryTheory.CatFiberedInGroupoids.homFunctor_comp_p`, under a name short enough to appear in
a statement and marked `implicit_reducible` so that the equality
`CategoryTheory.Functor.Fiber.fiberInclusion_obj_mapOfComp_obj` between the image of a fibre
object and the fibre object of the image — which holds by `rfl` — is visible to the rewriting
tactics. -/
@[implicit_reducible]
noncomputable def fiberMapOfHom
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (U : BigFppfOver B S hS) : 𝒳.val.p.Fiber U ⥤ 𝒴.val.p.Fiber U :=
  Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor p)
    (CatFiberedInGroupoids.homFunctor_comp_p p) U

/-- The inclusion of a fibre sends a composite of four morphisms, grouped as a triple followed by
one, to the corresponding composite of the images. -/
private theorem fiberInclusion_map_comp_triple_comp {C D : Type*} [Category C] [Category D]
    {p : C ⥤ D} {X : D} {a b c d e : p.Fiber X} (A : a ⟶ b) (Bm : b ⟶ c) (Cm : c ⟶ d)
    (E : d ⟶ e) : Functor.Fiber.fiberInclusion.map ((A ≫ Bm ≫ Cm) ≫ E) =
      (Functor.Fiber.fiberInclusion.map A ≫ Functor.Fiber.fiberInclusion.map Bm ≫
        Functor.Fiber.fiberInclusion.map Cm) ≫ Functor.Fiber.fiberInclusion.map E := by
  simp

/-- The component at the terminal object of the pasting of `β` and `α` along the thickening
`i` is the component of `β` at `(T, i)` followed by the image under `f` of that of `α`. -/
private theorem pasting_app_unit {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {T T' : BigFppfOver B S hS} (i : T ⟶ T') {x : schemeFibredCategory B S hS T ⟶ 𝒳.1}
    {y : schemeFibredCategory B S hS T' ⟶ 𝒴.1} {a : schemeFibredCategory B S hS T' ⟶ 𝒳.1}
    (α : schemeFibredCategoryMap B S hS i ≫ a ⟶ x) (β : y ⟶ a ≫ f.hom) :
    (CatFiberedInGroupoids.homEquivBasedNatTrans
        (schemeFibredCategoryMap B S hS i ≫ y) (x ≫ f.hom)
        (Bicategory.whiskerLeft (schemeFibredCategoryMap B S hS i) β ≫
          (Bicategory.associator (schemeFibredCategoryMap B S hS i) a f.hom).inv ≫
            Bicategory.whiskerRight α f.hom)).app (Over.mk (𝟙 T)) =
      β.hom.toNatTrans.app (Over.mk i) ≫
        (CatFiberedInGroupoids.homFunctor f.hom).map
          (α.hom.toNatTrans.app (Over.mk (𝟙 T))) := by
  have hassoc : (Bicategory.associator (schemeFibredCategoryMap B S hS i).hom a.hom
      f.hom.hom).inv.toNatTrans.app (Over.mk (𝟙 T)) = 𝟙 _ := rfl
  change β.hom.toNatTrans.app (Over.mk i) ≫ (Bicategory.associator
    (schemeFibredCategoryMap B S hS i).hom a.hom f.hom.hom).inv.toNatTrans.app (Over.mk (𝟙 T)) ≫
      (CatFiberedInGroupoids.homFunctor f.hom).map (α.hom.toNatTrans.app (Over.mk (𝟙 T))) = _
  rw [hassoc]
  exact congrArg (fun z => β.hom.toNatTrans.app (Over.mk i) ≫ z) (Category.id_comp _)

/-- The forward half of **Stacks 0DNY**, for a lifting diagram whose 1-morphism of represented
fibred categories is literally the one induced by the thickening.

Evaluating the diagram at the terminal objects of the two slices turns it into the lifting
problem of Stacks 06D0 for the fibre object `x` names over `T` and the fibre object `y` names
over `T'`, whose comparison 2-morphism is `γ` read through the chosen pullback along `i`. Formal
smoothness solves that problem, and the 2-Yoneda lemma turns the solution back into a 1-morphism
out of the fibred category represented by `T'` together with the two 2-morphisms. -/
private theorem nonempty_dottedArrow_aux
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h : IsFormallySmoothOnObjects B S hS 𝒳.1 𝒴.1 f.hom)
    {T T' : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (i : T ⟶ T')
    (hth : Stacks.Thickenings.IsFirstOrderThickening (B.inclusion.map i.left))
    (x : schemeFibredCategory B S hS T ⟶ 𝒳.1)
    (y : schemeFibredCategory B S hS T' ⟶ 𝒴.1)
    (γd : (schemeFibredCategoryMap B S hS i ≫ y) ⟶ (x ≫ f.hom)) :
    Nonempty (DottedArrow x (schemeFibredCategoryMap B S hS i) f.hom y γd) := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  unfold IsFormallySmoothOnObjects at h
  -- the value of `y` at the object `(T, i)` of the slice is a chosen pullback of `y` at `T'`
  let hcy : 𝒴.val.val.p.pullbackFiber ((Functor.twoYonedaEvaluation 𝒴.val.val.p T').obj y.hom) i ≅
      (Functor.twoYonedaEvaluation 𝒴.val.val.p T).obj (schemeFibredCategoryMap B S hS i ≫ y).hom :=
    Functor.TwoYoneda.pullbackFiberTwoYonedaIso 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids i y.hom
  let γEval := (Functor.twoYonedaEvaluation 𝒴.val.val.p T).mapIso
    (CatFiberedInGroupoids.basedIsoOfHom₂ γd)
  let γ₀ : (fiberMapOfHom f.hom T).obj ((Functor.twoYonedaEvaluation 𝒳.val.val.p T).obj x.hom) ≅
      𝒴.val.val.p.pullbackFiber
        ((Functor.twoYonedaEvaluation 𝒴.val.val.p T').obj y.hom) i :=
    γEval.symm ≪≫ hcy.symm
  obtain ⟨x', β, γ', hsq⟩ := h T T' i hT hT' hth
    ((Functor.twoYonedaEvaluation 𝒳.val.val.p T).obj x.hom)
    ((Functor.twoYonedaEvaluation 𝒴.val.val.p T').obj y.hom) γ₀
  have hx' : (Functor.twoYonedaEvaluation 𝒳.val.val.p T').obj
      (objectMorphism B S hS 𝒳.val x').hom ≅ x' :=
    Functor.TwoYoneda.liftBasedEvaluationIso 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids T' x'
  let hcx : 𝒳.val.val.p.pullbackFiber
        ((Functor.twoYonedaEvaluation 𝒳.val.val.p T').obj
          (objectMorphism B S hS 𝒳.val x').hom) i ≅
      (Functor.twoYonedaEvaluation 𝒳.val.val.p T).obj
        (schemeFibredCategoryMap B S hS i ≫ objectMorphism B S hS 𝒳.val x').hom :=
    Functor.TwoYoneda.pullbackFiberTwoYonedaIso 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids i (objectMorphism B S hS 𝒳.val x').hom
  let αEvalIso : (Functor.twoYonedaEvaluation 𝒳.val.val.p T).obj
        (schemeFibredCategoryMap B S hS i ≫ objectMorphism B S hS 𝒳.val x').hom ≅
      (Functor.twoYonedaEvaluation 𝒳.val.val.p T).obj x.hom :=
    hcx.symm ≪≫ Functor.pullbackFiberIso hx' i ≪≫ β
  let αH := pointHom₂ B S hS T 𝒳.val αEvalIso.hom
  -- the image under `f` of that comparison, read in the fibre of `𝒴` over `T'`
  let hxF : (Functor.twoYonedaEvaluation 𝒴.val.val.p T').obj
        ((objectMorphism B S hS 𝒳.val x') ≫ f.hom).hom ≅
      (fiberMapOfHom f.hom T').obj x' :=
    (fiberMapOfHom f.hom T').mapIso hx'
  let βEvalIso : (Functor.twoYonedaEvaluation 𝒴.val.val.p T').obj y.hom ≅
      (Functor.twoYonedaEvaluation 𝒴.val.val.p T').obj
        ((objectMorphism B S hS 𝒳.val x') ≫ f.hom).hom :=
    γ'.symm ≪≫ hxF.symm
  let βH := pointHom₂ B S hS T' 𝒴.val βEvalIso.hom
  refine ⟨⟨(objectMorphism B S hS 𝒳.val x'), αH, βH, ?_⟩⟩
  change γd = Bicategory.whiskerLeft (schemeFibredCategoryMap B S hS i) βH ≫
    (Bicategory.associator (schemeFibredCategoryMap B S hS i)
      (objectMorphism B S hS 𝒳.val x') f.hom).inv ≫
      Bicategory.whiskerRight αH f.hom
  have hmapCart' : 𝒴.val.val.p.IsCartesian i
      ((CatFiberedInGroupoids.homFunctor f.hom).map
        (Functor.IsPreFibered.pullbackMap x'.2 i)) := by
    have hxLift : 𝒳.val.val.p.IsHomLift i
      (Functor.IsPreFibered.pullbackMap x'.2 i) := inferInstance
    have := CatFiberedInGroupoids.isStronglyCartesian_map f.hom i
      (Functor.IsPreFibered.pullbackMap x'.2 i)
    infer_instance
  -- the comparison between the image of a chosen pullback and the chosen pullback of the image
  let compareI := Functor.fiberIsoOfCartesian (p := 𝒴.val.val.p)
    (z := 𝒴.val.val.p.pullbackFiber ((fiberMapOfHom f.hom T').obj x') i)
    (z' := (fiberMapOfHom f.hom T).obj (𝒳.val.val.p.pullbackFiber x' i)) i
    (Functor.IsPreFibered.pullbackMap ((fiberMapOfHom f.hom T').obj x').2 i)
    ((CatFiberedInGroupoids.homFunctor f.hom).map
      (Functor.IsPreFibered.pullbackMap x'.2 i))
    (by infer_instance) hmapCart'
  have hsq' : (compareI.hom ≫ (fiberMapOfHom f.hom T).map β.hom) ≫ γ₀.hom =
      Functor.pullbackFiberHom (p := 𝒴.val.val.p) γ'.hom i := hsq
  have hsqInv : γ₀.inv =
      Functor.pullbackFiberHom (p := 𝒴.val.val.p) γ'.inv i ≫
        compareI.hom ≫ (fiberMapOfHom f.hom T).map β.hom := by
    apply (cancel_mono γ₀.hom).1
    calc
      γ₀.inv ≫ γ₀.hom = 𝟙 _ := γ₀.inv_hom_id
      _ = (Functor.pullbackFiberHom (p := 𝒴.val.val.p) γ'.inv i ≫
          compareI.hom ≫ (fiberMapOfHom f.hom T).map β.hom) ≫ γ₀.hom := by
            simp [Category.assoc, hsq']
  have hgammaEval : γEval.hom =
      hcy.inv ≫ Functor.pullbackFiberHom (p := 𝒴.val.val.p) γ'.inv i ≫
        compareI.hom ≫ (fiberMapOfHom f.hom T).map β.hom := by
    rw [← hsqInv]
    exact (Iso.inv_hom_id_assoc hcy γEval.hom).symm
  -- the comparison of the two cartesian lifts of `i` at the image of `x'`
  let cFX : 𝒴.val.val.p.pullbackFiber
        ((Functor.twoYonedaEvaluation 𝒴.val.val.p T').obj
          (objectMorphism B S hS 𝒳.val x' ≫ f.hom).hom) i ≅
      (fiberMapOfHom f.hom T).obj
        ((Functor.twoYonedaEvaluation 𝒳.val.val.p T).obj
          (schemeFibredCategoryMap B S hS i ≫ objectMorphism B S hS 𝒳.val x').hom) :=
    Functor.TwoYoneda.pullbackFiberTwoYonedaIso 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids i ((objectMorphism B S hS 𝒳.val x') ≫ f.hom).hom
  have hrhs : Functor.Fiber.fiberInclusion.map
        (Functor.pullbackFiberHom (p := 𝒴.val.val.p)
            hxF.inv i ≫ cFX.hom ≫
          (fiberMapOfHom f.hom T).map hcx.inv ≫
          (fiberMapOfHom f.hom T).map
            (Functor.pullbackFiberHom (p := 𝒳.val.val.p) hx'.hom i)) ≫
      (CatFiberedInGroupoids.homFunctor f.hom).map
        (Functor.IsPreFibered.pullbackMap x'.2 i) =
      Functor.IsPreFibered.pullbackMap ((fiberMapOfHom f.hom T').obj x').2 i := by
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    -- the image under `f` of the defining factorisation of the chosen pullback of the lift
    have s1 : Functor.Fiber.fiberInclusion.map ((fiberMapOfHom f.hom T).map
          (Functor.pullbackFiberHom (p := 𝒳.val.val.p) hx'.hom i)) ≫
        (CatFiberedInGroupoids.homFunctor f.hom).map
          (Functor.IsPreFibered.pullbackMap x'.2 i) =
        (CatFiberedInGroupoids.homFunctor f.hom).map
            (Functor.IsPreFibered.pullbackMap
              ((Functor.twoYonedaEvaluation 𝒳.val.val.p T').obj
                (objectMorphism B S hS 𝒳.val x').hom).2 i) ≫
          Functor.Fiber.fiberInclusion.map hxF.hom := by
      change (CatFiberedInGroupoids.homFunctor f.hom).map
          (Functor.Fiber.fiberInclusion.map
            (Functor.pullbackFiberHom (p := 𝒳.val.val.p) hx'.hom i)) ≫
          (CatFiberedInGroupoids.homFunctor f.hom).map
            (Functor.IsPreFibered.pullbackMap x'.2 i) = _
      rw [← Functor.map_comp, Functor.pullbackFiberHom_fac, Functor.map_comp]
      rfl
    -- the image under `f` of the comparison of the two cartesian lifts in `𝒳`
    have s2 : Functor.Fiber.fiberInclusion.map ((fiberMapOfHom f.hom T).map hcx.inv) ≫
        (CatFiberedInGroupoids.homFunctor f.hom).map
          (Functor.IsPreFibered.pullbackMap
            ((Functor.twoYonedaEvaluation 𝒳.val.val.p T').obj
              (objectMorphism B S hS 𝒳.val x').hom).2 i) =
        (CatFiberedInGroupoids.homFunctor f.hom).map
          ((objectMorphism B S hS 𝒳.val x').hom.map
            (Functor.TwoYoneda.sliceToTerminal i)) := by
      change (CatFiberedInGroupoids.homFunctor f.hom).map
          (Functor.Fiber.fiberInclusion.map hcx.inv) ≫ _ = _
      rw [← Functor.map_comp]
      exact congrArg _ (Functor.fiberIsoOfCartesian_inv_fac i _ _ _ _)
    -- the defining factorisation of the comparison in `𝒴`
    have s3 : Functor.Fiber.fiberInclusion.map cFX.hom ≫
        (CatFiberedInGroupoids.homFunctor f.hom).map
          ((objectMorphism B S hS 𝒳.val x').hom.map
            (Functor.TwoYoneda.sliceToTerminal i)) =
        Functor.IsPreFibered.pullbackMap
          ((Functor.twoYonedaEvaluation 𝒴.val.val.p T').obj
            ((objectMorphism B S hS 𝒳.val x') ≫ f.hom).hom).2 i :=
      Functor.fiberIsoOfCartesian_hom_fac i _ _ _ _
    -- the defining factorisation of the chosen pullback of the image comparison
    have s4 : Functor.Fiber.fiberInclusion.map
          (Functor.pullbackFiberHom (p := 𝒴.val.val.p) hxF.inv i) ≫
        Functor.IsPreFibered.pullbackMap
          ((Functor.twoYonedaEvaluation 𝒴.val.val.p T').obj
            ((objectMorphism B S hS 𝒳.val x') ≫ f.hom).hom).2 i =
        Functor.IsPreFibered.pullbackMap ((fiberMapOfHom f.hom T').obj x').2 i ≫
          Functor.Fiber.fiberInclusion.map hxF.inv :=
      Functor.pullbackFiberHom_fac hxF.inv i
    have s5 : Functor.Fiber.fiberInclusion.map hxF.inv ≫
        Functor.Fiber.fiberInclusion.map hxF.hom = 𝟙 _ := by
      rw [← Functor.map_comp, hxF.inv_hom_id, CategoryTheory.Functor.map_id]
    exact comp_five_eq_of_factorisations _ _ _ _ _ _ _ _ _ _ _ s1 s2 s3 s4 s5
  have hcore : compareI.hom = Functor.pullbackFiberHom (p := 𝒴.val.val.p)
        hxF.inv i ≫ cFX.hom ≫
        (fiberMapOfHom f.hom T).map hcx.inv ≫
        (fiberMapOfHom f.hom T).map
          (Functor.pullbackFiberHom (p := 𝒳.val.val.p) hx'.hom i) :=
    Functor.fiber_hom_ext_of_cartesian i
      ((CatFiberedInGroupoids.homFunctor f.hom).map
        (Functor.IsPreFibered.pullbackMap x'.2 i)) hmapCart' _ _
      ((Functor.fiberIsoOfCartesian_hom_fac i _ _ _ _).trans hrhs.symm)
  have hkey : hcy.inv ≫ Functor.pullbackFiberHom (p := 𝒴.val.val.p) γ'.inv i ≫
        compareI.hom ≫ (fiberMapOfHom f.hom T).map β.hom =
      (hcy.inv ≫ Functor.pullbackFiberHom (p := 𝒴.val.val.p) βEvalIso.hom i ≫ cFX.hom) ≫
        (fiberMapOfHom f.hom T).map αEvalIso.hom := by
    have hβhom : βEvalIso.hom = γ'.inv ≫ hxF.inv := rfl
    have hαhom : αEvalIso.hom =
        hcx.inv ≫ Functor.pullbackFiberHom (p := 𝒳.val.val.p) hx'.hom i ≫ β.hom := rfl
    rw [hβhom, hαhom, Functor.pullbackFiberHom_comp, Functor.map_comp, Functor.map_comp,
      hcore]
    simp [Category.assoc]
  have hAlphaApp : αH.hom.toNatTrans.app (Over.mk (𝟙 T)) =
      Functor.Fiber.fiberInclusion.map αEvalIso.hom :=
    pointHom₂_app_unit B S hS T 𝒳.val αEvalIso.hom
  have hBetaAtI : βH.hom.toNatTrans.app (Over.mk i) =
      Functor.Fiber.fiberInclusion.map hcy.inv ≫
        Functor.Fiber.fiberInclusion.map
          (Functor.pullbackFiberHom (p := 𝒴.val.val.p) βEvalIso.hom i) ≫
          Functor.Fiber.fiberInclusion.map cFX.hom := by
    have hmap : (Functor.twoYonedaEvaluation 𝒴.val.val.p T').map βH.hom = βEvalIso.hom :=
      Functor.TwoYoneda.twoYonedaEvaluation_map_hom₂OfFiberHom 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids T' βEvalIso.hom
    have hcomp := Functor.TwoYoneda.twoYonedaEvaluation_app_eq_comp 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids i y.hom ((objectMorphism B S hS 𝒳.val x') ≫ f.hom).hom βH.hom
    rwa [hmap] at hcomp
  have hGammaApp : (CatFiberedInGroupoids.homEquivBasedNatTrans
        (schemeFibredCategoryMap B S hS i ≫ y) (x ≫ f.hom) γd).app
      (Over.mk (𝟙 T)) = Functor.Fiber.fiberInclusion.map γEval.hom :=
    (Functor.twoYonedaEvaluation_map 𝒴.val.val.p T
      (CatFiberedInGroupoids.homEquivBasedNatTrans
        (schemeFibredCategoryMap B S hS i ≫ y) (x ≫ f.hom) γd)).symm
  apply (CatFiberedInGroupoids.homEquivBasedNatTrans
    (schemeFibredCategoryMap B S hS i ≫ y) (x ≫ f.hom)).injective
  refine Functor.TwoYoneda.hom_ext_of_app_unit 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids _ _ ?_
  rw [pasting_app_unit f i αH βH, hGammaApp, hgammaEval, hBetaAtI, hAlphaApp]
  rw [hkey]
  exact fiberInclusion_map_comp_triple_comp _ _ _ _

/-- **Stacks 0DNY**, forward half: formal smoothness gives a dotted arrow in every infinitesimal
lifting diagram. The diagram's `j_canonical` field identifies its 1-morphism of represented
fibred categories with the one induced by the thickening, which reduces the statement to
`AlgebraicGeometry.Stack.nonempty_dottedArrow_aux`. -/
private theorem nonempty_dottedArrow_of_isFormallySmoothOnObjects
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h : IsFormallySmoothOnObjects B S hS 𝒳.1 𝒴.1 f.hom)
    (d : InfinitesimalLiftingDiagram B S hS 𝒳 𝒴 f) :
    Nonempty (DottedArrow d.x d.j f.hom d.y d.γ) := by
  obtain ⟨T, T', hT, hT', i, hth, j, hj, x, y, γd⟩ := d
  change Nonempty (DottedArrow x j f.hom y γd)
  obtain rfl : j = schemeFibredCategoryMap B S hS i :=
    (CatFiberedInGroupoids.homEquivBasedFunctor _ _).injective
      (BasedCategory.BasedFunctor.ext' hj)
  exact nonempty_dottedArrow_aux f h hT hT' i hth x y _

/-- **Stacks 0DNY**, backward half: if every infinitesimal lifting diagram admits a dotted
arrow then the morphism is formally smooth on objects.

The lifting problem of Stacks 06D0 is turned into a diagram by naming its two fibre objects
through the 2-Yoneda lemma and reading its comparison 2-morphism as the 2-commutativity datum;
a dotted arrow for that diagram evaluates back to a solution of the lifting problem. -/
private theorem isFormallySmoothOnObjects_of_nonempty_dottedArrow
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (h : ∀ d : InfinitesimalLiftingDiagram B S hS 𝒳 𝒴 f,
      Nonempty (DottedArrow d.x d.j f.hom d.y d.γ)) :
    IsFormallySmoothOnObjects B S hS 𝒳.1 𝒴.1 f.hom := by
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  change ∀ (U U' : BigFppfOver B S hS) (i : U ⟶ U'),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj U') →
    Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) →
    ∀ (x : 𝒳.val.val.p.Fiber U) (y : 𝒴.val.val.p.Fiber U')
      (γ : (fiberMapOfHom f.hom U).obj x ≅ Functor.pullbackFiber 𝒴.val.val.p y i),
      ∃ (x' : 𝒳.val.val.p.Fiber U')
        (β : Functor.pullbackFiber 𝒳.val.val.p x' i ≅ x)
        (γ' : (fiberMapOfHom f.hom U').obj x' ≅ y),
        ((Functor.fiberIsoOfCartesian (p := 𝒴.val.val.p) i
              (Functor.IsPreFibered.pullbackMap ((fiberMapOfHom f.hom U').obj x').2 i)
              ((CatFiberedInGroupoids.homFunctor f.hom).map
                (Functor.IsPreFibered.pullbackMap x'.2 i))
              (Functor.IsPreFibered.pullbackMap.IsCartesian _ _)
              (@Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
                _ _ _ _ _ _ _ _ _ _ _
                (CatFiberedInGroupoids.isStronglyCartesian_map f.hom i
                  (Functor.IsPreFibered.pullbackMap x'.2 i)))).hom ≫
          (fiberMapOfHom f.hom U).map β.hom) ≫ γ.hom =
          Functor.pullbackFiberHom (p := 𝒴.val.val.p) γ'.hom i
  intro U U' i hU hU' hth x y γ
  -- the points of `𝒳` and `𝒴` named by the two fibre objects
  have hx : (Functor.twoYonedaEvaluation 𝒳.val.val.p U).obj
      (objectMorphism B S hS 𝒳.val x).hom ≅ x :=
    Functor.TwoYoneda.liftBasedEvaluationIso 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids U x
  have hy : (Functor.twoYonedaEvaluation 𝒴.val.val.p U').obj
      (objectMorphism B S hS 𝒴.val y).hom ≅ y :=
    Functor.TwoYoneda.liftBasedEvaluationIso 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids U' y
  let hcy : 𝒴.val.val.p.pullbackFiber
        ((Functor.twoYonedaEvaluation 𝒴.val.val.p U').obj
          (objectMorphism B S hS 𝒴.val y).hom) i ≅
      (Functor.twoYonedaEvaluation 𝒴.val.val.p U).obj
        (schemeFibredCategoryMap B S hS i ≫ objectMorphism B S hS 𝒴.val y).hom :=
    Functor.TwoYoneda.pullbackFiberTwoYonedaIso 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids i (objectMorphism B S hS 𝒴.val y).hom
  -- the 2-commutativity datum of the diagram the two points form
  let hδ : (Functor.twoYonedaEvaluation 𝒴.val.val.p U).obj
        (schemeFibredCategoryMap B S hS i ≫ objectMorphism B S hS 𝒴.val y).hom ≅
      (Functor.twoYonedaEvaluation 𝒴.val.val.p U).obj
        (objectMorphism B S hS 𝒳.val x ≫ f.hom).hom :=
    hcy.symm ≪≫ Functor.pullbackFiberIso hy i ≪≫ γ.symm ≪≫
      (fiberMapOfHom f.hom U).mapIso hx.symm
  let d : InfinitesimalLiftingDiagram B S hS 𝒳 𝒴 f :=
    { T := U, T' := U', affine_T := hU, affine_T' := hU', i := i, thickening := hth
      j := schemeFibredCategoryMap B S hS i, j_canonical := rfl
      x := objectMorphism B S hS 𝒳.val x, y := objectMorphism B S hS 𝒴.val y
      γ := pointHom₂ B S hS U 𝒴.val hδ.hom }
  obtain ⟨a⟩ := h d
  -- the dotted arrow evaluates back to a solution of the lifting problem
  let hcxA : 𝒳.val.val.p.pullbackFiber
        ((Functor.twoYonedaEvaluation 𝒳.val.val.p U').obj a.a.hom) i ≅
      (Functor.twoYonedaEvaluation 𝒳.val.val.p U).obj
        (schemeFibredCategoryMap B S hS i ≫ a.a).hom :=
    Functor.TwoYoneda.pullbackFiberTwoYonedaIso 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids i a.a.hom
  let αEval := (Functor.twoYonedaEvaluation 𝒳.val.val.p U).mapIso
    (CatFiberedInGroupoids.basedIsoOfHom₂ a.α)
  let βEval := (Functor.twoYonedaEvaluation 𝒴.val.val.p U').mapIso
    (CatFiberedInGroupoids.basedIsoOfHom₂ a.β)
  let βfs : 𝒳.val.val.p.pullbackFiber
        ((Functor.twoYonedaEvaluation 𝒳.val.val.p U').obj a.a.hom) i ≅ x :=
    hcxA ≪≫ αEval ≪≫ hx
  let γfs : (fiberMapOfHom f.hom U').obj
        ((Functor.twoYonedaEvaluation 𝒳.val.val.p U').obj a.a.hom) ≅ y :=
    βEval.symm ≪≫ hy
  refine ⟨(Functor.twoYonedaEvaluation 𝒳.val.val.p U').obj a.a.hom, βfs, γfs, ?_⟩
  -- the comparison between the image of a chosen pullback and the chosen pullback of the image
  have hmapCart2 : 𝒴.val.val.p.IsCartesian i
      ((CatFiberedInGroupoids.homFunctor f.hom).map
        (Functor.IsPreFibered.pullbackMap
          ((Functor.twoYonedaEvaluation 𝒳.val.val.p U').obj a.a.hom).2 i)) :=
    @Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian
      _ _ _ _ _ _ _ _ _ _ _
      (CatFiberedInGroupoids.isStronglyCartesian_map f.hom i
        (Functor.IsPreFibered.pullbackMap
          ((Functor.twoYonedaEvaluation 𝒳.val.val.p U').obj a.a.hom).2 i))
  let CI := Functor.fiberIsoOfCartesian (p := 𝒴.val.val.p)
    (z := 𝒴.val.val.p.pullbackFiber
      ((fiberMapOfHom f.hom U').obj
        ((Functor.twoYonedaEvaluation 𝒳.val.val.p U').obj a.a.hom)) i)
    (z' := (fiberMapOfHom f.hom U).obj
      (𝒳.val.val.p.pullbackFiber
        ((Functor.twoYonedaEvaluation 𝒳.val.val.p U').obj a.a.hom) i)) i
    (Functor.IsPreFibered.pullbackMap
      ((fiberMapOfHom f.hom U').obj
        ((Functor.twoYonedaEvaluation 𝒳.val.val.p U').obj a.a.hom)).2 i)
    ((CatFiberedInGroupoids.homFunctor f.hom).map
      (Functor.IsPreFibered.pullbackMap
        ((Functor.twoYonedaEvaluation 𝒳.val.val.p U').obj a.a.hom).2 i))
    (by infer_instance) hmapCart2
  -- the comparison of the two cartesian lifts of `i` at the image of the diagonal
  let cA : 𝒴.val.val.p.pullbackFiber
        ((Functor.twoYonedaEvaluation 𝒴.val.val.p U').obj (a.a ≫ f.hom).hom) i ≅
      (fiberMapOfHom f.hom U).obj
        ((Functor.twoYonedaEvaluation 𝒳.val.val.p U).obj
          (schemeFibredCategoryMap B S hS i ≫ a.a).hom) :=
    Functor.TwoYoneda.pullbackFiberTwoYonedaIso 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids i (a.a ≫ f.hom).hom
  have hcompat : Functor.Fiber.fiberInclusion.map hδ.hom =
      a.β.hom.toNatTrans.app (Over.mk i) ≫
        (CatFiberedInGroupoids.homFunctor f.hom).map
          (a.α.hom.toNatTrans.app (Over.mk (𝟙 U))) :=
    ((pointHom₂_app_unit B S hS U 𝒴.val hδ.hom).symm.trans
      (congrArg (fun z => z.hom.toNatTrans.app (Over.mk (𝟙 U))) a.compat)).trans
      (pasting_app_unit f i a.α a.β)
  have hβAtI : a.β.hom.toNatTrans.app (Over.mk i) =
      Functor.Fiber.fiberInclusion.map hcy.inv ≫
        Functor.Fiber.fiberInclusion.map
          (Functor.pullbackFiberHom (p := 𝒴.val.val.p) βEval.hom i) ≫
          Functor.Fiber.fiberInclusion.map cA.hom :=
    Functor.TwoYoneda.twoYonedaEvaluation_app_eq_comp 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids i (objectMorphism B S hS 𝒴.val y).hom
      (a.a ≫ f.hom).hom a.β.hom
  have hαApp : a.α.hom.toNatTrans.app (Over.mk (𝟙 U)) =
      Functor.Fiber.fiberInclusion.map αEval.hom :=
    (Functor.twoYonedaEvaluation_map 𝒳.val.val.p U a.α.hom).symm
  -- the compatibility triangle of the dotted arrow, in the fibre of `𝒴` over `U`
  have hδfib : hδ.hom =
      (hcy.inv ≫ Functor.pullbackFiberHom (p := 𝒴.val.val.p) βEval.hom i ≫ cA.hom) ≫
        (fiberMapOfHom f.hom U).map αEval.hom := by
    apply Functor.Fiber.hom_ext
    rw [hcompat, hβAtI, hαApp]
    exact (fiberInclusion_map_comp_triple_comp hcy.inv
      (Functor.pullbackFiberHom (p := 𝒴.val.val.p) βEval.hom i) cA.hom
      ((fiberMapOfHom f.hom U).map αEval.hom)).symm
  have hδhom : hδ.hom = hcy.inv ≫ Functor.pullbackFiberHom (p := 𝒴.val.val.p) hy.hom i ≫
      γ.inv ≫ (fiberMapOfHom f.hom U).map hx.inv := rfl
  have hkey3 : Functor.pullbackFiberHom (p := 𝒴.val.val.p) hy.hom i ≫
        γ.inv ≫ (fiberMapOfHom f.hom U).map hx.inv =
      Functor.pullbackFiberHom (p := 𝒴.val.val.p) βEval.hom i ≫ cA.hom ≫
        (fiberMapOfHom f.hom U).map αEval.hom := by
    refine (cancel_epi hcy.inv).mp ?_
    rw [← hδhom, hδfib]
    simp only [Category.assoc]
  -- base change along `i` of the two composites of the evaluated `β`
  have h5 : Functor.pullbackFiberHom (p := 𝒴.val.val.p) βEval.inv i ≫
      Functor.pullbackFiberHom (p := 𝒴.val.val.p) βEval.hom i = 𝟙 _ := by
    rw [← Functor.pullbackFiberHom_comp, βEval.inv_hom_id, Functor.pullbackFiberHom_id]
  -- the image of the 2-Yoneda comparison in `𝒳` is the 2-Yoneda comparison of the composite
  have hcore2 : CI.hom ≫ (fiberMapOfHom f.hom U).map hcxA.hom = cA.hom := by
    have t1 : (CatFiberedInGroupoids.homFunctor f.hom).map
          (Functor.Fiber.fiberInclusion.map hcxA.hom) ≫
        (CatFiberedInGroupoids.homFunctor f.hom).map
          (a.a.hom.map (Functor.TwoYoneda.sliceToTerminal i)) =
        (CatFiberedInGroupoids.homFunctor f.hom).map
          (Functor.IsPreFibered.pullbackMap
            ((Functor.twoYonedaEvaluation 𝒳.val.val.p U').obj a.a.hom).2 i) :=
      (Functor.map_comp _ _ _).symm.trans
        (congrArg _ (Functor.fiberIsoOfCartesian_hom_fac i _ _ _ _))
    have t3 : Functor.Fiber.fiberInclusion.map cA.hom ≫
        (a.a ≫ f.hom).hom.map (Functor.TwoYoneda.sliceToTerminal i) =
        Functor.IsPreFibered.pullbackMap
          ((Functor.twoYonedaEvaluation 𝒴.val.val.p U').obj (a.a ≫ f.hom).hom).2 i :=
      Functor.fiberIsoOfCartesian_hom_fac i _ _ _ _
    refine Functor.fiber_hom_ext_of_cartesian i
      ((a.a ≫ f.hom).hom.map (Functor.TwoYoneda.sliceToTerminal i))
      (Functor.TwoYoneda.isCartesian_map_sliceToTerminal 𝒴.val.val.p
        𝒴.val.isFiberedInGroupoids i (a.a ≫ f.hom).hom) _ _ ?_
    exact (congrArg (fun z => z ≫ (a.a ≫ f.hom).hom.map
          (Functor.TwoYoneda.sliceToTerminal i))
        (Functor.map_comp Functor.Fiber.fiberInclusion CI.hom
          ((fiberMapOfHom f.hom U).map hcxA.hom))).trans
      ((comp_three_eq_of_factorisations _ _ _ _ _ t1
        (Functor.fiberIsoOfCartesian_hom_fac i _ _ _ _)).trans t3.symm)
  have hbf : βfs.hom = hcxA.hom ≫ αEval.hom ≫ hx.hom := rfl
  have hg2 : Functor.pullbackFiberHom (p := 𝒴.val.val.p) γfs.hom i =
      Functor.pullbackFiberHom (p := 𝒴.val.val.p) βEval.inv i ≫
        Functor.pullbackFiberHom (p := 𝒴.val.val.p) hy.hom i :=
    Functor.pullbackFiberHom_comp βEval.inv hy.hom i
  rw [hbf, Functor.map_comp, Functor.map_comp, hg2]
  exact comp_eq_of_cancel_iso _ _ _ ((fiberMapOfHom f.hom U).mapIso hx) γ _ _ _ _
    h5 hcore2 hkey3

/-- **Stacks 0DNY.** A 1-morphism of algebraic stacks over `S` is formally smooth exactly when
every infinitesimal lifting diagram for it — the solid diagram 0DNX, i.e. a first-order
thickening of affine objects of the site together with a point of the source over the smaller
one, a point of the target over the larger one and a 2-morphism witnessing 2-commutativity —
admits a dotted arrow, i.e. the category of dotted arrows of Stacks 0H18 for that square is
nonempty. -/
@[stacks 0DNY]
theorem isFormallySmoothOnObjects_iff_nonempty_dottedArrow
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    IsFormallySmoothOnObjects B S hS 𝒳.1 𝒴.1 f.hom ↔
      ∀ d : InfinitesimalLiftingDiagram B S hS 𝒳 𝒴 f,
        Nonempty (DottedArrow d.x d.j f.hom d.y d.γ) :=
  ⟨nonempty_dottedArrow_of_isFormallySmoothOnObjects f,
    isFormallySmoothOnObjects_of_nonempty_dottedArrow f⟩

end AlgebraicGeometry.Stack

end
