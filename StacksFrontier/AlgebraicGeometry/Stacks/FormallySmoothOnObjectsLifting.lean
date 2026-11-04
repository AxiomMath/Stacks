module

public import StacksFrontier.AlgebraicGeometry.Stacks.FormallySmoothOnObjects
public import StacksFrontier.CategoryTheory.FiberedCategory.GrothendieckArrowAttachment

/-!
# Formal smoothness on objects as a lifting problem

`AlgebraicGeometry.Stack.IsFormallySmoothOnObjects` (**Stacks 06D0**) is stated with the
canonical chosen pullbacks of `CategoryTheory.Functor.pullbackFiber` and the comparison
isomorphism `CategoryTheory.Functor.fiberIsoOfCartesian`. That shape is the right one for the
definition but an awkward one to use: a construction that solves a first-order lifting problem
produces an object `x'` over `U'` together with a morphism `x ⟶ x'` lifting `i` and a vertical
identification of its image with `y'`, not a pair of isomorphisms between chosen pullbacks.

This file records the translation between the two shapes, in both directions, and the two-step
reduction it is wanted for: to lift through a composite `p ≫ q` it suffices to lift through `q`
alone, provided `p` is already formally smooth on objects.

## Main results

* `AlgebraicGeometry.Stack.isFormallySmoothOnObjects_iff_exists_homLift`: formal smoothness on
  objects of `p` is equivalent to the lifting property stated with a morphism `x ⟶ x'` over `i`
  and a vertical morphism `p x' ⟶ y'`.
* `AlgebraicGeometry.Stack.isFormallySmoothOnObjects_of_exists_homLift` and
  `AlgebraicGeometry.Stack.exists_homLift_of_isFormallySmoothOnObjects`: the two implications
  separately, which is the form a proof uses.
* `AlgebraicGeometry.Stack.isFormallySmoothOnObjects_comp_of_lifts_through`: if `p` is formally
  smooth on objects and every first-order lifting problem for `p ≫ q` admits a solution already
  over `𝒴`, then `p ≫ q` is formally smooth on objects.

## Implementation notes

The lifting shape asks for `b : x ⟶ x'` with `𝒳.val.p.IsHomLift i b` rather than for an
isomorphism `𝒳.val.p.pullbackFiber x' i ≅ x`. The two are interchangeable because a category
fibred in groupoids has every lift cartesian,
`CategoryTheory.IsFiberedInGroupoids.isStronglyCartesian_homLift`, so `b` and the chosen pullback
map of `x'` along `i` are two cartesian lifts of `i` with the same codomain and
`CategoryTheory.Functor.fiberIsoOfCartesian` turns them into the isomorphism the definition wants.
In the other direction the isomorphism is composed with the chosen pullback map to give `b`.

The vertical identification `c : p x' ⟶ y'` is upgraded to an isomorphism, as the definition
needs, by `CategoryTheory.IsFiberedInGroupoids.fiber_isGroupoid`: a vertical morphism of a
category fibred in groupoids is invertible in its fibre.

In `isFormallySmoothOnObjects_comp_of_lifts_through` the solution over `𝒴` is transported along
`p`'s own lifting property and the two vertical morphisms are composed; that the image under `q`
of a vertical morphism is vertical is `CategoryTheory.Functor.isHomLift_map_of_comp_eq` at
`CategoryTheory.CatFiberedInGroupoids.homFunctor_comp_p`.

No hypothesis of any statement here stands in for a result stated elsewhere: the two
implications of `isFormallySmoothOnObjects_iff_exists_homLift` are converses of one another, and
the `hlift` hypothesis of the composite reduction is the lifting problem that the caller solves.

## References

* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u v w

-- The instance arguments of `CategoryTheory.Functor.IsHomLift` and
-- `CategoryTheory.Functor.IsStronglyCartesian` are only found after unfolding the inclusion of a
-- fibre into the total category, as recorded in
-- `StacksFrontier/CategoryTheory/FiberedCategory/ChoiceOfPullbacks.lean`.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The first-order lifting problem of **Stacks 06D0** written with a morphism of the total
category: for every first-order thickening `i : U ⟶ U'` of affine objects of the site, every
object `x` of `𝒳` over `U`, every object `y'` of `𝒴` over `U'` and every morphism
`a : p x ⟶ y'` lifting `i`, there is an object `x'` of `𝒳` over `U'`, a morphism `b : x ⟶ x'`
lifting `i` and a vertical morphism `c : p x' ⟶ y'` with `p b ≫ c = a`. -/
def HasFirstOrderObjectLifts
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U U' : BigFppfOver B S hS) (i : U ⟶ U'),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj U') →
    IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) →
    ∀ (x : 𝒳.val.p.Fiber U) (y' : 𝒴.val.p.Fiber U')
      (a : (CatFiberedInGroupoids.homFunctor p).obj x.1 ⟶ y'.1),
      𝒴.val.p.IsHomLift i a →
      ∃ (x' : 𝒳.val.p.Fiber U') (b : x.1 ⟶ x'.1)
        (c : (CatFiberedInGroupoids.homFunctor p).obj x'.1 ⟶ y'.1),
        𝒳.val.p.IsHomLift i b ∧ 𝒴.val.p.IsHomLift (𝟙 U') c ∧
        (CatFiberedInGroupoids.homFunctor p).map b ≫ c = a

/-- Solving every first-order lifting problem in the shape of
`AlgebraicGeometry.Stack.HasFirstOrderObjectLifts` makes a 1-morphism formally smooth on
objects. -/
theorem isFormallySmoothOnObjects_of_exists_homLift
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hlift : HasFirstOrderObjectLifts B S hS p) :
    IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p := by
  let : 𝒳.val.p.IsFiberedInGroupoids := 𝒳.isFiberedInGroupoids
  let : 𝒴.val.p.IsFiberedInGroupoids := 𝒴.isFiberedInGroupoids
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let F := CatFiberedInGroupoids.homFunctor p
  let pU := fun U => Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p F
    (CatFiberedInGroupoids.homFunctor_comp_p p) U
  intro U U' i hU hU' hi x y' γ
  let a : F.obj x.1 ⟶ y'.1 :=
    Functor.Fiber.fiberInclusion.map γ.hom ≫ Functor.IsPreFibered.pullbackMap y'.2 i
  have ha : 𝒴.val.p.IsHomLift i a := by
    have := γ.hom.2
    exact IsHomLift.comp_lift_id_left 𝒴.val.p i
      (Functor.IsPreFibered.pullbackMap y'.2 i) (Functor.Fiber.fiberInclusion.map γ.hom)
  obtain ⟨x', b, c, hb, hc, he⟩ := hlift U U' i hU hU' hi x y' a ha
  have hb_cart : 𝒳.val.p.IsCartesian i b := by
    have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift i b
    infer_instance
  let β : 𝒳.val.p.pullbackFiber x' i ≅ x :=
    Functor.fiberIsoOfCartesian i (Functor.IsPreFibered.pullbackMap x'.2 i)
      b (by infer_instance) hb_cart
  let c₀ : (pU U').obj x' ⟶ y' := ⟨c, hc⟩
  let := 𝒴.isFiberedInGroupoids.fiber_isGroupoid U'
  let γ' := asIso c₀
  refine ⟨x', β, γ', ?_⟩
  apply Functor.pullbackFiberHom_uniq
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.Fiber.fiberInclusion_map_mapOfComp_map]
  dsimp only [γ', asIso, c₀]
  show _ ≫ F.map (Functor.Fiber.fiberInclusion.map β.hom) ≫ a = _ ≫ c
  rw [← he]
  have hβ : Functor.Fiber.fiberInclusion.map β.hom ≫ b =
      Functor.IsPreFibered.pullbackMap x'.2 i :=
    Functor.fiberIsoOfCartesian_hom_fac i _ b _ hb_cart
  show _ ≫ F.map (Functor.Fiber.fiberInclusion.map β.hom) ≫ F.map b ≫ c = _
  rw [← Category.assoc (F.map (Functor.Fiber.fiberInclusion.map β.hom)) (F.map b) c,
    ← F.map_comp, hβ]
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun k => k ≫ c) (Functor.fiberIsoOfCartesian_hom_fac i _ _ _ _)

/-- The identification of chosen pullbacks in `IsFormallySmoothOnObjects` turns into the
factorization `p b ≫ c = a` of `HasFirstOrderObjectLifts`, with `b` the inverse of `β` followed
by the chosen pullback map of `x'` and `c` the vertical morphism underlying `γ'`. -/
theorem homFunctor_map_comp_eq_of_pullbackFiberHom_eq
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    [𝒳.val.p.IsFibered] [𝒴.val.p.IsFibered] {U U' : BigFppfOver B S hS} (i : U ⟶ U')
    {x : 𝒳.val.p.Fiber U} {x' : 𝒳.val.p.Fiber U'} {y' : 𝒴.val.p.Fiber U'}
    (a : (CatFiberedInGroupoids.homFunctor p).obj x.1 ⟶ y'.1)
    (β : 𝒳.val.p.pullbackFiber x' i ≅ x)
    (γ : (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor p)
      (CatFiberedInGroupoids.homFunctor_comp_p p) U).obj x ≅ 𝒴.val.p.pullbackFiber y' i)
    (γ' : (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor p)
      (CatFiberedInGroupoids.homFunctor_comp_p p) U').obj x' ≅ y')
    (δ : 𝒴.val.p.pullbackFiber ((Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor_comp_p p) U').obj
          x') i ≅
      (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor p)
        (CatFiberedInGroupoids.homFunctor_comp_p p) U).obj (𝒳.val.p.pullbackFiber x' i))
    (hγ : Functor.Fiber.fiberInclusion.map γ.hom ≫ Functor.IsPreFibered.pullbackMap y'.2 i = a)
    (hδ : Functor.Fiber.fiberInclusion.map δ.hom ≫
        (CatFiberedInGroupoids.homFunctor p).map (Functor.IsPreFibered.pullbackMap x'.2 i) =
      Functor.IsPreFibered.pullbackMap ((Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor_comp_p p) U').obj
          x').2 i)
    (h : (δ.hom ≫ (Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor p)
      (CatFiberedInGroupoids.homFunctor_comp_p p) U).map β.hom) ≫ γ.hom =
        Functor.pullbackFiberHom γ'.hom i) :
    (CatFiberedInGroupoids.homFunctor p).map (Functor.Fiber.fiberInclusion.map β.inv ≫
      Functor.IsPreFibered.pullbackMap x'.2 i) ≫ Functor.Fiber.fiberInclusion.map γ'.hom = a := by
  subst hγ
  let F := CatFiberedInGroupoids.homFunctor p
  have h₁ := congrArg (fun k => Functor.Fiber.fiberInclusion.map k ≫
    Functor.IsPreFibered.pullbackMap y'.2 i) h
  simp only [Functor.map_comp, Category.assoc, Functor.pullbackFiberHom_fac,
    Functor.Fiber.fiberInclusion_map_mapOfComp_map] at h₁
  have h₂ : F.map (Functor.IsPreFibered.pullbackMap x'.2 i) ≫
      Functor.Fiber.fiberInclusion.map γ'.hom =
      F.map (Functor.Fiber.fiberInclusion.map β.hom) ≫ Functor.Fiber.fiberInclusion.map γ.hom ≫
        Functor.IsPreFibered.pullbackMap y'.2 i :=
    (cancel_epi (Functor.Fiber.fiberInclusion.map δ.hom)).mp <| (Category.assoc _ _ _).symm.trans <|
      (congrArg (fun k => k ≫ _) hδ).trans <| h₁.symm.trans <|
        congrArg (_ ≫ ·) (Category.assoc _ _ _)
  let b : x.1 ⟶ x'.1 := Functor.Fiber.fiberInclusion.map β.inv ≫
    Functor.IsPreFibered.pullbackMap x'.2 i
  let c : F.obj x'.1 ⟶ y'.1 := Functor.Fiber.fiberInclusion.map γ'.hom
  show F.map b ≫ c = _
  rw [F.map_comp, Category.assoc, h₂, ← Category.assoc, ← F.map_comp,
    ← Functor.map_comp, β.inv_hom_id, CategoryTheory.Functor.map_id]
  exact (congrArg (fun f => f ≫ _) (F.map_id x.1)).trans (Category.id_comp _)

/-- A 1-morphism formally smooth on objects solves every first-order lifting problem in the
shape of `AlgebraicGeometry.Stack.HasFirstOrderObjectLifts`. -/
theorem exists_homLift_of_isFormallySmoothOnObjects
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hp : IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p) :
    HasFirstOrderObjectLifts B S hS p := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let F := CatFiberedInGroupoids.homFunctor p
  let pU := fun U => Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p F
    (CatFiberedInGroupoids.homFunctor_comp_p p) U
  intro U U' i hU hU' hi x y' a ha
  have hac : 𝒴.val.p.IsCartesian i a := by
    have := 𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift i a
    infer_instance
  let γ : (pU U).obj x ≅ 𝒴.val.p.pullbackFiber y' i :=
    Functor.fiberIsoOfCartesian i a (Functor.IsPreFibered.pullbackMap y'.2 i)
      hac (by infer_instance)
  obtain ⟨x', β, γ', h⟩ := hp U U' i hU hU' hi x y' γ
  let b : x.1 ⟶ x'.1 := Functor.Fiber.fiberInclusion.map β.inv ≫
    Functor.IsPreFibered.pullbackMap x'.2 i
  let c : F.obj x'.1 ⟶ y'.1 := Functor.Fiber.fiberInclusion.map γ'.hom
  have hb : 𝒳.val.p.IsHomLift i b := by
    have := β.inv.2
    infer_instance
  have hc : 𝒴.val.p.IsHomLift (𝟙 U') c := γ'.hom.2
  refine ⟨x', b, c, hb, hc, ?_⟩
  have hcart : 𝒴.val.p.IsCartesian i
      (F.map (Functor.IsPreFibered.pullbackMap x'.2 i)) := by
    have := CatFiberedInGroupoids.isStronglyCartesian_map p i
      (Functor.IsPreFibered.pullbackMap x'.2 i)
    infer_instance
  let δ : 𝒴.val.p.pullbackFiber ((pU U').obj x') i ≅
      (pU U).obj (𝒳.val.p.pullbackFiber x' i) :=
    Functor.fiberIsoOfCartesian (p := 𝒴.val.p) i
      (Functor.IsPreFibered.pullbackMap ((pU U').obj x').2 i)
      (F.map (Functor.IsPreFibered.pullbackMap x'.2 i)) (by infer_instance) hcart
  change (δ.hom ≫ (pU U).map β.hom) ≫ γ.hom =
    Functor.pullbackFiberHom γ'.hom i at h
  exact homFunctor_map_comp_eq_of_pullbackFiberHom_eq B S hS p i a β γ γ' δ
    (Functor.fiberIsoOfCartesian_hom_fac i _ _ _ _)
    (Functor.fiberIsoOfCartesian_hom_fac i _ _ _ hcart) h

/-- **Stacks 06D0 as a lifting problem.** A 1-morphism of categories fibred in groupoids over
the big fppf site is formally smooth on objects exactly when every first-order lifting problem
over an affine thickening has a solution given by a morphism of the total category over the
thickening together with a vertical identification downstairs. -/
theorem isFormallySmoothOnObjects_iff_exists_homLift
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴) :
    IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p ↔ HasFirstOrderObjectLifts B S hS p :=
  ⟨exists_homLift_of_isFormallySmoothOnObjects B S hS p,
    isFormallySmoothOnObjects_of_exists_homLift B S hS p⟩

/-- If `p : 𝒳 ⟶ 𝒴` is formally smooth on objects and every first-order lifting problem for the
composite `p ≫ q` can be solved already over `𝒴` — that is, the lift of the object is asked for
in `𝒴` rather than in `𝒳` — then `p ≫ q` is formally smooth on objects.

This is the step that reduces a lifting problem for a 1-morphism factored through an open
substack to one for the second factor: the first factor contributes nothing beyond its own
formal smoothness. -/
theorem isFormallySmoothOnObjects_comp_of_lifts_through
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (p : 𝒳 ⟶ 𝒴) (q : 𝒴 ⟶ 𝒵)
    (hp : IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p)
    (hlift : ∀ (U U' : BigFppfOver B S hS) (i : U ⟶ U'),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj U') →
      IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) →
      ∀ (x : 𝒳.val.p.Fiber U) (z' : 𝒵.val.p.Fiber U')
        (a : (CatFiberedInGroupoids.homFunctor (p ≫ q)).obj x.1 ⟶ z'.1),
        𝒵.val.p.IsHomLift i a →
        ∃ (y' : 𝒴.val.p.Fiber U')
          (b : (CatFiberedInGroupoids.homFunctor p).obj x.1 ⟶ y'.1)
          (c : (CatFiberedInGroupoids.homFunctor q).obj y'.1 ⟶ z'.1),
          𝒴.val.p.IsHomLift i b ∧ 𝒵.val.p.IsHomLift (𝟙 U') c ∧
          (CatFiberedInGroupoids.homFunctor q).map b ≫ c = a) :
    IsFormallySmoothOnObjects B S hS 𝒳 𝒵 (p ≫ q) := by
  apply isFormallySmoothOnObjects_of_exists_homLift B S hS
  intro U U' i hU hU' hi x z' a ha
  obtain ⟨y', b, c, hb, hc, hbc⟩ := hlift U U' i hU hU' hi x z' a ha
  obtain ⟨x', b', c', hb', hc', hbc'⟩ :=
    exists_homLift_of_isFormallySmoothOnObjects B S hS p hp U U' i hU hU' hi x y' b hb
  let Q := CatFiberedInGroupoids.homFunctor q
  refine ⟨x', b', Q.map c' ≫ c, hb', ?_, ?_⟩
  · have : 𝒵.val.p.IsHomLift (𝟙 U') (Q.map c') :=
      Functor.isHomLift_map_of_comp_eq
        (CatFiberedInGroupoids.homFunctor_comp_p q) (𝟙 U') c'
    exact IsHomLift.comp_lift_id_right 𝒵.val.p (𝟙 U') (Q.map c') c
  · show Q.map ((CatFiberedInGroupoids.homFunctor p).map b') ≫ Q.map c' ≫ c = a
    rwa [← Category.assoc, ← Q.map_comp, hbc']

end AlgebraicGeometry.Stack

end
