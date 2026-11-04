module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong
import all StacksFrontier.Deformation.Artin.ChangeOfField.Equivalence

/-!
# The comparison of a square of fibres from any restriction equivalence

Let `q : 𝒴 ⥤ 𝒞` be fibred in groupoids and let

```text
  U --f--> V
  |g       |i
  v        v
  W --j--> Z
```

be a commutative square of `𝒞`. The Rim–Schlessinger conditions (Stacks 07WP, 07Y8) ask that the
comparison `Deformation.Artin.fiberSquareComparison` from the fibre over `Z` to the two-fibre
product of the fibres over `V` and `W` be an equivalence; that comparison is built from a choice
of pullbacks. Moduli problems usually come with *their own* base-change functors — restriction of
families along a morphism of bases — and prove the gluing statement for those. This file shows
that this is enough: if restriction along the four sides of the square is given by any functors
together with their natural cartesian comparisons, and the restriction functor from the fibre
over `Z` to the two-fibre product of *those* functors is an equivalence compatibly with the
comparisons, then the canonical comparison is an equivalence.

## Main definitions

* `Deformation.Artin.FiberBaseChange`: a base-change functor between two fibres of `q` along a
  morphism of `𝒞`, with its natural comparison to the identity lying over that morphism.
* `Deformation.Artin.FiberBaseChange.isoPullbackFunctor`: such a functor is canonically
  isomorphic to the pullback functor of any choice of pullbacks.
* `Deformation.Artin.catPullbackMap`: the functor between categorical pullbacks induced by
  isomorphisms of their legs, which is an equivalence.

## Main results

* `Deformation.Artin.isEquivalence_fiberSquareComparison_of_restriction`: the comparison of a
  square of fibres is an equivalence as soon as a restriction functor built from any base-change
  functors is, compatibly with the comparisons.

## Implementation notes

Every identity between morphisms of a fibre is proved by composing with a cartesian morphism out
of the common target (`CategoryTheory.Functor.fiber_hom_ext_of_cartesian`); in a category fibred
in groupoids every morphism is cartesian over its image.

## References

* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace Deformation.Artin

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoryTheory.Limits.CategoricalPullback.π₁
  CategoryTheory.Limits.CategoricalPullback.π₂

universe v₁ v₂ v₃ u₁ u₂ u₃

section CatPullback

variable {A₁ : Type u₁} {B₁ : Type u₂} {C₁ : Type u₃}
  [Category.{v₁} A₁] [Category.{v₂} B₁] [Category.{v₃} C₁]
  {F F' : A₁ ⥤ B₁} {G G' : C₁ ⥤ B₁}

/-- The functor between categorical pullbacks induced by isomorphisms of their two legs: it is
the identity on the two components and conjugates the structural isomorphism. -/
@[simps]
def catPullbackMap (μ : F ≅ F') (ν : G ≅ G') :
    CategoricalPullback F G ⥤ CategoricalPullback F' G' where
  obj x := ⟨x.fst, x.snd, μ.symm.app x.fst ≪≫ x.iso ≪≫ ν.app x.snd⟩
  map φ := ⟨φ.fst, φ.snd, by simp⟩

attribute [local implicit_reducible] catPullbackMap

/-- `Deformation.Artin.catPullbackMap` is faithful: it is the identity on components. -/
instance (μ : F ≅ F') (ν : G ≅ G') : (catPullbackMap μ ν).Faithful :=
  ⟨fun h => CategoricalPullback.hom_ext (congrArg (fun φ => φ.fst) h)
    (congrArg (fun φ => φ.snd) h)⟩

/-- `Deformation.Artin.catPullbackMap` is full: a compatible pair for the conjugated structural
isomorphisms is compatible for the original ones. -/
instance (μ : F ≅ F') (ν : G ≅ G') : (catPullbackMap μ ν).Full := by
  refine ⟨fun {x y} φ => ?_⟩
  let a : x.fst ⟶ y.fst := φ.fst
  let b : x.snd ⟶ y.snd := φ.snd
  have hw : F'.map a ≫ μ.inv.app y.fst ≫ y.iso.hom ≫ ν.hom.app y.snd =
      (μ.inv.app x.fst ≫ x.iso.hom ≫ ν.hom.app x.snd) ≫ G'.map b := φ.w
  have h : F.map a ≫ y.iso.hom = x.iso.hom ≫ G.map b := by
    have h₁ : F'.map a ≫ μ.inv.app y.fst = μ.inv.app x.fst ≫ F.map a :=
      μ.inv.naturality a
    have h₂ : ν.hom.app x.snd ≫ G'.map b = G.map b ≫ ν.hom.app y.snd :=
      (ν.hom.naturality b).symm
    rw [← Category.assoc, h₁, Category.assoc, Category.assoc, Category.assoc, h₂] at hw
    refine (cancel_epi (μ.inv.app x.fst)).1 ((cancel_mono (ν.hom.app y.snd)).1 ?_)
    simpa only [Category.assoc] using hw
  exact ⟨⟨a, b, h⟩, rfl⟩

/-- `Deformation.Artin.catPullbackMap` is essentially surjective: conjugate back. -/
instance (μ : F ≅ F') (ν : G ≅ G') : (catPullbackMap μ ν).EssSurj := by
  refine ⟨fun y => ⟨⟨y.fst, y.snd, μ.app y.fst ≪≫ y.iso ≪≫ ν.symm.app y.snd⟩,
    ⟨CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) ?_⟩⟩⟩
  change F'.map (𝟙 y.fst) ≫ y.iso.hom =
    (μ.inv.app y.fst ≫ (μ.hom.app y.fst ≫ y.iso.hom ≫ ν.inv.app y.snd) ≫ ν.hom.app y.snd) ≫
      G'.map (𝟙 y.snd)
  simp

/-- `Deformation.Artin.catPullbackMap` is an equivalence. -/
instance (μ : F ≅ F') (ν : G ≅ G') : (catPullbackMap μ ν).IsEquivalence where

end CatPullback

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒴 : Type u₂} [Category.{v₂} 𝒴] (q : 𝒴 ⥤ 𝒞)

/-- A *base-change functor* along `e : A ⟶ A'`: a functor from the fibre of `q` over `A'` to the
fibre over `A`, with a natural comparison from the base change of an object to the object which
lies over `e`. -/
structure FiberBaseChange {A A' : 𝒞} (e : A ⟶ A') where
  /-- The base-change functor. -/
  functor : q.Fiber A' ⥤ q.Fiber A
  /-- The comparison from a base change to the object it is a base change of. -/
  comparison : functor ⋙ Fiber.fiberInclusion ⟶ Fiber.fiberInclusion
  /-- The comparison lies over `e`. -/
  comparison_isHomLift (x : q.Fiber A') : q.IsHomLift e (comparison.app x)

namespace FiberBaseChange

variable {q} {A A' : 𝒞} {e : A ⟶ A'} (F : FiberBaseChange q e)
  (c : q.ChoiceOfPullbacks)

/-- In a category fibred in groupoids the comparison of a base-change functor is cartesian. -/
theorem comparison_isCartesian (hq : q.IsFiberedInGroupoids) (x : q.Fiber A') :
    q.IsCartesian e (F.comparison.app x) :=
  have := F.comparison_isHomLift x
  (hq.isStronglyCartesian_homLift e _).isCartesian_of_isStronglyCartesian

/-- A base-change functor is canonically isomorphic to the pullback functor of a choice of
pullbacks: both send an object to the source of a cartesian morphism into it over `e`. -/
def isoPullbackFunctor (hq : q.IsFiberedInGroupoids) : F.functor ≅ c.pullbackFunctor e :=
  NatIso.ofComponents
    (fun x => fiberIsoOfCartesian e (F.comparison.app x) (c.map e x)
      (F.comparison_isCartesian hq x)
      (c.isStronglyCartesian e x).isCartesian_of_isStronglyCartesian)
    (fun {x x'} α => by
      apply fiber_hom_ext_of_cartesian e (c.map e x')
        (c.isStronglyCartesian e x').isCartesian_of_isStronglyCartesian
      change Fiber.fiberInclusion.map (F.functor.map α ≫ _) ≫ c.map e x' =
        Fiber.fiberInclusion.map (_ ≫ c.homMap e α) ≫ c.map e x'
      rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        fiberIsoOfCartesian_hom_fac, ChoiceOfPullbacks.homMap_fac,
        fiberIsoOfCartesian_hom_fac_assoc]
      exact F.comparison.naturality α)

/-- The comparison isomorphism carries the chosen cartesian lift to the given comparison. -/
@[reassoc (attr := simp)]
theorem isoPullbackFunctor_hom_app_fac (hq : q.IsFiberedInGroupoids) (x : q.Fiber A') :
    Fiber.fiberInclusion.map ((F.isoPullbackFunctor c hq).hom.app x) ≫ c.map e x =
      F.comparison.app x :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- The inverse comparison isomorphism carries the given comparison to the chosen cartesian
lift. -/
@[reassoc (attr := simp)]
theorem isoPullbackFunctor_inv_app_fac (hq : q.IsFiberedInGroupoids) (x : q.Fiber A') :
    Fiber.fiberInclusion.map ((F.isoPullbackFunctor c hq).inv.app x) ≫ F.comparison.app x =
      c.map e x :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- Pulling back along `f` a morphism into a base change, followed by the chosen cartesian
lifts, is the chosen lift along `f` followed by the morphism and the comparison. -/
private theorem homMap_isoPullbackFunctor_hom_app_fac (hq : q.IsFiberedInGroupoids) {U : 𝒞}
    (f : U ⟶ A) {s : q.Fiber A'} {y : q.Fiber A} (ρ : y ⟶ F.functor.obj s) :
    Fiber.fiberInclusion.map (c.homMap f (ρ ≫ (F.isoPullbackFunctor c hq).hom.app s)) ≫
        c.map f (c.obj e s) ≫ c.map e s =
      c.map f y ≫ Fiber.fiberInclusion.map ρ ≫ F.comparison.app s := by
  refine (c.homMap_fac_assoc f _ _).trans ?_
  rw [Functor.map_comp, Category.assoc, F.isoPullbackFunctor_hom_app_fac]

end FiberBaseChange

/-- The compatibility of the structural isomorphisms needed to compare the canonical
comparison of a square of fibres with a restriction functor, after the chosen cartesian lifts
to the fourth corner. -/
private theorem fiberSquareComparison_iso_fac_of_restriction
    (hq : q.IsFiberedInGroupoids) (c : q.ChoiceOfPullbacks)
    {U V W Z : 𝒞} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (w : f ≫ i = g ≫ j)
    (Ff : FiberBaseChange q f) (Fg : FiberBaseChange q g)
    (Fi : FiberBaseChange q i) (Fj : FiberBaseChange q j)
    (θ : Fi.functor ⋙ Ff.functor ≅ Fj.functor ⋙ Fg.functor)
    (hθ : ∀ s : q.Fiber Z, Fiber.fiberInclusion.map (θ.hom.app s) ≫
      Fg.comparison.app (Fj.functor.obj s) ≫ Fj.comparison.app s =
        Ff.comparison.app (Fi.functor.obj s) ≫ Fi.comparison.app s)
    (R : q.Fiber Z ⥤ CategoricalPullback Ff.functor Fg.functor)
    (ρ₁ : R ⋙ CategoricalPullback.π₁ _ _ ≅ Fi.functor)
    (ρ₂ : R ⋙ CategoricalPullback.π₂ _ _ ≅ Fj.functor)
    (hρ : ∀ s : q.Fiber Z, Ff.functor.map (ρ₁.hom.app s) ≫ θ.hom.app s =
      (R.obj s).iso.hom ≫ Fg.functor.map (ρ₂.hom.app s)) (s : q.Fiber Z) :
    Fiber.fiberInclusion.map (c.homMap f (ρ₁.hom.app s ≫ (Fi.isoPullbackFunctor c hq).hom.app s) ≫
        ((fiberSquareComparison q c f g i j w).obj s).iso.hom) ≫
        c.map g (c.obj j s) ≫ c.map j s =
      Fiber.fiberInclusion.map (((Ff.isoPullbackFunctor c hq).inv.app (R.obj s).fst ≫
        (R.obj s).iso.hom ≫ (Fg.isoPullbackFunctor c hq).hom.app (R.obj s).snd) ≫
          c.homMap g (ρ₂.hom.app s ≫ (Fj.isoPullbackFunctor c hq).hom.app s)) ≫
        c.map g (c.obj j s) ≫ c.map j s := by
  have h₁ : Fiber.fiberInclusion.map ((fiberSquareComparison q c f g i j w).obj s).iso.hom ≫
      c.map g (c.obj j s) ≫ c.map j s = c.map f (c.obj i s) ≫ c.map i s :=
    fiberSquareComparison_iso_fac q c f g i j w s
  have h₂ : Fiber.fiberInclusion.map (R.obj s).iso.hom ≫
      Fiber.fiberInclusion.map (Fg.functor.map (ρ₂.hom.app s)) ≫
        Fg.comparison.app (Fj.functor.obj s) ≫ Fj.comparison.app s =
      Fiber.fiberInclusion.map (Ff.functor.map (ρ₁.hom.app s)) ≫
        Ff.comparison.app (Fi.functor.obj s) ≫ Fi.comparison.app s := by
    rw [← hθ s, ← Category.assoc, ← Functor.map_comp, ← hρ s, Functor.map_comp, Category.assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [h₁, Fi.homMap_isoPullbackFunctor_hom_app_fac c hq f,
    Fj.homMap_isoPullbackFunctor_hom_app_fac c hq g,
    FiberBaseChange.isoPullbackFunctor_hom_app_fac_assoc,
    ← FiberBaseChange.isoPullbackFunctor_inv_app_fac Ff c hq, Category.assoc,
    ← Ff.comparison.naturality_assoc, ← Fg.comparison.naturality_assoc, Functor.comp_map,
    Functor.comp_map, h₂]
  rfl

/-- **The canonical comparison of a square of fibres from a restriction equivalence.** Let
`Ff`, `Fg`, `Fi`, `Fj` be base-change functors along the four sides of a commutative square of
`𝒞`, let `θ` identify the two base changes from the fourth corner to the first, compatibly with
the comparisons, and let `R` be a functor from the fibre over the fourth corner to the two-fibre
product of `Ff` and `Fg` whose two projections are `Fi` and `Fj`, compatibly with `θ`. If `R` is
an equivalence, then so is the canonical comparison `Deformation.Artin.fiberSquareComparison`
of any choice of pullbacks. -/
theorem isEquivalence_fiberSquareComparison_of_restriction
    (hq : q.IsFiberedInGroupoids) (c : q.ChoiceOfPullbacks)
    {U V W Z : 𝒞} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (w : f ≫ i = g ≫ j)
    (Ff : FiberBaseChange q f) (Fg : FiberBaseChange q g)
    (Fi : FiberBaseChange q i) (Fj : FiberBaseChange q j)
    (θ : Fi.functor ⋙ Ff.functor ≅ Fj.functor ⋙ Fg.functor)
    (hθ : ∀ s : q.Fiber Z, Fiber.fiberInclusion.map (θ.hom.app s) ≫
      Fg.comparison.app (Fj.functor.obj s) ≫ Fj.comparison.app s =
        Ff.comparison.app (Fi.functor.obj s) ≫ Fi.comparison.app s)
    (R : q.Fiber Z ⥤ CategoricalPullback Ff.functor Fg.functor) [R.IsEquivalence]
    (ρ₁ : R ⋙ CategoricalPullback.π₁ _ _ ≅ Fi.functor)
    (ρ₂ : R ⋙ CategoricalPullback.π₂ _ _ ≅ Fj.functor)
    (hρ : ∀ s : q.Fiber Z, Ff.functor.map (ρ₁.hom.app s) ≫ θ.hom.app s =
      (R.obj s).iso.hom ≫ Fg.functor.map (ρ₂.hom.app s)) :
    (fiberSquareComparison q c f g i j w).IsEquivalence := by
  let νi := Fi.isoPullbackFunctor c hq
  let νj := Fj.isoPullbackFunctor c hq
  have hcart (s : q.Fiber Z) : q.IsCartesian (g ≫ j) (c.map g (c.obj j s) ≫ c.map j s) :=
    (hq.isStronglyCartesian_homLift (g ≫ j) _).isCartesian_of_isStronglyCartesian
  let e : R ⋙ catPullbackMap (Ff.isoPullbackFunctor c hq) (Fg.isoPullbackFunctor c hq) ≅
      fiberSquareComparison q c f g i j w :=
    NatIso.ofComponents
      (fun s => CategoricalPullback.mkIso ((ρ₁ ≪≫ νi).app s) ((ρ₂ ≪≫ νj).app s) (by
        apply fiber_hom_ext_of_cartesian (g ≫ j) _ (hcart s)
        exact fiberSquareComparison_iso_fac_of_restriction q hq c f g i j w Ff Fg Fi Fj θ hθ R
          ρ₁ ρ₂ hρ s))
      (fun α => by
        apply CategoricalPullback.hom_ext
        · exact (ρ₁ ≪≫ νi).hom.naturality α
        · exact (ρ₂ ≪≫ νj).hom.naturality α)
  exact Functor.isEquivalence_of_iso e

end Deformation.Artin

end
