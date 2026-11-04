module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberHom

/-!
# The chosen pullback of a chosen pullback

The chosen pullback of `f^* y` along `ε` is a cartesian lift of `ε ≫ f` at `y`, hence canonically
isomorphic to the chosen pullback along the composite. The comparison is taken along a *named*
morphism equal to `ε ≫ f` (`CategoryTheory.Functor.pullbackFiberCompIso'`) so that its target can
be the chosen pullback along a morphism given by other means, with
`CategoryTheory.Functor.pullbackFiberCompIso` the case of the composite itself.

## Main definitions

* `CategoryTheory.Functor.pullbackFiberIdIso`, the chosen pullback along an identity;
* `CategoryTheory.Functor.pullbackFiberCompIso'` and
  `CategoryTheory.Functor.pullbackFiberCompIso`, the contraction of an iterated chosen pullback;
* `CategoryTheory.Functor.pullbackFiberComparison`, the comparison of the chosen pullbacks along
  two morphisms with a common further pullback.

## Main results

* `CategoryTheory.Functor.pullbackFiberCompIso'_pentagon` and
  `CategoryTheory.Functor.pullbackFiberCompIso_pentagon`, that contracting a threefold iterated
  chosen pullback in either order agrees.
-/

@[expose] public section

-- Needed throughout: the transfer lemmas below relate `p` and `P.ι ⋙ p`, and the instance
-- arguments of `IsHomLift` and `IsCartesian` are only found after unfolding the composite.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {W : 𝒮} {y y' : p.Fiber W} {Z : 𝒮}

/-- Pulling back along an isomorphism of the base is injective on morphisms of the fibre. -/
lemma eq_of_pullbackFiberHom_eq (α β : y ⟶ y') (b : Z ⟶ W) [IsIso b]
    (h : pullbackFiberHom α b = pullbackFiberHom β b) : α = β := by
  have : p.IsCartesian b (IsPreFibered.pullbackMap y.2 b) :=
    IsPreFibered.pullbackMap.IsCartesian y.2 b
  have : p.IsStronglyCartesian b (IsPreFibered.pullbackMap y.2 b) := inferInstance
  have : IsIso (IsPreFibered.pullbackMap y.2 b) :=
    IsStronglyCartesian.isIso_of_base_isIso p b _
  refine Fiber.hom_ext ?_
  rw [← cancel_epi (IsPreFibered.pullbackMap y.2 b), ← pullbackFiberHom_fac α b,
    ← pullbackFiberHom_fac β b, h]

/-- The chosen pullback along an identity is canonically isomorphic, in the fibre, to the object
itself. -/
noncomputable def pullbackFiberIdIso {T : 𝒮} (y : p.Fiber T) :
    pullbackFiber p y (𝟙 T) ≅ y :=
  have : p.IsHomLift (𝟙 T) (𝟙 y.1) := IsHomLift.id y.2
  fiberIsoOfCartesian (𝟙 T) (IsPreFibered.pullbackMap y.2 (𝟙 T)) (𝟙 y.1)
    (IsPreFibered.pullbackMap.IsCartesian _ _) inferInstance

/-- The chosen cartesian lift of a chosen pullback of a chosen pullback, over a named morphism that
the composite equals. -/
lemma isCartesian_pullbackMap_comp_pullbackMap {T V Z : 𝒮} (y : p.Fiber T) (f : V ⟶ T) (ε : Z ⟶ V)
    (b : Z ⟶ T) (h : ε ≫ f = b) :
    p.IsCartesian b
      (IsPreFibered.pullbackMap (pullbackFiber p y f).2 ε ≫ IsPreFibered.pullbackMap y.2 f) := by
  subst h
  infer_instance

/-- The chosen pullback of a chosen pullback is canonically isomorphic, in the fibre, to the
chosen pullback along a *named* morphism that the composite equals. -/
noncomputable def pullbackFiberCompIso' {T V Z : 𝒮} (y : p.Fiber T) (f : V ⟶ T) (ε : Z ⟶ V)
    (b : Z ⟶ T) (h : ε ≫ f = b) :
    pullbackFiber p (pullbackFiber p y f) ε ≅ pullbackFiber p y b :=
  fiberIsoOfCartesian b
    (IsPreFibered.pullbackMap (pullbackFiber p y f).2 ε ≫ IsPreFibered.pullbackMap y.2 f)
    (IsPreFibered.pullbackMap y.2 b) (isCartesian_pullbackMap_comp_pullbackMap y f ε b h)
    (IsPreFibered.pullbackMap.IsCartesian _ _)

/-- `pullbackFiberCompIso'` is compatible with the lifts it compares: followed by the chosen
cartesian lift of `b` it is the composite of the two chosen lifts of `ε` and `f`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberCompIso'_hom_fac {T V Z : 𝒮} (y : p.Fiber T) (f : V ⟶ T) (ε : Z ⟶ V)
    (b : Z ⟶ T) (h : ε ≫ f = b) :
    Fiber.fiberInclusion.map (pullbackFiberCompIso' y f ε b h).hom ≫
        IsPreFibered.pullbackMap y.2 b =
      IsPreFibered.pullbackMap (pullbackFiber p y f).2 ε ≫ IsPreFibered.pullbackMap y.2 f :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- The inverse of `pullbackFiberCompIso'`, followed by the composite of the chosen cartesian
lifts of `ε` and `f`, is the chosen cartesian lift of `b`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberCompIso'_inv_fac {T V Z : 𝒮} (y : p.Fiber T) (f : V ⟶ T) (ε : Z ⟶ V)
    (b : Z ⟶ T) (h : ε ≫ f = b) :
    Fiber.fiberInclusion.map (pullbackFiberCompIso' y f ε b h).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p y f).2 ε ≫ IsPreFibered.pullbackMap y.2 f =
      IsPreFibered.pullbackMap y.2 b :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- Contracting a threefold chosen pullback from the inside and from the outside agree. -/
lemma pullbackFiberCompIso'_pentagon {T V W Z : 𝒮} (y : p.Fiber T) (f : V ⟶ T) (ε : W ⟶ V)
    (γ : Z ⟶ W) (b : W ⟶ T) (hb : ε ≫ f = b) (m : Z ⟶ V) (hm : γ ≫ ε = m) (c : Z ⟶ T)
    (hc : m ≫ f = c) :
    pullbackFiberHom (pullbackFiberCompIso' y f ε b hb).hom γ ≫
        (pullbackFiberCompIso' y b γ c (by rw [← hb, ← hc, ← hm, Category.assoc])).hom =
      (pullbackFiberCompIso' (pullbackFiber p y f) ε γ m hm).hom ≫
        (pullbackFiberCompIso' y f m c hc).hom := by
  refine fiber_hom_ext_of_cartesian c (IsPreFibered.pullbackMap y.2 c)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp [Functor.map_comp, Category.assoc, pullbackFiberCompIso'_hom_fac,
    pullbackFiberCompIso'_hom_fac_assoc, pullbackFiberHom_fac_assoc]

/-- The chosen pullback of a chosen pullback is canonically isomorphic, in the fibre, to the chosen
pullback along the composite. -/
noncomputable def pullbackFiberCompIso {T V Z : 𝒮} (y : p.Fiber T) (f : V ⟶ T)
    (ε : Z ⟶ V) : pullbackFiber p (pullbackFiber p y f) ε ≅ pullbackFiber p y (ε ≫ f) :=
  pullbackFiberCompIso' y f ε (ε ≫ f) rfl

/-- `pullbackFiberCompIso'` at the composite itself is `pullbackFiberCompIso`. -/
@[simp]
lemma pullbackFiberCompIso'_rfl {T V Z : 𝒮} (y : p.Fiber T) (f : V ⟶ T) (ε : Z ⟶ V) :
    pullbackFiberCompIso' y f ε (ε ≫ f) rfl = pullbackFiberCompIso y f ε := rfl

/-- The forward direction of `pullbackFiberIdIso`, seen in `𝒳`, is the chosen cartesian lift of
the identity. -/
@[simp]
lemma pullbackFiberIdIso_hom_fac {T : 𝒮} (y : p.Fiber T) :
    Fiber.fiberInclusion.map (pullbackFiberIdIso y).hom = IsPreFibered.pullbackMap y.2 (𝟙 T) := by
  have hid : p.IsHomLift (𝟙 T) (𝟙 y.1) := IsHomLift.id y.2
  have := hid
  exact (Category.comp_id _).symm.trans (fiberIsoOfCartesian_hom_fac (p := p) (b := 𝟙 T)
    (z := pullbackFiber p y (𝟙 T)) (z' := y) (a := y.1)
    (IsPreFibered.pullbackMap y.2 (𝟙 T)) (𝟙 y.1)
    (IsPreFibered.pullbackMap.IsCartesian y.2 (𝟙 T)) inferInstance)

/-- The inverse of `pullbackFiberIdIso`, followed by the chosen cartesian lift of the identity, is
the identity. -/
@[reassoc (attr := simp)]
lemma pullbackFiberIdIso_inv_fac {T : 𝒮} (y : p.Fiber T) :
    Fiber.fiberInclusion.map (pullbackFiberIdIso y).inv ≫ IsPreFibered.pullbackMap y.2 (𝟙 T) =
      𝟙 y.1 :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- Base changing the inverse of `pullbackFiberIdIso` along `b` is inverse to contracting the
chosen pullback along the identity. -/
lemma pullbackFiberHom_pullbackFiberIdIso_inv {T Z : 𝒮} (y : p.Fiber T) (b : Z ⟶ T) :
    pullbackFiberHom (pullbackFiberIdIso y).inv b ≫
        (pullbackFiberCompIso' y (𝟙 T) b b (Category.comp_id b)).hom = 𝟙 _ := by
  refine fiber_hom_ext_of_cartesian b (IsPreFibered.pullbackMap y.2 b)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp [Functor.map_comp, Category.assoc, pullbackFiberCompIso'_hom_fac,
    pullbackFiberHom_fac_assoc, pullbackFiberIdIso_inv_fac, Category.comp_id, Functor.map_id,
    Category.id_comp]

/-- `pullbackFiberHom_pullbackFiberIdIso_inv` solved for the base change: base changing the inverse
of `pullbackFiberIdIso` along `b` is inverse to contracting the chosen pullback along the
identity. -/
lemma pullbackFiberHom_pullbackFiberIdIso_inv_eq {T Z : 𝒮} (y : p.Fiber T) (b : Z ⟶ T) :
    pullbackFiberHom (pullbackFiberIdIso y).inv b =
      (pullbackFiberCompIso' y (𝟙 T) b b (Category.comp_id b)).inv := by
  rw [← cancel_mono (pullbackFiberCompIso' y (𝟙 T) b b (Category.comp_id b)).hom,
    pullbackFiberHom_pullbackFiberIdIso_inv, Iso.inv_hom_id]

/-- `pullbackFiberCompIso'_pentagon` in the spelling in which the two contractions of a threefold
chosen pullback that land over `(γ ≫ ε) ≫ f` are written with the composite, and only the one
landing over `γ ≫ (ε ≫ f)` needs its base morphism named. -/
lemma pullbackFiberCompIso_pentagon {T V W Z : 𝒮} (y : p.Fiber T) (f : V ⟶ T) (ε : W ⟶ V)
    (γ : Z ⟶ W) :
    pullbackFiberHom (pullbackFiberCompIso y f ε).hom γ ≫
        (pullbackFiberCompIso' y (ε ≫ f) γ ((γ ≫ ε) ≫ f) (Category.assoc _ _ _).symm).hom =
      (pullbackFiberCompIso (pullbackFiber p y f) ε γ).hom ≫
        (pullbackFiberCompIso y f (γ ≫ ε)).hom :=
  pullbackFiberCompIso'_pentagon y f ε γ _ rfl _ rfl _ rfl

/-- The canonical isomorphism, in the fibre over `Z`, between the chosen pullbacks along `ε` and
`ε'` of the chosen pullbacks of one object `y` along `f` and `g`, for `ε ≫ f = ε' ≫ g`: both carry
a cartesian morphism to `y` over that common composite. -/
noncomputable def pullbackFiberComparison {T : 𝒮} (y : p.Fiber T) {V W Z : 𝒮} {f : V ⟶ T}
    {g : W ⟶ T} (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    pullbackFiber p (pullbackFiber p y f) ε ≅ pullbackFiber p (pullbackFiber p y g) ε' :=
  have : p.IsCartesian ε (IsPreFibered.pullbackMap (pullbackFiber p y f).2 ε) :=
    IsPreFibered.pullbackMap.IsCartesian _ _
  have : p.IsCartesian f (IsPreFibered.pullbackMap y.2 f) :=
    IsPreFibered.pullbackMap.IsCartesian _ _
  have : p.IsCartesian ε' (IsPreFibered.pullbackMap (pullbackFiber p y g).2 ε') :=
    IsPreFibered.pullbackMap.IsCartesian _ _
  have : p.IsCartesian g (IsPreFibered.pullbackMap y.2 g) :=
    IsPreFibered.pullbackMap.IsCartesian _ _
  fiberIsoOfCartesian (ε ≫ f)
    (IsPreFibered.pullbackMap (pullbackFiber p y f).2 ε ≫ IsPreFibered.pullbackMap y.2 f)
    (IsPreFibered.pullbackMap (pullbackFiber p y g).2 ε' ≫ IsPreFibered.pullbackMap y.2 g)
    inferInstance (by rw [heq]; infer_instance)

/-- The comparison of a chosen pullback with itself is the identity. -/
@[simp]
lemma pullbackFiberComparison_self {T : 𝒮} (y : p.Fiber T) {V Z : 𝒮} {f : V ⟶ T} (ε : Z ⟶ V)
    (heq : ε ≫ f = ε ≫ f) : (pullbackFiberComparison y ε ε heq).hom = 𝟙 _ :=
  fiberIsoOfCartesian_self _ _ _

/-- `pullbackFiberCompIso` is compatible with the lifts it compares: followed by the chosen
cartesian lift of `ε ≫ f` it is the composite of the two chosen lifts of `ε` and `f`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberCompIso_hom_fac {T V Z : 𝒮} (y : p.Fiber T) (f : V ⟶ T) (ε : Z ⟶ V) :
    Fiber.fiberInclusion.map (pullbackFiberCompIso y f ε).hom ≫
        IsPreFibered.pullbackMap y.2 (ε ≫ f) =
      IsPreFibered.pullbackMap (pullbackFiber p y f).2 ε ≫ IsPreFibered.pullbackMap y.2 f :=
  pullbackFiberCompIso'_hom_fac _ _ _ _ _

/-- The inverse of `pullbackFiberCompIso`, followed by the composite of the chosen cartesian lifts
of `ε` and `f`, is the chosen cartesian lift of `ε ≫ f`. -/
@[reassoc (attr := simp)]
lemma pullbackFiberCompIso_inv_fac {T V Z : 𝒮} (y : p.Fiber T) (f : V ⟶ T) (ε : Z ⟶ V) :
    Fiber.fiberInclusion.map (pullbackFiberCompIso y f ε).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p y f).2 ε ≫ IsPreFibered.pullbackMap y.2 f =
      IsPreFibered.pullbackMap y.2 (ε ≫ f) :=
  pullbackFiberCompIso'_inv_fac _ _ _ _ _

/-- Base change along a composite is base change along the two factors in turn, after contracting
the iterated chosen pullbacks. -/
lemma pullbackFiberHom_comp_base {T : 𝒮} {y y' : p.Fiber T} (α : y ⟶ y') {V Z : 𝒮} (f : V ⟶ T)
    (γ : Z ⟶ V) :
    pullbackFiberHom α (γ ≫ f) =
      (pullbackFiberCompIso y f γ).inv ≫ pullbackFiberHom (pullbackFiberHom α f) γ ≫
        (pullbackFiberCompIso y' f γ).hom :=
  (pullbackFiberHom_uniq α (γ ≫ f) _ (by
    simp only [Functor.map_comp, Category.assoc, pullbackFiberCompIso_hom_fac,
      pullbackFiberHom_fac_assoc]
    rw [pullbackFiberHom_fac, pullbackFiberCompIso_inv_fac_assoc])).symm

/-- `pullbackFiberComparison` is compatible with the two composites of chosen cartesian lifts it
compares. -/
@[reassoc (attr := simp)]
lemma pullbackFiberComparison_hom_fac {T : 𝒮} (y : p.Fiber T) {V W Z : 𝒮} {f : V ⟶ T} {g : W ⟶ T}
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    Fiber.fiberInclusion.map (pullbackFiberComparison y ε ε' heq).hom ≫
        IsPreFibered.pullbackMap (pullbackFiber p y g).2 ε' ≫ IsPreFibered.pullbackMap y.2 g =
      IsPreFibered.pullbackMap (pullbackFiber p y f).2 ε ≫ IsPreFibered.pullbackMap y.2 f :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

end Functor

end CategoryTheory
