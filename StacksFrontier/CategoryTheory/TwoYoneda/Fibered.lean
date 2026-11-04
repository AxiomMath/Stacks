module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import StacksCore.Tactic.StacksAttribute

/-!
# The 2-Yoneda lemma for fibred categories (Stacks 0GWI)

Let `𝒞` be a category, let `p : 𝒮 ⥤ 𝒞` be a fibred category over `𝒞`, and let `U : 𝒞`.
The slice category `𝒞/U` is fibred over `𝒞` via the forgetful functor `Over.forget U`,
and in this fibration *every* morphism `g : a ⟶ b` of `Over U` is strongly Cartesian over
its underlying `𝒞`-arrow `g.left`. The object `1_U = (U, 𝟙 U)` is terminal in `𝒞/U`, and
the 2-Yoneda lemma says that evaluation at `1_U` is an equivalence of categories
`Mor_{Fib/𝒞}(𝒞/U, 𝒮) ⥤ 𝒮_U`, `G ↦ G 1_U`.

An object of `Mor_{Fib/𝒞}(𝒞/U, 𝒮)` is a morphism of fibred categories in the sense of
Stacks Definition 02XP(2): a functor `G : Over U ⥤ 𝒮` with `G ⋙ p = Over.forget U`
strictly, sending strongly Cartesian morphisms to strongly Cartesian morphisms. Because
every arrow of the slice fibration is Cartesian, the second condition is the
unconditional requirement that `G.map g` be strongly Cartesian over `g.left`. A morphism
of `Mor_{Fib/𝒞}(𝒞/U, 𝒮)` is a natural transformation of the underlying functors all of
whose components lie over identities (Stacks Definition 02XP(3)).

Dictionary between the Stacks Project and Mathlib:

| Stacks notion                       | Mathlib name                                  |
|-------------------------------------|-----------------------------------------------|
| `𝒞/U`                               | `CategoryTheory.Over U`                       |
| structure functor `π_U`             | `CategoryTheory.Over.forget U`                |
| `𝒮_U`                               | `CategoryTheory.Functor.Fiber p U`            |
| `φ` lies over `f`                   | `CategoryTheory.Functor.IsHomLift p f φ`      |
| strongly Cartesian (02XK)           | `CategoryTheory.Functor.IsStronglyCartesian`  |
| fibred category (003T)              | `CategoryTheory.Functor.IsFibered`            |
| chosen pullbacks (02XN)             | `CategoryTheory.Functor.IsPreFibered.pullbackObj` |
-/

@[expose] public section

-- Load-bearing: the `eqToHom` casts produced by `Functor.congr_obj`/`congr_hom` mention
-- `(Over.forget U).obj x`, which is only reducibly equal to `x.left`, and the
-- `IsHomLift`/`Fiber.homMk` API compares such casts up to definitional unfolding.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

namespace Functor

/-- A morphism of fibred categories `(𝒞/U, Over.forget U) ⟶ (𝒮, p)`, i.e. an object of
the category `Mor_{Fib/𝒞}(𝒞/U, 𝒮)` of Stacks Definition 02XP(2) with source the slice
fibration. It is a functor over `𝒞` — a `BasedFunctor` between the based categories
attached to `Over.forget U` and to `p`, so the underlying functor `Over U ⥤ 𝒮` commutes
strictly with the projections to `𝒞` — which in addition preserves strongly Cartesian
morphisms.

Since the slice projection `Over.forget U` is a fibration in which every morphism
`g : a ⟶ b` of `Over U` is strongly Cartesian over its underlying `𝒞`-arrow
`g.left = (Over.forget U).map g`, the preservation condition specialises to the
unconditional requirement that `toFunctor.map g` be strongly Cartesian over `g.left`. -/
@[stacks_fixed 0GWI]
structure FiberedMor (p : 𝒮 ⥤ 𝒞) (U : 𝒞) extends
    BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p where
  /-- Preservation of strongly Cartesian morphisms: the image of every morphism `g` of
  `Over U` is strongly Cartesian over the base arrow `g.left`. -/
  cartesian : ∀ {a b : Over U} (g : a ⟶ b),
    p.IsStronglyCartesian g.left (toFunctor.map g)

namespace FiberedMor

variable {p : 𝒮 ⥤ 𝒞} {U : 𝒞}

/-- The object-level consequence of strict commutation: `p (G x) = π_U x`. -/
lemma obj_over (G : FiberedMor p U) (x : Over U) :
    p.obj (G.toFunctor.obj x) = (Over.forget U).obj x :=
  G.w_obj x

/-- The morphism-level consequence of strict commutation: `G.map g` lies over the
underlying base arrow `g.left = (Over.forget U).map g`. -/
lemma isHomLift_map (G : FiberedMor p U) {a b : Over U} (g : a ⟶ b) :
    p.IsHomLift g.left (G.toFunctor.map g) := by
  apply IsHomLift.of_fac' p g.left (G.toFunctor.map g) (G.obj_over a) (G.obj_over b)
  have h := Functor.congr_hom G.w g
  simp only [BasedCategory.ofFunctor, Functor.comp_map, Over.forget_map] at h
  rw [h]

/-- The category `Mor_{Fib/𝒞}(𝒞/U, 𝒮)` of morphisms of fibred categories from the slice
fibration `𝒞/U` to `p`. Its morphisms are the 2-morphisms of fibred categories of Stacks
Definition 02XP(3), i.e. the `BasedNatTrans` of the underlying functors over `𝒞`: natural
transformations all of whose components lie over an identity. -/
instance instCategory (p : 𝒮 ⥤ 𝒞) (U : 𝒞) : Category (FiberedMor p U) where
  Hom G H := G.toBasedFunctor ⟶ H.toBasedFunctor
  id G := 𝟙 G.toBasedFunctor
  comp α β := α ≫ β
  id_comp _ := Category.id_comp _
  comp_id _ := Category.comp_id _
  assoc _ _ _ := Category.assoc _ _ _

/-- The terminal object `1_U = (U, 𝟙 U)` of the slice category `𝒞/U`. -/
abbrev unit (U : 𝒞) : Over U := Over.mk (𝟙 U)

/-- The canonical morphism `x ⟶ 1_U` of `𝒞/U` to the terminal object; its underlying
`𝒞`-arrow is the structure map `x.hom`. -/
def toUnit (x : Over U) : x ⟶ unit U :=
  Over.homMk x.hom (by simp)

/-- The underlying `𝒞`-arrow of the canonical morphism `toUnit x` is the structure map `x.hom`. -/
@[simp] lemma toUnit_left (x : Over U) : (toUnit x).left = x.hom := rfl

/-- The canonical arrows to the terminal object are compatible with the arrows of `𝒞/U`. -/
lemma toUnit_comp {x' x : Over U} (g : x' ⟶ x) : toUnit x' = g ≫ toUnit x := by
  apply Over.OverMorphism.ext
  simp [toUnit, Over.w g]

/-- The value of a morphism of fibred categories at the terminal object lies over `U`. -/
lemma obj_over_unit (G : FiberedMor p U) : p.obj (G.toFunctor.obj (unit U)) = U :=
  G.obj_over (unit U)

/-- The component at the terminal object of a 2-morphism lies over `𝟙 U`. -/
lemma isHomLift_app_unit {G H : FiberedMor p U} (t : G ⟶ H) :
    p.IsHomLift (𝟙 U) (t.toNatTrans.app (unit U)) :=
  t.isHomLift rfl

end FiberedMor

/-- The evaluation, or "2-Yoneda", functor
`ev_U : Mor_{Fib/𝒞}(𝒞/U, 𝒮) ⥤ 𝒮_U`, `G ↦ G 1_U`.

On objects it sends a morphism of fibred categories `G` to its value at the terminal
object `1_U = (U, 𝟙 U)` of `𝒞/U`, which lies in the fibre over `U` because
`G ⋙ p = Over.forget U`. On a 2-morphism `t` it returns the component of `t` at `1_U`,
which lies over `𝟙 U` and is therefore a morphism of the fibre. -/
@[stacks 0GWI]
def fibYonedaEvaluation (p : 𝒮 ⥤ 𝒞) (U : 𝒞) : FiberedMor p U ⥤ p.Fiber U where
  obj G := Fiber.mk G.obj_over_unit
  map {G H} t :=
    haveI := FiberedMor.isHomLift_app_unit t
    Fiber.homMk p U (t.toNatTrans.app (FiberedMor.unit U))
  map_id G := by
    apply Fiber.fiberInclusion.map_injective
    have := FiberedMor.isHomLift_app_unit (𝟙 G)
    rw [Fiber.fiberInclusion_homMk,
      Fiber.fiberInclusion.map_id (Fiber.mk G.obj_over_unit)]
    rfl
  map_comp {G H K} α β := by
    have := FiberedMor.isHomLift_app_unit α
    have := FiberedMor.isHomLift_app_unit β
    have := FiberedMor.isHomLift_app_unit (α ≫ β)
    apply Fiber.fiberInclusion.map_injective
    rw [Fiber.fiberInclusion_homMk, Fiber.fiberInclusion.map_comp,
      Fiber.fiberInclusion_homMk, Fiber.fiberInclusion_homMk]
    rfl

/-- The evaluation functor sends a 2-morphism to its component at the terminal object. -/
lemma fibYonedaEvaluation_map (p : 𝒮 ⥤ 𝒞) (U : 𝒞) {G H : FiberedMor p U} (t : G ⟶ H) :
    haveI := FiberedMor.isHomLift_app_unit t
    (fibYonedaEvaluation p U).map t = Fiber.homMk p U (t.toNatTrans.app (FiberedMor.unit U)) :=
  rfl

/-- The image of a 2-morphism under the evaluation functor, viewed in `𝒮`, is its component at
the terminal object. -/
private lemma fiberInclusion_map_fibYonedaEvaluation_map (p : 𝒮 ⥤ 𝒞) (U : 𝒞)
    {G H : FiberedMor p U} (t : G ⟶ H) :
    Fiber.fiberInclusion.map ((fibYonedaEvaluation p U).map t) =
      t.toNatTrans.app (FiberedMor.unit U) :=
  haveI := FiberedMor.isHomLift_app_unit t
  Fiber.fiberInclusion_homMk p U _

/-- The evaluation functor is faithful. -/
lemma fibYonedaEvaluation_faithful (p : 𝒮 ⥤ 𝒞) [p.IsFibered] (U : 𝒞) :
    (fibYonedaEvaluation p U).Faithful := by
  refine ⟨fun {G H} t t' h => ?_⟩
  have hunit : t.toNatTrans.app (FiberedMor.unit U) = t'.toNatTrans.app (FiberedMor.unit U) := by
    rw [← fiberInclusion_map_fibYonedaEvaluation_map, h,
      fiberInclusion_map_fibYonedaEvaluation_map]
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  have hlt : p.IsHomLift (𝟙 x.left) (t.toNatTrans.app x) := t.isHomLift rfl
  have hlt' : p.IsHomLift (𝟙 x.left) (t'.toNatTrans.app x) := t'.isHomLift rfl
  have hsc : p.IsStronglyCartesian x.hom (H.toFunctor.map (FiberedMor.toUnit x)) :=
    FiberedMor.toUnit_left x ▸ H.cartesian (FiberedMor.toUnit x)
  apply IsStronglyCartesian.ext p x.hom (H.toFunctor.map (FiberedMor.toUnit x)) (𝟙 x.left)
  have nat_t := t.toNatTrans.naturality (FiberedMor.toUnit x)
  have nat_t' := t'.toNatTrans.naturality (FiberedMor.toUnit x)
  rw [← nat_t, ← nat_t', hunit]

/-!
### Fullness: building a 2-morphism from its value at the terminal object

Construction of a 2-morphism `G ⟶ H` out of a morphism `G 1_U ⟶ H 1_U` over `𝟙 U`, by
pulling back along the canonical arrows to the terminal object.
-/

namespace FiberedMor.HomOfUnitHom

variable {p : 𝒮 ⥤ 𝒞} [p.IsFibered] {U : 𝒞} {G H : FiberedMor p U}
  (φbar : G.toFunctor.obj (unit U) ⟶ H.toFunctor.obj (unit U))

/-- `H.toFunctor.map (toUnit x)` is strongly Cartesian over `x.hom`. -/
instance isStronglyCartesian_map_toUnit (x : Over U) :
    p.IsStronglyCartesian x.hom (H.toFunctor.map (toUnit x)) :=
  toUnit_left x ▸ H.cartesian (toUnit x)

/-- `G.toFunctor.map (toUnit x)` lies over `x.hom`. -/
instance isHomLift_map_toUnit (x : Over U) :
    p.IsHomLift x.hom (G.toFunctor.map (toUnit x)) :=
  toUnit_left x ▸ G.isHomLift_map (toUnit x)

variable [hφ : p.IsHomLift (𝟙 U) φbar]

/-- The composite `G.toFunctor.map (toUnit x) ≫ φbar` lies over `x.hom`. -/
instance isHomLift_map_toUnit_comp (x : Over U) :
    p.IsHomLift x.hom (G.toFunctor.map (toUnit x) ≫ φbar) :=
  IsHomLift.comp_lift_id_right p x.hom (G.toFunctor.map (toUnit x)) φbar

/-- The component at `x` of the 2-morphism induced by `φbar`: the unique lift of
`𝟙 x.left` through the strongly Cartesian arrow `H.toFunctor.map (toUnit x)` whose
composite with it is `G.toFunctor.map (toUnit x) ≫ φbar`. -/
noncomputable def app (x : Over U) : G.toFunctor.obj x ⟶ H.toFunctor.obj x :=
  IsStronglyCartesian.map p x.hom (H.toFunctor.map (toUnit x))
    (show x.hom = 𝟙 x.left ≫ x.hom by simp) (G.toFunctor.map (toUnit x) ≫ φbar)

omit [p.IsFibered] in
/-- The defining factorisation of `app`. -/
lemma app_fac (x : Over U) :
    app φbar x ≫ H.toFunctor.map (toUnit x) = G.toFunctor.map (toUnit x) ≫ φbar :=
  IsStronglyCartesian.fac p x.hom (H.toFunctor.map (toUnit x))
    (show x.hom = 𝟙 x.left ≫ x.hom by simp) (G.toFunctor.map (toUnit x) ≫ φbar)

/-- Each component of the induced 2-morphism lies over an identity. -/
instance app_isHomLift (x : Over U) : p.IsHomLift (𝟙 x.left) (app φbar x) :=
  IsStronglyCartesian.map_isHomLift p x.hom (H.toFunctor.map (toUnit x))
    (show x.hom = 𝟙 x.left ≫ x.hom by simp) (G.toFunctor.map (toUnit x) ≫ φbar)

end FiberedMor.HomOfUnitHom

/-- The evaluation functor is full. -/
lemma fibYonedaEvaluation_full (p : 𝒮 ⥤ 𝒞) [p.IsFibered] (U : 𝒞) :
    (fibYonedaEvaluation p U).Full := by
  refine ⟨fun {G H} φ => ?_⟩
  set φbar : G.toFunctor.obj (FiberedMor.unit U) ⟶ H.toFunctor.obj (FiberedMor.unit U) :=
    Fiber.fiberInclusion.map φ
  have hφ : p.IsHomLift (𝟙 U) φbar := inferInstance
  let τ : G.toFunctor ⟶ H.toFunctor :=
    { app := fun x => FiberedMor.HomOfUnitHom.app φbar x
      naturality := fun x' x g => by
        have := G.isHomLift_map g
        have := H.isHomLift_map g
        have hL : p.IsHomLift g.left
            (G.toFunctor.map g ≫ FiberedMor.HomOfUnitHom.app φbar x) :=
          IsHomLift.comp_lift_id_right p g.left (G.toFunctor.map g)
            (FiberedMor.HomOfUnitHom.app φbar x)
        have hR : p.IsHomLift g.left
            (FiberedMor.HomOfUnitHom.app φbar x' ≫ H.toFunctor.map g) :=
          IsHomLift.comp_lift_id_left p g.left (H.toFunctor.map g)
            (FiberedMor.HomOfUnitHom.app φbar x')
        apply IsStronglyCartesian.ext p x.hom
          (H.toFunctor.map (FiberedMor.toUnit x)) g.left
        have hx' : FiberedMor.toUnit x' = g ≫ FiberedMor.toUnit x := FiberedMor.toUnit_comp g
        rw [Category.assoc, FiberedMor.HomOfUnitHom.app_fac φbar x, ← Category.assoc,
          ← G.toFunctor.map_comp, ← hx', Category.assoc]
        rw [show H.toFunctor.map g ≫ H.toFunctor.map (FiberedMor.toUnit x)
              = H.toFunctor.map (FiberedMor.toUnit x') from by
            rw [← H.toFunctor.map_comp, ← hx']]
        rw [FiberedMor.HomOfUnitHom.app_fac φbar x'] }
  let t : BasedNatTrans G.toBasedFunctor H.toBasedFunctor :=
    { toNatTrans := τ
      isHomLift' := fun x => by
        simpa [BasedCategory.ofFunctor] using
          FiberedMor.HomOfUnitHom.app_isHomLift φbar x }
  refine ⟨t, ?_⟩
  apply Fiber.hom_ext
  rw [fiberInclusion_map_fibYonedaEvaluation_map]
  dsimp only [t, τ]
  have hfac := FiberedMor.HomOfUnitHom.app_fac φbar (FiberedMor.unit U)
  have hid : FiberedMor.toUnit (FiberedMor.unit U) = 𝟙 (FiberedMor.unit U) := by
    apply Over.OverMorphism.ext; simp [FiberedMor.toUnit]
  rw [hid, H.toFunctor.map_id, G.toFunctor.map_id, Category.comp_id, Category.id_comp] at hfac
  exact hfac

/-!
### Essential surjectivity: the quasi-inverse built from the cleavage

Construction of a morphism of fibred categories out of an object of the fibre `𝒮_U`,
using the chosen cleavage of `p`: the object `(V, f)` of `𝒞/U` is sent to the chosen
pullback `f^* a`.
-/

namespace FiberedMor.OfFiberObj

variable (p : 𝒮 ⥤ 𝒞) [p.IsFibered] (U : 𝒞) {a : 𝒮} (ha : p.obj a = U)

/-- The underlying functor `𝒞/U ⥤ 𝒮` of the quasi-inverse, sending `(V, f) ↦ f^* a` and
a morphism `g` to the map induced by the universal property of the chosen Cartesian
lift. -/
noncomputable def pullbackFunctor : Over U ⥤ 𝒮 where
  obj x := IsPreFibered.pullbackObj ha x.hom
  map {x' x} g :=
    IsStronglyCartesian.map p x.hom (IsPreFibered.pullbackMap ha x.hom)
      (show x'.hom = g.left ≫ x.hom from (Over.w g).symm)
      (IsPreFibered.pullbackMap ha x'.hom)
  map_id x := by
    simp only [Over.id_left]
    exact IsStronglyCartesian.map_self p x.hom (IsPreFibered.pullbackMap ha x.hom)
  map_comp {x'' x' x} g' g :=
    (IsStronglyCartesian.map_comp_map p x.hom (IsPreFibered.pullbackMap ha x.hom)
      (show x'.hom = g.left ≫ x.hom from (Over.w g).symm)
      (show x''.hom = g'.left ≫ x'.hom from (Over.w g').symm)
      (IsPreFibered.pullbackMap ha x'.hom) (IsPreFibered.pullbackMap ha x''.hom)).symm

/-- The image of a morphism under `pullbackFunctor` lies over its base arrow. -/
lemma pullbackFunctor_map_isHomLift {x' x : Over U} (g : x' ⟶ x) :
    p.IsHomLift g.left ((pullbackFunctor p U ha).map g) :=
  IsStronglyCartesian.map_isHomLift p x.hom (IsPreFibered.pullbackMap ha x.hom)
    (show x'.hom = g.left ≫ x.hom from (Over.w g).symm)
    (IsPreFibered.pullbackMap ha x'.hom)

/-- The image of a morphism under `pullbackFunctor` is compatible with the chosen
Cartesian lifts. -/
lemma pullbackFunctor_map_fac {x' x : Over U} (g : x' ⟶ x) :
    (pullbackFunctor p U ha).map g ≫ IsPreFibered.pullbackMap ha x.hom
      = IsPreFibered.pullbackMap ha x'.hom :=
  IsStronglyCartesian.fac p x.hom (IsPreFibered.pullbackMap ha x.hom)
    (show x'.hom = g.left ≫ x.hom from (Over.w g).symm)
    (IsPreFibered.pullbackMap ha x'.hom)

/-- Cancellation of the chosen Cartesian lift: a morphism of chosen pullbacks whose
composite with `pullbackMap ha x.hom` is strongly Cartesian is itself strongly
Cartesian. -/
@[sga "1 VI 6.13" "special case"]
lemma isStronglyCartesian_of_comp_pullback {x' x : Over U} (g : x' ⟶ x)
    (φ : IsPreFibered.pullbackObj ha x'.hom ⟶ IsPreFibered.pullbackObj ha x.hom)
    [hlift : p.IsHomLift g.left φ]
    [hsc : p.IsStronglyCartesian (g.left ≫ x.hom)
      (φ ≫ IsPreFibered.pullbackMap ha x.hom)] :
    p.IsStronglyCartesian g.left φ :=
  IsStronglyCartesian.of_comp p (f := g.left) (g := x.hom) (φ := φ)
    (ψ := IsPreFibered.pullbackMap ha x.hom)

/-- `pullbackFunctor` preserves strongly Cartesian morphisms. -/
lemma pullbackFunctor_map_isStronglyCartesian {x' x : Over U} (g : x' ⟶ x) :
    p.IsStronglyCartesian g.left ((pullbackFunctor p U ha).map g) := by
  have hsc0 : p.IsStronglyCartesian x'.hom (IsPreFibered.pullbackMap ha x'.hom) :=
    inferInstance
  have hsc : p.IsStronglyCartesian (g.left ≫ x.hom)
      ((pullbackFunctor p U ha).map g ≫ IsPreFibered.pullbackMap ha x.hom) := by
    rw [pullbackFunctor_map_fac p U ha g, Over.w g]; exact hsc0
  have hlift := pullbackFunctor_map_isHomLift p U ha g
  exact isStronglyCartesian_of_comp_pullback p U ha g ((pullbackFunctor p U ha).map g)
    (hlift := hlift) (hsc := hsc)

/-- `pullbackFunctor` commutes strictly with the projections to `𝒞`. -/
lemma pullbackFunctor_comp : pullbackFunctor p U ha ⋙ p = Over.forget U := by
  apply CategoryTheory.Functor.ext
  · intro x' x g
    have := pullbackFunctor_map_isHomLift p U ha g
    rw [Functor.comp_map, IsHomLift.fac' p g.left ((pullbackFunctor p U ha).map g)]
    rfl
  · intro x
    exact IsPreFibered.pullbackObj_proj ha x.hom

/-- The morphism of fibred categories `𝒞/U ⟶ 𝒮` determined by an object of the fibre. -/
noncomputable def fiberedMor : FiberedMor p U where
  toFunctor := pullbackFunctor p U ha
  w := pullbackFunctor_comp p U ha
  cartesian g := pullbackFunctor_map_isStronglyCartesian p U ha g

/-- The chosen Cartesian lift of `𝟙 U` is an isomorphism, whence the isomorphism
`(𝟙 U)^* a ≅ a` in the fibre `𝒮_U`. -/
noncomputable def fiberIso (hproj : p.obj (IsPreFibered.pullbackObj ha (𝟙 U)) = U) :
    Fiber.mk hproj ≅ Fiber.mk ha := by
  haveI hiso : IsIso (IsPreFibered.pullbackMap ha (𝟙 U)) :=
    IsStronglyCartesian.isIso_of_base_isIso p (𝟙 U) (IsPreFibered.pullbackMap ha (𝟙 U))
  haveI hinv : p.IsHomLift (𝟙 U) (CategoryTheory.inv (IsPreFibered.pullbackMap ha (𝟙 U))) :=
    IsHomLift.lift_id_inv_isIso p U (IsPreFibered.pullbackMap ha (𝟙 U))
  exact {
    hom := Fiber.homMk p U (IsPreFibered.pullbackMap ha (𝟙 U))
    inv := Fiber.homMk p U (CategoryTheory.inv (IsPreFibered.pullbackMap ha (𝟙 U)))
    hom_inv_id := by
      apply Fiber.hom_ext
      rw [Fiber.fiberInclusion.map_comp, Fiber.fiberInclusion_homMk,
        Fiber.fiberInclusion_homMk, Fiber.fiberInclusion.map_id]
      simp
    inv_hom_id := by
      apply Fiber.hom_ext
      rw [Fiber.fiberInclusion.map_comp, Fiber.fiberInclusion_homMk,
        Fiber.fiberInclusion_homMk, Fiber.fiberInclusion.map_id]
      simp }

end FiberedMor.OfFiberObj

/-- The evaluation functor is essentially surjective. -/
lemma fibYonedaEvaluation_essSurj (p : 𝒮 ⥤ 𝒞) [p.IsFibered] (U : 𝒞) :
    (fibYonedaEvaluation p U).EssSurj := by
  refine ⟨fun y => ⟨FiberedMor.OfFiberObj.fiberedMor p U y.2, ⟨?_⟩⟩⟩
  exact FiberedMor.OfFiberObj.fiberIso p U y.2
    (FiberedMor.OfFiberObj.fiberedMor p U y.2).obj_over_unit

/-- **The 2-Yoneda lemma for fibred categories (Stacks 0GWI).** For a fibred category
`p : 𝒮 ⥤ 𝒞` and an object `U : 𝒞`, the evaluation functor
`ev_U : Mor_{Fib/𝒞}(𝒞/U, 𝒮) ⥤ 𝒮_U`, `G ↦ G 1_U`, is an equivalence of categories. -/
@[stacks 0GWI]
theorem fibYonedaEvaluation_isEquivalence (p : 𝒮 ⥤ 𝒞) [p.IsFibered] (U : 𝒞) :
    (fibYonedaEvaluation p U).IsEquivalence :=
  have := fibYonedaEvaluation_faithful p U
  have := fibYonedaEvaluation_full p U
  have := fibYonedaEvaluation_essSurj p U
  { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

end Functor

end CategoryTheory
