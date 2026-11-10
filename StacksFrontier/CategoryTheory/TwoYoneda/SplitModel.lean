module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.OfPresheaf
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The 2-Yoneda construction of a split model

Let `p : 𝒮 ⥤ 𝒞` be a category fibred in groupoids. Define a contravariant functor `F` from `𝒞` to
groupoids by
`F(U) = Mor_{Cat/𝒞}(𝒞/U, 𝒮)`,
with `F(f) : F(V) ⥤ F(U)` induced, for `f : U ⟶ V`, by the functor `𝒞/U ⥤ 𝒞/V`; let `𝒮'` be the
category fibred in groupoids attached to `F`. Then `(U, x) ↦ x(id_U)` is a functor `G : 𝒮' ⥤ 𝒮`
over `𝒞` whose restriction to the fibre over `U` is the evaluation functor `F(U) ⥤ 𝒮_U` of the
2-Yoneda lemma, hence an equivalence; so `G` is an equivalence, and an equivalence over `𝒞`.

## Main definitions

* `CategoryTheory.BasedCategory.slice`: the slice category `𝒞/U` as an object of `Cat/𝒞`, so that
  `Mor_{Cat/𝒞}(𝒞/U, 𝒮)` is the hom-category `BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor p`;
* `CategoryTheory.BasedFunctor.overMap` and `CategoryTheory.BasedFunctor.precomp`: the functor
  `𝒞/U ⥤ 𝒞/V` as a 1-morphism over `𝒞`, and precomposition with a 1-morphism over `𝒞`;
* `CategoryTheory.Functor.twoYonedaPresheaf`: the functor `F` of the remark;
* `CategoryTheory.Functor.sliceEv`: the arrow `x(a) ⟶ x(id_U)` obtained by evaluating
  `x ∈ F(U)` along the unique arrow from `a` to the terminal object `id_U` of `𝒞/U`;
* `CategoryTheory.Functor.twoYonedaComparison`: the functor `G` of the remark.

## Main results

* `CategoryTheory.Functor.twoYonedaComparison_comp`: `G` is a functor over `𝒞`;
* `CategoryTheory.Functor.inducedFunctor_comp_mapOfComp`: the restriction of `G` to the fibre over
  `U` is the evaluation functor of the 2-Yoneda lemma;
* `CategoryTheory.Functor.twoYonedaComparison_isEquivalence` and
  `CategoryTheory.Functor.twoYonedaComparison_isEquivalenceOver`: `G` is an equivalence of
  categories, and an equivalence in the 2-category of categories fibred in groupoids over `𝒞`.

## Implementation notes

`F` is a strict functor to `Grpd`, not a pseudofunctor, because `Over.map` is strictly functorial
(`Over.mapId_eq`, `Over.mapComp_eq`) and so is precomposition of based functors. That `F(U)` is a
groupoid uses that `p` is fibred in groupoids: `F(U)` is equivalent to the groupoid `𝒮_U` by the
2-Yoneda lemma.

`G` sends a morphism `(f, φ) : (V, y) ⟶ (U, x)` of `𝒮'`, with `φ : y ⟶ (𝒞/f)^* x` a 2-morphism
over `𝒞`, to `φ(id_V) : y(id_V) ⟶ x(id_V ∘ f)` followed by `sliceEv`, the evaluation
`x(id_V ∘ f) ⟶ x(id_U)`.

The domain of `G` is written as the Grothendieck construction
`∫ᶜ (F ⋙ Grpd.forgetToCat).toPseudofunctor'`, the underlying category of
`presheafOfGroupoids F`, and its codomain as `(BasedCategory.ofFunctor p).obj`, which is `𝒮`.
-/

@[expose] public section

-- The proofs below rewrite in `𝒮` under two spellings of its category structure, the ambient one
-- and the one carried by `BasedCategory.ofFunctor p`, which agree only at default transparency.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- The slice category `𝒞/U` as an object of the 2-category of categories over `𝒞`, i.e. with
its structure functor `𝒞/U ⥤ 𝒞`. -/
abbrev BasedCategory.slice (U : 𝒞) : BasedCategory.{v₁, max u₁ v₁} 𝒞 :=
  BasedCategory.ofFunctor (Over.forget U)

namespace BasedFunctor

/-- Two 1-morphisms over `𝒞` with the same underlying functor are equal. -/
private lemma ext_of_toFunctor {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
    {Φ Ψ : 𝒳 ⥤ᵇ 𝒴} (h : Φ.toFunctor = Ψ.toFunctor) : Φ = Ψ := by
  cases Φ; cases Ψ; subst h; rfl

/-- The functor `𝒞/U ⥤ 𝒞/V` induced by `f : U ⟶ V`, as a 1-morphism over `𝒞`. -/
def overMap {U V : 𝒞} (f : U ⟶ V) : BasedCategory.slice U ⥤ᵇ BasedCategory.slice V where
  toFunctor := Over.map f
  w := Over.mapForget_eq f

/-- The underlying functor of `overMap f` is `Over.map f`. -/
@[simp] lemma overMap_toFunctor {U V : 𝒞} (f : U ⟶ V) :
    (overMap f).toFunctor = Over.map f := rfl

/-- `𝒞/U ⥤ 𝒞/U` induced by the identity is the identity. -/
lemma overMap_id (U : 𝒞) : overMap (𝟙 U) = BasedFunctor.id (BasedCategory.slice U) :=
  ext_of_toFunctor (Over.mapId_eq U)

/-- The functors `𝒞/U ⥤ 𝒞/V` are strictly functorial in `f`. -/
lemma overMap_comp {U V W : 𝒞} (f : U ⟶ V) (g : V ⟶ W) :
    overMap (f ≫ g) = BasedFunctor.comp (overMap f) (overMap g) :=
  ext_of_toFunctor (Over.mapComp_eq f g)

/-- Precomposition with a 1-morphism `Φ : 𝒳 ⟶ 𝒴` over `𝒞`, as a functor between the categories
of 1-morphisms over `𝒞` into a fixed `𝒵`. -/
@[sga "4 Vbis 1.2.10"]
def precomp {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
    (Φ : 𝒳 ⥤ᵇ 𝒴) (𝒵 : BasedCategory.{v₄, u₄} 𝒞) : (𝒴 ⥤ᵇ 𝒵) ⥤ (𝒳 ⥤ᵇ 𝒵) where
  obj G := BasedFunctor.comp Φ G
  map α := BasedCategory.whiskerLeft Φ α

/-- Precomposition with `Φ` sends `G` to the composite of `Φ` and `G`. -/
@[simp] lemma precomp_obj {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
    (Φ : 𝒳 ⥤ᵇ 𝒴) (𝒵 : BasedCategory.{v₄, u₄} 𝒞) (G : 𝒴 ⥤ᵇ 𝒵) :
    (precomp Φ 𝒵).obj G = BasedFunctor.comp Φ G := rfl

/-- Precomposition with the identity is the identity. -/
lemma precomp_id (𝒳 : BasedCategory.{v₂, u₂} 𝒞) (𝒵 : BasedCategory.{v₄, u₄} 𝒞) :
    precomp (BasedFunctor.id 𝒳) 𝒵 = CategoryTheory.Functor.id _ := rfl

/-- Precomposition is contravariantly functorial. -/
lemma precomp_comp {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
    {𝒳' : BasedCategory.{v₃, u₃} 𝒞} (Φ : 𝒳 ⥤ᵇ 𝒴) (Ψ : 𝒴 ⥤ᵇ 𝒳')
    (𝒵 : BasedCategory.{v₄, u₄} 𝒞) :
    precomp (BasedFunctor.comp Φ Ψ) 𝒵 = precomp Ψ 𝒵 ⋙ precomp Φ 𝒵 := rfl

/-- The component at `z` of the precomposition of a 2-morphism `α` with `Φ` is the component of
`α` at `Φ z`. -/
@[simp] lemma precomp_map_app {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
    (Φ : 𝒳 ⥤ᵇ 𝒴) {𝒵 : BasedCategory.{v₄, u₄} 𝒞} {G H : 𝒴 ⥤ᵇ 𝒵} (α : G ⟶ H) (z : 𝒳.obj) :
    ((precomp Φ 𝒵).map α).app z = α.app (Φ.obj z) := rfl

/-- The component at `z` of a composite of 2-morphisms over `𝒞`. -/
lemma comp_app {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
    {x y z : 𝒳 ⥤ᵇ 𝒴} (α : x ⟶ y) (β : y ⟶ z) (w : 𝒳.obj) :
    (α ≫ β).app w = α.app w ≫ β.app w := rfl

/-- The component at `z` of the transport along an equality of 1-morphisms over `𝒞` is the
transport along the induced equality of objects. -/
lemma eqToHom_app {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
    {x y : 𝒳 ⥤ᵇ 𝒴} (h : x = y) (z : 𝒳.obj) :
    (eqToHom h).app z = eqToHom (CategoryTheory.Functor.congr_obj
      (congrArg BasedFunctor.toFunctor h) z) := by
  subst h; simp

end BasedFunctor

/-- The category `Mor_{Cat/𝒞}(𝒞/U, 𝒮)` is a groupoid when `p : 𝒮 ⥤ 𝒞` is fibred in groupoids. -/
lemma isGroupoid_basedFunctor_slice (p : 𝒮 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) (U : 𝒞) :
    IsGroupoid (BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor p) :=
  have h := Functor.twoYonedaEvaluation_isEquivalence p hp U
  have : IsGroupoid (p.Fiber U) := hp.fiber_isGroupoid U
  have : (Functor.twoYonedaEvaluation p U).Full := h.full
  have : (Functor.twoYonedaEvaluation p U).Faithful := h.faithful
  isGroupoid_of_reflects_iso (Functor.twoYonedaEvaluation p U)

/-- The contravariant functor `F : 𝒞 ⥤ Groupoids` with `F(U) = Mor_{Cat/𝒞}(𝒞/U, 𝒮)` and
`F(f) : F(V) ⥤ F(U)` given by precomposition with the functor `𝒞/U ⥤ 𝒞/V` induced by
`f : U ⟶ V`. -/
@[stacks 076J]
noncomputable def Functor.twoYonedaPresheaf (p : 𝒮 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) :
    𝒞ᵒᵖ ⥤ Grpd.{max u₁ v₁ v₂, max u₁ v₁ u₂ v₂} where
  obj U := @Grpd.of (BasedCategory.slice U.unop ⥤ᵇ BasedCategory.ofFunctor p)
    (@Groupoid.ofIsGroupoid _ _ (isGroupoid_basedFunctor_slice p hp U.unop))
  map f := BasedFunctor.precomp (BasedFunctor.overMap f.unop) (BasedCategory.ofFunctor p)
  map_id U := by simp only [unop_id, BasedFunctor.overMap_id]; rfl
  map_comp f g := by simp only [unop_comp, BasedFunctor.overMap_comp]; rfl

namespace Functor

open Opposite Pseudofunctor Pseudofunctor.CoGrothendieck

variable (p : 𝒮 ⥤ 𝒞)

/-- Evaluation of `x ∈ Mor_{Cat/𝒞}(𝒞/U, 𝒮)` along the unique arrow from `a` to the terminal
object `id_U` of `𝒞/U`: the arrow `x(a) ⟶ x(id_U)` of `𝒮`. -/
noncomputable def sliceEv {U : 𝒞} (x : BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor p)
    (a : Over U) : x.obj a ⟶ x.obj (Over.mk (𝟙 U)) :=
  x.map (Over.mkIdTerminal.from a)

/-- Every arrow of `𝒞/U` with target `id_U` induces the same arrow of `𝒮` as the unique one. -/
lemma sliceEv_eq {U : 𝒞} (x : BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor p) {a : Over U}
    (h : a ⟶ Over.mk (𝟙 U)) : sliceEv p x a = x.map h :=
  congrArg (fun k => x.map k) (Over.mkIdTerminal.hom_ext (Over.mkIdTerminal.from a) h)

/-- Evaluation at the terminal object `id_U` itself is the identity arrow. -/
@[simp] lemma sliceEv_id {U : 𝒞} (x : BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor p) :
    sliceEv p x (Over.mk (𝟙 U)) = 𝟙 _ := by
  rw [sliceEv_eq p x (𝟙 _)]
  exact x.toFunctor.map_id _

/-- Evaluating at the terminal object absorbs any arrow of `𝒞/U`. -/
lemma map_comp_sliceEv {U : 𝒞} (x : BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor p)
    {a b : Over U} (h : a ⟶ b) : x.map h ≫ sliceEv p x b = sliceEv p x a := by
  rw [sliceEv_eq p x (h ≫ Over.mkIdTerminal.from b)]
  exact (x.toFunctor.map_comp _ _).symm

/-- Evaluating at the terminal object absorbs the transport along an equality of objects
of `𝒞/U`. -/
lemma eqToHom_comp_sliceEv {U : 𝒞} (x : BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor p)
    {a b : Over U} (hab : a = b) (h : x.obj a = x.obj b) :
    eqToHom h ≫ sliceEv p x b = sliceEv p x a := by
  subst hab; simp

/-- Evaluating a 2-morphism `α : y ⟶ (𝒞/g)^* x` at an object `z` of `𝒞/U` and then at the
terminal object of `𝒞/W` is the same as evaluating first at the terminal object of `𝒞/U`. -/
lemma app_comp_sliceEv {U W : 𝒞} (g : U ⟶ W)
    (y : BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor p)
    (x : BasedCategory.slice W ⥤ᵇ BasedCategory.ofFunctor p)
    (α : y ⟶ BasedFunctor.comp (BasedFunctor.overMap g) x) (z : Over U) :
    α.app z ≫ sliceEv p x ((Over.map g).obj z) =
      sliceEv p y z ≫ α.app (Over.mk (𝟙 U)) ≫
        sliceEv p x ((Over.map g).obj (Over.mk (𝟙 U))) := by
  have ht : sliceEv p y z ≫ α.app (Over.mk (𝟙 U)) ≫
        sliceEv p x ((Over.map g).obj (Over.mk (𝟙 U))) =
      α.app z ≫ x.map ((Over.map g).map (Over.mkIdTerminal.from z)) ≫
        sliceEv p x ((Over.map g).obj (Over.mk (𝟙 U))) :=
    α.toNatTrans.naturality_assoc (Over.mkIdTerminal.from z) _
  rw [ht, map_comp_sliceEv]
  rfl

/-- The unique arrow from `z` to the terminal object `id_U` of `𝒞/U` lies over the structure
morphism of `z`. -/
lemma forget_map_from_mkIdTerminal {U : 𝒞} (z : Over U) :
    (Over.forget U).map (Over.mkIdTerminal.from z) = z.hom := by
  rw [Over.mkIdTerminal.hom_ext (Over.mkIdTerminal.from z) (Over.homMk z.hom (by simp))]
  simp

/-- The fibre component of an identity of `𝒮'`, evaluated at the terminal object of `𝒞/U`, is
absorbed by evaluation at the terminal object. -/
lemma id_fiber_app_comp_sliceEv (hp : p.IsFiberedInGroupoids)
    (a : ∫ᶜ (p.twoYonedaPresheaf hp ⋙ Grpd.forgetToCat).toPseudofunctor') :
    (Hom.fiber (𝟙 a)).app (Over.mk (𝟙 a.base)) ≫
      sliceEv p a.fiber ((Over.map (𝟙 a.base)).obj (Over.mk (𝟙 a.base))) = 𝟙 _ := by
  simp only [CoGrothendieck.categoryStruct_id_fiber, Functor.toPseudofunctor'_mapId, eqToIso.inv]
  rw [Cat.eqToHom_app, BasedFunctor.eqToHom_app,
    eqToHom_comp_sliceEv p a.fiber (show Over.mk (𝟙 a.base)
      = (Over.map (𝟙 a.base)).obj (Over.mk (𝟙 a.base)) from
      (CategoryTheory.Functor.congr_obj (Over.mapId_eq a.base) _).symm)]
  exact sliceEv_id p a.fiber

/-- The functor `G : 𝒮' ⥤ 𝒮` sending the pair `(U, x)` to `x(id_U)`. -/
@[stacks 076J]
noncomputable def twoYonedaComparison (hp : p.IsFiberedInGroupoids) :
    ∫ᶜ (p.twoYonedaPresheaf hp ⋙ Grpd.forgetToCat).toPseudofunctor' ⥤
      (BasedCategory.ofFunctor p).obj where
  obj a := a.fiber.obj (Over.mk (𝟙 a.base))
  map {a b} φ := φ.fiber.app (Over.mk (𝟙 a.base)) ≫
    sliceEv p b.fiber ((Over.map φ.base).obj (Over.mk (𝟙 a.base)))
  map_id a := id_fiber_app_comp_sliceEv p hp a
  map_comp {a b c} φ ψ := by
    simp only [CoGrothendieck.categoryStruct_comp_fiber, CoGrothendieck.categoryStruct_comp_base,
      Functor.toPseudofunctor'_mapComp, eqToIso.inv]
    rw [BasedFunctor.comp_app, BasedFunctor.comp_app]
    erw [BasedFunctor.precomp_map_app]
    rw [Cat.eqToHom_app, BasedFunctor.eqToHom_app]
    simp only [Category.assoc]
    rw [eqToHom_comp_sliceEv p c.fiber (show (Over.map ψ.base).obj
        ((Over.map φ.base).obj (Over.mk (𝟙 a.base)))
          = (Over.map (φ.base ≫ ψ.base)).obj (Over.mk (𝟙 a.base)) from
        (CategoryTheory.Functor.congr_obj (Over.mapComp_eq φ.base ψ.base) _).symm)]
    erw [app_comp_sliceEv]
    rfl

/-- A functor over `𝒞` defined on `𝒞/U` sends an arrow of `𝒞/U` to an arrow of `𝒮` lying over its
image in `𝒞`. -/
lemma isHomLift_map_of_slice {U : 𝒞} (x : BasedCategory.slice U ⥤ᵇ BasedCategory.ofFunctor p)
    {a b : Over U} (k : a ⟶ b) : p.IsHomLift ((Over.forget U).map k) (x.map k) := by
  have hw : x.toFunctor ⋙ p = Over.forget U := x.w
  have hh := CategoryTheory.Functor.congr_hom hw k
  simp only [CategoryTheory.Functor.comp_map] at hh
  apply IsHomLift.of_fac' p ((Over.forget U).map k) (x.map k) ?ha ?hb
  case ha => simpa using CategoryTheory.Functor.congr_obj hw a
  case hb => simpa using CategoryTheory.Functor.congr_obj hw b
  · convert hh using 2

/-- `G` sends a morphism of `𝒮'` lying over `f` to a morphism of `𝒮` lying over `f`. -/
lemma isHomLift_twoYonedaComparison_map (hp : p.IsFiberedInGroupoids)
    {a b : ∫ᶜ (p.twoYonedaPresheaf hp ⋙ Grpd.forgetToCat).toPseudofunctor'} (φ : a ⟶ b) :
    p.IsHomLift (Hom.base φ) ((p.twoYonedaComparison hp).map φ) := by
  have h₁ : p.IsHomLift (𝟙 a.base) ((Hom.fiber φ).app (Over.mk (𝟙 a.base))) :=
    (Hom.fiber φ).isHomLift' (Over.mk (𝟙 a.base))
  have h₂ : p.IsHomLift (Hom.base φ)
      (sliceEv p b.fiber ((Over.map (Hom.base φ)).obj (Over.mk (𝟙 a.base)))) := by
    have h := isHomLift_map_of_slice p b.fiber (Over.mkIdTerminal.from
      ((Over.map (Hom.base φ)).obj (Over.mk (𝟙 a.base))))
    have hz : ((Over.map (Hom.base φ)).obj (Over.mk (𝟙 a.base))).hom = Hom.base φ := by simp
    rwa [forget_map_from_mkIdTerminal, hz] at h
  exact IsHomLift.comp_lift_id_left p (Hom.base φ) _ _

/-- The functor `G` is a functor over `𝒞`: its composite with `p` is the projection of the
category `𝒮'` attached to `F`. -/
@[stacks 076J]
lemma twoYonedaComparison_comp (hp : p.IsFiberedInGroupoids) :
    p.twoYonedaComparison hp ⋙ p = (presheafOfGroupoids (p.twoYonedaPresheaf hp)).p :=
  CategoryTheory.Functor.ext (fun a => BasedFunctor.w_obj a.fiber (Over.mk (𝟙 a.base)))
    (fun _ _ φ => by
      have := isHomLift_twoYonedaComparison_map p hp φ
      exact IsHomLift.fac' p (Hom.base φ) _)

/-- The fibre of `G` over `U`, read through the identification of `𝒮'_U` with `F(U)` that the
Grothendieck construction provides, is the evaluation functor of the 2-Yoneda lemma. -/
lemma inducedFunctor_comp_mapOfComp (hp : p.IsFiberedInGroupoids) (U : 𝒞) :
    Fiber.inducedFunctor (CoGrothendieck.comp_const
        (p.twoYonedaPresheaf hp ⋙ Grpd.forgetToCat).toPseudofunctor' U) ⋙
      Fiber.mapOfComp (CoGrothendieck.forget _) p (p.twoYonedaComparison hp)
        (twoYonedaComparison_comp p hp) U =
      twoYonedaEvaluation p U := by
  refine CategoryTheory.Functor.ext (fun x => rfl) (fun x y ν => ?_)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Fiber.hom_ext
  change ((CoGrothendieck.ι _ U).map ν).fiber.app (Over.mk (𝟙 U)) ≫
      sliceEv p y ((Over.map ((CoGrothendieck.ι _ U).map ν).base).obj (Over.mk (𝟙 U)))
    = ν.app (Over.mk (𝟙 U))
  erw [BasedFunctor.comp_app]
  rw [Category.assoc]
  erw [id_fiber_app_comp_sliceEv p hp ⟨U, y⟩, Category.comp_id]

/-- Each fibre of `G` is an equivalence. -/
lemma isEquivalence_mapOfComp (hp : p.IsFiberedInGroupoids) (U : 𝒞) :
    (Fiber.mapOfComp (CoGrothendieck.forget _) p (p.twoYonedaComparison hp)
      (twoYonedaComparison_comp p hp) U).IsEquivalence := by
  have : (Fiber.inducedFunctor (CoGrothendieck.comp_const
      (p.twoYonedaPresheaf hp ⋙ Grpd.forgetToCat).toPseudofunctor' U) ⋙
      Fiber.mapOfComp (CoGrothendieck.forget _) p (p.twoYonedaComparison hp)
        (twoYonedaComparison_comp p hp) U).IsEquivalence := by
    rw [inducedFunctor_comp_mapOfComp p hp U]; exact twoYonedaEvaluation_isEquivalence p hp U
  exact CategoryTheory.Functor.isEquivalence_of_comp_left
    (Fiber.inducedFunctor (CoGrothendieck.comp_const
      (p.twoYonedaPresheaf hp ⋙ Grpd.forgetToCat).toPseudofunctor' U)) _

/-- The functor `G : 𝒮' ⥤ 𝒮` is an equivalence of categories. -/
theorem twoYonedaComparison_isEquivalence (hp : p.IsFiberedInGroupoids) :
    (p.twoYonedaComparison hp).IsEquivalence :=
  (IsFiberedInGroupoids.isEquivalence_iff_forall_fiber (CoGrothendieck.forget _) p
      (isFiberedInGroupoids_presheafOfGroupoids (p.twoYonedaPresheaf hp)) hp
      (p.twoYonedaComparison hp) (twoYonedaComparison_comp p hp)).mpr
    (isEquivalence_mapOfComp p hp)

/-- The functor `G` is an equivalence in the 2-category of categories fibred in groupoids over
`𝒞`: it admits a quasi-inverse which is again a functor over `𝒞`, and the unit and counit have
all their components lying over identity morphisms of `𝒞`. -/
@[stacks 076J]
theorem twoYonedaComparison_isEquivalenceOver (hp : p.IsFiberedInGroupoids) :
    ∃ (H : 𝒮 ⥤ (presheafOfGroupoids (p.twoYonedaPresheaf hp)).obj)
      (_ : H ⋙ (presheafOfGroupoids (p.twoYonedaPresheaf hp)).p = p)
      (η : p.twoYonedaComparison hp ⋙ H ≅ 𝟭 _)
      (ε : H ⋙ p.twoYonedaComparison hp ≅ 𝟭 _),
      (∀ a, (presheafOfGroupoids (p.twoYonedaPresheaf hp)).p.IsHomLift
          (𝟙 ((presheafOfGroupoids (p.twoYonedaPresheaf hp)).p.obj a)) (η.hom.app a)) ∧
      (∀ z, p.IsHomLift (𝟙 (p.obj z)) (ε.hom.app z)) :=
  IsFiberedInGroupoids.isEquivalence_over (CoGrothendieck.forget _) p
    (isFiberedInGroupoids_presheafOfGroupoids (p.twoYonedaPresheaf hp)) hp
    (p.twoYonedaComparison hp) (twoYonedaComparison_comp p hp)
    (twoYonedaComparison_isEquivalence p hp)

end Functor

end CategoryTheory
