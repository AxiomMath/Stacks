module

public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyFunctor

/-! # Restriction along a stackification is an equivalence of morphism categories

Let `(𝒞, J)` be a site, `p : 𝒮 ⥤ 𝒞` a fibred category, `G : 𝒮 ⥤ 𝒮'` a 1-morphism exhibiting
`𝒮'` as the stackification of `𝒮` in the sense of Stacks 02ZN, and `q : 𝒳 ⥤ 𝒞` a stack.
Stacks 0435 produces, from a 1-morphism `F : 𝒮 ⥤ 𝒳` of fibred categories over `𝒞`, an extension
`H : 𝒮' ⥤ 𝒳` together with a 2-isomorphism `G ⋙ H ≅ F`. This file proves Stacks 04W9:
restriction along `G` is an *equivalence*

`Mor_{Stacks/𝒞}(𝒮', 𝒳) ≃ Mor_{Fib/𝒞}(𝒮, 𝒳)`

of morphism categories, the extension of Stacks 0435 being a quasi-inverse.

## Main definitions

* `CategoryTheory.Functor.FibredMor`, the morphism category `Mor_{Fib/𝒞}(𝒮, 𝒳)` of Stacks 02ZG:
  its objects are the 1-morphisms of fibred categories over `𝒞` and its morphisms are the
  2-morphisms, the morphisms of functors all of whose components lie over identities;
* `CategoryTheory.Functor.restrictMor`, the canonical functor
  `Mor_{Fib/𝒞}(𝒮', 𝒳) ⥤ Mor_{Fib/𝒞}(𝒮, 𝒳)` given by composition with `G`;
* `CategoryTheory.Functor.Stackification.extendTrans`, the 2-morphism `H ⟶ H'` extending a
  2-morphism `G ⋙ H ⟶ G ⋙ H'` of the restrictions;
* `CategoryTheory.Functor.Stackification.restrictEquivalence`, the equivalence of Stacks 04W9.

## Main results

* `CategoryTheory.Functor.Stackification.restrict_faithful` and
  `CategoryTheory.Functor.Stackification.restrict_full`, that restriction along `G` is fully
  faithful;
* `CategoryTheory.Functor.Stackification.restrict_essSurj`, that it is essentially surjective,
  which is Stacks 0435;
* `CategoryTheory.Functor.Stackification.restrict_isEquivalence`, that restriction along `G` is
  therefore an equivalence of categories.

## Implementation notes

Both sides of the equivalence are the same construction `CategoryTheory.Functor.FibredMor`: by
Stacks 02ZG an `i`-morphism of stacks is an `i`-morphism of fibred categories, so the morphism
category `Mor_{Stacks/𝒞}(𝒮', 𝒳)` is the morphism category of fibred categories over `𝒞` of the two
underlying fibred categories. It is *not* the hom-category of `CategoryTheory.BasedStack`: that
2-category bundles all of its objects into one pair of universes, whereas `𝒮` and `𝒳` live in
independent universes here, and `𝒮` is not assumed to be a stack.

The hypothesis "`G` exhibits `𝒮'` as the stackification of `𝒮`" is stated as the unfolded clauses
of Stacks 02ZN — local injectivity and local surjectivity of the maps of morphism presheaves, and
local essential surjectivity on fibres.

There are four independent object universes, an independent hom universe for the site, and one
hom universe shared by the total categories, the sharing being forced by
`IsFibredOneMorphism.morPresheafMap`.

## References

* [Stacks 04W9](https://stacks.math.columbia.edu/tag/04W9);
* [Stacks 0435](https://stacks.math.columbia.edu/tag/0435).
-/

@[expose] public section

namespace CategoryTheory

open Opposite

namespace Functor

/-! ### The morphism category of two fibred categories over `𝒞` -/

section MorphismCategory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
  {𝒳 : Type u₃} [Category.{v₃} 𝒳]

/-- **The morphism category `Mor_{Fib/𝒞}(𝒮, 𝒳)`**, Stacks 02ZG: an object is a 1-morphism of
fibred categories over `𝒞` from `p` to `q`, that is a functor `𝒮 ⥤ 𝒳` strictly over `𝒞` which
preserves strongly cartesian morphisms. -/
structure FibredMor (p : 𝒮 ⥤ 𝒞) (q : 𝒳 ⥤ 𝒞) where
  /-- The underlying functor. -/
  functor : 𝒮 ⥤ 𝒳
  /-- It is a 1-morphism of fibred categories over `𝒞`. -/
  isFibredOneMorphism : p.IsFibredOneMorphism q functor

namespace FibredMor

variable {p : 𝒮 ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞}

/-- An object of a morphism category lies over the object of `𝒞` it came from. -/
lemma obj_eq (K : FibredMor p q) (A : 𝒮) : q.obj (K.functor.obj A) = p.obj A :=
  Functor.congr_obj K.isFibredOneMorphism.comp_eq A

/-- **A 2-morphism of fibred categories over `𝒞`**, Stacks 02ZG (3): a morphism of the underlying
functors each of whose components lies over an identity. -/
structure Hom (K L : FibredMor p q) where
  /-- The underlying morphism of functors. -/
  trans : K.functor ⟶ L.functor
  /-- Each of its components lies over an identity. -/
  isHomLift (A : 𝒮) : q.IsHomLift (𝟙 (p.obj A)) (trans.app A)

/-- A 2-morphism is determined by the underlying morphism of functors. -/
@[ext]
lemma Hom.ext' {K L : FibredMor p q} {α β : Hom K L} (h : α.trans = β.trans) : α = β := by
  cases α; cases β; simp_all

/-- The identity 2-morphism, and the vertical composition of 2-morphisms. -/
instance category : Category (FibredMor p q) where
  Hom := Hom
  id K := ⟨𝟙 K.functor, fun A => IsHomLift.id (K.obj_eq A)⟩
  comp {K L M} α β :=
    ⟨α.trans ≫ β.trans, fun A => by
      have h1 := α.isHomLift A
      have h2 := β.isHomLift A
      have h0 : q.IsHomLift (𝟙 (p.obj A) ≫ 𝟙 (p.obj A))
        (α.trans.app A ≫ β.trans.app A) := inferInstance
      rwa [Category.comp_id] at h0⟩
  id_comp _ := Hom.ext' (Category.id_comp _)
  comp_id _ := Hom.ext' (Category.comp_id _)
  assoc _ _ _ := Hom.ext' (Category.assoc _ _ _)

/-- The underlying morphism of functors of the identity 2-morphism is the identity. -/
@[simp]
lemma id_trans (K : FibredMor p q) : (𝟙 K : K ⟶ K).trans = 𝟙 K.functor := rfl

/-- The underlying morphism of functors of a composite of 2-morphisms is the composite. -/
@[simp]
lemma comp_trans {K L M : FibredMor p q} (α : K ⟶ L) (β : L ⟶ M) :
    (α ≫ β).trans = α.trans ≫ β.trans := rfl

/-- A morphism of functors all of whose components lie over identities and which is invertible as
a morphism of functors is an isomorphism of the morphism category. -/
def isoMk {K L : FibredMor p q} (e : K.functor ≅ L.functor)
    (he : ∀ A : 𝒮, q.IsHomLift (𝟙 (p.obj A)) (e.hom.app A)) : K ≅ L where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, fun A => by
    have h : q.IsHomLift (𝟙 (p.obj A)) (e.app A).hom := he A
    rw [← Iso.app_inv]
    exact IsHomLift.lift_id_inv q (p.obj A) (e.app A)⟩
  hom_inv_id := Hom.ext' e.hom_inv_id
  inv_hom_id := Hom.ext' e.inv_hom_id

end FibredMor

end MorphismCategory

/-! ### Restriction along a 1-morphism -/

section Restrict

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
  {𝒮' : Type u₃} [Category.{v₃} 𝒮'] {𝒳 : Type u₄} [Category.{v₄} 𝒳]
  {p : 𝒮 ⥤ 𝒞} {p' : 𝒮' ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'}

/-- **Restriction along a 1-morphism `G` of fibred categories over `𝒞`**: the functor
`Mor_{Fib/𝒞}(𝒮', 𝒳) ⥤ Mor_{Fib/𝒞}(𝒮, 𝒳)` sending a 1-morphism `H` to `G ⋙ H` and a 2-morphism
to its left whiskering by `G`. For a stackification `G` this is the functor of Stacks 04W9. -/
def restrictMor (hG : p.IsFibredOneMorphism p' G) : FibredMor p' q ⥤ FibredMor p q where
  obj H := ⟨G ⋙ H.functor, hG.comp H.isFibredOneMorphism⟩
  map {H H'} α :=
    ⟨Functor.whiskerLeft G α.trans, fun A => by
      have heq : p'.obj (G.obj A) = p.obj A := Functor.congr_obj hG.comp_eq A
      have h := α.isHomLift (G.obj A)
      rwa [heq] at h⟩
  map_id _ := FibredMor.Hom.ext' rfl
  map_comp _ _ := FibredMor.Hom.ext' rfl

/-- Restriction along `G` sends a 1-morphism `H` to `G ⋙ H`. -/
@[simp]
lemma restrictMor_obj_functor (hG : p.IsFibredOneMorphism p' G) (H : FibredMor p' q) :
    ((restrictMor (q := q) hG).obj H).functor = G ⋙ H.functor := rfl

/-- Restriction along `G` sends a 2-morphism to its left whiskering by `G`. -/
@[simp]
lemma restrictMor_map_trans (hG : p.IsFibredOneMorphism p' G) {H H' : FibredMor p' q}
    (α : H ⟶ H') : ((restrictMor (q := q) hG).map α).trans = Functor.whiskerLeft G α.trans := rfl

end Restrict

/-! ### The image of a local presentation under a 1-morphism -/

section MapFiber

universe vb v u₁ u₂ u₃

-- `Functor.Fiber` and its inclusion are Mathlib definitions that are not implicit-reducible;
-- the composites below cross from a fibre into the total category through them.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒴 : Type u₂} [Category.{v} 𝒴] {𝒳 : Type u₃}
  [Category.{v} 𝒳] {r : 𝒴 ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} [r.IsFibered] [q.IsFibered] {K : 𝒴 ⥤ 𝒳}

namespace LocalPresentation

variable (hK : r.IsFibredOneMorphism q K) {U : 𝒞} {x : r.Fiber U} {R : Sieve U}
  (P : LocalPresentation r x R)

/-- **The image of a local presentation under a 1-morphism of fibred categories.** A 1-morphism
`K` carries a local presentation of `x` to a local presentation of `K x`: the presenting objects
are the images of the presenting objects, and the cartesian morphisms are the images of the
cartesian morphisms, which are cartesian because `K` preserves strongly cartesian morphisms. -/
@[implicit_reducible]
noncomputable def mapFiber : LocalPresentation q ((fiberFunctorOfCompEq hK.comp_eq U).obj x) R where
  obj := fun ⦃V⦄ f hf => (fiberFunctorOfCompEq hK.comp_eq V).obj (P.obj f hf)
  iso := fun ⦃_V⦄ f hf =>
    have : q.IsStronglyCartesian f (K.map (P.mor f hf)) :=
      hK.map_isStronglyCartesian f (P.mor f hf) (P.isStronglyCartesian_mor f hf)
    fiberIsoOfCartesian f (K.map (P.mor f hf))
      (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hK.comp_eq U).obj x).2 f) inferInstance
      (IsPreFibered.pullbackMap.IsCartesian _ _)

/-- The presenting objects of the image of a local presentation are the images of the presenting
objects. -/
@[simp]
lemma mapFiber_obj ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) :
    (P.mapFiber hK).obj f hf = (fiberFunctorOfCompEq hK.comp_eq V).obj (P.obj f hf) := rfl

/-- The cartesian morphisms of the image of a local presentation are the images of the cartesian
morphisms. -/
@[simp]
lemma mapFiber_mor ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) :
    (P.mapFiber hK).mor f hf = K.map (P.mor f hf) := by
  rw [mor]
  exact fiberIsoOfCartesian_hom_fac _ _ _ _ _

omit [q.IsFibered] in
include hK in
/-- The image of a cartesian morphism of a local presentation is cartesian. -/
lemma isCartesian_map_mor ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) :
    q.IsCartesian f (K.map (P.mor f hf)) :=
  have : q.IsStronglyCartesian f (K.map (P.mor f hf)) :=
    hK.map_isStronglyCartesian f (P.mor f hf) (P.isStronglyCartesian_mor f hf)
  inferInstance

/-- **The comparison of the presenting objects of the image.** It is the image of the comparison
of the presenting objects, read through the comparison
`IsFibredOneMorphism.mapPullbackFiberIso` of `K` on chosen pullbacks. -/
lemma mapFiber_isoAlong ⦃V W : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U}
    (hb : γ ≫ f = b) (hb' : R.arrows b) :
    ((P.mapFiber hK).isoAlong hf γ hb hb').hom =
      (hK.mapPullbackFiberIso (P.obj f hf) γ).hom ≫
        (fiberFunctorOfCompEq hK.comp_eq W).map (P.isoAlong hf γ hb hb').hom := by
  refine fiber_hom_ext_of_cartesian b (K.map (P.mor b hb'))
    (P.isCartesian_map_mor hK b hb') _ _ ?_
  have key := (P.mapFiber hK).isoAlong_hom_fac hf γ hb hb'
  rw [mapFiber_mor, mapFiber_mor] at key
  rw [key, Fiber.fiberInclusion.map_comp, Category.assoc,
    fiberInclusion_map_fiberFunctorOfCompEq_map, ← K.map_comp, isoAlong_hom_fac, K.map_comp,
    ← Category.assoc, IsFibredOneMorphism.mapPullbackFiberIso_hom_fac]

/-! #### Reading a morphism of a fibre through two local presentations -/

section Compare

omit [r.IsFibered]

variable {z y : q.Fiber U} (Pq : LocalPresentation q z R) (Qq : LocalPresentation q y R)

/-- **A morphism of the fibre, read through two local presentations.** If the base change of
`m : z ⟶ y` along a member of the sieve is the morphism `w` of the presenting objects, conjugated
by the two identifications with the chosen pullbacks, then `m` intertwines the cartesian morphisms
of the two presentations with `w`. -/
lemma mor_comp_of_pullbackFiberHom_eq (m : z ⟶ y) ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f)
    (w : Pq.obj f hf ⟶ Qq.obj f hf)
    (hw : pullbackFiberHom m f = (Pq.iso f hf).inv ≫ w ≫ (Qq.iso f hf).hom) :
    Pq.mor f hf ≫ Fiber.fiberInclusion.map m =
      Fiber.fiberInclusion.map w ≫ Qq.mor f hf := by
  rw [mor, mor, Category.assoc, ← pullbackFiberHom_fac m f, hw]
  simp only [Fiber.fiberInclusion.map_comp, Category.assoc]
  rw [← Category.assoc (Fiber.fiberInclusion.map (Pq.iso f hf).hom),
    ← Fiber.fiberInclusion.map_comp, Iso.hom_inv_id, Fiber.fiberInclusion.map_id,
    Category.id_comp]

/-- **The comparison of the presenting objects against the identification at a refinement.** This
is `CategoryTheory.Functor.LocalPresentation.iso_inv_eq` solved for the identification at the
refined member of the sieve. -/
lemma isoAlong_comp_iso_hom ⦃V W : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U}
    (hb : γ ≫ f = b) (hb' : R.arrows b) :
    (Pq.isoAlong hf γ hb hb').hom ≫ (Pq.iso b hb').hom =
      pullbackFiberHom (Pq.iso f hf).hom γ ≫ (pullbackFiberCompIso' z f γ b hb).hom := by
  have key : pullbackFiberHom (Pq.iso f hf).hom γ ≫
      (pullbackFiberCompIso' z f γ b hb).hom ≫ (Pq.iso b hb').inv =
      (Pq.isoAlong hf γ hb hb').hom := by
    rw [Pq.iso_inv_eq hf γ hb hb']
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, pullbackFiberHom_hom_inv_id, Category.id_comp]
  rw [← key]
  simp [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **A morphism of a fibre glued from a compatible family of morphisms of the presenting
objects.** Let `z` and `y` be objects of the fibre of `𝒳` over `U`, presented along one and the
same covering sieve, and let `w` be a family of morphisms of the presenting objects compatible
with the comparisons `CategoryTheory.Functor.LocalPresentation.isoAlong` along a refinement. Then
there is a morphism `z ⟶ y` of the fibre whose restriction along the cartesian morphisms of the
presentations is `w`. -/
theorem exists_hom_of_family {J : GrothendieckTopology 𝒞} {z y : q.Fiber U} {R : Sieve U}
    (Pq : LocalPresentation q z R) (Qq : LocalPresentation q y R) (hmor : IsMorSheaf q J U z y)
    (hR : R ∈ J U)
    (w : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f), Pq.obj f hf ⟶ Qq.obj f hf)
    (hw : ∀ ⦃V W : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) (γ : W ⟶ V) (b : W ⟶ U) (hb : γ ≫ f = b)
      (hb' : R.arrows b),
      (Pq.isoAlong hf γ hb hb').hom ≫ w b hb' =
        pullbackFiberHom (w f hf) γ ≫ (Qq.isoAlong hf γ hb hb').hom) :
    ∃ m : z ⟶ y, ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
      Pq.mor f hf ≫ Fiber.fiberInclusion.map m =
        Fiber.fiberInclusion.map (w f hf) ≫ Qq.mor f hf := by
  have hcompat : ∀ ⦃V W : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) (γ : W ⟶ V) (b : W ⟶ U)
      (hb : γ ≫ f = b) (hb' : R.arrows b),
      (Pq.iso b hb').inv ≫ w b hb' ≫ (Qq.iso b hb').hom =
        (pullbackFiberCompIso' z f γ b hb).inv ≫
          pullbackFiberHom ((Pq.iso f hf).inv ≫ w f hf ≫ (Qq.iso f hf).hom) γ ≫
          (pullbackFiberCompIso' y f γ b hb).hom := by
    intro V W f hf γ b hb hb'
    rw [Pq.iso_inv_eq hf γ hb hb', pullbackFiberHom_comp, pullbackFiberHom_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hw f hf γ b hb hb', Qq.isoAlong_comp_iso_hom hf γ hb hb']
  obtain ⟨m, hm⟩ := exists_fiberHom_of_locally q hmor hR
    (fun ⦃_V⦄ f hf => (Pq.iso f hf).inv ≫ w f hf ≫ (Qq.iso f hf).hom) hcompat
  exact ⟨m, fun ⦃_V⦄ f hf =>
    Pq.mor_comp_of_pullbackFiberHom_eq Qq m f hf (w f hf) (hm f hf)⟩

end Compare

end LocalPresentation

end MapFiber

/-! ### The comparison of chosen pullbacks along a composite of two 1-morphisms -/

section CompComparison

universe vb v u₁ u₂ u₃ u₄

-- `Functor.Fiber` and its inclusion are Mathlib definitions that are not implicit-reducible;
-- the composites below cross from a fibre into the total category through them.
attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒮 : Type u₂} [Category.{v} 𝒮] {𝒮' : Type u₃}
  [Category.{v} 𝒮'] {𝒳 : Type u₄} [Category.{v} 𝒳]
  {p : 𝒮 ⥤ 𝒞} {p' : 𝒮' ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'} {K : 𝒮' ⥤ 𝒳}
  [p.IsFibered] [p'.IsFibered] [q.IsFibered]

namespace IsFibredOneMorphism

variable (hG : p.IsFibredOneMorphism p' G) (hK : p'.IsFibredOneMorphism q K)

/-- **The comparison of the chosen pullbacks along a composite of two 1-morphisms**: in the fibre
of `𝒳` over `V`, between the chosen pullback of `K (G a)` along `f` and `K (G (f^* a))`. It is the
comparison `IsFibredOneMorphism.mapPullbackFiberIso` of `K` at `G a`, followed by the image
under `K` of the comparison of `G` at `a`. -/
noncomputable def compPullbackFiberIso {U : 𝒞} (a : p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    pullbackFiber q ((fiberFunctorOfCompEq hK.comp_eq U).obj
        ((fiberFunctorOfCompEq hG.comp_eq U).obj a)) f ≅
      (fiberFunctorOfCompEq hK.comp_eq V).obj
        ((fiberFunctorOfCompEq hG.comp_eq V).obj (pullbackFiber p a f)) :=
  hK.mapPullbackFiberIso ((fiberFunctorOfCompEq hG.comp_eq U).obj a) f ≪≫
    (fiberFunctorOfCompEq hK.comp_eq V).mapIso (hG.mapPullbackFiberIso a f)

/-- The `hom` component of `IsFibredOneMorphism.compPullbackFiberIso`. -/
lemma compPullbackFiberIso_hom_eq {U : 𝒞} (a : p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    (hG.compPullbackFiberIso hK a f).hom =
      (hK.mapPullbackFiberIso ((fiberFunctorOfCompEq hG.comp_eq U).obj a) f).hom ≫
        (fiberFunctorOfCompEq hK.comp_eq V).map (hG.mapPullbackFiberIso a f).hom := rfl

/-- The `inv` component of `IsFibredOneMorphism.compPullbackFiberIso`. -/
lemma compPullbackFiberIso_inv_eq {U : 𝒞} (a : p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    (hG.compPullbackFiberIso hK a f).inv =
      (fiberFunctorOfCompEq hK.comp_eq V).map (hG.mapPullbackFiberIso a f).inv ≫
        (hK.mapPullbackFiberIso ((fiberFunctorOfCompEq hG.comp_eq U).obj a) f).inv := rfl

/-- The comparison of the chosen pullbacks along a composite, composed with the image of the image
of the chosen cartesian lift, is the chosen cartesian lift. -/
@[reassoc (attr := simp)]
lemma compPullbackFiberIso_hom_fac {U : 𝒞} (a : p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    Fiber.fiberInclusion.map (hG.compPullbackFiberIso hK a f).hom ≫
        K.map (G.map (IsPreFibered.pullbackMap a.2 f)) =
      IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hK.comp_eq U).obj
        ((fiberFunctorOfCompEq hG.comp_eq U).obj a)).2 f := by
  rw [compPullbackFiberIso_hom_eq, Fiber.fiberInclusion.map_comp, Category.assoc,
    fiberInclusion_map_fiberFunctorOfCompEq_map, ← K.map_comp, mapPullbackFiberIso_hom_fac,
    mapPullbackFiberIso_hom_fac]

/-- The inverse form of `IsFibredOneMorphism.compPullbackFiberIso_hom_fac`. -/
@[reassoc (attr := simp)]
lemma compPullbackFiberIso_inv_fac {U : 𝒞} (a : p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    Fiber.fiberInclusion.map (hG.compPullbackFiberIso hK a f).inv ≫
        IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hK.comp_eq U).obj
          ((fiberFunctorOfCompEq hG.comp_eq U).obj a)).2 f =
      K.map (G.map (IsPreFibered.pullbackMap a.2 f)) := by
  rw [compPullbackFiberIso_inv_eq, Fiber.fiberInclusion.map_comp, Category.assoc,
    mapPullbackFiberIso_inv_fac, fiberInclusion_map_fiberFunctorOfCompEq_map, ← K.map_comp,
    mapPullbackFiberIso_inv_fac]

/-- **The image under `K` of a morphism between images under `G`, against base change.** Where a
morphism `θ : G a ⟶ G b` of a fibre of `𝒮'` is the image under `G` of a section `u` of
`Mor(a, b)`, the base change along `f` of its image under `K` is the image under `K ∘ G` of `u`,
conjugated by the comparisons
`IsFibredOneMorphism.compPullbackFiberIso`. -/
lemma pullbackFiberHom_map_of_morMapAt {U : 𝒞} {a b : p.Fiber U}
    (θ : (fiberFunctorOfCompEq hG.comp_eq U).obj a ⟶ (fiberFunctorOfCompEq hG.comp_eq U).obj b)
    {V : 𝒞} (f : V ⟶ U) (u : pullbackFiber p a f ⟶ pullbackFiber p b f)
    (hu : hG.morMapAt a b f u = pullbackFiberHom θ f) :
    pullbackFiberHom ((fiberFunctorOfCompEq hK.comp_eq U).map θ) f =
      (hG.compPullbackFiberIso hK a f).hom ≫
        (fiberFunctorOfCompEq hK.comp_eq V).map ((fiberFunctorOfCompEq hG.comp_eq V).map u) ≫
        (hG.compPullbackFiberIso hK b f).inv := by
  rw [← hK.morMapAt_pullbackFiberHom θ f, ← hu, morMapAt_def, morMapAt_def, Functor.map_comp,
    Functor.map_comp, compPullbackFiberIso_hom_eq, compPullbackFiberIso_inv_eq]
  simp [Category.assoc]

end IsFibredOneMorphism

end CompComparison

/-! ### Restriction along a stackification -/

section Uniqueness

universe vb v u₁ u₂ u₃ u₄

-- The chosen pullbacks, the fibre inclusion and the induced functor on fibres are semireducible,
-- so the endpoints of the composites below agree only once they unfold.
set_option backward.isDefEq.respectTransparency false

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒮 : Type u₂} [Category.{v} 𝒮] {𝒮' : Type u₃}
  [Category.{v} 𝒮'] {𝒳 : Type u₄} [Category.{v} 𝒳] {J : GrothendieckTopology 𝒞}
  {p : 𝒮 ⥤ 𝒞} {p' : 𝒮' ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'}
  [p.IsFibered] [p'.IsFibered] [q.IsFibered]

namespace Stackification

variable (hG : p.IsFibredOneMorphism p' G)
  (hmor : ∀ (U : 𝒞) (x y : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap x y))
  (hqmor : ∀ (U : 𝒞) (x y : q.Fiber U), IsMorSheaf q J U x y)
  (hobj : ∀ (U : 𝒞) (x' : p'.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
    (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x' f))
  (hdesc : HasEffectiveDescent q J)

/-! #### The chosen local presentation of an object of `𝒮'`

Clause (2) of Stacks 02ZN presents every object of a fibre of `𝒮'`, along a covering sieve, by
objects of `𝒮`. We choose such a presentation at each object. -/

section ChosenPresentation

/-- The covering sieve along which clause (2) of Stacks 02ZN presents an object of a fibre of
`𝒮'` by objects of `𝒮`. -/
noncomputable def locSieve {U : 𝒞} (x' : p'.Fiber U) : Sieve U := (hobj U x').choose

omit [p.IsFibered] in
/-- The chosen sieve is a covering sieve. -/
lemma locSieve_mem {U : 𝒞} (x' : p'.Fiber U) : locSieve hG hobj x' ∈ J U :=
  (hobj U x').choose_spec.1

omit [p.IsFibered] in
/-- At every member of the chosen sieve, the chosen pullback of `x'` is isomorphic to the image
under `G` of an object of a fibre of `𝒮`. -/
lemma exists_locObj {U : 𝒞} (x' : p'.Fiber U) ⦃V : 𝒞⦄ (f : V ⟶ U)
    (hf : (locSieve hG hobj x').arrows f) :
    ∃ z : p.Fiber V,
      Nonempty ((fiberFunctorOfCompEq hG.comp_eq V).obj z ≅ pullbackFiber p' x' f) :=
  (hobj U x').choose_spec.2 hf

/-- The object of `𝒮` presenting `x'` at a member of the chosen covering sieve. -/
noncomputable def locObj {U : 𝒞} (x' : p'.Fiber U) ⦃V : 𝒞⦄ (f : V ⟶ U)
    (hf : (locSieve hG hobj x').arrows f) : p.Fiber V :=
  (exists_locObj hG hobj x' f hf).choose

/-- Its image under `G` is the chosen pullback of `x'`. -/
noncomputable def locIso {U : 𝒞} (x' : p'.Fiber U) ⦃V : 𝒞⦄ (f : V ⟶ U)
    (hf : (locSieve hG hobj x').arrows f) :
    (fiberFunctorOfCompEq hG.comp_eq V).obj (locObj hG hobj x' f hf) ≅
      pullbackFiber p' x' f :=
  (exists_locObj hG hobj x' f hf).choose_spec.some

/-- **The chosen local presentation of an object of a fibre of `𝒮'`**, by the images under `G` of
the chosen local objects of `𝒮`. -/
noncomputable def locPres {U : 𝒞} (x' : p'.Fiber U) :
    LocalPresentation p' x' (locSieve hG hobj x') :=
  presG hG (locObj hG hobj x') (locIso hG hobj x')

end ChosenPresentation

/-- An object of `𝒮'`, read as an object of the fibre over its image. -/
abbrev selfFiber' (X : 𝒮') : p'.Fiber (p'.obj X) := Fiber.mk rfl

omit [p.IsFibered] in
include hqmor hobj in
/-- **Restriction along a stackification is faithful.** Two 2-morphisms `H ⟶ H'` of `𝒮' ⥤ 𝒳` that
agree on the image of `G` are equal. -/
theorem restrict_faithful : (restrictMor (q := q) hG).Faithful where
  map_injective {H H'} α β hαβ := by
    have happ : ∀ A : 𝒮, α.trans.app (G.obj A) = β.trans.app (G.obj A) := fun A =>
      NatTrans.congr_app (congrArg FibredMor.Hom.trans hαβ) A
    refine FibredMor.Hom.ext' ?_
    ext X
    refine LocalPresentation.hom_ext_of_locally
      ((locPres hG hobj (selfFiber' X)).mapFiber H.isFibredOneMorphism)
      (x' := (fiberFunctorOfCompEq H'.isFibredOneMorphism.comp_eq (p'.obj X)).obj (selfFiber' X))
      (hqmor (p'.obj X)) (locSieve_mem hG hobj _) (fun ⦃_V⦄ ⦃_g⦄ hg => hg)
      (α.isHomLift X) (β.isHomLift X) ?_
    intro V g hg
    rw [LocalPresentation.mapFiber_mor]
    have hα : H.functor.map ((locPres hG hobj (selfFiber' X)).mor g hg) ≫ α.trans.app X =
        α.trans.app (G.obj (locObj hG hobj (selfFiber' X) g hg).1) ≫
          H'.functor.map ((locPres hG hobj (selfFiber' X)).mor g hg) :=
      α.trans.naturality _
    have hβ : H.functor.map ((locPres hG hobj (selfFiber' X)).mor g hg) ≫ β.trans.app X =
        β.trans.app (G.obj (locObj hG hobj (selfFiber' X) g hg).1) ≫
          H'.functor.map ((locPres hG hobj (selfFiber' X)).mor g hg) :=
      β.trans.naturality _
    rw [hα, hβ, happ]

include hmor hqmor hobj hdesc in
/-- **Restriction along a stackification is essentially surjective.** This is Stacks 0435: every
1-morphism `F : 𝒮 ⥤ 𝒳` of fibred categories over `𝒞` into a stack extends to a 1-morphism
`H : 𝒮' ⥤ 𝒳` together with a 2-isomorphism `G ⋙ H ≅ F`. -/
theorem restrict_essSurj : (restrictMor (q := q) hG).EssSurj where
  mem_essImage F :=
    ⟨⟨extend hG F.isFibredOneMorphism hmor hqmor hobj hdesc,
        extend_isFibredOneMorphism hG F.isFibredOneMorphism hmor hqmor hobj hdesc⟩,
      ⟨FibredMor.isoMk (unit hG F.isFibredOneMorphism hmor hqmor hobj hdesc)
        (isHomLift_unit_app hG F.isFibredOneMorphism hmor hqmor hobj hdesc)⟩⟩

/-! #### The 2-morphism extending a 2-morphism of the restrictions

Let `H` and `H'` be 1-morphisms `𝒮' ⥤ 𝒳` of fibred categories over `𝒞` and let
`τ : G ⋙ H ⟶ G ⋙ H'` be a 2-morphism of their restrictions. The components of `τ` glue to a
2-morphism `H ⟶ H'` whose left whiskering by `G` is `τ`. -/

section Fullness

variable {H H' : 𝒮' ⥤ 𝒳} (hH : p'.IsFibredOneMorphism q H) (hH' : p'.IsFibredOneMorphism q H')
  (τ : G ⋙ H ⟶ G ⋙ H') (hτ : ∀ A : 𝒮, q.IsHomLift (𝟙 (p.obj A)) (τ.app A))

/-- The component of `τ` at an object of a fibre of `𝒮`, read as a morphism of the fibre of `𝒳`
over the same object of `𝒞`. -/
def transFib {U : 𝒞} (a : p.Fiber U) :
    (fiberFunctorOfCompEq hH.comp_eq U).obj ((fiberFunctorOfCompEq hG.comp_eq U).obj a) ⟶
      (fiberFunctorOfCompEq hH'.comp_eq U).obj ((fiberFunctorOfCompEq hG.comp_eq U).obj a) :=
  ⟨τ.app a.1, by
    have h := hτ a.1
    rwa [a.2] at h⟩

omit [p.IsFibered] [p'.IsFibered] [q.IsFibered] in
/-- The component `transFib`, as a morphism of the total category, is the component of `τ`. -/
@[simp]
lemma fiberInclusion_map_transFib {U : 𝒞} (a : p.Fiber U) :
    Fiber.fiberInclusion.map (transFib hG hH hH' τ hτ a) = τ.app a.1 := rfl

omit [p.IsFibered] [p'.IsFibered] [q.IsFibered] in
/-- The components are natural for the morphisms of the fibres of `𝒮`. -/
@[reassoc]
lemma transFib_naturality {U : 𝒞} {a b : p.Fiber U} (m : a ⟶ b) :
    (fiberFunctorOfCompEq hH.comp_eq U).map ((fiberFunctorOfCompEq hG.comp_eq U).map m) ≫
        transFib hG hH hH' τ hτ b =
      transFib hG hH hH' τ hτ a ≫
        (fiberFunctorOfCompEq hH'.comp_eq U).map ((fiberFunctorOfCompEq hG.comp_eq U).map m) :=
  Fiber.hom_ext (τ.naturality (Fiber.fiberInclusion.map m))

/-- **The components against base change.** The base change of the component at `a` along `f` is
the component at the chosen pullback of `a`, conjugated by the comparisons
`IsFibredOneMorphism.compPullbackFiberIso`. -/
lemma pullbackFiberHom_transFib {U : 𝒞} (a : p.Fiber U) {V : 𝒞} (f : V ⟶ U) :
    pullbackFiberHom (transFib hG hH hH' τ hτ a) f =
      (hG.compPullbackFiberIso hH a f).hom ≫
        transFib hG hH hH' τ hτ (pullbackFiber p a f) ≫
        (hG.compPullbackFiberIso hH' a f).inv := by
  have hnat : H.map (G.map (IsPreFibered.pullbackMap a.2 f)) ≫ τ.app a.1 =
      τ.app (pullbackFiber p a f).1 ≫ H'.map (G.map (IsPreFibered.pullbackMap a.2 f)) :=
    τ.naturality _
  refine fiber_hom_ext_of_cartesian f
    (IsPreFibered.pullbackMap ((fiberFunctorOfCompEq hH'.comp_eq U).obj
      ((fiberFunctorOfCompEq hG.comp_eq U).obj a)).2 f)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  rw [pullbackFiberHom_fac]
  simp only [Fiber.fiberInclusion.map_comp, Category.assoc, fiberInclusion_map_transFib,
    IsFibredOneMorphism.compPullbackFiberIso_inv_fac]
  rw [← hnat, ← Category.assoc, IsFibredOneMorphism.compPullbackFiberIso_hom_fac]

include hmor hqmor in
/-- **The components are natural for every morphism of a fibre of `𝒮'` between images under
`G`.** -/
lemma transFib_naturality_of_hom {U : 𝒞} {a b : p.Fiber U}
    (θ : (fiberFunctorOfCompEq hG.comp_eq U).obj a ⟶ (fiberFunctorOfCompEq hG.comp_eq U).obj b) :
    (fiberFunctorOfCompEq hH.comp_eq U).map θ ≫ transFib hG hH hH' τ hτ b =
      transFib hG hH hH' τ hτ a ≫ (fiberFunctorOfCompEq hH'.comp_eq U).map θ := by
  obtain ⟨R, hR, hlift⟩ := exists_covering_lift hG hmor θ
  refine eq_of_pullbackFiberHom_locally_eq q (hqmor U _ _) hR ?_
  intro V f hf
  obtain ⟨u, hu⟩ := hlift f hf
  rw [pullbackFiberHom_comp, pullbackFiberHom_comp,
    hG.pullbackFiberHom_map_of_morMapAt hH θ f u hu,
    hG.pullbackFiberHom_map_of_morMapAt hH' θ f u hu,
    pullbackFiberHom_transFib, pullbackFiberHom_transFib]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [transFib_naturality_assoc]

include hmor hqmor in
/-- **The components against a refinement of a local presentation.** For the images under `H`
and `H'` of a local presentation of an object of `𝒮'` by objects of `𝒮`, the components of `τ`
at the presenting objects are compatible with the comparisons
`CategoryTheory.Functor.LocalPresentation.isoAlong` along a refinement. -/
lemma isoAlong_comp_transFib {U : 𝒞} {x' : p'.Fiber U} {R : Sieve U}
    (s : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R.arrows f → p.Fiber V)
    (φ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
      (fiberFunctorOfCompEq hG.comp_eq V).obj (s f hf) ≅ pullbackFiber p' x' f)
    ⦃V W : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) (γ : W ⟶ V) (b : W ⟶ U) (hb : γ ≫ f = b)
    (hb' : R.arrows b) :
    (((presG hG s φ).mapFiber hH).isoAlong hf γ hb hb').hom ≫
        transFib hG hH hH' τ hτ (s b hb') =
      pullbackFiberHom (transFib hG hH hH' τ hτ (s f hf)) γ ≫
        (((presG hG s φ).mapFiber hH').isoAlong hf γ hb hb').hom := by
  have hnat := transFib_naturality_of_hom hG hmor hqmor hH hH' τ hτ
    ((hG.mapPullbackFiberIso (s f hf) γ).inv ≫ ((presG hG s φ).isoAlong hf γ hb hb').hom)
  rw [Functor.map_comp, Functor.map_comp] at hnat
  have hcancel : (fiberFunctorOfCompEq hH.comp_eq W).map
        ((presG hG s φ).isoAlong hf γ hb hb').hom ≫ transFib hG hH hH' τ hτ (s b hb') =
      (fiberFunctorOfCompEq hH.comp_eq W).map (hG.mapPullbackFiberIso (s f hf) γ).hom ≫
        transFib hG hH hH' τ hτ (pullbackFiber p (s f hf) γ) ≫
        (fiberFunctorOfCompEq hH'.comp_eq W).map (hG.mapPullbackFiberIso (s f hf) γ).inv ≫
        (fiberFunctorOfCompEq hH'.comp_eq W).map
          ((presG hG s φ).isoAlong hf γ hb hb').hom := by
    calc (fiberFunctorOfCompEq hH.comp_eq W).map ((presG hG s φ).isoAlong hf γ hb hb').hom ≫
          transFib hG hH hH' τ hτ (s b hb')
        = ((fiberFunctorOfCompEq hH.comp_eq W).map (hG.mapPullbackFiberIso (s f hf) γ).hom ≫
            (fiberFunctorOfCompEq hH.comp_eq W).map (hG.mapPullbackFiberIso (s f hf) γ).inv) ≫
            (fiberFunctorOfCompEq hH.comp_eq W).map
              ((presG hG s φ).isoAlong hf γ hb hb').hom ≫
            transFib hG hH hH' τ hτ (s b hb') := by
          rw [map_hom_comp_map_inv, Category.id_comp]
      _ = (fiberFunctorOfCompEq hH.comp_eq W).map (hG.mapPullbackFiberIso (s f hf) γ).hom ≫
            ((fiberFunctorOfCompEq hH.comp_eq W).map (hG.mapPullbackFiberIso (s f hf) γ).inv ≫
              (fiberFunctorOfCompEq hH.comp_eq W).map
                ((presG hG s φ).isoAlong hf γ hb hb').hom) ≫
            transFib hG hH hH' τ hτ (s b hb') := by
          simp [Category.assoc]
      _ = _ := by rw [hnat]
  have hcan2 : (hH'.mapPullbackFiberIso ((fiberFunctorOfCompEq hG.comp_eq V).obj (s f hf)) γ).inv ≫
      (hH'.mapPullbackFiberIso ((presG hG s φ).obj f hf) γ).hom = 𝟙 _ :=
    (hH'.mapPullbackFiberIso ((presG hG s φ).obj f hf) γ).inv_hom_id
  rw [LocalPresentation.mapFiber_isoAlong, LocalPresentation.mapFiber_isoAlong,
    pullbackFiberHom_transFib, IsFibredOneMorphism.compPullbackFiberIso_hom_eq,
    IsFibredOneMorphism.compPullbackFiberIso_inv_eq]
  simp only [Category.assoc]
  rw [hcancel, reassoc_of% hcan2]
  rfl

include hmor hqmor hobj hH hH' hτ in
/-- **The component at an object of `𝒮'` of the 2-morphism extending `τ`.** There is a morphism
`H X ⟶ H' X` over the identity whose restriction along the chosen presentation of `X` is given by
the components of `τ` at the presenting objects. -/
lemma exists_transComponent (X : 𝒮') :
    ∃ m : H.obj X ⟶ H'.obj X, q.IsHomLift (𝟙 (p'.obj X)) m ∧
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ p'.obj X) (hf : (locSieve hG hobj (selfFiber' X)).arrows f),
        H.map ((locPres hG hobj (selfFiber' X)).mor f hf) ≫ m =
          τ.app (locObj hG hobj (selfFiber' X) f hf).1 ≫
            H'.map ((locPres hG hobj (selfFiber' X)).mor f hf) := by
  obtain ⟨m, hm⟩ := LocalPresentation.exists_hom_of_family
    ((locPres hG hobj (selfFiber' X)).mapFiber hH)
    ((locPres hG hobj (selfFiber' X)).mapFiber hH')
    (hqmor (p'.obj X) _ _) (locSieve_mem hG hobj (selfFiber' X))
    (fun ⦃_V⦄ f hf => transFib hG hH hH' τ hτ (locObj hG hobj (selfFiber' X) f hf))
    (fun ⦃_V _W⦄ f hf γ b hb hb' =>
      isoAlong_comp_transFib hG hmor hqmor hH hH' τ hτ (locObj hG hobj (selfFiber' X))
        (locIso hG hobj (selfFiber' X)) f hf γ b hb hb')
  refine ⟨Fiber.fiberInclusion.map m, m.2, ?_⟩
  intro V f hf
  have h := hm f hf
  rwa [LocalPresentation.mapFiber_mor, LocalPresentation.mapFiber_mor,
    fiberInclusion_map_transFib] at h

include hmor hqmor hobj hH hH' hτ in
/-- **The 2-morphism extending `τ`, on objects.** -/
noncomputable def transComponent (X : 𝒮') : H.obj X ⟶ H'.obj X :=
  (exists_transComponent hG hmor hqmor hobj hH hH' τ hτ X).choose

include hmor hqmor hobj hH hH' hτ in
/-- The component `transComponent` lies over the identity. -/
lemma isHomLift_transComponent (X : 𝒮') :
    q.IsHomLift (𝟙 (p'.obj X)) (transComponent hG hmor hqmor hobj hH hH' τ hτ X) :=
  (exists_transComponent hG hmor hqmor hobj hH hH' τ hτ X).choose_spec.1

include hmor hqmor hobj hH hH' hτ in
/-- The local characterization of the component: along the chosen presentation of `X` it is the
component of `τ` at the presenting object. -/
lemma transComponent_spec (X : 𝒮') ⦃V : 𝒞⦄ (f : V ⟶ p'.obj X)
    (hf : (locSieve hG hobj (selfFiber' X)).arrows f) :
    H.map ((locPres hG hobj (selfFiber' X)).mor f hf) ≫
        transComponent hG hmor hqmor hobj hH hH' τ hτ X =
      τ.app (locObj hG hobj (selfFiber' X) f hf).1 ≫
        H'.map ((locPres hG hobj (selfFiber' X)).mor f hf) :=
  (exists_transComponent hG hmor hqmor hobj hH hH' τ hτ X).choose_spec.2 f hf

include hmor hqmor hobj hH hH' hτ in
/-- **The component against a morphism out of an image under `G` lying over a member of the chosen
sieve.** -/
lemma transComponent_spec_of_mem {W : 𝒞} (w : p.Fiber W) (Y : 𝒮') {h : W ⟶ p'.obj Y}
    (hh : (locSieve hG hobj (selfFiber' Y)).arrows h) (χ : G.obj w.1 ⟶ Y)
    (hχ : p'.IsHomLift h χ) :
    H.map χ ≫ transComponent hG hmor hqmor hobj hH hH' τ hτ Y = τ.app w.1 ≫ H'.map χ := by
  obtain ⟨κ, hfac⟩ : ∃ κ : (fiberFunctorOfCompEq hG.comp_eq W).obj w ⟶
      (locPres hG hobj (selfFiber' Y)).obj h hh,
      Fiber.fiberInclusion.map κ ≫ (locPres hG hobj (selfFiber' Y)).mor h hh = χ := by
    have hcart := (locPres hG hobj (selfFiber' Y)).isCartesian_mor h hh
    have := hχ
    exact ⟨⟨IsCartesian.map p' h ((locPres hG hobj (selfFiber' Y)).mor h hh) χ, inferInstance⟩,
      IsCartesian.fac p' h _ χ⟩
  rw [← hfac, H.map_comp, H'.map_comp, Category.assoc,
    transComponent_spec hG hmor hqmor hobj hH hH' τ hτ Y h hh, ← Category.assoc, ← Category.assoc]
  congr 1
  exact congrArg Fiber.fiberInclusion.map
    (transFib_naturality_of_hom hG hmor hqmor hH hH' τ hτ κ)

omit [q.IsFibered] in
/-- The cartesian morphism of the tautological presentation of `G a` by the chosen pullbacks of
`a` is the image under `G` of the chosen cartesian lift. -/
@[simp]
lemma presG_pullbackPresentation_mor {U : 𝒞} (a : p.Fiber U) (R : Sieve U) ⦃V : 𝒞⦄ (f : V ⟶ U)
    (hf : R.arrows f) :
    (presG hG (pullbackObjects a R) (pullbackPresentation hG a R)).mor f hf =
      G.map (IsPreFibered.pullbackMap a.2 f) := by
  rw [LocalPresentation.mor]
  exact hG.mapPullbackFiberIso_inv_fac a f

include hmor hqmor hobj hH hH' hτ in
/-- **The component against an arbitrary morphism out of an image under `G`.** -/
lemma transComponent_spec_of_hom {U : 𝒞} (a : p.Fiber U) (Y : 𝒮') (fb : U ⟶ p'.obj Y)
    (χ : G.obj a.1 ⟶ Y) (hχ : p'.IsHomLift fb χ) :
    H.map χ ≫ transComponent hG hmor hqmor hobj hH hH' τ hτ Y = τ.app a.1 ≫ H'.map χ := by
  have := hχ
  have hR₀ : Sieve.pullback fb (locSieve hG hobj (selfFiber' Y)) ∈ J U :=
    J.pullback_stable fb (locSieve_mem hG hobj (selfFiber' Y))
  have hL : q.IsHomLift fb (H.map χ ≫ transComponent hG hmor hqmor hobj hH hH' τ hτ Y) := by
    have h1 : q.IsHomLift fb (H.map χ) := isHomLift_map_of_comp_eq hH.comp_eq fb χ
    have h2 := isHomLift_transComponent hG hmor hqmor hobj hH hH' τ hτ Y
    infer_instance
  have hRt : q.IsHomLift fb (τ.app a.1 ≫ H'.map χ) := by
    have h1 : q.IsHomLift (𝟙 U) (τ.app a.1) := (transFib hG hH hH' τ hτ a).2
    have h2 : q.IsHomLift fb (H'.map χ) := isHomLift_map_of_comp_eq hH'.comp_eq fb χ
    infer_instance
  refine LocalPresentation.hom_ext_of_locally
    ((presG hG (pullbackObjects a ⊤) (pullbackPresentation hG a ⊤)).mapFiber hH)
    (x' := (fiberFunctorOfCompEq hH'.comp_eq (p'.obj Y)).obj (selfFiber' Y))
    (hqmor U) hR₀ (fun ⦃_V⦄ ⦃_g⦄ _ => trivial) hL hRt ?_
  intro V g hg
  have hnat : H.map (G.map (IsPreFibered.pullbackMap a.2 g)) ≫ τ.app a.1 =
      τ.app (pullbackFiber p a g).1 ≫ H'.map (G.map (IsPreFibered.pullbackMap a.2 g)) :=
    τ.naturality _
  have hpb : p.IsHomLift g (IsPreFibered.pullbackMap a.2 g) := inferInstance
  have hpb' : p'.IsHomLift g (G.map (IsPreFibered.pullbackMap a.2 g)) :=
    isHomLift_map_of_comp_eq hG.comp_eq g (IsPreFibered.pullbackMap a.2 g)
  rw [LocalPresentation.mapFiber_mor, presG_pullbackPresentation_mor, ← Category.assoc,
    ← Category.assoc, ← H.map_comp, hnat, Category.assoc, ← H'.map_comp]
  exact transComponent_spec_of_mem hG hmor hqmor hobj hH hH' τ hτ (pullbackFiber p a g) Y hg
    (G.map (IsPreFibered.pullbackMap a.2 g) ≫ χ) inferInstance

include hmor hqmor hobj hH hH' hτ in
/-- `CategoryTheory.Functor.Stackification.transComponent_spec_of_hom` at an object of `𝒮`
rather than at an object of a fibre. -/
lemma transComponent_spec_of_map {U : 𝒞} (A : 𝒮) (hA : p.obj A = U) (Y : 𝒮')
    (fb : U ⟶ p'.obj Y) (χ : G.obj A ⟶ Y) (hχ : p'.IsHomLift fb χ) :
    H.map χ ≫ transComponent hG hmor hqmor hobj hH hH' τ hτ Y = τ.app A ≫ H'.map χ :=
  transComponent_spec_of_hom hG hmor hqmor hobj hH hH' τ hτ (Fiber.mk hA) Y fb χ hχ

include hmor hqmor hobj hH hH' hτ in
/-- **The components are natural.** -/
lemma transComponent_naturality {X Y : 𝒮'} (ψ : X ⟶ Y) :
    H.map ψ ≫ transComponent hG hmor hqmor hobj hH hH' τ hτ Y =
      transComponent hG hmor hqmor hobj hH hH' τ hτ X ≫ H'.map ψ := by
  have hψ : p'.IsHomLift (p'.map ψ) ψ := inferInstance
  have hL : q.IsHomLift (p'.map ψ)
      (H.map ψ ≫ transComponent hG hmor hqmor hobj hH hH' τ hτ Y) := by
    have h1 : q.IsHomLift (p'.map ψ) (H.map ψ) := isHomLift_map_of_comp_eq hH.comp_eq _ ψ
    have h2 := isHomLift_transComponent hG hmor hqmor hobj hH hH' τ hτ Y
    infer_instance
  have hRt : q.IsHomLift (p'.map ψ)
      (transComponent hG hmor hqmor hobj hH hH' τ hτ X ≫ H'.map ψ) := by
    have h1 := isHomLift_transComponent hG hmor hqmor hobj hH hH' τ hτ X
    have h2 : q.IsHomLift (p'.map ψ) (H'.map ψ) := isHomLift_map_of_comp_eq hH'.comp_eq _ ψ
    infer_instance
  refine LocalPresentation.hom_ext_of_locally
    ((locPres hG hobj (selfFiber' X)).mapFiber hH)
    (x' := (fiberFunctorOfCompEq hH'.comp_eq (p'.obj Y)).obj (selfFiber' Y))
    (hqmor (p'.obj X)) (locSieve_mem hG hobj (selfFiber' X)) (fun ⦃_V⦄ ⦃_g⦄ hg => hg) hL hRt ?_
  intro V g hg
  have hcart : p'.IsStronglyCartesian g ((locPres hG hobj (selfFiber' X)).mor g hg) :=
    (locPres hG hobj (selfFiber' X)).isStronglyCartesian_mor g hg
  rw [LocalPresentation.mapFiber_mor, ← Category.assoc, ← Category.assoc,
    transComponent_spec hG hmor hqmor hobj hH hH' τ hτ X g hg, ← H.map_comp, Category.assoc,
    ← H'.map_comp]
  exact transComponent_spec_of_hom hG hmor hqmor hobj hH hH' τ hτ
    (locObj hG hobj (selfFiber' X) g hg) Y (g ≫ p'.map ψ)
    ((locPres hG hobj (selfFiber' X)).mor g hg ≫ ψ) inferInstance

include hmor hqmor hobj hH hH' hτ in
/-- **The 2-morphism `H ⟶ H'` extending a 2-morphism `τ : G ⋙ H ⟶ G ⋙ H'` of the
restrictions.** -/
noncomputable def extendTrans : H ⟶ H' where
  app := transComponent hG hmor hqmor hobj hH hH' τ hτ
  naturality _ _ ψ := transComponent_naturality hG hmor hqmor hobj hH hH' τ hτ ψ

include hmor hqmor hobj hH hH' hτ in
/-- The components of the extended 2-morphism lie over identities. -/
lemma isHomLift_extendTrans_app (X : 𝒮') :
    q.IsHomLift (𝟙 (p'.obj X)) ((extendTrans hG hmor hqmor hobj hH hH' τ hτ).app X) :=
  isHomLift_transComponent hG hmor hqmor hobj hH hH' τ hτ X

include hmor hqmor hobj hH hH' hτ in
/-- **The extended 2-morphism restricts to `τ`.** -/
lemma whiskerLeft_extendTrans :
    Functor.whiskerLeft G (extendTrans hG hmor hqmor hobj hH hH' τ hτ) = τ := by
  ext A
  rw [Functor.whiskerLeft_app]
  unfold extendTrans
  have hlift : p'.IsHomLift (eqToHom (Functor.congr_obj hG.comp_eq A).symm) (𝟙 (G.obj A)) := by
    refine IsHomLift.of_fac' p' _ (𝟙 (G.obj A)) (Functor.congr_obj hG.comp_eq A) rfl ?_
    simp
  have h := transComponent_spec_of_map hG hmor hqmor hobj hH hH' τ hτ A rfl (G.obj A)
    (eqToHom (Functor.congr_obj hG.comp_eq A).symm) (𝟙 (G.obj A)) hlift
  simpa using h

end Fullness

include hmor hqmor hobj in
/-- **Restriction along a stackification is full.** A 2-morphism `G ⋙ H ⟶ G ⋙ H'` of the
restrictions extends to a 2-morphism `H ⟶ H'`. -/
theorem restrict_full : (restrictMor (q := q) hG).Full where
  map_surjective {K L} t :=
    ⟨⟨extendTrans hG hmor hqmor hobj K.isFibredOneMorphism L.isFibredOneMorphism t.trans
        t.isHomLift,
      isHomLift_extendTrans_app hG hmor hqmor hobj K.isFibredOneMorphism L.isFibredOneMorphism
        t.trans t.isHomLift⟩,
    FibredMor.Hom.ext' (whiskerLeft_extendTrans hG hmor hqmor hobj K.isFibredOneMorphism
      L.isFibredOneMorphism t.trans t.isHomLift)⟩

/-! #### The equivalence -/

include hmor hqmor hobj hdesc in
/-- **Stacks 04W9.** Restriction along a stackification `G : 𝒮 ⥤ 𝒮'` is an equivalence from the
category of 1-morphisms `𝒮' ⥤ 𝒳` of fibred categories over `𝒞` into a stack, and their
2-morphisms, onto the category of 1-morphisms `𝒮 ⥤ 𝒳` and their 2-morphisms. -/
@[stacks 04W9]
theorem restrict_isEquivalence : (restrictMor (q := q) hG).IsEquivalence where
  faithful := restrict_faithful hG hqmor hobj
  full := restrict_full hG hmor hqmor hobj
  essSurj := restrict_essSurj hG hmor hqmor hobj hdesc

include hmor hqmor hobj hdesc in
/-- **The canonical equivalence of morphism categories of Stacks 04W9**,
`Mor_{Stacks/𝒞}(𝒮', 𝒳) ≌ Mor_{Fib/𝒞}(𝒮, 𝒳)`. Its functor is restriction along the stackification
`G`, and a quasi-inverse is the extension of Stacks 0435. -/
@[stacks 04W9]
noncomputable def restrictEquivalence : FibredMor p' q ≌ FibredMor p q :=
  have := restrict_isEquivalence hG hmor hqmor hobj hdesc
  (restrictMor hG).asEquivalence

include hmor hqmor hobj hdesc in
/-- The functor of the equivalence of Stacks 04W9 is restriction along `G`. -/
@[simp]
lemma restrictEquivalence_functor :
    (restrictEquivalence hG hmor hqmor hobj hdesc).functor = restrictMor (q := q) hG := rfl

end Stackification

end Uniqueness

end Functor

end CategoryTheory
