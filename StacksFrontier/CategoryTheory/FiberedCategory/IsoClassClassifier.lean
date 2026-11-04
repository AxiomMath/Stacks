module

public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct

/-!
# Identifying the presheaf of isomorphism classes through a classifying map

Let `p : 𝒮 ⥤ 𝒞` be a fibred category and `F` a presheaf of sets on `𝒞`.  A *classifier* of `p`
by `F` assigns to every object of the fibre over `U` a section of `F` over `U`, in such a way that
a morphism of `𝒮` lying over `f : V ⟶ U` relates the section of its source to the restriction
along `f` of the section of its target, two objects of one fibre with the same section are
isomorphic in that fibre, and every section is attained.  Such a classifier identifies the
presheaf of isomorphism classes `\overline{𝒮}` of `p` naturally with `F`.

## Main definitions

* `CategoryTheory.Functor.IsoClassClassifier`: a classifier of `p` by `F`.
* `CategoryTheory.Functor.IsoClassClassifier.equiv`: the resulting bijections
  `\overline{𝒮}(U) ≃ F(U)`.

## Main results

* `CategoryTheory.Functor.IsoClassClassifier.equiv_naturality`: the bijections are natural.
* `CategoryTheory.TwoFibreProductOver.structureFunctor_isFiberedInSetoids`: a 2-fibre product
  of two categories fibred in setoids over a category fibred in groupoids is fibred in setoids,
  whatever the category over which the product is taken.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Opposite

universe w v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮] (p : 𝒮 ⥤ 𝒞)
  (F : 𝒞ᵒᵖ ⥤ Type w)

/-- **A classifier of a fibred category by a presheaf of sets**: a section of `F` attached to every
object of every fibre, compatible with the morphisms of `𝒮`, injective up to isomorphism in the
fibre and surjective. -/
structure IsoClassClassifier where
  /-- The section of `F` classified by an object of the fibre over `U`. -/
  cls : ∀ U : 𝒞, p.Fiber U → F.obj (op U)
  /-- A morphism lying over `f : V ⟶ U` relates the two sections by restriction along `f`. -/
  cls_map : ∀ {V U : 𝒞} (f : V ⟶ U) (x' : p.Fiber V) (x : p.Fiber U) (φ : x'.1 ⟶ x.1),
    p.IsHomLift f φ → cls V x' = F.map f.op (cls U x)
  /-- Two objects of one fibre classifying the same section are isomorphic in that fibre. -/
  injective : ∀ (U : 𝒞) (x y : p.Fiber U), cls U x = cls U y → Nonempty (x ≅ y)
  /-- Every section is classified by an object. -/
  surjective : ∀ (U : 𝒞) (s : F.obj (op U)), ∃ x : p.Fiber U, cls U x = s

namespace IsoClassClassifier

variable {p F} (c : IsoClassClassifier p F)

/-- The classifier is constant on the isomorphism classes of a fibre. -/
theorem cls_eq_of_iso {U : 𝒞} {x y : p.Fiber U} (e : x ≅ y) : c.cls U x = c.cls U y := by
  have h := c.cls_map (𝟙 U) x y e.hom.1 e.hom.2
  rwa [op_id, F.map_id, types_id_apply] at h

/-- The map from isomorphism classes to sections induced by a classifier. -/
def toFun (U : 𝒞) : _root_.Quotient (isIsomorphicSetoid (p.Fiber U)) → F.obj (op U) :=
  _root_.Quotient.lift (c.cls U) fun _ _ h =>
    c.cls_eq_of_iso ((isIsomorphicSetoid_r_iff _ _).1 h).some

/-- The map induced by a classifier sends the isomorphism class of an object `x` to the section
classified by `x`. -/
theorem toFun_isoClassMk {U : 𝒞} (x : p.Fiber U) : c.toFun U (isoClassMk p x) = c.cls U x :=
  rfl

/-- **The bijection between isomorphism classes and sections induced by a classifier.** -/
noncomputable def equiv [p.IsFibered] (U : 𝒞ᵒᵖ) : p.isoClassPresheaf.obj U ≃ F.obj U :=
  Equiv.ofBijective (c.toFun U.unop)
    ⟨fun a b hab => by
      induction a using _root_.Quotient.ind with
      | _ x =>
        induction b using _root_.Quotient.ind with
        | _ y => exact (isoClassMk_eq_iff x y).2 (c.injective _ x y hab),
     fun s => by
      obtain ⟨x, hx⟩ := c.surjective U.unop s
      exact ⟨isoClassMk p x, hx⟩⟩

/-- The bijection induced by a classifier sends the isomorphism class of an object `x` to the
section classified by `x`. -/
theorem equiv_isoClassMk [p.IsFibered] {U : 𝒞} (x : p.Fiber U) :
    c.equiv (op U) (isoClassMk p x) = c.cls U x :=
  rfl

/-- **The bijections induced by a classifier are natural.** -/
theorem equiv_naturality [p.IsFibered] {U V : 𝒞ᵒᵖ} (f : U ⟶ V)
    (a : p.isoClassPresheaf.obj U) :
    c.equiv V (p.isoClassPresheaf.map f a) = F.map f (c.equiv U a) := by
  induction a using _root_.Quotient.ind with
  | _ x =>
    show c.cls V.unop (pullbackFiber p x f.unop) = F.map f.unop.op (c.cls U.unop x)
    exact c.cls_map f.unop _ x (IsPreFibered.pullbackMap x.2 f.unop) inferInstance

end IsoClassClassifier

end CategoryTheory.Functor

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]

/-- **A 2-fibre product of two categories fibred in setoids is fibred in setoids**, over any
category fibred in groupoids: a morphism of the 2-fibre product is determined by its two
components, and each of those is the unique morphism over the common base morphism. -/
theorem structureFunctor_isFiberedInSetoids (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞)
    (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) (h𝒳 : p𝒳.IsFiberedInSetoids) (h𝒴 : p𝒴.IsFiberedInSetoids)
    (h𝒮 : p𝒮.IsFiberedInGroupoids) (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) :
    (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsFiberedInSetoids where
  isFiberedInGroupoids := isFiberedInGroupoids p𝒳 p𝒴 p𝒮 F G h𝒳.isFiberedInGroupoids
    h𝒴.isFiberedInGroupoids h𝒮 hF hG
  fiber_isThin U := by
    have := h𝒳.isFiberedInGroupoids.isFibered
    have := h𝒴.isFiberedInGroupoids.isFibered
    intro P Q
    refine ⟨fun m m' => Functor.Fiber.hom_ext ?_⟩
    have hm := m.2
    have hm' := m'.2
    have hb : m.1.hbase = m'.1.hbase := by
      have e := IsHomLift.fac' (structureFunctor p𝒳 p𝒴 p𝒮 F G) (𝟙 U) m.1
      have e' := IsHomLift.fac' (structureFunctor p𝒳 p𝒴 p𝒮 F G) (𝟙 U) m'.1
      exact e.trans e'.symm
    have ha := m.1.ha
    have hb' := m.1.hb
    have ha' : p𝒳.IsHomLift m.1.hbase m'.1.a := hb ▸ m'.1.ha
    have hbb' : p𝒴.IsHomLift m.1.hbase m'.1.b := hb ▸ m'.1.hb
    exact Hom.ext hb
      (Functor.hom_unique_of_fiber_isThin p𝒳 m.1.hbase (h𝒳.fiber_isThin _) _ _ ha ha')
      (Functor.hom_unique_of_fiber_isThin p𝒴 m.1.hbase (h𝒴.fiber_isThin _) _ _ hb' hbb')

end CategoryTheory.TwoFibreProductOver
