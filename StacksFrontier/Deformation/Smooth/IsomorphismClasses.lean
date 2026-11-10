module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Skeletal
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.Basic

/-!
# The morphism to isomorphism classes

The morphism from a predeformation category to the functor of its
fibrewise isomorphism classes is smooth.

## Main definitions

* `isomorphismClassesData` constructs the covariant functor of fibrewise
  isomorphism classes and its canonical based morphism.
* `toIsomorphismClasses` is this canonical morphism.
* `specialFiberObject` is a choice of object in the special fibre of a predeformation
  category.

## Main results

* `isSmooth_toIsomorphismClasses` states that the morphism to isomorphism classes
  is smooth.

## Implementation notes

The target is specifically the category of elements of a covariant type-valued functor on the
base, whose value at each algebra is the quotient of that fibre's objects by isomorphism.
The projection takes each object to its own quotient class, and its based-functor structure
supplies naturality.

## References

* [Stacks Project, Tag 06HK](https://stacks.math.columbia.edu/tag/06HK)
* [Stacks Project, Tag 07W5](https://stacks.math.columbia.edu/tag/07W5)
-/

@[expose] public section

namespace Deformation

/-! ### The morphism to isomorphism classes is smooth -/

section
open CategoryTheory
open CategoryTheory.Functor
open Opposite
universe u v w u₁ v₁ u₂ v₂ u₃ v₃


variable {C : Type u₃} [Category.{v₃} C]

/-- An object of the fibre of `p` over `A`, as an object of the fibre of `p.op` over `op A`. -/
public def fiberToOppFiber {𝓕 : Type u₁} [Category.{v₁} 𝓕]
    {𝒞 : Type u₂} [Category.{v₂} 𝒞] (p : 𝓕 ⥤ 𝒞) (A : 𝒞)
    (x : Fiber p A) : Fiber p.op (op A) :=
  ⟨op x.1, congrArg op x.2⟩

/-- An object of the fibre of `p.op` over `op A`, as an object of the fibre of `p` over `A`. -/
public def fiberFromOppFiber {𝓕 : Type u₁} [Category.{v₁} 𝓕]
    {𝒞 : Type u₂} [Category.{v₂} 𝒞] (p : 𝓕 ⥤ 𝒞) (A : 𝒞)
    (x : Fiber p.op (op A)) : Fiber p A :=
  ⟨unop x.1, congrArg unop x.2⟩

/-- An isomorphism in the fibre of `p` over `A` induces an isomorphism between the corresponding
objects of the fibre of `p.op` over `op A`, whose forward map is the opposite of the inverse. -/
public def fiberIsoToOpp {𝓕 : Type u₁} [Category.{v₁} 𝓕]
    {𝒞 : Type u₂} [Category.{v₂} 𝒞] (p : 𝓕 ⥤ 𝒞) (A : 𝒞)
    {x y : Fiber p A} (e : x ≅ y) : fiberToOppFiber p A x ≅ fiberToOppFiber p A y := by
  refine ⟨⟨(e.inv.1).op, ?_⟩, ⟨(e.hom.1).op, ?_⟩, ?_, ?_⟩
  · have : p.IsHomLift (𝟙 A) e.inv.1 := e.inv.2
    apply IsHomLift.of_fac p.op (𝟙 (op A)) (e.inv.1).op (congrArg op x.2) (congrArg op y.2)
    simpa [op_comp, op_id] using congrArg Quiver.Hom.op
      (IsHomLift.fac p (𝟙 A) e.inv.1)
  · have : p.IsHomLift (𝟙 A) e.hom.1 := e.hom.2
    apply IsHomLift.of_fac p.op (𝟙 (op A)) (e.hom.1).op (congrArg op y.2) (congrArg op x.2)
    simpa [op_comp, op_id] using congrArg Quiver.Hom.op
      (IsHomLift.fac p (𝟙 A) e.hom.1)
  · exact Fiber.hom_ext (congrArg (fun q => (Fiber.fiberInclusion.map q).op) e.hom_inv_id)
  · exact Fiber.hom_ext (congrArg (fun q => (Fiber.fiberInclusion.map q).op) e.inv_hom_id)

/-- An isomorphism in the fibre of `p.op` over `op A` induces an isomorphism between the
corresponding objects of the fibre of `p` over `A`, whose forward map is the unopposite of the
inverse. -/
public def fiberIsoFromOpp {𝓕 : Type u₁} [Category.{v₁} 𝓕]
    {𝒞 : Type u₂} [Category.{v₂} 𝒞] (p : 𝓕 ⥤ 𝒞) (A : 𝒞)
    {x y : Fiber p.op (op A)} (e : x ≅ y) : fiberFromOppFiber p A x ≅ fiberFromOppFiber p A y := by
  refine ⟨⟨(e.inv.1).unop, ?_⟩, ⟨(e.hom.1).unop, ?_⟩, ?_, ?_⟩
  · have : p.op.IsHomLift (𝟙 (op A)) e.inv.1 := e.inv.2
    apply IsHomLift.of_fac p (𝟙 A) (e.inv.1).unop (congrArg unop x.2) (congrArg unop y.2)
    simpa [unop_comp, unop_id] using congrArg Quiver.Hom.unop
      (IsHomLift.fac p.op (𝟙 (op A)) e.inv.1)
  · have : p.op.IsHomLift (𝟙 (op A)) e.hom.1 := e.hom.2
    apply IsHomLift.of_fac p (𝟙 A) (e.hom.1).unop (congrArg unop y.2) (congrArg unop x.2)
    simpa [unop_comp, unop_id] using congrArg Quiver.Hom.unop
      (IsHomLift.fac p.op (𝟙 (op A)) e.hom.1)
  · apply Fiber.hom_ext
    change (e.inv.1).unop ≫ (e.hom.1).unop = 𝟙 _
    rw [← unop_comp]
    exact congrArg (fun q => (Fiber.fiberInclusion.map q).unop) e.hom_inv_id
  · apply Fiber.hom_ext
    change (e.hom.1).unop ≫ (e.inv.1).unop = 𝟙 _
    rw [← unop_comp]
    exact congrArg (fun q => (Fiber.fiberInclusion.map q).unop) e.inv_hom_id

/-- The isomorphism classes of the fibre of `p` over `A` are in bijection with the isomorphism
classes of the fibre of `p.op` over `op A`. -/
public noncomputable def fiberIsoClassOppEquiv {𝓕 : Type u₁} [Category.{v₁} 𝓕]
    {𝒞 : Type u₂} [Category.{v₂} 𝒞] (p : 𝓕 ⥤ 𝒞) (A : 𝒞) :
    Quotient (isIsomorphicSetoid (Fiber p A)) ≃
      Quotient (isIsomorphicSetoid (Fiber p.op (op A))) := by
  classical
  exact {
    toFun := Quotient.map (fiberToOppFiber p A) fun _ _ ⟨e⟩ => ⟨fiberIsoToOpp p A e⟩
    invFun := Quotient.map (fiberFromOppFiber p A) fun _ _ ⟨e⟩ => ⟨fiberIsoFromOpp p A e⟩
    left_inv := Quotient.ind fun _ => rfl
    right_inv := Quotient.ind fun _ => rfl }

/-- The covariant functor of fibrewise isomorphism classes of a category cofibered in groupoids:
it sends `A` to the set of isomorphism classes of the fibre over `A`, and a morphism of the base to
pushforward of classes along it. -/
public noncomputable def associatedClassesFunctor
    (𝓕 : BasedCategory.{v₁, u₁} (C))
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) :
    C ⥤ Type u₁ := by
  classical
  letI : 𝓕.p.op.IsFibered := h𝓕.isFibered
  let D := 𝓕.p.op.isoClassPresheaf
  refine {
    obj A := Quotient (isIsomorphicSetoid (Fiber 𝓕.p A))
    map := fun {A B} f => ↾fun q => (fiberIsoClassOppEquiv 𝓕.p B).symm
      (D.map f.op.op (fiberIsoClassOppEquiv 𝓕.p A q))
    map_id := ?_
    map_comp := ?_ }
  · intro A
    ext q
    change (fiberIsoClassOppEquiv 𝓕.p A).symm
      (D.map (𝟙 (op (op A))) (fiberIsoClassOppEquiv 𝓕.p A q)) = q
    simp [D]
  · intro A B C f g
    ext q
    change (fiberIsoClassOppEquiv 𝓕.p C).symm
        (D.map ((f ≫ g).op.op) (fiberIsoClassOppEquiv 𝓕.p A q)) =
      (fiberIsoClassOppEquiv 𝓕.p C).symm
        (D.map (g.op.op) (fiberIsoClassOppEquiv 𝓕.p B
          ((fiberIsoClassOppEquiv 𝓕.p B).symm
            (D.map (f.op.op) (fiberIsoClassOppEquiv 𝓕.p A q)))))
    simp [op_comp]

/-- If `g : a ⟶ b` lies over `f : A ⟶ B`, the functor of fibrewise isomorphism classes sends the
class of `a` along `f` to the class of `b`. -/
public theorem associatedClasses_map_lift
    (𝓕 : BasedCategory.{v₁, u₁} (C))
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p)
    {A B : C} (f : A ⟶ B)
    {a b : 𝓕.obj} (g : a ⟶ b) (ha : 𝓕.p.obj a = A) (hb : 𝓕.p.obj b = B)
    (hg : 𝓕.p.IsHomLift f g) :
    (associatedClassesFunctor 𝓕 h𝓕).map f
      (Quotient.mk _ (Fiber.mk ha : Fiber 𝓕.p A)) =
    Quotient.mk _ (Fiber.mk hb : Fiber 𝓕.p B) := by
  classical
  let : 𝓕.p.op.IsFibered := h𝓕.isFibered
  let x : Fiber 𝓕.p.op (op A) := fiberToOppFiber 𝓕.p A (Fiber.mk ha)
  let y : Fiber 𝓕.p.op (op B) := fiberToOppFiber 𝓕.p B (Fiber.mk hb)
  apply (fiberIsoClassOppEquiv 𝓕.p B).injective
  change (𝓕.p.op.isoClassPresheaf.map f.op.op (Functor.isoClassMk 𝓕.p.op x)) =
    Functor.isoClassMk 𝓕.p.op y
  rw [Functor.isoClassPresheaf_map_isoClassMk]
  have hlift : 𝓕.p.op.IsHomLift f.op g.op := isHomLift_op 𝓕.p f g (inst := hg)
  have hcart : 𝓕.p.op.IsCartesian f.op g.op := by
    have := h𝓕.isStronglyCartesian_homLift f.op g.op
    infer_instance
  exact (Functor.isoClassMk_eq_pullbackFiber_of_isCartesian
    (p := 𝓕.p.op) f.op x y g.op hlift hcart).symm

/-- The based functor from `𝓕` to the category of elements of its functor of fibrewise
isomorphism classes, sending each object to its own isomorphism class. -/
public noncomputable def associatedProjection
    (𝓕 : BasedCategory.{v₁, u₁} (C))
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) :
    BasedFunctor 𝓕 (BasedCategory.ofFunctor
      (Functor.Elements.π (associatedClassesFunctor 𝓕 h𝓕))) := by
  classical
  let F := associatedClassesFunctor 𝓕 h𝓕
  refine {
    toFunctor := {
      obj := fun a => Functor.elementsMk F (𝓕.p.obj a)
        (Quotient.mk _ (Fiber.mk rfl : Fiber 𝓕.p (𝓕.p.obj a)))
      map := fun {a b} f => Functor.Elements.homMk (𝓕.p.map f)
        (associatedClasses_map_lift 𝓕 h𝓕 (𝓕.p.map f) f rfl rfl (by infer_instance))
      map_id a := Functor.Elements.hom_ext (𝓕.p.map_id a)
      map_comp f g := Functor.Elements.hom_ext (𝓕.p.map_comp f g) }
    w := rfl }

/-- A fibre of the projection from the category of elements of a type-valued functor has at most
one morphism between any two objects. -/
public theorem elementsFiber_isThin {𝒞 : Type u₂} [Category.{v₂} 𝒞]
    (F : 𝒞 ⥤ Type u₁) (A : 𝒞) :
    Quiver.IsThin (Fiber (Functor.Elements.π F) A) := by
  refine fun x y => ⟨fun f g => Fiber.hom_ext (Functor.Elements.hom_ext ?_)⟩
  have : (Functor.Elements.π F).IsHomLift (𝟙 A) f.1 := f.2
  have : (Functor.Elements.π F).IsHomLift (𝟙 A) g.1 := g.2
  exact (IsHomLift.fac' (Functor.Elements.π F) (𝟙 A) f.1).trans
    (IsHomLift.fac' (Functor.Elements.π F) (𝟙 A) g.1).symm

/-- Isomorphic objects of a fibre of the projection from the category of elements of a
type-valued functor are equal. -/
public theorem elementsFiber_skeletal {𝒞 : Type u₂} [Category.{v₂} 𝒞]
    (F : 𝒞 ⥤ Type u₁) (A : 𝒞) : Skeletal (Fiber (Functor.Elements.π F) A) := by
  rintro ⟨@⟨X, q⟩, hx⟩ ⟨@⟨Y, r⟩, hy⟩ ⟨e⟩
  change X = A at hx
  change Y = A at hy
  subst X Y
  have : (Functor.Elements.π F).IsHomLift (𝟙 A) e.hom.1 := e.hom.2
  have hbase : (e.hom.1).hom = 𝟙 A := by
    simpa [Functor.Elements.π] using IsHomLift.fac' (Functor.Elements.π F) (𝟙 A) e.hom.1
  obtain rfl : q = r := by simpa [hbase] using (e.hom.1).map_val
  rfl

/-- The element of `F.obj A` represented by an object of the fibre over `A` of the category of
elements of `F`. -/
public def elementsFiberValue {𝒞 : Type u₂} [Category.{v₂} 𝒞]
    (F : 𝒞 ⥤ Type u₁) (A : 𝒞)
    (z : Fiber (Functor.Elements.π F) A) : F.obj A :=
  F.map (eqToHom z.2) z.1.val

/-- Two objects of the fibre over `A` of the category of elements of `F` that represent the same
element of `F.obj A` are isomorphic. -/
public theorem elementsFiberIsoOfValueEq {𝒞 : Type u₂} [Category.{v₂} 𝒞]
    (F : 𝒞 ⥤ Type u₁) (A : 𝒞)
    (z z' : Fiber (Functor.Elements.π F) A)
    (h : elementsFiberValue F A z = elementsFiberValue F A z') : Nonempty (z ≅ z') := by
  rcases z with ⟨@⟨X, x⟩, hx⟩
  rcases z' with ⟨@⟨Y, y⟩, hy⟩
  change X = A at hx
  change Y = A at hy
  let e : X ≅ Y := eqToIso (hx.trans hy.symm)
  have he : F.map e.hom x = y := by
    change F.map (eqToHom hx) x = F.map (eqToHom hy) y at h
    calc
      F.map e.hom x = F.map (eqToHom hy.symm) (F.map (eqToHom hx) x) := by
        simp [e]
      _ = F.map (eqToHom hy.symm) (F.map (eqToHom hy) y) := by rw [← h]
      _ = y := by simp
  let i : (Functor.elementsMk F X x) ≅ Functor.elementsMk F Y y :=
    Functor.Elements.isoMk (F := F) e he
  have hi : (Functor.Elements.π F).IsHomLift (𝟙 A) i.hom := by
    apply IsHomLift.of_fac (Functor.Elements.π F) (𝟙 A) i.hom hx hy
    simp [i, e, Functor.Elements.π]
  have hii : (Functor.Elements.π F).IsHomLift (𝟙 A) i.inv := by
    apply IsHomLift.of_fac (Functor.Elements.π F) (𝟙 A) i.inv hy hx
    simp [i, e, Functor.Elements.π]
  exact ⟨{
    hom := ⟨i.hom, hi⟩
    inv := ⟨i.inv, hii⟩
    hom_inv_id := Fiber.hom_ext i.hom_inv_id
    inv_hom_id := Fiber.hom_ext i.inv_hom_id }⟩

/-- The functor induced by a based functor on the strict fibre over `A`. -/
public def fiberFunctor
    {𝓕 : BasedCategory.{v₁, u₁} (C)}
    {𝓖 : BasedCategory.{v₂, u₂} (C)}
    (φ : BasedFunctor 𝓕 𝓖) (A : C) :
    Fiber 𝓕.p A ⥤ Fiber 𝓖.p A :=
  Fiber.inducedFunctor (F := Fiber.fiberInclusion ⋙ φ.toFunctor) (by
    rw [Functor.assoc, φ.w, Fiber.fiberInclusion_comp_eq_const])

/-- The image of an object `x` of the fibre over `A` under the projection to the category of
elements of the functor of isomorphism classes represents the isomorphism class of `x`. -/
public theorem associatedProjection_fiberValue
    (𝓕 : BasedCategory.{v₁, u₁} (C))
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p)
    (A : C) (x : Fiber 𝓕.p A) :
    elementsFiberValue (associatedClassesFunctor 𝓕 h𝓕) A
      ((fiberFunctor (associatedProjection 𝓕 h𝓕) A).obj x) =
    Quotient.mk _ x := by
  rcases x with ⟨a, ha⟩
  dsimp [elementsFiberValue, fiberFunctor, associatedProjection]
  change (associatedClassesFunctor 𝓕 h𝓕).map (eqToHom ha)
      (Quotient.mk _ (Fiber.mk rfl : Fiber 𝓕.p (𝓕.p.obj a))) =
    Quotient.mk _ (Fiber.mk ha : Fiber 𝓕.p A)
  exact associatedClasses_map_lift 𝓕 h𝓕 (eqToHom ha) (𝟙 a) rfl ha
    (IsHomLift.of_fac 𝓕.p (eqToHom ha) (𝟙 a) rfl ha (by simp))

/-- A based functor realizes the associated functor of isomorphism classes when it is full,
is essentially surjective on each fibre, and each target fibre is a discrete category whose
objects identify precisely the isomorphism classes in the corresponding source fibre. -/
public structure IsIsomorphismClasses
    {𝓕 : BasedCategory.{v₁, u₁} (C)}
    {𝓖 : BasedCategory.{v₂, u₂} (C)}
    (φ : BasedFunctor 𝓕 𝓖) : Prop where
  /-- The source is a category cofibered in groupoids, as in the construction of the
  associated functor of isomorphism classes. -/
  source_cofibered : IsCofiberedInGroupoids 𝓕.p
  /-- Every arrow between isomorphism classes is represented by an arrow upstairs. -/
  full : φ.toFunctor.Full
  /-- Every object in a target fibre is represented by an object of the source fibre. -/
  fiber_essSurj : ∀ A, (fiberFunctor φ A).EssSurj
  /-- A fibre of the functor of isomorphism classes has at most one arrow between two objects. -/
  fiber_thin : ∀ A, Quiver.IsThin (Fiber 𝓖.p A)
  /-- Isomorphic objects in a target fibre are equal. -/
  fiber_skeletal : ∀ A, Skeletal (Fiber 𝓖.p A)
  /-- The object map has exactly the equivalence relation given by isomorphism in each fibre. -/
  obj_eq_iff_isomorphic : ∀ A (x x' : Fiber 𝓕.p A),
    (fiberFunctor φ A).obj x = (fiberFunctor φ A).obj x' ↔ Nonempty (x ≅ x')

/-- The functor of fibrewise isomorphism classes together with its canonical map from the
cofibered category. The target is its category of elements, so its base-change maps are those
of the isomorphism-class functor itself. -/
public structure IsomorphismClassesData
    (𝓕 : BasedCategory.{v₁, u₁} (C)) where
  /-- The covariant functor sending an Artinian algebra to isomorphism classes in its fibre. -/
  classes : (C) ⥤ Type u₁
  /-- The canonical map into the category of elements of `classes`. -/
  projection : BasedFunctor 𝓕
    (BasedCategory.ofFunctor (Functor.Elements.π classes))
  /-- At each base object, the value is the quotient of the fibre by isomorphism. -/
  classes_eq : ∀ A, classes.obj A =
    Quotient (isIsomorphicSetoid (Fiber 𝓕.p A))
  /-- The projection sends each object to its own isomorphism class. -/
  projection_obj : ∀ (a : 𝓕.obj),
    cast (classes_eq (𝓕.p.obj a))
      (cast (congrArg classes.obj (projection.w_obj a)) (projection.obj a).2) =
        Quotient.mk (isIsomorphicSetoid (Fiber 𝓕.p (𝓕.p.obj a)))
          (Fiber.mk rfl : Fiber 𝓕.p (𝓕.p.obj a))
  /-- Its fibres are exactly the isomorphism-class quotients. -/
  quotient : IsIsomorphismClasses projection

/-- The functor of fibrewise isomorphism classes of a category cofibered in groupoids, together
with its canonical projection, as `IsomorphismClassesData`. -/
public noncomputable def isomorphismClassesData
    (𝓕 : BasedCategory.{v₁, u₁} (C))
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) : IsomorphismClassesData 𝓕 := by
  classical
  let F := associatedClassesFunctor 𝓕 h𝓕
  let φ := associatedProjection 𝓕 h𝓕
  refine ⟨F, φ, fun A => rfl, fun a => rfl, ?_⟩
  · refine {
      source_cofibered := h𝓕
      full := {
        map_surjective := by
          intro a b g
          let f := g.hom
          let : 𝓕.p.op.IsFibered := h𝓕.isFibered
          obtain ⟨c, qop, hcart⟩ :=
            IsPreFibered.exists_isCartesian 𝓕.p.op (by rfl) f.op
          let d : 𝓕.obj := unop c
          let q : a ⟶ d := qop.unop
          have hcartI : 𝓕.p.op.IsCartesian f.op qop := hcart
          have : 𝓕.p.op.IsHomLift f.op qop := hcartI.toIsHomLift
          have hdom := IsHomLift.domain_eq 𝓕.p.op f.op qop
          have hd : 𝓕.p.obj d = 𝓕.p.obj b := by
            simpa [d, φ, associatedProjection, Functor.op] using congrArg unop hdom
          have hq : 𝓕.p.IsHomLift f q := by
            apply IsHomLift.of_fac 𝓕.p f q rfl hd
            simpa [q, d, Functor.op, op_comp, op_id] using
              congrArg Quiver.Hom.unop (IsHomLift.fac 𝓕.p.op f.op qop)
          have hclassg : F.map f
              (Quotient.mk _ (Fiber.mk rfl : Fiber 𝓕.p (𝓕.p.obj a))) =
              Quotient.mk _ (Fiber.mk rfl : Fiber 𝓕.p (𝓕.p.obj b)) :=
            g.map_val
          have hclassq := associatedClasses_map_lift 𝓕 h𝓕 f q rfl hd hq
          have hclass :
              Quotient.mk (isIsomorphicSetoid (Fiber 𝓕.p (𝓕.p.obj b)))
                (Fiber.mk hd : Fiber 𝓕.p (𝓕.p.obj b)) =
              Quotient.mk (isIsomorphicSetoid (Fiber 𝓕.p (𝓕.p.obj b)))
                (Fiber.mk rfl : Fiber 𝓕.p (𝓕.p.obj b)) :=
            hclassq.symm.trans hclassg
          obtain ⟨e⟩ := (Functor.isoClassMk_eq_iff
            (Fiber.mk hd : Fiber 𝓕.p (𝓕.p.obj b))
            (Fiber.mk rfl : Fiber 𝓕.p (𝓕.p.obj b))).1 hclass
          let eArrow : d ⟶ b := Fiber.fiberInclusion.map e.hom
          let candidate : a ⟶ b := q ≫ eArrow
          have hcandidate : 𝓕.p.IsHomLift f candidate := by
            have : 𝓕.p.IsHomLift (𝟙 (𝓕.p.obj b)) eArrow := e.hom.2
            exact IsHomLift.comp_lift_id_right' 𝓕.p f q (𝓕.p.obj b) eArrow
          refine ⟨candidate, ?_⟩
          apply Functor.Elements.hom_ext
          let G := Functor.Elements.π F
          let fG : G.obj (φ.obj a) ⟶ G.obj (φ.obj b) := f
          have : 𝓕.p.IsHomLift fG candidate := hcandidate
          have : G.IsHomLift fG (φ.toFunctor.map candidate) :=
            BasedFunctor.preserves_isHomLift φ fG candidate
          have : G.IsHomLift fG g := by
            simpa [fG, G, f, Functor.Elements.π] using
              (CategoryTheory.IsHomLift.map G g)
          have h1 := IsHomLift.eq_of_isHomLift G fG (φ.toFunctor.map candidate)
          have h2 := IsHomLift.eq_of_isHomLift G fG g
          simpa [G, Functor.Elements.π] using h1.symm.trans h2 }
      fiber_essSurj := fun A => {
        mem_essImage := by
          intro z
          let q := elementsFiberValue F A z
          obtain ⟨x, hx⟩ := Functor.isoClassMk_surjective (p := 𝓕.p) q
          exact ⟨x, elementsFiberIsoOfValueEq F A _ _
            ((associatedProjection_fiberValue 𝓕 h𝓕 A x).trans hx)⟩ }
      fiber_thin := fun A => elementsFiber_isThin F A
      fiber_skeletal := fun A => elementsFiber_skeletal F A
      obj_eq_iff_isomorphic := by
        intro A x y
        refine ⟨fun heq => ?_, fun ⟨e⟩ => elementsFiber_skeletal F A ⟨(fiberFunctor φ A).mapIso e⟩⟩
        have hq := congrArg (elementsFiberValue F A) heq
        rw [associatedProjection_fiberValue 𝓕 h𝓕 A x,
          associatedProjection_fiberValue 𝓕 h𝓕 A y] at hq
        exact (Functor.isoClassMk_eq_iff x y).1 hq }

/-- The canonical morphism from a cofibered category to its associated functor of
isomorphism classes. -/
public noncomputable abbrev toIsomorphismClasses
    (𝓕 : BasedCategory.{v₁, u₁} (C))
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) :
    BasedFunctor 𝓕 (BasedCategory.ofFunctor
      (Functor.Elements.π (isomorphismClassesData 𝓕 h𝓕).classes)) :=
  (isomorphismClassesData 𝓕 h𝓕).projection

/-- The canonical morphism from a category cofibered in groupoids to its associated functor of
isomorphism classes is smooth. -/
@[stacks 06HK]
public theorem isSmooth_toIsomorphismClasses
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k))
    (h𝓕 : IsCofiberedInGroupoids 𝓕.p) :
    IsSmooth (toIsomorphismClasses 𝓕 h𝓕) := by
  classical
  intro B A f hf y x g hg
  let data := isomorphismClassesData 𝓕 h𝓕
  let φ := data.projection
  let : φ.toFunctor.Full := data.quotient.full
  let target := BasedCategory.ofFunctor (Functor.Elements.π data.classes)
  have hy : target.p.obj y = B := IsHomLift.domain_eq target.p f g
  let z : Fiber target.p B := Fiber.mk hy
  let : (fiberFunctor φ B).EssSurj := data.quotient.fiber_essSurj B
  obtain ⟨u, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (fiberFunctor φ B) z
  let x' : 𝓕.obj := u.1
  let a : φ.obj x' ⟶ y := Fiber.fiberInclusion.map e.hom
  have ha : target.p.IsHomLift (𝟙 B) a := e.hom.2
  let r : φ.obj x' ⟶ φ.obj x := a ≫ g
  have hr : target.p.IsHomLift f r := inferInstance
  obtain ⟨h, hh⟩ := φ.toFunctor.map_surjective r
  have hsource : 𝓕.p.IsHomLift f h := by
    have : target.p.IsHomLift f (φ.toFunctor.map h) := by rwa [hh]
    exact BasedFunctor.isHomLift_map φ f h
  exact ⟨x', h, a, hsource, ha, hh⟩

/-- A choice of object of the special fibre of a predeformation category. The special fibre is
equivalent to the one-object discrete category, so this is the image of its single object; any
two choices are isomorphic by `specialFiberObjects_isomorphic`. -/
public noncomputable def specialFiberObject
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) :
    p.Fiber (residueFieldObject.{u, v, w} Λ k) :=
  (Classical.choice hp.specialFiber).inverse.obj (Discrete.mk PUnit.unit)

end

/-! ### The associated functor of fibrewise isomorphism classes -/

section
open CategoryTheory CategoryTheory.Functor
universe u v u₁ v₁ u₂ v₂

variable {C : Type u} [Category.{v} C]
    (𝓕 : BasedCategory.{v₁, u₁} C) (h𝓕 : IsCofiberedInGroupoids 𝓕.p)

/-- The associated covariant functor of fibrewise isomorphism classes. -/
@[stacks 07W5]
noncomputable abbrev isomorphismClasses : C ⥤ Type u₁ :=
  (isomorphismClassesData 𝓕 h𝓕).classes

/-- The values of the associated functor are precisely the fibrewise isomorphism quotients. -/
theorem isomorphismClasses_obj (A : C) :
    (isomorphismClasses 𝓕 h𝓕).obj A = Quotient (isIsomorphicSetoid (Fiber 𝓕.p A)) :=
  (isomorphismClassesData 𝓕 h𝓕).classes_eq A

/-- The class of an object of a fibre, in the associated functor. -/
noncomputable def classOf {A : C} (x : Fiber 𝓕.p A) : (isomorphismClasses 𝓕 h𝓕).obj A :=
  cast (congrArg (isomorphismClasses 𝓕 h𝓕).obj
    (((toIsomorphismClasses 𝓕 h𝓕).w_obj x.1).trans x.2))
      ((toIsomorphismClasses 𝓕 h𝓕).obj x.1).2

/-- The canonical map sends an object to its own isomorphism class. -/
theorem classOf_eq {A : C} (x : Fiber 𝓕.p A) :
    cast (isomorphismClasses_obj 𝓕 h𝓕 A) (classOf 𝓕 h𝓕 x) =
      Quotient.mk (isIsomorphicSetoid (Fiber 𝓕.p A)) x := by
  rcases x with ⟨x, rfl⟩
  exact (isomorphismClassesData 𝓕 h𝓕).projection_obj x

/-- Isomorphic objects of a fibre have the same isomorphism class in the associated functor: the
class is the quotient class, and the quotient is by fibrewise isomorphism. -/
theorem classOf_eq_of_isIsomorphic {A : C} (x y : Fiber 𝓕.p A) (h : IsIsomorphic x y) :
    classOf 𝓕 h𝓕 x = classOf 𝓕 h𝓕 y :=
  (Equiv.cast (isomorphismClasses_obj 𝓕 h𝓕 A)).injective <|
    (classOf_eq 𝓕 h𝓕 x).trans ((Quotient.sound h).trans (classOf_eq 𝓕 h𝓕 y).symm)

private theorem map_cast {C : Type u} [Category.{v} C] (F : C ⥤ Type u₁)
    {A A' B B' : C} (hA : A = A') (hB : B = B') (f : A ⟶ B) (x : F.obj A) :
    F.map (eqToHom hA.symm ≫ f ≫ eqToHom hB) (cast (congrArg F.obj hA) x) =
      cast (congrArg F.obj hB) (F.map f x) := by
  cases hA
  cases hB
  simp

/-- The associated functor maps a class to the class of any pushforward.
This pins down its action on base morphisms independently of the choice of pushforwards. -/
theorem map_classOf {A B : C} (f : A ⟶ B) (x : Fiber 𝓕.p A) (y : Fiber 𝓕.p B)
    (a : x.1 ⟶ y.1) [𝓕.p.IsHomLift f a] :
    (isomorphismClasses 𝓕 h𝓕).map f (classOf 𝓕 h𝓕 x) = classOf 𝓕 h𝓕 y := by
  let q := toIsomorphismClasses 𝓕 h𝓕
  have : (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕)).IsHomLift f (q.map a) :=
    BasedFunctor.preserves_isHomLift q f a
  have h := IsHomLift.fac (Functor.Elements.π (isomorphismClasses 𝓕 h𝓕)) f (q.map a)
  dsimp only [classOf]
  rw [h]
  exact (map_cast _ ((q.w_obj x.1).trans x.2) ((q.w_obj y.1).trans y.2)
    (q.map a).hom (q.obj x.1).val).trans
      (congrArg (cast (congrArg (isomorphismClasses 𝓕 h𝓕).obj
        ((q.w_obj y.1).trans y.2))) (q.map a).map_val)

/-- Every associated class has an object representative in the fibre. -/
theorem classOf_surjective (A : C) : Function.Surjective (classOf 𝓕 h𝓕 (A := A)) := by
  intro z
  obtain ⟨x, hx⟩ := Quotient.exists_rep (cast (isomorphismClasses_obj 𝓕 h𝓕 A) z)
  exact ⟨x, (Equiv.cast (isomorphismClasses_obj 𝓕 h𝓕 A)).injective ((classOf_eq 𝓕 h𝓕 x).trans hx)⟩

variable {𝓕} {𝓖 : BasedCategory.{v₂, u₂} C}
    (h𝓖 : IsCofiberedInGroupoids 𝓖.p) (φ : BasedFunctor 𝓕 𝓖)

/-- A based functor sends a fibrewise class to the class of its image. -/
noncomputable def mapIsomorphismClasses (A : C) :
    (isomorphismClasses 𝓕 h𝓕).obj A → (isomorphismClasses 𝓖 h𝓖).obj A :=
  fun z ↦ cast (isomorphismClasses_obj 𝓖 h𝓖 A).symm
    (@Quotient.map _ _ (isIsomorphicSetoid (Fiber 𝓕.p A))
      (isIsomorphicSetoid (Fiber 𝓖.p A)) (fiberFunctor φ A).obj
      (fun _ _ ⟨i⟩ ↦ ⟨(fiberFunctor φ A).mapIso i⟩)
      (cast (isomorphismClasses_obj 𝓕 h𝓕 A) z))

/-- The map on associated functors is characterized on representatives. -/
theorem mapIsomorphismClasses_classOf {A : C} (x : Fiber 𝓕.p A) :
    mapIsomorphismClasses h𝓕 h𝓖 φ A (classOf 𝓕 h𝓕 x) =
      classOf 𝓖 h𝓖 ((fiberFunctor φ A).obj x) := by
  apply (Equiv.cast (isomorphismClasses_obj 𝓖 h𝓖 A)).injective
  simp only [Equiv.cast_apply, mapIsomorphismClasses, cast_cast, cast_eq,
    classOf_eq, Quotient.map_mk]

/-- The maps on fibrewise isomorphism classes commute with pushforward. -/
theorem mapIsomorphismClasses_naturality {A B : C} (f : A ⟶ B)
    (z : (isomorphismClasses 𝓕 h𝓕).obj A) :
    mapIsomorphismClasses h𝓕 h𝓖 φ B ((isomorphismClasses 𝓕 h𝓕).map f z) =
      (isomorphismClasses 𝓖 h𝓖).map f (mapIsomorphismClasses h𝓕 h𝓖 φ A z) := by
  obtain ⟨x, rfl⟩ := classOf_surjective 𝓕 h𝓕 A z
  obtain ⟨y, a, ha⟩ := h𝓕.exists_lift f.op (Opposite.op x.1) (congrArg Opposite.op x.2)
  have ha' : 𝓕.p.IsHomLift f a.unop := isHomLift_unop 𝓕.p f.op a (inst := ha)
  let y' : Fiber 𝓕.p B := ⟨y.unop, IsHomLift.codomain_eq 𝓕.p f a.unop⟩
  rw [map_classOf 𝓕 h𝓕 f x y' a.unop, mapIsomorphismClasses_classOf,
    mapIsomorphismClasses_classOf]
  exact (@map_classOf C _ 𝓖 h𝓖 A B f ((fiberFunctor φ A).obj x)
    ((fiberFunctor φ B).obj y') (φ.map a.unop)
    (BasedFunctor.preserves_isHomLift φ f a.unop)).symm

/-- The associated natural transformation, with universe lifts for independent total categories. -/
noncomputable def isomorphismClassesMap :
    (isomorphismClasses 𝓕 h𝓕 ⋙ uliftFunctor.{u₂}) ⟶
      (isomorphismClasses 𝓖 h𝓖 ⋙ uliftFunctor.{u₁}) where
  app A := ↾fun z ↦ ⟨mapIsomorphismClasses h𝓕 h𝓖 φ A z.down⟩
  naturality {A B} f := by
    ext z
    exact ULift.ext (mapIsomorphismClasses_naturality h𝓕 h𝓖 φ f z.down)

end

end Deformation
