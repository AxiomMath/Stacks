module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import StacksFrontier.Deformation.Cofibered

/-!
# The automorphism functor of an object

The automorphism functor of an object of a category cofibered
in groupoids.

## Main definitions

* `ChosenPushforwards` records chosen cocartesian pushforwards of one object.
* `ChosenPushforwards.ofCofiberedInGroupoids` equips any chosen lifts
  in a category cofibered in groupoids with their pushforward universal property.
* `automorphismFunctor` is the resulting set-valued automorphism functor.

## Implementation notes

Automorphisms are taken in `Functor.Fiber`, so they lie over the identity of
the base object. Both the maps between pushforwards and the induced maps on
automorphisms are constructed from the universal property of the chosen
strongly cocartesian arrows. Thus no functoriality or action on automorphisms
is included in the chosen data.

The construction works more generally whenever the chosen arrows are strongly
cocartesian. For a category cofibered in groupoids this property follows from
the cofibered hypothesis, as implemented by `ChosenPushforwards.ofCofiberedInGroupoids`;
only the chosen objects, arrows, and their images in the base are inputs.
The sole covering declaration is `automorphismFunctor`. Its object types reduce
to fibre automorphism groups, with group instances supplied explicitly, and its
maps reduce to the bundled homomorphisms
`ChosenPushforwards.transportAutHom`, so clients can use their group operations
and the homomorphism API directly.

## References

* [Stacks Project, Tag 06JT](https://stacks.math.columbia.edu/tag/06JT)
-/

@[expose] public section

namespace Deformation

/-! ### The automorphism functor of an object in a cofibered category -/

section
open CategoryTheory
universe v₁ v₂ u₁ u₂

/-- A choice of pushforward of `x` along every arrow with source `p.obj x`.
The map from `x` to each chosen object is required to be strongly
cocartesian. -/
public structure ChosenPushforwardsAt
    {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
    (p : F ⥤ C) (x : F) where
  /-- The chosen pushforward along an arrow out of `p.obj x`. -/
  obj : ∀ A : Under (p.obj x), p.Fiber A.right
  /-- The chosen arrow from `x` to the pushforward. -/
  inclusion : ∀ A : Under (p.obj x), x ⟶ (obj A).1
  /-- The chosen arrow has the pushforward universal property. -/
  inclusion_cocartesian : ∀ A : Under (p.obj x),
    p.IsStronglyCocartesian A.hom (inclusion A)

namespace ChosenPushforwardsAt

/-- A choice of lifts in a category cofibered in groupoids is a choice of
strongly cocartesian pushforwards. No action on automorphisms is part of the input. -/
@[implicit_reducible]
public def ofCofiberedInGroupoids
    {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
    {p : F ⥤ C} {x : F} (hp : IsCofiberedInGroupoids p)
    (obj : ∀ A : Under (p.obj x), p.Fiber A.right)
    (inclusion : ∀ A : Under (p.obj x), x ⟶ (obj A).1)
    (inclusion_lift : ∀ A : Under (p.obj x), p.IsHomLift A.hom (inclusion A)) :
    ChosenPushforwardsAt p x where
  obj := obj
  inclusion := inclusion
  inclusion_cocartesian A := by
    have lift_cocartesian : ∀ {R S : C} {a b : F} (f : R ⟶ S) (φ : a ⟶ b),
        p.IsHomLift f φ → p.IsStronglyCocartesian f φ := by
      intro R S a b f φ hφ
      cases hφ
      refine ⟨fun {b'} g φ' hφ' ↦ ?_⟩
      have hcomm : g.op ≫ p.op.map φ.op = p.op.map φ'.op := by
        change (p.map φ ≫ g).op = (p.map φ').op
        exact congrArg Quiver.Hom.op (IsHomLift.eq_of_isHomLift p _ φ')
      obtain ⟨χ, ⟨hχ, hfac⟩, huniq⟩ := hp.unique_lift φ.op φ'.op g.op hcomm
      refine ⟨χ.unop, ⟨?_, ?_⟩, ?_⟩
      · have heq : p.map χ.unop = g := congrArg Quiver.Hom.unop hχ
        rw [← heq]
        infer_instance
      · exact congrArg Quiver.Hom.unop hfac
      · intro ψ ⟨hψ, hψfac⟩
        have heq : p.op.map ψ.op = g.op :=
          congrArg Quiver.Hom.op (IsHomLift.eq_of_isHomLift p g ψ).symm
        exact congrArg Quiver.Hom.unop
          (huniq ψ.op ⟨heq, congrArg Quiver.Hom.op hψfac⟩)
    exact lift_cocartesian A.hom (inclusion A) (inclusion_lift A)

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
  {p : F ⥤ C} {x : F} (P : ChosenPushforwardsAt p x)

/-- The canonical arrow between two chosen pushforwards. -/
@[implicit_reducible]
public noncomputable def map {A B : Under (p.obj x)} (f : A ⟶ B) :
    (P.obj A).1 ⟶ (P.obj B).1 := by
  let := P.inclusion_cocartesian A
  let := P.inclusion_cocartesian B
  exact Functor.IsStronglyCocartesian.map p A.hom (P.inclusion A) f.w.symm (P.inclusion B)

public instance map_isHomLift {A B : Under (p.obj x)} (f : A ⟶ B) :
    p.IsHomLift f.right (P.map f) := by
  dsimp [map]
  infer_instance

@[reassoc (attr := simp)]
public lemma inclusion_map {A B : Under (p.obj x)} (f : A ⟶ B) :
    P.inclusion A ≫ P.map f = P.inclusion B := by
  let := P.inclusion_cocartesian A
  let := P.inclusion_cocartesian B
  exact Functor.IsStronglyCocartesian.fac p A.hom (P.inclusion A) f.w.symm (P.inclusion B)

public instance map_cocartesian {A B : Under (p.obj x)} (f : A ⟶ B) :
    p.IsStronglyCocartesian f.right (P.map f) := by
  let := P.inclusion_cocartesian A
  have hcomp : p.IsStronglyCocartesian (A.hom ≫ f.right)
      (P.inclusion A ≫ P.map f) := by
    rw [f.w, P.inclusion_map f]
    exact P.inclusion_cocartesian B
  let := hcomp
  exact Functor.IsStronglyCocartesian.of_comp (p := p) (f := A.hom)
    (g := f.right) (φ := P.inclusion A) (ψ := P.map f)

/-- A lift of `f.right` compatible with the inclusions is the canonical arrow `P.map f`. -/
private theorem map_eq_of_inclusion_comp {A B : Under (p.obj x)} (f : A ⟶ B)
    (g : (P.obj A).1 ⟶ (P.obj B).1) (hg : p.IsHomLift f.right g)
    (h : P.inclusion A ≫ g = P.inclusion B) : P.map f = g := by
  let := P.inclusion_cocartesian A
  exact Functor.IsStronglyCocartesian.ext p A.hom (P.inclusion A) f.right (by simpa using h.symm)

@[simp]
public lemma map_id (A : Under (p.obj x)) : P.map (𝟙 A) = 𝟙 (P.obj A).1 :=
  P.map_eq_of_inclusion_comp _ _ (CategoryTheory.IsHomLift.id (P.obj A).2) (by simp)

@[reassoc (attr := simp)]
public lemma map_comp {A B D : Under (p.obj x)} (f : A ⟶ B) (g : B ⟶ D) :
    P.map (f ≫ g) = P.map f ≫ P.map g :=
  P.map_eq_of_inclusion_comp _ _
    (by simpa using CategoryTheory.IsHomLift.comp p f.right g.right (P.map f) (P.map g)) (by simp)

/-- The endomorphism of a pushforward canonically induced by an automorphism
of an earlier pushforward. -/
@[implicit_reducible]
public noncomputable def transportHom {A B : Under (p.obj x)} (f : A ⟶ B)
    (a : Aut (P.obj A)) : (P.obj B).1 ⟶ (P.obj B).1 := by
  let := P.map_cocartesian f
  let : p.IsHomLift (𝟙 A.right) a.asIso.hom.val := a.asIso.hom.2
  let : p.IsHomLift f.right
      (a.asIso.hom.val ≫ P.map f) :=
    CategoryTheory.IsHomLift.comp_lift_id_left p f.right (P.map f)
      a.asIso.hom.val
  exact Functor.IsStronglyCocartesian.map p f.right (P.map f)
    (Category.comp_id f.right).symm
    (a.asIso.hom.val ≫ P.map f)

public instance transportHom_isHomLift {A B : Under (p.obj x)} (f : A ⟶ B)
    (a : Aut (P.obj A)) : p.IsHomLift (𝟙 B.right) (P.transportHom f a) := by
  dsimp [transportHom]
  infer_instance

@[reassoc (attr := simp)]
public lemma map_transportHom {A B : Under (p.obj x)} (f : A ⟶ B)
    (a : Aut (P.obj A)) :
    P.map f ≫ P.transportHom f a =
      a.asIso.hom.val ≫ P.map f := by
  let := P.map_cocartesian f
  let : p.IsHomLift (𝟙 A.right) a.asIso.hom.val := a.asIso.hom.2
  let : p.IsHomLift f.right
      (a.asIso.hom.val ≫ P.map f) :=
    CategoryTheory.IsHomLift.comp_lift_id_left p f.right (P.map f)
      a.asIso.hom.val
  exact Functor.IsStronglyCocartesian.fac p f.right (P.map f)
    (Category.comp_id f.right).symm
    (a.asIso.hom.val ≫ P.map f)

/-- Transport of a fibre automorphism along the canonical arrow between two
chosen pushforwards. -/
@[implicit_reducible]
public noncomputable def transportAut {A B : Under (p.obj x)} (f : A ⟶ B)
    (a : Aut (P.obj A)) : Aut (P.obj B) where
  asIso.hom := ⟨P.transportHom f a, inferInstance⟩
  asIso.inv := ⟨P.transportHom f a⁻¹, P.transportHom_isHomLift f a⁻¹⟩
  asIso.hom_inv_id := by
    apply Functor.Fiber.hom_ext
    change P.transportHom f a ≫ P.transportHom f a⁻¹ = 𝟙 (P.obj B).1
    let := P.map_cocartesian f
    let := P.transportHom_isHomLift f a
    let := P.transportHom_isHomLift f a⁻¹
    let : p.IsHomLift (𝟙 B.right)
        (P.transportHom f a ≫ P.transportHom f a⁻¹) :=
      by
        simpa using (CategoryTheory.IsHomLift.comp p (𝟙 B.right) (𝟙 B.right)
          (P.transportHom f a) (P.transportHom f a⁻¹))
    let : p.IsHomLift (𝟙 B.right) (𝟙 (P.obj B).1) :=
      CategoryTheory.IsHomLift.id (P.obj B).2
    apply Functor.IsStronglyCocartesian.ext p f.right (P.map f) (𝟙 B.right)
    calc
      P.map f ≫ (P.transportHom f a ≫ P.transportHom f a⁻¹) =
          (P.map f ≫ P.transportHom f a) ≫ P.transportHom f a⁻¹ :=
        (Category.assoc _ _ _).symm
      _ =
          (a.asIso.hom.val ≫ P.map f) ≫ P.transportHom f a⁻¹ :=
        congrArg (fun h ↦ h ≫ P.transportHom f a⁻¹) (P.map_transportHom f a)
      _ = a.asIso.hom.val ≫ (P.map f ≫ P.transportHom f a⁻¹) := Category.assoc _ _ _
      _ = a.asIso.hom.val ≫ (a.asIso.inv.val ≫ P.map f) :=
        congrArg (fun h ↦ a.asIso.hom.val ≫ h) (P.map_transportHom f a⁻¹)
      _ = P.map f := by
        rw [← Category.assoc]
        have h : a.asIso.hom.val ≫ a.asIso.inv.val = 𝟙 (P.obj A).1 :=
          congrArg Subtype.val a.asIso.hom_inv_id
        rw [h, Category.id_comp]
      _ = P.map f ≫ 𝟙 (P.obj B).1 := (Category.comp_id _).symm
  asIso.inv_hom_id := by
    apply Functor.Fiber.hom_ext
    change P.transportHom f a⁻¹ ≫ P.transportHom f a = 𝟙 (P.obj B).1
    let := P.map_cocartesian f
    let := P.transportHom_isHomLift f a
    let := P.transportHom_isHomLift f a⁻¹
    let : p.IsHomLift (𝟙 B.right)
        (P.transportHom f a⁻¹ ≫ P.transportHom f a) :=
      by
        simpa using (CategoryTheory.IsHomLift.comp p (𝟙 B.right) (𝟙 B.right)
          (P.transportHom f a⁻¹) (P.transportHom f a))
    let : p.IsHomLift (𝟙 B.right) (𝟙 (P.obj B).1) :=
      CategoryTheory.IsHomLift.id (P.obj B).2
    apply Functor.IsStronglyCocartesian.ext p f.right (P.map f) (𝟙 B.right)
    calc
      P.map f ≫ (P.transportHom f a⁻¹ ≫ P.transportHom f a) =
          (P.map f ≫ P.transportHom f a⁻¹) ≫ P.transportHom f a :=
        (Category.assoc _ _ _).symm
      _ =
          (a.asIso.inv.val ≫ P.map f) ≫ P.transportHom f a :=
        congrArg (fun h ↦ h ≫ P.transportHom f a) (P.map_transportHom f a⁻¹)
      _ = a.asIso.inv.val ≫ (P.map f ≫ P.transportHom f a) := Category.assoc _ _ _
      _ = a.asIso.inv.val ≫ (a.asIso.hom.val ≫ P.map f) :=
        congrArg (fun h ↦ a.asIso.inv.val ≫ h) (P.map_transportHom f a)
      _ = P.map f := by
        rw [← Category.assoc]
        have h : a.asIso.inv.val ≫ a.asIso.hom.val = 𝟙 (P.obj A).1 :=
          congrArg Subtype.val a.asIso.inv_hom_id
        rw [h, Category.id_comp]
      _ = P.map f ≫ 𝟙 (P.obj B).1 := (Category.comp_id _).symm

/-- Transport of automorphisms is a homomorphism. -/
@[implicit_reducible]
public noncomputable def transportAutHom {A B : Under (p.obj x)} (f : A ⟶ B) :
    Aut (P.obj A) →* Aut (P.obj B) where
  toFun := P.transportAut f
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply Functor.Fiber.hom_ext
    change P.transportHom f (1 : Aut (P.obj A)) = 𝟙 (P.obj B).1
    let := P.map_cocartesian f
    let : p.IsHomLift (𝟙 B.right) (𝟙 (P.obj B).1) :=
      CategoryTheory.IsHomLift.id (P.obj B).2
    apply Functor.IsStronglyCocartesian.ext p f.right (P.map f) (𝟙 B.right)
    rw [P.map_transportHom]
    change 𝟙 (P.obj A).1 ≫ P.map f = P.map f ≫ 𝟙 (P.obj B).1
    simp
  map_mul' a b := by
    apply Aut.ext
    apply Iso.ext
    apply Functor.Fiber.hom_ext
    change P.transportHom f (a * b) = P.transportHom f b ≫ P.transportHom f a
    let := P.map_cocartesian f
    let := P.transportHom_isHomLift f b
    let := P.transportHom_isHomLift f a
    let : p.IsHomLift (𝟙 B.right)
        (P.transportHom f b ≫ P.transportHom f a) :=
      by
        simpa using (CategoryTheory.IsHomLift.comp p (𝟙 B.right) (𝟙 B.right)
          (P.transportHom f b) (P.transportHom f a))
    apply Functor.IsStronglyCocartesian.ext p f.right (P.map f) (𝟙 B.right)
    calc
      P.map f ≫ P.transportHom f (a * b) = (a * b).asIso.hom.val ≫ P.map f :=
        P.map_transportHom f (a * b)
      _ = (b.asIso.hom.val ≫ a.asIso.hom.val) ≫ P.map f := rfl
      _ = b.asIso.hom.val ≫ (a.asIso.hom.val ≫ P.map f) := Category.assoc _ _ _
      _ = b.asIso.hom.val ≫ (P.map f ≫ P.transportHom f a) :=
        congrArg (fun h ↦ b.asIso.hom.val ≫ h) (P.map_transportHom f a).symm
      _ = (b.asIso.hom.val ≫ P.map f) ≫ P.transportHom f a :=
        (Category.assoc _ _ _).symm
      _ = (P.map f ≫ P.transportHom f b) ≫ P.transportHom f a :=
        congrArg (fun h ↦ h ≫ P.transportHom f a) (P.map_transportHom f b).symm
      _ = P.map f ≫ (P.transportHom f b ≫ P.transportHom f a) :=
        Category.assoc _ _ _

@[simp]
public lemma transportAut_id (A : Under (p.obj x)) (a : Aut (P.obj A)) :
    P.transportAut (𝟙 A) a = a := by
  apply Aut.ext
  apply Iso.ext
  apply Functor.Fiber.hom_ext
  show P.transportHom (𝟙 A) a = a.asIso.hom.val
  simpa only [P.map_id, Category.id_comp, Category.comp_id] using
    P.map_transportHom (𝟙 A) a

public lemma transportAut_comp {A B D : Under (p.obj x)} (f : A ⟶ B) (g : B ⟶ D)
    (a : Aut (P.obj A)) :
    P.transportAut (f ≫ g) a = P.transportAut g (P.transportAut f a) := by
  apply Aut.ext
  apply Iso.ext
  apply Functor.Fiber.hom_ext
  show P.transportHom (f ≫ g) a =
    P.transportHom g (P.transportAut f a)
  let := P.map_cocartesian (f ≫ g)
  let := P.transportHom_isHomLift (f ≫ g) a
  let := P.transportHom_isHomLift g (P.transportAut f a)
  apply Functor.IsStronglyCocartesian.ext p (f ≫ g).right (P.map (f ≫ g))
    (𝟙 D.right)
  rw [P.map_transportHom (f ≫ g) a, P.map_comp f g,
    Category.assoc, P.map_transportHom g (P.transportAut f a)]
  show a.asIso.hom.val ≫ (P.map f ≫ P.map g) =
    P.map f ≫ (P.transportHom f a ≫ P.map g)
  simp only [← Category.assoc, P.map_transportHom f a]

end ChosenPushforwardsAt

/-- The automorphism functor of `x`: at `f : p.obj x ⟶ V` it is the type
of automorphisms over `V` of the chosen pushforward `f_* x`. -/
@[stacks 06JT, implicit_reducible]
public noncomputable def automorphismFunctor
    {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
    {p : F ⥤ C} {x : F} (P : ChosenPushforwardsAt p x) : Under (p.obj x) ⥤ Type v₁ where
  obj A := Aut (P.obj A)
  map f := ↾fun a ↦ P.transportAutHom f a
  map_id A := ConcreteCategory.hom_ext _ _ fun a ↦ P.transportAut_id A a
  map_comp f g := ConcreteCategory.hom_ext _ _ fun a ↦ P.transportAut_comp f g a

/-- The values of the automorphism functor retain their fibre automorphism
group structure, even though its target is the category of types. -/
public instance automorphismFunctorObjGroup
    {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
    {p : F ⥤ C} {x : F} (P : ChosenPushforwardsAt p x) (A : Under (p.obj x)) :
    Group ((automorphismFunctor P).obj A) :=
  inferInstanceAs (Group (Aut (P.obj A)))

end

end Deformation
