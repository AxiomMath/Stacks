module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Skeletal
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
public import StacksFrontier.Deformation.RimSchlessinger.Basic

/-!
# Lifts of objects along fibre squares

Lifts of an object along a fibre square in a category cofibered in groupoids satisfying the
Rim-Schlessinger condition: the set of lifts over a fibre product, the set of lifts with one
factor fixed, and the composite of two fibre squares.

## Main definitions

* `Lift`: the category of lifts of an object along a base morphism.
* `LiftClasses`: its set of isomorphism classes.
* `Lift.over` and `LiftClasses.over`: the same category and set for an object of the base
  category given together with its morphism to the base, the base morphism being left implicit.
* `LiftProductEquiv`: a bijection between pairs of classes of lifts over the two factors and
  classes of lifts over the fibre product, together with its fibre-product characterization.
* `IsPushforwardOf`: a lift over the fibre product pushes forward to a specified lift over the
  second factor.
* `liftSourceFiber`: the source of a lift, as an object of its fibre.
* `FixedLiftEquiv`: a bijection on isomorphism classes of lifts with the lift over the first
  factor fixed, together with its pushforward characterization.

## Main results

* `isIso_liftHom`: the category of lifts is a groupoid.
* `liftClassesProdEquivPullback`: the product bijection for lifts.
* `liftClassesEquivOfFixedLift`: the bijection after fixing the lift over the first factor.
* `liftClassesEquivProdOfCompositePullback`: the product bijection over the left square of a
  composite of two fibre squares.
* `liftClassesEquivOuterProdOfCompositePullback`: the resulting bijection with lifts over the
  outer factors.

## Implementation notes

An object over the target algebra is represented by an object of `Functor.Fiber`. The category
of lifts is the category of arrows over the specified base morphism, and its set of
isomorphism classes is represented by `ThinSkeleton`.

Pushing forward is characterized without choosing a pushforward object: the source object, its
fixed projection, and the projection to the proposed image must form a limiting pullback cone.

## References

* [Stacks Project, Tag 06JE](https://stacks.math.columbia.edu/tag/06JE)
* [Stacks Project, Tag 06JF](https://stacks.math.columbia.edu/tag/06JF)
* [Stacks Project, Tag 06JH](https://stacks.math.columbia.edu/tag/06JH)
-/

@[expose] public section

namespace Deformation

/-! ### Lifts over a fibre product -/

section
open CategoryTheory CategoryTheory.Limits
universe u v uF vF

/-- The category of lifts of `x` along `f`. Its objects are arrows to `x` lying over `f`; its
arrows are commuting triangles whose remaining side lies over the identity. -/
@[stacks 06JE "objects"]
public structure Lift
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {A' A : C} (f : A' ⟶ A) (x : p.Fiber A) where
  /-- The source of the lifting arrow. -/
  obj : F
  /-- The lifting arrow. -/
  hom : obj ⟶ x.1
  /-- The lifting arrow lies over the prescribed arrow in the base. -/
  isHomLift : p.IsHomLift f hom

attribute [instance] Lift.isHomLift

/-- A morphism of lifts is a morphism over the identity which makes the triangle of
lifting arrows commute. -/
@[stacks 06JE "morphisms"]
public structure Lift.Hom
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {A' A : C} {f : A' ⟶ A} {x : p.Fiber A}
    (a b : Lift p f x) where
  /-- The morphism between the sources of the lifting arrows. -/
  hom : a.obj ⟶ b.obj
  /-- A morphism of lifts lies over the identity of the source algebra. -/
  isHomLift : p.IsHomLift (𝟙 A') hom
  /-- The triangle with the two lifting arrows commutes. -/
  fac : hom ≫ b.hom = a.hom

attribute [instance] Lift.Hom.isHomLift

/-- Two morphisms of lifts are equal when their underlying morphisms are. -/
@[ext]
public lemma Lift.Hom.ext
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {A' A : C} {f : A' ⟶ A} {x : p.Fiber A}
    {a b : Lift p f x} {g h : Lift.Hom a b} (w : g.hom = h.hom) : g = h := by
  cases g
  cases h
  cases w
  rfl

/-- The lifts of `x` along `f` and their morphisms form a category. -/
public instance Lift.category
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {A' A : C} {f : A' ⟶ A} {x : p.Fiber A} :
    Category.{vF} (Lift p f x) where
  Hom := Lift.Hom
  id a :=
    { hom := 𝟙 a.obj
      isHomLift := CategoryTheory.IsHomLift.id
        (CategoryTheory.IsHomLift.domain_eq p f a.hom)
      fac := Category.id_comp _ }
  comp g h :=
    { hom := g.hom ≫ h.hom
      isHomLift := inferInstance
      fac := by rw [Category.assoc, h.fac, g.fac] }
  id_comp _ := Lift.Hom.ext (Category.id_comp _)
  comp_id _ := Lift.Hom.ext (Category.comp_id _)
  assoc _ _ _ := Lift.Hom.ext (Category.assoc _ _ _)

/-- The set of isomorphism classes of lifts of `x` along `f`. -/
@[stacks 06JE "the set of lifts"]
public abbrev LiftClasses
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {A' A : C} (f : A' ⟶ A) (x : p.Fiber A) :=
  ThinSkeleton (Lift p f x)

/-! ### Lifts named by the source object alone -/

/-- The category of lifts of `x` to an object `A'` of the base category given together with
its morphism to `A`: the lifts of `x` along that morphism, which the name leaves implicit. -/
@[stacks 06JF "the category of lifts named by the source object"]
public abbrev Lift.over
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {A : C} (A' : Over A) (x : p.Fiber A) :=
  Lift p A'.hom x

/-- The set of isomorphism classes of lifts of `x` to an object `A'` of the base category
given together with its morphism to `A`, that morphism being left implicit. -/
@[stacks 06JF "the set of lifts named by the source object"]
public abbrev LiftClasses.over
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {A : C} (A' : Over A) (x : p.Fiber A) :=
  LiftClasses p A'.hom x

/-- The lifts of `x` to `A'` regarded over `A` by `f` are the lifts of `x` along `f`. -/
public lemma Lift.over_mk
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {A' A : C} (f : A' ⟶ A) (x : p.Fiber A) :
    Lift.over p (Over.mk f) x = Lift p f x :=
  rfl

/-- The isomorphism classes of lifts of `x` to `A'` regarded over `A` by `f` are the
isomorphism classes of lifts of `x` along `f`. -/
public lemma LiftClasses.over_mk
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {A' A : C} (f : A' ⟶ A) (x : p.Fiber A) :
    LiftClasses.over p (Over.mk f) x = LiftClasses p f x :=
  rfl

/-- Every object of the base category over `A` is its own source object together with its
morphism to `A`, so the two ways of naming a category of lifts agree. -/
public lemma Lift.over_eq_over_mk_hom
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {A : C} (A' : Over A) (x : p.Fiber A) :
    Lift.over p A' x = Lift.over p (Over.mk A'.hom) x :=
  rfl

/-- A lift to the base fibre product is the fibre product of two given lifts if it admits
projection arrows over the base projections which exhibit its source as their pullback. -/
public def IsFiberProductOf
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {A₁ A₂ A : C} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) {x : p.Fiber A}
    (z : Lift p (c.fst ≫ f₁) x) (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x) : Prop :=
  ∃ (g₁ : z.obj ⟶ a₁.obj) (g₂ : z.obj ⟶ a₂.obj)
    (comm : g₁ ≫ a₁.hom = g₂ ≫ a₂.hom),
      p.IsHomLift c.fst g₁ ∧
      p.IsHomLift c.snd g₂ ∧
      g₁ ≫ a₁.hom = z.hom ∧
      g₂ ≫ a₂.hom = z.hom ∧
      Nonempty (IsLimit (PullbackCone.mk g₁ g₂ comm))

/-- A bijection on isomorphism classes whose value on every pair is represented by the
fibre product of representatives. -/
public structure LiftProductEquiv
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {A₁ A₂ A : C} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (x : p.Fiber A) where
  /-- The underlying bijection on isomorphism classes. -/
  equiv : (LiftClasses p f₁ x × LiftClasses p f₂ x) ≃
    LiftClasses p (c.fst ≫ f₁) x
  /-- The bijection sends representatives to the class of their fibre product. -/
  maps_pair_to_fiberProduct : ∀ (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x),
    ∃ z : Lift p (c.fst ≫ f₁) x,
      IsFiberProductOf c z a₁ a₂ ∧
        equiv (ThinSkeleton.mk a₁, ThinSkeleton.mk a₂) = ThinSkeleton.mk z

/-- In a category cofibered in groupoids, an arrow lying over an isomorphism is an
isomorphism. -/
private lemma isIso_of_isHomLift_isIso
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} (hp : IsCofiberedInGroupoids p) {R S : C} (f : R ⟶ S) [IsIso f]
    {a b : F} (φ : a ⟶ b) [p.IsHomLift f φ] : IsIso φ := by
  have : IsIso (p.map φ) := by
    rw [CategoryTheory.IsHomLift.fac' p f φ]
    infer_instance
  exact isIso_of_isIso_map hp φ

/-- Every morphism of lifts in a category cofibered in groupoids is an isomorphism; that is,
the category of lifts of an object along a morphism is a groupoid. -/
public lemma isIso_liftHom
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} (hp : IsCofiberedInGroupoids p)
    {A' A : C} {f : A' ⟶ A} {x : p.Fiber A}
    {a b : Lift p f x} (h : a ⟶ b) : IsIso h := by
  have : IsIso h.hom := isIso_of_isHomLift_isIso hp (𝟙 A') h.hom
  let hi : b ⟶ a :=
    { hom := inv h.hom
      isHomLift := inferInstance
      fac := by rw [← h.fac, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp] }
  exact ⟨hi, Lift.Hom.ext (IsIso.hom_inv_id h.hom), Lift.Hom.ext (IsIso.inv_hom_id h.hom)⟩

/-- Every lift `z` of `x` along a composite `g ≫ f` factors as an arrow lying over `g`
followed by a lift of `x` along `f`. -/
lemma lift_factor
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} (hp : IsCofiberedInGroupoids p)
    {A₀ A₁ A : C} (g : A₀ ⟶ A₁) (f : A₁ ⟶ A) (x : p.Fiber A)
    (z : Lift p (g ≫ f) x) :
    ∃ a : Lift p f x, ∃ h : z.obj ⟶ a.obj,
      p.IsHomLift g h ∧ h ≫ a.hom = z.hom := by
  let hz := CategoryTheory.IsHomLift.domain_eq p (g ≫ f) z.hom
  obtain ⟨y, h, hh⟩ := exists_pushforward hp g z.obj hz
  let : p.IsHomLift g h := hh
  let hy := CategoryTheory.IsHomLift.codomain_eq p g h
  let q : p.obj y ⟶ p.obj x.1 := eqToHom hy ≫ f ≫ eqToHom x.2.symm
  have hcomm : p.map h ≫ q = p.map z.hom := by
    rw [CategoryTheory.IsHomLift.fac' p g h,
      CategoryTheory.IsHomLift.fac' p (g ≫ f) z.hom]
    simp [q, Category.assoc]
  obtain ⟨a, ⟨hbase, hfac⟩, _⟩ := existsUnique_factor_of_isHomLift hp h z.hom q hcomm
  have ha : p.IsHomLift f a :=
    CategoryTheory.IsHomLift.of_fac' p f a hy x.2 hbase
  exact ⟨⟨y, a, ha⟩, h, hh, hfac⟩

/-- Transport a lift along an equality of the base morphisms. -/
private def liftOfEq
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {A' A : C} {f f' : A' ⟶ A} (h : f = f') {x : p.Fiber A}
    (z : Lift p f x) : Lift p f' x :=
  ⟨z.obj, z.hom, h ▸ z.isHomLift⟩

private lemma lift_to_pair
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} (hp : IsCofiberedInGroupoids p)
    {A₁ A₂ A : C} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (x : p.Fiber A)
    (z : Lift p (c.fst ≫ f₁) x) :
    ∃ (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x)
      (g₁ : z.obj ⟶ a₁.obj) (g₂ : z.obj ⟶ a₂.obj),
      p.IsHomLift c.fst g₁ ∧ p.IsHomLift c.snd g₂ ∧
        g₁ ≫ a₁.hom = z.hom ∧ g₂ ≫ a₂.hom = z.hom := by
  obtain ⟨a₁, g₁, hg₁, hfac₁⟩ := lift_factor hp c.fst f₁ x z
  obtain ⟨a₂, g₂, hg₂, hfac₂⟩ := lift_factor hp c.snd f₂ x (liftOfEq p c.condition z)
  exact ⟨a₁, a₂, g₁, g₂, hg₁, hg₂, hfac₁, hfac₂⟩

private lemma base_pullback_iso
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {A₁ A₂ A : C} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c) (x : p.Fiber A)
    (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x)
    (d : PullbackCone a₁.hom a₂.hom) (hdp : IsLimit (d.map p)) :
    ∃ i : p.obj d.pt ≅ c.pt,
      i.hom ≫ c.fst = p.map d.fst ≫
          eqToHom (CategoryTheory.IsHomLift.domain_eq p f₁ a₁.hom) ∧
      i.hom ≫ c.snd = p.map d.snd ≫
          eqToHom (CategoryTheory.IsHomLift.domain_eq p f₂ a₂.hom) := by
  let h₁ := CategoryTheory.IsHomLift.domain_eq p f₁ a₁.hom
  let h₂ := CategoryTheory.IsHomLift.domain_eq p f₂ a₂.hom
  let hb := IsPullback.of_isLimit hdp
  have hb' : IsPullback
      (p.map d.fst ≫ eqToHom h₁) (p.map d.snd ≫ eqToHom h₂) f₁ f₂ := by
    apply hb.of_iso (Iso.refl _) (eqToIso h₁) (eqToIso h₂) (eqToIso x.2)
    · change p.map d.fst ≫ eqToHom h₁ =
        𝟙 (p.obj d.pt) ≫ (p.map d.fst ≫ eqToHom h₁)
      simp
    · change p.map d.snd ≫ eqToHom h₂ =
        𝟙 (p.obj d.pt) ≫ (p.map d.snd ≫ eqToHom h₂)
      simp
    · rw [CategoryTheory.IsHomLift.fac' p f₁ a₁.hom]
      simp [Category.assoc]
    · rw [CategoryTheory.IsHomLift.fac' p f₂ a₂.hom]
      simp [Category.assoc]
  let i := hb'.isoIsPullback A₁ A₂ (IsPullback.of_isLimit hc)
  exact ⟨i, hb'.isoIsPullback_hom_fst A₁ A₂ (IsPullback.of_isLimit hc),
    hb'.isoIsPullback_hom_snd A₁ A₂ (IsPullback.of_isLimit hc)⟩

private lemma exists_fiber_product_of_surj_second
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (hRS : SatisfiesRS p)
    {A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c)
    (hsurj : Function.Surjective f₂.hom) (x : p.Fiber A)
    (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x) :
    ∃ z : Lift p (c.fst ≫ f₁) x, IsFiberProductOf c z a₁ a₂ := by
  obtain ⟨d, ⟨hd, hdp⟩⟩ := hRS.2 a₁.hom a₂.hom
    (surjective_map_of_lift p f₂ a₂.hom hsurj)
  obtain ⟨i, hi₁, hi₂⟩ := base_pullback_iso p c hc x a₁ a₂ d hdp.some
  obtain ⟨y, e, he⟩ := exists_pushforward hRS.1 i.hom d.pt rfl
  let : p.IsHomLift i.hom e := he
  have : IsIso e := isIso_of_isHomLift_isIso hRS.1 i.hom e
  have : p.IsHomLift i.inv (inv e) := by
    have hiinv : i.inv = inv i.hom :=
      (CategoryTheory.hom_comp_eq_id i.hom).mp i.hom_inv_id
    rw [hiinv]
    infer_instance
  let h₁ := CategoryTheory.IsHomLift.domain_eq p f₁ a₁.hom
  let h₂ := CategoryTheory.IsHomLift.domain_eq p f₂ a₂.hom
  let hy := CategoryTheory.IsHomLift.codomain_eq p i.hom e
  have hm : p.map (inv e) = eqToHom hy ≫ i.inv := by
    rw [CategoryTheory.IsHomLift.fac' p i.inv (inv e)]
    simp
  let g₁ : y ⟶ a₁.obj := inv e ≫ d.fst
  let g₂ : y ⟶ a₂.obj := inv e ≫ d.snd
  have hg₁ : p.IsHomLift c.fst g₁ := by
    apply CategoryTheory.IsHomLift.of_commsq p c.fst g₁ hy h₁
    change p.map (inv e ≫ d.fst) ≫ eqToHom h₁ = eqToHom hy ≫ c.fst
    calc
      p.map (inv e ≫ d.fst) ≫ eqToHom h₁ =
          (eqToHom hy ≫ i.inv) ≫ (p.map d.fst ≫ eqToHom h₁) := by
            simp only [p.map_comp, hm, Category.assoc]
      _ = eqToHom hy ≫ c.fst := by rw [← hi₁]; simp [Category.assoc]
  have hg₂ : p.IsHomLift c.snd g₂ := by
    apply CategoryTheory.IsHomLift.of_commsq p c.snd g₂ hy h₂
    change p.map (inv e ≫ d.snd) ≫ eqToHom h₂ = eqToHom hy ≫ c.snd
    calc
      p.map (inv e ≫ d.snd) ≫ eqToHom h₂ =
          (eqToHom hy ≫ i.inv) ≫ (p.map d.snd ≫ eqToHom h₂) := by
            simp only [p.map_comp, hm, Category.assoc]
      _ = eqToHom hy ≫ c.snd := by rw [← hi₂]; simp [Category.assoc]
  have hcomm : g₁ ≫ a₁.hom = g₂ ≫ a₂.hom := by
    dsimp [g₁, g₂]
    simp only [Category.assoc, d.condition]
  let z : Lift p (c.fst ≫ f₁) x :=
    { obj := y
      hom := g₁ ≫ a₁.hom
      isHomLift := inferInstance }
  let ei : d.pt ≅ y := asIso e
  have hlim : IsLimit (PullbackCone.mk g₁ g₂ hcomm) := by
    apply IsLimit.ofIsoLimit hd.some
    exact PullbackCone.ext ei
      (by change d.fst = e ≫ (inv e ≫ d.fst); simp)
      (by change d.snd = e ≫ (inv e ≫ d.snd); simp)
  exact ⟨z, g₁, g₂, hcomm, hg₁, hg₂, rfl, hcomm.symm, ⟨hlim⟩⟩

private lemma exists_fiber_product
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (hRS : SatisfiesRS p)
    {A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c)
    (hsurj : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom)
    (x : p.Fiber A) (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x) :
    ∃ z : Lift p (c.fst ≫ f₁) x, IsFiberProductOf c z a₁ a₂ := by
  rcases hsurj with h₁ | h₂
  · obtain ⟨z', hz'⟩ := exists_fiber_product_of_surj_second p hRS c.flip
      (PullbackCone.flipIsLimit hc) h₁ x a₂ a₁
    let z : Lift p (c.fst ≫ f₁) x := liftOfEq p c.condition.symm z'
    rcases hz' with ⟨g₂, g₁, hcomm, hg₂, hg₁, hfac₂, hfac₁, hlim⟩
    refine ⟨z, g₁, g₂, hcomm.symm, hg₁, hg₂, hfac₁, hfac₂, ?_⟩
    have hflip := PullbackCone.flipIsLimit hlim.some
    change IsLimit (PullbackCone.mk g₁ g₂ hcomm.symm) at hflip
    exact ⟨hflip⟩
  · exact exists_fiber_product_of_surj_second p hRS c hc h₂ x a₁ a₂

private noncomputable def mapped_pullback_of_lift
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {A₁ A₂ A : C} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c) (x : p.Fiber A)
    (z : Lift p (c.fst ≫ f₁) x) (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x)
    (g₁ : z.obj ⟶ a₁.obj) (g₂ : z.obj ⟶ a₂.obj)
    (comm : g₁ ≫ a₁.hom = g₂ ≫ a₂.hom)
    (hg₁ : p.IsHomLift c.fst g₁) (hg₂ : p.IsHomLift c.snd g₂) :
    IsLimit ((PullbackCone.mk g₁ g₂ comm).map p) := by
  let h₀ := CategoryTheory.IsHomLift.domain_eq p c.fst g₁
  let h₁ := CategoryTheory.IsHomLift.codomain_eq p c.fst g₁
  let h₂ := CategoryTheory.IsHomLift.codomain_eq p c.snd g₂
  have hb : IsPullback (p.map g₁) (p.map g₂)
      (p.map a₁.hom) (p.map a₂.hom) := by
    apply (IsPullback.of_isLimit hc).of_iso'
      (eqToIso h₀) (eqToIso h₁) (eqToIso h₂) (eqToIso x.2)
    · rw [CategoryTheory.IsHomLift.fac' p c.fst g₁]
      simp [Category.assoc]
    · rw [CategoryTheory.IsHomLift.fac' p c.snd g₂]
      simp [Category.assoc]
    · rw [CategoryTheory.IsHomLift.fac' p f₁ a₁.hom]
      simp [Category.assoc]
    · rw [CategoryTheory.IsHomLift.fac' p f₂ a₂.hom]
      simp [Category.assoc]
  change IsLimit (PullbackCone.mk (p.map g₁) (p.map g₂) (by
    simpa only [p.map_comp] using congrArg p.map comm))
  exact hb.isLimit

private lemma fiber_product_of_lift
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (hRS : SatisfiesRS p)
    {A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c)
    (hsurj : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom)
    (x : p.Fiber A) (z : Lift p (c.fst ≫ f₁) x) :
    ∃ (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x), IsFiberProductOf c z a₁ a₂ := by
  obtain ⟨a₁, a₂, g₁, g₂, hg₁, hg₂, hfac₁, hfac₂⟩ :=
    lift_to_pair hRS.1 c x z
  let comm : g₁ ≫ a₁.hom = g₂ ≫ a₂.hom := hfac₁.trans hfac₂.symm
  let d : PullbackCone a₁.hom a₂.hom := PullbackCone.mk g₁ g₂ comm
  have hdmap : IsLimit (d.map p) :=
    mapped_pullback_of_lift p c hc x z a₁ a₂ g₁ g₂ comm hg₁ hg₂
  have hd : Nonempty (IsLimit d) := by
    rcases hsurj with h₁ | h₂
    · have hdmapFlip := PullbackCone.flipIsLimit hdmap
      have hdFlip : Nonempty (IsLimit d.flip) :=
        isLimit_of_map_isLimit hRS a₂.hom a₁.hom d.flip
          (surjective_map_of_lift p f₁ a₁.hom h₁) (by
            change Nonempty (IsLimit (d.map p).flip)
            exact ⟨hdmapFlip⟩)
      exact ⟨PullbackCone.isLimitOfFlip hdFlip.some⟩
    · exact isLimit_of_map_isLimit hRS a₁.hom a₂.hom d
        (surjective_map_of_lift p f₂ a₂.hom h₂) ⟨hdmap⟩
  exact ⟨a₁, a₂, g₁, g₂, comm, hg₁, hg₂, hfac₁, hfac₂, hd⟩

private lemma factor_unique
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} (hp : IsCofiberedInGroupoids p)
    {A₀ A₁ A : C} (g : A₀ ⟶ A₁) (f : A₁ ⟶ A) (x : p.Fiber A)
    (z : Lift p (g ≫ f) x) (a b : Lift p f x)
    (φ : z.obj ⟶ a.obj) (ψ : z.obj ⟶ b.obj)
    (hφ : p.IsHomLift g φ) (hψ : p.IsHomLift g ψ)
    (hfacφ : φ ≫ a.hom = z.hom) (hfacψ : ψ ≫ b.hom = z.hom) :
    ∃ i : a ≅ b, φ ≫ i.hom.hom = ψ := by
  let : p.IsHomLift g φ := hφ
  let : p.IsHomLift g ψ := hψ
  let ha := CategoryTheory.IsHomLift.codomain_eq p g φ
  let hb := CategoryTheory.IsHomLift.codomain_eq p g ψ
  let q : p.obj a.obj ⟶ p.obj b.obj := eqToHom ha ≫ eqToHom hb.symm
  have hcomm : p.map φ ≫ q = p.map ψ := by
    rw [CategoryTheory.IsHomLift.fac' p g φ,
      CategoryTheory.IsHomLift.fac' p g ψ]
    simp [q, Category.assoc]
  obtain ⟨h, ⟨hbase, htri⟩, _⟩ := existsUnique_factor_of_isHomLift hp φ ψ q hcomm
  have hh : p.IsHomLift (𝟙 A₁) h := by
    apply CategoryTheory.IsHomLift.of_fac' p (𝟙 A₁) h ha hb
    simpa [q] using hbase
  let : p.IsHomLift (𝟙 A₁) h := hh
  let : p.IsStronglyCocartesian g φ :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hp g φ hφ
  have hfac : h ≫ b.hom = a.hom := by
    apply Functor.IsStronglyCocartesian.ext p g φ f
    calc
      φ ≫ (h ≫ b.hom) = (φ ≫ h) ≫ b.hom := (Category.assoc _ _ _).symm
      _ = z.hom := by rw [htri, hfacψ]
      _ = φ ≫ a.hom := hfacφ.symm
  let l : a ⟶ b := ⟨h, hh, hfac⟩
  have : IsIso l := isIso_liftHom hp l
  exact ⟨asIso l, htri⟩

/-- A morphism between the source objects of two arrows over the projections of a pullback
square, compatible with these arrows, lies over the identity of the pullback. -/
private lemma isHomLift_id_of_comp_eq
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {A₁ A₂ A : C} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c) {X X' Y₁ Y₂ : F} (i : X ⟶ X')
    (g₁ : X ⟶ Y₁) (g₂ : X ⟶ Y₂) (g₁' : X' ⟶ Y₁) (g₂' : X' ⟶ Y₂)
    (hg₁ : p.IsHomLift c.fst g₁) (hg₂ : p.IsHomLift c.snd g₂)
    (hg₁' : p.IsHomLift c.fst g₁') (hg₂' : p.IsHomLift c.snd g₂')
    (hi₁ : i ≫ g₁' = g₁) (hi₂ : i ≫ g₂' = g₂) : p.IsHomLift (𝟙 c.pt) i := by
  let hX := CategoryTheory.IsHomLift.domain_eq p c.fst g₁
  let hX' := CategoryTheory.IsHomLift.domain_eq p c.fst g₁'
  have key : ∀ {Y : F} {B : C} (s : c.pt ⟶ B) (u : X ⟶ Y) (u' : X' ⟶ Y)
      [p.IsHomLift s u] [p.IsHomLift s u'], i ≫ u' = u →
        (p.map i ≫ eqToHom hX') ≫ s = eqToHom hX ≫ s := by
    intro Y B s u u' _ _ h
    have e := congrArg p.map h
    rw [p.map_comp, CategoryTheory.IsHomLift.fac' p s u',
      CategoryTheory.IsHomLift.fac' p s u] at e
    simpa using (cancel_mono (eqToHom _)).1 (by simpa [Category.assoc] using e)
  apply CategoryTheory.IsHomLift.of_commsq p (𝟙 c.pt) i hX hX'
  simpa using PullbackCone.IsLimit.hom_ext hc (key _ g₁ g₁' hi₁) (key _ g₂ g₂' hi₂)

private lemma fiber_product_unique
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} (hp : IsCofiberedInGroupoids p)
    {A₁ A₂ A : C} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c) (x : p.Fiber A)
    (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x)
    (z z' : Lift p (c.fst ≫ f₁) x)
    (hz : IsFiberProductOf c z a₁ a₂)
    (hz' : IsFiberProductOf c z' a₁ a₂) : Nonempty (z ≅ z') := by
  rcases hz with ⟨g₁, g₂, comm, hg₁, hg₂, hfac₁, _, hlim⟩
  rcases hz' with ⟨g₁', g₂', comm', hg₁', hg₂', hfac₁', _, hlim'⟩
  let i : z.obj ≅ z'.obj := hlim.some.conePointUniqueUpToIso hlim'.some
  have hi₁ : i.hom ≫ g₁' = g₁ :=
    IsLimit.conePointUniqueUpToIso_hom_comp hlim.some hlim'.some WalkingCospan.left
  have hi₂ : i.hom ≫ g₂' = g₂ :=
    IsLimit.conePointUniqueUpToIso_hom_comp hlim.some hlim'.some WalkingCospan.right
  have hi := isHomLift_id_of_comp_eq p c hc i.hom g₁ g₂ g₁' g₂' hg₁ hg₂ hg₁' hg₂' hi₁ hi₂
  let l : z ⟶ z' :=
    { hom := i.hom
      isHomLift := hi
      fac := by rw [← hfac₁', ← Category.assoc, hi₁, hfac₁] }
  have : IsIso l := isIso_liftHom hp l
  exact ⟨asIso l⟩

private def lift_iso_obj
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {A' A : C} {f : A' ⟶ A} {x : p.Fiber A}
    {a b : Lift p f x} (i : a ≅ b) : a.obj ≅ b.obj where
  hom := i.hom.hom
  inv := i.inv.hom
  hom_inv_id := congrArg Lift.Hom.hom i.hom_inv_id
  inv_hom_id := congrArg Lift.Hom.hom i.inv_hom_id

private lemma fiber_product_transport
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {A₁ A₂ A : C} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (x : p.Fiber A)
    {z z' : Lift p (c.fst ≫ f₁) x}
    {a₁ a₁' : Lift p f₁ x} {a₂ a₂' : Lift p f₂ x}
    (hz : IsFiberProductOf c z a₁ a₂)
    (i : z ≅ z') (j₁ : a₁ ≅ a₁') (j₂ : a₂ ≅ a₂') :
    IsFiberProductOf c z' a₁' a₂' := by
  rcases hz with ⟨g₁, g₂, comm, hg₁, hg₂, hfac₁, hfac₂, hlim⟩
  let : p.IsHomLift c.fst g₁ := hg₁
  let : p.IsHomLift c.snd g₂ := hg₂
  let g₁' : z'.obj ⟶ a₁'.obj := i.inv.hom ≫ g₁ ≫ j₁.hom.hom
  let g₂' : z'.obj ⟶ a₂'.obj := i.inv.hom ≫ g₂ ≫ j₂.hom.hom
  have hg₁' : p.IsHomLift c.fst g₁' := by
    dsimp [g₁']
    infer_instance
  have hg₂' : p.IsHomLift c.snd g₂' := by
    dsimp [g₂']
    infer_instance
  have hfac₁' : g₁' ≫ a₁'.hom = z'.hom := by
    simp only [g₁', Category.assoc]
    rw [j₁.hom.fac, hfac₁, i.inv.fac]
  have hfac₂' : g₂' ≫ a₂'.hom = z'.hom := by
    simp only [g₂', Category.assoc]
    rw [j₂.hom.fac, hfac₂, i.inv.fac]
  let comm' : g₁' ≫ a₁'.hom = g₂' ≫ a₂'.hom :=
    hfac₁'.trans hfac₂'.symm
  have hpb : IsPullback g₁' g₂' a₁'.hom a₂'.hom := by
    apply (IsPullback.of_isLimit hlim.some).of_iso
      (lift_iso_obj i) (lift_iso_obj j₁) (lift_iso_obj j₂) (Iso.refl x.1)
    · dsimp [g₁', lift_iso_obj]
      show g₁ ≫ j₁.hom.hom = i.hom.hom ≫ (i.inv.hom ≫ g₁ ≫ j₁.hom.hom)
      rw [← Category.assoc, ← Category.assoc]
      have hi : i.hom.hom ≫ i.inv.hom = 𝟙 z.obj :=
        congrArg Lift.Hom.hom i.hom_inv_id
      rw [hi, Category.id_comp]
    · dsimp [g₂', lift_iso_obj]
      show g₂ ≫ j₂.hom.hom = i.hom.hom ≫ (i.inv.hom ≫ g₂ ≫ j₂.hom.hom)
      rw [← Category.assoc, ← Category.assoc]
      have hi : i.hom.hom ≫ i.inv.hom = 𝟙 z.obj :=
        congrArg Lift.Hom.hom i.hom_inv_id
      rw [hi, Category.id_comp]
    · dsimp only [lift_iso_obj]
      simpa only [Iso.refl_hom, Category.comp_id] using j₁.hom.fac.symm
    · dsimp only [lift_iso_obj]
      simpa only [Iso.refl_hom, Category.comp_id] using j₂.hom.fac.symm
  exact ⟨g₁', g₂', comm', hg₁', hg₂', hfac₁', hfac₂', ⟨hpb.isLimit⟩⟩

section QuotientBijection

variable {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type uF} [Category.{vF} F]
  (p : F ⥤ ArtinianLocalAlgCat Λ k)
  (hRS : SatisfiesRS p)
  {A₁ A₂ A : ArtinianLocalAlgCat Λ k}
  {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
  (c : PullbackCone f₁ f₂) (hc : IsLimit c)
  (hsurj : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom)
  (x : p.Fiber A)

private noncomputable def chosenProduct (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x) :
    { z : Lift p (c.fst ≫ f₁) x // IsFiberProductOf c z a₁ a₂ } :=
  Classical.choice (by
    obtain ⟨z, hz⟩ := exists_fiber_product p hRS c hc hsurj x a₁ a₂
    exact ⟨⟨z, hz⟩⟩)

private noncomputable def chosenFactors (z : Lift p (c.fst ≫ f₁) x) :
    { a : Lift p f₁ x × Lift p f₂ x // IsFiberProductOf c z a.1 a.2 } :=
  Classical.choice (by
    obtain ⟨a₁, a₂, hz⟩ := fiber_product_of_lift p hRS c hc hsurj x z
    exact ⟨⟨(a₁, a₂), hz⟩⟩)

private noncomputable def pairToClass
    (a : LiftClasses p f₁ x × LiftClasses p f₂ x) :
    LiftClasses p (c.fst ≫ f₁) x :=
  ThinSkeleton.mk ((chosenProduct p hRS c hc hsurj x
    (Quotient.out a.1) (Quotient.out a.2)).1)

private noncomputable def classToPair
    (z : LiftClasses p (c.fst ≫ f₁) x) :
    LiftClasses p f₁ x × LiftClasses p f₂ x :=
  let a := chosenFactors p hRS c hc hsurj x (Quotient.out z)
  (ThinSkeleton.mk a.1.1, ThinSkeleton.mk a.1.2)

private lemma pairToClass_of_fiber_product
    (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x)
    (z : Lift p (c.fst ≫ f₁) x)
    (hz : IsFiberProductOf c z a₁ a₂) :
    pairToClass p hRS c hc hsurj x (ThinSkeleton.mk a₁, ThinSkeleton.mk a₂) =
      ThinSkeleton.mk z := by
  let b₁ : Lift p f₁ x := Quotient.out (ThinSkeleton.mk a₁)
  let b₂ : Lift p f₂ x := Quotient.out (ThinSkeleton.mk a₂)
  let w := chosenProduct p hRS c hc hsurj x b₁ b₂
  have hb₁ : ThinSkeleton.mk b₁ = ThinSkeleton.mk a₁ := Quotient.out_eq _
  have hb₂ : ThinSkeleton.mk b₂ = ThinSkeleton.mk a₂ := Quotient.out_eq _
  obtain ⟨j₁⟩ : Nonempty (b₁ ≅ a₁) := Quotient.exact hb₁
  obtain ⟨j₂⟩ : Nonempty (b₂ ≅ a₂) := Quotient.exact hb₂
  have hw : IsFiberProductOf c w.1 a₁ a₂ :=
    fiber_product_transport c x w.2 (Iso.refl w.1) j₁ j₂
  have ⟨i⟩ := fiber_product_unique hRS.1 c hc x a₁ a₂ w.1 z hw hz
  change ThinSkeleton.mk w.1 = ThinSkeleton.mk z
  exact Quotient.sound ⟨i⟩

private lemma classToPair_of_fiber_product
    (z : Lift p (c.fst ≫ f₁) x)
    (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x)
    (hz : IsFiberProductOf c z a₁ a₂) :
    classToPair p hRS c hc hsurj x (ThinSkeleton.mk z) =
      (ThinSkeleton.mk a₁, ThinSkeleton.mk a₂) := by
  let w : Lift p (c.fst ≫ f₁) x := Quotient.out (ThinSkeleton.mk z)
  let b := chosenFactors p hRS c hc hsurj x w
  have hw : ThinSkeleton.mk w = ThinSkeleton.mk z := Quotient.out_eq _
  obtain ⟨i⟩ : Nonempty (w ≅ z) := Quotient.exact hw
  have hbz : IsFiberProductOf c z b.1.1 b.1.2 :=
    fiber_product_transport c x b.2 i (Iso.refl _) (Iso.refl _)
  rcases hbz with ⟨gb₁, gb₂, _, hgb₁, hgb₂, hfacb₁, hfacb₂, _⟩
  rcases hz with ⟨ga₁, ga₂, _, hga₁, hga₂, hfaca₁, hfaca₂, _⟩
  obtain ⟨i₁, _⟩ := factor_unique hRS.1 c.fst f₁ x z b.1.1 a₁
    gb₁ ga₁ hgb₁ hga₁ hfacb₁ hfaca₁
  obtain ⟨i₂, _⟩ := factor_unique hRS.1 c.snd f₂ x (liftOfEq p c.condition z) b.1.2 a₂
    gb₂ ga₂ hgb₂ hga₂ hfacb₂ hfaca₂
  change (ThinSkeleton.mk b.1.1, ThinSkeleton.mk b.1.2) =
    (ThinSkeleton.mk a₁, ThinSkeleton.mk a₂)
  exact Prod.ext (Quotient.sound ⟨i₁⟩) (Quotient.sound ⟨i₂⟩)

private noncomputable def liftClassesEquiv :
    (LiftClasses p f₁ x × LiftClasses p f₂ x) ≃
      LiftClasses p (c.fst ≫ f₁) x where
  toFun := pairToClass p hRS c hc hsurj x
  invFun := classToPair p hRS c hc hsurj x
  left_inv := by
    intro a
    let a₁ : Lift p f₁ x := Quotient.out a.1
    let a₂ : Lift p f₂ x := Quotient.out a.2
    let w := chosenProduct p hRS c hc hsurj x a₁ a₂
    calc
      classToPair p hRS c hc hsurj x (pairToClass p hRS c hc hsurj x a) =
          (ThinSkeleton.mk a₁, ThinSkeleton.mk a₂) := by
            change classToPair p hRS c hc hsurj x (ThinSkeleton.mk w.1) = _
            exact classToPair_of_fiber_product p hRS c hc hsurj x w.1 a₁ a₂ w.2
      _ = a := Prod.ext (Quotient.out_eq a.1) (Quotient.out_eq a.2)
  right_inv := by
    intro z
    let w : Lift p (c.fst ≫ f₁) x := Quotient.out z
    let a := chosenFactors p hRS c hc hsurj x w
    calc
      pairToClass p hRS c hc hsurj x (classToPair p hRS c hc hsurj x z) =
          ThinSkeleton.mk w := by
            change pairToClass p hRS c hc hsurj x
              (ThinSkeleton.mk a.1.1, ThinSkeleton.mk a.1.2) = _
            exact pairToClass_of_fiber_product p hRS c hc hsurj x a.1.1 a.1.2 w a.2
      _ = z := Quotient.out_eq z

end QuotientBijection

/-- Isomorphism classes of lifts to a fibre product are in bijection with pairs of
isomorphism classes of lifts to the two factors when one structural map is surjective. -/
@[stacks 06JH "product_bijection"]
public theorem liftClassesProdEquivPullback
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (hRS : SatisfiesRS p)
    {A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c)
    (hsurj : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom)
    (x : p.Fiber A) :
    Nonempty (LiftProductEquiv p c x) :=
  ⟨{ equiv := liftClassesEquiv p hRS c hc hsurj x
     maps_pair_to_fiberProduct a₁ a₂ :=
       let w := chosenProduct p hRS c hc hsurj x a₁ a₂
       ⟨w.1, w.2, pairToClass_of_fiber_product p hRS c hc hsurj x a₁ a₂ w.1 w.2⟩ }⟩

end

/-! ### Lifts with one factor fixed -/

section
open CategoryTheory CategoryTheory.Limits
universe u v uF vF

/-- The object at the source of a lift, regarded as an object of the appropriate fibre. -/
public def liftSourceFiber
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {A₁ A : C} {f₁ : A₁ ⟶ A} {x : p.Fiber A}
    (a₁ : Lift p f₁ x) : p.Fiber A₁ :=
  ⟨a₁.obj, CategoryTheory.IsHomLift.domain_eq p f₁ a₁.hom⟩

/-- A lift to the fibre product, viewed as a lift of the original object along the
composite structural map. -/
public def liftToComposite
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {A₁ A : C} {f₁ : A₁ ⟶ A} {x : p.Fiber A}
    (a₁ : Lift p f₁ x) {B : C} {g : B ⟶ A₁}
    (b : Lift p g (liftSourceFiber a₁)) : Lift p (g ≫ f₁) x where
  obj := b.obj
  hom := b.hom ≫ a₁.hom
  isHomLift := @CategoryTheory.IsHomLift.comp _ _ _ _ p _ _ _ _ _ _
    g f₁ b.hom a₁.hom b.isHomLift a₁.isHomLift

/-- The lift `a₂` is obtained by pushing `b` along the second projection when `b` and
`a₂`, with their maps to the fixed lift and the original object, form a pullback. -/
public def IsPushforwardOf
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {A₁ A₂ A : C} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) {x : p.Fiber A} (a₁ : Lift p f₁ x)
    (b : Lift p c.fst (liftSourceFiber a₁)) (a₂ : Lift p f₂ x) : Prop :=
  ∃ (g₂ : b.obj ⟶ a₂.obj)
    (comm : b.hom ≫ a₁.hom = g₂ ≫ a₂.hom),
      p.IsHomLift c.snd g₂ ∧
        Nonempty (IsLimit (PullbackCone.mk b.hom g₂ comm))

/-- A bijection between lifts of a fixed lift to the fibre product and lifts of the
original object over the other factor, characterized by pushforward. -/
public structure FixedLiftEquiv
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    (p : F ⥤ C) {A₁ A₂ A : C} {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (x : p.Fiber A) (a₁ : Lift p f₁ x) where
  /-- The underlying bijection on isomorphism classes of lifts. -/
  equiv : LiftClasses p c.fst (liftSourceFiber a₁) ≃ LiftClasses p f₂ x
  /-- The bijection sends a lift precisely to its pushforward along the second
  projection. -/
  maps_to_pushforward : ∀ (b : Lift p c.fst (liftSourceFiber a₁)) (a₂ : Lift p f₂ x),
    equiv (ThinSkeleton.mk b) = ThinSkeleton.mk a₂ ↔ IsPushforwardOf c a₁ b a₂

private def liftToCompositeFunctor
    {C : Type u} [Category.{v} C] {F : Type uF} [Category.{vF} F]
    {p : F ⥤ C} {A₁ A : C} {f₁ : A₁ ⟶ A} {x : p.Fiber A}
    (a₁ : Lift p f₁ x) {B : C} {g : B ⟶ A₁} :
    Lift p g (liftSourceFiber a₁) ⥤ Lift p (g ≫ f₁) x where
  obj := liftToComposite a₁
  map := fun {b b'} h =>
    { hom := h.hom
      isHomLift := h.isHomLift
      fac := by
        change h.hom ≫ (b'.hom ≫ a₁.hom) = b.hom ≫ a₁.hom
        calc
          h.hom ≫ (b'.hom ≫ a₁.hom) = (h.hom ≫ b'.hom) ≫ a₁.hom :=
            (Category.assoc _ _ _).symm
          _ = b.hom ≫ a₁.hom := by rw [h.fac] }

private lemma productEquiv_symm_of_fiberProduct
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (hRS : SatisfiesRS p)
    {A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c)
    (x : p.Fiber A) (E : LiftProductEquiv p c x)
    (z : Lift p (c.fst ≫ f₁) x) (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x)
    (hz : IsFiberProductOf c z a₁ a₂) :
    E.equiv.symm (ThinSkeleton.mk z) = (ThinSkeleton.mk a₁, ThinSkeleton.mk a₂) := by
  obtain ⟨z', hz', heq⟩ := E.maps_pair_to_fiberProduct a₁ a₂
  obtain ⟨i⟩ := fiber_product_unique hRS.1 c hc x a₁ a₂ z' z hz' hz
  have hclass : ThinSkeleton.mk z' = ThinSkeleton.mk z := Quotient.sound ⟨i⟩
  apply E.equiv.injective
  calc
    E.equiv (E.equiv.symm (ThinSkeleton.mk z)) = ThinSkeleton.mk z := Equiv.apply_symm_apply _ _
    _ = ThinSkeleton.mk z' := hclass.symm
    _ = E.equiv (ThinSkeleton.mk a₁, ThinSkeleton.mk a₂) := heq.symm

private lemma productEquiv_eq_fiberProduct
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (_hRS : SatisfiesRS p)
    {A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (x : p.Fiber A) (E : LiftProductEquiv p c x)
    (z : Lift p (c.fst ≫ f₁) x) (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x)
    (heq : E.equiv (ThinSkeleton.mk a₁, ThinSkeleton.mk a₂) = ThinSkeleton.mk z) :
    IsFiberProductOf c z a₁ a₂ := by
  obtain ⟨z', hz', heq'⟩ := E.maps_pair_to_fiberProduct a₁ a₂
  have hclass : ThinSkeleton.mk z' = ThinSkeleton.mk z := heq'.symm.trans heq
  obtain ⟨i⟩ : Nonempty (z' ≅ z) := Quotient.exact hclass
  exact fiber_product_transport c x hz' i (Iso.refl _) (Iso.refl _)

private lemma fixedDecompositionFirst
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (hRS : SatisfiesRS p)
    {A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c)
    (hsurj : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom)
    (x : p.Fiber A) (a₁ : Lift p f₁ x) (E : LiftProductEquiv p c x)
    (b : Lift p c.fst (liftSourceFiber a₁)) :
    (E.equiv.symm
      ((ThinSkeleton.map (liftToCompositeFunctor a₁)).obj (ThinSkeleton.mk b))).1 =
        ThinSkeleton.mk a₁ := by
  let z := liftToComposite a₁ b
  obtain ⟨a₁', a₂', hz⟩ := fiber_product_of_lift p hRS c hc hsurj x z
  have hpair := productEquiv_symm_of_fiberProduct p hRS c hc x E z a₁' a₂' hz
  rcases hz with ⟨g₁, g₂, comm, hg₁, hg₂, hfac₁, hfac₂, hlim⟩
  obtain ⟨i, _⟩ := factor_unique hRS.1 c.fst f₁ x z a₁' a₁ g₁ b.hom
    hg₁ b.isHomLift hfac₁ (by rfl)
  change (E.equiv.symm (ThinSkeleton.mk z)).1 = ThinSkeleton.mk a₁
  rw [hpair]
  exact Quotient.sound ⟨i⟩

private lemma isPushforward_iff_fiberProduct
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (hRS : SatisfiesRS p)
    {A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (_hc : IsLimit c)
    (x : p.Fiber A) (a₁ : Lift p f₁ x)
    (b : Lift p c.fst (liftSourceFiber a₁)) (a₂ : Lift p f₂ x) :
    IsPushforwardOf c a₁ b a₂ ↔
      IsFiberProductOf c (liftToComposite a₁ b) a₁ a₂ := by
  constructor
  · rintro ⟨g₂, comm, hg₂, hlim⟩
    refine ⟨b.hom, g₂, comm, b.isHomLift, hg₂, rfl, comm.symm, hlim⟩
  · rintro ⟨g₁, g₂, comm, hg₁, hg₂, hfac₁, hfac₂, hlim⟩
    obtain ⟨j, hj⟩ := factor_unique hRS.1 c.fst f₁ x
      (liftToComposite a₁ b) a₁ a₁ g₁ b.hom hg₁ b.isHomLift hfac₁ (by rfl)
    let g₁' : (liftToComposite a₁ b).obj ⟶ a₁.obj := g₁ ≫ j.hom.hom
    have hg₁' : p.IsHomLift c.fst g₁' := by
      dsimp [g₁']
      infer_instance
    have hfac₁' : g₁' ≫ a₁.hom = (liftToComposite a₁ b).hom := by
      rw [Category.assoc, j.hom.fac, hfac₁]
    let comm' : g₁' ≫ a₁.hom = g₂ ≫ a₂.hom := hfac₁'.trans hfac₂.symm
    have hpb : IsPullback g₁' g₂ a₁.hom a₂.hom := by
      apply (IsPullback.of_isLimit hlim.some).of_iso
        (Iso.refl (liftToComposite a₁ b).obj) (lift_iso_obj j)
        (Iso.refl a₂.obj) (Iso.refl x.1)
      · change g₁ ≫ j.hom.hom = 𝟙 (liftToComposite a₁ b).obj ≫ g₁'
        simp [g₁']
      · change g₂ ≫ 𝟙 a₂.obj = 𝟙 (liftToComposite a₁ b).obj ≫ g₂
        simp
      · dsimp only [lift_iso_obj]
        simpa only [Iso.refl_hom, Category.comp_id] using j.hom.fac.symm
      · change a₂.hom ≫ 𝟙 x.1 = 𝟙 a₂.obj ≫ a₂.hom
        simp
    have hlim' : IsLimit (PullbackCone.mk g₁' g₂ comm') := by
      convert hpb.isLimit using 1
      rfl
    have hg₂' : p.IsHomLift c.snd g₂ := hg₂
    have hfirst : g₁' = b.hom := hj
    have commB : b.hom ≫ a₁.hom = g₂ ≫ a₂.hom := by
      rw [← hfirst]
      exact comm'
    have hlimB : IsLimit (PullbackCone.mk b.hom g₂ commB) := by
      have hcone : PullbackCone.mk g₁' g₂ comm' ≅
          PullbackCone.mk b.hom g₂ commB :=
        PullbackCone.ext (Iso.refl (liftToComposite a₁ b).obj)
          (by
            change g₁' = 𝟙 (liftToComposite a₁ b).obj ≫ b.hom
            exact hfirst.trans (Category.id_comp _).symm)
          (by
            change g₂ = 𝟙 (liftToComposite a₁ b).obj ≫ g₂
            exact (Category.id_comp _).symm)
      exact IsLimit.ofIsoLimit hlim' hcone
    exact ⟨g₂, commB, hg₂', ⟨hlimB⟩⟩

private lemma fixedFiberProduct_unique
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (hRS : SatisfiesRS p)
    {A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c) (x : p.Fiber A)
    (a₁ : Lift p f₁ x) (a₂ : Lift p f₂ x)
    (b b' : Lift p c.fst (liftSourceFiber a₁))
    (hb : IsPushforwardOf c a₁ b a₂) (hb' : IsPushforwardOf c a₁ b' a₂) :
    Nonempty (b ≅ b') := by
  rcases hb with ⟨g₂, comm, hg₂, hlim⟩
  rcases hb' with ⟨g₂', comm', hg₂', hlim'⟩
  let i : b.obj ≅ b'.obj := hlim.some.conePointUniqueUpToIso hlim'.some
  have hi₁ : i.hom ≫ b'.hom = b.hom :=
    IsLimit.conePointUniqueUpToIso_hom_comp hlim.some hlim'.some WalkingCospan.left
  have hi₂ : i.hom ≫ g₂' = g₂ :=
    IsLimit.conePointUniqueUpToIso_hom_comp hlim.some hlim'.some WalkingCospan.right
  have hi := isHomLift_id_of_comp_eq p c hc i.hom b.hom g₂ b'.hom g₂'
    b.isHomLift hg₂ b'.isHomLift hg₂' hi₁ hi₂
  let l : b ⟶ b' :=
    { hom := i.hom
      isHomLift := hi
      fac := hi₁ }
  have : IsIso l := isIso_liftHom hRS.1 l
  exact ⟨asIso l⟩

private noncomputable def chosenFixedLift
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    {A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (x : p.Fiber A) (a₁ : Lift p f₁ x)
    (E : LiftProductEquiv p c x) (a₂ : Lift p f₂ x) :
    {b : Lift p c.fst (liftSourceFiber a₁) // IsPushforwardOf c a₁ b a₂} := by
  classical
  let h : ∃ b : Lift p c.fst (liftSourceFiber a₁), IsPushforwardOf c a₁ b a₂ := by
    obtain ⟨z, hz, heq⟩ := E.maps_pair_to_fiberProduct a₁ a₂
    rcases hz with ⟨g₁, g₂, comm, hg₁, hg₂, hfac₁, hfac₂, hlim⟩
    let b : Lift p c.fst (liftSourceFiber a₁) := ⟨z.obj, g₁, hg₁⟩
    have comm' : b.hom ≫ a₁.hom = g₂ ≫ a₂.hom := hfac₁.trans hfac₂.symm
    exact ⟨b, g₂, comm', hg₂, ⟨by convert hlim.some using 1 <;> rfl⟩⟩
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/-- After fixing a lift over the first factor, pushing along the second projection gives
a bijection from lifts of the fixed object to lifts over the second factor. -/
@[stacks 06JH "fixed_lift_bijection"]
public theorem liftClassesEquivOfFixedLift
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (hRS : SatisfiesRS p)
    {A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A}
    (c : PullbackCone f₁ f₂) (hc : IsLimit c)
    (hsurj : Function.Surjective f₁.hom ∨ Function.Surjective f₂.hom)
    (x : p.Fiber A) (a₁ : Lift p f₁ x) :
    Nonempty (FixedLiftEquiv p c x a₁) := by
  classical
  obtain ⟨E⟩ := liftClassesProdEquivPullback p hRS c hc hsurj x
  let T : ThinSkeleton (Lift p c.fst (liftSourceFiber a₁)) ⥤
      ThinSkeleton (Lift p (c.fst ≫ f₁) x) :=
    ThinSkeleton.map (liftToCompositeFunctor (a₁ := a₁) (B := c.pt) (g := c.fst))
  let toSecond : LiftClasses p c.fst (liftSourceFiber a₁) → LiftClasses p f₂ x :=
    fun b => (E.equiv.symm (T.obj b)).2
  let fromSecond : LiftClasses p f₂ x → LiftClasses p c.fst (liftSourceFiber a₁) :=
    fun a₂ => ThinSkeleton.mk
      (chosenFixedLift p c x a₁ E (Quotient.out a₂)).1
  have hmaps : ∀ (b : Lift p c.fst (liftSourceFiber a₁)) (a₂ : Lift p f₂ x),
      toSecond (ThinSkeleton.mk b) = ThinSkeleton.mk a₂ ↔ IsPushforwardOf c a₁ b a₂ := by
    intro b a₂
    change (E.equiv.symm (ThinSkeleton.mk (liftToComposite a₁ b))).2 =
      ThinSkeleton.mk a₂ ↔ IsPushforwardOf c a₁ b a₂
    have hfirst := fixedDecompositionFirst p hRS c hc hsurj x a₁ E b
    change (E.equiv.symm (ThinSkeleton.mk (liftToComposite a₁ b))).1 =
      ThinSkeleton.mk a₁ at hfirst
    constructor
    · intro hsecond
      have hpair : E.equiv.symm (ThinSkeleton.mk (liftToComposite a₁ b)) =
          (ThinSkeleton.mk a₁, ThinSkeleton.mk a₂) := Prod.ext hfirst hsecond
      have heq : E.equiv (ThinSkeleton.mk a₁, ThinSkeleton.mk a₂) =
          ThinSkeleton.mk (liftToComposite a₁ b) := by
        calc
          E.equiv (ThinSkeleton.mk a₁, ThinSkeleton.mk a₂) =
              E.equiv (E.equiv.symm (ThinSkeleton.mk (liftToComposite a₁ b))) :=
                congrArg E.equiv hpair.symm
          _ = ThinSkeleton.mk (liftToComposite a₁ b) := Equiv.apply_symm_apply _ _
      have hfp := productEquiv_eq_fiberProduct p hRS c x E
        (liftToComposite a₁ b) a₁ a₂ heq
      exact (isPushforward_iff_fiberProduct p hRS c hc x a₁ b a₂).2 hfp
    · intro hpush
      have hfp := (isPushforward_iff_fiberProduct p hRS c hc x a₁ b a₂).1 hpush
      have hpair := productEquiv_symm_of_fiberProduct p hRS c hc x E
        (liftToComposite a₁ b) a₁ a₂ hfp
      exact congrArg Prod.snd hpair
  refine ⟨{
    equiv := {
      toFun := toSecond
      invFun := fromSecond
      left_inv := ?_
      right_inv := ?_ }
    maps_to_pushforward := hmaps }⟩
  · intro q
    let b : Lift p c.fst (liftSourceFiber a₁) := Quotient.out q
    let a₂c : LiftClasses p f₂ x := toSecond q
    let a₂ : Lift p f₂ x := Quotient.out a₂c
    let b' := chosenFixedLift p c x a₁ E a₂
    have hbq : ThinSkeleton.mk b = q := Quotient.out_eq q
    have ha₂ : ThinSkeleton.mk a₂ = a₂c := Quotient.out_eq a₂c
    have hto : toSecond (ThinSkeleton.mk b) = ThinSkeleton.mk a₂ := by
      calc
        toSecond (ThinSkeleton.mk b) = a₂c := by
          dsimp [a₂c]
          rw [hbq]
        _ = ThinSkeleton.mk a₂ := ha₂.symm
    have hpush : IsPushforwardOf c a₁ b a₂ := (hmaps b a₂).1 hto
    obtain ⟨i⟩ := fixedFiberProduct_unique p hRS c hc x a₁ a₂ b b'.1
      hpush b'.2
    change ThinSkeleton.mk b'.1 = q
    calc
      ThinSkeleton.mk b'.1 = ThinSkeleton.mk b := Quotient.sound ⟨i.symm⟩
      _ = q := hbq
  · intro a₂c
    let a₂ : Lift p f₂ x := Quotient.out a₂c
    let b := chosenFixedLift p c x a₁ E a₂
    have ha₂ : ThinSkeleton.mk a₂ = a₂c := Quotient.out_eq a₂c
    calc
      toSecond (fromSecond a₂c) = ThinSkeleton.mk a₂ :=
        (hmaps b.1 a₂).2 b.2
      _ = a₂c := ha₂

end

/-! ### Lifts over a composite of fibre squares -/

section
open CategoryTheory CategoryTheory.Limits

universe uF vF

/-- Let `left` be a fibre square of a surjection `g : A₁' ⟶ A₁` and the first projection of
`right`. Isomorphism classes of lifts of the source of `a₁` along `left.fst ≫ g` are in
bijection with pairs of isomorphism classes of lifts of it along `g` and along `right.fst`. -/
@[stacks 06JH "composite_square_bijection"]
public theorem liftClassesEquivProdOfCompositePullback
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (hRS : SatisfiesRS p)
    {A₁' A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A} {g : A₁' ⟶ A₁}
    (right : PullbackCone f₁ f₂)
    (left : PullbackCone g right.fst)
    (hleft : IsLimit left)
    (hg : Function.Surjective g.hom)
    (x : p.Fiber A) (a₁ : Lift p f₁ x) :
    Nonempty (LiftClasses p (left.fst ≫ g) (liftSourceFiber a₁) ≃
      LiftClasses p g (liftSourceFiber a₁) ×
        LiftClasses p right.fst (liftSourceFiber a₁)) :=
  ⟨(Classical.choice (liftClassesProdEquivPullback p hRS left hleft (Or.inl hg)
    (liftSourceFiber a₁))).equiv.symm⟩

/-- Let `right` be a fibre square of `f₁` and `f₂` with `f₁` surjective, and `left` a fibre
square of a surjection `g : A₁' ⟶ A₁` and the first projection of `right`. Isomorphism classes
of lifts of the source of `a₁` along `left.fst ≫ g` are in bijection with pairs of an
isomorphism class of lifts of it along `g` and an isomorphism class of lifts of `x` along
`f₂`. -/
@[stacks 06JH "composite_square_bijection"]
public theorem liftClassesEquivOuterProdOfCompositePullback
    {Λ : Type*} {k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (hRS : SatisfiesRS p)
    {A₁' A₁ A₂ A : ArtinianLocalAlgCat Λ k}
    {f₁ : A₁ ⟶ A} {f₂ : A₂ ⟶ A} {g : A₁' ⟶ A₁}
    (right : PullbackCone f₁ f₂)
    (hright : IsLimit right)
    (left : PullbackCone g right.fst)
    (hleft : IsLimit left)
    (hg : Function.Surjective g.hom)
    (hf₁ : Function.Surjective f₁.hom)
    (x : p.Fiber A) (a₁ : Lift p f₁ x) :
    Nonempty (LiftClasses p (left.fst ≫ g) (liftSourceFiber a₁) ≃
      LiftClasses p g (liftSourceFiber a₁) × LiftClasses p f₂ x) :=
  ⟨(Classical.choice (liftClassesEquivProdOfCompositePullback p hRS right left hleft hg x a₁)).trans
    (Equiv.prodCongr (Equiv.refl _)
      (Classical.choice (liftClassesEquivOfFixedLift p hRS right hright (Or.inl hf₁) x a₁)).equiv)⟩

end

end Deformation
