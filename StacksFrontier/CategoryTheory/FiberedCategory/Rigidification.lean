module

public import Mathlib.Algebra.Category.Grp.Basic
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberComp
public import StacksFrontier.CategoryTheory.Sites.Stack.DescentDataEquivalence
import Mathlib.Tactic.Group

/-!
# Fibred categories rigidified by a presheaf of groups

Let `p : 𝒳 ⥤ 𝒮` be a fibred category and let `𝒜` be a presheaf of groups on `𝒮`. A
*rigidification* of `p` by `𝒜` attaches to every morphism `φ : x ⟶ y` of `𝒳` an element of
`𝒜 (p x)`, multiplicatively in composites, so that for any two objects `x`, `y` and any
morphism `f : p x ⟶ p y` of the base the morphisms `x ⟶ y` over `f` are in bijection with
`𝒜 (p x)`. The model is the classifying stack of a group: there every fibre is equivalent to
the one-object groupoid of `𝒜 (U)`, and a morphism over `f` is a section of `𝒜` over its
source.

For such a `p` a descent datum relative to a family `{X i ⟶ T}` is the same thing as a
non-abelian Čech `1`-cocycle of the family with values in `𝒜`. This file makes the comparison
explicit in the direction needed to *build* descent data: a morphism between two chosen
pullbacks `f₁^* z₁ ⟶ f₂^* z₂` has a *normalized element*, its element corrected by the elements
of the two chosen cartesian lifts, and the normalized elements of the pullback functors, of the
composition constraints and of the gluing morphisms of a descent datum are computed. In
particular every cocycle gives a descent datum, two descent data whose cocycles differ by a
coboundary are isomorphic, and pulling back a descent datum along a morphism of families
restricts its cocycle up to an explicit coboundary.

## Main definitions

* `CategoryTheory.Functor.Rigidification`: a rigidification of `p` by `𝒜`.
* `CategoryTheory.Functor.Rigidification.eltOver`: the element of a morphism lying over a
  given morphism of the base, read over the source of that morphism.
* `CategoryTheory.Functor.Rigidification.fiberElt` and
  `CategoryTheory.Functor.Rigidification.cartElt`: the element of a morphism of a fibre, and
  of a chosen cartesian lift.
* `CategoryTheory.Functor.Rigidification.pullElt`: the normalized element of a morphism between
  two chosen pullbacks.
* `CategoryTheory.Functor.FamilyCocycle`: a Čech `1`-cocycle of a family with values in `𝒜`, its
  twist by a Čech `0`-cochain, its pullback along a morphism of families, and the cocycle
  `CategoryTheory.Functor.FamilyCocycle.ofPair` of a two-member family of monomorphisms;
  `CategoryTheory.Functor.FamilyCocycle.IsTorsionClass` says its Čech class is torsion.
* `CategoryTheory.Functor.Rigidification.IsRepresentedBy` and
  `CategoryTheory.Functor.Rigidification.descentDatumOfCocycle`: a descent datum represented by
  a cocycle, and the descent datum of a cocycle.

## Main results

* `CategoryTheory.Functor.Rigidification.pullElt_pullHom`: the normalized element is compatible
  with further pullback.
* `CategoryTheory.Functor.Rigidification.isoOfIsRepresentedBy`: descent data represented by
  cohomologous cocycles are isomorphic.
* `CategoryTheory.Functor.Rigidification.map_mul_val_eq_of_isRepresentedBy`: a morphism of
  descent data is a cochain relating their cocycles.
* `CategoryTheory.Functor.Rigidification.isRepresentedBy_pull`: the cocycle of a pulled-back
  descent datum.

## Implementation notes

The chosen cartesian lifts of a fibred category are chosen by `Classical.choice`, so their
elements are not known. They cancel out of every statement about normalized elements, which is
why those, and not the elements themselves, are what the descent data are compared through.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Functor

open IsHomLift IsFibered

universe w v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- A *rigidification* of a functor `p : 𝒳 ⥤ 𝒮` by a presheaf of groups `𝒜` on `𝒮`: an element
`elt φ` of `𝒜 (p x)` for every morphism `φ : x ⟶ y` of `𝒳`, multiplicative in composites
(the element of the second factor being restricted along the image of the first), such that the
morphisms `x ⟶ y` lying over a given `f : p x ⟶ p y` are in bijection with `𝒜 (p x)` through
`elt`. -/
structure Rigidification (p : 𝒳 ⥤ 𝒮) (𝒜 : 𝒮ᵒᵖ ⥤ GrpCat.{w}) where
  /-- The element of a morphism, a section of `𝒜` over the image of its source. -/
  elt {x y : 𝒳} (φ : x ⟶ y) : 𝒜.obj (op (p.obj x))
  /-- The element of a composite. -/
  elt_comp {x y z : 𝒳} (φ : x ⟶ y) (χ : y ⟶ z) :
    elt (φ ≫ χ) = elt φ * 𝒜.map (p.map φ).op (elt χ)
  /-- A morphism over a given morphism of the base is determined by its element, and every
  element occurs. -/
  existsUnique (x y : 𝒳) (f : p.obj x ⟶ p.obj y) (a : 𝒜.obj (op (p.obj x))) :
    ∃! φ : x ⟶ y, p.map φ = f ∧ elt φ = a

namespace Rigidification

variable {p : 𝒳 ⥤ 𝒮} {𝒜 : 𝒮ᵒᵖ ⥤ GrpCat.{w}} (ρ : Rigidification p 𝒜)

/-- The element of an identity is the unit. -/
@[simp]
lemma elt_id (x : 𝒳) : ρ.elt (𝟙 x) = 1 := by
  have h := ρ.elt_comp (𝟙 x) (𝟙 x)
  rw [Category.comp_id, p.map_id, op_id, 𝒜.map_id] at h
  exact left_eq_mul.mp h

/-! ### Elements of morphisms lying over a morphism of the base -/

/-- The element of a morphism `φ` lying over `f : R ⟶ S`, read in `𝒜 R`. -/
def eltOver {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [p.IsHomLift f φ] : 𝒜.obj (op R) :=
  𝒜.map (eqToHom (domain_eq p f φ).symm).op (ρ.elt φ)

/-- Over its own image a morphism has its own element. -/
@[simp]
lemma eltOver_map {a b : 𝒳} (φ : a ⟶ b) : ρ.eltOver (p.map φ) φ = ρ.elt φ := by
  simp [eltOver]

/-- The element over a base morphism depends on the base morphism and the morphism only. -/
lemma eltOver_congr {R S : 𝒮} {a b : 𝒳} {f f' : R ⟶ S} {φ φ' : a ⟶ b} (hf : f = f')
    (hφ : φ = φ') [p.IsHomLift f φ] [p.IsHomLift f' φ'] :
    ρ.eltOver f φ = ρ.eltOver f' φ' := by
  subst hf hφ
  rfl

/-- The element of a composite of morphisms lying over two composable morphisms of the base. -/
lemma eltOver_comp {R S T : 𝒮} {a b c : 𝒳} (f : R ⟶ S) (g : S ⟶ T) (φ : a ⟶ b) (χ : b ⟶ c)
    [p.IsHomLift f φ] [p.IsHomLift g χ] :
    ρ.eltOver (f ≫ g) (φ ≫ χ) = ρ.eltOver f φ * 𝒜.map f.op (ρ.eltOver g χ) := by
  have ha := domain_eq p f φ
  have hb := codomain_eq p f φ
  have hc := codomain_eq p g χ
  subst ha hb hc
  obtain rfl := eq_of_isHomLift p f φ
  obtain rfl := eq_of_isHomLift p g χ
  rw [ρ.eltOver_congr (p.map_comp φ χ).symm rfl, eltOver_map, eltOver_map, eltOver_map,
    ρ.elt_comp]

/-- Over a given morphism of the base, a morphism between two given objects is determined by
its element, and every element occurs. -/
lemma existsUnique_eltOver {R S : 𝒮} {a b : 𝒳} (ha : p.obj a = R) (hb : p.obj b = S)
    (f : R ⟶ S) (α : 𝒜.obj (op R)) :
    ∃! φ : a ⟶ b, ∃ _ : p.IsHomLift f φ, ρ.eltOver f φ = α := by
  subst ha hb
  obtain ⟨φ, ⟨hφ, he⟩, huniq⟩ := ρ.existsUnique a b f α
  subst hφ
  refine ⟨φ, ⟨inferInstance, by rw [eltOver_map, he]⟩, ?_⟩
  rintro φ' ⟨hφ', he'⟩
  have hφ'' : p.map φ' = p.map φ := (eq_of_isHomLift p _ φ').symm
  refine huniq φ' ⟨hφ'', ?_⟩
  rw [← eltOver_map, ← he']
  exact ρ.eltOver_congr hφ'' rfl

/-- Two morphisms over the same morphism of the base with the same element are equal. -/
lemma eq_of_eltOver_eq {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) {φ φ' : a ⟶ b} [p.IsHomLift f φ]
    [p.IsHomLift f φ'] (h : ρ.eltOver f φ = ρ.eltOver f φ') : φ = φ' :=
  (ρ.existsUnique_eltOver (domain_eq p f φ) (codomain_eq p f φ) f (ρ.eltOver f φ)).unique
    ⟨inferInstance, rfl⟩ ⟨inferInstance, h.symm⟩

/-! ### Elements of morphisms of the fibres and of the chosen cartesian lifts -/

/-- The element of a morphism of the fibre over `Y`, read in `𝒜 Y`. -/
def fiberElt {Y : 𝒮} {a b : p.Fiber Y} (ψ : a ⟶ b) : 𝒜.obj (op Y) :=
  haveI := ψ.2
  ρ.eltOver (𝟙 Y) ψ.1

/-- The element of a composite of morphisms of a fibre is the product of their elements. -/
@[simp]
lemma fiberElt_comp {Y : 𝒮} {a b c : p.Fiber Y} (ψ : a ⟶ b) (ψ' : b ⟶ c) :
    ρ.fiberElt (ψ ≫ ψ') = ρ.fiberElt ψ * ρ.fiberElt ψ' := by
  have := ψ.2
  have := ψ'.2
  have := (ψ ≫ ψ').2
  have h := ρ.eltOver_comp (𝟙 Y) (𝟙 Y) ψ.1 ψ'.1
  rw [op_id, 𝒜.map_id] at h
  exact (ρ.eltOver_congr (Category.comp_id _).symm rfl).trans h

/-- The element of an identity of a fibre is the unit. -/
@[simp]
lemma fiberElt_id {Y : 𝒮} (a : p.Fiber Y) : ρ.fiberElt (𝟙 a) = 1 := by
  have h := ρ.fiberElt_comp (𝟙 a) (𝟙 a)
  rw [Category.comp_id] at h
  exact left_eq_mul.mp h

/-- A morphism of a fibre is determined by its element. -/
lemma fiberElt_injective {Y : 𝒮} {a b : p.Fiber Y} :
    Function.Injective (ρ.fiberElt (a := a) (b := b)) := fun _ _ h =>
  Fiber.hom_ext (ρ.eq_of_eltOver_eq (𝟙 Y) h)

/-- Every element of `𝒜 Y` is the element of a morphism between any two given objects of the
fibre over `Y`. -/
lemma exists_fiberElt {Y : 𝒮} (a b : p.Fiber Y) (α : 𝒜.obj (op Y)) :
    ∃ ψ : a ⟶ b, ρ.fiberElt ψ = α := by
  obtain ⟨φ, ⟨hφ, he⟩, -⟩ := ρ.existsUnique_eltOver a.2 b.2 (𝟙 Y) α
  exact ⟨⟨φ, hφ⟩, he⟩

/-- The morphism between two objects of a fibre with a prescribed element. -/
def fiberHomOfElt {Y : 𝒮} (a b : p.Fiber Y) (α : 𝒜.obj (op Y)) : a ⟶ b :=
  (ρ.exists_fiberElt a b α).choose

@[simp]
lemma fiberElt_fiberHomOfElt {Y : 𝒮} (a b : p.Fiber Y) (α : 𝒜.obj (op Y)) :
    ρ.fiberElt (ρ.fiberHomOfElt a b α) = α :=
  (ρ.exists_fiberElt a b α).choose_spec

/-- The element of the inverse of an isomorphism of a fibre is the inverse of its element. -/
@[simp]
lemma fiberElt_inv {Y : 𝒮} {a b : p.Fiber Y} (e : a ≅ b) :
    ρ.fiberElt e.inv = (ρ.fiberElt e.hom)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← fiberElt_comp, e.hom_inv_id, fiberElt_id])

/-- Restriction along an identity of the base is the identity. -/
lemma map_op_id_apply (Y : 𝒮) (α : 𝒜.obj (op Y)) : 𝒜.map (𝟙 Y).op α = α := by
  rw [op_id, 𝒜.map_id]
  rfl

/-- The isomorphism between two objects of a fibre with a prescribed element. -/
def fiberIsoOfElt {Y : 𝒮} (a b : p.Fiber Y) (α : 𝒜.obj (op Y)) : a ≅ b where
  hom := ρ.fiberHomOfElt a b α
  inv := ρ.fiberHomOfElt b a α⁻¹
  hom_inv_id := ρ.fiberElt_injective (by simp)
  inv_hom_id := ρ.fiberElt_injective (by simp)

@[simp]
lemma fiberElt_fiberIsoOfElt_hom {Y : 𝒮} (a b : p.Fiber Y) (α : 𝒜.obj (op Y)) :
    ρ.fiberElt (ρ.fiberIsoOfElt a b α).hom = α :=
  ρ.fiberElt_fiberHomOfElt a b α

/-! ### Chosen pullbacks and normalized elements -/

section Pullback

variable [p.IsFibered]

/-- The element of the chosen cartesian lift of `f : Y ⟶ X` ending at `z`. -/
def cartElt {X Y : 𝒮} (z : p.Fiber X) (f : Y ⟶ X) : 𝒜.obj (op Y) :=
  ρ.eltOver f (IsPreFibered.pullbackMap z.2 f)

/-- The *normalized element* of a morphism `f₁^* z₁ ⟶ f₂^* z₂` between two chosen pullbacks: its
element, corrected on both sides by the elements of the chosen cartesian lifts. It is the element
that the morphism would have if the two chosen lifts had the unit for their elements. -/
def pullElt {X₁ X₂ Y : 𝒮} {z₁ : p.Fiber X₁} {z₂ : p.Fiber X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (ψ : pullbackFiber p z₁ f₁ ⟶ pullbackFiber p z₂ f₂) : 𝒜.obj (op Y) :=
  (ρ.cartElt z₁ f₁)⁻¹ * ρ.fiberElt ψ * ρ.cartElt z₂ f₂

/-- The normalized element of a composite is the product of the normalized elements. -/
@[simp]
lemma pullElt_comp {X₁ X₂ X₃ Y : 𝒮} {z₁ : p.Fiber X₁} {z₂ : p.Fiber X₂} {z₃ : p.Fiber X₃}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃} (ψ : pullbackFiber p z₁ f₁ ⟶ pullbackFiber p z₂ f₂)
    (ψ' : pullbackFiber p z₂ f₂ ⟶ pullbackFiber p z₃ f₃) :
    ρ.pullElt (ψ ≫ ψ') = ρ.pullElt ψ * ρ.pullElt ψ' := by
  simp only [pullElt, fiberElt_comp]
  group

/-- The normalized element of an identity is the unit. -/
@[simp]
lemma pullElt_id {X Y : 𝒮} (z : p.Fiber X) (f : Y ⟶ X) :
    ρ.pullElt (𝟙 (pullbackFiber p z f)) = 1 := by
  simp [pullElt]

/-- A morphism between two chosen pullbacks is determined by its normalized element. -/
lemma pullElt_injective {X₁ X₂ Y : 𝒮} {z₁ : p.Fiber X₁} {z₂ : p.Fiber X₂} {f₁ : Y ⟶ X₁}
    {f₂ : Y ⟶ X₂} :
    Function.Injective (ρ.pullElt (z₁ := z₁) (z₂ := z₂) (f₁ := f₁) (f₂ := f₂)) := fun _ _ h =>
  ρ.fiberElt_injective (mul_left_cancel (mul_right_cancel h))

/-- The morphism between two chosen pullbacks with a prescribed normalized element. -/
def pullHomOfElt {X₁ X₂ Y : 𝒮} (z₁ : p.Fiber X₁) (z₂ : p.Fiber X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (α : 𝒜.obj (op Y)) : pullbackFiber p z₁ f₁ ⟶ pullbackFiber p z₂ f₂ :=
  ρ.fiberHomOfElt _ _ (ρ.cartElt z₁ f₁ * α * (ρ.cartElt z₂ f₂)⁻¹)

@[simp]
lemma pullElt_pullHomOfElt {X₁ X₂ Y : 𝒮} (z₁ : p.Fiber X₁) (z₂ : p.Fiber X₂) (f₁ : Y ⟶ X₁)
    (f₂ : Y ⟶ X₂) (α : 𝒜.obj (op Y)) : ρ.pullElt (ρ.pullHomOfElt z₁ z₂ f₁ f₂ α) = α := by
  simp only [pullElt, pullHomOfElt, fiberElt_fiberHomOfElt]
  group

/-- The base change of a morphism of a fibre along `b`, compared through the chosen cartesian
lifts of `b`: the element form of `CategoryTheory.Functor.pullbackFiberHom_fac`. -/
lemma fiberElt_pullbackFiberHom {W Z : 𝒮} {y y' : p.Fiber W} (α : y ⟶ y') (b : Z ⟶ W) :
    ρ.fiberElt (pullbackFiberHom α b) * ρ.cartElt y' b =
      ρ.cartElt y b * 𝒜.map b.op (ρ.fiberElt α) := by
  have := (pullbackFiberHom α b).2
  have := α.2
  have h₁ := ρ.eltOver_comp (𝟙 Z) b (pullbackFiberHom α b).1 (IsPreFibered.pullbackMap y'.2 b)
  have h₂ := ρ.eltOver_comp b (𝟙 W) (IsPreFibered.pullbackMap y.2 b) α.1
  rw [map_op_id_apply] at h₁
  refine h₁.symm.trans (Eq.trans ?_ h₂)
  have key : (pullbackFiberHom α b).1 ≫ IsPreFibered.pullbackMap y'.2 b =
      IsPreFibered.pullbackMap y.2 b ≫ α.1 := pullbackFiberHom_fac α b
  exact ρ.eltOver_congr (by rw [Category.id_comp, Category.comp_id]) key

/-- The normalized element of the base change of a morphism of a fibre is the restriction of its
element. -/
@[simp]
lemma pullElt_pullbackFiberHom {W Z : 𝒮} {y y' : p.Fiber W} (α : y ⟶ y') (b : Z ⟶ W) :
    ρ.pullElt (pullbackFiberHom α b) = 𝒜.map b.op (ρ.fiberElt α) := by
  rw [pullElt, mul_assoc, ρ.fiberElt_pullbackFiberHom, ← mul_assoc, inv_mul_cancel, one_mul]

/-- The contraction of an iterated chosen pullback, compared through the chosen cartesian lifts:
the element form of `CategoryTheory.Functor.pullbackFiberCompIso'_hom_fac`. -/
lemma fiberElt_pullbackFiberCompIso'_hom {T V Z : 𝒮} (y : p.Fiber T) (f : V ⟶ T) (ε : Z ⟶ V)
    (b : Z ⟶ T) (h : ε ≫ f = b) :
    ρ.fiberElt (pullbackFiberCompIso' y f ε b h).hom * ρ.cartElt y b =
      ρ.cartElt (pullbackFiber p y f) ε * 𝒜.map ε.op (ρ.cartElt y f) := by
  have := (pullbackFiberCompIso' y f ε b h).hom.2
  have h₁ := ρ.eltOver_comp (𝟙 Z) b (pullbackFiberCompIso' y f ε b h).hom.1
    (IsPreFibered.pullbackMap y.2 b)
  have h₂ := ρ.eltOver_comp ε f (IsPreFibered.pullbackMap (pullbackFiber p y f).2 ε)
    (IsPreFibered.pullbackMap y.2 f)
  rw [map_op_id_apply] at h₁
  refine h₁.symm.trans (Eq.trans ?_ h₂)
  have key : (pullbackFiberCompIso' y f ε b h).hom.1 ≫ IsPreFibered.pullbackMap y.2 b =
      IsPreFibered.pullbackMap (pullbackFiber p y f).2 ε ≫ IsPreFibered.pullbackMap y.2 f :=
    pullbackFiberCompIso'_hom_fac y f ε b h
  exact ρ.eltOver_congr (by rw [Category.id_comp, h]) key

/-- The normalized element of the contraction of an iterated chosen pullback is the restriction of
the element of the inner chosen cartesian lift. -/
@[simp]
lemma pullElt_pullbackFiberCompIso'_hom {T V Z : 𝒮} (y : p.Fiber T) (f : V ⟶ T) (ε : Z ⟶ V)
    (b : Z ⟶ T) (h : ε ≫ f = b) :
    ρ.pullElt (z₁ := pullbackFiber p y f) (z₂ := y) (f₁ := ε) (f₂ := b)
      (pullbackFiberCompIso' y f ε b h).hom = 𝒜.map ε.op (ρ.cartElt y f) := by
  rw [pullElt, mul_assoc, ρ.fiberElt_pullbackFiberCompIso'_hom, ← mul_assoc, inv_mul_cancel,
    one_mul]

/-- The normalized element of the inverse of an isomorphism between chosen pullbacks is the
inverse of its normalized element. -/
@[simp]
lemma pullElt_inv {X₁ X₂ Y : 𝒮} {z₁ : p.Fiber X₁} {z₂ : p.Fiber X₂} {f₁ : Y ⟶ X₁}
    {f₂ : Y ⟶ X₂} (e : pullbackFiber p z₁ f₁ ≅ pullbackFiber p z₂ f₂) :
    ρ.pullElt e.inv = (ρ.pullElt e.hom)⁻¹ := by
  simp only [pullElt, fiberElt_inv]
  group

/-- The normalized element of a morphism between chosen pullbacks is unchanged by pulling the
morphism back further, in the sense of
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom`, up to restriction. -/
lemma pullElt_pullHom {X₁ X₂ Y Y' : 𝒮} {z₁ : p.Fiber X₁} {z₂ : p.Fiber X₂} {f₁ : Y ⟶ X₁}
    {f₂ : Y ⟶ X₂} (ψ : pullbackFiber p z₁ f₁ ⟶ pullbackFiber p z₂ f₂) (g : Y' ⟶ Y)
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    ρ.pullElt (z₁ := z₁) (z₂ := z₂) (f₁ := gf₁) (f₂ := gf₂)
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := pullbackPseudofunctor p)
      (M₁ := z₁) (M₂ := z₂) (f₁ := f₁) (f₂ := f₂) ψ g gf₁ gf₂ hgf₁ hgf₂) =
      𝒜.map g.op (ρ.pullElt ψ) := by
  subst hgf₁ hgf₂
  rw [pullHom_eq]
  have e₁ := ρ.fiberElt_pullbackFiberCompIso'_hom z₁ f₁ g (g ≫ f₁) rfl
  have e₂ := ρ.fiberElt_pullbackFiberCompIso'_hom z₂ f₂ g (g ≫ f₂) rfl
  have e₃ := ρ.fiberElt_pullbackFiberHom ψ g
  rw [pullbackFiberCompIso'_rfl] at e₁ e₂
  rw [← eq_mul_inv_iff_mul_eq] at e₁ e₂ e₃
  simp only [pullElt, fiberElt_comp, fiberElt_inv, e₁, e₂, e₃, map_mul, _root_.map_inv]
  group

end Pullback

end Rigidification

/-! ### Cocycles of a family with values in a presheaf of groups -/

universe t

/-- A *Čech `1`-cocycle* of a family of morphisms `f i : X i ⟶ S` with values in a presheaf of
groups `𝒜`, in the form in which descent data are indexed: an element `val f₁ f₂` of `𝒜 Y` for
every pair of morphisms `f₁ : Y ⟶ X i₁`, `f₂ : Y ⟶ X i₂`, which for pairs agreeing over `S` is
natural in `Y`, trivial on the diagonal and multiplicative on triples. -/
structure FamilyCocycle (𝒜 : 𝒮ᵒᵖ ⥤ GrpCat.{w}) {ι : Type t} {S : 𝒮} {X : ι → 𝒮}
    (f : ∀ i, X i ⟶ S) where
  /-- The value of the cocycle on a pair of morphisms to two members of the family. -/
  val ⦃Y : 𝒮⦄ ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) : 𝒜.obj (op Y)
  /-- Naturality. -/
  map_val ⦃Y Y' : 𝒮⦄ (g : Y' ⟶ Y) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (h : f₁ ≫ f i₁ = f₂ ≫ f i₂) : val (g ≫ f₁) (g ≫ f₂) = 𝒜.map g.op (val f₁ f₂)
  /-- The cocycle is trivial on the diagonal. -/
  val_self ⦃Y : 𝒮⦄ ⦃i : ι⦄ (g : Y ⟶ X i) : val g g = 1
  /-- The cocycle condition. -/
  val_mul ⦃Y : 𝒮⦄ ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃)
    (h₁₂ : f₁ ≫ f i₁ = f₂ ≫ f i₂) (h₂₃ : f₂ ≫ f i₂ = f₃ ≫ f i₃) :
    val f₁ f₂ * val f₂ f₃ = val f₁ f₃

namespace FamilyCocycle

variable {𝒜 : 𝒮ᵒᵖ ⥤ GrpCat.{w}} {ι : Type t} {S : 𝒮} {X : ι → 𝒮} {f : ∀ i, X i ⟶ S}

/-- The cocycle obtained from `c` by the Čech `0`-cochain `s`: the value on `(f₁, f₂)` is
`(f₁^* s i₁)⁻¹ * c (f₁, f₂) * f₂^* s i₂`. Two cocycles are *cohomologous* when one is a twist of
the other. -/
def twist (c : FamilyCocycle 𝒜 f) (s : ∀ i, 𝒜.obj (op (X i))) : FamilyCocycle 𝒜 f where
  val Y i₁ i₂ f₁ f₂ := (𝒜.map f₁.op (s i₁))⁻¹ * c.val f₁ f₂ * 𝒜.map f₂.op (s i₂)
  map_val Y Y' g i₁ i₂ f₁ f₂ h := by
    simp only [op_comp, Functor.map_comp, GrpCat.comp_apply, c.map_val g f₁ f₂ h, map_mul,
      _root_.map_inv]
  val_self Y i g := by simp [c.val_self]
  val_mul Y i₁ i₂ i₃ f₁ f₂ f₃ h₁₂ h₂₃ := by
    rw [← c.val_mul f₁ f₂ f₃ h₁₂ h₂₃]
    group

@[simp]
lemma twist_val (c : FamilyCocycle 𝒜 f) (s : ∀ i, 𝒜.obj (op (X i))) {Y : 𝒮} {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) :
    (c.twist s).val f₁ f₂ = (𝒜.map f₁.op (s i₁))⁻¹ * c.val f₁ f₂ * 𝒜.map f₂.op (s i₂) :=
  rfl

/-- The pullback of a cocycle along a morphism of families with fixed target. -/
def pull {S' : 𝒮} {𝒰 : PreZeroHypercover.{t} S} {𝒰' : PreZeroHypercover.{t} S'} {g : S' ⟶ S}
    (c : FamilyCocycle 𝒜 𝒰.f) (Φ : 𝒰'.HomOver 𝒰 g) : FamilyCocycle 𝒜 𝒰'.f where
  val Y i₁ i₂ a₁ a₂ := c.val (a₁ ≫ Φ.h₀ i₁) (a₂ ≫ Φ.h₀ i₂)
  map_val Y Y' g' i₁ i₂ a₁ a₂ h := by
    simp only [Category.assoc]
    exact c.map_val g' _ _ (by simp only [Category.assoc, Φ.w₀, reassoc_of% h])
  val_self Y i a := c.val_self _
  val_mul Y i₁ i₂ i₃ a₁ a₂ a₃ h₁₂ h₂₃ :=
    c.val_mul _ _ _ (by simp only [Category.assoc, Φ.w₀, reassoc_of% h₁₂])
      (by simp only [Category.assoc, Φ.w₀, reassoc_of% h₂₃])

@[simp]
lemma pull_val {S' : 𝒮} {𝒰 : PreZeroHypercover.{t} S} {𝒰' : PreZeroHypercover.{t} S'}
    {g : S' ⟶ S} (c : FamilyCocycle 𝒜 𝒰.f) (Φ : 𝒰'.HomOver 𝒰 g) {Y : 𝒮} {i₁ i₂ : 𝒰'.I₀}
    (a₁ : Y ⟶ 𝒰'.X i₁) (a₂ : Y ⟶ 𝒰'.X i₂) :
    (c.pull Φ).val a₁ a₂ = c.val (a₁ ≫ Φ.h₀ i₁) (a₂ ≫ Φ.h₀ i₂) :=
  rfl

/-- The Čech class of a cocycle *is torsion* when some nonzero power of the cocycle is a
coboundary: there are `m ≠ 0` and a Čech `0`-cochain `s` with
`c (f₁, f₂) ^ m = (f₁^* s i₁)⁻¹ * f₂^* s i₂` on every pair agreeing over the target. For a
presheaf of commutative groups this says that the class of `c` in `Ȟ¹` has finite order. -/
def IsTorsionClass (c : FamilyCocycle 𝒜 f) : Prop :=
  ∃ m : ℕ, m ≠ 0 ∧ ∃ s : ∀ i, 𝒜.obj (op (X i)), ∀ ⦃Y : 𝒮⦄ ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂), f₁ ≫ f i₁ = f₂ ≫ f i₂ →
      c.val f₁ f₂ ^ m = (𝒜.map f₁.op (s i₁))⁻¹ * 𝒜.map f₂.op (s i₂)

section Pair

variable {S : 𝒮} {X : Bool → 𝒮} (f : ∀ i, X i ⟶ S) [∀ i, Mono (f i)]
  (γ : ∀ ⦃Y : 𝒮⦄ (_ : Y ⟶ X false) (_ : Y ⟶ X true), 𝒜.obj (op Y))

/-- The value of the cocycle of a two-member family of monomorphisms: `γ` on a pair
`(Y ⟶ X false, Y ⟶ X true)`, its inverse on a pair in the other order, and the unit on a pair of
morphisms to the same member. -/
def pairVal : ∀ ⦃Y : 𝒮⦄ ⦃i₁ i₂ : Bool⦄ (_ : Y ⟶ X i₁) (_ : Y ⟶ X i₂), 𝒜.obj (op Y)
  | _, false, true, a, b => γ a b
  | _, true, false, b, a => (γ a b)⁻¹
  | _, false, false, _, _ => 1
  | _, true, true, _, _ => 1

variable {f} in
/-- Two morphisms to the same member of a family of monomorphisms which agree over the target
are equal. -/
lemma eq_of_comp_eq {Y : 𝒮} {i : Bool} {a a' : Y ⟶ X i} (h : a ≫ f i = a' ≫ f i) : a = a' :=
  (cancel_mono (f i)).mp h

/-- **The cocycle of a two-member family of monomorphisms** with a prescribed value `γ` on pairs
`(Y ⟶ X false, Y ⟶ X true)` agreeing over the target, natural in `Y`. -/
def ofPair (hγ : ∀ ⦃Y Y' : 𝒮⦄ (g : Y' ⟶ Y) (a : Y ⟶ X false) (b : Y ⟶ X true),
      a ≫ f false = b ≫ f true → γ (g ≫ a) (g ≫ b) = 𝒜.map g.op (γ a b)) :
    FamilyCocycle 𝒜 f where
  val := pairVal γ
  map_val Y Y' g i₁ i₂ f₁ f₂ h := by
    cases i₁ <;> cases i₂
    · exact (map_one _).symm
    · exact hγ g f₁ f₂ h
    · exact (congrArg _ (hγ g f₂ f₁ h.symm)).trans (_root_.map_inv _ _).symm
    · exact (map_one _).symm
  val_self Y i g := by
    cases i
    · rfl
    · rfl
  val_mul Y i₁ i₂ i₃ f₁ f₂ f₃ h₁₂ h₂₃ := by
    cases i₁ <;> cases i₂ <;> cases i₃
    · exact one_mul _
    · obtain rfl := eq_of_comp_eq h₁₂
      exact one_mul _
    · obtain rfl := eq_of_comp_eq (h₁₂.trans h₂₃)
      exact mul_inv_cancel _
    · obtain rfl := eq_of_comp_eq h₂₃
      exact mul_one _
    · obtain rfl := eq_of_comp_eq h₂₃
      exact mul_one _
    · obtain rfl := eq_of_comp_eq (h₁₂.trans h₂₃)
      exact inv_mul_cancel _
    · obtain rfl := eq_of_comp_eq h₁₂
      exact one_mul _
    · exact one_mul _

@[simp]
lemma ofPair_val_false_true (hγ : ∀ ⦃Y Y' : 𝒮⦄ (g : Y' ⟶ Y) (a : Y ⟶ X false) (b : Y ⟶ X true),
      a ≫ f false = b ≫ f true → γ (g ≫ a) (g ≫ b) = 𝒜.map g.op (γ a b)) {Y : 𝒮}
    (a : Y ⟶ X false) (b : Y ⟶ X true) : (ofPair f γ hγ).val a b = γ a b :=
  rfl

end Pair

end FamilyCocycle

/-! ### Descent data with a prescribed cocycle -/

/- The objects and morphisms of the pullback pseudofunctor are those of the fibres and of the
chosen pullbacks by `rfl`, but only after unfolding definitions that the ordinary tactics do not
see through; naming them lets the statements below be type-correct at `implicit` transparency, as
in `PresentingDescentData.lean`. -/
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.homMk CategoryTheory.Functor.pullbackFiberHom
  CategoryTheory.Functor.IsFibered.pullbackPseudofunctor
  CategoryTheory.Functor.IsFibered.pbObj CategoryTheory.Functor.IsFibered.pbMap
  CategoryTheory.Functor.IsFibered.fiberPullback
  CategoryTheory.Functor.IsFibered.fiberPullbackMap
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  CategoryTheory.Cat.str CategoryTheory.LocallyDiscrete.categoryStruct
  CategoryTheory.Functor.Fiber.fiberCategory Quiver.Hom.toLoc
  CategoryTheory.Pseudofunctor.DescentData.pullFunctorObj
  CategoryTheory.Functor.FamilyDescentDatum.pull

namespace Rigidification

variable {p : 𝒳 ⥤ 𝒮} {𝒜 : 𝒮ᵒᵖ ⥤ GrpCat.{w}} (ρ : Rigidification p 𝒜) [p.IsFibered]
  {ι : Type t} {S : 𝒮} {X : ι → 𝒮} {f : ∀ i, X i ⟶ S}

/-- A descent datum for `p` relative to the family `f` *is represented by* the cocycle `c` when
the normalized element of each of its gluing morphisms is the corresponding value of `c`. -/
def IsRepresentedBy (D : (pullbackPseudofunctor p).DescentData f) (c : FamilyCocycle 𝒜 f) :
    Prop :=
  ∀ ⦃Y : 𝒮⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q),
    ρ.pullElt (z₁ := D.obj i₁) (z₂ := D.obj i₂) (f₁ := f₁) (f₂ := f₂) (D.hom q f₁ f₂ hf₁ hf₂) =
      c.val f₁ f₂

/-- **The descent datum of a cocycle**: the objects `z i`, glued by the morphisms between their
chosen pullbacks whose normalized elements are the values of the cocycle. -/
def descentDatumOfCocycle (z : ∀ i, p.Fiber (X i)) (c : FamilyCocycle 𝒜 f) :
    (pullbackPseudofunctor p).DescentData f where
  obj := z
  hom Y q i₁ i₂ f₁ f₂ _ _ := ρ.pullHomOfElt (z i₁) (z i₂) f₁ f₂ (c.val f₁ f₂)
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    refine ρ.pullElt_injective (z₁ := z i₁) (z₂ := z i₂) (f₁ := gf₁) (f₂ := gf₂) ?_
    rw [ρ.pullElt_pullHom _ g gf₁ gf₂ hgf₁ hgf₂, pullElt_pullHomOfElt, pullElt_pullHomOfElt,
      ← hgf₁, ← hgf₂, c.map_val g f₁ f₂ (hf₁.trans hf₂.symm)]
  hom_self Y q i g _ := by
    refine ρ.pullElt_injective (z₁ := z i) (z₂ := z i) (f₁ := g) (f₂ := g) ?_
    rw [pullElt_pullHomOfElt, c.val_self]
    exact (ρ.pullElt_id (z i) g).symm
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    refine ρ.pullElt_injective (z₁ := z i₁) (z₂ := z i₃) (f₁ := f₁) (f₂ := f₃) ?_
    refine (ρ.pullElt_comp _ _).trans ?_
    rw [pullElt_pullHomOfElt, pullElt_pullHomOfElt, pullElt_pullHomOfElt,
      c.val_mul f₁ f₂ f₃ (hf₁.trans hf₂.symm) (hf₂.trans hf₃.symm)]

@[simp]
lemma descentDatumOfCocycle_obj (z : ∀ i, p.Fiber (X i)) (c : FamilyCocycle 𝒜 f) (i : ι) :
    (ρ.descentDatumOfCocycle z c).obj i = z i :=
  rfl

/-- The descent datum of a cocycle is represented by it. -/
lemma isRepresentedBy_descentDatumOfCocycle (z : ∀ i, p.Fiber (X i)) (c : FamilyCocycle 𝒜 f) :
    ρ.IsRepresentedBy (ρ.descentDatumOfCocycle z c) c := by
  intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
  exact ρ.pullElt_pullHomOfElt (z i₁) (z i₂) f₁ f₂ (c.val f₁ f₂)

/-- **A morphism of descent data, read on cocycles.** If `D` and `D'` are represented by `c`
and `c'`, the elements `s i` of the components of a morphism `D ⟶ D'` satisfy
`f₁^* s i₁ * c' (f₁, f₂) = c (f₁, f₂) * f₂^* s i₂`: the cocycle `c'` is the twist of `c` by `s`. -/
lemma map_mul_val_eq_of_isRepresentedBy {D D' : (pullbackPseudofunctor p).DescentData f}
    {c c' : FamilyCocycle 𝒜 f} (hD : ρ.IsRepresentedBy D c) (hD' : ρ.IsRepresentedBy D' c')
    (φ : D ⟶ D') {Y : 𝒮} {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (h : f₁ ≫ f i₁ = f₂ ≫ f i₂) :
    𝒜.map f₁.op (ρ.fiberElt (φ.hom i₁)) * c'.val f₁ f₂ =
      c.val f₁ f₂ * 𝒜.map f₂.op (ρ.fiberElt (φ.hom i₂)) := by
  have hc := φ.comm (f₁ ≫ f i₁) f₁ f₂ rfl h.symm
  rw [pullbackPseudofunctor_map_map, pullbackPseudofunctor_map_map] at hc
  have e := congrArg (ρ.pullElt (z₁ := D.obj i₁) (z₂ := D'.obj i₂) (f₁ := f₁) (f₂ := f₂)) hc
  rw [ρ.pullElt_comp (z₂ := D'.obj i₁) (f₂ := f₁), ρ.pullElt_comp (z₂ := D.obj i₂) (f₂ := f₂),
    pullElt_pullbackFiberHom, pullElt_pullbackFiberHom, hD, hD'] at e
  exact e

/-- **Cohomologous cocycles give isomorphic descent data.** Two descent data represented by
cocycles `c` and `c'` are isomorphic as soon as `c'` is the twist of `c` by a Čech `0`-cochain
`s`; the components of the isomorphism have the elements `s i`. -/
def isoOfIsRepresentedBy {D D' : (pullbackPseudofunctor p).DescentData f}
    {c c' : FamilyCocycle 𝒜 f} (hD : ρ.IsRepresentedBy D c) (hD' : ρ.IsRepresentedBy D' c')
    (s : ∀ i, 𝒜.obj (op (X i)))
    (hs : ∀ ⦃Y : 𝒮⦄ ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂),
      f₁ ≫ f i₁ = f₂ ≫ f i₂ → c'.val f₁ f₂ = (c.twist s).val f₁ f₂) : D ≅ D' :=
  Pseudofunctor.DescentData.isoMk (fun i => ρ.fiberIsoOfElt (D.obj i) (D'.obj i) (s i)) (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    rw [pullbackPseudofunctor_map_map, pullbackPseudofunctor_map_map]
    refine ρ.pullElt_injective (z₁ := D.obj i₁) (z₂ := D'.obj i₂) (f₁ := f₁) (f₂ := f₂) ?_
    rw [ρ.pullElt_comp (z₂ := D'.obj i₁) (f₂ := f₁), ρ.pullElt_comp (z₂ := D.obj i₂) (f₂ := f₂),
      pullElt_pullbackFiberHom, pullElt_pullbackFiberHom, hD, hD', fiberElt_fiberIsoOfElt_hom,
      fiberElt_fiberIsoOfElt_hom, hs f₁ f₂ (hf₁.trans hf₂.symm), FamilyCocycle.twist_val]
    group)

/-- The components of `isoOfIsRepresentedBy` have the elements of the cochain. -/
@[simp]
lemma fiberElt_isoOfIsRepresentedBy_hom {D D' : (pullbackPseudofunctor p).DescentData f}
    {c c' : FamilyCocycle 𝒜 f} (hD : ρ.IsRepresentedBy D c) (hD' : ρ.IsRepresentedBy D' c')
    (s : ∀ i, 𝒜.obj (op (X i)))
    (hs : ∀ ⦃Y : 𝒮⦄ ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂),
      f₁ ≫ f i₁ = f₂ ≫ f i₂ → c'.val f₁ f₂ = (c.twist s).val f₁ f₂) (i : ι) :
    ρ.fiberElt ((ρ.isoOfIsRepresentedBy hD hD' s hs).hom.hom i) = s i :=
  ρ.fiberElt_fiberIsoOfElt_hom _ _ _

/-- **Pulling back a descent datum along a morphism of families pulls back its cocycle**, up to
the twist by the elements of the chosen cartesian lifts along which the objects are pulled
back. -/
lemma isRepresentedBy_pull {S' : 𝒮} {𝒰 : PreZeroHypercover.{t} S}
    {𝒰' : PreZeroHypercover.{t} S'} {g : S' ⟶ S} (Φ : 𝒰'.HomOver 𝒰 g)
    {D : FamilyDescentDatum p 𝒰} {c : FamilyCocycle 𝒜 𝒰.f} (hD : ρ.IsRepresentedBy D c) :
    ρ.IsRepresentedBy (FamilyDescentDatum.pull p Φ D)
      ((c.pull Φ).twist fun i => (ρ.cartElt (D.obj (Φ.s₀ i)) (Φ.h₀ i))⁻¹) := by
  intro Y q i₁ i₂ a₁ a₂ ha₁ ha₂
  rw [FamilyDescentDatum.pull_hom]
  have h₁ := Functor.pullbackPseudofunctor_mapComp'_inv_app p (Φ.h₀ i₁) a₁ (a₁ ≫ Φ.h₀ i₁) rfl
    (D.obj (Φ.s₀ i₁))
  have h₂ := Functor.pullbackPseudofunctor_mapComp'_hom_app p (Φ.h₀ i₂) a₂ (a₂ ≫ Φ.h₀ i₂) rfl
    (D.obj (Φ.s₀ i₂))
  simp only [op_comp, Quiver.Hom.comp_toLoc, Pseudofunctor.mapComp'_eq_mapComp] at h₁ h₂
  rw [h₁, h₂]
  refine (ρ.pullElt_comp (z₂ := D.obj (Φ.s₀ i₁)) (f₂ := a₁ ≫ Φ.h₀ i₁) _ _).trans ?_
  refine (congrArg (_ * ·)
    (ρ.pullElt_comp (z₂ := D.obj (Φ.s₀ i₂)) (f₂ := a₂ ≫ Φ.h₀ i₂) _ _)).trans ?_
  have e₁ : ρ.pullElt (z₁ := (FamilyDescentDatum.pull p Φ D).obj i₁) (z₂ := D.obj (Φ.s₀ i₁))
      (f₁ := a₁) (f₂ := a₁ ≫ Φ.h₀ i₁)
      (pullbackFiberCompIso' (D.obj (Φ.s₀ i₁)) (Φ.h₀ i₁) a₁ (a₁ ≫ Φ.h₀ i₁) rfl).hom =
        𝒜.map a₁.op (ρ.cartElt (D.obj (Φ.s₀ i₁)) (Φ.h₀ i₁)) :=
    ρ.pullElt_pullbackFiberCompIso'_hom _ _ _ _ rfl
  have e₂ : ρ.pullElt (z₁ := D.obj (Φ.s₀ i₂)) (z₂ := (FamilyDescentDatum.pull p Φ D).obj i₂)
      (f₁ := a₂ ≫ Φ.h₀ i₂) (f₂ := a₂)
      (pullbackFiberCompIso' (D.obj (Φ.s₀ i₂)) (Φ.h₀ i₂) a₂ (a₂ ≫ Φ.h₀ i₂) rfl).inv =
        (𝒜.map a₂.op (ρ.cartElt (D.obj (Φ.s₀ i₂)) (Φ.h₀ i₂)))⁻¹ :=
    (ρ.pullElt_inv _).trans (congrArg _ (ρ.pullElt_pullbackFiberCompIso'_hom _ _ _ _ rfl))
  rw [e₁, e₂, hD, FamilyCocycle.twist_val, FamilyCocycle.pull_val, _root_.map_inv,
    _root_.map_inv, inv_inv, mul_assoc]

end Rigidification

end CategoryTheory.Functor
