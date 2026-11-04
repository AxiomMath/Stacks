module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksCore.Tactic.StacksAttribute

/-! # Change of rings for presheaves of modules is monoidal

Let `θ : O₁ ⟶ O₂` be a morphism of presheaves of commutative rings on a category `C`. The
change-of-rings functor `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ`, i.e.
`G ↦ O₂ ⊗_{p,O₁} G`, carries the objectwise tensor product to the objectwise tensor product:

`O₂ ⊗_{O₁} (A ⊗_{O₁} B) ≅ (O₂ ⊗_{O₁} A) ⊗_{O₂} (O₂ ⊗_{O₁} B)`,

naturally in `A` and `B`. Objectwise this is Mathlib's
`TensorProduct.AlgebraTensorModule.distribBaseChange`, which is the comparison isomorphism of
Mathlib's `(ModuleCat.extendScalars _).Monoidal` instance; the content of this file is that it
is compatible with the restriction maps of the presheaves, and natural in both arguments.

This is the presheaf-level half of step 4 of the chain of bijections recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageTensor`, whose assembly is Tag 03EL
(`f^*(F ⊗_{O_D} G) ≅ f^*F ⊗_{O_C} f^*G` for a morphism of ringed topoi): the pullback of
Stacks 03D6 part (2) is by definition the inverse image followed by extension of scalars, so
base change of a tensor product is exactly what step 4 asks for.

## Main definitions

* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorAppIso`: the objectwise comparison
  isomorphism, namely `TensorProduct.AlgebraTensorModule.distribBaseChange` on sections over a
  fixed object.
* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorObjIso`: the comparison as an
  isomorphism of presheaves of `O₂`-modules.
* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorIso`: the comparison as an
  isomorphism of bifunctors, so that naturality in both module arguments is part of the datum.
* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsUnitIso`: the comparison isomorphism of
  the tensor units, `O₂ ≅ O₂ ⊗_{O₁} O₁`.
* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsCoreMonoidal` and `changeOfRingsMonoidal`:
  **change of rings is a strong monoidal functor** for the objectwise tensor product.

## Main results

* `Stacks.PresheafOfModules.ChangeOfRings.linearMap_ext_tmul_tmul`: two `S`-linear maps out of
  `S ⊗[R] (M ⊗[R] N)` agree as soon as they agree on the elements `a ⊗ₜ (m ⊗ₜ n)`.
* `Stacks.PresheafOfModules.ChangeOfRings.linearMap_ext_one_tmul` and its iterates: two
  `S`-linear maps out of a base-changed module agree as soon as they agree on the elements
  `1 ⊗ₜ …`.
* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsMonoidal_delta`: the cotensorator of the
  monoidal structure is the base-change comparison isomorphism.
* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorObjIso_hom_app`: the components of
  the comparison are the objectwise ones, which carry `a ⊗ₜ (x ⊗ₜ y)` to `(a ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y)`.

## Implementation notes

Both the naturality square in the site variable and the naturality square in the two module
variables are checked on the elements `a ⊗ₜ (x ⊗ₜ y)`, using
`Stacks.PresheafOfModules.ChangeOfRings.linearMap_ext_tmul_tmul`. The second is then `rfl`; the
first needs exactly one fact, that the restriction map of `O₂` preserves `1`, because
`distribBaseChange` puts a `1` in the last slot.

Reaching that fact needs care, and none of `rw`, `simp` or a type ascription on a binder gets
there. A section of `A` carried along a restriction map has type
`((ModuleCat.restrictScalars _).obj (A.obj Y))`, which is the carrier of `A.obj Y` with the
scalars of the *source* object, so a tensor formed against it over `O₁.obj Y` has no `Module`
instance below default transparency. The two moves that do work, and which are used below, are
to coerce each such *term* with `show A.obj Y from _` — a `show … from` ascription on a term
checks at default transparency, unlike an ascription on a binder — and to spell every base ring
of a `⊗ₜ` as `Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O₁` or
`Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O₂` rather than
`O₁.obj _` or `O₂.obj _`, so that a single spelling of the algebra instance serves the whole
term. With both in place the goal can be restated as the equation it really is, and closes with
one `rw`.

**The monoidal structure.** The comparison isomorphism and its two naturality squares are
exactly the data of a `CategoryTheory.Functor.CoreMonoidal` structure on change of rings, once
the comparison of the tensor units is added. The three coherences are checked objectwise, and
there the functor is Mathlib's `ModuleCat.extendScalars`, whose own monoidal structure has
`TensorProduct.AlgebraTensorModule.distribBaseChange` as its cotensorator and
`TensorProduct.AlgebraTensorModule.rid` as its unit comparison; so the coherences hold on the
elements `1 ⊗ₜ …` for the same reasons they do there. Checking on `1 ⊗ₜ …` rather than on
`a ⊗ₜ …` is what makes the two naturality squares and associativity definitional: with a general
scalar `a` in front, associativity is still an identity but no longer a definitional one. The
reduction is `Stacks.PresheafOfModules.ChangeOfRings.linearMap_ext_one_tmul`, which is the
`ModuleCat.ExtendScalars.hom_ext` of Mathlib read as a statement about linear maps.

The module universe is the universe of the ring sections. This is forced: Mathlib's monoidal
structure on presheaves of modules is only available for `PresheafOfModules.{w}` over a ring
presheaf of the shape `O ⋙ forget₂ CommRingCat RingCat` with `O : Cᵒᵖ ⥤ CommRingCat.{w}`.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TensorProduct

universe w v u

namespace Stacks.PresheafOfModules.ChangeOfRings

/-! ## Extensionality for linear maps out of a base-changed tensor product -/

section Ext

/-- Two `S`-linear maps out of `S ⊗[R] M` agree as soon as they agree on the elements
`a ⊗ₜ m`. -/
private theorem linearMap_ext_tmul_aux {R S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    {M P : Type w} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module S P]
    {α β : (S ⊗[R] M) →ₗ[S] P} (h : ∀ (a : S) (m : M), α (a ⊗ₜ m) = β (a ⊗ₜ m)) : α = β :=
  LinearMap.ext fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => simp [hp, hq]
    | tmul a m => exact h a m

/-- Two `S`-linear maps out of `S ⊗[R] (M ⊗[R] N)` agree on `a ⊗ₜ t` for all `t` as soon as they
agree on the elements `a ⊗ₜ (m ⊗ₜ n)`. -/
private theorem apply_tmul_eq_of_tmul_tmul {R S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    {M N P : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module S P] {α β : (S ⊗[R] (M ⊗[R] N)) →ₗ[S] P} {a : S}
    (h : ∀ (m : M) (n : N), α (a ⊗ₜ (m ⊗ₜ n)) = β (a ⊗ₜ (m ⊗ₜ n))) (t : M ⊗[R] N) :
    α (a ⊗ₜ t) = β (a ⊗ₜ t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => simp [tmul_add, hp, hq]
  | tmul m n => exact h m n

/-- Two `S`-linear maps out of `S ⊗[R] (M ⊗[R] N)` agree as soon as they agree on the
elements `a ⊗ₜ (m ⊗ₜ n)`. -/
theorem linearMap_ext_tmul_tmul {R S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    {M N P : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module S P] {α β : (S ⊗[R] (M ⊗[R] N)) →ₗ[S] P}
    (h : ∀ (a : S) (m : M) (n : N), α (a ⊗ₜ (m ⊗ₜ n)) = β (a ⊗ₜ (m ⊗ₜ n))) : α = β :=
  linearMap_ext_tmul_aux fun a => apply_tmul_eq_of_tmul_tmul (h a)

end Ext

/-! ## The comparison isomorphism -/

section Comparison

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : O₁ ⟶ O₂)
  (A B : PresheafOfModules.{w} (ringPresheaf O₁))

/-- The comparison isomorphism `O₂(X) ⊗_{O₁(X)} (A(X) ⊗_{O₁(X)} B(X)) ≅
(O₂(X) ⊗_{O₁(X)} A(X)) ⊗_{O₂(X)} (O₂(X) ⊗_{O₁(X)} B(X))` on sections over a fixed object.
This is Mathlib's `TensorProduct.AlgebraTensorModule.distribBaseChange`, i.e. the comparison
isomorphism of the monoidal structure on `ModuleCat.extendScalars`. -/
def changeOfRingsTensorAppIso (X : Cᵒᵖ) :
    (changeOfRingsObj θ (A ⊗ B)).obj X ≅
      ((changeOfRingsObj θ A) ⊗ (changeOfRingsObj θ B)).obj X :=
  letI := (θ.app X).hom.toAlgebra
  (TensorProduct.AlgebraTensorModule.distribBaseChange (O₁.obj X) (O₂.obj X)
    (A.obj X) (B.obj X)).toModuleIso

/-- The comparison isomorphism is compatible with the restriction maps of the presheaves. The
only fact used is that the restriction map of `O₂` preserves `1`. -/
theorem changeOfRingsTensorAppIso_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (changeOfRingsObj θ (A ⊗ B)).map f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map
          (changeOfRingsTensorAppIso θ A B Y).hom =
      (changeOfRingsTensorAppIso θ A B X).hom ≫
        ((changeOfRingsObj θ A) ⊗ (changeOfRingsObj θ B)).map f := by
  let : Algebra ((ringPresheaf O₁).obj X) ((ringPresheaf O₂).obj X) := (θ.app X).hom.toAlgebra
  let : Algebra ((ringPresheaf O₁).obj Y) ((ringPresheaf O₂).obj Y) := (θ.app Y).hom.toAlgebra
  refine ModuleCat.hom_ext (linearMap_ext_tmul_tmul fun a x y => ?_)
  have h1 : ((ringPresheaf O₂).map f).hom (1 : (ringPresheaf O₂).obj X) = 1 := map_one _
  show ((((ringPresheaf O₂).map f).hom a) ⊗ₜ[(ringPresheaf O₁).obj Y]
          (show A.obj Y from A.map f x)) ⊗ₜ[(ringPresheaf O₂).obj Y]
        ((1 : (ringPresheaf O₂).obj Y) ⊗ₜ[(ringPresheaf O₁).obj Y]
          (show B.obj Y from B.map f y)) =
      ((((ringPresheaf O₂).map f).hom a) ⊗ₜ[(ringPresheaf O₁).obj Y]
          (show A.obj Y from A.map f x)) ⊗ₜ[(ringPresheaf O₂).obj Y]
        ((((ringPresheaf O₂).map f).hom 1) ⊗ₜ[(ringPresheaf O₁).obj Y]
          (show B.obj Y from B.map f y))
  rw [h1]

/-- **Base change of a tensor product of presheaves of modules.** The change-of-rings functor
of Tag 03CU carries the objectwise tensor product over `O₁` to the objectwise tensor product
over `O₂`: `O₂ ⊗_{O₁} (A ⊗_{O₁} B) ≅ (O₂ ⊗_{O₁} A) ⊗_{O₂} (O₂ ⊗_{O₁} B)`. -/
def changeOfRingsTensorObjIso :
    changeOfRingsObj θ (A ⊗ B) ≅ (changeOfRingsObj θ A) ⊗ (changeOfRingsObj θ B) :=
  PresheafOfModules.isoMk (changeOfRingsTensorAppIso θ A B)
    fun {_ _} f => changeOfRingsTensorAppIso_naturality θ A B f

/-- The components of the comparison isomorphism of presheaves are the objectwise comparison
isomorphisms, i.e. `TensorProduct.AlgebraTensorModule.distribBaseChange`, which carries
`a ⊗ₜ (x ⊗ₜ y)` to `(a ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y)`. -/
theorem changeOfRingsTensorObjIso_hom_app (X : Cᵒᵖ) :
    (changeOfRingsTensorObjIso θ A B).hom.app X = (changeOfRingsTensorAppIso θ A B X).hom := rfl

end Comparison

/-! ## Naturality in the two module arguments -/

section Naturality

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : O₁ ⟶ O₂)

/-- The comparison isomorphism is natural in both module arguments. -/
theorem changeOfRingsTensorObjIso_naturality
    {A₁ A₂ B₁ B₂ : PresheafOfModules.{w} (ringPresheaf O₁)} (u : A₁ ⟶ A₂) (v : B₁ ⟶ B₂) :
    (changeOfRings θ).map (u ⊗ₘ v) ≫ (changeOfRingsTensorObjIso θ A₂ B₂).hom =
      (changeOfRingsTensorObjIso θ A₁ B₁).hom ≫
        ((changeOfRings θ).map u ⊗ₘ (changeOfRings θ).map v) := by
  refine PresheafOfModules.hom_ext fun X => ?_
  let : Algebra ((ringPresheaf O₁).obj X) ((ringPresheaf O₂).obj X) := (θ.app X).hom.toAlgebra
  refine ModuleCat.hom_ext (linearMap_ext_tmul_tmul fun _ _ _ => ?_)
  rfl

/-- **Base change of a tensor product of presheaves of modules, functorially.** The
change-of-rings functor of Tag 03CU is monoidal for the objectwise tensor product, in the form
of an isomorphism of bifunctors: `O₂ ⊗_{O₁} (A ⊗_{O₁} B) ≅ (O₂ ⊗_{O₁} A) ⊗_{O₂} (O₂ ⊗_{O₁} B)`
naturally in `A` and `B`. This is step 4 of the chain of Tag 03EL at the level of presheaves
of modules. -/
def changeOfRingsTensorIso :
    tensor (PresheafOfModules.{w} (ringPresheaf O₁)) ⋙ changeOfRings θ ≅
      Functor.prod (changeOfRings θ) (changeOfRings θ) ⋙
        tensor (PresheafOfModules.{w} (ringPresheaf O₂)) :=
  NatIso.ofComponents (fun AB => changeOfRingsTensorObjIso θ AB.1 AB.2)
    fun {_ _} uv => changeOfRingsTensorObjIso_naturality θ uv.1 uv.2

/-- The components of `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorIso` are the
comparison isomorphisms. -/
theorem changeOfRingsTensorIso_app
    (AB : PresheafOfModules.{w} (ringPresheaf O₁) × PresheafOfModules.{w} (ringPresheaf O₁)) :
    (changeOfRingsTensorIso θ).app AB = changeOfRingsTensorObjIso θ AB.1 AB.2 := rfl

end Naturality

/-! ## Change of rings as a monoidal functor -/

section MonoidalFunctor

variable {C : Type u} [Category.{v} C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : O₁ ⟶ O₂)

/-- Two `S`-linear maps out of `S ⊗[R] M` agree as soon as they agree on the elements
`a ⊗ₜ m`. -/
theorem linearMap_ext_tmul {R S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    {M P : Type w} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module S P]
    {α β : (S ⊗[R] M) →ₗ[S] P} (h : ∀ (a : S) (m : M), α (a ⊗ₜ m) = β (a ⊗ₜ m)) : α = β :=
  linearMap_ext_tmul_aux h

/-- Two `S`-linear maps out of `S ⊗[R] M` agree as soon as they agree on the elements
`1 ⊗ₜ m`. This is the extensionality principle behind the change-of-rings adjunction: a map out
of a base-changed module is determined by its restriction. -/
theorem linearMap_ext_one_tmul {R S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    {M P : Type w} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module S P]
    {α β : (S ⊗[R] M) →ₗ[S] P} (h : ∀ m : M, α ((1 : S) ⊗ₜ m) = β ((1 : S) ⊗ₜ m)) : α = β :=
  linearMap_ext_tmul fun a m => by
    have ha : (a ⊗ₜ[R] m : S ⊗[R] M) = a • ((1 : S) ⊗ₜ[R] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ha, map_smul, map_smul, h]

/-- Two `S`-linear maps out of `S ⊗[R] (M ⊗[R] N)` agree as soon as they agree on the elements
`1 ⊗ₜ (m ⊗ₜ n)`. -/
theorem linearMap_ext_one_tmul_tmul {R S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    {M N P : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module S P] {α β : (S ⊗[R] (M ⊗[R] N)) →ₗ[S] P}
    (h : ∀ (m : M) (n : N), α ((1 : S) ⊗ₜ (m ⊗ₜ n)) = β ((1 : S) ⊗ₜ (m ⊗ₜ n))) : α = β :=
  linearMap_ext_one_tmul (apply_tmul_eq_of_tmul_tmul h)

/-- Two `S`-linear maps out of `S ⊗[R] ((M ⊗[R] N) ⊗[R] P)` agree as soon as they agree on the
elements `1 ⊗ₜ ((m ⊗ₜ n) ⊗ₜ p)`. -/
theorem linearMap_ext_one_tmul_tmul_tmul {R S : Type w} [CommRing R] [CommRing S] [Algebra R S]
    {M N P Q : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module S Q]
    {α β : (S ⊗[R] ((M ⊗[R] N) ⊗[R] P)) →ₗ[S] Q}
    (h : ∀ (m : M) (n : N) (p : P),
      α ((1 : S) ⊗ₜ ((m ⊗ₜ n) ⊗ₜ p)) = β ((1 : S) ⊗ₜ ((m ⊗ₜ n) ⊗ₜ p))) : α = β :=
  linearMap_ext_one_tmul_tmul fun u p => by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [TensorProduct.add_tmul, tmul_add, hx, hy]
    | tmul m n => exact h m n p

/-- The comparison isomorphism of the tensor units on sections over a fixed object,
`O₂(X) ≅ O₂(X) ⊗_{O₁(X)} O₁(X)`. This is Mathlib's
`TensorProduct.AlgebraTensorModule.rid`, i.e. the unit comparison of the monoidal structure on
`ModuleCat.extendScalars`. -/
def changeOfRingsUnitAppIso (X : Cᵒᵖ) :
    (𝟙_ (PresheafOfModules.{w} (ringPresheaf O₂))).obj X ≅
      (changeOfRingsObj θ (𝟙_ (PresheafOfModules.{w} (ringPresheaf O₁)))).obj X :=
  letI := (θ.app X).hom.toAlgebra
  (TensorProduct.AlgebraTensorModule.rid (O₁.obj X) (O₂.obj X) (O₂.obj X)).symm.toModuleIso

/-- The unit comparison is compatible with the restriction maps of the two unit presheaves. The
only fact used is that the restriction map of `O₁` preserves `1`. -/
theorem changeOfRingsUnitAppIso_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (𝟙_ (PresheafOfModules.{w} (ringPresheaf O₂))).map f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map
          (changeOfRingsUnitAppIso θ Y).hom =
      (changeOfRingsUnitAppIso θ X).hom ≫
        (changeOfRingsObj θ (𝟙_ (PresheafOfModules.{w} (ringPresheaf O₁)))).map f := by
  let := (θ.app X).hom.toAlgebra
  let := (θ.app Y).hom.toAlgebra
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  exact congrArg
    (fun r : O₁.obj Y =>
      (show O₂.obj Y from ((ringPresheaf O₂).map f).hom a) ⊗ₜ[O₁.obj Y] r)
    (map_one ((ringPresheaf O₁).map f).hom).symm

/-- The comparison isomorphism of the tensor units, `O₂ ≅ O₂ ⊗_{O₁} O₁`, as an isomorphism of
presheaves of `O₂`-modules. -/
def changeOfRingsUnitIso :
    𝟙_ (PresheafOfModules.{w} (ringPresheaf O₂)) ≅
      (changeOfRings θ).obj (𝟙_ (PresheafOfModules.{w} (ringPresheaf O₁))) :=
  PresheafOfModules.isoMk (changeOfRingsUnitAppIso θ)
    fun {_ _} f => changeOfRingsUnitAppIso_naturality θ f

/-- **Change of rings for presheaves of modules is a monoidal functor**, in the form of the
core data: the unit comparison is `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsUnitIso`
and the tensorator is the inverse of
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorObjIso`. -/
noncomputable def changeOfRingsCoreMonoidal : (changeOfRings θ).CoreMonoidal :=
  Functor.CoreMonoidal.mk'
    (εIso := changeOfRingsUnitIso θ)
    (μIso := fun A B => (changeOfRingsTensorObjIso θ A B).symm)
    (μIso_inv_natural_left := fun {_ _} _ _ => PresheafOfModules.hom_ext fun X => by
      let : Algebra ((ringPresheaf O₁).obj X) ((ringPresheaf O₂).obj X) :=
        (θ.app X).hom.toAlgebra
      exact ModuleCat.hom_ext (linearMap_ext_one_tmul_tmul fun _ _ => rfl))
    (μIso_inv_natural_right := fun {_ _} _ _ => PresheafOfModules.hom_ext fun X => by
      let : Algebra ((ringPresheaf O₁).obj X) ((ringPresheaf O₂).obj X) :=
        (θ.app X).hom.toAlgebra
      exact ModuleCat.hom_ext (linearMap_ext_one_tmul_tmul fun _ _ => rfl))
    (oplax_associativity := fun _ _ _ => PresheafOfModules.hom_ext fun X => by
      let : Algebra ((ringPresheaf O₁).obj X) ((ringPresheaf O₂).obj X) :=
        (θ.app X).hom.toAlgebra
      exact ModuleCat.hom_ext (linearMap_ext_one_tmul_tmul_tmul fun _ _ _ => rfl))
    (oplax_left_unitality := fun A => PresheafOfModules.hom_ext fun X => by
      let := (θ.app X).hom.toAlgebra
      let : Algebra (O₁.obj X) ((ringPresheaf O₂).obj X) := (θ.app X).hom.toAlgebra
      refine ModuleCat.hom_ext (linearMap_ext_one_tmul fun x => ?_)
      exact congrArg
        (fun s : (ringPresheaf O₂).obj X =>
          s ⊗ₜ[(ringPresheaf O₂).obj X]
            (show ((changeOfRings θ).obj A).obj X from (1 : O₂.obj X) ⊗ₜ[O₁.obj X] x))
        (one_smul (O₁.obj X) (1 : O₂.obj X)).symm)
    (oplax_right_unitality := fun A => PresheafOfModules.hom_ext fun X => by
      let := (θ.app X).hom.toAlgebra
      let : Algebra (O₁.obj X) ((ringPresheaf O₂).obj X) := (θ.app X).hom.toAlgebra
      refine ModuleCat.hom_ext (linearMap_ext_one_tmul fun x => ?_)
      exact congrArg
        (fun s : (ringPresheaf O₂).obj X =>
          (show ((changeOfRings θ).obj A).obj X from
            (1 : O₂.obj X) ⊗ₜ[O₁.obj X] x) ⊗ₜ[(ringPresheaf O₂).obj X] s)
        (one_smul (O₁.obj X) (1 : O₂.obj X)).symm)

/-- **Change of rings for presheaves of modules is a monoidal functor.** The change-of-rings
functor of Tag 03CU is strong monoidal for the objectwise tensor product: its tensorator is the
comparison isomorphism
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsTensorObjIso` of base change, and its unit
comparison is `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsUnitIso`. -/
@[instance_reducible]
noncomputable def changeOfRingsMonoidal : (changeOfRings θ).Monoidal :=
  (changeOfRingsCoreMonoidal θ).toMonoidal

/-- The oplax tensorator of `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsMonoidal` is the
base-change comparison isomorphism. -/
theorem changeOfRingsMonoidal_delta
    (A B : PresheafOfModules.{w} (ringPresheaf O₁)) :
    Functor.OplaxMonoidal.δ (self := (changeOfRingsMonoidal θ).toOplaxMonoidal)
        (changeOfRings θ) A B =
      (changeOfRingsTensorObjIso θ A B).hom :=
  rfl

end MonoidalFunctor

end Stacks.PresheafOfModules.ChangeOfRings

end
