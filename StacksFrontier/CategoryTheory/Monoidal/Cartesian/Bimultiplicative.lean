module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# Bimultiplicative morphisms of monoid objects

Let `C` be a cartesian monoidal category and `M`, `N`, `L` monoid objects of `C`. A morphism
`β : M ⊗ N ⟶ L` is *bimultiplicative* when it is multiplicative in each variable on generalized
elements: for all `f₁ f₂ : X ⟶ M` and `g : X ⟶ N`,
`lift (f₁ * f₂) g ≫ β = (lift f₁ g ≫ β) * (lift f₂ g ≫ β)`, and symmetrically. For commutative
group objects written additively this is biadditivity, the internal form of a bilinear pairing;
in the category of types it is the usual notion.

A monoidal functor between cartesian monoidal categories carries bimultiplicative morphisms to
bimultiplicative morphisms. This is how the pairing of coefficients
`ℱ_ρ ⊗ ℱ_{ρ^∨} → ℤ/ℓ^kℤ` in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) is carried from the invariant pairing of
`π₁`-modules to the finite locally constant sheaves of Tag 0DV5: the equivalence of Tag 0DV5 (2)
is the transport of commutative group objects along a product-preserving equivalence.

## Main definitions

* `CategoryTheory.IsBimultiplicative`: multiplicativity in each variable on generalized
  elements.

## Main results

* `CategoryTheory.isBimultiplicative_iff`: it suffices to test on the universal generalized
  elements, the projections of `M ⊗ (M ⊗ N)` and of `M ⊗ (N ⊗ N)`.
* `CategoryTheory.IsBimultiplicative.map`: a monoidal functor carries a bimultiplicative `β` to
  the bimultiplicative `μ F M N ≫ F.map β`; `CategoryTheory.IsBimultiplicative.of_map` is the
  converse for a faithful one, and `CategoryTheory.IsBimultiplicative.preimage` descends a
  bimultiplicative morphism along a fully faithful one.
* `CategoryTheory.IsBimultiplicative.comp`: composition with morphisms of monoid objects.
* `CategoryTheory.isBimultiplicative_iff_app`: in a category of presheaves of types,
  bimultiplicativity is sectionwise multiplicativity in each variable.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped MonObj

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]

/-- A morphism `β : M ⊗ N ⟶ L` of monoid objects is **bimultiplicative** when it is
multiplicative in each variable on generalized elements. -/
structure IsBimultiplicative {M N L : C} [MonObj M] [MonObj N] [MonObj L] (β : M ⊗ N ⟶ L) :
    Prop where
  /-- Multiplicativity in the first variable. -/
  lift_mul_left {X : C} (f₁ f₂ : X ⟶ M) (g : X ⟶ N) :
    lift (f₁ * f₂) g ≫ β = (lift f₁ g ≫ β) * (lift f₂ g ≫ β)
  /-- Multiplicativity in the second variable. -/
  lift_mul_right {X : C} (f : X ⟶ M) (g₁ g₂ : X ⟶ N) :
    lift f (g₁ * g₂) ≫ β = (lift f g₁ ≫ β) * (lift f g₂ ≫ β)

variable {M N L : C} [MonObj M] [MonObj N] [MonObj L]

/-- **Bimultiplicativity is tested on the universal generalized elements**: the two
projections `M ⊗ (M ⊗ N) ⟶ M` and the projection to `N`, and symmetrically for
`M ⊗ (N ⊗ N)`. -/
theorem isBimultiplicative_iff (β : M ⊗ N ⟶ L) :
    IsBimultiplicative β ↔
      lift (fst M (M ⊗ N) * (snd M (M ⊗ N) ≫ fst M N)) (snd M (M ⊗ N) ≫ snd M N) ≫ β =
          (lift (fst M (M ⊗ N)) (snd M (M ⊗ N) ≫ snd M N) ≫ β) *
            (lift (snd M (M ⊗ N) ≫ fst M N) (snd M (M ⊗ N) ≫ snd M N) ≫ β) ∧
        lift (fst M (N ⊗ N)) (snd M (N ⊗ N) ≫ fst N N * (snd M (N ⊗ N) ≫ snd N N)) ≫ β =
          (lift (fst M (N ⊗ N)) (snd M (N ⊗ N) ≫ fst N N) ≫ β) *
            (lift (fst M (N ⊗ N)) (snd M (N ⊗ N) ≫ snd N N) ≫ β) := by
  refine ⟨fun h => ⟨h.lift_mul_left _ _ _, h.lift_mul_right _ _ _⟩, fun ⟨hl, hr⟩ => ⟨?_, ?_⟩⟩
  · intro X f₁ f₂ g
    simpa [comp_mul, ← Category.assoc, comp_lift] using congrArg (lift f₁ (lift f₂ g) ≫ ·) hl
  · intro X f g₁ g₂
    simpa [comp_mul, ← Category.assoc, comp_lift] using congrArg (lift f (lift g₁ g₂) ≫ ·) hr

open scoped Obj in
/-- **A monoidal functor carries bimultiplicative morphisms to bimultiplicative morphisms**: if
`β : M ⊗ N ⟶ L` is bimultiplicative then so is `μ F M N ≫ F.map β : F M ⊗ F N ⟶ F L`, for the
monoid structures `F` transports. -/
theorem IsBimultiplicative.map {β : M ⊗ N ⟶ L} (hβ : IsBimultiplicative β) (F : C ⥤ D)
    [F.Monoidal] : IsBimultiplicative (Functor.LaxMonoidal.μ F M N ≫ F.map β) := by
  have key : ∀ {X : D} {A : C} (a : A ⟶ M) (b : A ⟶ N) (h : X ⟶ F.obj A),
      lift (h ≫ F.map a) (h ≫ F.map b) ≫ Functor.LaxMonoidal.μ F M N ≫ F.map β =
        h ≫ F.map (lift a b ≫ β) := by
    intro X A a b h
    rw [← comp_lift_assoc, Functor.Monoidal.lift_μ_assoc, ← F.map_comp]
  have split : ∀ {X : D} {P Q R : C} (a : X ⟶ F.obj P) (b : X ⟶ F.obj Q) (c : X ⟶ F.obj R),
      ∃ h : X ⟶ F.obj (P ⊗ (Q ⊗ R)), a = h ≫ F.map (fst _ _) ∧
        b = h ≫ F.map (snd _ _ ≫ fst _ _) ∧ c = h ≫ F.map (snd _ _ ≫ snd _ _) := by
    intro X P Q R a b c
    refine ⟨lift a (lift b c ≫ Functor.LaxMonoidal.μ F Q R) ≫ Functor.LaxMonoidal.μ F _ _, ?_⟩
    simp
  constructor
  · intro X f₁ f₂ g
    obtain ⟨h, rfl, rfl, rfl⟩ := split f₁ f₂ g
    rw [← comp_mul, ← Functor.map_mul, key, key, key, hβ.lift_mul_left, Functor.map_mul, comp_mul]
  · intro X f g₁ g₂
    obtain ⟨h, rfl, rfl, rfl⟩ := split f g₁ g₂
    rw [← comp_mul, ← Functor.map_mul, key, key, key, hβ.lift_mul_right, Functor.map_mul, comp_mul]

open scoped Obj in
/-- **A faithful monoidal functor reflects bimultiplicativity**: if `μ F M N ≫ F.map β` is
bimultiplicative for the monoid structures `F` transports, then so is `β`. -/
theorem IsBimultiplicative.of_map {β : M ⊗ N ⟶ L} (F : C ⥤ D) [F.Monoidal] [F.Faithful]
    (hβ : IsBimultiplicative (Functor.LaxMonoidal.μ F M N ≫ F.map β)) : IsBimultiplicative β := by
  have key : ∀ {X : C} (a : X ⟶ M) (b : X ⟶ N),
      F.map (lift a b ≫ β) = lift (F.map a) (F.map b) ≫ Functor.LaxMonoidal.μ F M N ≫ F.map β := by
    intro X a b
    rw [Functor.Monoidal.lift_μ_assoc, F.map_comp]
  refine ⟨fun f₁ f₂ g => F.map_injective ?_, fun f g₁ g₂ => F.map_injective ?_⟩ <;>
    rw [Functor.map_mul, key, key, key, Functor.map_mul]
  exacts [hβ.lift_mul_left _ _ _, hβ.lift_mul_right _ _ _]

/-- Bimultiplicativity is preserved by precomposing with morphisms of monoid objects in each
variable and postcomposing with a morphism of monoid objects. -/
theorem IsBimultiplicative.comp {M' N' L' : C} [MonObj M'] [MonObj N'] [MonObj L']
    {β : M ⊗ N ⟶ L} (hβ : IsBimultiplicative β) (a : M' ⟶ M) (b : N' ⟶ N) (c : L ⟶ L')
    [ha : IsMonHom a] [hb : IsMonHom b] [hc : IsMonHom c] :
    IsBimultiplicative ((a ⊗ₘ b) ≫ β ≫ c) := by
  constructor
  · intro X f₁ f₂ g
    rw [lift_map_assoc, MonObj.mul_comp, ← Category.assoc, hβ.lift_mul_left, MonObj.mul_comp,
      Category.assoc, Category.assoc, lift_map_assoc, lift_map_assoc]
  · intro X f g₁ g₂
    rw [lift_map_assoc, MonObj.mul_comp, ← Category.assoc, hβ.lift_mul_right, MonObj.mul_comp,
      Category.assoc, Category.assoc, lift_map_assoc, lift_map_assoc]

open scoped Obj in
/-- **Bimultiplicative morphisms descend along a fully faithful monoidal functor**: a
bimultiplicative `β' : F M ⊗ F N ⟶ F L` comes from the bimultiplicative morphism
`hF.preimage (δ F M N ≫ β') : M ⊗ N ⟶ L`. Along an equivalence such as Tag 0DV5 (2) this carries
a pairing of `π₁`-modules to a pairing of the corresponding sheaves. -/
theorem IsBimultiplicative.preimage {F : C ⥤ D} [F.Monoidal] (hF : F.FullyFaithful)
    {β' : F.obj M ⊗ F.obj N ⟶ F.obj L} (hβ' : IsBimultiplicative β') :
    IsBimultiplicative (hF.preimage (Functor.OplaxMonoidal.δ F M N ≫ β')) := by
  have := hF.faithful
  refine IsBimultiplicative.of_map F ?_
  rwa [hF.map_preimage, Functor.Monoidal.μ_δ_assoc]

/-! ### Presheaves of types -/

section Presheaf

universe w v₃ u₃

variable {E : Type u₃} [Category.{v₃} E] {R S T : E ⥤ Type w} [MonObj R] [MonObj S] [MonObj T]

/-- **Bimultiplicativity of a morphism of presheaves of types is sectionwise**: `β` is
bimultiplicative exactly when on the sections over every object it is multiplicative in each
variable for the operations `μ.app U`. -/
theorem isBimultiplicative_iff_app (β : R ⊗ S ⟶ T) :
    IsBimultiplicative β ↔ ∀ (U : E),
      (∀ (x x' : R.obj U) (y : S.obj U),
        β.app U ((MonObj.mul (X := R)).app U (x, x'), y) =
          (MonObj.mul (X := T)).app U (β.app U (x, y), β.app U (x', y))) ∧
      (∀ (x : R.obj U) (y y' : S.obj U),
        β.app U (x, (MonObj.mul (X := S)).app U (y, y')) =
          (MonObj.mul (X := T)).app U (β.app U (x, y), β.app U (x, y'))) := by
  rw [isBimultiplicative_iff]
  constructor
  · rintro ⟨hl, hr⟩ U
    exact ⟨fun x x' y => ConcreteCategory.congr_hom (CC := fun X : Type w => X) (congr_app hl U)
        ((x, (x', y)) : R.obj U × (R.obj U × S.obj U)),
      fun x y y' => ConcreteCategory.congr_hom (CC := fun X : Type w => X) (congr_app hr U)
        ((x, (y, y')) : R.obj U × (S.obj U × S.obj U))⟩
  · intro h
    refine ⟨?_, ?_⟩ <;> ext U ⟨a, b, c⟩
    · exact (h U).1 a b c
    · exact (h U).2 a b c

end Presheaf

end CategoryTheory
