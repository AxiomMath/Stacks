module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion

/-!
# Shrinking the morphisms of a category over a base

Let `p : 𝒳 ⥤ 𝒞` be a category over `𝒞`. When `𝒳` is locally `w`-small, replacing every hom set of
`𝒳` by a `w`-small model gives a category `ShrinkHoms 𝒳` with the same objects and morphisms in
`Type w`, and `p` transported along the equivalence `𝒳 ≌ ShrinkHoms 𝒳` makes it a category over
`𝒞` equivalent over `𝒞` to `𝒳`.

For a fibred category, local smallness of `𝒳` reduces to local smallness of the base and of the
fibres: a morphism `a ⟶ b` of `𝒳` is the same as its image `φ : p a ⟶ p b` together with a
morphism of the fibre over `p a` from `a` to the chosen pullback of `b` along `φ`.

## Main definitions

* `StacksRepresentableCFG.shrinkHomsEquivalenceOver`: the equivalence over `𝒞`
  between `p` and `ShrinkHoms.inverse 𝒳 ⋙ p`.

## Main results

* `CategoryTheory.Functor.locallySmall_of_small_fiberHom`: a prefibred category over a locally
  `w`-small base whose fibres have `w`-small hom sets is locally `w`-small.
-/

@[expose] public section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- A prefibred category over a locally `w`-small base whose fibres have `w`-small hom sets is
locally `w`-small. -/
theorem locallySmall_of_small_fiberHom (p : 𝒳 ⥤ 𝒞) [p.IsPreFibered] [LocallySmall.{w} 𝒞]
    (h : ∀ (U : 𝒞) (x y : p.Fiber U), Small.{w} (x ⟶ y)) : LocallySmall.{w} 𝒳 where
  hom_small a b := by
    let Y : (p.obj a ⟶ p.obj b) → p.Fiber (p.obj a) := fun φ =>
      Fiber.mk (IsPreFibered.pullbackObj_proj (rfl : p.obj b = p.obj b) φ)
    have key (α : a ⟶ b) : ∃ β : a ⟶ IsPreFibered.pullbackObj (rfl : p.obj b = p.obj b) (p.map α),
        IsHomLift p (𝟙 (p.obj a)) β ∧
          β ≫ IsPreFibered.pullbackMap (rfl : p.obj b = p.obj b) (p.map α) = α :=
      have := IsHomLift.map (p := p) α
      ⟨_, IsCartesian.map_isHomLift p (p.map α) _ α,
        IsCartesian.fac p (p.map α) (IsPreFibered.pullbackMap rfl (p.map α)) α⟩
    choose lift hlift hfac using key
    let F : (a ⟶ b) → Σ φ : p.obj a ⟶ p.obj b, (Fiber.mk (rfl : p.obj a = p.obj a) ⟶ Y φ) :=
      fun α => ⟨p.map α, ⟨lift α, hlift α⟩⟩
    let G : (Σ φ : p.obj a ⟶ p.obj b, (Fiber.mk (rfl : p.obj a = p.obj a) ⟶ Y φ)) → (a ⟶ b) :=
      fun s => (show a ⟶ IsPreFibered.pullbackObj (rfl : p.obj b = p.obj b) s.1 from s.2.1) ≫
        IsPreFibered.pullbackMap (rfl : p.obj b = p.obj b) s.1
    have (φ : p.obj a ⟶ p.obj b) : Small.{w} (Fiber.mk (rfl : p.obj a = p.obj a) ⟶ Y φ) :=
      h _ _ _
    exact small_of_injective (f := F) (Function.LeftInverse.injective (g := G) hfac)

end Functor

end CategoryTheory

namespace StacksRepresentableCFG

open CategoryTheory

universe w v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- A locally `w`-small category over `𝒞` is equivalent over `𝒞` to its hom-shrunk model
`ShrinkHoms 𝒳`, whose morphisms live in `Type w`, lying over `𝒞` through
`ShrinkHoms.inverse 𝒳 ⋙ p`. The underlying equivalence is `ShrinkHoms.equivalence 𝒳`. -/
noncomputable def shrinkHomsEquivalenceOver (p : 𝒳 ⥤ 𝒞) [LocallySmall.{w} 𝒳] :
    EquivalenceOver p (ShrinkHoms.inverse 𝒳 ⋙ p) where
  hom := ⟨ShrinkHoms.functor 𝒳, by
    have h : ShrinkHoms.functor 𝒳 ⋙ ShrinkHoms.inverse 𝒳 = 𝟭 𝒳 :=
      CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ f => by
        simp only [CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map]
        change (equivShrink _).symm (equivShrink _ f) = _
        rw [Equiv.symm_apply_apply]
        exact (by simp : f = 𝟙 _ ≫ f ≫ 𝟙 _))
    rw [← CategoryTheory.Functor.assoc, h, CategoryTheory.Functor.id_comp]⟩
  inv := { functor := ShrinkHoms.inverse 𝒳, w := rfl }
  unitIso := (ShrinkHoms.equivalence 𝒳).unitIso
  counitIso := (ShrinkHoms.equivalence 𝒳).counitIso
  unit_over := by
    ext x
    change p.map (𝟙 x) = _
    rw [CategoryTheory.Functor.map_id, eqToHom_app]
    exact (eqToHom_refl _ _).symm
  counit_over := by
    ext x
    change p.map ((equivShrink _).symm (equivShrink _ (𝟙 (ShrinkHoms.fromShrinkHoms x)))) = _
    rw [Equiv.symm_apply_apply, CategoryTheory.Functor.map_id, eqToHom_app]
    exact (eqToHom_refl _ _).symm

end StacksRepresentableCFG

end
