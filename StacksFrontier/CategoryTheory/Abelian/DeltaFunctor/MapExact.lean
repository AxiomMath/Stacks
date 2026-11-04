module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Effaceable
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalUniversal

/-!
# Composing a δ-functor with an exact functor

Let `F = (Fⁿ, δ)` be a cohomological δ-functor from an abelian category `A` to an abelian
category `B`, and `Φ : B ⥤ C` an exact additive functor to an abelian category `C`. Then
`(Φ ∘ Fⁿ, Φ(δ))` is again a cohomological δ-functor, because `Φ` preserves the exactness of
every piece of the long exact sequence and the monomorphism `F⁰(X₁) → F⁰(X₂)`. It is effaceable
as soon as `F` is: `Φ` sends `Fⁿ⁺¹(ι) = 0` to `0`.

Applied to the opposite `H.op : Aᵒᵖ → Bᵒᵖ` of a homological δ-functor `H` and to an exact
contravariant functor `Φ : Bᵒᵖ ⥤ C` (for instance character duality of modules), this gives the
**dual of a homological δ-functor**, a cohomological δ-functor on `Aᵒᵖ`, `X ↦ Φ(Hₙ(X))`, which is
effaceable, hence universal (Stacks 010T), whenever `H` is coeffaceable.

## Main definitions

* `CategoryTheory.DeltaFunctor.mapExact`: `Φ ∘ F`.
* `Stacks.CategoryHomology.HomologicalDeltaFunctor.dualExact`: `X ↦ Φ(Hₙ(X.unop))` on `Aᵒᵖ`.

## Main results

* `CategoryTheory.DeltaFunctor.effaceable_mapExact`.
* `Stacks.CategoryHomology.HomologicalDeltaFunctor.isUniversal_dualExact`: the dual of a
  coeffaceable homological δ-functor is universal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.DeltaFunctor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] (F : DeltaFunctor A B) (Φ : B ⥤ C) [Φ.Additive]
  [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

/-- **The composite of a δ-functor with an exact functor**, `(Φ ∘ Fⁿ, Φ(δ))`. -/
def mapExact : DeltaFunctor A C where
  functor n := F.functor n ⋙ Φ
  δ hS n := Φ.map (F.δ hS n)
  map_g_δ hS n := by
    change Φ.map ((F.functor n).map _) ≫ Φ.map (F.δ hS n) = 0
    rw [← Φ.map_comp, F.map_g_δ, Φ.map_zero]
  δ_map_f hS n := by
    change Φ.map (F.δ hS n) ≫ Φ.map ((F.functor (n + 1)).map _) = 0
    rw [← Φ.map_comp, F.δ_map_f, Φ.map_zero]
  mono_map_f hS := by
    have := F.mono_map_f hS
    change Mono (Φ.map ((F.functor 0).map _))
    infer_instance
  exact_map hS n := (F.exact_map hS n).map Φ
  exact_δ₁ hS n := (F.exact_δ₁ hS n).map Φ
  exact_δ₂ hS n := (F.exact_δ₂ hS n).map Φ
  δ_naturality hS hT φ n := by
    change Φ.map ((F.functor n).map φ.τ₃) ≫ Φ.map (F.δ hT n) =
      Φ.map (F.δ hS n) ≫ Φ.map ((F.functor (n + 1)).map φ.τ₁)
    rw [← Φ.map_comp, ← Φ.map_comp, F.δ_naturality]

/-- The `n`-th functor of `F.mapExact Φ` is `F.functor n ⋙ Φ`. -/
@[simp]
lemma mapExact_functor (n : ℕ) : (F.mapExact Φ).functor n = F.functor n ⋙ Φ := rfl

/-- The connecting morphisms of `F.mapExact Φ` are the images under `Φ` of those of `F`. -/
@[simp]
lemma mapExact_δ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (F.mapExact Φ).δ hS n = Φ.map (F.δ hS n) := rfl

/-- An effacement for `F` is one for `Φ ∘ F`. -/
def Effacement.mapExact {X : A} {n : ℕ} (e : F.Effacement X n) : (F.mapExact Φ).Effacement X n where
  I := e.I
  ι := e.ι
  map_ι := by
    change Φ.map ((F.functor (n + 1)).map e.ι) = 0
    rw [e.map_ι, Φ.map_zero]

/-- **`Φ ∘ F` is effaceable when `F` is.** -/
theorem effaceable_mapExact [F.Effaceable] : (F.mapExact Φ).Effaceable where
  nonempty X n := ⟨(Effaceable.nonempty (F := F) X n).some.mapExact F Φ⟩

end CategoryTheory.DeltaFunctor

namespace Stacks.CategoryHomology.HomologicalDeltaFunctor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C] (H : HomologicalDeltaFunctor A B) (Φ : Bᵒᵖ ⥤ C)
  [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

/-- **The dual of a homological δ-functor** along an exact contravariant functor `Φ`: the
cohomological δ-functor `X ↦ Φ(Hₙ(X.unop))` on `Aᵒᵖ`, whose connecting morphisms are the images
under `Φ` of those of `H`. -/
def dualExact : CategoryTheory.DeltaFunctor Aᵒᵖ C := H.op.mapExact Φ

/-- The `n`-th functor of `H.dualExact Φ` sends `X` to `Φ(Hₙ(X.unop))`. -/
lemma dualExact_functor_obj (n : ℕ) (X : Aᵒᵖ) :
    ((H.dualExact Φ).functor n).obj X = Φ.obj (Opposite.op ((H.functor n).obj X.unop)) := rfl

/-- The `n`-th functor of `H.dualExact Φ` sends `f` to `Φ(Hₙ(f.unop))`. -/
lemma dualExact_functor_map (n : ℕ) {X Y : Aᵒᵖ} (f : X ⟶ Y) :
    ((H.dualExact Φ).functor n).map f = Φ.map ((H.functor n).map f.unop).op := rfl

/-- **The dual of a coeffaceable homological δ-functor is effaceable.** -/
theorem effaceable_dualExact [H.Coeffaceable] : (H.dualExact Φ).Effaceable := by
  have := H.effaceable_op
  exact H.op.effaceable_mapExact Φ

/-- **The dual of a coeffaceable homological δ-functor is universal** (Stacks 010T). -/
theorem isUniversal_dualExact [H.Coeffaceable] : (H.dualExact Φ).IsUniversal := by
  have := H.effaceable_dualExact Φ
  exact CategoryTheory.DeltaFunctor.isUniversal_of_effaceable _

end Stacks.CategoryHomology.HomologicalDeltaFunctor

end
