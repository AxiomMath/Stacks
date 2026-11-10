module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Natural endomorphisms of extension of scalars are central

Let `f : A →+* B` be a homomorphism of commutative rings and `δ` a natural endomorphism of the
extension of scalars `M ↦ B ⊗_A M`, restricted to any full subcategory of `A`-modules which
contains `A`. Evaluating `δ` at `A` gives an element `u = δ_A(1 ⊗ 1)` of `B ⊗_A A = B`, and
naturality along the maps `A ⟶ M`, `a ↦ a • m`, shows that `δ_M` is multiplication by `u`.
Hence `δ` commutes with every `B`-linear map between modules of the form `B ⊗_A M`, also with
those which do not come from `A`-linear maps.

This is what makes two families of comparison isomorphisms between iterated base changes
interchangeable when one descends morphisms along a limit of rings: they differ by a natural
automorphism of a base change functor, which is multiplication by a unit, and conjugating a
`B`-linear map by it does nothing.

## Main results

* `ModuleCat.ExtendScalars.natTrans_app_comp_eq`: a natural endomorphism of extension of scalars
  commutes with every `B`-linear map between its values.
-/

@[expose] public section

open CategoryTheory

universe u

namespace ModuleCat.ExtendScalars

open scoped ChangeOfRings

variable {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
  {P : ObjectProperty (ModuleCat.{u} A)}

/-- The map `A ⟶ M`, `a ↦ a • m`, of `A`-modules. -/
private def toSpanSingleton (M : ModuleCat.{u} A) (m : M) : ModuleCat.of A A ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)

/-- The element `a ∈ B` acts on `1 ⊗ 1 ∈ B ⊗_A A` as `a ⊗ 1`. -/
private theorem smul_one_tmul_one (a : B) :
    a • (show (ModuleCat.extendScalars f).obj (ModuleCat.of A A) from (1 : B) ⊗ₜ[A,f] (1 : A)) =
      a ⊗ₜ[A,f] (1 : A) := by
  exact (ExtendScalars.smul_tmul (f := f) (M := ModuleCat.of A A) a 1 (1 : A)).trans
    (by rw [mul_one])

/-- Extension of scalars of `a ↦ a • m` sends `1 ⊗ 1` to `1 ⊗ m`. -/
private theorem map_toSpanSingleton_one_tmul_one (M : ModuleCat.{u} A) (m : M) :
    (ModuleCat.extendScalars f).map (toSpanSingleton M m) ((1 : B) ⊗ₜ[A,f] (1 : A)) =
      (1 : B) ⊗ₜ[A,f] m := by
  change (1 : B) ⊗ₜ[A,f] ((1 : A) • m) = _
  rw [one_smul]

/-- A natural endomorphism `δ` of extension of scalars acts on `B ⊗_A M` as multiplication by
`δ_A(1 ⊗ 1)`, read through `B ⊗_A A = B`. -/
private theorem natTrans_app_tmul (hA : P (ModuleCat.of A A))
    (δ : P.ι ⋙ ModuleCat.extendScalars f ⟶ P.ι ⋙ ModuleCat.extendScalars f)
    (M : P.FullSubcategory) (m : M.obj) :
    δ.app M ((1 : B) ⊗ₜ[A,f] m) =
      (ModuleCat.extendScalars f).map (toSpanSingleton M.obj m)
        (δ.app ⟨ModuleCat.of A A, hA⟩ ((1 : B) ⊗ₜ[A,f] (1 : A))) := by
  have h := congrArg (fun g => g.hom ((1 : B) ⊗ₜ[A,f] (1 : A)))
    (δ.naturality (X := ⟨ModuleCat.of A A, hA⟩) (Y := M)
      (ObjectProperty.homMk (toSpanSingleton M.obj m)))
  exact (congrArg (δ.app M) (map_toSpanSingleton_one_tmul_one (f := f) M.obj m).symm).trans h

/-- **A natural endomorphism of extension of scalars is multiplication by a scalar**: `δ_M` is
multiplication by the element of `B` that `δ_A(1 ⊗ 1)` corresponds to under `B ⊗_A A = B`. -/
theorem natTrans_app_eq_smul (hA : P (ModuleCat.of A A))
    (δ : P.ι ⋙ ModuleCat.extendScalars f ⟶ P.ι ⋙ ModuleCat.extendScalars f) :
    ∃ u : B, ∀ M : P.FullSubcategory,
      δ.app M = u • 𝟙 ((ModuleCat.extendScalars f).obj M.obj) := by
  let u : B := TensorProduct.rid A ((restrictScalars f).obj (of B B))
    (δ.app ⟨ModuleCat.of A A, hA⟩ ((1 : B) ⊗ₜ[A,f] (1 : A)))
  let e₁ : (ModuleCat.extendScalars f).obj (ModuleCat.of A A) := (1 : B) ⊗ₜ[A,f] (1 : A)
  have hu : δ.app ⟨ModuleCat.of A A, hA⟩ e₁ = u • e₁ := by
    rw [smul_one_tmul_one]
    exact ((TensorProduct.rid A ((restrictScalars f).obj (of B B))).symm_apply_apply _).symm
  refine ⟨u, fun M => ExtendScalars.hom_ext fun m => ?_⟩
  have h1 := map_toSpanSingleton_one_tmul_one (f := f) M.obj m
  calc δ.app M ((1 : B) ⊗ₜ[A,f] m)
      = (ModuleCat.extendScalars f).map (toSpanSingleton M.obj m)
          (δ.app ⟨ModuleCat.of A A, hA⟩ e₁) := natTrans_app_tmul hA δ M m
    _ = (ModuleCat.extendScalars f).map (toSpanSingleton M.obj m) (u • e₁) := by rw [hu]
    _ = (u • 𝟙 ((ModuleCat.extendScalars f).obj M.obj))
          ((ModuleCat.extendScalars f).map (toSpanSingleton M.obj m) e₁) := map_smul _ _ _
    _ = (u • 𝟙 ((ModuleCat.extendScalars f).obj M.obj)) ((1 : B) ⊗ₜ[A,f] m) :=
          congrArg (u • 𝟙 ((ModuleCat.extendScalars f).obj M.obj)) h1

/-- **A natural endomorphism of extension of scalars commutes with every `B`-linear map between
its values**, on any full subcategory of `A`-modules containing `A`. -/
theorem natTrans_app_comp_eq (hA : P (ModuleCat.of A A))
    (δ : P.ι ⋙ ModuleCat.extendScalars f ⟶ P.ι ⋙ ModuleCat.extendScalars f)
    {M N : P.FullSubcategory}
    (φ : (ModuleCat.extendScalars f).obj M.obj ⟶ (ModuleCat.extendScalars f).obj N.obj) :
    δ.app M ≫ φ = φ ≫ δ.app N := by
  obtain ⟨u, hu⟩ := natTrans_app_eq_smul hA δ
  rw [hu, hu]
  exact (Linear.smul_comp _ _ _ _ _ _).trans ((congrArg (u • ·)
    ((Category.id_comp φ).trans (Category.comp_id φ).symm)).trans
      (Linear.comp_smul _ _ _ _ _ _).symm)

/-- An element of `B` acting as the identity on `B ⊗_A A` is `1`. -/
theorem eq_one_of_smul_id_eq_id (a : B)
    (h : a • 𝟙 ((ModuleCat.extendScalars f).obj (ModuleCat.of A A)) = 𝟙 _) : a = 1 := by
  let e₁ : (ModuleCat.extendScalars f).obj (ModuleCat.of A A) := (1 : B) ⊗ₜ[A,f] (1 : A)
  have h₁ : a • e₁ = e₁ := congrArg (fun g => g.hom e₁) h
  rw [smul_one_tmul_one] at h₁
  exact (TensorProduct.rid A ((restrictScalars f).obj (of B B))).symm.injective h₁

end ModuleCat.ExtendScalars

end
