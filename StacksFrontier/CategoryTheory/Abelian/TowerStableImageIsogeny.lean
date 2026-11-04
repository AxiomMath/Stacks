module

public import StacksFrontier.CategoryTheory.Abelian.TowerMittagLeffler

/-!
# The stable image tower is isogenous to the tower, uniformly in the level

Let `T`, `S` be towers in an abelian category with the exact sequences of
`CategoryTheory.LAdicTower.LESData` (for instance `Tₙ = R^q f_! Fₙ`, `Sₙ = R^{q+1} f_! Fₙ` for the
levels of a flat ℓ-adic sheaf), `S₀` a Noetherian object and `Sₙ` killed by `ℓⁿ⁺¹`. The stable
images `Hₙ = Im(T_{n+β+1} ⟶ Tₙ)` (`CategoryTheory.LAdicTower.LESData.stableImageTower`) are not
only pro-isomorphic to `T`: multiplication by `ℓ^{β+1}` on `Tₙ` factors through `Hₙ`, so
`Hₙ ⊆ Tₙ` is an isogeny with exponent `β + 1` independent of `n`.

Indeed, the obstruction to lifting a generalized element `x` of `Tₙ` to `T_{n+β+1}` is its image
under the connecting map `δ : Tₙ ⟶ S_β`, and `S_β` is killed by `ℓ^{β+1}`, so `ℓ^{β+1} x` lifts.
The factorisations form a map of towers `T ⟶ H`
(`CategoryTheory.LAdicTower.LESData.stableImageIsogeny`), inverse to the inclusion `H ⟶ T` up to
`ℓ^{β+1}` in both orders, and compatible with every endomorphism of `T` preserving `H`.

## Main definitions

* `CategoryTheory.LAdicTower.LESData.stableImageIsogenyApp`: the factorisation at level `n`.
* `CategoryTheory.LAdicTower.LESData.stableImageIsogeny`: the map of towers `T ⟶ H`.

## Main results

* `CategoryTheory.LAdicTower.LESData.stableImageIsogeny_ι`: `T ⟶ H ⟶ T` is `ℓ^{β+1}`.
* `CategoryTheory.LAdicTower.LESData.ι_stableImageIsogeny`: `H ⟶ T ⟶ H` is `ℓ^{β+1}`.
* `CategoryTheory.LAdicTower.LESData.stableImageIsogeny_naturality`: compatibility with
  endomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Preadditive Opposite

namespace CategoryTheory.LAdicTower

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] {T S : ℕᵒᵖ ⥤ C} {ℓ : ℕ}

namespace LESData

variable (D : LESData T S ℓ) [IsNoetherianObject (towerObj S 0)]

/-- Multiplication by a natural number commutes with every morphism. -/
private theorem comp_nsmul_id_eq_nsmul_id_comp {X Y : C} (f : X ⟶ Y) (m : ℕ) :
    f ≫ (m • 𝟙 Y) = (m • 𝟙 X) ≫ f := by
  rw [comp_nsmul, nsmul_comp, Category.comp_id, Category.id_comp]

/-- **`ℓ^{β+1} Tₙ` lies in the stable image**: multiplication by `ℓ^{β+1}` on `Tₙ` composed with
the cokernel of the inclusion of the stable image `Hₙ` vanishes, `β` the uniform shift. -/
theorem nsmul_comp_cokernel_stableImageι (hS : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj S n) = 0)
    (n : ℕ) :
    (ℓ ^ (D.shift + 1) • 𝟙 (towerObj T n)) ≫ cokernel.π (D.stableImageι.app (op n)) = 0 := by
  have hδ : (ℓ ^ (D.shift + 1) • 𝟙 (towerObj T n)) ≫ D.δ D.shift n = 0 := by
    rw [nsmul_comp, Category.id_comp, ← Category.comp_id (D.δ D.shift n), ← comp_nsmul,
      hS D.shift, comp_zero]
  obtain ⟨X', π, hπ, y, hy⟩ := D.exactδ D.shift n (n + D.shift + 1) (by omega) _ hδ
  rw [← cancel_epi π, comp_zero, ← Category.assoc, hy, Category.assoc,
    ← D.stableImageRetraction_ι n, Category.assoc, cokernel.condition, comp_zero, comp_zero]

/-- **The factorisation `Tₙ ⟶ Hₙ` of `ℓ^{β+1}`** through the stable image. -/
def stableImageIsogenyApp (hS : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj S n) = 0) (n : ℕ) :
    towerObj T n ⟶ towerObj D.stableImageTower n :=
  Abelian.monoLift (D.stableImageι.app (op n)) _ (D.nsmul_comp_cokernel_stableImageι hS n)

/-- The factorisation `Tₙ ⟶ Hₙ` followed by the inclusion `Hₙ ⟶ Tₙ` is multiplication by
`ℓ^{β+1}` on `Tₙ`. -/
@[reassoc (attr := simp)]
theorem stableImageIsogenyApp_ι (hS : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj S n) = 0) (n : ℕ) :
    D.stableImageIsogenyApp hS n ≫ D.stableImageι.app (op n) =
      ℓ ^ (D.shift + 1) • 𝟙 (towerObj T n) :=
  Abelian.monoLift_comp _ _ _

/-- The factorisations are natural in the level. -/
theorem towerMap_stableImageIsogenyApp (hS : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj S n) = 0)
    {n n' : ℕ} (h : n ≤ n') :
    towerMap T h ≫ D.stableImageIsogenyApp hS n =
      D.stableImageIsogenyApp hS n' ≫ towerMap D.stableImageTower h := by
  rw [← cancel_mono (D.stableImageι.app (op n)), Category.assoc, Category.assoc,
    stableImageIsogenyApp_ι, D.towerMap_stableImageι, stableImageIsogenyApp_ι_assoc,
    comp_nsmul_id_eq_nsmul_id_comp]

/-- **The map of towers `T ⟶ H`**, levelwise the factorisation of `ℓ^{β+1}` through the stable
image. -/
def stableImageIsogeny (hS : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj S n) = 0) :
    T ⟶ D.stableImageTower where
  app n := D.stableImageIsogenyApp hS n.unop
  naturality _ _ f := (D.towerMap_stableImageIsogenyApp hS (leOfHom f.unop))

/-- The component of `T ⟶ H` at level `n` is the factorisation `Tₙ ⟶ Hₙ`. -/
theorem stableImageIsogeny_app (hS : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj S n) = 0) (n : ℕ) :
    (D.stableImageIsogeny hS).app (op n) = D.stableImageIsogenyApp hS n :=
  rfl

/-- **`T ⟶ H ⟶ T` is multiplication by `ℓ^{β+1}`.** -/
@[reassoc]
theorem stableImageIsogeny_ι (hS : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj S n) = 0) :
    D.stableImageIsogeny hS ≫ D.stableImageι = ℓ ^ (D.shift + 1) • 𝟙 T := by
  ext ⟨n⟩
  rw [NatTrans.comp_app, stableImageIsogeny_app, stableImageIsogenyApp_ι, NatTrans.app_nsmul,
    NatTrans.id_app]

/-- **`H ⟶ T ⟶ H` is multiplication by `ℓ^{β+1}`.** -/
@[reassoc]
theorem ι_stableImageIsogeny (hS : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj S n) = 0) :
    D.stableImageι ≫ D.stableImageIsogeny hS = ℓ ^ (D.shift + 1) • 𝟙 D.stableImageTower := by
  ext ⟨n⟩
  rw [NatTrans.comp_app, NatTrans.app_nsmul, NatTrans.id_app, stableImageIsogeny_app,
    ← cancel_mono (D.stableImageι.app (op n)), Category.assoc, stableImageIsogenyApp_ι,
    comp_nsmul_id_eq_nsmul_id_comp]

/-- **The isogeny `T ⟶ H` commutes with endomorphisms**: if `β` on `H` is the restriction of `α`
on `T` (`β ≫ ι = ι ≫ α`, as for `CategoryTheory.LAdicTower.LESData.stableImageMap`), then
`α ≫ (T ⟶ H) = (T ⟶ H) ≫ β`. -/
theorem stableImageIsogeny_naturality (hS : ∀ n, ℓ ^ (n + 1) • 𝟙 (towerObj S n) = 0)
    (α : T ⟶ T) (β : D.stableImageTower ⟶ D.stableImageTower)
    (hβ : β ≫ D.stableImageι = D.stableImageι ≫ α) :
    α ≫ D.stableImageIsogeny hS = D.stableImageIsogeny hS ≫ β := by
  ext ⟨n⟩
  have hβn : β.app (op n) ≫ D.stableImageι.app (op n) =
      D.stableImageι.app (op n) ≫ α.app (op n) :=
    congrArg (fun t => NatTrans.app t (op n)) hβ
  rw [NatTrans.comp_app, NatTrans.comp_app, ← cancel_mono (D.stableImageι.app (op n)),
    Category.assoc, Category.assoc, hβn, stableImageIsogeny_app, stableImageIsogenyApp_ι_assoc,
    stableImageIsogenyApp_ι, comp_nsmul_id_eq_nsmul_id_comp]

end LESData

end CategoryTheory.LAdicTower
