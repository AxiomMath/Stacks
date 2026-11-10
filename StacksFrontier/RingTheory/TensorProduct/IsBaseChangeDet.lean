module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Bases after base change, read off a determinant

Let `M` be a free `R`-module with a finite basis `b`, and let `N` be a base change of `M` to an
`R`-algebra `S`, through `ε : M →ₗ[R] N`. A family `v` of elements of `M` indexed by the same set
becomes a basis of `N` after base change exactly when the determinant of `v` in the basis `b`
becomes a unit in `S`. Applied to the residue field at a prime and to a localization, this is the
form of Nakayama's lemma used to spread a basis of a fibre to a neighbourhood: a family whose
image in the fibre at `p` is a basis has determinant outside `p`, and so is a basis after
inverting that determinant.

## Main results

* `IsBaseChange.det_basis_comp`: the determinant of `ε ∘ v` in the base-changed basis is the
  image of the determinant of `v`.
* `IsBaseChange.isUnit_algebraMap_det_iff`: `ε ∘ v` is a basis exactly when the image of the
  determinant of `v` is a unit.
-/

@[expose] public section

open Module

namespace IsBaseChange

variable {R S M N ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [Fintype ι] [DecidableEq ι] {ε : M →ₗ[R] N} (hε : IsBaseChange S ε) (b : Basis ι R M)

/-- The determinant of a base-changed family in the base-changed basis is the image of the
determinant of the family. -/
theorem det_basis_comp (v : ι → M) :
    (hε.basis b).det (ε ∘ v) = algebraMap R S (b.det v) := by
  rw [Basis.det_apply, Basis.det_apply, RingHom.map_det]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, hε.basis_repr_comp_apply]

include hε in
/-- **A base-changed family is a basis exactly when the image of its determinant is a unit.** -/
theorem isUnit_algebraMap_det_iff (v : ι → M) :
    (LinearIndependent S (ε ∘ v) ∧ Submodule.span S (Set.range (ε ∘ v)) = ⊤) ↔
      IsUnit (algebraMap R S (b.det v)) := by
  rw [← hε.det_basis_comp b v]
  exact (hε.basis b).is_basis_iff_det

/-- **Base change in two steps.** If `N` is the base change of `M` along `φ : A → B` and `O` is
its base change along `χ = ι ∘ φ`, the factorization `N → O` of `M → O` is the base change of `N`
along `ι : B → T`. The module structures are those pulled back along the ring maps. -/
theorem exists_lift_isBaseChange {A B T M N O : Type*} [CommRing A] [CommRing B] [CommRing T]
    [Algebra B T] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] [AddCommGroup O]
    [Module T O] [Module B O] [IsScalarTower B T O] (φ : A →+* B) {χ : A →+* T}
    (hχ : (algebraMap B T).comp φ = χ)
    (f : letI := Module.compHom N φ; M →ₗ[A] N)
    (hf : letI := φ.toAlgebra; letI := Module.compHom N φ
      letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      IsBaseChange B f)
    (f' : letI := Module.compHom O χ; M →ₗ[A] O)
    (hf' : letI := χ.toAlgebra; letI := Module.compHom O χ
      letI : IsScalarTower A T O := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      IsBaseChange T f') :
    ∃ τ : N →ₗ[B] O, (∀ m, τ (f m) = f' m) ∧ IsBaseChange T τ := by
  subst hχ
  let := φ.toAlgebra
  let : Algebra A T := ((algebraMap B T).comp φ).toAlgebra
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let := Module.compHom N φ
  let : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module A O := Module.compHom O ((algebraMap B T).comp φ)
  let : IsScalarTower A T O := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : IsScalarTower A B O :=
    IsScalarTower.of_algebraMap_smul fun a o ↦ (algebraMap_smul T (φ a) o).symm
  exact ⟨hf.lift f', LinearMap.congr_fun (hf.lift_comp f'),
    IsBaseChange.of_comp hf (by rwa [hf.lift_comp f'])⟩

end IsBaseChange

namespace AlternatingMap

/-- **Cramer's rule** for an alternating map: replacing one entry of a family by a linear
combination of the family multiplies the value by the coefficient of that entry. -/
theorem map_update_sum_smul {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Fintype ι] [DecidableEq ι] (f : M [⋀^ι]→ₗ[R] N)
    (v : ι → M) (c : ι → R) (i : ι) :
    f (Function.update v i (∑ j, c j • v j)) = c i • f v := by
  rw [f.map_update_sum, Finset.sum_eq_single i]
  · rw [f.map_update_smul, Function.update_eq_self]
  · intro j _ hj
    rw [f.map_update_smul, f.map_update_self v (Ne.symm hj), smul_zero]
  · exact fun h ↦ absurd (Finset.mem_univ i) h

end AlternatingMap

namespace IsBaseChange

section Cramer

variable {R S M N ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [Fintype ι] [DecidableEq ι] {ε : M →ₗ[R] N} (hε : IsBaseChange S ε) (b : Basis ι R M)

include hε in
/-- **Cramer's rule after base change.** If the image of `x` expands in the base-changed family
`ε ∘ v` with coefficients `c`, replacing the `i₀`-th entry of `v` by `x` multiplies the
determinant by `c i₀`. -/
theorem det_update_eq_mul_det (v : ι → M) (x : M) (i₀ : ι) (c : ι → S)
    (hc : ε x = ∑ i, c i • (ε ∘ v) i) :
    algebraMap R S (b.det (Function.update v i₀ x)) = c i₀ * algebraMap R S (b.det v) := by
  rw [← hε.det_basis_comp b, ← hε.det_basis_comp b, Function.comp_update, hc,
    AlternatingMap.map_update_sum_smul, smul_eq_mul]

include hε in
/-- **Coordinates and Cramer's rule after base change.** If the base-changed family `ε ∘ v` is a
basis of `N`, the image of `x` expands in it, and replacing the `i₀`-th entry of `v` by `x`
multiplies the determinant by the coefficient at `i₀`. -/
theorem exists_repr_det_update (v : ι → M) (hli : LinearIndependent S (ε ∘ v))
    (hsp : Submodule.span S (Set.range (ε ∘ v)) = ⊤) (x : M) (i₀ : ι) :
    ∃ c : ι → S, ε x = ∑ i, c i • (ε ∘ v) i ∧
      algebraMap R S (b.det (Function.update v i₀ x)) = c i₀ * algebraMap R S (b.det v) := by
  have h : ε x = ∑ i, (Basis.mk hli hsp.ge).repr (ε x) i • (ε ∘ v) i := by
    simpa using ((Basis.mk hli hsp.ge).sum_repr (ε x)).symm
  exact ⟨_, h, hε.det_update_eq_mul_det b v x i₀ _ h⟩

end Cramer

/-- **Spreading out a basis with a non-degenerate expansion from a fibre.** Let `N₁` be a free
base change of an `A`-module `M` along `φ₁ : A → B₁`, and `O` its base change to a field `κ`
along `ι₁ ∘ φ₁`. If a family `w` of `M` becomes a basis of `O` and the expansion of the image of
`z` in it has a nonzero coefficient at `i₀`, there are `d, e ∈ B₁` with nonzero images in `κ` such
that over every `B₁`-algebra `B` in which `d` and `e` become units, the images of `w` are a basis
of the base change of `M` and the coefficient at `i₀` of `z` is a unit. -/
theorem exists_det_spread {A B₁ κ M N₁ O : Type*} [CommRing A] [CommRing B₁] [Field κ]
    [AddCommGroup M] [Module A M] [AddCommGroup N₁] [Module B₁ N₁] [AddCommGroup O] [Module κ O]
    {n : ℕ} (φ₁ : A →+* B₁) (ι₁ : B₁ →+* κ) {χ : A →+* κ} (hχ : ι₁.comp φ₁ = χ)
    (ρ₁ : letI := Module.compHom N₁ φ₁; M →ₗ[A] N₁)
    (hρ₁ : letI := φ₁.toAlgebra; letI := Module.compHom N₁ φ₁
      letI : IsScalarTower A B₁ N₁ := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      IsBaseChange B₁ ρ₁)
    {ι : Type*} [Finite ι] (b₁ : Basis ι B₁ N₁)
    (ρκ : letI := Module.compHom O χ; M →ₗ[A] O)
    (hρκ : letI := χ.toAlgebra; letI := Module.compHom O χ
      letI : IsScalarTower A κ O := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      IsBaseChange κ ρκ)
    (w : Fin n → M) (z : M) (i₀ : Fin n)
    (hli : LinearIndependent κ fun i => ρκ (w i))
    (hsp : Submodule.span κ (Set.range fun i => ρκ (w i)) = ⊤)
    (hz : ∀ c : Fin n → κ, ρκ z = ∑ i, c i • ρκ (w i) → c i₀ ≠ 0) :
    ∃ d e : B₁, ι₁ d ≠ 0 ∧ ι₁ e ≠ 0 ∧
      ∀ {B NB : Type*} [CommRing B] [AddCommGroup NB] [Module B NB] (ψ : B₁ →+* B)
        {φ : A →+* B} (_ : ψ.comp φ₁ = φ) (ρB : letI := Module.compHom NB φ; M →ₗ[A] NB),
        (letI := φ.toAlgebra; letI := Module.compHom NB φ
          letI : IsScalarTower A B NB := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
          IsBaseChange B ρB) →
        IsUnit (ψ d) → IsUnit (ψ e) →
        ∃ c : Fin n → B, IsUnit (c i₀) ∧ ρB z = ∑ i, c i • ρB (w i) := by
  have := Fintype.ofFinite ι
  subst hχ
  let : Algebra B₁ κ := ι₁.toAlgebra
  let : Module B₁ O := Module.compHom O ι₁
  let : IsScalarTower B₁ κ O := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  obtain ⟨τκ, hτκ, hbcτκ⟩ := exists_lift_isBaseChange (O := O) φ₁ rfl ρ₁ hρ₁ ρκ hρκ
  have hcard : Fintype.card ι = n := by
    rw [← Module.finrank_eq_card_basis (hbcτκ.basis b₁),
      Module.finrank_eq_card_basis (Basis.mk hli hsp.ge), Fintype.card_fin]
  classical
  replace b₁ := b₁.reindex (Fintype.equivFinOfCardEq hcard)
  set v : Fin n → N₁ := fun i => ρ₁ (w i)
  have hκw : τκ ∘ v = fun i => ρκ (w i) := funext fun i => hτκ _
  rw [← hκw] at hli hsp
  have hd := (hbcτκ.isUnit_algebraMap_det_iff b₁ v).1 ⟨hli, hsp⟩
  obtain ⟨c, hc, hdet⟩ := hbcτκ.exists_repr_det_update b₁ v hli hsp (ρ₁ z) i₀
  rw [hκw, hτκ] at hc
  refine ⟨b₁.det v, b₁.det (Function.update v i₀ (ρ₁ z)), hd.ne_zero, ?_, ?_⟩
  · change algebraMap B₁ κ _ ≠ 0
    rw [hdet]
    exact mul_ne_zero (hz c hc) hd.ne_zero
  · intro B NB _ _ _ ψ φ hψ ρB hρB hψd hψe
    subst hψ
    let : Algebra B₁ B := ψ.toAlgebra
    let : Module B₁ NB := Module.compHom NB ψ
    let : IsScalarTower B₁ B NB := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    obtain ⟨τB, hτB, hbcτB⟩ := exists_lift_isBaseChange (O := NB) φ₁ rfl ρ₁ hρ₁ ρB hρB
    have hBw : τB ∘ v = fun i => ρB (w i) := funext fun i => hτB _
    obtain ⟨hliB, hspB⟩ := (hbcτB.isUnit_algebraMap_det_iff b₁ v).2 hψd
    obtain ⟨c, hc, hdet⟩ := hbcτB.exists_repr_det_update b₁ v hliB hspB (ρ₁ z) i₀
    rw [hBw, hτB] at hc
    have he : ψ (b₁.det (Function.update v i₀ (ρ₁ z))) = c i₀ * ψ (b₁.det v) := hdet
    rw [he] at hψe
    exact ⟨c, isUnit_of_mul_isUnit_left hψe, hc⟩

end IsBaseChange
