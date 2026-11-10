module

public import Mathlib.RingTheory.TensorProduct.Free
public import StacksFrontier.AlgebraicGeometry.Duality.FunnyMap
public import StacksCore.Tactic.StacksAttribute

/-!
# Naturality of the canonical map of a two-term diagram

The canonical exterior-power maps `cᵖ : ⋀ᵖ(L / d(M⁻¹)) → ⋀ᵖK ⊗ det(M⁻¹ → M⁰)` attached to a
short exact sequence `0 → K → L → M⁰ → 0` together with a compatible two-term complex
`M⁻¹ → M⁰` are natural for morphisms of such diagrams: given a second diagram over a ring
extension `R₁ → R₂` and semilinear maps between the two, the evident square of exterior powers
commutes. The vertical maps on exterior powers are specified by their action on exterior
generators, and the maps on the two terms of the complex are assumed to become isomorphisms after
extension of scalars.

## Main results

* `Stacks.DeRham.funnyMap_naturality` is the naturality square.

## References

* [Stacks Project, Tag 0H9F](https://stacks.math.columbia.edu/tag/0H9F)
-/

@[expose] public section

namespace Stacks.DeRham

open scoped TensorProduct

universe u₁ u₂

variable (R₁ : Type u₁) (R₂ : Type u₂) [CommRing R₁] [CommRing R₂] [Algebra R₁ R₂]

/-- The canonical maps `Stacks.DeRham.funnyMap` are natural for compatible morphisms of two-term
diagrams, provided the two terms of the complex are carried isomorphically to their scalar
extensions. -/
@[stacks 0H9F]
theorem funnyMap_naturality
    {K₁ L₁ N₁ Z₁ K₂ L₂ N₂ Z₂ : Type*}
    [AddCommGroup K₁] [Module R₁ K₁]
    [AddCommGroup L₁] [Module R₁ L₁]
    [AddCommGroup N₁] [Module R₁ N₁]
    [AddCommGroup Z₁] [Module R₁ Z₁]
    [AddCommGroup K₂] [Module R₂ K₂]
    [AddCommGroup L₂] [Module R₂ L₂]
    [AddCommGroup N₂] [Module R₂ N₂]
    [AddCommGroup Z₂] [Module R₂ Z₂]
    (n p : ℕ)
    (i₁ : K₁ →ₗ[R₁] L₁) (π₁ : L₁ →ₗ[R₁] Z₁)
    (d₁ : N₁ →ₗ[R₁] L₁) (dM₁ : N₁ →ₗ[R₁] Z₁)
    (i₂ : K₂ →ₗ[R₂] L₂) (π₂ : L₂ →ₗ[R₂] Z₂)
    (d₂ : N₂ →ₗ[R₂] L₂) (dM₂ : N₂ →ₗ[R₂] Z₂)
    (hi₁ : Function.Injective i₁) (hexact₁ : Function.Exact i₁ π₁)
    (hπ₁ : Function.Surjective π₁) (hsquare₁ : π₁.comp d₁ = dM₁)
    (hi₂ : Function.Injective i₂) (hexact₂ : Function.Exact i₂ π₂)
    (hπ₂ : Function.Surjective π₂) (hsquare₂ : π₂.comp d₂ = dM₂)
    (hZ₁ : Nonempty (Module.Basis (Fin n) R₁ Z₁))
    (hN₁ : Nonempty (Module.Basis (Fin n) R₁ N₁))
    (hZ₂ : Nonempty (Module.Basis (Fin n) R₂ Z₂))
    (hN₂ : Nonempty (Module.Basis (Fin n) R₂ N₂))
    (k : K₁ →ₛₗ[algebraMap R₁ R₂] K₂)
    (l : L₁ →ₛₗ[algebraMap R₁ R₂] L₂)
    (neg : N₁ →ₛₗ[algebraMap R₁ R₂] N₂)
    (zero : Z₁ →ₛₗ[algebraMap R₁ R₂] Z₂)
    (hki : ∀ x, l (i₁ x) = i₂ (k x))
    (hlπ : ∀ x, zero (π₁ x) = π₂ (l x))
    (hnd : ∀ x, l (d₁ x) = d₂ (neg x))
    (negBaseChange : TensorProduct R₁ R₂ N₁ ≃ₗ[R₂] N₂)
    (zeroBaseChange : TensorProduct R₁ R₂ Z₁ ≃ₗ[R₂] Z₂)
    (hnegBaseChange : ∀ x r, negBaseChange (r ⊗ₜ[R₁] x) = r • neg x)
    (hzeroBaseChange : ∀ x r, zeroBaseChange (r ⊗ₜ[R₁] x) = r • zero x)
    (onH : (⋀[R₁]^p (L₁ ⧸ LinearMap.range d₁)) →ₛₗ[algebraMap R₁ R₂]
      (⋀[R₂]^p (L₂ ⧸ LinearMap.range d₂)))
    (onK : (⋀[R₁]^p K₁) →ₛₗ[algebraMap R₁ R₂] (⋀[R₂]^p K₂))
    (onNegTop : (⋀[R₁]^n N₁) →ₛₗ[algebraMap R₁ R₂] (⋀[R₂]^n N₂))
    (onZeroTop : (⋀[R₁]^n Z₁) →ₛₗ[algebraMap R₁ R₂] (⋀[R₂]^n Z₂))
    (onNegDual : Module.Dual R₁ (⋀[R₁]^n N₁) →ₛₗ[algebraMap R₁ R₂]
      Module.Dual R₂ (⋀[R₂]^n N₂))
    (onDet : twoTermDeterminant R₁ n N₁ Z₁ →ₛₗ[algebraMap R₁ R₂]
      twoTermDeterminant R₂ n N₂ Z₂)
    (honH : ∀ x : Fin p → L₁,
      onH (exteriorPower.ιMulti R₁ p (fun j ↦ (LinearMap.range d₁).mkQ (x j))) =
        exteriorPower.ιMulti R₂ p (fun j ↦ (LinearMap.range d₂).mkQ (l (x j))))
    (honK : ∀ x : Fin p → K₁,
      onK (exteriorPower.ιMulti R₁ p x) =
        exteriorPower.ιMulti R₂ p (fun j ↦ k (x j)))
    (honNegTop : ∀ x : Fin n → N₁,
      onNegTop (exteriorPower.ιMulti R₁ n x) =
        exteriorPower.ιMulti R₂ n (fun j ↦ neg (x j)))
    (honZeroTop : ∀ x : Fin n → Z₁,
      onZeroTop (exteriorPower.ιMulti R₁ n x) =
        exteriorPower.ιMulti R₂ n (fun j ↦ zero (x j)))
    (honNegDual : ∀ (φ : Module.Dual R₁ (⋀[R₁]^n N₁)) (x : ⋀[R₁]^n N₁),
      onNegDual φ (onNegTop x) = algebraMap R₁ R₂ (φ x))
    (honDet : ∀ (z : ⋀[R₁]^n Z₁) (φ : Module.Dual R₁ (⋀[R₁]^n N₁)),
      onDet (z ⊗ₜ[R₁] φ) = onZeroTop z ⊗ₜ[R₂] onNegDual φ) :
    (TensorProduct.map onK onDet).comp
        (funnyMap n i₁ π₁ d₁ dM₁ hi₁ hexact₁ hπ₁ hsquare₁ hZ₁ hN₁ p) =
      (funnyMap n i₂ π₂ d₂ dM₂ hi₂ hexact₂ hπ₂ hsquare₂ hZ₂ hN₂ p).comp onH := by
  classical
  let bN₁ : Module.Basis (Fin n) R₁ N₁ := Classical.choice hN₁
  let bN₂ : Module.Basis (Fin n) R₂ N₂ :=
    (Algebra.TensorProduct.basis R₂ bN₁).map negBaseChange
  have hbN₂ (j : Fin n) : bN₂ j = neg (bN₁ j) := by
    simp [bN₂, hnegBaseChange]
  let _ : Module.Free R₁ Z₁ := Module.Free.of_basis (Classical.choice hZ₁)
  let _ : Module R₁ K₂ := Module.compHom K₂ (algebraMap R₁ R₂)
  let _ : IsScalarTower R₁ R₂ K₂ := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  obtain ⟨r₁, hr₁⟩ := exists_retraction n i₁ π₁ hi₁ hexact₁ hπ₁ hZ₁
  obtain ⟨r₂₀, hr₂₀⟩ := exists_retraction n i₂ π₂ hi₂ hexact₂ hπ₂ hZ₂
  let q : L₁ →ₗ[R₁] K₂ :=
    { toFun := fun x => r₂₀ (l x) - k (r₁ x)
      map_add' := by
        intro x y; simp only [map_add]; abel
      map_smul' := by
        intro a x
        change r₂₀ (l (a • x)) - k (r₁ (a • x)) =
          (algebraMap R₁ R₂ a) • (r₂₀ (l x) - k (r₁ (x)))
        rw [map_smulₛₗ, LinearMap.map_smul_of_tower, LinearMap.map_smul,
          map_smulₛₗ, smul_sub] }
  have h₁ (x : K₁) : r₁ (i₁ x) = x := LinearMap.congr_fun hr₁ x
  have h₂ (y : K₂) : r₂₀ (i₂ y) = y := LinearMap.congr_fun hr₂₀ y
  have hqi (x : K₁) : q (i₁ x) = 0 := by
    change r₂₀ (l (i₁ x)) - k (r₁ (i₁ x)) = 0
    simp [hki x, h₂, h₁]
  obtain ⟨s, hs⟩ := π₁.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ₁)
  let t : Z₁ →ₗ[R₁] K₂ := q.comp s
  let t₂ : Z₂ →ₗ[R₂] K₂ :=
    (t.liftBaseChange R₂).comp zeroBaseChange.symm.toLinearMap
  have ht₂ (z : Z₁) : t₂ (zero z) = t z := by
    have hz : zeroBaseChange.symm (zero z) = (1 : R₂) ⊗ₜ[R₁] z := by
      apply zeroBaseChange.injective
      simp [hzeroBaseChange]
    change (t.liftBaseChange R₂) (zeroBaseChange.symm (zero z)) = t z
    rw [hz, LinearMap.liftBaseChange_one_tmul]
  have hqfactor (x : L₁) : q x = t (π₁ x) := by
    have hss (z : Z₁) : π₁ (s z) = z := LinearMap.congr_fun hs z
    have hπx : π₁ (x - s (π₁ x)) = 0 := by simp [map_sub, hss]
    obtain ⟨y, hy⟩ := (hexact₁ (x - s (π₁ x))).mp hπx
    have hx : x = s (π₁ x) + i₁ y := by rw [hy]; abel
    rw [hx]
    simp [map_add, hss, hexact₁.apply_apply_eq_zero, hqi, t, LinearMap.comp_apply]
  let r₂ : L₂ →ₗ[R₂] K₂ := r₂₀ - t₂.comp π₂
  have hr₂ : r₂.comp i₂ = LinearMap.id := by
    ext x
    simp [r₂, h₂, hexact₂.apply_apply_eq_zero]
  have hrl (x : L₁) : r₂ (l x) = k (r₁ x) := by
    have hfactor : r₂₀ (l x) - k (r₁ x) = t (π₁ x) := hqfactor x
    change r₂₀ (l x) - t₂ (π₂ (l x)) = k (r₁ x)
    rw [← hlπ x, ht₂, ← hfactor]
    abel
  have htop : onNegTop (exteriorPower.ιMulti R₁ n (fun j => bN₁ j)) =
      exteriorPower.ιMulti R₂ n (fun j => bN₂ j) := by
    simpa [hbN₂] using honNegTop (fun j => bN₁ j)
  have hdual : onNegDual (basisTopDual bN₁) = basisTopDual bN₂ := by
    apply (bN₂.exteriorPower n).ext
    intro s'
    have hs' : (s' : Finset (Fin n)) = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        (by rw [Finset.card_univ, Fintype.card_fin]
            exact (Set.powersetCard.card_eq s').symm.le)
    have horder : Finset.orderEmbOfFin (Finset.univ : Finset (Fin n)) (by simp) =
        OrderEmbedding.ofStrictMono (id : Fin n → Fin n) strictMono_id := by
      symm; exact Finset.orderEmbOfFin_unique' (by simp) (by intro j; simp)
    have heval : (bN₂.exteriorPower n) s' =
        exteriorPower.ιMulti R₂ n (fun j => bN₂ j) := by
      have hsobj : s' = (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin n) n) :=
        Subtype.ext hs'
      rw [hsobj]
      simp [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
        Set.powersetCard.ofFinEmbEquiv_symm_apply, horder]
    rw [heval]
    have h := honNegDual (basisTopDual bN₁) (exteriorPower.ιMulti R₁ n bN₁)
    rw [htop, basisTopDual_apply, map_one] at h
    simpa [basisTopDual_apply] using h
  have hproj (v : Fin (p + n) → L₁) :
      (TensorProduct.map onK onZeroTop)
          (topWedgeProjection p n r₁ π₁ (exteriorPower.ιMulti R₁ (p + n) v)) =
        topWedgeProjection p n r₂ π₂
          (exteriorPower.ιMulti R₂ (p + n) (fun j => l (v j))) := by
    rw [topWedgeProjection_apply_ιMulti, topWedgeProjection_apply_ιMulti,
      AlternatingMap.domCoprod_apply, AlternatingMap.domCoprod_apply,
      _root_.sum_apply, _root_.sum_apply, map_sum]
    apply Finset.sum_congr rfl
    intro σ _
    induction σ using Quotient.inductionOn' with
    | _ σ =>
        rw [AlternatingMap.domCoprod.summand_mk'',
          AlternatingMap.domCoprod.summand_mk'']
        simp [MultilinearMap.domCoprod_apply, hrl, hlπ, honK, honZeroTop]
  have hassoc (u : (⋀[R₁]^p K₁) ⊗[R₁] (⋀[R₁]^n Z₁)) :
      (TensorProduct.map onK onDet)
          (TensorProduct.assoc R₁ (⋀[R₁]^p K₁) (⋀[R₁]^n Z₁)
            (Module.Dual R₁ (⋀[R₁]^n N₁)) (u ⊗ₜ[R₁] basisTopDual bN₁)) =
        TensorProduct.assoc R₂ (⋀[R₂]^p K₂) (⋀[R₂]^n Z₂)
          (Module.Dual R₂ (⋀[R₂]^n N₂))
          ((TensorProduct.map onK onZeroTop u) ⊗ₜ[R₂]
            onNegDual (basisTopDual bN₁)) := by
    induction u using TensorProduct.inductionOn with
    | tmul z w => simp [TensorProduct.assoc_tmul, honDet]
    | add x y hx hy =>
        simp only [TensorProduct.add_tmul, map_add]; rw [hx, hy]
  have htuple (v : Fin p → L₁) :
      (fun j : Fin (p + n) => l (Fin.append v (d₁ ∘ bN₁) j)) =
        Fin.append (fun j => l (v j)) (d₂ ∘ bN₂) := by
    funext j; cases j using Fin.addCases <;> simp [hnd, hbN₂]
  have hgen (v : Fin p → L₁) :
      (TensorProduct.map onK onDet)
          (funnyMapLift p n r₁ π₁ d₁ bN₁ (exteriorPower.ιMulti R₁ p v)) =
        funnyMapLift p n r₂ π₂ d₂ bN₂
          (exteriorPower.ιMulti R₂ p (fun j => l (v j))) := by
    rw [funnyMapLift_apply, funnyMapLift_apply, exteriorPower.wedgeMul_ιMulti,
      exteriorPower.wedgeMul_ιMulti, hassoc, hproj, htuple, hdual]
  apply LinearMap.ext_on (exteriorPower.ιMulti_span R₁ p (L₁ ⧸ LinearMap.range d₁))
  rintro _ ⟨v, rfl⟩
  choose vL hvL using fun j => (LinearMap.range d₁).mkQ_surjective (v j)
  rw [← funext hvL]
  change TensorProduct.map onK onDet
      (funnyMap n i₁ π₁ d₁ dM₁ hi₁ hexact₁ hπ₁ hsquare₁ hZ₁ hN₁ p
        (exteriorPower.ιMulti R₁ p (fun j => (LinearMap.range d₁).mkQ (vL j)))) =
    funnyMap n i₂ π₂ d₂ dM₂ hi₂ hexact₂ hπ₂ hsquare₂ hZ₂ hN₂ p
      (onH (exteriorPower.ιMulti R₁ p (fun j => (LinearMap.range d₁).mkQ (vL j))))
  rw [funnyMap_apply_ιMulti n p i₁ π₁ d₁ dM₁ hi₁ hexact₁ hπ₁ hsquare₁ hZ₁ hN₁ r₁ hr₁ bN₁ vL,
    honH vL, funnyMap_apply_ιMulti n p i₂ π₂ d₂ dM₂ hi₂ hexact₂ hπ₂ hsquare₂ hZ₂ hN₂ r₂ hr₂ bN₂
      (fun j => l (vL j))]
  exact hgen vL

end Stacks.DeRham
