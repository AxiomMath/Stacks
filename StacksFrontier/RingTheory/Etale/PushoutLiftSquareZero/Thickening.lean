module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Etale.Pi
public import StacksFrontier.RingTheory.Etale.Lifting
public import StacksFrontier.RingTheory.Nilpotent.Descent
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex

/-!
# Square-zero ideals and base change

Let `A` be a commutative ring and `J ⊆ A` an ideal with `J² = 0`. For an `A`-algebra `T`, the map
`J ⊗[A] T → T`, `j ⊗ t ↦ j t`, has image `JT`, and it factors through `J ⊗[A] (T ⧸ JT)` because
`J` kills `JT`. When `T` is flat over `A` the map `J ⊗[A] T → T` is injective, so `JT` is
`J ⊗[A] (T ⧸ JT)`.

These are the identifications by which the general case of Stacks 0ALT reads the `J`-parts of
the rings it glues as base changes of a single module over the reduction. This file also records
the rigidity of square-zero thickenings, étaleness across them, and étale lifts of étale
`A ⧸ J`-algebras (Stacks 04D1).

## Main results

* `SquareZero.tensorMul`: the map `J ⊗[A] T → T`.
* `SquareZero.range_tensorMul`: its image is `JT`.
* `SquareZero.injective_tensorMul_of_flat`: it is injective for `T` flat over `A`.
* `SquareZero.bijective_of_pushOf`, `SquareZero.etale_of_pushOf`: rigidity of square-zero
  thickenings, and étaleness across them.
* `SquareZero.EtaleLiftData`, `SquareZero.nonempty_etaleLiftData`: étale lifts over `A` of étale
  `A ⧸ J`-algebras.
-/

@[expose] public noncomputable section

open TensorProduct

universe u v

namespace SquareZero

variable {A : Type u} [CommRing A] (J : Ideal A) (T : Type v) [CommRing T] [Algebra A T]

/-- The multiplication map `J ⊗[A] T → T`, `j ⊗ t ↦ j t`. -/
def tensorMul : J ⊗[A] T →ₗ[A] T :=
  TensorProduct.lift ((LinearMap.mul A T).compl₁₂ ((Algebra.linearMap A T).comp J.subtype)
    LinearMap.id)

/-- On pure tensors, `tensorMul` is multiplication: `j ⊗ t ↦ j t`. -/
@[simp]
theorem tensorMul_tmul (j : J) (t : T) :
    tensorMul J T (j ⊗ₜ t) = algebraMap A T j * t := rfl

/-- The image of `J ⊗[A] T → T` is the extended ideal `JT`. -/
theorem range_tensorMul :
    (LinearMap.range (tensorMul J T) : Set T) = J.map (algebraMap A T) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul j t =>
      rw [tensorMul_tmul, mul_comm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ j.2)
    | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  · intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨j, hj, rfl⟩ := ht
      exact ⟨⟨j, hj⟩ ⊗ₜ 1, by simp⟩
    | zero => exact ⟨0, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | smul s x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      have key : ∀ b : J ⊗[A] T,
          tensorMul J T (((LinearMap.mulLeft A s).lTensor J) b) = s • tensorMul J T b := by
        intro b
        induction b using TensorProduct.induction_on with
        | zero => simp
        | tmul j t =>
          simp only [LinearMap.lTensor_tmul, LinearMap.mulLeft_apply, tensorMul_tmul, smul_eq_mul]
          ring
        | add a b ha hb => simp only [map_add, ha, hb, smul_add]
      exact ⟨((LinearMap.mulLeft A s).lTensor J) a, key a⟩

/-- For `T` flat over `A`, the map `J ⊗[A] T → T` is injective. -/
theorem injective_tensorMul_of_flat [Module.Flat A T] : Function.Injective (tensorMul J T) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := T) J.subtype
    Subtype.val_injective
  have heq : tensorMul J T = (TensorProduct.lid A T).toLinearMap ∘ₗ J.subtype.rTensor T := by
    apply TensorProduct.ext'
    intro j t
    simp [Algebra.smul_def]
  rw [heq]
  exact (TensorProduct.lid A T).injective.comp h

section Push

variable {A : Type u} [CommRing A] (J : Ideal A) {T T₀ : Type v} [CommRing T] [CommRing T₀]
  [Algebra A T] [Algebra A T₀]

/-- Tensoring a reduction with kernel `JT` with `J` is bijective, `J` being square zero. -/
theorem bijective_rTensor_of_ker_eq (hJ : J ^ 2 = ⊥) (π : T →ₐ[A] T₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : T →+* T₀) = J.map (algebraMap A T)) :
    Function.Bijective (π.toLinearMap.rTensor J) := by
  refine ⟨?_, LinearMap.rTensor_surjective _ hπ⟩
  -- the kernel `JT ⊗ J` maps to zero in `T ⊗ J`
  have hex := rTensor_exact J (LinearMap.exact_subtype_ker_map π.toLinearMap) hπ
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro w hw
  obtain ⟨v, rfl⟩ := (hex w).mp hw
  rw [Submodule.mem_bot]
  clear hw
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul k j =>
    have hk : (k : T) ∈ J.map (algebraMap A T) := by
      rw [← hker]; exact k.2
    have key : ∀ t ∈ J.map (algebraMap A T), t ⊗ₜ[A] j = 0 := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨a, ha, rfl⟩ := ht
        rw [← mul_one (algebraMap A T a), ← Algebra.smul_def, TensorProduct.smul_tmul]
        have : a • j = 0 := by
          apply Subtype.ext
          have hmem : a * (j : A) ∈ J ^ 2 := by rw [sq]; exact Ideal.mul_mem_mul ha j.2
          rw [hJ] at hmem
          simpa using hmem
        rw [this, TensorProduct.tmul_zero]
      | zero => simp
      | add x y _ _ hx hy => rw [TensorProduct.add_tmul, hx, hy, add_zero]
      | smul t x _ hx =>
        rw [smul_eq_mul, show t * x = t • x from rfl, ← TensorProduct.smul_tmul', hx, smul_zero]
    rw [LinearMap.rTensor_tmul]
    exact key _ hk
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

/-- The multiplication map `T ⊗[A] J → T`, `t ⊗ j ↦ j t`, in the order with `T` on the left. -/
noncomputable def mulTensor : T ⊗[A] J →ₗ[A] T :=
  tensorMul J T ∘ₗ (TensorProduct.comm A T J).toLinearMap

/-- On pure tensors, `mulTensor` is multiplication: `t ⊗ j ↦ j t`. -/
@[simp]
theorem mulTensor_tmul (t : T) (j : J) : mulTensor J (t ⊗ₜ j) = algebraMap A T j * t := rfl

/-- **The `J`-part of `T` as a tensor model over the reduction.** For `π : T ↠ T₀` with kernel
`JT` and `J² = 0`, the map `T₀ ⊗[A] J → T`, `π(t) ⊗ j ↦ j t`. -/
noncomputable def pushOf (hJ : J ^ 2 = ⊥) (π : T →ₐ[A] T₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : T →+* T₀) = J.map (algebraMap A T)) : T₀ ⊗[A] J →ₗ[A] T :=
  mulTensor J ∘ₗ
    (LinearEquiv.ofBijective _ (bijective_rTensor_of_ker_eq J hJ π hπ hker)).symm.toLinearMap

variable (hJ : J ^ 2 = ⊥) (π : T →ₐ[A] T₀) (hπ : Function.Surjective π)
  (hker : RingHom.ker (π : T →+* T₀) = J.map (algebraMap A T))

/-- On pure tensors, `pushOf` sends `π(t) ⊗ j` to `j t`. -/
theorem pushOf_tmul (t : T) (j : J) :
    pushOf J hJ π hπ hker (π t ⊗ₜ j) = algebraMap A T j * t := by
  have h : (LinearEquiv.ofBijective _ (bijective_rTensor_of_ker_eq J hJ π hπ hker)).symm
      (π t ⊗ₜ j) = t ⊗ₜ j := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp only [pushOf, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h,
    mulTensor_tmul]

/-- `pushOf` composed with `π ⊗ J` is the multiplication map `T ⊗[A] J → T`. -/
theorem pushOf_rTensor (x : T ⊗[A] J) :
    pushOf J hJ π hπ hker (π.toLinearMap.rTensor J x) = mulTensor J x := by
  simp only [pushOf, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [show π.toLinearMap.rTensor J x =
      LinearEquiv.ofBijective _ (bijective_rTensor_of_ker_eq J hJ π hπ hker) x from rfl,
    LinearEquiv.symm_apply_apply]

/-- The image of `pushOf` is the extended ideal `JT`. -/
theorem range_pushOf :
    (LinearMap.range (pushOf J hJ π hπ hker) : Set T) = J.map (algebraMap A T) := by
  have hr : LinearMap.range (pushOf J hJ π hπ hker) = LinearMap.range (mulTensor J) := by
    simp only [pushOf, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  have hm : LinearMap.range (mulTensor J) = LinearMap.range (tensorMul J T) := by
    simp only [mulTensor, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  rw [hr, hm, range_tensorMul]

/-- `pushOf` is injective when `T` is flat over `A`. -/
theorem injective_pushOf [Module.Flat A T] : Function.Injective (pushOf J hJ π hπ hker) := by
  simp only [pushOf, mulTensor, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (injective_tensorMul_of_flat J T).comp
    ((TensorProduct.comm A T J).injective.comp (LinearEquiv.injective _))

/-- **Naturality of the push.** An `A`-algebra map `φ : T → T'` compatible with reductions
`φ₀ : T₀ → T'₀` intertwines the two pushes. -/
theorem pushOf_naturality {T' T'₀ : Type v} [CommRing T'] [CommRing T'₀] [Algebra A T']
    [Algebra A T'₀] (π' : T' →ₐ[A] T'₀) (hπ' : Function.Surjective π')
    (hker' : RingHom.ker (π' : T' →+* T'₀) = J.map (algebraMap A T'))
    (φ : T →ₐ[A] T') (φ₀ : T₀ →ₐ[A] T'₀) (hφ : ∀ t, π' (φ t) = φ₀ (π t)) (x : T₀ ⊗[A] J) :
    pushOf J hJ π' hπ' hker' (φ₀.toLinearMap.rTensor J x) = φ (pushOf J hJ π hπ hker x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t₀ j =>
    obtain ⟨t, rfl⟩ := hπ t₀
    rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, ← hφ, pushOf_tmul, pushOf_tmul,
      map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Rigidity of square-zero thickenings.** Let `πE : E ↠ T₀` and `πT : T ↠ T₀` be reductions
with kernels `JE` and `JT`, and let `φ : E → T` be an `A`-algebra map over `T₀`. Then `φ` is
surjective, and it is injective as soon as every element of `T₀ ⊗[A] J` killed by the push into
`T` is killed by the push into `E`. -/
theorem bijective_of_pushOf {E : Type v} [CommRing E] [Algebra A E] (πE : E →ₐ[A] T₀)
    (hπE : Function.Surjective πE) (hkerE : RingHom.ker (πE : E →+* T₀) = J.map (algebraMap A E))
    (φ : E →ₐ[A] T) (hφ : ∀ e, π (φ e) = πE e)
    (h : ∀ w, pushOf J hJ π hπ hker w = 0 → pushOf J hJ πE hπE hkerE w = 0) :
    Function.Bijective φ := by
  have hnat : ∀ w, pushOf J hJ π hπ hker w = φ (pushOf J hJ πE hπE hkerE w) := fun w ↦ by
    have := pushOf_naturality J hJ πE hπE hkerE π hπ hker φ (AlgHom.id A T₀) hφ w
    rwa [AlgHom.toLinearMap_id, LinearMap.rTensor_id, LinearMap.id_apply] at this
  have hrange : ∀ {S : Type v} [CommRing S] [Algebra A S] (πS : S →ₐ[A] T₀)
      (hπS : Function.Surjective πS) (hkerS : RingHom.ker (πS : S →+* T₀) = J.map (algebraMap A S))
      (x : S), πS x = 0 → ∃ w, pushOf J hJ πS hπS hkerS w = x := by
    intro S _ _ πS hπS hkerS x hx
    have hmem : x ∈ (LinearMap.range (pushOf J hJ πS hπS hkerS) : Set S) := by
      rw [range_pushOf, SetLike.mem_coe, ← hkerS, RingHom.mem_ker]
      exact hx
    exact hmem
  refine ⟨fun x y hxy ↦ ?_, fun t ↦ ?_⟩
  · rw [← sub_eq_zero] at hxy ⊢
    rw [← map_sub] at hxy
    obtain ⟨w, hw⟩ := hrange πE hπE hkerE (x - y) (by rw [← hφ, hxy, map_zero])
    rw [← hw]
    apply h
    rw [hnat, hw, hxy]
  · obtain ⟨e, he⟩ := hπE (π t)
    obtain ⟨w, hw⟩ := hrange π hπ hker (t - φ e) (by rw [map_sub, hφ, he, sub_self])
    refine ⟨e + pushOf J hJ πE hπE hkerE w, ?_⟩
    rw [map_add, ← hnat, hw, add_sub_cancel]

end Push

section EtaleAway

variable {A₀ : Type u} {B₀ : Type v} [CommRing A₀] [CommRing B₀] [Algebra A₀ B₀]

/-- If `B₀` is étale over `A₀` at every prime lying over the complement of `V(I₀)`, then inverting
the image of an element of `I₀` gives an étale `A₀`-algebra. -/
theorem etale_localizationAway_of_isEtaleAt [Algebra.FinitePresentation A₀ B₀] (I₀ : Ideal A₀)
    (hB : ∀ q : Ideal B₀, ∀ _ : q.IsPrime, ¬ I₀ ≤ q.comap (algebraMap A₀ B₀) →
      Algebra.IsEtaleAt A₀ q)
    {a : A₀} (ha : a ∈ I₀) : Algebra.Etale A₀ (Localization.Away (algebraMap A₀ B₀ a)) := by
  rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale]
  intro p hp
  exact hB p.asIdeal p.isPrime fun hle ↦ hp (hle ha)

end EtaleAway

section EtaleLift

variable {A : Type u} [CommRing A] (J : Ideal A) (P : Type u) [CommRing P] [Algebra A P]
  [Algebra (A ⧸ J) P] [IsScalarTower A (A ⧸ J) P] [Algebra.Etale (A ⧸ J) P]

/-- An étale `A`-algebra lifting an étale `A ⧸ J`-algebra `P`: a surjection onto `P` whose kernel
is `J` times the algebra. Stacks 04D1 says one exists. -/
structure EtaleLiftData where
  /-- The lifting algebra. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra A carrier]
  /-- The lifting algebra is étale over `A`. -/
  etale : Algebra.Etale A carrier
  /-- The reduction onto `P`. -/
  π : carrier →ₐ[A] P
  /-- The reduction is surjective. -/
  surjective : Function.Surjective π
  /-- The kernel of the reduction is the extension of `J`. -/
  ker_eq : RingHom.ker (π : carrier →+* P) = J.map (algebraMap A carrier)

attribute [instance] EtaleLiftData.commRing EtaleLiftData.algebra

/-- An étale lift of `P` exists (Stacks 04D1). -/
theorem nonempty_etaleLiftData : Nonempty (EtaleLiftData J P) := by
  obtain ⟨C, _, _, hC, ψ, hψ, hker⟩ :=
    etale_lift_along_surjection A (A ⧸ J) P Ideal.Quotient.mk_surjective
  have hk : RingHom.ker (algebraMap A (A ⧸ J)) = J := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  rw [hk] at hker
  exact ⟨⟨C, hC, ψ, hψ, hker⟩⟩

/-- A chosen étale lift of `P` over `A` (Stacks 04D1). -/
def etaleLiftData : EtaleLiftData J P := Classical.choice (nonempty_etaleLiftData J P)

/-- The chosen étale lift. -/
abbrev etaleLift : Type u := (etaleLiftData J P).carrier

/-- The chosen étale lift is étale over `A`. -/
instance : Algebra.Etale A (etaleLift J P) := (etaleLiftData J P).etale

/-- The reduction of the étale lift onto `P`. -/
abbrev etaleLiftπ : etaleLift J P →ₐ[A] P := (etaleLiftData J P).π

/-- The reduction of the étale lift onto `P` is surjective. -/
theorem surjective_etaleLiftπ : Function.Surjective (etaleLiftπ J P) :=
  (etaleLiftData J P).surjective

/-- The kernel of the reduction of the étale lift onto `P` is `J` times the lift. -/
theorem ker_etaleLiftπ :
    RingHom.ker (etaleLiftπ J P : etaleLift J P →+* P) = J.map (algebraMap A (etaleLift J P)) :=
  (etaleLiftData J P).ker_eq

end EtaleLift

section Nilpotent

variable {A : Type u} [CommRing A] (J : Ideal A) (T : Type v) [CommRing T] [Algebra A T]

/-- The extension of a square-zero ideal is square zero. -/
theorem map_sq_eq_bot (hJ : J ^ 2 = ⊥) : (J.map (algebraMap A T)) ^ 2 = ⊥ := by
  rw [← Ideal.map_pow, hJ, Ideal.map_bot]

/-- The extension of a square-zero ideal is nilpotent. -/
theorem isNilpotent_map (hJ : J ^ 2 = ⊥) : IsNilpotent (J.map (algebraMap A T)) :=
  ⟨2, map_sq_eq_bot J T hJ⟩

/-- Localizing a reduction modulo a square-zero ideal: the kernel of `T_g → (T ⧸ JT)_g` lies in
the extension of `J`, which is square zero. -/
theorem isNilpotent_ker_localization_map (hJ : J ^ 2 = ⊥) (g : T)
    (Tg : Type v) [CommRing Tg] [Algebra T Tg] [IsLocalization.Away g Tg]
    (T₀g : Type v) [CommRing T₀g] [Algebra (T ⧸ J.map (algebraMap A T)) T₀g]
    [IsLocalization.Away (Ideal.Quotient.mk (J.map (algebraMap A T)) g) T₀g] :
    IsNilpotent (RingHom.ker (IsLocalization.Away.map Tg T₀g
      (Ideal.Quotient.mk (J.map (algebraMap A T))) g)) := by
  have hle : RingHom.ker (IsLocalization.Away.map Tg T₀g
      (Ideal.Quotient.mk (J.map (algebraMap A T))) g) ≤
      (J.map (algebraMap A T)).map (algebraMap T Tg) := by
    intro x hx
    obtain ⟨c, ⟨_, n, rfl⟩, rfl⟩ :
        ∃ (c : T) (s : Submonoid.powers g), IsLocalization.mk' Tg c s = x := by
      obtain ⟨⟨c, s⟩, hs⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) x
      exact ⟨c, s, hs⟩
    rw [RingHom.mem_ker] at hx
    simp only [IsLocalization.Away.map, IsLocalization.map_mk'] at hx
    rw [IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := hx
    have hmem : g ^ m * c ∈ J.map (algebraMap A T) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]
      simpa using hm
    have hx' : IsLocalization.mk' Tg c (⟨g ^ n, n, rfl⟩ : Submonoid.powers g) =
        algebraMap T Tg (g ^ m * c) *
          IsLocalization.mk' Tg (1 : T) (⟨g ^ (m + n), m + n, rfl⟩ : Submonoid.powers g) := by
      rw [← IsLocalization.mk'_one (M := Submonoid.powers g) Tg, ← IsLocalization.mk'_mul,
        mul_one, IsLocalization.mk'_eq_iff_eq]
      simp only [pow_add, one_mul]
      ring_nf
    rw [hx']
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hmem)
  refine ⟨2, le_bot_iff.mp ?_⟩
  calc RingHom.ker _ ^ 2 ≤ ((J.map (algebraMap A T)).map (algebraMap T Tg)) ^ 2 :=
        Ideal.pow_right_mono hle 2
    _ = ⊥ := by rw [← Ideal.map_pow, map_sq_eq_bot J T hJ, Ideal.map_bot]

end Nilpotent

section QuotientBaseChange

/-- **Étaleness of a basic open survives reduction modulo an ideal of the base.** If `C[1/x]` is
étale over `A` for `x ∈ C`, then `(C ⧸ KC)[1/x]` is étale over `A ⧸ K`: it is
`C[1/x] ⧸ K C[1/x] = (A ⧸ K) ⊗[A] C[1/x]`. -/
theorem etale_localizationAway_quotient {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (K : Ideal A) (x : C) [Algebra.Etale A (Localization.Away x)] :
    Algebra.Etale (A ⧸ K)
      (Localization.Away (Ideal.Quotient.mk (K.map (algebraMap A C)) x)) := by
  set Cx := Localization.Away x
  set KC := K.map (algebraMap A C)
  set KCx := K.map (algebraMap A Cx)
  have : Algebra.Etale (A ⧸ K) (Cx ⧸ KCx) :=
    .of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Cx K).symm
  have hle : KC ≤ KCx.comap (algebraMap C Cx) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact Ideal.le_comap_map
  let : Algebra (C ⧸ KC) (Cx ⧸ KCx) := (Ideal.quotientMap KCx (algebraMap C Cx) hle).toAlgebra
  have : IsScalarTower (A ⧸ K) (C ⧸ KC) (Cx ⧸ KCx) := IsScalarTower.of_algebraMap_eq fun a ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    change Ideal.Quotient.mk KCx (algebraMap A Cx a) =
      Ideal.Quotient.mk KCx (algebraMap C Cx (algebraMap A C a))
    rw [← IsScalarTower.algebraMap_apply]
  have hloc : IsLocalization ((Submonoid.powers x).map (Ideal.Quotient.mk KC)) (Cx ⧸ KCx) :=
    IsLocalization.of_surjective (Submonoid.powers x) Cx (Ideal.Quotient.mk KC)
      Ideal.Quotient.mk_surjective (Ideal.Quotient.mk KCx) Ideal.Quotient.mk_surjective rfl (by
        rw [Ideal.mk_ker, Ideal.mk_ker, Ideal.map_map, ← IsScalarTower.algebraMap_eq])
  rw [Submonoid.map_powers] at hloc
  let e : Localization.Away (Ideal.Quotient.mk KC x) ≃ₐ[C ⧸ KC] Cx ⧸ KCx :=
    IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk KC x)) _ _
  exact .of_equiv (e.restrictScalars (A ⧸ K)).symm

end QuotientBaseChange

section Thickening

variable {A : Type u} [CommRing A] (J : Ideal A) (hJ : J ^ 2 = ⊥)
  {T T₀ S S₀ : Type u} [CommRing T] [CommRing T₀] [CommRing S] [CommRing S₀]
  [Algebra A T] [Algebra A T₀] [Algebra A S] [Algebra A S₀]
  [Algebra T S] [IsScalarTower A T S] [Algebra T₀ S₀] [IsScalarTower A T₀ S₀]
  [Algebra.Etale T₀ S₀]

/-- **Étaleness across a square-zero thickening.** Let `T ↠ T₀` and `S ↠ S₀` be reductions with
kernels `JT` and `JS`, `J² = 0`, compatible with a map `T → S`, and let `S₀` be étale over `T₀`.
Suppose that every element of `S₀ ⊗[A] J` killed by the push into `S` comes from an element of
`T₀ ⊗[A] J` killed by the push into `T`. Then `S` is étale over `T`: it is the étale lift of `S₀`
along `T ↠ T₀` (Stacks 04D1), the comparison map being bijective by rigidity. -/
theorem etale_of_pushOf (π : T →ₐ[A] T₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : T →+* T₀) = J.map (algebraMap A T))
    (πS : S →ₐ[A] S₀) (hπS : Function.Surjective πS)
    (hkerS : RingHom.ker (πS : S →+* S₀) = J.map (algebraMap A S))
    (hcomp : ∀ t, πS (algebraMap T S t) = algebraMap T₀ S₀ (π t))
    (H : ∀ w : S₀ ⊗[A] J, pushOf J hJ πS hπS hkerS w = 0 →
      ∃ m : T₀ ⊗[A] J, (IsScalarTower.toAlgHom A T₀ S₀).toLinearMap.rTensor J m = w ∧
        pushOf J hJ π hπ hker m = 0) :
    Algebra.Etale T S := by
  let : Algebra T T₀ := (π : T →+* T₀).toAlgebra
  let : Algebra T S₀ := ((algebraMap T₀ S₀).comp (π : T →+* T₀)).toAlgebra
  have : IsScalarTower T T₀ S₀ := .of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨C', _, _, hC', ψ, hψ, hkerψ⟩ := etale_lift_along_surjection T T₀ S₀ hπ
  let : Algebra A C' := ((algebraMap T C').comp (algebraMap A T)).toAlgebra
  have : IsScalarTower A T C' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A T S₀ := .of_algebraMap_eq fun a ↦ by
    change algebraMap A S₀ a = algebraMap T₀ S₀ (π (algebraMap A T a))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  let ψA : C' →ₐ[A] S₀ := ψ.restrictScalars A
  have hkerψA : RingHom.ker (ψA : C' →+* S₀) = J.map (algebraMap A C') := by
    change RingHom.ker (ψ : C' →+* S₀) = _
    rw [hkerψ]
    change (RingHom.ker (π : T →+* T₀)).map (algebraMap T C') = _
    rw [hker, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let πST : S →ₐ[T] S₀ :=
    { (πS : S →+* S₀) with
      commutes' := hcomp }
  have hnil : IsNilpotent (RingHom.ker (πST : S →+* S₀)) := by
    change IsNilpotent (RingHom.ker (πS : S →+* S₀))
    rw [hkerS]
    exact isNilpotent_map J S hJ
  let φ : C' →ₐ[T] S := Algebra.FormallySmooth.liftOfSurjective ψ πST hπS hnil
  have hφ : ∀ x, πS (φ x) = ψA x := fun x ↦
    Algebra.FormallySmooth.liftOfSurjective_apply ψ πST hπS hnil x
  have hbij : Function.Bijective (φ.restrictScalars A) :=
    bijective_of_pushOf J hJ πS hπS hkerS ψA hψ hkerψA (φ.restrictScalars A) hφ fun w hw ↦ by
      obtain ⟨m, rfl, hm⟩ := H w hw
      rw [pushOf_naturality J hJ π hπ hker ψA hψ hkerψA (IsScalarTower.toAlgHom A T C')
        (IsScalarTower.toAlgHom A T₀ S₀) (fun t ↦ ψ.commutes t) m, hm, map_zero]
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective φ hbij)

/-- An element whose image under a surjection with nilpotent kernel is a unit is a unit. -/
theorem _root_.isUnit_of_isUnit_map_of_isNilpotent_ker {R S : Type*} [CommRing R] [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hnil : IsNilpotent (RingHom.ker π)) {x : R}
    (hx : IsUnit (π x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨y, hy⟩ := hπ (↑u⁻¹ : S)
  have hmem : x * y - 1 ∈ RingHom.ker π := by
    rw [RingHom.mem_ker, map_sub, map_mul, hy, ← hu, Units.mul_inv, map_one, sub_self]
  obtain ⟨n, hn⟩ := hnil
  have hnil' : IsNilpotent (x * y - 1) :=
    ⟨n, by simpa only [hn, Ideal.zero_eq_bot, Ideal.mem_bot] using Ideal.pow_mem_pow hmem n⟩
  exact isUnit_of_mul_isUnit_left (sub_add_cancel (x * y) 1 ▸ hnil'.isUnit_add_one)

include hJ in
/-- **Localizing a square-zero thickening against an étale lift.** Let `π : T ↠ T₀` be a
reduction with kernel `JT`, `J² = 0`, let `x ∈ T`, and let `E` be an étale `A`-algebra lifting
`T₀[1/π x]`, receiving a map from `T` which inverts `x` and lifts `T → T₀[1/π x]`. Then
`T[1/x] ≅ E`, so `T[1/x]` is étale over `A`. -/
theorem etale_localizationAway_of_thickening {E Q : Type u} [CommRing E] [CommRing Q]
    [Algebra A E] [Algebra.Etale A E] [Algebra A Q] [Algebra T₀ Q] [IsScalarTower A T₀ Q]
    (π : T →ₐ[A] T₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : T →+* T₀) = J.map (algebraMap A T)) (x : T)
    [IsLocalization.Away (π x) Q]
    (πE : E →ₐ[A] Q) (hπE : Function.Surjective πE)
    (hkerE : RingHom.ker (πE : E →+* Q) = J.map (algebraMap A E))
    (ε : T →ₐ[A] E) (hε : ∀ t, πE (ε t) = algebraMap T₀ Q (π t)) :
    Algebra.Etale A (Localization.Away x) := by
  have hT : Submonoid.map (π : T →+* T₀) (Submonoid.powers x) = Submonoid.powers (π x) := by
    rw [Submonoid.map_powers]; rfl
  have : IsLocalization (Submonoid.map (π : T →+* T₀) (Submonoid.powers x)) Q := by
    rw [hT]; infer_instance
  let π' : Localization.Away x →ₐ[A] Q := IsLocalization.Away.mapₐ _ _ π x
  have hπ' : Function.Surjective π' :=
    IsLocalization.Away.mapₐ_surjective_of_surjective x hπ
  have hker' : RingHom.ker (π' : Localization.Away x →+* Q) =
      J.map (algebraMap A (Localization.Away x)) := by
    change RingHom.ker (IsLocalization.map Q (π : T →+* T₀)
      (Submonoid.powers x).le_comap_map) = _
    rw [IsLocalization.ker_map (S := Localization.Away x) Q (π : T →+* T₀)
      (M := Submonoid.powers x) (T := Submonoid.map (π : T →+* T₀) (Submonoid.powers x)) rfl,
      hker, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hunit : IsUnit (ε x) := by
    refine isUnit_of_isUnit_map_of_isNilpotent_ker (πE : E →+* Q) hπE
      (by rw [hkerE]; exact isNilpotent_map J E hJ) ?_
    change IsUnit (πE (ε x))
    rw [hε]
    exact IsLocalization.Away.algebraMap_isUnit (π x)
  let ρ : Localization.Away x →ₐ[A] E := IsLocalization.Away.liftAlgHom x (f := ε) hunit
  have hρ : ∀ y, πE (ρ y) = π' y := fun y ↦ by
    have : (πE.comp ρ) = π' := by
      ext t
      change πE (IsLocalization.Away.lift x hunit (algebraMap T _ t)) =
        IsLocalization.map Q (π : T →+* T₀) (Submonoid.powers x).le_comap_map (algebraMap T _ t)
      rw [IsLocalization.Away.lift_eq, IsLocalization.map_eq]
      exact hε t
    exact AlgHom.congr_fun this y
  have hbij : Function.Bijective ρ :=
    bijective_of_pushOf J hJ πE hπE hkerE π' hπ' hker' ρ hρ (fun w hw ↦ by
      rw [injective_pushOf J hJ _ _ _ (hw.trans (map_zero _).symm), map_zero])
  exact Algebra.Etale.of_equiv (AlgEquiv.ofBijective ρ hbij).symm

include hJ in
/-- A square-zero thickening of a finite type algebra is of finite type (Stacks 0G8U). -/
theorem finiteType_of_thickening (π : T →ₐ[A] T₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : T →+* T₀) = J.map (algebraMap A T)) [Algebra.FiniteType A T₀] :
    Algebra.FiniteType A T := by
  have e : (T ⧸ J.map (algebraMap A T)) ≃ₐ[A] T₀ :=
    (Ideal.quotientEquivAlgOfEq A hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hπ)
  have : Algebra.FiniteType A (T ⧸ J.map (algebraMap A T)) := .equiv inferInstance e.symm
  exact finiteType_of_isNilpotent_quotient_finiteType A J T ⟨2, by rw [hJ, Ideal.zero_eq_bot]⟩
    (.of_restrictScalars_finiteType A (A ⧸ J) _)

omit [Algebra T S] [IsScalarTower A T S] [Algebra T₀ S₀] [IsScalarTower A T₀ S₀]
  [Algebra.Etale T₀ S₀] in
/-- The reduction of a surjection with kernel `JT` modulo `IT`: an element mapping into `I T₀`
lies in `IT + JT`. -/
theorem mem_sup_of_map_mem (π : T →ₐ[A] T₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker (π : T →+* T₀) = J.map (algebraMap A T)) (I : Ideal A) {t : T}
    (ht : π t ∈ I.map (algebraMap A T₀)) :
    t ∈ I.map (algebraMap A T) ⊔ J.map (algebraMap A T) := by
  have h : I.map (algebraMap A T₀) = (I.map (algebraMap A T)).map (π : T →+* T₀) := by
    rw [Ideal.map_map]
    congr 1
    ext a
    simp
  rw [h] at ht
  have ht' : t ∈ Ideal.comap (π : T →+* T₀) ((I.map (algebraMap A T)).map (π : T →+* T₀)) := ht
  rwa [Ideal.comap_map_of_surjective (π : T →+* T₀) hπ, ← RingHom.ker_eq_comap_bot, hker] at ht'


end Thickening

end SquareZero
