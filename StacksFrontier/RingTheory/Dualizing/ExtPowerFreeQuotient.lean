module

public import StacksFrontier.RingTheory.Dualizing.ExtPowerRegularElement

/-!
# `Ext` out of the quotient of a finite free module by a power of a regular element

Let `B` be a Noetherian local ring with normalized dualizing complex `ω`, and let `f ∈ B` be a
nonzerodivisor. `StacksFrontier.RingTheory.Dualizing.ExtPowerRegularElement` proves that the
reduction map

  `Ext^{-k+1}_B(B/fB, ω) ⟶ Ext^{-k+1}_B(B/f^{n+1}B, ω)`

is zero as soon as `1 ≤ k ≤ depth(B)`, `f^c` kills `H^{-k}(ω)` and `c ≤ n`.  This file upgrades
that statement from the ring itself to a finite free module `B^r`, and then transports it along
an arbitrary presentation.

The upgrade is formal.  A finite product `Fin r → M` is the `r`-fold biproduct of `M`, so the
identity of `B^r` is the sum `∑ j, p_j ≫ s_j` of its projections followed by its coprojections.
The functor `M ↦ M[0]` into the derived category is additive and composition is bilinear, so a
class in `Ext^i_B(B^r, ω)` which dies against every coprojection `s_j : B ⟶ B^r` is zero.  Both
hypotheses of `Dualizing.extQuotPow_eq_zero` are statements of exactly that shape — a vanishing
and an annihilation in `Ext^i_B(B^r, ω)` — so each follows from its counterpart over `B`, which
is what the proof over `B` already supplies.

The transport is equally formal.  The hypotheses on `h : L → L₀` say that `h` is a surjection
with kernel `fL`, and that is precisely what the model reduction
`Dualizing.quotPowToQuot f (Fin r → B) n` is (`Dualizing.ker_quotPowToQuot`).  Two surjections
out of one module with one kernel differ by a unique isomorphism of their targets
(`Dualizing.equivOfKerEq`), so the given isomorphism `e : L ≃ B^r/f^{n+1}B^r` extends to an
isomorphism `L₀ ≃ B^r/fB^r` compatible with `h`, and the vanishing transports.  No compatible
choice of bases at different levels `n` is involved.

That last point is why the statement is useful.  In the proof of [Stacks, Tag 0EFX] the modules
`L` are the terms of a filtration, each presented separately as a quotient of a finite free
module, and nothing identifies their presentations across the levels `n`.

## Main definitions

* `Dualizing.equivOfKerEq` — the isomorphism between the targets of two surjections out of one
  module with the same kernel.

## Main results

* `Dualizing.eq_zero_of_forall_comp_single_eq_zero` — a class in `Ext^i_A(M^r, K)` vanishing
  against every coprojection `M ⟶ M^r` is zero.
* `Dualizing.subsingleton_moduleExtInto_pi` and `Dualizing.smul_eq_zero_pi` — the two
  consequences of that used below.
* `Dualizing.ker_quotPowToQuot` — the kernel of `M/f^{n+1}M ⟶ M/fM` is `f·(M/f^{n+1}M)`.
* `Dualizing.equivOfKerEq_apply` — the compatibility of `Dualizing.equivOfKerEq` with the two
  surjections.
* `Dualizing.extQuotPow_fin_eq_zero` — the finite free form of
  `Dualizing.extQuotPow_eq_zero_of_le_depth_of_pow_smul_eq_zero`.
* `Dualizing.ext_precomp_eq_zero_of_isoQuotPow` — the same vanishing for precomposition with an
  arbitrary surjection with kernel `fL` out of a module isomorphic to `B^r/f^{n+1}B^r`.
* `Dualizing.extPrecomp_eq_zero_of_pos` — in positive degree every precomposition map between
  `Ext` modules of finite modules is zero, which is the remaining case of [Stacks, Tag 0DXU].

## References

* [Stacks Project, Tag 0DXU](https://stacks.math.columbia.edu/tag/0DXU)
* [Stacks Project, Tag 0EFX](https://stacks.math.columbia.edu/tag/0EFX)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated DerivedCategory
open Pointwise

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Dualizing

variable {A : Type u} [CommRing A]

/-! ### `Ext` out of a finite product -/

/-- **A finite product is a biproduct.** The identity of `Fin r → M` is the sum over `j` of the
`j`-th projection followed by the `j`-th coprojection. -/
theorem id_eq_sum_proj_comp_single (M : Type v) [AddCommGroup M] [Module A M] (r : ℕ) :
    𝟙 (ModuleCat.of A (Fin r → M)) =
      ∑ j : Fin r, ModuleCat.ofHom (LinearMap.proj j : (Fin r → M) →ₗ[A] M) ≫
        ModuleCat.ofHom (LinearMap.single A (fun _ : Fin r => M) j) := by
  ext x
  simp

/-- **`Ext` out of a finite product is detected by the coprojections.** A class in
`Ext^i_A(M^r, K)` whose composite with every coprojection `M ⟶ M^r` vanishes is zero.

This is the additivity of `Ext^i(-, K)` in its first variable: the identity of `M^r` is the sum
of the composites `p_j ≫ s_j` (`Dualizing.id_eq_sum_proj_comp_single`), the functor `M ↦ M[0]`
is additive, and composition is bilinear. -/
theorem eq_zero_of_forall_comp_single_eq_zero (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ) (r : ℕ)
    (x : moduleExtInto (Fin r → M) K i)
    (hx : ∀ j : Fin r, (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
      (ModuleCat.ofHom (LinearMap.single A (fun _ : Fin r => M) j)) ≫ x = 0) :
    x = 0 := by
  have hid : (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
      (𝟙 (ModuleCat.of A (Fin r → M))) ≫ x = x := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← hid, id_eq_sum_proj_comp_single, CategoryTheory.Functor.map_sum, Preadditive.sum_comp]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hx j, comp_zero]

/-- **The vanishing of `Ext` out of a finite product.** If `Ext^i_A(M, K)` vanishes then so does
`Ext^i_A(M^r, K)`. -/
theorem subsingleton_moduleExtInto_pi (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ) (r : ℕ)
    [Subsingleton (moduleExtInto M K i)] :
    Subsingleton (moduleExtInto (Fin r → M) K i) :=
  ⟨fun a b => sub_eq_zero.mp
    (eq_zero_of_forall_comp_single_eq_zero M K i r (a - b) fun _ => Subsingleton.elim _ _)⟩

/-- **An annihilator of `Ext` out of a module annihilates `Ext` out of a finite product.** If
`a ∈ A` kills `Ext^i_A(M, K)` then it kills `Ext^i_A(M^r, K)`. -/
theorem smul_eq_zero_pi (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ) (r : ℕ) (a : A)
    (ha : ∀ y : moduleExtInto M K i, a • y = 0) (x : moduleExtInto (Fin r → M) K i) :
    a • x = 0 := by
  refine eq_zero_of_forall_comp_single_eq_zero M K i r _ fun j => ?_
  rw [Linear.comp_smul, ha]

/-! ### The kernel of the reduction map -/

/-- **The kernel of the reduction `M/f^{n+1}M → M/fM` is `f·(M/f^{n+1}M)`.** The kernel is the
image of `fM`, and `f^{n+1}M ⊆ fM`, so that image is `f` times the whole quotient. -/
theorem ker_quotPowToQuot (f : A) (M : Type v) [AddCommGroup M] [Module A M] (n : ℕ) :
    LinearMap.ker (quotPowToQuot f M n) =
      f • (⊤ : Submodule A (QuotSMulTop (f ^ (n + 1)) M)) := by
  ext y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [LinearMap.mem_ker, quotPowToQuot_mk, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, -, rfl⟩
    exact ⟨Submodule.Quotient.mk w, Submodule.mem_top, rfl⟩
  · rintro ⟨z, -, hz⟩
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hz' : (Submodule.Quotient.mk (f • w) : QuotSMulTop (f ^ (n + 1)) M) =
        Submodule.Quotient.mk x := hz
    obtain ⟨v, -, hv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ (f ^ (n + 1)) ⊤).mp
      ((Submodule.Quotient.eq _).mp hz')
    refine ⟨w - f ^ n • v, Submodule.mem_top, ?_⟩
    rw [smul_sub, smul_smul, show f * f ^ n = f ^ (n + 1) by ring, hv, sub_sub_cancel]

/-! ### Two surjections with one kernel -/

/-- **Two surjections out of one module with the same kernel have isomorphic targets.** The
isomorphism is the one compatible with the two surjections, which is
`Dualizing.equivOfKerEq_apply`. -/
noncomputable def equivOfKerEq {L L₀ L₁ : Type v} [AddCommGroup L] [Module A L]
    [AddCommGroup L₀] [Module A L₀] [AddCommGroup L₁] [Module A L₁]
    (h : L →ₗ[A] L₀) (hsurj : Function.Surjective h)
    (g : L →ₗ[A] L₁) (gsurj : Function.Surjective g)
    (hker : LinearMap.ker h = LinearMap.ker g) :
    L₀ ≃ₗ[A] L₁ :=
  (h.quotKerEquivOfSurjective hsurj).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (g.quotKerEquivOfSurjective gsurj))

/-- **The compatibility of `Dualizing.equivOfKerEq` with the two surjections.** -/
@[simp]
theorem equivOfKerEq_apply {L L₀ L₁ : Type v} [AddCommGroup L] [Module A L]
    [AddCommGroup L₀] [Module A L₀] [AddCommGroup L₁] [Module A L₁]
    (h : L →ₗ[A] L₀) (hsurj : Function.Surjective h)
    (g : L →ₗ[A] L₁) (gsurj : Function.Surjective g)
    (hker : LinearMap.ker h = LinearMap.ker g) (x : L) :
    equivOfKerEq h hsurj g gsurj hker (h x) = g x := by
  simp [equivOfKerEq]

/-! ### The free-module form of the vanishing -/

section Dualizing

variable {B : Type u} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]

/-- **The last step of the proof of [Stacks, Tag 0DXU] for a finite free module.** Let `B` be a
Noetherian local ring with normalized dualizing complex `ω`, let `f ∈ B` act regularly on `B`,
let `1 ≤ k ≤ depth(B)`, and let `f^c` annihilate `Ext^{-k}_B(B, ω) = H^{-k}(ω)`. Then for every
`n ≥ c` and every `r` the reduction map

  `Ext^{-k+1}_B(B^r/fB^r, ω) ⟶ Ext^{-k+1}_B(B^r/f^{n+1}B^r, ω)`

is zero.

This is `Dualizing.extQuotPow_eq_zero_of_le_depth_of_pow_smul_eq_zero` with the ring replaced by
the finite free module `B^r`, and its proof is the same one, each of the two hypotheses of
`Dualizing.extQuotPow_eq_zero` being carried from `B` to `B^r` by the additivity of `Ext` out of
a finite product: the absence of `f`-torsion in `Ext^{-k+1}_B(B^r, ω)` is again the vanishing of
that module, now by `Dualizing.subsingleton_moduleExtInto_pi`, and `f^n` again kills
`Ext^{-k}_B(B^r, ω)` outright, now by `Dualizing.smul_eq_zero_pi`. -/
theorem extQuotPow_fin_eq_zero
    (K : DerivedCategory (ModuleCat.{u} B)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    (f : B) (hreg : IsSMulRegular B f) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : (k : ℕ∞) ≤ Module.depth B (IsLocalRing.maximalIdeal B) B) (c : ℕ)
    (hc : ∀ x : moduleExtInto B K (-(k : ℤ)), f ^ c • x = 0) (n : ℕ) (hn : c ≤ n) (r : ℕ) :
    extQuotPow (Fin r → B) K f n (-(k : ℤ) + 1) = 0 := by
  have hregr : IsSMulRegular (Fin r → B) f := IsSMulRegular.pi fun _ => hreg
  refine extQuotPow_eq_zero (Fin r → B) K f hregr n (-(k : ℤ)) (fun x _ => ?_) (fun z => ?_)
  · have : Subsingleton (moduleExtInto B K (-(k : ℤ) + 1)) := by
      have hlt : ((k - 1 : ℕ) : ℕ∞) < Module.depth B (IsLocalRing.maximalIdeal B) B :=
        lt_of_lt_of_le (by exact_mod_cast Nat.sub_lt (by omega) Nat.one_pos) hk
      have heq : -((k - 1 : ℕ) : ℤ) = -(k : ℤ) + 1 := by omega
      exact heq ▸ subsingleton_moduleExtInto_self_of_lt_depth K hK (k - 1) hlt
    have : Subsingleton (moduleExtInto (Fin r → B) K (-(k : ℤ) + 1)) :=
      subsingleton_moduleExtInto_pi B K (-(k : ℤ) + 1) r
    exact Subsingleton.elim x 0
  · have hz : f ^ n • z = 0 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [pow_add, mul_comm (f ^ c) (f ^ d), mul_smul,
        smul_eq_zero_pi B K (-(k : ℤ)) r (f ^ c) hc, smul_zero]
    rw [hz]
    exact Submodule.zero_mem _

/-! ### The vanishing for an arbitrary presentation -/

/-- **The last step of the proof of [Stacks, Tag 0DXU] for an arbitrary free presentation.** Let
`B`, `ω`, `f`, `k`, `c` and `n` be as in `Dualizing.extQuotPow_fin_eq_zero`, let `L` be a module
isomorphic to `B^r/f^{n+1}B^r`, and let `h : L → L₀` be a surjection with kernel `fL`. Then
precomposition with `h`,

  `Ext^{-k+1}_B(L₀, ω) ⟶ Ext^{-k+1}_B(L, ω)`,

is zero.

The hypotheses on `h` say exactly that `h` is, up to an isomorphism of its target, the reduction
`B^r/f^{n+1}B^r ⟶ B^r/fB^r` transported along `e`: that reduction is surjective with kernel `f`
times the whole module (`Dualizing.ker_quotPowToQuot`), the isomorphism `e` carries `fL` to that
kernel, and two surjections out of `L` with one kernel differ by an isomorphism of their targets
(`Dualizing.equivOfKerEq`). So the statement is `Dualizing.extQuotPow_fin_eq_zero` read through
that isomorphism.

No compatibility between the presentations `e` at different levels `n` is required. -/
theorem ext_precomp_eq_zero_of_isoQuotPow
    (K : DerivedCategory (ModuleCat.{u} B)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    (f : B) (hreg : IsSMulRegular B f) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : (k : ℕ∞) ≤ Module.depth B (IsLocalRing.maximalIdeal B) B) (c : ℕ)
    (hc : ∀ x : moduleExtInto B K (-(k : ℤ)), f ^ c • x = 0) (n : ℕ) (hn : c ≤ n)
    {L L₀ : Type u} [AddCommGroup L] [Module B L] [AddCommGroup L₀] [Module B L₀]
    (r : ℕ) (e : L ≃ₗ[B] QuotSMulTop (f ^ (n + 1)) (Fin r → B))
    (h : L →ₗ[B] L₀) (hsurj : Function.Surjective h)
    (hker : LinearMap.ker h = f • (⊤ : Submodule B L)) :
    Linear.leftComp B
        ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} B)) (-(k : ℤ) + 1)).obj K)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map (ModuleCat.ofHom h)) = 0 := by
  -- The model surjection `L ⟶ B^r/fB^r`, namely the reduction read through `e`.
  have hqsurj : Function.Surjective (quotPowToQuot f (Fin r → B) n) := fun y => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨(Submodule.Quotient.mk x : QuotSMulTop (f ^ (n + 1)) (Fin r → B)), rfl⟩
  have hgsurj : Function.Surjective
      ((quotPowToQuot f (Fin r → B) n).comp e.toLinearMap) :=
    hqsurj.comp e.surjective
  have hkerg : LinearMap.ker ((quotPowToQuot f (Fin r → B) n).comp e.toLinearMap) =
      f • (⊤ : Submodule B L) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.mem_ker, ker_quotPowToQuot,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, -, hy⟩
      obtain ⟨w, rfl⟩ := e.surjective y
      exact ⟨w, Submodule.mem_top, e.injective ((map_smul e f w).trans hy)⟩
    · rintro ⟨w, -, rfl⟩
      exact ⟨e w, Submodule.mem_top, (map_smul e f w).symm⟩
  -- The induced isomorphism `L₀ ≃ B^r/fB^r`.
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : L₀ ≃ₗ[B] QuotSMulTop f (Fin r → B),
      ∀ x : L, e₀ (h x) = quotPowToQuot f (Fin r → B) n (e x) :=
    ⟨equivOfKerEq h hsurj _ hgsurj (hker.trans hkerg.symm),
      equivOfKerEq_apply h hsurj _ hgsurj (hker.trans hkerg.symm)⟩
  have hcomm : ModuleCat.ofHom h ≫ ModuleCat.ofHom e₀.toLinearMap =
      ModuleCat.ofHom e.toLinearMap ≫
        ModuleCat.ofHom (quotPowToQuot f (Fin r → B) n) := by
    ext x
    exact he₀ x
  have hcompose : ModuleCat.ofHom e₀.toLinearMap ≫ ModuleCat.ofHom e₀.symm.toLinearMap =
      𝟙 (ModuleCat.of B L₀) := by
    ext y
    exact e₀.symm_apply_apply y
  refine LinearMap.ext fun x => ?_
  have hx : x = (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map
      (ModuleCat.ofHom e₀.toLinearMap) ≫
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map
        (ModuleCat.ofHom e₀.symm.toLinearMap) ≫ x) := by
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hcompose,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hinner : (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map
      (ModuleCat.ofHom (quotPowToQuot f (Fin r → B) n)) ≫
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map
        (ModuleCat.ofHom e₀.symm.toLinearMap) ≫ x) = 0 :=
    LinearMap.congr_fun (extQuotPow_fin_eq_zero K hK f hreg k hk1 hk c hc n hn r) _
  rw [LinearMap.zero_apply, Linear.leftComp_apply, hx, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, hcomm, CategoryTheory.Functor.map_comp, Category.assoc,
    hinner, comp_zero]

/-! ### The case of positive degree -/

/-- **`Ext` out of a finite module into a normalized dualizing complex vanishes in positive
degree, so there every precomposition map is zero.** This is the case `dim(A/𝔮) ≥ 3` of
[Stacks, Tag 0DXU], where the degree `-2 + dim(A/𝔮)` is positive and
`Dualizing.subsingleton_moduleExtInto_of_pos` kills the target outright. -/
theorem extPrecomp_eq_zero_of_pos
    (K : DerivedCategory (ModuleCat.{u} B)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    {L L₀ : Type u} [AddCommGroup L] [Module B L] [Module.Finite B L]
    [AddCommGroup L₀] [Module B L₀] [Module.Finite B L₀]
    (h : L →ₗ[B] L₀) (j : ℤ) (hj : 0 < j) :
    Linear.leftComp B ((CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} B)) j).obj K)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).map (ModuleCat.ofHom h)) = 0 := by
  have := subsingleton_moduleExtInto_of_pos (M := L) K hK j hj
  exact LinearMap.ext fun x => Subsingleton.elim _ _

end Dualizing

end Dualizing

end
