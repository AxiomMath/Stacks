module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.AlgebraicGeometry.DenseDenominators.Algebra

/-!
# The algebra of denominators is quasi-coherent

Let `Y` be a reduced scheme, `Ω` an open subset of `Y` and `S` a flat algebra over the
sections of the structure sheaf on `Ω`, presented by a finite spanning family. For an affine open
`U` of `Y` and a section `r` over `U`, the algebra of denominators over the basic open set of `r`
is the localization of the algebra of denominators over `U` away from `r`. Together with
`Stacks.DenseDenominators.sub_eq_top` and the compatibility with restriction this is the
statement that the algebras of denominators are the sections of a quasi-coherent sheaf.

## Main results

* `Stacks.DenseDenominators.isLocalization_away_sub`: the algebra of denominators over the basic
  open set of `r` is the localization away from `r` of the algebra of denominators over the
  affine open.

## Implementation notes

The three conditions characterizing a localization away from an element are supplied through
`IsLocalization.Away.mk`, and each uses a different input.

* That `r` becomes a unit is `IsAffineOpen.isLocalization_basicOpen`, transported along the ring
  homomorphism `Stacks.DenseDenominators.toSub`.
* Surjectivity decomposes an element over the basic open set into a section plus multiples of the
  generators by denominators, clears the section with `IsLocalization.Away.surj` and each
  denominator with `Stacks.DenseDenominators.exists_pow_mul_eq_resHom_of_mem_denom`, and then
  raises every cleared piece to one common power of `r` — which keeps the denominators
  denominators, the ideal of denominators being an ideal.
* The third condition is the only place flatness of `S` is used, and it needs only a single factor
  of `r`. Restriction in the ambient ring is the right tensoring with `S` of restriction of
  sections, by `Stacks.DenseDenominators.ambRes_eq_rTensor`; flatness keeps the kernel sequence of
  restriction exact after tensoring, so an element of the ambient ring over `U` dying over the
  basic open set is a sum of terms `k ⊗ₜ s` with `k` a section over `U ⊓ Ω` dying over
  `Y.basicOpen r ⊓ Ω`; and each such `k` is killed by `r` through
  `Stacks.DenseRestriction.mul_eq_zero_of_res_eq_zero_of_basicOpen_le`.

The local instance `Stacks.DenseDenominators.algebraInf`, making the sections over `W ⊓ Ω` an
algebra over the sections over `Ω`, is re-enabled here with `attribute [local instance]` rather
than restated, so that it is literally the instance the definitions of
`Stacks.DenseDenominators.amb` and `Stacks.DenseDenominators.sub` were elaborated with.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.FiniteAlgebraPresentation TensorProduct

universe u

namespace Stacks.DenseDenominators

attribute [local instance] algebraInf

variable {Y : Scheme.{u}} {Ω : Y.Opens}

section Ambient

variable (S : Type u) [CommRing S] [Algebra Γ(Y, Ω) S]

/-- **Restriction in the ambient ring is right tensoring with `S`.** Both sides send `t ⊗ₜ s` to
the restriction of `t` tensored with `s`. -/
lemma ambRes_eq_rTensor {V W : Y.Opens} (h : V ≤ W) (x : amb Ω S W) :
    ambRes Ω S h x = LinearMap.rTensor S (resAlgHom Ω h).toLinearMap x := by
  induction x using TensorProduct.inductionOn with
  | tmul t s => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **One factor of `r` kills everything in the ambient ring over an affine open that dies over
the basic open set of `r`.** This is where flatness of `S` is used: tensoring the exact sequence
`ker ⟶ Γ(Y, U ⊓ Ω) ⟶ Γ(Y, Y.basicOpen r ⊓ Ω)` with the flat module `S` keeps it exact, so such an
element is a sum of terms `k ⊗ₜ s` with `k` a section over `U ⊓ Ω` restricting to zero over
`Y.basicOpen r ⊓ Ω`, and each of those is killed by `r` on the reduced scheme `Y`. -/
lemma toAmb_mul_eq_zero_of_ambRes_eq_zero [IsReduced Y] [Module.Flat Γ(Y, Ω) S] {U : Y.Opens}
    (r : Γ(Y, U)) (w : amb Ω S U) (hw : ambRes Ω S (Y.basicOpen_le r) w = 0) :
    toAmb Ω S U r * w = 0 := by
  have hbas : Y.basicOpen (resHom (inf_le_left : U ⊓ Ω ≤ U) r) ≤ Y.basicOpen r ⊓ Ω := by
    rw [Scheme.basicOpen_res]
    exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
  have hgen : ∀ k : Γ(Y, U ⊓ Ω),
      resHom (inf_le_inf (Y.basicOpen_le r) (le_refl Ω)) k = 0 →
      ∀ s : S, toAmb Ω S U r * (k ⊗ₜ[Γ(Y, Ω)] s) = 0 := by
    intro k hk s
    rw [toAmb_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Stacks.DenseRestriction.mul_eq_zero_of_res_eq_zero_of_basicOpen_le
        (inf_le_inf (Y.basicOpen_le r) (le_refl Ω)) _ _ hbas hk, zero_tmul]
  have hex := Module.Flat.rTensor_exact (R := Γ(Y, Ω)) S
    (LinearMap.exact_subtype_ker_map (resAlgHom Ω (Y.basicOpen_le r)).toLinearMap)
  have hw' : LinearMap.rTensor S (resAlgHom Ω (Y.basicOpen_le r)).toLinearMap w = 0 := by
    rw [← ambRes_eq_rTensor]
    exact hw
  obtain ⟨v, hv⟩ := (hex w).mp hw'
  rw [← hv]
  clear hv hw' hw
  induction v using TensorProduct.inductionOn with
  | tmul k s => exact hgen _ (LinearMap.mem_ker.mp k.2) s
  | add v v' h1 h2 => rw [map_add, mul_add, h1, h2, add_zero]

end Ambient

section Subring

variable {S : Type u} [CommRing S] [Algebra Γ(Y, Ω) S] (P : Presentation Γ(Y, Ω) S)

/-- **Multiplying a decomposed element of the algebra of denominators by a section.** The section
part is multiplied, and each multiple of a generator by a denominator stays one. -/
lemma decomp_mul_toAmb {W : Y.Opens} (u v : Γ(Y, W)) (ρ : P.L → Γ(Y, W)) :
    (toAmb Ω S W u + ∑ l, genMul P W l (ρ l)) * toAmb Ω S W v
      = toAmb Ω S W (u * v) + ∑ l, genMul P W l (ρ l * v) := by
  rw [add_mul, ← map_mul, Finset.sum_mul]
  refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
  rw [mul_comm, toAmb_mul_genMul, mul_comm v (ρ l)]

end Subring

/-- **The algebra of denominators over the basic open set of `r` is the localization away from `r`
of the algebra of denominators over the affine open.** This is the quasi-coherence of the
construction: `r` becomes a unit because the sections over its basic open set are already the
localization, denominators over the basic open set can be cleared to denominators over the affine
open at the cost of a power of `r`, and flatness of `S` makes one single factor of `r` enough to
detect equality. -/
theorem isLocalization_away_sub {Y : Scheme.{u}} [IsReduced Y] {Ω : Y.Opens}
    {S : Type u} [CommRing S] [Algebra Γ(Y, Ω) S]
    [Module.Flat Γ(Y, Ω) S] (P : Presentation Γ(Y, Ω) S)
    {U : Y.Opens} (hU : IsAffineOpen U) (r : Γ(Y, U)) :
    letI := (subRes P (Y.basicOpen_le r)).toAlgebra
    IsLocalization.Away (toSub P U r) (sub P (Y.basicOpen r)) := by
  classical
  let := (subRes P (Y.basicOpen_le r)).toAlgebra
  have := hU.isLocalization_basicOpen r
  have halg : algebraMap (sub P U) (sub P (Y.basicOpen r)) = subRes P (Y.basicOpen_le r) :=
    RingHom.algebraMap_toAlgebra _
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · -- `r` becomes a unit: it already is one in the sections over its basic open set
    have hru : IsUnit (resHom (Y.basicOpen_le r) r) := by
      have h := IsLocalization.Away.algebraMap_isUnit (S := Γ(Y, Y.basicOpen r)) r
      rwa [algebraMap_basicOpen_eq] at h
    rw [halg, subRes_toSub]
    exact hru.map (toSub P (Y.basicOpen r))
  · -- surjectivity: clear the section and every denominator by one common power of `r`
    intro z
    obtain ⟨u, ρ, hρ, hz⟩ := z.2
    obtain ⟨n₀, a₀, ha₀⟩ := IsLocalization.Away.surj r u
    rw [algebraMap_basicOpen_eq] at ha₀
    choose m ρ' hρ'mem hρ'eq using fun l =>
      exists_pow_mul_eq_resHom_of_mem_denom P.coeffFamily hU r (ρ l) (hρ l)
    obtain ⟨N, hn₀, hm⟩ : ∃ N : ℕ, n₀ ≤ N ∧ ∀ l, m l ≤ N :=
      ⟨max n₀ (Finset.univ.sup m), le_max_left _ _,
        fun l => (Finset.le_sup (Finset.mem_univ l)).trans (le_max_right _ _)⟩
    have hclear : ∀ (x : Γ(Y, Y.basicOpen r)) (n : ℕ) (a : Γ(Y, U)),
        x * resHom (Y.basicOpen_le r) r ^ n = resHom (Y.basicOpen_le r) a → n ≤ N →
        x * resHom (Y.basicOpen_le r) r ^ N = resHom (Y.basicOpen_le r) (r ^ (N - n) * a) := by
      intro x n a h hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [map_mul, map_pow, ← h, Nat.add_sub_cancel_left, pow_add]
      ring
    have hu' := hclear u n₀ a₀ ha₀ hn₀
    have hρ'' := fun l => hclear (ρ l) (m l) (ρ' l) ((hρ'eq l).trans (mul_comm _ _)).symm (hm l)
    refine ⟨N, ⟨toAmb Ω S U (r ^ (N - n₀) * a₀) + ∑ l, genMul P U l (r ^ (N - m l) * ρ' l),
      ⟨r ^ (N - n₀) * a₀, fun l => r ^ (N - m l) * ρ' l,
        fun l => Ideal.mul_mem_left _ _ (hρ'mem l), rfl⟩⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, Subring.coe_pow, halg]
    simp only [subRes_coe, toSub_coe]
    rw [ambRes_toAmb, hz, ← map_pow, decomp_mul_toAmb, map_add, ambRes_toAmb, map_sum, hu']
    refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
    rw [ambRes_genMul, hρ'' l]
  · -- one factor of `r` detects equality, by flatness of `S`
    intro a b hab
    rw [halg] at hab
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subring.coe_mul, Subring.coe_mul, toSub_coe]
    refine sub_eq_zero.mp ?_
    rw [← mul_sub]
    refine toAmb_mul_eq_zero_of_ambRes_eq_zero S r _ ?_
    rw [map_sub, ← subRes_coe, ← subRes_coe, hab, sub_self]

end Stacks.DenseDenominators

end
