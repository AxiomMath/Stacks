module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.RepresentationTheory.Coinvariants
import StacksCore.Tactic.StacksAttribute

/-!
# The sign-twisted permutation action on a tensor power, and the exterior power

Let `B` be a commutative ring, `M` a `B`-module and `k` a natural number. The symmetric group
`S_k` acts on the `k`th tensor power `M^{⊗ k}` by permuting the factors; **twisting that action
by the sign character** gives the representation

`σ ↦ sign(σ) • (x_1 ⊗ ⋯ ⊗ x_k ↦ x_{σ⁻¹(1)} ⊗ ⋯ ⊗ x_{σ⁻¹(k)})`,

and this file identifies its coinvariants with the exterior power `∧^k_B M`.

The identification is not an isomorphism for every ring: the canonical map is always surjective
and its kernel is always killed by `2`, and the kernel is genuinely nonzero for `B = M = ℤ` and
`k = 2`, where the coinvariants are `ℤ/2` and `∧²_ℤ ℤ = 0`. It is an isomorphism as soon as `2`
is invertible in `B`.

This is the linear-algebra content of Remark 08SG, which deduces
`H_k(C, Sym^k ℱ) = ∧^k_B(H_1(C, ℱ))` from the statement that `H_k(C, Sym^k ℱ)` is the
`S_k`-coinvariants of `H_1(C, ℱ)^{⊗ k}` for "the usual action of `S_k` on the tensor product
multiplied by the sign character". The site-theoretic half is in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerQuillenCoinvariants`.

## Main definitions

* `Stacks.SignedTensorPower.signedPermRep`: the sign-twisted permutation representation of
  `S_k` on `M^{⊗ k}`.
* `Stacks.SignedTensorPower.signedCoinvariants`: its coinvariants, that is
  `M^{⊗ k} / ⟨x - sign(σ) • σ(x)⟩`.
* `Stacks.SignedTensorPower.toExteriorPower`: the canonical `B`-linear map from those
  coinvariants to `∧^k_B M`, sending the class of `x_1 ⊗ ⋯ ⊗ x_k` to `x_1 ∧ ⋯ ∧ x_k`.
* `Stacks.SignedTensorPower.equivExteriorPower`: that map as an isomorphism, when `2` is a unit.

## Main results

* `Stacks.SignedTensorPower.signedPermRep_tprod`: the action on a pure tensor is the permutation
  of the factors multiplied by the sign character — the shape of the action asserted by the
  remark.
* `Stacks.SignedTensorPower.toExteriorPower_surjective`,
  `Stacks.SignedTensorPower.toExteriorPower_unique`: the canonical map is surjective and is the
  only linear map sending the class of a pure tensor to the corresponding wedge.
* `Stacks.SignedTensorPower.ker_toExteriorPower`: its kernel is spanned by the classes of the
  pure tensors having two equal entries, and
  `Stacks.SignedTensorPower.two_smul_eq_zero_of_mem_ker`: every element of the kernel is killed
  by `2`.
* `Stacks.SignedTensorPower.exists_equiv_exteriorPower`: **Remark 08SG**, linear-algebra half:
  if `2` is invertible in `B` the coinvariants are isomorphic to `∧^k_B M`, by an isomorphism
  taking the class of `x_1 ⊗ ⋯ ⊗ x_k` to `x_1 ∧ ⋯ ∧ x_k`.
* `Stacks.SignedTensorPower.not_injective_toExteriorPower_int`: over `ℤ`, with `M = ℤ` and
  `k = 2`, the canonical map is not injective, so the hypothesis that `2` be invertible cannot
  be dropped. The nonzero class responsible is
  `Stacks.SignedTensorPower.mk_tprod_one_ne_zero`: over `ℤ`, with `M = ℤ` and `k = 2`, the class
  of `1 ⊗ 1` in the sign-twisted coinvariants is nonzero.
* `Stacks.SignedTensorPower.signedCoinvariantsMap`: the sign-twisted coinvariants are functorial
  in the module.

## Implementation notes

The sign character is what makes `toExteriorPower` well defined: the relation
`x - sign(σ) • σ(x)` is sent to `ιMulti x - sign(σ)² • ιMulti x = 0` because permuting the
arguments of an alternating map multiplies it by the sign. Without the twist the relation
`x - σ(x)` would be sent to `(1 - sign σ) • ιMulti x`, which is not zero.

The kernel is computed by the universal property of the exterior power: the quotient of
`M^{⊗ k}` by the signed relations together with the pure tensors having a repeated entry
receives an alternating map from `M^k`, hence a map from `∧^k_B M` inverting
`toExteriorPower` modulo that span.

## References

* [Stacks Project, Tag 08SG](https://stacks.math.columbia.edu/tag/08SG)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.SignedTensorPower

universe u v

variable (B : Type u) [CommRing B] (M : Type v) [AddCommGroup M] [Module B M] (k : ℕ)

/-- **The usual permutation action of `S_k` on the `k`th tensor power of `M`**: the permutation
`σ` sends `x_1 ⊗ ⋯ ⊗ x_k` to `x_{σ⁻¹(1)} ⊗ ⋯ ⊗ x_{σ⁻¹(k)}`. -/
public def permRep : Representation B (Equiv.Perm (Fin k)) (⨂[B]^k M) where
  toFun σ := (PiTensorProduct.reindex B (fun _ : Fin k => M) σ).toLinearMap
  map_one' := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
      PiTensorProduct.reindex_tprod, Module.End.one_apply]
    rfl
  map_mul' σ τ := by
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
      PiTensorProduct.reindex_tprod, Module.End.mul_apply]
    rfl

/-- The permutation action on a pure tensor: `σ` sends `⨂ i, x i` to `⨂ i, x (σ⁻¹ i)`. -/
@[simp]
public theorem permRep_tprod (σ : Equiv.Perm (Fin k)) (x : Fin k → M) :
    permRep B M k σ (⨂ₜ[B] i, x i) = ⨂ₜ[B] i, x (σ.symm i) := by
  simp [permRep]

/-- **The sign-twisted permutation action of `S_k` on the `k`th tensor power of `M`**: the usual
action `Stacks.SignedTensorPower.permRep` multiplied by the sign character. This is the action
Remark 08SG describes as "the usual action of `S_k` on the tensor product multiplied by the sign
character". -/
public def signedPermRep : Representation B (Equiv.Perm (Fin k)) (⨂[B]^k M) where
  toFun σ := (Equiv.Perm.sign σ : ℤ) • permRep B M k σ
  map_one' := by simp
  map_mul' σ τ := by
    simp only [map_mul, Units.val_mul]
    rw [smul_mul_smul_comm]

/-- The sign-twisted action is the usual permutation action multiplied by the sign character. -/
public theorem signedPermRep_apply (σ : Equiv.Perm (Fin k)) :
    signedPermRep B M k σ = (Equiv.Perm.sign σ : ℤ) • permRep B M k σ := rfl

/-- The sign-twisted action on a pure tensor: `σ` permutes the factors and multiplies by the
sign character. -/
@[simp]
public theorem signedPermRep_tprod (σ : Equiv.Perm (Fin k)) (x : Fin k → M) :
    signedPermRep B M k σ (⨂ₜ[B] i, x i) =
      (Equiv.Perm.sign σ : ℤ) • ⨂ₜ[B] i, x (σ.symm i) := by
  simp [signedPermRep_apply]

/-- The `S_k`-coinvariants of the sign-twisted permutation action on `M^{⊗ k}`, that is the
quotient of `M^{⊗ k}` by the submodule generated by the elements `sign(σ) • σ(x) - x`. -/
public abbrev signedCoinvariants := Representation.Coinvariants (signedPermRep B M k)

/-- The multilinear lift of `exteriorPower.ιMulti` is invariant under the sign-twisted
permutation action: this is where the sign character is used, the two signs cancelling because
permuting the arguments of an alternating map multiplies it by the sign. -/
public theorem lift_ιMulti_comp (σ : Equiv.Perm (Fin k)) :
    (PiTensorProduct.lift (exteriorPower.ιMulti B k).toMultilinearMap) ∘ₗ
        signedPermRep B M k σ =
      PiTensorProduct.lift (exteriorPower.ιMulti B k).toMultilinearMap := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
    signedPermRep_tprod, map_zsmul, PiTensorProduct.lift.tprod,
    AlternatingMap.coe_multilinearMap]
  rw [show (fun i => x (σ.symm i)) = x ∘ σ.symm from rfl,
    (exteriorPower.ιMulti B k).map_perm x σ.symm, Units.smul_def, smul_smul,
    Equiv.Perm.sign_symm]
  norm_num

/-- The canonical `B`-linear map from the sign-twisted coinvariants of `M^{⊗ k}` to the exterior
power `∧^k_B M`, taking the class of `x_1 ⊗ ⋯ ⊗ x_k` to `x_1 ∧ ⋯ ∧ x_k`. It is well defined
precisely because the action is twisted by the sign character. -/
public def toExteriorPower : signedCoinvariants B M k →ₗ[B] ⋀[B]^k M :=
  Representation.Coinvariants.lift _
    (PiTensorProduct.lift (exteriorPower.ιMulti B k).toMultilinearMap)
    (lift_ιMulti_comp B M k)

/-- The canonical map sends the class of `x_1 ⊗ ⋯ ⊗ x_k` to `x_1 ∧ ⋯ ∧ x_k`. -/
@[simp]
public theorem toExteriorPower_mk_tprod (x : Fin k → M) :
    toExteriorPower B M k (Representation.Coinvariants.mk _ (⨂ₜ[B] i, x i)) =
      exteriorPower.ιMulti B k x := by
  simp [toExteriorPower]

/-- The canonical map onto the exterior power is surjective. -/
public theorem toExteriorPower_surjective : Function.Surjective (toExteriorPower B M k) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff,
    ← exteriorPower.ιMulti_span (R := B) (n := k) (M := M), Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact ⟨_, toExteriorPower_mk_tprod B M k x⟩

/-- `toExteriorPower` is the unique linear map taking the class of a pure tensor to the
corresponding wedge product. -/
public theorem toExteriorPower_unique (φ : signedCoinvariants B M k →ₗ[B] ⋀[B]^k M)
    (hφ : ∀ x : Fin k → M,
      φ (Representation.Coinvariants.mk _ (⨂ₜ[B] i, x i)) = exteriorPower.ιMulti B k x) :
    φ = toExteriorPower B M k :=
  Representation.Coinvariants.hom_ext <| PiTensorProduct.ext <|
    MultilinearMap.ext fun x => (hφ x).trans (toExteriorPower_mk_tprod B M k x).symm

section Functoriality

variable {N : Type v} [AddCommGroup N] [Module B N]

/-- **The sign-twisted coinvariants are functorial in the module**: a `B`-linear map
`f : M →ₗ[B] N` induces a `B`-linear map of sign-twisted coinvariants, taking the class of
`x_1 ⊗ ⋯ ⊗ x_k` to the class of `f(x_1) ⊗ ⋯ ⊗ f(x_k)`. It is well defined because the tensor
power of `f` is equivariant for the permutation action and the sign character is untouched. -/
public def signedCoinvariantsMap (f : M →ₗ[B] N) :
    signedCoinvariants B M k →ₗ[B] signedCoinvariants B N k :=
  Representation.Coinvariants.lift _
    ((Representation.Coinvariants.mk (signedPermRep B N k)).comp
      (PiTensorProduct.map (fun _ : Fin k => f)))
    (by
      intro σ
      refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
      simpa only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
        signedPermRep_tprod, map_zsmul, PiTensorProduct.map_tprod] using
        Representation.Coinvariants.mk_self_apply (signedPermRep B N k) σ (⨂ₜ[B] i, f (x i)))

/-- The map induced by `f` sends the class of `x_1 ⊗ ⋯ ⊗ x_k` to the class of
`f(x_1) ⊗ ⋯ ⊗ f(x_k)`. -/
@[simp]
public theorem signedCoinvariantsMap_mk_tprod (f : M →ₗ[B] N) (x : Fin k → M) :
    signedCoinvariantsMap B M k f (Representation.Coinvariants.mk _ (⨂ₜ[B] i, x i)) =
      Representation.Coinvariants.mk (signedPermRep B N k) (⨂ₜ[B] i, f (x i)) := by
  simp [signedCoinvariantsMap]

end Functoriality

/-- The pure tensors of `M^{⊗ k}` having two equal entries in distinct slots. -/
public def diagonalTprod : Set (⨂[B]^k M) :=
  {y | ∃ (x : Fin k → M) (i j : Fin k), i ≠ j ∧ x i = x j ∧ y = ⨂ₜ[B] a, x a}

private theorem comp_swap_eq_self {α : Type*} {n : ℕ} {x : Fin n → α} {i j : Fin n}
    (hx : x i = x j) : x ∘ Equiv.swap i j = x := by
  funext a
  rcases eq_or_ne a i with rfl | ha
  · simp [hx]
  rcases eq_or_ne a j with rfl | hb
  · simp [Equiv.swap_apply_right, hx]
  · simp [Equiv.swap_apply_of_ne_of_ne ha hb]

/-- The class of a pure tensor with two equal entries is killed by `2`: the transposition of the
two slots fixes the tensor, so the sign twist identifies its class with its own negative. -/
public theorem two_smul_mk_tprod_of_eq (x : Fin k → M) {i j : Fin k} (hij : i ≠ j)
    (hx : x i = x j) :
    (2 : B) • Representation.Coinvariants.mk (signedPermRep B M k) (⨂ₜ[B] a, x a) = 0 := by
  have h1 : signedPermRep B M k (Equiv.swap i j) (⨂ₜ[B] a, x a) = -(⨂ₜ[B] a, x a) := by
    rw [signedPermRep_tprod, Equiv.symm_swap, Equiv.Perm.sign_swap hij,
      show (fun a => x (Equiv.swap i j a)) = x ∘ Equiv.swap i j from rfl,
      comp_swap_eq_self hx]
    norm_num
  have h2 : -Representation.Coinvariants.mk (signedPermRep B M k) (⨂ₜ[B] a, x a) =
      Representation.Coinvariants.mk (signedPermRep B M k) (⨂ₜ[B] a, x a) := by
    rw [← map_neg, ← h1]
    exact Representation.Coinvariants.mk_self_apply _ _ _
  rw [two_smul]
  exact neg_eq_iff_add_eq_zero.mp h2

/-- The kernel of the canonical map onto the exterior power is spanned by the classes of the
pure tensors having two equal entries. -/
public theorem ker_toExteriorPower :
    LinearMap.ker (toExteriorPower B M k) =
      Submodule.span B
        (Representation.Coinvariants.mk (signedPermRep B M k) '' diagonalTprod B M k) := by
  set P := Submodule.span B
    (Representation.Coinvariants.mk (signedPermRep B M k) '' diagonalTprod B M k)
  apply le_antisymm
  · intro y hy
    let A : M [⋀^Fin k]→ₗ[B] (signedCoinvariants B M k ⧸ P) :=
      { (P.mkQ ∘ₗ Representation.Coinvariants.mk (signedPermRep B M k)).compMultilinearMap
          (PiTensorProduct.tprod B) with
        map_eq_zero_of_eq' := fun x i j hx hij => (Submodule.Quotient.mk_eq_zero _).mpr
          (Submodule.subset_span ⟨_, ⟨x, i, j, hij, hx, rfl⟩, rfl⟩) }
    have hg : (exteriorPower.alternatingMapLinearEquiv A) ∘ₗ toExteriorPower B M k = P.mkQ := by
      apply Representation.Coinvariants.hom_ext
      apply PiTensorProduct.ext
      refine MultilinearMap.ext fun x => ?_
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
        toExteriorPower_mk_tprod, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      rfl
    have hy' := LinearMap.congr_fun hg y
    rw [LinearMap.coe_comp, Function.comp_apply, hy, map_zero] at hy'
    exact (Submodule.Quotient.mk_eq_zero _).mp hy'.symm
  · rw [Submodule.span_le]
    rintro _ ⟨y, ⟨x, i, j, hij, hx, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, toExteriorPower_mk_tprod]
    exact (exteriorPower.ιMulti B k).map_eq_zero_of_eq x hx hij

/-- Every element of the kernel of the canonical map onto the exterior power is killed by `2`:
the discrepancy between the sign-twisted coinvariants and the exterior power is `2`-torsion. -/
public theorem two_smul_eq_zero_of_mem_ker {y : signedCoinvariants B M k}
    (hy : toExteriorPower B M k y = 0) : (2 : B) • y = 0 := by
  rw [← LinearMap.mem_ker, ker_toExteriorPower] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨_, ⟨x, i, j, hij, hx, rfl⟩, rfl⟩ := hz
      exact two_smul_mk_tprod_of_eq B M k x hij hx
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add, ha, hb, add_zero]
  | smul c a _ ha => rw [smul_comm, ha, smul_zero]

/-- If `2` is invertible in `B`, the sign-twisted coinvariants of `M^{⊗ k}` are the exterior
power `∧^k_B M`. -/
public def equivExteriorPower (h2 : IsUnit (2 : B)) :
    signedCoinvariants B M k ≃ₗ[B] ⋀[B]^k M :=
  LinearEquiv.ofBijective (toExteriorPower B M k)
    ⟨(injective_iff_map_eq_zero _).mpr fun _ hy =>
        h2.smul_eq_zero.mp (two_smul_eq_zero_of_mem_ker B M k hy),
      toExteriorPower_surjective B M k⟩

/-- **Remark 08SG, linear-algebra half.** If `2` is invertible in `B`, the `S_k`-coinvariants of
the sign-twisted permutation action on `M^{⊗ k}` are isomorphic to the exterior power
`∧^k_B M`, by the isomorphism taking the class of `x_1 ⊗ ⋯ ⊗ x_k` to `x_1 ∧ ⋯ ∧ x_k`.

Without a hypothesis on `2` the map is still surjective with `2`-torsion kernel
(`Stacks.SignedTensorPower.toExteriorPower_surjective`,
`Stacks.SignedTensorPower.two_smul_eq_zero_of_mem_ker`), but not injective in general
(`Stacks.SignedTensorPower.not_injective_toExteriorPower_int`). -/
public theorem exists_equiv_exteriorPower (h2 : IsUnit (2 : B)) :
    ∃ e : signedCoinvariants B M k ≃ₗ[B] ⋀[B]^k M,
      ∀ x : Fin k → M,
        e (Representation.Coinvariants.mk (signedPermRep B M k) (⨂ₜ[B] i, x i)) =
          exteriorPower.ιMulti B k x :=
  ⟨equivExteriorPower B M k h2, toExteriorPower_mk_tprod B M k⟩

section Integers

private def modTwoMultilinear :
    MultilinearMap ℤ (fun _ : Fin 2 => ℤ) (ZMod 2) :=
  (MultilinearMap.mkPiAlgebra ℤ (Fin 2) (ZMod 2)).compLinearMap
    fun _ => (Int.castRingHom (ZMod 2)).toAddMonoidHom.toIntLinearMap

private theorem modTwoMultilinear_apply (x : Fin 2 → ℤ) :
    modTwoMultilinear x = ∏ i, (x i : ZMod 2) := by
  simp [modTwoMultilinear]

private def modTwo : signedCoinvariants ℤ ℤ 2 →ₗ[ℤ] ZMod 2 :=
  Representation.Coinvariants.lift _ (PiTensorProduct.lift modTwoMultilinear) (by
    intro σ
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      signedPermRep_tprod, map_zsmul, PiTensorProduct.lift.tprod, modTwoMultilinear_apply]
    rw [show (∏ i, ((x (σ.symm i) : ℤ) : ZMod 2)) = ∏ i, ((x i : ℤ) : ZMod 2) from
      Equiv.prod_comp σ.symm fun i => ((x i : ℤ) : ZMod 2)]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;>
      simp [show ∀ z : ZMod 2, -z = z by decide])

/-- **Over `ℤ`, the sign-twisted coinvariants of `ℤ^{⊗ 2}` are not zero**: the class of `1 ⊗ 1`
is nonzero there, those coinvariants being `ℤ/2`, as the reduction `modTwo` detects. -/
public theorem mk_tprod_one_ne_zero :
    Representation.Coinvariants.mk (signedPermRep ℤ ℤ 2) (⨂ₜ[ℤ] _ : Fin 2, (1 : ℤ)) ≠ 0 := by
  intro h1
  have h3 : modTwo (Representation.Coinvariants.mk (signedPermRep ℤ ℤ 2)
      (⨂ₜ[ℤ] _ : Fin 2, (1 : ℤ))) = 1 := by
    change PiTensorProduct.lift modTwoMultilinear (⨂ₜ[ℤ] _ : Fin 2, (1 : ℤ)) = 1
    rw [PiTensorProduct.lift.tprod, modTwoMultilinear_apply]
    simp
  rw [h1, map_zero] at h3
  exact zero_ne_one h3

/-- Over `ℤ`, the canonical map from the sign-twisted coinvariants of `ℤ^{⊗ 2}` to `∧²_ℤ ℤ` is
not injective: the coinvariants are `ℤ/2` and the exterior square is `0`. So the identification
of Remark 08SG does require `2` to be invertible. -/
public theorem not_injective_toExteriorPower_int :
    ¬ Function.Injective (toExteriorPower ℤ ℤ 2) := by
  intro hinj
  have h0 : toExteriorPower ℤ ℤ 2
      (Representation.Coinvariants.mk (signedPermRep ℤ ℤ 2) (⨂ₜ[ℤ] _ : Fin 2, (1 : ℤ))) = 0 := by
    rw [toExteriorPower_mk_tprod]
    exact (exteriorPower.ιMulti ℤ 2).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  exact mk_tprod_one_ne_zero (hinj (by rw [h0, map_zero]))

end Integers

end Stacks.SignedTensorPower

end
