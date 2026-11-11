module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CompletedDeRhamNilpotentReduction
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeBaseChangeRows

/-!
# Reductions of the base-change connections are determined by the degree zero

Let `E` be a cosimplicial divided power algebra with completed rings `D(b)`, let `V` be a
cosimplicial module over them with modules `M(b)`, let `∇` be a completed connection on `M(0)`,
and let `∇_b` be the connection on `M(b)` obtained from `∇` by base change along the coprojection
`σ_b : ⦋0⦌ ⟶ ⦋b⦌` (`Crystalline.CosimplicialCompletedModule.baseChangeConnection`).

Suppose `p` is nilpotent in every `D(b)`, and that `M(b)` is reduced, along a ring map
`θ_b : D(b) → R'_b`, a semilinear map `λ_b : M(b) → N'_b` and a semilinear map of forms
`Θ_b : Ω^1_{D(b)} → Ω'_b`, to a module `N'_b` carrying an additive map
`∇'_b : N'_b → N'_b ⊗ Ω'_b` satisfying a Leibniz rule.  This file proves that if the reduction
of `∇` is `∇'_0`, the reductions are compatible with `σ_b` and the `∇'_b` are compatible with
`σ_b`, then the reduction of every `∇_b` is `∇'_b`: this is the hypothesis `hnabla` of
`Crystalline.FormsData.ConnModule.reduceComplexHom` in every cosimplicial degree.

## Main results

* `Crystalline.reduceTensor_smul` — `reduceTensor` is semilinear over `θ`.
* `Crystalline.reduceTensor_connection_of_span` — the reduction of a completed connection is a
  given Leibniz map as soon as it is so on a set spanning the module.
* `Crystalline.CosimplicialCompletedModule.span_range_map_coprojection` — when `p` is nilpotent
  in `D(b)`, the image of `M(0)` under `σ_b` spans `M(b)` over `D(b)`.
* `Crystalline.CosimplicialCompletedModule.reduceTensor_tensorMap` — the reductions are natural
  along a cosimplicial map.
* `Crystalline.CosimplicialCompletedModule.reduceTensor_baseChangeConnection` — the main result,
  and `Crystalline.CosimplicialCompletedModule.reduceTensor_baseChangePair_nabla`, the same for
  the connections of `Crystalline.CosimplicialCompletedModule.baseChangePair`.

The rings `R'_b`, the modules `N'_b`, `Ω'_b`, the maps `θ_b`, `λ_b`, `Θ_b`, `∇'_b` and the
compatibility maps are data and hypotheses: nothing here constructs them.
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers Simplicial
open scoped TensorProduct

universe u v

namespace Crystalline

section Reduce

variable {p : ℕ} {D : Type*} [CommRing D] {R' : Type*} [CommRing R'] (θ : D →+* R')
  (hpk : ∃ k : ℕ, (p : D) ^ k = 0)
  {M X : Type*} [AddCommGroup M] [Module D M] [AddCommGroup X] [Module D X]
  {N Y : Type*} [AddCommGroup N] [Module R' N] [AddCommGroup Y] [Module R' Y]

/-- **`reduceTensor` is semilinear over `θ`**: the reduction of `x • z` is `θ x` times the
reduction of `z`. -/
theorem reduceTensor_smul (lam : M →ₛₗ[θ] N) (Φ : X →ₛₗ[θ] Y) (x : D)
    (z : CompletedTensor p D X M) :
    reduceTensor θ hpk lam Φ (x • z) = θ x • reduceTensor θ hpk lam Φ z := by
  have h := completedTensor_addMonoidHom_ext_of_pow_eq_zero hpk
    (f := (reduceTensor θ hpk lam Φ).comp (DistribSMul.toAddMonoidHom _ x))
    (g := (DistribSMul.toAddMonoidHom _ (θ x)).comp (reduceTensor θ hpk lam Φ))
    fun m ω ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply,
        DistribSMul.toAddMonoidHom_apply, ← map_smul, TensorProduct.smul_tmul',
        reduceTensor_of_tmul, map_smulₛₗ]
  exact DFunLike.congr_fun h z

/-- **The reduction of a completed connection is determined on generators**: if `∇'` on `N`
satisfies the Leibniz rule `∇'(r n) = r ∇' n + n ⊗ d' r`, the reduction `Θ` of the forms
carries `d` to `d'`, and the reduction of `∇ m` is `∇' (λ m)` for every `m` in a set `G`
spanning `M`, then it is so for every `m`. -/
theorem reduceTensor_connection_of_span {Ω : Type*} [AddCommGroup Ω] [Module D Ω] {d : D → Ω}
    (nabla : CompletedConnection p D Ω d M) (lam : M →ₛₗ[θ] N) (Θ1 : Ω →ₛₗ[θ] Y)
    (nablaK : N →+ N ⊗[R'] Y) (dK : R' → Y)
    (hleib : ∀ (r : R') (n : N), nablaK (r • n) = r • nablaK n + n ⊗ₜ dK r)
    (hd : ∀ x, Θ1 (d x) = dK (θ x)) (G : Set M) (hspan : Submodule.span D G = ⊤)
    (hG : ∀ m ∈ G, nablaK (lam m) = reduceTensor θ hpk lam Θ1 (nabla m)) (m : M) :
    nablaK (lam m) = reduceTensor θ hpk lam Θ1 (nabla m) := by
  have hmem : m ∈ Submodule.span D G := hspan ▸ Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem x hx => exact hG x hx
  | zero =>
    have h0 : nabla 0 = 0 := by
      have := nabla.map_add 0 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    rw [map_zero, map_zero, h0, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, nabla.map_add, map_add, hx, hy]
  | smul c x _ hx =>
    rw [map_smulₛₗ, hleib, hx, nabla.leibniz, map_add, reduceTensor_smul, reduceTensor_of_tmul,
      hd]

end Reduce

namespace CosimplicialCompletedModule

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}

section Generation

variable (V : CosimplicialCompletedModule.{u, v, v} E p)
  (beta : ∀ b : ℕ, letI := E.coprojectionAlgebra p b
    CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E.completedRing p b)
      (V.carrier 0) ≃ₗ[E.completedRing p b] V.carrier b)
  (hbeta : ∀ (b : ℕ) (x : E.completedRing p b) (m : V.carrier 0),
    letI := E.coprojectionAlgebra p b
    beta b (AdicCompletion.of (pAdicIdeal (A := E.completedRing p b) p)
        (E.completedRing p b ⊗[E.completedRing p 0] V.carrier 0) (x ⊗ₜ[E.completedRing p 0] m)) =
      x • V.map (CosimplicialDPAlgebra.coprojection b) m)

include hbeta in
/-- **The image of `M(0)` spans `M(b)`** when `p` is nilpotent in `D(b)`: then
`(D(b) ⊗_{D(0)} M(0))^∧ = D(b) ⊗_{D(0)} M(0)` is spanned by the pure tensors `x ⊗ m`, which
`β_b` carries to `x • σ_b m`. -/
theorem span_range_map_coprojection (b : ℕ) (hpk : ∃ k : ℕ, (p : E.completedRing p b) ^ k = 0) :
    Submodule.span (E.completedRing p b)
      (Set.range (V.map (CosimplicialDPAlgebra.coprojection b))) = ⊤ := by
  let := E.coprojectionAlgebra p b
  refine Submodule.eq_top_iff'.mpr fun y ↦ ?_
  obtain ⟨x, rfl⟩ := (beta b).surjective y
  obtain ⟨t, rfl⟩ := (ofLinearEquivOfPowEqZero hpk
    (E.completedRing p b ⊗[E.completedRing p 0] V.carrier 0)).surjective x
  rw [ofLinearEquivOfPowEqZero_apply]
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | tmul c m =>
    rw [hbeta]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨m, rfl⟩)
  | add s t hs ht => rw [map_add, map_add]; exact Submodule.add_mem _ hs ht

end Generation

section Naturality

variable (V : CosimplicialCompletedModule.{u, v, v} E p)

/-- **The reductions are natural along a cosimplicial map `φ : m ⟶ n`**: if `λ_n ∘ M(φ) = ρ ∘ λ_m`
and `Θ_n ∘ Ω(φ) = ρ_Ω ∘ Θ_m`, and `Ψ` is `ρ ⊗ ρ_Ω` on pure tensors, then the reduction of the
transition `M(φ)_*` of the completed tensors `M ⊗̂ Ω^a` is `Ψ` of the reduction, in every
exterior degree `a`. -/
theorem reduceTensor_tensorMap {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ)
    {Rm Nm Om Rn Nn On : Type*} [CommRing Rm] [AddCommGroup Nm] [Module Rm Nm] [AddCommGroup Om]
    [Module Rm Om] [CommRing Rn] [AddCommGroup Nn] [Module Rn Nn] [AddCommGroup On] [Module Rn On]
    (θm : E.completedRing p m.len →+* Rm) (θn : E.completedRing p n.len →+* Rn)
    (hpkm : ∃ k : ℕ, (p : E.completedRing p m.len) ^ k = 0)
    (hpkn : ∃ k : ℕ, (p : E.completedRing p n.len) ^ k = 0)
    (lamm : V.carrier m.len →ₛₗ[θm] Nm) (lamn : V.carrier n.len →ₛₗ[θn] Nn)
    (Θm : E.forms p a m.len →ₛₗ[θm] Om) (Θn : E.forms p a n.len →ₛₗ[θn] On)
    (Ψ : Nm ⊗[Rm] Om →+ Nn ⊗[Rn] On) (ρ : Nm →+ Nn) (ρΩ : Om →+ On)
    (hΨ : ∀ x ω, Ψ (x ⊗ₜ ω) = ρ x ⊗ₜ ρΩ ω) (hlam : ∀ x, lamn (V.map φ x) = ρ (lamm x))
    (hΘ : ∀ ω, Θn (E.formsMap p φ a ω) = ρΩ (Θm ω)) (z : V.obj a m.len) :
    reduceTensor θn hpkn lamn Θn (V.tensorMap φ a z) = Ψ (reduceTensor θm hpkm lamm Θm z) := by
  have h := completedTensor_addMonoidHom_ext_of_pow_eq_zero hpkm
    (f := (reduceTensor θn hpkn lamn Θn).comp (V.tensorMap φ a).toAddMonoidHom)
    (g := Ψ.comp (reduceTensor θm hpkm lamm Θm)) fun x ω ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
        tensorMap_of_tmul, reduceTensor_of_tmul, hΨ, hlam, hΘ]
  exact DFunLike.congr_fun h z

end Naturality

section Main

variable (V : CosimplicialCompletedModule.{u, v, v} E p)
  (nabla : CompletedConnection p (E.completedRing p 0) (E.forms p 1 0) (E.differential p 0)
    (V.carrier 0))
  (beta : ∀ b : ℕ, letI := E.coprojectionAlgebra p b
    CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E.completedRing p b)
      (V.carrier 0) ≃ₗ[E.completedRing p b] V.carrier b)
  (hbeta : ∀ (b : ℕ) (x : E.completedRing p b) (m : V.carrier 0),
    letI := E.coprojectionAlgebra p b
    beta b (AdicCompletion.of (pAdicIdeal (A := E.completedRing p b) p)
        (E.completedRing p b ⊗[E.completedRing p 0] V.carrier 0) (x ⊗ₜ[E.completedRing p 0] m)) =
      x • V.map (CosimplicialDPAlgebra.coprojection b) m)

include hbeta in
/-- **The reduction of the base-change connection `∇_b` is `∇'_b`.**  Given the reductions
`(θ_0, λ_0, Θ_0)` of the degree zero and `(θ_b, λ_b, Θ_b)` of the degree `b`, with `p` nilpotent
in `D(0)` and `D(b)`: if the reduction of `∇` is `∇'_0`, the reductions are compatible with the
coprojection `σ_b` through `ρ`, `ρ_Ω` and `Ψ = ρ ⊗ ρ_Ω`, `∇'_b` satisfies the Leibniz rule over
a differential `d'_b` compatible with `Θ_b`, and `∇'_b ∘ ρ = Ψ ∘ ∇'_0`, then the reduction of
`∇_b` is `∇'_b`. -/
theorem reduceTensor_baseChangeConnection (b : ℕ)
    {R0 N0 Om0 Rb Nb Omb : Type*} [CommRing R0] [AddCommGroup N0] [Module R0 N0]
    [AddCommGroup Om0] [Module R0 Om0] [CommRing Rb] [AddCommGroup Nb] [Module Rb Nb]
    [AddCommGroup Omb] [Module Rb Omb]
    (θ0 : E.completedRing p 0 →+* R0) (hpk0 : ∃ k : ℕ, (p : E.completedRing p 0) ^ k = 0)
    (lam0 : V.carrier 0 →ₛₗ[θ0] N0) (Θ0 : E.forms p 1 0 →ₛₗ[θ0] Om0)
    (nablaK0 : N0 →+ N0 ⊗[R0] Om0)
    (hnabla0 : ∀ m, nablaK0 (lam0 m) = reduceTensor θ0 hpk0 lam0 Θ0 (nabla m))
    (θb : E.completedRing p b →+* Rb) (hpkb : ∃ k : ℕ, (p : E.completedRing p b) ^ k = 0)
    (lamb : V.carrier b →ₛₗ[θb] Nb) (Θb : E.forms p 1 b →ₛₗ[θb] Omb)
    (nablaKb : Nb →+ Nb ⊗[Rb] Omb) (dKb : Rb → Omb)
    (hleibb : ∀ (r : Rb) (n : Nb), nablaKb (r • n) = r • nablaKb n + n ⊗ₜ dKb r)
    (hdb : ∀ x, Θb (E.differential p b x) = dKb (θb x))
    (Ψ : N0 ⊗[R0] Om0 →+ Nb ⊗[Rb] Omb) (ρ : N0 →+ Nb) (ρΩ : Om0 →+ Omb)
    (hΨ : ∀ x ω, Ψ (x ⊗ₜ ω) = ρ x ⊗ₜ ρΩ ω)
    (hlam : ∀ x, lamb (V.map (CosimplicialDPAlgebra.coprojection b) x) = ρ (lam0 x))
    (hΘ : ∀ ω, Θb (E.formsMap p (CosimplicialDPAlgebra.coprojection b) 1 ω) = ρΩ (Θ0 ω))
    (hnablaK : ∀ x, nablaKb (ρ x) = Ψ (nablaK0 x)) (y : V.carrier b) :
    nablaKb (lamb y) = reduceTensor θb hpkb lamb Θb (V.baseChangeConnection nabla beta b y) := by
  refine reduceTensor_connection_of_span θb hpkb (V.baseChangeConnection nabla beta b) lamb Θb
    nablaKb dKb hleibb hdb _ (V.span_range_map_coprojection beta hbeta b hpkb) ?_ y
  rintro _ ⟨x, rfl⟩
  rw [V.baseChangeConnection_map_coprojection nabla beta hbeta b x,
    V.reduceTensor_tensorMap (CosimplicialDPAlgebra.coprojection b) 1 θ0 θb hpk0 hpkb lam0 lamb Θ0
      Θb Ψ ρ ρΩ hΨ hlam hΘ, ← hnabla0, ← hnablaK, hlam]

end Main

section Pair

variable {E' : CosimplicialDPAlgebra.{u, u} A} (V : CosimplicialCompletedModule.{u, u, u} E' p)
  (nabla : CompletedConnection p (E'.completedRing p 0) (E'.forms p 1 0) (E'.differential p 0)
    (V.carrier 0))
  (beta : ∀ b : ℕ, letI := E'.coprojectionAlgebra p b
    CompletedConnection.baseChangeCarrier p (E'.completedRing p 0) (E'.completedRing p b)
      (V.carrier 0) ≃ₗ[E'.completedRing p b] V.carrier b)
  (hbeta : ∀ (b : ℕ) (x : E'.completedRing p b) (m : V.carrier 0),
    letI := E'.coprojectionAlgebra p b
    beta b (AdicCompletion.of (pAdicIdeal (A := E'.completedRing p b) p)
        (E'.completedRing p b ⊗[E'.completedRing p 0] V.carrier 0)
        (x ⊗ₜ[E'.completedRing p 0] m)) =
      x • V.map (CosimplicialDPAlgebra.coprojection b) m)
  (hδ : ∀ x : V.carrier 0,
    V.baseChangeConnection nabla beta 1 (V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) x) =
      V.tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1 (nabla x))
  (hint : CompletedDeRham.HasIntegrableConnection p (E'.completedRing p 0)
    (fun a => E'.forms p a 0) (E'.wedge p 0) (E'.deRham p 0) (V.carrier 0) nabla
    (E'.isGradedLeibniz p 0))

/-- **The reduction of the connection of `baseChangePair` in degree `b` is `∇'_b`**, under the
hypotheses of `Crystalline.CosimplicialCompletedModule.reduceTensor_baseChangeConnection`. -/
theorem reduceTensor_baseChangePair_nabla (b : ℕ)
    {R0 N0 Om0 Rb Nb Omb : Type*} [CommRing R0] [AddCommGroup N0] [Module R0 N0]
    [AddCommGroup Om0] [Module R0 Om0] [CommRing Rb] [AddCommGroup Nb] [Module Rb Nb]
    [AddCommGroup Omb] [Module Rb Omb]
    (θ0 : E'.completedRing p 0 →+* R0) (hpk0 : ∃ k : ℕ, (p : E'.completedRing p 0) ^ k = 0)
    (lam0 : V.carrier 0 →ₛₗ[θ0] N0) (Θ0 : E'.forms p 1 0 →ₛₗ[θ0] Om0)
    (nablaK0 : N0 →+ N0 ⊗[R0] Om0)
    (hnabla0 : ∀ m, nablaK0 (lam0 m) = reduceTensor θ0 hpk0 lam0 Θ0 (nabla m))
    (θb : E'.completedRing p b →+* Rb) (hpkb : ∃ k : ℕ, (p : E'.completedRing p b) ^ k = 0)
    (lamb : V.carrier b →ₛₗ[θb] Nb) (Θb : E'.forms p 1 b →ₛₗ[θb] Omb)
    (nablaKb : Nb →+ Nb ⊗[Rb] Omb) (dKb : Rb → Omb)
    (hleibb : ∀ (r : Rb) (n : Nb), nablaKb (r • n) = r • nablaKb n + n ⊗ₜ dKb r)
    (hdb : ∀ x, Θb (E'.differential p b x) = dKb (θb x))
    (Ψ : N0 ⊗[R0] Om0 →+ Nb ⊗[Rb] Omb) (ρ : N0 →+ Nb) (ρΩ : Om0 →+ Omb)
    (hΨ : ∀ x ω, Ψ (x ⊗ₜ ω) = ρ x ⊗ₜ ρΩ ω)
    (hlam : ∀ x, lamb (V.map (CosimplicialDPAlgebra.coprojection b) x) = ρ (lam0 x))
    (hΘ : ∀ ω, Θb (E'.formsMap p (CosimplicialDPAlgebra.coprojection b) 1 ω) = ρΩ (Θ0 ω))
    (hnablaK : ∀ x, nablaKb (ρ x) = Ψ (nablaK0 x)) (y : V.carrier b) :
    nablaKb (lamb y) = reduceTensor θb hpkb lamb Θb
      ((V.baseChangePair nabla beta hbeta hδ hint).nabla b y) := by
  rw [baseChangePair_nabla]
  exact V.reduceTensor_baseChangeConnection nabla beta hbeta b θ0 hpk0 lam0 Θ0 nablaK0 hnabla0
    θb hpkb lamb Θb nablaKb dKb hleibb hdb Ψ ρ ρΩ hΨ hlam hΘ hnablaK y

end Pair

end CosimplicialCompletedModule

end Crystalline
