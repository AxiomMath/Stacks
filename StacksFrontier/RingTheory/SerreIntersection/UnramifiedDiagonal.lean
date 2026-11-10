module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.FreeMap
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.SerreIntersection.FlatLocalTransfer
public import StacksFrontier.RingTheory.SerreIntersection.PowerSeriesSerre
public import StacksFrontier.RingTheory.SerreIntersection.QuotientChangeOfRings

/-!
# The diagonal of a power series ring over a discrete valuation ring

Let `Λ` be a regular local ring of dimension one with maximal ideal `(ϖ)`, that is a discrete
valuation ring with uniformizer `ϖ`, and let `R = Λ[[x_1, …, x_n]]`, `B = Λ[[y, x]]`. This file
carries the reduction to the diagonal of `StacksFrontier.RingTheory.SerreIntersection.DiagonalTor`
over from a field to `Λ`, for modules on which `ϖ` is a nonzerodivisor.

* For a finite `R`-module `M` on which `ϖ` is a nonzerodivisor the base change `B ⊗_{R, x} M` is
  flat over `R` through `y` (`flat_twist_ext_left_of_isSMulRegular`): along a free cover the
  contraction `B → R`, `y ↦ 0`, reduces this to the injectivity of `K / ϖ K → R^j / ϖ R^j` for the
  kernel `K` of the cover, which is the `ϖ`-torsion freeness of `M`.
* Reduction modulo `ϖ` maps the complete tensor product `(B ⊗_R M) ⊗_R N` onto the complete
  tensor product over the residue field `k` of the reductions `k[[x]] ⊗_R M` and
  `k[[x]] ⊗_R N` (`pairReduce`, `pairReduce_surjective`).
* Hence for `ϖ`-torsion free `M`, `N` with `M ⊗_R N` supported in the closed point,
  `dim M + dim N ≤ dim R` and the Euler characteristic `χ(M, N)` is positive when equality holds
  (`supportDim_add_supportDim_le_and_pos_of_isSMulRegular`).
* **Serre's dimension inequality over `R`**, for all nonzero finite `M`, `N` with `M ⊗_R N`
  supported in the closed point (`supportDim_add_supportDim_le_of_mvPowerSeries`): reduce to
  `R ⧸ 𝔭`, `R ⧸ 𝔮` for top-dimensional points of the supports; if `ϖ` lies in one of them use the
  inequality over `k[[x]]` (`supportDim_quotSMulTop_add_le`), otherwise the torsion free case.
* **Serre's positivity over `R` for two primes**
  (`torEulerCharacteristic_quotient_pos_of_mvPowerSeries`): `χ(R ⧸ 𝔭, R ⧸ 𝔮) > 0` when
  `dim R ⧸ 𝔭 + dim R ⧸ 𝔮 = dim R`, using the change of rings `χ^R(M, N) = χ^{k[[x]]}(M, N / ϖ N)`
  of `QuotientChangeOfRings` when `ϖ ∈ 𝔭`.
-/

@[expose] public noncomputable section

open MvPowerSeries IsLocalRing Stacks.CompleteLocalRing.RegularSubring
open scoped TensorProduct Pointwise

universe u

namespace Stacks.SerreIntersection.PowerSeriesDiagonal

section Uniformizer

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] {ϖ : Λ}
  (hϖ : maximalIdeal Λ = Ideal.span {ϖ}) (n : ℕ)

omit [IsNoetherianRing Λ] in
include hϖ in
/-- Killing the first set of variables after including through the second carries the maximal
ideal of `Λ[[x]]` into `(ϖ)`. -/
theorem killFirst_right_mem (r : MvPowerSeries (Fin n) Λ)
    (hr : r ∈ maximalIdeal (MvPowerSeries (Fin n) Λ)) :
    killFirst Λ n (right Λ n r) ∈ Ideal.span {(C ϖ : MvPowerSeries (Fin n) Λ)} := by
  have hle : maximalIdeal (MvPowerSeries (Fin n) Λ) ≤ Ideal.comap ((killFirst Λ n).comp
      (right Λ n)) (Ideal.span {(C ϖ : MvPowerSeries (Fin n) Λ)}) := by
    rw [maximalIdeal_mvPowerSeries, hϖ]
    refine sup_le ?_ (Ideal.span_le.mpr ?_)
    · rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, Ideal.span_le, Set.singleton_subset_iff,
        SetLike.mem_coe, Ideal.mem_comap]
      change killFirst Λ n (right Λ n (C ϖ)) ∈ _
      have h : killFirst Λ n (right Λ n (C ϖ)) = C ϖ := by
        change killCompl _ (rename _ (C ϖ)) = C ϖ
        rw [rename_C, killCompl_C]
      rw [h]
      exact Ideal.mem_span_singleton_self _
    · rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap]
      change killFirst Λ n (right Λ n (X i)) ∈ _
      have h : killFirst Λ n (right Λ n (X i)) = 0 := by
        change killCompl _ (rename _ (X i)) = 0
        rw [rename_X]
        exact killCompl_X_eq_zero (by simp)
      rw [h]
      exact Ideal.zero_mem _
  exact hle hr

omit [IsNoetherianRing Λ] in
/-- `C ϖ` lies in the maximal ideal of `Λ[[x]]`. -/
theorem C_mem_maximalIdeal {σ : Type*} (hϖ' : ϖ ∈ maximalIdeal Λ) :
    (C ϖ : MvPowerSeries σ Λ) ∈ maximalIdeal (MvPowerSeries σ Λ) := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, constantCoeff_C]
  exact hϖ'

/-- `C a` lies in the maximal ideal of `S[[x]]` when `a` generates the maximal ideal of `S`. -/
private theorem C_mem_maximalIdeal_of_eq_span {S : Type u} [CommRing S] [IsLocalRing S] {a : S}
    {σ : Type*} (h : maximalIdeal S = Ideal.span {a}) :
    (C a : MvPowerSeries σ S) ∈ maximalIdeal (MvPowerSeries σ S) :=
  C_mem_maximalIdeal (h ▸ Ideal.mem_span_singleton_self a)

include hϖ in
/-- **Tor independence over a discrete valuation ring.** For a finite `Λ[[x]]`-module `M` on
which `ϖ` is a nonzerodivisor, the base change `Λ[[y, x]] ⊗_{Λ[[x]]} M` along the inclusion of
the second set of variables is flat over `Λ[[x]]` through the first. -/
theorem flat_twist_ext_left_of_isSMulRegular (M : Type u) [AddCommGroup M]
    [Module (MvPowerSeries (Fin n) Λ) M] [Module.Finite (MvPowerSeries (Fin n) Λ) M]
    (hM : IsSMulRegular M (C ϖ : MvPowerSeries (Fin n) Λ)) :
    Module.Flat (MvPowerSeries (Fin n) Λ) (Twist (right Λ n) (Ext (left Λ n) M)) := by
  refine flat_twist_ext_of_smul_top (left Λ n) (right Λ n) (killFirst Λ n) (killFirst_left Λ n)
    (ker_killFirst_le Λ n) (Ideal.span {(C ϖ : MvPowerSeries (Fin n) Λ)})
    (fun r hr => killFirst_right_mem hϖ n r hr) (fun r hr => ?_) M (fun j p x hx => ?_)
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have h : left Λ n (c * C ϖ) = left Λ n c * right Λ n (C ϖ) := by
      rw [map_mul]
      congr 1
      change rename _ (C ϖ) = rename _ (C ϖ)
      rw [rename_C, rename_C]
    rw [h]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (C_mem_maximalIdeal_of_eq_span hϖ))
  · rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨v, -, hv⟩ := hx
    have hpv : p v = 0 := by
      apply hM
      change C ϖ • p v = C ϖ • (0 : M)
      rw [smul_zero, ← map_smul, hv]
      exact x.2
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨⟨v, hpv⟩, Submodule.mem_top, Subtype.ext hv⟩

end Uniformizer


section Reduction

variable (Λ : Type u) [CommRing Λ] [IsLocalRing Λ] (n : ℕ)

local notation "𝓡" => MvPowerSeries (Fin n) Λ
local notation "𝓑" => MvPowerSeries (Fin n ⊕ Fin n) Λ
local notation "𝓡k" => MvPowerSeries (Fin n) (ResidueField Λ)
local notation "𝓑k" => MvPowerSeries (Fin n ⊕ Fin n) (ResidueField Λ)

/-- Reduction of coefficients is surjective. -/
theorem map_surjective_of_surjective {σ R S : Type*} [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Surjective φ) : Function.Surjective (MvPowerSeries.map (σ := σ) φ) := by
  intro q
  let p : MvPowerSeries σ R := fun e => Function.surjInv hφ (coeff e q)
  refine ⟨p, ?_⟩
  ext e
  rw [coeff_map]
  exact Function.surjInv_eq hφ (coeff e q)

/-- Reduction of coefficients `Λ[[x]] → k[[x]]` is surjective. -/
theorem algebraMap_surjective : Function.Surjective (algebraMap 𝓡 𝓡k) :=
  map_surjective_of_surjective (residue_surjective (R := Λ))

/-- Reduction of coefficients `Λ[[y, x]] → k[[y, x]]` is surjective. -/
theorem algebraMap_sum_surjective : Function.Surjective (algebraMap 𝓑 𝓑k) :=
  map_surjective_of_surjective (residue_surjective (R := Λ))

/-- Reduction of coefficients commutes with the inclusion `left` of `Λ[[x]]` into `Λ[[y, x]]`. -/
theorem algebraMap_left (r : 𝓡) :
    algebraMap 𝓑 𝓑k (left Λ n r) = left (ResidueField Λ) n (algebraMap 𝓡 𝓡k r) :=
  (rename_map _ _ r).symm

/-- Reduction of coefficients commutes with the inclusion `right` of `Λ[[x]]` into `Λ[[y, x]]`. -/
theorem algebraMap_right (r : 𝓡) :
    algebraMap 𝓑 𝓑k (right Λ n r) = right (ResidueField Λ) n (algebraMap 𝓡 𝓡k r) :=
  (rename_map _ _ r).symm

variable {Λ n}

/-- The reduction `B ⊗_{R, x} M → k[[y, x]] ⊗_{k[[x]], x} (k[[x]] ⊗_R M)`,
`b ⊗ m ↦ b̄ ⊗ (1 ⊗ m)`. -/
def extReduce (M : Type u) [AddCommGroup M] [Module 𝓡 M] :
    Ext (left Λ n) M →+ Ext (left (ResidueField Λ) n) (𝓡k ⊗[𝓡] M) :=
  TensorProduct.liftAddHom
    { toFun b :=
        ((TensorProduct.mk 𝓡k (Twist (left (ResidueField Λ) n) 𝓑k) (𝓡k ⊗[𝓡] M)
          (Twist.mk _ (algebraMap 𝓑 𝓑k (@id 𝓑 b)))).toAddMonoidHom).comp
          (TensorProduct.mk 𝓡 𝓡k M 1).toAddMonoidHom
      map_zero' := by
        ext m
        change Twist.mk _ (algebraMap 𝓑 𝓑k 0) ⊗ₜ _ = 0
        rw [map_zero, Twist.mk_zero, TensorProduct.zero_tmul]
      map_add' b b' := by
        ext m
        change Twist.mk _ (algebraMap 𝓑 𝓑k ((@id 𝓑 b) + (@id 𝓑 b'))) ⊗ₜ _ =
          Twist.mk _ (algebraMap 𝓑 𝓑k b) ⊗ₜ _ + Twist.mk _ (algebraMap 𝓑 𝓑k b') ⊗ₜ _
        rw [map_add, ← Twist.mk_add, TensorProduct.add_tmul]
        rfl }
    (fun r b m => by
      change Twist.mk _ (algebraMap 𝓑 𝓑k (left Λ n r * (@id 𝓑 b))) ⊗ₜ
          ((1 : 𝓡k) ⊗ₜ[𝓡] m) =
        Twist.mk _ (algebraMap 𝓑 𝓑k b) ⊗ₜ ((1 : 𝓡k) ⊗ₜ[𝓡] (r • m))
      rw [map_mul, algebraMap_left, ← smul_eq_mul, ← Twist.rsmul_mk, TensorProduct.smul_tmul]
      congr 1
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
        Algebra.smul_def, mul_one])

/-- `extReduce M` sends `b ⊗ m` to `b̄ ⊗ (1 ⊗ m)`. -/
theorem extReduce_tmul (M : Type u) [AddCommGroup M] [Module 𝓡 M] (b : 𝓑) (m : M) :
    extReduce M (Twist.mk (left Λ n) b ⊗ₜ m) =
      Twist.mk _ (algebraMap 𝓑 𝓑k b) ⊗ₜ ((1 : 𝓡k) ⊗ₜ[𝓡] m) := rfl

/-- `extReduce M` is semilinear along the reduction of coefficients `Λ[[y, x]] → k[[y, x]]`. -/
theorem extReduce_smul (M : Type u) [AddCommGroup M] [Module 𝓡 M] (b : 𝓑)
    (z : Ext (left Λ n) M) : extReduce M (b • z) = algebraMap 𝓑 𝓑k b • extReduce M z := by
  induction z using TensorProduct.inductionOn with
  | tmul b' m =>
    obtain ⟨b', rfl⟩ : ∃ c : 𝓑, Twist.mk (left Λ n) c = b' := ⟨b', rfl⟩
    rw [TensorProduct.smul_tmul', Twist.smul_mk, extReduce_tmul, extReduce_tmul,
      TensorProduct.smul_tmul', Twist.smul_mk, smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The reduction of the complete tensor product,
`(B ⊗_{R, x} M) ⊗_{R, y} N → (k[[y, x]] ⊗ (k[[x]] ⊗_R M)) ⊗_{k[[x]]} (k[[x]] ⊗_R N)`. -/
def pairReduceAddHom (M N : Type u) [AddCommGroup M] [Module 𝓡 M] [AddCommGroup N] [Module 𝓡 N] :
    Pair (left Λ n) (right Λ n) M N →+
      Pair (left (ResidueField Λ) n) (right (ResidueField Λ) n) (𝓡k ⊗[𝓡] M) (𝓡k ⊗[𝓡] N) :=
  TensorProduct.liftAddHom
    { toFun y :=
        ((TensorProduct.mk 𝓡k (Twist (right (ResidueField Λ) n)
          (Ext (left (ResidueField Λ) n) (𝓡k ⊗[𝓡] M))) (𝓡k ⊗[𝓡] N)
          (Twist.mk _ (extReduce M (@id (Ext (left Λ n) M) y)))).toAddMonoidHom).comp
          (TensorProduct.mk 𝓡 𝓡k N 1).toAddMonoidHom
      map_zero' := by
        ext m
        change Twist.mk _ (extReduce M 0) ⊗ₜ _ = 0
        rw [map_zero, Twist.mk_zero, TensorProduct.zero_tmul]
      map_add' y y' := by
        ext m
        change Twist.mk _ (extReduce M ((@id (Ext (left Λ n) M) y) + (@id (Ext (left Λ n) M) y')))
          ⊗ₜ _ = Twist.mk _ (extReduce M y) ⊗ₜ _ + Twist.mk _ (extReduce M y') ⊗ₜ _
        rw [map_add, ← Twist.mk_add, TensorProduct.add_tmul]
        rfl }
    (fun r y m => by
      change Twist.mk _ (extReduce M (right Λ n r • (@id (Ext (left Λ n) M) y))) ⊗ₜ
          ((1 : 𝓡k) ⊗ₜ[𝓡] m) =
        Twist.mk _ (extReduce M y) ⊗ₜ ((1 : 𝓡k) ⊗ₜ[𝓡] (r • m))
      rw [extReduce_smul, algebraMap_right, ← Twist.rsmul_mk, TensorProduct.smul_tmul]
      congr 1
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← TensorProduct.smul_tmul,
        Algebra.smul_def, mul_one])

/-- `pairReduceAddHom M N` sends `y ⊗ m` to `extReduce M y ⊗ (1 ⊗ m)`. -/
theorem pairReduceAddHom_tmul (M N : Type u) [AddCommGroup M] [Module 𝓡 M] [AddCommGroup N]
    [Module 𝓡 N] (y : Twist (right Λ n) (Ext (left Λ n) M)) (m : N) :
    pairReduceAddHom M N (y ⊗ₜ m) =
      Twist.mk _ (extReduce M (@id (Ext (left Λ n) M) y)) ⊗ₜ ((1 : 𝓡k) ⊗ₜ[𝓡] m) := rfl

/-- `pairReduceAddHom M N` is semilinear along the reduction of coefficients
`Λ[[y, x]] → k[[y, x]]`. -/
theorem pairReduceAddHom_smul (M N : Type u) [AddCommGroup M] [Module 𝓡 M] [AddCommGroup N]
    [Module 𝓡 N] (b : 𝓑) (z : Pair (left Λ n) (right Λ n) M N) :
    pairReduceAddHom M N (b • z) = algebraMap 𝓑 𝓑k b • pairReduceAddHom M N z := by
  induction z using TensorProduct.inductionOn with
  | tmul y m =>
    rw [TensorProduct.smul_tmul', pairReduceAddHom_tmul, pairReduceAddHom_tmul,
      TensorProduct.smul_tmul', Twist.smul_mk]
    change Twist.mk _ (extReduce M (b • (@id (Ext (left Λ n) M) y))) ⊗ₜ _ = _
    rw [extReduce_smul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **Reduction modulo the maximal ideal of `Λ` of the complete tensor product**, as a map of
`Λ[[y, x]]`-modules to the complete tensor product over the residue field, viewed as a
`Λ[[y, x]]`-module through the reduction of coefficients. -/
def pairReduce (M N : Type u) [AddCommGroup M] [Module 𝓡 M] [AddCommGroup N] [Module 𝓡 N] :
    Pair (left Λ n) (right Λ n) M N →ₗ[𝓑]
      Twist (algebraMap 𝓑 𝓑k)
        (Pair (left (ResidueField Λ) n) (right (ResidueField Λ) n) (𝓡k ⊗[𝓡] M) (𝓡k ⊗[𝓡] N)) where
  toFun z := Twist.mk _ (pairReduceAddHom M N z)
  map_add' z z' := by rw [map_add]; rfl
  map_smul' b z := by
    rw [pairReduceAddHom_smul]
    rfl

/-- The reduction `pairReduce M N` of the complete tensor product is surjective. -/
theorem pairReduce_surjective (M N : Type u) [AddCommGroup M] [Module 𝓡 M] [AddCommGroup N]
    [Module 𝓡 N] : Function.Surjective (pairReduce (Λ := Λ) (n := n) M N) := by
  have hR := algebraMap_surjective Λ n
  have hB := algebraMap_sum_surjective Λ n
  intro w
  obtain ⟨w, rfl⟩ : ∃ w' : Pair (left (ResidueField Λ) n) (right (ResidueField Λ) n)
      (𝓡k ⊗[𝓡] M) (𝓡k ⊗[𝓡] N), Twist.mk (algebraMap 𝓑 𝓑k) w' = w := ⟨w, rfl⟩
  suffices h : w ∈ (pairReduceAddHom (Λ := Λ) (n := n) M N).range by
    obtain ⟨z, hz⟩ := h
    exact ⟨z, by rw [← hz]; rfl⟩
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => exact AddSubgroup.add_mem _ hx hy
  | tmul x m =>
    obtain ⟨x, rfl⟩ : ∃ x' : Ext (left (ResidueField Λ) n) (𝓡k ⊗[𝓡] M),
        Twist.mk (right (ResidueField Λ) n) x' = x := ⟨x, rfl⟩
    induction m using TensorProduct.inductionOn with
    | add a b ha hb => rw [TensorProduct.tmul_add]; exact AddSubgroup.add_mem _ ha hb
    | tmul c m =>
      obtain ⟨c, rfl⟩ := hR c
      have hc : (algebraMap 𝓡 𝓡k c ⊗ₜ[𝓡] m : 𝓡k ⊗[𝓡] N) = (1 : 𝓡k) ⊗ₜ[𝓡] (c • m) := by
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
      rw [hc]
      induction x using TensorProduct.inductionOn with
      | add a b ha hb =>
        rw [← Twist.mk_add, TensorProduct.add_tmul]
        exact AddSubgroup.add_mem _ ha hb
      | tmul b' m' =>
        obtain ⟨b', rfl⟩ : ∃ c : 𝓑k, Twist.mk (left (ResidueField Λ) n) c = b' := ⟨b', rfl⟩
        obtain ⟨b, rfl⟩ := hB b'
        induction m' using TensorProduct.inductionOn with
        | add a a' ha ha' =>
          rw [TensorProduct.tmul_add, ← Twist.mk_add, TensorProduct.add_tmul]
          exact AddSubgroup.add_mem _ ha ha'
        | tmul d m' =>
          obtain ⟨d, rfl⟩ := hR d
          refine ⟨(Twist.mk (right Λ n) (Twist.mk (left Λ n) b ⊗ₜ (d • m') : Ext (left Λ n) M)) ⊗ₜ
            (c • m), ?_⟩
          rw [pairReduceAddHom_tmul]
          change Twist.mk _ (extReduce M (Twist.mk (left Λ n) b ⊗ₜ (d • m'))) ⊗ₜ _ = _
          rw [extReduce_tmul, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

end Reduction

section Dimension

/-- Along a surjective ring map `f : A → A'`, a finite `A'`-module has the same support dimension
over `A` (through `f`) as over `A'`. -/
theorem supportDim_twist_of_surjective {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A')
    (hf : Function.Surjective f) (P : Type u) [AddCommGroup P] [Module A' P] [Module.Finite A' P] :
    Module.supportDim A (Twist f P) = Module.supportDim A' P := by
  let := f.toAlgebra
  have : Module.Finite A A' := RingHom.Finite.of_surjective f hf
  have : Algebra.IsIntegral A A' := Algebra.IsIntegral.of_finite A A'
  have : IsScalarTower A A' (Twist f P) :=
    ⟨fun a b x => by
      change (f a * b) • x = f a • b • x
      rw [mul_smul]⟩
  have : Module.Finite A' (Twist f P) := ‹Module.Finite A' P›
  have : Module.Finite A (Twist f P) := Module.Finite.trans A' (Twist f P)
  exact AlgebraicGeometry.supportDim_eq_of_isIntegral A A' (Twist f P)

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] {ϖ : Λ}
  (hϖ : maximalIdeal Λ = Ideal.span {ϖ}) {n : ℕ}

local notation "𝓡" => MvPowerSeries (Fin n) Λ
local notation "𝓑" => MvPowerSeries (Fin n ⊕ Fin n) Λ
local notation "𝓡k" => MvPowerSeries (Fin n) (ResidueField Λ)
local notation "𝓑k" => MvPowerSeries (Fin n ⊕ Fin n) (ResidueField Λ)

include hϖ in
/-- The kernel of the reduction `Λ[[x]] → k[[x]]` is generated by `ϖ`. -/
theorem ker_algebraMap_eq : RingHom.ker (algebraMap 𝓡 𝓡k) = Ideal.span {(C ϖ : 𝓡)} := by
  change RingHom.ker (MvPowerSeries.map (algebraMap Λ (ResidueField Λ))) = _
  rw [ker_map_of_fg _ (Ideal.fg_of_isNoetherianRing _)]
  change Ideal.map C (RingHom.ker (residue Λ)) = _
  rw [ker_residue, hϖ, Ideal.map_span, Set.image_singleton]

include hϖ in
/-- `dim_{k[[x]]} (k[[x]] ⊗ X) = dim_{Λ[[x]]} (X / ϖ X)`. -/
theorem supportDim_baseChange_residue (X : Type u) [AddCommGroup X] [Module 𝓡 X]
    [Module.Finite 𝓡 X] :
    Module.supportDim 𝓡k (𝓡k ⊗[𝓡] X) = Module.supportDim 𝓡 (QuotSMulTop (C ϖ : 𝓡) X) := by
  have : Module.Finite 𝓡 𝓡k := RingHom.Finite.of_surjective _ (algebraMap_surjective Λ n)
  have : Algebra.IsIntegral 𝓡 𝓡k := Algebra.IsIntegral.of_finite 𝓡 𝓡k
  rw [← AlgebraicGeometry.supportDim_eq_of_isIntegral 𝓡 𝓡k (𝓡k ⊗[𝓡] X)]
  exact Module.supportDim_eq_of_equiv
    (Stacks.SerreIntersection.baseChangeEquivQuotSMulTop (algebraMap_surjective Λ n)
      (ker_algebraMap_eq hϖ) X)

include hϖ in
/-- For a nonzero finite `Λ[[x]]`-module `X`, the base change `k[[x]] ⊗_{Λ[[x]]} X` is nonzero. -/
theorem nontrivial_baseChange_residue (X : Type u) [AddCommGroup X] [Module 𝓡 X]
    [Module.Finite 𝓡 X] [Nontrivial X] : Nontrivial (𝓡k ⊗[𝓡] X) := by
  have := nontrivial_quotSMulTop_of_mem_maximalIdeal X
    (C_mem_maximalIdeal_of_eq_span (σ := Fin n) hϖ)
  exact (Stacks.SerreIntersection.baseChangeEquivQuotSMulTop (algebraMap_surjective Λ n)
    (ker_algebraMap_eq hϖ) X).toEquiv.nontrivial

/-- Cancelling `+ 1` below a natural number. -/
theorem natCast_le_of_add_one_le {p : WithBot ℕ∞} {m : ℕ} (h : (m : WithBot ℕ∞) + 1 ≤ p + 1) :
    (m : WithBot ℕ∞) ≤ p := by
  cases p with
  | bot => exact absurd h (by simp)
  | coe e =>
    have h' : ((m : ℕ∞) + 1 : ℕ∞) ≤ e + 1 := by exact_mod_cast h
    exact_mod_cast (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'

/-- The Krull dimension of `Λ[[x_1, …, x_n]]` is `n + 1` when `Λ` has dimension one. -/
private theorem ringKrullDim_mvPowerSeries_eq_add_one (hdim : ringKrullDim Λ = 1) :
    ringKrullDim (MvPowerSeries (Fin n) Λ) = ((n : ℕ) : WithBot ℕ∞) + 1 := by
  rw [MvPowerSeries.ringKrullDim_fin_eq_add, hdim]
  exact add_comm _ _

omit [IsLocalRing Λ] [IsNoetherianRing Λ] in
/-- On `(B ⊗_{R, x} M) ⊗_{R, y} N`, multiplication by `ϖ` is multiplication by `ϖ` on `N`; so it
is injective when `B ⊗_{R, x} M` is flat over `R` through `y` and `ϖ` is regular on `N`. -/
theorem isSMulRegular_pair (M N : Type u) [AddCommGroup M] [Module 𝓡 M] [AddCommGroup N]
    [Module 𝓡 N] [Module.Flat 𝓡 (Twist (right Λ n) (Ext (left Λ n) M))]
    (hN : IsSMulRegular N (C ϖ : 𝓡)) :
    IsSMulRegular (Pair (left Λ n) (right Λ n) M N) (C ϖ : 𝓑) := by
  have h : ∀ z : Pair (left Λ n) (right Λ n) M N, (C ϖ : 𝓑) • z =
      LinearMap.lTensor (Twist (right Λ n) (Ext (left Λ n) M)) (LinearMap.lsmul 𝓡 N (C ϖ)) z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul y m =>
      rw [LinearMap.lTensor_tmul, LinearMap.lsmul_apply, ← TensorProduct.smul_tmul,
        TensorProduct.smul_tmul']
      congr 1
      change (C ϖ : 𝓑) • y = right Λ n (C ϖ) • y
      congr 1
      change C ϖ = rename _ (C ϖ)
      rw [rename_C]
    | add x y hx hy => rw [smul_add, hx, hy, map_add]
  intro z z' hzz'
  apply Module.Flat.lTensor_preserves_injective_linearMap
    (M := Twist (right Λ n) (Ext (left Λ n) M))
    (LinearMap.lsmul 𝓡 N (C ϖ)) hN
  change (C ϖ : 𝓑) • z = (C ϖ : 𝓑) • z' at hzz'
  rwa [h, h] at hzz'

omit [IsNoetherianRing Λ] in
include hϖ in
/-- **Serre's dimension inequality and positivity over a discrete valuation ring, for torsion
free modules.** Let `Λ` be a regular local ring of dimension one with maximal ideal `(ϖ)`, let
`R = Λ[[x_1, …, x_n]]` and let `M`, `N` be nonzero finite `R`-modules on which `ϖ` is a
nonzerodivisor, with `M ⊗_R N` supported in the closed point. Then
`dim Supp M + dim Supp N ≤ dim R`, and if equality holds then `χ(M, N) > 0`.

The complete tensor product `C = (B ⊗_{R, x} M) ⊗_{R, y} N` over `B = Λ[[y, x]]` has `C / ϖ C`
mapping onto the complete tensor product of the reductions `M / ϖ M` and `N / ϖ N` over the
residue field, of dimension `dim M + dim N - 2`, and `ϖ` is regular on `C`; so
`dim C ≥ dim M + dim N - 1`. The diagonal is cut out of `B` by a regular sequence of length
`n` and `C` modulo it is `M ⊗_R N`, of finite length; so `dim C ≤ n` and `χ(M, N)` is the
multiplicity of the diagonal against `C`, positive when `dim C = n`. -/
theorem supportDim_add_supportDim_le_and_pos_of_isSMulRegular [IsRegularLocalRing Λ]
    (hdim : ringKrullDim Λ = 1) (M N : Type u) [AddCommGroup M] [Module 𝓡 M] [Module.Finite 𝓡 M]
    [Nontrivial M] [AddCommGroup N] [Module 𝓡 N] [Module.Finite 𝓡 N] [Nontrivial N]
    (hM : IsSMulRegular M (C ϖ : 𝓡)) (hN : IsSMulRegular N (C ϖ : 𝓡))
    (hMN : Module.support 𝓡 (M ⊗[𝓡] N) ⊆ {closedPoint 𝓡}) :
    Module.supportDim 𝓡 M + Module.supportDim 𝓡 N ≤ ringKrullDim 𝓡 ∧
      (Module.supportDim 𝓡 M + Module.supportDim 𝓡 N = ringKrullDim 𝓡 →
        0 < Stacks.Intersection.torEulerCharacteristic 𝓡 M N) := by
  have hϖm : ϖ ∈ maximalIdeal Λ := hϖ ▸ Ideal.mem_span_singleton_self ϖ
  have := flat_twist_ext_left_of_isSMulRegular hϖ n M hM
  have := finite_pair (K := Λ) (n := n) M N
  set P := Pair (left Λ n) (right Λ n) M N
  have hdimR := ringKrullDim_mvPowerSeries_eq_add_one (n := n) hdim
  obtain ⟨f, hf, hI⟩ := exists_isRegular_span_eq_ker_diag Λ n 1 (by rw [hdim, Nat.cast_one])
  have h0 := supportDim_quotient_ker_diag (K := Λ) (n := n) M N hMN
  have hle : Module.supportDim 𝓑 P ≤ (n : WithBot ℕ∞) :=
    supportDim_le_of_supportDim_quotient_eq_zero f _ hI _ h0
  -- `ϖ` is regular on the complete tensor product
  have hP1 := Module.supportDim_quotSMulTop_succ_eq_supportDim (isSMulRegular_pair M N hN)
    (C_mem_maximalIdeal_of_eq_span (σ := Fin n ⊕ Fin n) hϖ)
  -- the reduction modulo `ϖ`
  have := nontrivial_baseChange_residue (n := n) hϖ M
  have := nontrivial_baseChange_residue (n := n) hϖ N
  have := finite_pair (K := ResidueField Λ) (n := n) (𝓡k ⊗[𝓡] M) (𝓡k ⊗[𝓡] N)
  have hred : (C ϖ : 𝓑) • (⊤ : Submodule 𝓑 P) ≤ LinearMap.ker (pairReduce M N) := by
    intro z hz
    obtain ⟨w, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
    rw [LinearMap.mem_ker, map_smul]
    change Twist.mk _ (algebraMap 𝓑 𝓑k (C ϖ) • pairReduceAddHom M N w) = 0
    have hc : algebraMap 𝓑 𝓑k (C ϖ) = 0 := by
      change MvPowerSeries.map _ (C ϖ) = 0
      rw [MvPowerSeries.map_C]
      change C (residue Λ ϖ) = 0
      rw [(residue_eq_zero_iff ϖ).mpr hϖm, map_zero]
    rw [hc, zero_smul]
    rfl
  have hsurj : Function.Surjective
      (((C ϖ : 𝓑) • (⊤ : Submodule 𝓑 P)).liftQ (pairReduce M N) hred) := by
    intro w
    obtain ⟨z, rfl⟩ := pairReduce_surjective M N w
    exact ⟨Submodule.Quotient.mk z, rfl⟩
  have hQ := Module.supportDim_le_of_surjective _ hsurj
  rw [supportDim_twist_of_surjective _ (algebraMap_sum_surjective Λ n), supportDim_pair] at hQ
  rw [supportDim_baseChange_residue hϖ, supportDim_baseChange_residue hϖ] at hQ
  have hMd := Module.supportDim_quotSMulTop_succ_eq_supportDim hM (C_mem_maximalIdeal_of_eq_span hϖ)
  have hNd := Module.supportDim_quotSMulTop_succ_eq_supportDim hN (C_mem_maximalIdeal_of_eq_span hϖ)
  have key : Module.supportDim 𝓡 M + Module.supportDim 𝓡 N ≤ Module.supportDim 𝓑 P + 1 := by
    rw [← hMd, ← hNd, ← hP1]
    calc Module.supportDim 𝓡 (QuotSMulTop (C ϖ : 𝓡) M) + 1 +
          (Module.supportDim 𝓡 (QuotSMulTop (C ϖ : 𝓡) N) + 1)
        = Module.supportDim 𝓡 (QuotSMulTop (C ϖ : 𝓡) M) +
            Module.supportDim 𝓡 (QuotSMulTop (C ϖ : 𝓡) N) + 1 + 1 := by abel
      _ ≤ _ := by gcongr
  refine ⟨?_, fun heq => ?_⟩
  · rw [hdimR]
    exact key.trans (by gcongr)
  · rw [torEulerCharacteristic_eq_localIntersectionMultiplicity Λ n M N]
    refine localIntersectionMultiplicity_pos_of_supportDim_eq f hf _ hI _ h0
      (le_antisymm hle (natCast_le_of_add_one_le ?_))
    rw [← hdimR, ← heq]
    exact key

end Dimension

section Inequality

/-- The support of `A ⧸ 𝔭` is contained in the support of `M` for `𝔭` in the support of `M`. -/
theorem support_quotient_subset_support {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M]
    [Module A M] [Module.Finite A M] {p : PrimeSpectrum A} (hp : p ∈ Module.support A M) :
    Module.support A (A ⧸ p.asIdeal) ⊆ Module.support A M := fun q hq => by
  rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient] at hq
  rw [Module.mem_support_iff_of_finite] at hp ⊢
  exact hp.trans hq

/-- **A top-dimensional point of the support.** A nonzero finite module over a Noetherian local
ring has a point `𝔭` of its support with `dim Supp(R ⧸ 𝔭) = dim Supp M`. -/
theorem exists_mem_support_supportDim_quotient_eq {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M] :
    ∃ p ∈ Module.support A M,
      Module.supportDim A (A ⧸ p.asIdeal) = Module.supportDim A M := by
  have hfin : Module.supportDim A M < ⊤ :=
    (Module.supportDim_le_ringKrullDim A M).trans_lt ringKrullDim_lt_top
  obtain ⟨e, he⟩ : ∃ e : ℕ, Module.supportDim A M = (e : WithBot ℕ∞) := by
    cases hdim : Module.supportDim A M with
    | bot => exact False.elim ((Module.supportDim_ne_bot_of_nontrivial A M) hdim)
    | coe d =>
      have hd : d < ⊤ := WithBot.coe_lt_coe.mp (by simpa [hdim] using hfin)
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hd)
      exact ⟨m, by rw [← hm]; rfl⟩
  have hle : ((e : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (Module.support A M) := by
    rw [← he]; rfl
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hle
  have hmem : ∀ q : PrimeSpectrum A, q ∈ Module.support A (A ⧸ l.head.1.asIdeal) ↔
      l.head.1.asIdeal ≤ q.asIdeal := fun q => by
    rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
  refine ⟨l.head.1, l.head.2, le_antisymm ?_ ?_⟩
  · exact Order.krullDim_le_of_strictMono
      (fun q => ⟨q.1, support_quotient_subset_support M l.head.2 q.2⟩) (fun _ _ h => h)
  · rw [he]
    let l' : LTSeries (Module.support A (A ⧸ l.head.1.asIdeal)) :=
      { length := l.length
        toFun := fun i => ⟨(l i).1, (hmem _).mpr (l.head_le i)⟩
        step := fun i => l.step i }
    rw [← hl]
    exact Order.LTSeries.length_le_krullDim l'

variable {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] {ϖ : Λ}
  (hϖ : maximalIdeal Λ = Ideal.span {ϖ}) {n : ℕ}

local notation "𝓡" => MvPowerSeries (Fin n) Λ
local notation "𝓡k" => MvPowerSeries (Fin n) (ResidueField Λ)

/-- If `M ⊗_R N` has finite length then so has its reduction to `k[[x]]`. -/
theorem support_baseChange_residue_tensor (M N : Type u) [AddCommGroup M] [Module 𝓡 M]
    [Module.Finite 𝓡 M] [AddCommGroup N] [Module 𝓡 N] [Module.Finite 𝓡 N]
    (hMN : Module.support 𝓡 (M ⊗[𝓡] N) ⊆ {closedPoint 𝓡}) :
    Module.support 𝓡k ((𝓡k ⊗[𝓡] M) ⊗[𝓡k] (𝓡k ⊗[𝓡] N)) ⊆ {closedPoint 𝓡k} := by
  rw [support_subset_closedPoint_iff_length_ne_top] at hMN ⊢
  rw [← (TensorProduct.AlgebraTensorModule.distribBaseChange 𝓡 𝓡k M N).length_eq,
    ← Module.length_eq_of_surjective (algebraMap_surjective Λ n)]
  exact ne_top_of_le_ne_top hMN (Module.length_le_of_surjective
    (TensorProduct.mk 𝓡 𝓡k (M ⊗[𝓡] N) 1) (fun z => by
      induction z using TensorProduct.inductionOn with
      | add x y hx hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        exact ⟨a + b, by simp [TensorProduct.tmul_add]⟩
      | tmul c z =>
        obtain ⟨c, rfl⟩ := algebraMap_surjective Λ n c
        exact ⟨c • z, by rw [TensorProduct.mk_apply, ← TensorProduct.smul_tmul, Algebra.smul_def,
          mul_one]⟩))

include hϖ in
/-- **The inequality modulo `ϖ`**: for nonzero finite `Λ[[x]]`-modules `M`, `N` with `M ⊗ N`
supported in the closed point, `dim Supp(M / ϖ M) + dim Supp(N / ϖ N) ≤ n`. This is Serre's
inequality over the power series ring `k[[x]]` over the residue field, applied to the
reductions. -/
theorem supportDim_quotSMulTop_add_le (M N : Type u) [AddCommGroup M] [Module 𝓡 M]
    [Module.Finite 𝓡 M] [Nontrivial M] [AddCommGroup N] [Module 𝓡 N] [Module.Finite 𝓡 N]
    [Nontrivial N] (hMN : Module.support 𝓡 (M ⊗[𝓡] N) ⊆ {closedPoint 𝓡}) :
    Module.supportDim 𝓡 (QuotSMulTop (C ϖ : 𝓡) M) + Module.supportDim 𝓡 (QuotSMulTop (C ϖ : 𝓡) N)
      ≤ (n : WithBot ℕ∞) := by
  have := nontrivial_baseChange_residue (n := n) hϖ M
  have := nontrivial_baseChange_residue (n := n) hϖ N
  have key := (serre_mvPowerSeries (𝓡k ⊗[𝓡] M) (𝓡k ⊗[𝓡] N)
    (support_baseChange_residue_tensor M N hMN)).1
  rwa [supportDim_baseChange_residue hϖ, supportDim_baseChange_residue hϖ,
    MvPowerSeries.ringKrullDim_eq] at key

omit [IsNoetherianRing Λ] in
/-- `ϖ` is a nonzerodivisor on `R ⧸ 𝔭` when `ϖ ∉ 𝔭`. -/
theorem isSMulRegular_quotient_prime {A : Type u} [CommRing A] (P : Ideal A) [P.IsPrime] {x : A}
    (hx : x ∉ P) : IsSMulRegular (A ⧸ P) x := by
  intro a b hab
  change Ideal.Quotient.mk P x * a = Ideal.Quotient.mk P x * b at hab
  exact mul_left_cancel₀ (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]) hab

/-- Every element of an ideal `I` kills `A ⧸ I`. -/
private theorem smul_eq_zero_of_mem_ideal {A : Type u} [CommRing A] {I : Ideal A} {x : A}
    (hx : x ∈ I) : ∀ m : A ⧸ I, x • m = 0 := by
  intro m
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact I.mul_mem_right _ hx

/-- If `x` kills `M` then `x • ⊤ = ⊥`. -/
private theorem smul_top_eq_bot_of_smul_eq_zero {A : Type u} [CommRing A] {M : Type u}
    [AddCommGroup M] [Module A M] {x : A} (hx : ∀ m : M, x • m = 0) :
    x • (⊤ : Submodule A M) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨w, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
  rw [hx w]
  exact Submodule.zero_mem _

/-- If `x` kills `M` then `M / x M` has the same support dimension as `M`. -/
theorem supportDim_quotSMulTop_of_smul_eq_zero {A : Type u} [CommRing A] (M : Type u)
    [AddCommGroup M] [Module A M] {x : A} (hx : ∀ m : M, x • m = 0) :
    Module.supportDim A (QuotSMulTop x M) = Module.supportDim A M :=
  Module.supportDim_eq_of_equiv
    (Submodule.quotEquivOfEqBot _ (smul_top_eq_bot_of_smul_eq_zero hx))

omit [IsNoetherianRing Λ] in
include hϖ in
/-- **Serre's dimension inequality over a power series ring over a discrete valuation ring.**
Let `Λ` be a regular local ring of dimension one with maximal ideal `(ϖ)` and let `M`, `N` be
nonzero finite modules over `R = Λ[[x_1, …, x_n]]` with `M ⊗_R N` supported in the closed point.
Then `dim Supp M + dim Supp N ≤ dim R`.

One reduces to `R ⧸ 𝔭` and `R ⧸ 𝔮` for top-dimensional points `𝔭`, `𝔮` of the two supports. If
`ϖ` lies in neither, both are `ϖ`-torsion free and the complete tensor product over `Λ` does it
(`supportDim_add_supportDim_le_and_pos_of_isSMulRegular`); if `ϖ ∈ 𝔭`, say, then
`R ⧸ 𝔭` is a module over `k[[x]]` and the inequality over `k[[x]]` for `R ⧸ 𝔭` and the
reduction of `R ⧸ 𝔮` modulo `ϖ`, whose dimension drops by at most one, gives it. -/
theorem supportDim_add_supportDim_le_of_mvPowerSeries [IsRegularLocalRing Λ]
    (hdim : ringKrullDim Λ = 1) (M N : Type u) [AddCommGroup M] [Module 𝓡 M] [Module.Finite 𝓡 M]
    [Nontrivial M] [AddCommGroup N] [Module 𝓡 N] [Module.Finite 𝓡 N] [Nontrivial N]
    (hMN : Module.support 𝓡 (M ⊗[𝓡] N) ⊆ {closedPoint 𝓡}) :
    Module.supportDim 𝓡 M + Module.supportDim 𝓡 N ≤ ringKrullDim 𝓡 := by
  have hCm : (C ϖ : 𝓡) ∈ maximalIdeal 𝓡 := C_mem_maximalIdeal_of_eq_span hϖ
  have hdimR := ringKrullDim_mvPowerSeries_eq_add_one (n := n) hdim
  obtain ⟨P, hPM, hP⟩ := exists_mem_support_supportDim_quotient_eq (A := 𝓡) M
  obtain ⟨Q, hQN, hQ⟩ := exists_mem_support_supportDim_quotient_eq (A := 𝓡) N
  rw [← hP, ← hQ]
  have hPQ : Module.support 𝓡 ((𝓡 ⧸ P.asIdeal) ⊗[𝓡] (𝓡 ⧸ Q.asIdeal)) ⊆ {closedPoint 𝓡} := by
    rw [Stacks.Intersection.support_tensorProduct_eq_inter]
    refine fun q hq => hMN ?_
    rw [Stacks.Intersection.support_tensorProduct_eq_inter]
    exact ⟨support_quotient_subset_support M hPM hq.1, support_quotient_subset_support N hQN hq.2⟩
  have hmod := supportDim_quotSMulTop_add_le hϖ (𝓡 ⧸ P.asIdeal) (𝓡 ⧸ Q.asIdeal) hPQ
  have hdropP := Module.supportDim_le_supportDim_quotSMulTop_succ (M := 𝓡 ⧸ P.asIdeal) hCm
  have hdropQ := Module.supportDim_le_supportDim_quotSMulTop_succ (M := 𝓡 ⧸ Q.asIdeal) hCm
  rw [hdimR]
  by_cases hPϖ : (C ϖ : 𝓡) ∈ P.asIdeal
  · rw [supportDim_quotSMulTop_of_smul_eq_zero _ (smul_eq_zero_of_mem_ideal hPϖ)] at hmod
    calc _ ≤ Module.supportDim 𝓡 (𝓡 ⧸ P.asIdeal) +
          (Module.supportDim 𝓡 (QuotSMulTop (C ϖ : 𝓡) (𝓡 ⧸ Q.asIdeal)) + 1) := by gcongr
      _ = _ + 1 := (add_assoc _ _ _).symm
      _ ≤ _ := by gcongr
  by_cases hQϖ : (C ϖ : 𝓡) ∈ Q.asIdeal
  · rw [supportDim_quotSMulTop_of_smul_eq_zero _ (smul_eq_zero_of_mem_ideal hQϖ)] at hmod
    calc _ ≤ (Module.supportDim 𝓡 (QuotSMulTop (C ϖ : 𝓡) (𝓡 ⧸ P.asIdeal)) + 1) +
          Module.supportDim 𝓡 (𝓡 ⧸ Q.asIdeal) := by gcongr
      _ = _ + 1 := add_right_comm _ _ _
      _ ≤ _ := by gcongr
  have h := (supportDim_add_supportDim_le_and_pos_of_isSMulRegular hϖ hdim (𝓡 ⧸ P.asIdeal)
    (𝓡 ⧸ Q.asIdeal) (isSMulRegular_quotient_prime _ hPϖ) (isSMulRegular_quotient_prime _ hQϖ)
    hPQ).1
  rwa [hdimR] at h

end Inequality

section Positivity

variable {Λ : Type u} [CommRing Λ] [IsRegularLocalRing Λ] {ϖ : Λ}
  (hϖ : maximalIdeal Λ = Ideal.span {ϖ}) (hdim : ringKrullDim Λ = 1) {n : ℕ}

local notation "𝓡" => MvPowerSeries (Fin n) Λ
local notation "𝓡k" => MvPowerSeries (Fin n) (ResidueField Λ)

include hϖ hdim in
/-- `ϖ` is a nonzerodivisor of `Λ[[x]]`. -/
theorem isSMulRegular_C : IsSMulRegular 𝓡 (C ϖ : 𝓡) := by
  have := MvPowerSeries.isRegularLocalRing Λ n
  have := IsRegularLocalRing.isDomain 𝓡
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    have hfield : IsField Λ := by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, hϖ, Ideal.span_singleton_eq_bot]
    rw [ringKrullDim_eq_zero_of_isField hfield] at hdim
    exact zero_ne_one hdim
  have hC : (C ϖ : 𝓡) ≠ 0 := fun h => hϖ0 (by
    have := congrArg (MvPowerSeries.constantCoeff (σ := Fin n) (R := Λ)) h
    rwa [constantCoeff_C, map_zero] at this)
  exact fun a b hab => mul_left_cancel₀ hC hab

include hϖ hdim in
/-- **Positivity when `ϖ` lies in exactly one of the two primes.** If `ϖ ∈ 𝔭`, `ϖ ∉ 𝔮` and
`dim R ⧸ 𝔭 + dim R ⧸ 𝔮 = dim R`, then `χ(R ⧸ 𝔭, R ⧸ 𝔮) > 0`: as `ϖ` kills `R ⧸ 𝔭` and is regular
on `R ⧸ 𝔮`, `χ` is the Euler characteristic over `k[[x]]` of `R ⧸ 𝔭` and `(R ⧸ 𝔮) / ϖ`, whose
dimensions add up to `n`. -/
theorem torEulerCharacteristic_pos_of_mem_of_notMem (P Q : Ideal 𝓡) [P.IsPrime] [Q.IsPrime]
    (hP : (C ϖ : 𝓡) ∈ P) (hQ : (C ϖ : 𝓡) ∉ Q)
    (hPQ : Module.support 𝓡 ((𝓡 ⧸ P) ⊗[𝓡] (𝓡 ⧸ Q)) ⊆ {closedPoint 𝓡})
    (heq : Module.supportDim 𝓡 (𝓡 ⧸ P) + Module.supportDim 𝓡 (𝓡 ⧸ Q) = ringKrullDim 𝓡) :
    0 < Stacks.Intersection.torEulerCharacteristic 𝓡 (𝓡 ⧸ P) (𝓡 ⧸ Q) := by
  have hCm : (C ϖ : 𝓡) ∈ maximalIdeal 𝓡 := C_mem_maximalIdeal_of_eq_span hϖ
  have hdimR := ringKrullDim_mvPowerSeries_eq_add_one (n := n) hdim
  have hkill := smul_eq_zero_of_mem_ideal hP
  -- `R ⧸ 𝔭` is its own reduction modulo `ϖ`
  let e : 𝓡k ⊗[𝓡] (𝓡 ⧸ P) ≃ₗ[𝓡] 𝓡 ⧸ P :=
    (Stacks.SerreIntersection.baseChangeEquivQuotSMulTop (algebraMap_surjective Λ n)
      (ker_algebraMap_eq hϖ) (𝓡 ⧸ P)).trans
      (Submodule.quotEquivOfEqBot _ (smul_top_eq_bot_of_smul_eq_zero hkill))
  rw [← torEulerCharacteristic_congr_left e,
    Stacks.SerreIntersection.torEulerCharacteristic_quotient
    (𝓡k ⊗[𝓡] (𝓡 ⧸ P)) (algebraMap_surjective Λ n) (ker_algebraMap_eq hϖ)
    (isSMulRegular_C hϖ hdim) (𝓡 ⧸ Q) (isSMulRegular_quotient_prime _ hQ)]
  have := nontrivial_baseChange_residue (n := n) hϖ (𝓡 ⧸ P)
  have := nontrivial_baseChange_residue (n := n) hϖ (𝓡 ⧸ Q)
  have hmod := supportDim_quotSMulTop_add_le hϖ (𝓡 ⧸ P) (𝓡 ⧸ Q) hPQ
  rw [supportDim_quotSMulTop_of_smul_eq_zero _ hkill] at hmod
  have hQd := Module.supportDim_quotSMulTop_succ_eq_supportDim (isSMulRegular_quotient_prime _ hQ)
    hCm
  refine (serre_mvPowerSeries (𝓡k ⊗[𝓡] (𝓡 ⧸ P)) (𝓡k ⊗[𝓡] (𝓡 ⧸ Q))
    (support_baseChange_residue_tensor _ _ hPQ)).2.2 ?_
  rw [supportDim_baseChange_residue hϖ, supportDim_baseChange_residue hϖ,
    supportDim_quotSMulTop_of_smul_eq_zero _ hkill, MvPowerSeries.ringKrullDim_eq]
  refine le_antisymm hmod (natCast_le_of_add_one_le ?_)
  rw [← hdimR, ← heq, ← hQd, add_assoc]

include hϖ hdim in
/-- **Serre's positivity over a power series ring over a discrete valuation ring, for two
primes.** Let `𝔭`, `𝔮` be primes of `R = Λ[[x_1, …, x_n]]` with `(R ⧸ 𝔭) ⊗ (R ⧸ 𝔮)` supported in
the closed point and `dim R ⧸ 𝔭 + dim R ⧸ 𝔮 = dim R`. Then `χ(R ⧸ 𝔭, R ⧸ 𝔮) > 0`. If `ϖ` lies in
neither prime this is the torsion free case; if in exactly one, the Euler characteristic is one
over `k[[x]]`; and `ϖ` cannot lie in both, for then the two dimensions add up to at most
`n < dim R`. -/
theorem torEulerCharacteristic_quotient_pos_of_mvPowerSeries (P Q : Ideal 𝓡) [P.IsPrime]
    [Q.IsPrime] (hPQ : Module.support 𝓡 ((𝓡 ⧸ P) ⊗[𝓡] (𝓡 ⧸ Q)) ⊆ {closedPoint 𝓡})
    (heq : Module.supportDim 𝓡 (𝓡 ⧸ P) + Module.supportDim 𝓡 (𝓡 ⧸ Q) = ringKrullDim 𝓡) :
    0 < Stacks.Intersection.torEulerCharacteristic 𝓡 (𝓡 ⧸ P) (𝓡 ⧸ Q) := by
  by_cases hP : (C ϖ : 𝓡) ∈ P
  · by_cases hQ : (C ϖ : 𝓡) ∈ Q
    · exfalso
      have hmod := supportDim_quotSMulTop_add_le hϖ (𝓡 ⧸ P) (𝓡 ⧸ Q) hPQ
      rw [supportDim_quotSMulTop_of_smul_eq_zero _ (smul_eq_zero_of_mem_ideal hP),
        supportDim_quotSMulTop_of_smul_eq_zero _ (smul_eq_zero_of_mem_ideal hQ), heq,
        MvPowerSeries.ringKrullDim_fin_eq_add, hdim] at hmod
      have h1 : ((1 : ℕ) : WithBot ℕ∞) + n ≤ (n : WithBot ℕ∞) + 0 := by
        simpa using hmod
      rw [add_comm] at h1
      have h2 : ((n : ℕ) : WithBot ℕ∞) + 1 ≤ (n : ℕ) := by simpa using h1
      have h3 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ((n : ℕ) : WithBot ℕ∞) := by exact_mod_cast h2
      have h4 : n + 1 ≤ n := by exact_mod_cast h3
      omega
    · exact torEulerCharacteristic_pos_of_mem_of_notMem hϖ hdim P Q hP hQ hPQ heq
  · by_cases hQ : (C ϖ : 𝓡) ∈ Q
    · rw [torEulerCharacteristic_comm]
      refine torEulerCharacteristic_pos_of_mem_of_notMem hϖ hdim Q P hQ hP ?_
        (by rw [add_comm, heq])
      rw [Stacks.Intersection.support_tensorProduct_eq_inter, Set.inter_comm,
        ← Stacks.Intersection.support_tensorProduct_eq_inter]
      exact hPQ
    · exact (supportDim_add_supportDim_le_and_pos_of_isSMulRegular hϖ hdim (𝓡 ⧸ P) (𝓡 ⧸ Q)
        (isSMulRegular_quotient_prime _ hP) (isSMulRegular_quotient_prime _ hQ) hPQ).2 heq

end Positivity

end Stacks.SerreIntersection.PowerSeriesDiagonal
