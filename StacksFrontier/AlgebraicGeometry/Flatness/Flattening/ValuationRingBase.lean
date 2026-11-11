module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Algebra.Module.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.MaximalIdealInjectivity
public import StacksFrontier.RingTheory.Flat.Finiteness
public import StacksFrontier.RingTheory.Flat.ShortExact

/-!
# Injectivity modulo the maximal ideal over a valuation ring base

## Situation 0AT0

Stacks 0AT0 fixes a local ring homomorphism `φ : A → B` of local rings which is essentially
of finite type, a flat `A`-module `M`, a finite `B`-module `N`, and an `A`-module map
`u : N → M` such that `ū : N/𝔪_A N → M/𝔪_A M` is injective.  The section "Variants of a
lemma" declares that *the lemma holds* in such a situation when all three of the following
are true: `u` is `A`-universally injective, `N` is of finite presentation over `B`, and `N`
is flat as an `A`-module.  Stacks 0AT5 asserts that the lemma holds whenever `A` is a
valuation ring.

The data and the hypotheses are the bundle
`AlgebraicGeometry.InjectiveModuloMaximalIdealSituation` of Stacks 0AT0.  Note that `u` is
only `A`-linear and `M` is only an `A`-module; neither is required to be compatible with `B`.

## The argument

Over the valuation ring `A` a module is flat exactly when it is torsion free
(`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`; a Bézout domain already suffices).  Let
`T ⊆ N` be the `A`-torsion.  It is a `B`-submodule, the `A`-action on `N` being the
restriction of the `B`-action, and `N/T` is torsion free, hence `A`-flat.  Stacks 0GSE then
makes `N/T` finitely presented over `B`, so `T` is finite over `B` by Stacks 0519.  Flatness
of `N/T` makes `T/𝔪_A T → N/𝔪_A N` injective (Stacks 00HL), while `u` kills `T` — every
element of `T` is annihilated by a nonzero element of `A`, and `M`, being `A`-flat, is
torsion free — so injectivity of `ū` forces `T/𝔪_A T = 0`.  Nakayama's lemma over `B`, for
which `T` must be finite over `B`, gives `T = 0`.  Hence `N` is `A`-flat, and Stacks 0GSE
applied once more gives finite presentation of `N` over `B`.

This is the source's own argument for the first two of the three assertions, up to the point
where it records that "we have proved two out of the three assertions".

## Scope

The third assertion, universal injectivity of `u`, and the statement of all three together
(`AlgebraicGeometry.injectiveModuloMaximalIdealConclusion_of_valuationRing`) are in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ValuationRingBaseUniversalInjectivity`,
which uses the existence of content ideals (Stacks 0ASX) and so needs imports this file does
not have.

## Main results

* `AlgebraicGeometry.flat_of_valuationRing`: `N` is flat over the valuation ring `A`.
* `AlgebraicGeometry.finitePresentation_of_valuationRing`: `N` is of finite presentation
  over `B`.

## Implementation notes

Mathlib's `ValuationRing` class presupposes `IsDomain`, so both appear as instance
arguments; it also supplies `IsLocalRing A` and `IsBezout A`, so neither is repeated.

The closed fibre `N/𝔪_A N` is the quotient `N ⧸ 𝔪_A • (⊤ : Submodule A N)` and `ū` is the
canonical `Submodule.mapQ` of `u`, exactly as in Stacks 0AT0's bundle.  The embedding
`T/𝔪_A T → N/𝔪_A N` is obtained from injectivity of `(A/𝔪_A) ⊗ T → (A/𝔪_A) ⊗ N`, which is
what Stacks 00HL delivers, transported along `TensorProduct.quotTensorEquivQuotSMul`.

## References

* [Stacks Project, Tag 0AT5](https://stacks.math.columbia.edu/tag/0AT5)
* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 0GSE](https://stacks.math.columbia.edu/tag/0GSE)
* [Stacks Project, Tag 0519](https://stacks.math.columbia.edu/tag/0519)
* [Stacks Project, Tag 00HL](https://stacks.math.columbia.edu/tag/00HL)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄

namespace AlgebraicGeometry

open scoped TensorProduct

/-- The `A`-torsion of `N`, viewed as a `B`-submodule.  The `A`-action on `N` is the
restriction of the `B`-action, so the two commute and the torsion is `B`-stable. -/
private def torsionAsBSubmodule (S : InjectiveModuloMaximalIdealSituation) [IsDomain S.A] :
    Submodule S.B S.N :=
  { carrier := (Submodule.torsion S.A S.N : Set S.N)
    zero_mem' := (Submodule.torsion S.A S.N).zero_mem
    add_mem' := (Submodule.torsion S.A S.N).add_mem
    smul_mem' := by
      intro b x hx
      obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
      refine ⟨a, ?_⟩
      rw [smul_comm a b x]
      simpa only [smul_zero] using congrArg (b • ·) ha }

/-- The quotient of `N` by its `A`-torsion is torsion free, hence flat over the valuation
ring `A`, a valuation ring being a Bézout domain. -/
private theorem quotientTorsion_flat (S : InjectiveModuloMaximalIdealSituation)
    [IsDomain S.A] [ValuationRing S.A] :
    Module.Flat S.A (S.N ⧸ torsionAsBSubmodule S) := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  change Module.IsTorsionFree S.A (S.N ⧸ Submodule.torsion S.A S.N)
  infer_instance

/-- The `A`-torsion of `N` is a finite `B`-module: the quotient `N/T` is `A`-flat and finite
over `B`, hence finitely presented over `B` by Stacks 0GSE, and a finite module mapping onto
a finitely presented one has a finite kernel by Stacks 0519. -/
private theorem torsion_finite (S : InjectiveModuloMaximalIdealSituation)
    [IsDomain S.A] [ValuationRing S.A] :
    Module.Finite S.B (torsionAsBSubmodule S) := by
  let T := torsionAsBSubmodule S
  let Q := S.N ⧸ T
  have : Module.FinitePresentation S.B Q :=
    (essentiallyOfFinitePresentation_and_finitePresentation_of_flat_of_valuationRing
      (A := S.A) (B := S.B) (M := Q)).2 (quotientTorsion_flat S)
        (Module.Finite.of_surjective T.mkQ T.mkQ_surjective)
  exact Module.Finite.of_exact_left T.subtype T.mkQ
    (LinearMap.exact_subtype_mkQ T) Subtype.val_injective T.mkQ_surjective

/-- Flatness of `N/T` over `A` embeds `T/𝔪_A T` into `N/𝔪_A N` (Stacks 00HL). -/
private theorem torsion_mapQ_injective (S : InjectiveModuloMaximalIdealSituation)
    [IsDomain S.A] [ValuationRing S.A] :
    Function.Injective (Submodule.mapQ
      (IsLocalRing.maximalIdeal S.A • (⊤ : Submodule S.A (torsionAsBSubmodule S)))
      (IsLocalRing.maximalIdeal S.A • (⊤ : Submodule S.A S.N))
      ((torsionAsBSubmodule S).subtype.restrictScalars S.A)
      (Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal S.A)
        ((torsionAsBSubmodule S).subtype.restrictScalars S.A))) := by
  let T := torsionAsBSubmodule S
  let m := IsLocalRing.maximalIdeal S.A
  let pT : Submodule S.A T := m • (⊤ : Submodule S.A T)
  let pN : Submodule S.A S.N := m • (⊤ : Submodule S.A S.N)
  let C := S.A ⧸ m
  let eT : C ⊗[S.A] T ≃ₗ[C] T ⧸ pT :=
    (TensorProduct.quotTensorEquivQuotSMul T m).extendScalarsOfSurjective
      IsLocalRing.residue_surjective
  let eN : C ⊗[S.A] S.N ≃ₗ[C] S.N ⧸ pN :=
    (TensorProduct.quotTensorEquivQuotSMul S.N m).extendScalarsOfSurjective
      IsLocalRing.residue_surjective
  let qmap : T ⧸ pT →ₗ[S.A] S.N ⧸ pN :=
    Submodule.mapQ pT pN (T.subtype.restrictScalars S.A)
      (Submodule.smul_top_le_comap_smul_top m (T.subtype.restrictScalars S.A))
  have : Module.Flat S.A (S.N ⧸ T) := quotientTorsion_flat S
  have hTensorInj : Function.Injective
      (LinearMap.lTensor C (T.subtype.restrictScalars S.A)) :=
    (flat_tor_zero (T.subtype.restrictScalars S.A) (T.mkQ.restrictScalars S.A)
      Subtype.val_injective (LinearMap.exact_subtype_mkQ T) T.mkQ_surjective).1
  have hcomm (z : C ⊗[S.A] T) :
      qmap (eT z) = eN (LinearMap.lTensor C (T.subtype.restrictScalars S.A) z) := by
    induction z using TensorProduct.inductionOn with
    | tmul r t =>
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
        simp only [eT, eN, LinearMap.lTensor_tmul]
        change qmap (Submodule.Quotient.mk (s • t)) =
          Submodule.Quotient.mk (s • (t : S.N))
        simp [qmap]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hx (x : T ⧸ pT) :
      eN (LinearMap.lTensor C (T.subtype.restrictScalars S.A) (eT.symm x)) = qmap x := by
    rw [← hcomm, eT.apply_symm_apply]
  intro x y hxy
  exact eT.symm.injective (hTensorInj (eN.injective ((hx x).trans (hxy.trans (hx y).symm))))

/-- For a local homomorphism `A → B` and a `B`-module `T`, if `T = 𝔪_A T` then `T = 𝔪_B T`. -/
theorem top_le_maximalIdeal_smul_top_of_isLocalHom {A B T : Type*} [CommRing A]
    [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [AddCommGroup T] [Module A T] [Module B T] [IsScalarTower A B T]
    (h : (⊤ : Submodule A T) ≤ IsLocalRing.maximalIdeal A • (⊤ : Submodule A T)) :
    (⊤ : Submodule B T) ≤ IsLocalRing.maximalIdeal B • (⊤ : Submodule B T) := by
  intro t _
  have ht : t ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A T) := h Submodule.mem_top
  refine Submodule.smul_induction_on ht ?_ ?_
  · intro a ha x _
    rw [← algebraMap_smul B a x]
    exact Submodule.smul_mem_smul
      (IsLocalRing.map_maximalIdeal_le (algebraMap A B) (Ideal.mem_map_of_mem _ ha))
      Submodule.mem_top
  · exact fun _ _ hx hy => Submodule.add_mem _ hx hy

/-- The `A`-torsion of `N` vanishes.  The map `u` kills the torsion, since `M` is torsion
free; flatness of `N/T` embeds `T/𝔪_A T` into `N/𝔪_A N`; and injectivity of `ū` therefore
collapses `T/𝔪_A T`, so Nakayama's lemma over `B` collapses `T`. -/
private theorem torsion_eq_bot_of_injective_mod_maximalIdeal
    (S : InjectiveModuloMaximalIdealSituation) [IsDomain S.A] [ValuationRing S.A] :
    Submodule.torsion S.A S.N = ⊥ := by
  let T := torsionAsBSubmodule S
  have := torsion_finite S
  have : Module.IsTorsionFree S.A S.M := Module.Flat.isTorsionFree
  let m := IsLocalRing.maximalIdeal S.A
  let pT : Submodule S.A T := m • (⊤ : Submodule S.A T)
  let pN : Submodule S.A S.N := m • (⊤ : Submodule S.A S.N)
  let pM : Submodule S.A S.M := m • (⊤ : Submodule S.A S.M)
  let qmap : T ⧸ pT →ₗ[S.A] S.N ⧸ pN :=
    Submodule.mapQ pT pN (T.subtype.restrictScalars S.A)
      (Submodule.smul_top_le_comap_smul_top m (T.subtype.restrictScalars S.A))
  let qU : S.N ⧸ pN →ₗ[S.A] S.M ⧸ pM :=
    Submodule.mapQ pN pM S.u (Submodule.smul_top_le_comap_smul_top m S.u)
  have hTle : (⊤ : Submodule S.A T) ≤ pT := by
    intro t _
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (t : S.N)).mp t.property
    have hkill : (a : S.A) • S.u (t : S.N) = 0 :=
      (S.u.map_smul _ _).symm.trans ((congrArg S.u ha).trans (map_zero S.u))
    have hu : S.u (t : S.N) = 0 :=
      (smul_eq_zero.mp hkill).resolve_left (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    have hres : pN.mkQ (t : S.N) = 0 := by
      apply S.injective_mod_maximalIdeal
      change qU (pN.mkQ (t : S.N)) = qU (pN.mkQ 0)
      simp [qU, hu]
    have hmap : qmap (Submodule.Quotient.mk t) = 0 := hres
    have htquot : Submodule.Quotient.mk t = 0 := torsion_mapQ_injective S hmap
    exact (Submodule.Quotient.mk_eq_zero pT).mp htquot
  have htopbot : (⊤ : Submodule S.B T) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (IsLocalRing.maximalIdeal S.B) ⊤ Module.Finite.fg_top
      (top_le_maximalIdeal_smul_top_of_isLocalHom hTle)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  refine le_antisymm (fun x hx => ?_) bot_le
  have ht : (⟨x, hx⟩ : T) ∈ (⊤ : Submodule S.B T) := Submodule.mem_top
  rw [htopbot] at ht
  have htx : (⟨x, hx⟩ : T) = 0 := by simpa using ht
  exact congrArg Subtype.val htx

/-- **Stacks Project, Tag 0AT5 (flatness).** In Situation 0AT0 with the base ring `A` a
valuation ring, the finite `B`-module `N` is flat over `A`. -/
@[stacks 0AT5 "flatness"]
theorem flat_of_valuationRing
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    [IsDomain S.A] [ValuationRing S.A] : Module.Flat S.A S.N :=
  Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (torsion_eq_bot_of_injective_mod_maximalIdeal S)

/-- **Stacks Project, Tag 0AT5 (finite presentation).** In Situation 0AT0 with the base ring
`A` a valuation ring, the finite `B`-module `N` is of finite presentation over `B`. -/
@[stacks 0AT5 "finite presentation"]
theorem finitePresentation_of_valuationRing
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    [IsDomain S.A] [ValuationRing S.A] : Module.FinitePresentation S.B S.N :=
  (essentiallyOfFinitePresentation_and_finitePresentation_of_flat_of_valuationRing
    (A := S.A) (B := S.B) (M := S.N)).2 (flat_of_valuationRing S) inferInstance

end AlgebraicGeometry

end
