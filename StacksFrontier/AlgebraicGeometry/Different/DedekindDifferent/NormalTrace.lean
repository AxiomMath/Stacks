module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.LocalProperties.Reduced
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.Support.DedekindDifferentSetup
public import StacksFrontier.AlgebraicGeometry.Discriminant.ProjectiveTraceContraction
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Trace.Integral

/-!
# The generic-fibre trace over a normal base

In the setup for the Dedekind different, normality of the base ring implies that the
generic-fibre trace of every element of `B` already belongs to `A`. Equivalently, `1` lies in
the complementary module, which is the hypothesis under which the Dedekind different is an
ideal of `B`.

## Main results

* `Stacks.Discriminant.trace_algebraMap_mem_range_of_isNormalRing` says that the generic-fibre
  trace of an element of a finite algebra over a normal ring lies in the canonical image of the
  base ring in its total quotient ring.

## Implementation notes

A normal ring need not be a domain, so its total quotient ring `K` need not be a field and the
eigenvalue argument proving integrality of a trace is unavailable over `K` itself. Instead the
trace is pushed into the fraction field of `K ⧸ 𝔭` for each minimal prime `𝔭` of `K`, where the
generic fibre becomes a finite-dimensional algebra over a field; the resulting monic relations
multiply to a monic relation holding modulo every minimal prime, hence exactly, since a normal
ring and therefore its total quotient ring are reduced. Integral closedness of a normal ring in
its total quotient ring then places the trace in the image of `A`.

## References

* [Stacks Project, Tag 0BW1](https://stacks.math.columbia.edu/tag/0BW1)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u v

/-- The image of a finite-projective trace in a field extension of the base is the trace of the
base-changed algebra, so it is integral over any base ring over which the element is. -/
private theorem isIntegral_algebraMap_finiteProjectiveTrace
    {A K L F : Type*} [CommRing A] [CommRing K] [CommRing L] [Field F]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Module.Finite K L] [Module.Projective K L]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    {x : L} (hx : IsIntegral A x) :
    IsIntegral A (algebraMap K F (finiteProjectiveTrace K L (Algebra.lmul K L x))) := by
  classical
  have : SMulCommClass K A F :=
    ⟨fun k a y => by simp only [Algebra.smul_def]; ring⟩
  have : IsScalarTower A F (F ⊗[K] L) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Finite F (F ⊗[K] L) := Module.Finite.base_change K F L
  have hx' : IsIntegral A ((1 : F) ⊗ₜ[K] x) := by
    simpa using hx.map ((Algebra.TensorProduct.includeRight :
      L →ₐ[K] F ⊗[K] L).restrictScalars A)
  have hbase := finiteProjectiveTrace_baseChange K L F (Algebra.lmul K L x)
  rw [Algebra.baseChange_lmul, finiteProjectiveTrace_eq_trace] at hbase
  rw [← hbase]
  exact Algebra.isIntegral_trace_of_finiteDimensional hx'

/-- An element of a reduced Noetherian ring satisfying a monic relation modulo every minimal
prime is integral: the finitely many relations multiply to one lying in the nilradical. -/
private theorem isIntegral_of_forall_minimalPrimes
    {A K : Type*} [CommRing A] [CommRing K] [Algebra A K] [IsNoetherianRing K] [IsReduced K]
    {t : K} (h : ∀ 𝔭 ∈ minimalPrimes K, ∃ p : Polynomial A, p.Monic ∧
      Polynomial.aeval t p ∈ 𝔭) :
    IsIntegral A t := by
  classical
  have hfin : (minimalPrimes K).Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing K ⊥
  set S := hfin.toFinset
  choose! p hpmonic hpmem using h
  set q := ∏ 𝔮 ∈ S, p 𝔮 with hq
  refine ⟨q, Polynomial.monic_prod_of_monic _ _ fun 𝔮 h𝔮 =>
    hpmonic 𝔮 (hfin.mem_toFinset.mp h𝔮), ?_⟩
  have hmem : ∀ 𝔮 : Ideal K, 𝔮.IsPrime → Polynomial.aeval t q ∈ 𝔮 := by
    intro 𝔮 h𝔮
    obtain ⟨𝔭, h𝔭, hle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := 𝔮) bot_le
    refine hle ?_
    rw [hq, map_prod, Finset.prod_eq_prod_sdiff_singleton_mul (hfin.mem_toFinset.mpr h𝔭)]
    exact Ideal.mul_mem_left _ _ (hpmem 𝔭 h𝔭)
  have hnil : IsNilpotent (Polynomial.aeval t q) := by
    rw [← mem_nilradical, nilradical_eq_sInf]
    exact Submodule.mem_sInf.mpr fun 𝔮 h𝔮 => hmem 𝔮 h𝔮
  exact hnil.eq_zero

/-- In the setup for the Dedekind different, if `A` is a normal ring, then the generic-fibre
trace of every element of `B` belongs to the canonical image of `A` in its total quotient
ring. -/
@[stacks 0BW1 "normal_trace"]
theorem trace_algebraMap_mem_range_of_isNormalRing
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (setup : DedekindDifferentSetup A B) (hA : IsNormalRing A) (b : B) :
    letI : Algebra (FractionRing A) (B ⊗[A] FractionRing A) :=
      Algebra.TensorProduct.rightAlgebra
    setup.trace (algebraMap B (B ⊗[A] FractionRing A) b) ∈
      Set.range (algebraMap A (FractionRing A)) := by
  classical
  let : IsNoetherianRing A := setup.isNoetherianRing
  let : Module.Finite A B := setup.finite
  set K := FractionRing A
  set L := B ⊗[A] K
  let : Algebra K L := Algebra.TensorProduct.rightAlgebra
  let : Algebra.Etale K L := setup.etaleGenericFiber
  have : Module.Finite K (K ⊗[A] B) := Module.Finite.base_change A K B
  let eKB : (K ⊗[A] B) ≃ₐ[K] L := Algebra.TensorProduct.commRight A K B
  have : Module.Finite K L := Module.Finite.equiv eKB.toLinearEquiv
  have : Module.Flat K L := Algebra.Smooth.flat K L
  have : Module.FinitePresentation K L :=
    Module.FinitePresentation.of_finite_of_finitePresentation K L
  have : Module.Projective K L := Module.Flat.projective_of_finitePresentation
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A L a = (1 : B) ⊗ₜ[A] algebraMap A K a
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      ← TensorProduct.smul_tmul]
    rfl
  have : IsReduced A := hA.isReduced
  have : IsNoetherianRing K :=
    IsLocalization.isNoetherianRing (nonZeroDivisors A) K inferInstance
  have : IsReduced K := inferInstanceAs (IsReduced (Localization (nonZeroDivisors A)))
  have : IsIntegrallyClosed A := hA.isIntegrallyClosed
  set x : L := algebraMap B L b
  have hxint : IsIntegral A x :=
    (Algebra.IsIntegral.isIntegral (R := A) b).map (IsScalarTower.toAlgHom A B L)
  have htrace : setup.trace x = finiteProjectiveTrace K L (Algebra.lmul K L x) := by
    have ht := finiteProjectiveTrace_eq_contract (R := K) (P := L) (Algebra.lmul K L x)
    simpa [DedekindDifferentSetup.trace] using ht.symm
  have hint : IsIntegral A (finiteProjectiveTrace K L (Algebra.lmul K L x)) := by
    refine isIntegral_of_forall_minimalPrimes fun 𝔭 h𝔭 => ?_
    have : 𝔭.IsPrime := h𝔭.isPrime
    obtain ⟨p, hp, hpz⟩ :=
      isIntegral_algebraMap_finiteProjectiveTrace (A := A) (K := K) (L := L)
        (F := FractionRing (K ⧸ 𝔭)) hxint
    refine ⟨p, hp, ?_⟩
    have hhom : algebraMap K (FractionRing (K ⧸ 𝔭))
        (Polynomial.aeval (finiteProjectiveTrace K L (Algebra.lmul K L x)) p) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
      simpa [IsScalarTower.algebraMap_eq A K (FractionRing (K ⧸ 𝔭))] using hpz
    rw [IsScalarTower.algebraMap_apply K (K ⧸ 𝔭) (FractionRing (K ⧸ 𝔭)),
      Ideal.Quotient.algebraMap_eq] at hhom
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((map_eq_zero_iff _ (IsFractionRing.injective (K ⧸ 𝔭) (FractionRing (K ⧸ 𝔭)))).mp hhom)
  rw [htrace]
  exact IsIntegrallyClosed.isIntegral_iff.mp hint

end Stacks.Discriminant
