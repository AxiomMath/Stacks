module

public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.TensorPower.Symmetric
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.Node.Quadric
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Parameters
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.CompleteLocalRing.QuotientNodal
public import StacksFrontier.RingTheory.CompleteLocalRing.QuotientNodal.NodalQuadraticRelation
public import StacksFrontier.RingTheory.CompleteLocalRing.QuotientNodal.NodalQuadraticRelationTransport
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.FormallySmooth.LocalRings
public import StacksFrontier.RingTheory.MvPowerSeries.CotangentSpace
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization
public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Basic
public import StacksFrontier.RingTheory.Depth.AlgebraMap
public import StacksFrontier.RingTheory.MvPowerSeries.RegularLocal

/-!
# Nodal local algebras

Let `k` be a field and `(A, 𝔪, κ)` a Noetherian local `k`-algebra. `A` is *nodal* when `κ/k` is
separable, `A` is reduced, and the cotangent space `𝔪/𝔪²` is two-dimensional and carries a
nondegenerate quadratic relation vanishing in `𝔪²/𝔪³`. Three descriptions of this condition
agree: the reduced one just given, the one with `IsReduced A` replaced by `depth A = 1`, and the
one asserting that the completion `A^∧` is a two-variable power-series hypersurface
`κ[[x, y]]/(a x² + b x y + c y²)` cut out by a form of nonzero discriminant.

## Main definitions

* `Stacks.Curves.HasNodalCompletion` — the completion of `A` is, as a `k`-algebra, a two-variable
  power-series hypersurface cut out by a nondegenerate binary quadratic form.
* `Stacks.Curves.IsNodalAlgebra` — the reduced characterization of a nodal local algebra.

## Main results

* `Stacks.Curves.isNodalAlgebra_tfae` — the three characterizations of a nodal local algebra are
  equivalent.

## References

* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
-/

@[expose] public section

open IsLocalRing
open Stacks.Flatness.RegularSequenceQuotient

universe u v

namespace Stacks.Curves

/-- A complete local ring with a chosen section of its residue map is a quotient of a finite
variable power series ring over that residue field. -/
private theorem exists_surjective_mvPowerSeries_of_residueSection
    (R : Type v) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (n : ℕ) (y : Fin n → R)
    (hy : Ideal.span (Set.range y) = maximalIdeal R)
    (σ : ResidueField R →+* R)
    (hσ : (residue R).comp σ = RingHom.id (ResidueField R)) :
    ∃ F : MvPowerSeries (Fin n) (ResidueField R) →+* R,
      Function.Surjective F ∧
        (∀ i, F (MvPowerSeries.X i) = y i) ∧
        (∀ c, F (MvPowerSeries.C c) = σ c) := by
  classical
  let f : ResidueField R →+* R := σ
  have hf : Function.Surjective ((residue R).comp f) := by
    intro x
    exact ⟨x, by simp [f, hσ]⟩
  let : WithIdeal (ResidueField R) := ⟨⊥⟩
  have hdiscrete : DiscreteTopology (ResidueField R) := is_bot_adic_iff.1 rfl
  let : WithIdeal R := ⟨maximalIdeal R⟩
  obtain ⟨_, hhausdorff⟩ :=
    (IsAdic.isAdicComplete_iff (I := maximalIdeal R) rfl).1
      (show IsAdicComplete (maximalIdeal R) R from inferInstance)
  let ha : MvPowerSeries.HasEval y :=
    { hpow := fun i => WithIdeal.isTopologicallyNilpotent_of_mem
        (by
          change y i ∈ maximalIdeal R
          rw [← hy]
          exact Ideal.subset_span ⟨i, rfl⟩)
      tendsto_zero := by simp [Filter.cofinite_eq_bot] }
  let F : MvPowerSeries (Fin n) (ResidueField R) →+* R :=
    MvPowerSeries.eval₂Hom (φ := f) continuous_of_discreteTopology ha
  have hFc : ⇑F = MvPowerSeries.eval₂ f y := MvPowerSeries.coe_eval₂Hom _ _
  have hFC : ∀ c, F (MvPowerSeries.C c) = σ c := by
    intro c
    rw [hFc, MvPowerSeries.eval₂_C]
  have hFX : ∀ i, F (MvPowerSeries.X i) = y i := by
    intro i
    rw [hFc, MvPowerSeries.eval₂_X]
  have hmap : Ideal.map F
      (Ideal.span (Set.range (MvPowerSeries.X : Fin n →
        MvPowerSeries (Fin n) (ResidueField R)))) = maximalIdeal R := by
    rw [Ideal.map_span, ← hy, ← Set.range_comp]
    exact congrArg _ (congrArg Set.range (funext hFX))
  have hhaus : IsHausdorff
      (Ideal.map F (Ideal.span (Set.range (MvPowerSeries.X : Fin n →
        MvPowerSeries (Fin n) (ResidueField R))))) R := by
    rw [hmap]
    infer_instance
  have hsurj : Function.Surjective F := by
    refine surjective_of_mk_map_comp_surjective (I := Ideal.span (Set.range
      (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) (ResidueField R)))) F ?_
    intro b
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨c, hc⟩ := hf (Ideal.Quotient.mk (maximalIdeal R) r)
    refine ⟨MvPowerSeries.C c, ?_⟩
    rw [RingHom.comp_apply, hFC c, ← hr]
    exact Ideal.Quotient.eq.2 (by rw [hmap]; exact Ideal.Quotient.eq.1 hc)
  exact ⟨F, hsurj, hFX, hFC⟩

private theorem map_nodalBinaryQuadratic {K : Type u} {R : Type v}
    [Field K] [CommRing R] (F : MvPowerSeries (Fin 2) K →+* R)
    (σ : K →+* R) (x y : R)
    (hC : ∀ z, F (MvPowerSeries.C z) = σ z)
    (hx : F (MvPowerSeries.X 0) = x)
    (hy : F (MvPowerSeries.X 1) = y) (a b c : K) :
    F (nodalBinaryQuadratic a b c) = σ a * x ^ 2 + σ b * x * y + σ c * y ^ 2 := by
  simp [nodalBinaryQuadratic, hC, hx, hy, mul_assoc]

private theorem nodalQuadratic_add_expansion {R : Type*} [CommRing R]
    (a b c x y u v : R) :
    (a * (x + u) ^ 2 + b * (x + u) * (y + v) + c * (y + v) ^ 2) =
      (a * x ^ 2 + b * x * y + c * y ^ 2) +
        (2 * a * x + b * y) * u + (b * x + 2 * c * y) * v +
          (a * u ^ 2 + b * u * v + c * v ^ 2) := by
  ring

private theorem nodalQuadratic_correction_tail_mem {R : Type*} [CommRing R]
    (m : Ideal R) (n : ℕ) (hn : 1 ≤ n) (a b c u v : R)
    (hu : u ∈ m ^ (n + 1)) (hv : v ∈ m ^ (n + 1)) :
    a * u ^ 2 + b * u * v + c * v ^ 2 ∈ m ^ (n + 3) := by
  have hprod (x y : R) (hx : x ∈ m ^ (n + 1)) (hy : y ∈ m ^ (n + 1)) :
      x * y ∈ m ^ (2 * n + 2) := by
    have heq : (n + 1) + (n + 1) = 2 * n + 2 := by omega
    rw [← heq, pow_add]
    exact Ideal.mul_mem_mul hx hy
  have hpow : m ^ (2 * n + 2) ≤ m ^ (n + 3) := by
    apply Ideal.pow_le_pow_right
    omega
  have huu := hpow (hprod u u hu hu)
  have huv := hpow (hprod u v hu hv)
  have hvv := hpow (hprod v v hv hv)
  simpa [pow_two, mul_assoc] using
    Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ huu)
      (Ideal.mul_mem_left _ _ huv)) (Ideal.mul_mem_left _ _ hvv)

private theorem exists_linear_combination_of_mem_span_pair {R : Type*} [CommRing R]
    (g₁ g₂ z : R) (hz : z ∈ Ideal.span ({g₁, g₂} : Set R)) :
    ∃ a b : R, z = g₁ * a + g₂ * b := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · intro z hz
    rcases Set.mem_insert_iff.mp hz with hz | hz
    · subst z
      exact ⟨1, 0, by simp⟩
    · have hz : z = g₂ := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨0, 1, by simp⟩
  · exact ⟨0, 0, by simp⟩
  · intro x y hx hy ⟨a₁, b₁, h₁⟩ ⟨a₂, b₂, h₂⟩
    refine ⟨a₁ + a₂, b₁ + b₂, ?_⟩
    rw [h₁, h₂]
    ring
  · intro r x hx ⟨a, b, heq⟩
    refine ⟨r * a, r * b, ?_⟩
    rw [heq]
    ring

private theorem exists_pair_decomposition_of_mem_mul {R : Type*} [CommRing R]
    (m I : Ideal R) (g₁ g₂ : R) (hgen : Ideal.span ({g₁, g₂} : Set R) = m)
    {z : R} (hz : z ∈ m * I) :
    ∃ u v : R, u ∈ I ∧ v ∈ I ∧ z = g₁ * u + g₂ * v := by
  change z ∈ m • (I : Submodule R R) at hz
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr s hs
    obtain ⟨a, b, hab⟩ := exists_linear_combination_of_mem_span_pair g₁ g₂ r
      (hgen ▸ hr)
    refine ⟨a * s, b * s, Ideal.mul_mem_left _ _ hs,
      Ideal.mul_mem_left _ _ hs, ?_⟩
    rw [hab]
    ring
  · intro x y hx hy
    obtain ⟨u₁, v₁, hu₁, hv₁, heq₁⟩ := hx
    obtain ⟨u₂, v₂, hu₂, hv₂, heq₂⟩ := hy
    refine ⟨u₁ + u₂, v₁ + v₂, Ideal.add_mem _ hu₁ hu₂,
      Ideal.add_mem _ hv₁ hv₂, ?_⟩
    rw [heq₁, heq₂]
    ring

private theorem nodalQuadratic_correction_step {R : Type*} [CommRing R]
    (m : Ideal R) (n : ℕ) (hn : 1 ≤ n) (a b c x y : R)
    (hgrad : Ideal.span ({2 * a * x + b * y, b * x + 2 * c * y} : Set R) = m)
    (hq : a * x ^ 2 + b * x * y + c * y ^ 2 ∈ m ^ (n + 2)) :
    ∃ u v : R, u ∈ m ^ (n + 1) ∧ v ∈ m ^ (n + 1) ∧
      a * (x + u) ^ 2 + b * (x + u) * (y + v) + c * (y + v) ^ 2 ∈ m ^ (n + 3) := by
  have hpow : m ^ (n + 2) = m * m ^ (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Ideal.IsTwoSided.pow_succ]
  obtain ⟨u, v, hu, hv, heq⟩ := exists_pair_decomposition_of_mem_mul m (m ^ (n + 1))
    (2 * a * x + b * y) (b * x + 2 * c * y) hgrad (hpow ▸ hq)
  have hnegU : -u ∈ m ^ (n + 1) := Submodule.neg_mem _ hu
  have hnegV : -v ∈ m ^ (n + 1) := Submodule.neg_mem _ hv
  have hcancel :
      a * x ^ 2 + b * x * y + c * y ^ 2 +
        (2 * a * x + b * y) * -u + (b * x + 2 * c * y) * -v = 0 := by
    rw [heq]
    ring
  refine ⟨-u, -v, hnegU, hnegV, ?_⟩
  rw [nodalQuadratic_add_expansion, hcancel, zero_add]
  exact nodalQuadratic_correction_tail_mem m n hn a b c (-u) (-v) hnegU hnegV

private theorem span_pair_eq_maximal_of_cotangent_span {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (x y : maximalIdeal R)
    (hspan : Submodule.span (ResidueField R)
      ((maximalIdeal R).toCotangent '' ({x, y} : Set (maximalIdeal R))) = ⊤) :
    Ideal.span ({(x : R), (y : R)} : Set R) = maximalIdeal R := by
  let J : Ideal R := Ideal.span ({(x : R), (y : R)} : Set R)
  let N : Submodule R (maximalIdeal R) :=
    Submodule.comap (maximalIdeal R).subtype J
  have hspanR : Submodule.span R
      ((maximalIdeal R).toCotangent '' ({x, y} : Set (maximalIdeal R))) = ⊤ := by
    have hres : (Submodule.span (ResidueField R)
        ((maximalIdeal R).toCotangent '' ({x, y} : Set (maximalIdeal R)))).restrictScalars R =
        ⊤ := by
      rw [Submodule.restrictScalars_eq_top_iff R]
      exact hspan
    rwa [Submodule.restrictScalars_span R (ResidueField R)
      (Ideal.Quotient.mk_surjective)] at hres
  have hxN : x ∈ N := Ideal.subset_span (by simp)
  have hyN : y ∈ N := Ideal.subset_span (by simp)
  have hle : Submodule.span R
      ((maximalIdeal R).toCotangent '' ({x, y} : Set (maximalIdeal R))) ≤
        N.map (maximalIdeal R).toCotangent := by
    rw [Submodule.span_le, Set.image_pair, Set.pair_subset_iff]
    exact ⟨Submodule.mem_map_of_mem hxN, Submodule.mem_map_of_mem hyN⟩
  have hN : N = ⊤ := (CotangentSpace.map_eq_top_iff (M := N)).mp (top_unique (hspanR ▸ hle))
  refine le_antisymm (Ideal.span_le.mpr (Set.pair_subset_iff.2 ⟨x.2, y.2⟩)) fun z hz => ?_
  exact (hN.symm ▸ Submodule.mem_top : (⟨z, hz⟩ : maximalIdeal R) ∈ N)

private theorem span_pair_subtype_eq_top_of_ideal_span_eq_maximal {R : Type*}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (g₁ g₂ : maximalIdeal R)
    (hgrad : Ideal.span ({(g₁ : R), (g₂ : R)} : Set R) = maximalIdeal R) :
    Submodule.span R ({g₁, g₂} : Set (maximalIdeal R)) = ⊤ := by
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨a, b, hab⟩ := exists_linear_combination_of_mem_span_pair
    (g₁ : R) (g₂ : R) (z : R) (hgrad.symm ▸ z.2)
  have heq : z = a • g₁ + b • g₂ := by
    apply Subtype.ext
    change (z : R) = a * (g₁ : R) + b * (g₂ : R)
    rw [hab]
    ring
  rw [heq]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem exists_cotangent_basis_of_pair_generators_and_finrank_two
    (R : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x y : maximalIdeal R)
    (hspan : Ideal.span ({(x : R), (y : R)} : Set R) = maximalIdeal R)
    (hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) = 2) :
    ∃ e : Module.Basis (BinaryIndex (ResidueField R))
        (ResidueField R) (CotangentSpace R),
      e ⟨0⟩ = (maximalIdeal R).toCotangent x ∧
        e ⟨1⟩ = (maximalIdeal R).toCotangent y := by
  let v : BinaryIndex (ResidueField R) → CotangentSpace R :=
    fun i => if i.down = 0 then (maximalIdeal R).toCotangent x
      else (maximalIdeal R).toCotangent y
  have hv₀ : v ⟨0⟩ = (maximalIdeal R).toCotangent x := by simp [v]
  have hv₁ : v ⟨1⟩ = (maximalIdeal R).toCotangent y := by simp [v]
  have hrange : Set.range v =
      {(maximalIdeal R).toCotangent x, (maximalIdeal R).toCotangent y} := by
    ext z
    constructor
    · rintro ⟨⟨i⟩, rfl⟩
      fin_cases i <;> simp [hv₀, hv₁]
    · rintro (rfl | rfl)
      exacts [⟨⟨0⟩, hv₀⟩, ⟨⟨1⟩, hv₁⟩]
  have hspanV : Submodule.span (ResidueField R) (Set.range v) = ⊤ := by
    rw [hrange]
    simpa [Set.image_pair] using CotangentSpace.span_image_eq_top_iff.2
      (span_pair_subtype_eq_top_of_ideal_span_eq_maximal x y hspan)
  have hcard : Fintype.card (BinaryIndex (ResidueField R)) =
      Module.finrank (ResidueField R) (CotangentSpace R) := by
    simp [BinaryIndex, hfinrank]
  have hlin : LinearIndependent (ResidueField R) v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank (by rw [hspanV]) hcard
  let e := Module.Basis.mk hlin hspanV.ge
  refine ⟨e, ?_, ?_⟩
  · simpa only [e, Module.Basis.mk_apply] using hv₀
  · simpa only [e, Module.Basis.mk_apply] using hv₁

private theorem nodal_gradient_span_stable {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (a b c x y u v : R)
    (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R)
    (hu : u ∈ (maximalIdeal R) ^ 2) (hv : v ∈ (maximalIdeal R) ^ 2)
    (hgrad : Ideal.span ({2 * a * x + b * y, b * x + 2 * c * y} : Set R) =
      maximalIdeal R) :
    Ideal.span
      ({2 * a * (x + u) + b * (y + v), b * (x + u) + 2 * c * (y + v)} : Set R) =
      maximalIdeal R := by
  let m := maximalIdeal R
  let g₁ : m := ⟨2 * a * x + b * y,
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_left _ _ hy)⟩
  let g₂ : m := ⟨b * x + 2 * c * y,
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_left _ _ hy)⟩
  have hxu : x + u ∈ m := Ideal.add_mem _ hx (Ideal.pow_le_self two_ne_zero hu)
  have hyv : y + v ∈ m := Ideal.add_mem _ hy (Ideal.pow_le_self two_ne_zero hv)
  let g₁' : m := ⟨2 * a * (x + u) + b * (y + v),
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hxu) (Ideal.mul_mem_left _ _ hyv)⟩
  let g₂' : m := ⟨b * (x + u) + 2 * c * (y + v),
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hxu) (Ideal.mul_mem_left _ _ hyv)⟩
  have hdiff₁ : (g₁' : R) - (g₁ : R) ∈ m ^ 2 := by
    have h₁ : 2 * a * u ∈ m ^ 2 := Ideal.mul_mem_left _ _ hu
    have h₂ : b * v ∈ m ^ 2 := Ideal.mul_mem_left _ _ hv
    convert Ideal.add_mem _ h₁ h₂ using 1; dsimp [g₁', g₁]; ring
  have hdiff₂ : (g₂' : R) - (g₂ : R) ∈ m ^ 2 := by
    have h₁ : b * u ∈ m ^ 2 := Ideal.mul_mem_left _ _ hu
    have h₂ : 2 * c * v ∈ m ^ 2 := Ideal.mul_mem_left _ _ hv
    convert Ideal.add_mem _ h₁ h₂ using 1; dsimp [g₂', g₂]; ring
  have hcot₁ : m.toCotangent g₁' = m.toCotangent g₁ := m.toCotangent_eq.mpr hdiff₁
  have hcot₂ : m.toCotangent g₂' = m.toCotangent g₂ := m.toCotangent_eq.mpr hdiff₂
  have hspanOld : Submodule.span (ResidueField R)
      (m.toCotangent '' ({g₁, g₂} : Set m)) = ⊤ :=
    (CotangentSpace.span_image_eq_top_iff (s := ({g₁, g₂} : Set m))).2
      (span_pair_subtype_eq_top_of_ideal_span_eq_maximal g₁ g₂ hgrad)
  have hset : m.toCotangent '' ({g₁', g₂'} : Set m) =
      m.toCotangent '' ({g₁, g₂} : Set m) := by
    rw [Set.image_pair, Set.image_pair, hcot₁, hcot₂]
  exact span_pair_eq_maximal_of_cotangent_span g₁' g₂' (hset ▸ hspanOld)

/-- A submodule containing both gradient combinations of a pair, for a binary quadratic form of
unit discriminant, contains the pair. -/
private theorem mem_of_nodal_gradient_mem {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (L : Submodule R M) (a b c : R) (e₀ e₁ : M)
    (hd : IsUnit (4 * a * c - b ^ 2))
    (h₀ : (2 * a) • e₀ + b • e₁ ∈ L) (h₁ : b • e₀ + (2 * c) • e₁ ∈ L) :
    e₀ ∈ L ∧ e₁ ∈ L := by
  obtain ⟨u, hu⟩ := hd.exists_left_inv
  constructor
  · have h := L.add_mem (L.smul_mem (u * (2 * c)) h₀) (L.smul_mem (-(u * b)) h₁)
    rwa [show (u * (2 * c)) • ((2 * a) • e₀ + b • e₁) + (-(u * b)) • (b • e₀ + (2 * c) • e₁) =
      (u * (4 * a * c - b ^ 2)) • e₀ by module, hu, one_smul] at h
  · have h := L.add_mem (L.smul_mem (-(u * b)) h₀) (L.smul_mem (u * (2 * a)) h₁)
    rwa [show (-(u * b)) • ((2 * a) • e₀ + b • e₁) + (u * (2 * a)) • (b • e₀ + (2 * c) • e₁) =
      (u * (4 * a * c - b ^ 2)) • e₁ by module, hu, one_smul] at h

private theorem nodal_gradient_generates_maximalIdeal {A : Type v} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A]
    (x y : maximalIdeal A)
    (e : Module.Basis (BinaryIndex (ResidueField A)) (ResidueField A) (CotangentSpace A))
    (a b c : A)
    (hx : e ⟨0⟩ = (maximalIdeal A).toCotangent x)
    (hy : e ⟨1⟩ = (maximalIdeal A).toCotangent y)
    (hdet : residue A (4 * a * c - b ^ 2) ≠ 0) :
    Ideal.span
      ({2 * a * x.1 + b * y.1, b * x.1 + 2 * c * y.1} : Set A) =
      maximalIdeal A := by
  let e₀ : CotangentSpace A := e ⟨0⟩
  let e₁ : CotangentSpace A := e ⟨1⟩
  let d : A := 4 * a * c - b ^ 2
  have hd : IsUnit d := (residue_ne_zero_iff_isUnit d).mp hdet
  let g₁ : maximalIdeal A := ⟨2 * a * x.1 + b * y.1,
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ x.2) (Ideal.mul_mem_left _ _ y.2)⟩
  let g₂ : maximalIdeal A := ⟨b * x.1 + 2 * c * y.1,
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ x.2) (Ideal.mul_mem_left _ _ y.2)⟩
  have harg₁ : g₁ = (2 * a) • x + b • y := rfl
  have harg₂ : g₂ = b • x + (2 * c) • y := rfl
  have hq₁ : (maximalIdeal A).toCotangent g₁ =
      (2 * a) • e₀ + b • e₁ := by
    rw [harg₁, map_add, map_smul, map_smul, ← hx, ← hy]
  have hq₂ : (maximalIdeal A).toCotangent g₂ =
      b • e₀ + (2 * c) • e₁ := by
    rw [harg₂, map_add, map_smul, map_smul, ← hx, ← hy]
  let L : Submodule A (CotangentSpace A) :=
    Submodule.span A {(maximalIdeal A).toCotangent g₁,
      (maximalIdeal A).toCotangent g₂}
  have hq₁mem : (maximalIdeal A).toCotangent g₁ ∈ L :=
    Submodule.subset_span (by simp)
  have hq₂mem : (maximalIdeal A).toCotangent g₂ ∈ L :=
    Submodule.subset_span (by simp)
  obtain ⟨he₀, he₁⟩ :=
    mem_of_nodal_gradient_mem L a b c e₀ e₁ hd (hq₁ ▸ hq₁mem) (hq₂ ▸ hq₂mem)
  have hL : L = ⊤ := by
    have hrange : Set.range (e : BinaryIndex (ResidueField A) → CotangentSpace A) ⊆ L := by
      rintro z ⟨⟨i⟩, rfl⟩
      fin_cases i
      exacts [he₀, he₁]
    have hle : Submodule.span A (Set.range (e : BinaryIndex (ResidueField A) →
        CotangentSpace A)) ≤ L := Submodule.span_le.2 hrange
    have hbase : Submodule.span A (Set.range
        (e : BinaryIndex (ResidueField A) → CotangentSpace A)) = ⊤ := by
      have hres : (Submodule.span (ResidueField A) (Set.range
          (e : BinaryIndex (ResidueField A) → CotangentSpace A))).restrictScalars A = ⊤ := by
        rw [Submodule.restrictScalars_eq_top_iff A]
        exact e.span_eq
      rwa [Submodule.restrictScalars_span A (ResidueField A)
        (Ideal.Quotient.mk_surjective)] at hres
    exact top_unique (hbase ▸ hle)
  have hspan : Submodule.span (ResidueField A)
      ((maximalIdeal A).toCotangent '' ({g₁, g₂} : Set (maximalIdeal A))) = ⊤ := by
    have hres : (Submodule.span (ResidueField A)
        ((maximalIdeal A).toCotangent '' ({g₁, g₂} : Set (maximalIdeal A)))).restrictScalars A =
        ⊤ := by
      rw [Submodule.restrictScalars_span A (ResidueField A)
        (Ideal.Quotient.mk_surjective)]
      simpa [L, Set.image_insert_eq] using hL
    rwa [Submodule.restrictScalars_eq_top_iff A] at hres
  exact span_pair_eq_maximal_of_cotangent_span g₁ g₂ hspan

/-- An invertible binary quadratic Hessian makes the gradient generators equivalent to the
original pair of parameters. -/
private theorem span_pair_eq_maximal_of_nodal_gradient_span {A : Type v} [CommRing A]
    [IsLocalRing A] (x y : maximalIdeal A) (a b c : A)
    (hdet : residue A (4 * a * c - b ^ 2) ≠ 0)
    (hgrad : Ideal.span
      ({2 * a * x.1 + b * y.1, b * x.1 + 2 * c * y.1} : Set A) = maximalIdeal A) :
    Ideal.span ({(x : A), (y : A)} : Set A) = maximalIdeal A := by
  have hd : IsUnit (4 * a * c - b ^ 2) := (residue_ne_zero_iff_isUnit _).mp hdet
  let J : Ideal A := Ideal.span {2 * a * x.1 + b * y.1, b * x.1 + 2 * c * y.1}
  let L : Ideal A := Ideal.span {(x : A), (y : A)}
  obtain ⟨hxJ, hyJ⟩ := mem_of_nodal_gradient_mem J a b c x.1 y.1 hd
    (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  have hLJ : L ≤ J := Ideal.span_le.mpr (Set.pair_subset_iff.2 ⟨hxJ, hyJ⟩)
  have hJL : J ≤ L := by
    apply Ideal.span_le.mpr
    rintro z (hz | hz)
    · subst z
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · subst z
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  exact le_antisymm (Ideal.span_le.mpr (Set.pair_subset_iff.2 ⟨x.2, y.2⟩)) (hgrad.symm.le.trans hJL)

private def NodalCorrectionState (R : Type*) [CommRing R]
    (m : Ideal R) (a b c : R) (n : ℕ) :=
  {p : R × R // p.1 ∈ m ∧ p.2 ∈ m ∧
    a * p.1 ^ 2 + b * p.1 * p.2 + c * p.2 ^ 2 ∈ m ^ (n + 3) ∧
    Ideal.span ({2 * a * p.1 + b * p.2, b * p.1 + 2 * c * p.2} : Set R) = m}

private def NodalCorrectionNext (R : Type*) [CommRing R]
    (m : Ideal R) (a b c : R) (n : ℕ) (s : NodalCorrectionState R m a b c n) :=
  {t : NodalCorrectionState R m a b c (n + 1) //
    t.1.1 - s.1.1 ∈ m ^ (n + 2) ∧ t.1.2 - s.1.2 ∈ m ^ (n + 2)}

private theorem nodalCorrectionNext_nonempty {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (m : Ideal R) (hm : m = maximalIdeal R)
    (a b c : R) (n : ℕ) (s : NodalCorrectionState R m a b c n) :
    Nonempty (NodalCorrectionNext R m a b c n s) := by
  subst hm
  rcases s.2 with ⟨hsx, hsy, hsq, hsgrad⟩
  obtain ⟨u, v, hu, hv, hq⟩ := nodalQuadratic_correction_step (maximalIdeal R)
    (n + 1) (by omega) a b c s.1.1 s.1.2 hsgrad hsq
  have hpow : 2 ≤ n + 2 := by omega
  have hu₂ : u ∈ (maximalIdeal R) ^ 2 := Ideal.pow_le_pow_right hpow hu
  have hv₂ : v ∈ (maximalIdeal R) ^ 2 := Ideal.pow_le_pow_right hpow hv
  have hx : s.1.1 + u ∈ maximalIdeal R :=
    Ideal.add_mem _ hsx (Ideal.pow_le_self two_ne_zero hu₂)
  have hy : s.1.2 + v ∈ maximalIdeal R :=
    Ideal.add_mem _ hsy (Ideal.pow_le_self two_ne_zero hv₂)
  have hgrad := nodal_gradient_span_stable a b c s.1.1 s.1.2 u v
    hsx hsy hu₂ hv₂ hsgrad
  let t : NodalCorrectionState R (maximalIdeal R) a b c (n + 1) :=
    ⟨(s.1.1 + u, s.1.2 + v), hx, hy, by simpa using hq, hgrad⟩
  refine ⟨⟨t, ⟨?_, ?_⟩⟩⟩
  · change (s.1.1 + u) - s.1.1 ∈ (maximalIdeal R) ^ (n + 2)
    simpa using hu
  · change (s.1.2 + v) - s.1.2 ∈ (maximalIdeal R) ^ (n + 2)
    simpa using hv

private noncomputable def nodalCorrectionNext {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (a b c : R) (n : ℕ)
    (s : NodalCorrectionState R (maximalIdeal R) a b c n) :
    NodalCorrectionNext R (maximalIdeal R) a b c n s :=
  Classical.choice (nodalCorrectionNext_nonempty (maximalIdeal R) rfl a b c n s)

private noncomputable def nodalCorrectionSequence {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (a b c : R) :
    NodalCorrectionState R (maximalIdeal R) a b c 0 →
      (n : ℕ) → NodalCorrectionState R (maximalIdeal R) a b c n
  | s₀, 0 => s₀
  | s₀, n + 1 =>
      (nodalCorrectionNext a b c n (nodalCorrectionSequence a b c s₀ n)).1

private theorem nodalCorrectionSequence_step_x {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (a b c : R)
    (s₀ : NodalCorrectionState R (maximalIdeal R) a b c 0) (n : ℕ) :
    (nodalCorrectionSequence a b c s₀ (n + 1)).1.1 -
      (nodalCorrectionSequence a b c s₀ n).1.1 ∈ (maximalIdeal R) ^ (n + 2) := by
  change (nodalCorrectionNext a b c n (nodalCorrectionSequence a b c s₀ n)).1.1.1 -
      (nodalCorrectionSequence a b c s₀ n).1.1 ∈ (maximalIdeal R) ^ (n + 2)
  exact (nodalCorrectionNext a b c n (nodalCorrectionSequence a b c s₀ n)).2.1

private theorem nodalCorrectionSequence_step_y {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (a b c : R)
    (s₀ : NodalCorrectionState R (maximalIdeal R) a b c 0) (n : ℕ) :
    (nodalCorrectionSequence a b c s₀ (n + 1)).1.2 -
      (nodalCorrectionSequence a b c s₀ n).1.2 ∈ (maximalIdeal R) ^ (n + 2) := by
  change (nodalCorrectionNext a b c n (nodalCorrectionSequence a b c s₀ n)).1.1.2 -
      (nodalCorrectionSequence a b c s₀ n).1.2 ∈ (maximalIdeal R) ^ (n + 2)
  exact (nodalCorrectionNext a b c n (nodalCorrectionSequence a b c s₀ n)).2.2

private theorem nodalQuadratic_sub_mem_of_coord_sub_mem {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) (a b c x y x' y' : R)
    (hx : x - x' ∈ I ^ n) (hy : y - y' ∈ I ^ n) :
    a * x ^ 2 + b * x * y + c * y ^ 2 -
      (a * x' ^ 2 + b * x' * y' + c * y' ^ 2) ∈ I ^ n := by
  have h₁ : a * (x - x') * (x + x') ∈ I ^ n :=
    Ideal.mul_mem_right (x + x') _ (Ideal.mul_mem_left _ a hx)
  have h₂ : b * (x - x') * y ∈ I ^ n :=
    Ideal.mul_mem_right y _ (Ideal.mul_mem_left _ b hx)
  have h₃ : b * x' * (y - y') ∈ I ^ n :=
    Ideal.mul_mem_left _ (b * x') hy
  have h₄ : c * (y - y') * (y + y') ∈ I ^ n :=
    Ideal.mul_mem_right (y + y') _ (Ideal.mul_mem_left _ c hy)
  have heq : a * x ^ 2 + b * x * y + c * y ^ 2 -
      (a * x' ^ 2 + b * x' * y' + c * y' ^ 2) =
      a * (x - x') * (x + x') + b * (x - x') * y +
        b * x' * (y - y') + c * (y - y') * (y + y') := by ring
  rw [heq]
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ h₁ h₂) h₃) h₄

private theorem nodalQuadratic_coeff_change_mod_cube {R : Type*} [CommRing R]
    (I : Ideal R) (x y a b c a' b' c' : R)
    (hx : x ∈ I) (hy : y ∈ I)
    (ha : a - a' ∈ I) (hb : b - b' ∈ I) (hc : c - c' ∈ I)
    (hrel : a * x ^ 2 + b * x * y + c * y ^ 2 ∈ I ^ 3) :
    a' * x ^ 2 + b' * x * y + c' * y ^ 2 ∈ I ^ 3 := by
  have hx2 : x ^ 2 ∈ I ^ 2 := Ideal.pow_mem_pow hx 2
  have hxy : x * y ∈ I ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul hx hy
  have hy2 : y ^ 2 ∈ I ^ 2 := Ideal.pow_mem_pow hy 2
  have h₁ : (a - a') * x ^ 2 ∈ I ^ 3 := by
    convert Ideal.mul_mem_mul ha hx2 using 1; ring
  have h₂ : (b - b') * (x * y) ∈ I ^ 3 := by
    convert Ideal.mul_mem_mul hb hxy using 1; ring
  have h₃ : (c - c') * y ^ 2 ∈ I ^ 3 := by
    convert Ideal.mul_mem_mul hc hy2 using 1; ring
  have hdiff : (a * x ^ 2 + b * x * y + c * y ^ 2) -
      (a' * x ^ 2 + b' * x * y + c' * y ^ 2) ∈ I ^ 3 := by
    convert Ideal.add_mem _ (Ideal.add_mem _ h₁ h₂) h₃ using 1; ring
  convert Ideal.sub_mem _ hrel hdiff using 1; ring

private theorem exists_exact_nodal_quadratic_root {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (a b c x₀ y₀ : R)
    (hx₀ : x₀ ∈ maximalIdeal R) (hy₀ : y₀ ∈ maximalIdeal R)
    (hq₀ : a * x₀ ^ 2 + b * x₀ * y₀ + c * y₀ ^ 2 ∈ (maximalIdeal R) ^ 3)
    (hgrad₀ : Ideal.span
      ({2 * a * x₀ + b * y₀, b * x₀ + 2 * c * y₀} : Set R) = maximalIdeal R) :
    ∃ xlim ylim : R,
      xlim ∈ maximalIdeal R ∧ ylim ∈ maximalIdeal R ∧
      a * xlim ^ 2 + b * xlim * ylim + c * ylim ^ 2 = 0 ∧
      Ideal.span ({2 * a * xlim + b * ylim, b * xlim + 2 * c * ylim} : Set R) =
        maximalIdeal R ∧
      xlim - x₀ ∈ (maximalIdeal R) ^ 2 ∧
      ylim - y₀ ∈ (maximalIdeal R) ^ 2 := by
  let s₀ : NodalCorrectionState R (maximalIdeal R) a b c 0 :=
    ⟨(x₀, y₀), hx₀, hy₀, by simpa using hq₀, hgrad₀⟩
  let S := nodalCorrectionSequence a b c s₀
  let f : ℕ → R := fun n => (S n).1.1
  let g : ℕ → R := fun n => (S n).1.2
  have htel (z : ℕ → R) : ∀ p q, p ≤ q →
      z p - z q = ∑ k ∈ Finset.Ico p q, (z k - z (k + 1)) := by
    intro p q hpq
    induction q generalizing p with
    | zero =>
        have : p = 0 := Nat.eq_zero_of_le_zero hpq
        subst p
        simp
    | succ q ih =>
        by_cases hpq' : p ≤ q
        · calc
            z p - z (q + 1) = (z p - z q) + (z q - z (q + 1)) := by ring
            _ = (∑ k ∈ Finset.Ico p q, (z k - z (k + 1))) +
                  (z q - z (q + 1)) := by rw [ih p hpq']
            _ = ∑ k ∈ Finset.Ico p (q + 1), (z k - z (k + 1)) := by
              rw [Finset.sum_Ico_succ_top hpq']
        · have hpq'' : p = q + 1 := by omega
          subst p
          simp
  have hlim (z : ℕ → R) (hz : ∀ n, z (n + 1) - z n ∈ (maximalIdeal R) ^ (n + 2)) :
      ∃ l, (∀ n, l - z n ∈ (maximalIdeal R) ^ n) ∧ l - z 0 ∈ (maximalIdeal R) ^ 2 := by
    have hcauchy : AdicCompletion.IsAdicCauchy (maximalIdeal R) R z := by
      intro p q hpq
      rw [SModEq.sub_mem]
      have hsum : (∑ k ∈ Finset.Ico p q, (z k - z (k + 1))) ∈ (maximalIdeal R) ^ p := by
        apply Submodule.sum_mem
        intro k hk
        rcases Finset.mem_Ico.mp hk with ⟨hpk, hkq⟩
        rw [show z k - z (k + 1) = -(z (k + 1) - z k) by ring]
        exact Submodule.neg_mem _ (Ideal.pow_le_pow_right (by omega) (hz k))
      have hdiff : z p - z q ∈ (maximalIdeal R) ^ p := (htel z p q hpq) ▸ hsum
      simpa [smul_eq_mul, Ideal.mul_top] using hdiff
    obtain ⟨l, hl⟩ := IsPrecomplete.prec IsAdicComplete.toIsPrecomplete hcauchy
    have hl_mem (n : ℕ) : l - z n ∈ (maximalIdeal R) ^ n := by
      simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using (hl n).symm
    refine ⟨l, hl_mem, ?_⟩
    have hstep₁ : z 2 - z 1 ∈ (maximalIdeal R) ^ 2 := Ideal.pow_le_pow_right (by omega) (hz 1)
    have h : l - z 0 = (l - z 2) + (z 2 - z 1) + (z 1 - z 0) := by ring
    rw [h]
    exact Ideal.add_mem _ (Ideal.add_mem _ (hl_mem 2) hstep₁) (hz 0)
  obtain ⟨xlim, hxlim_mem, hxclose⟩ := hlim f (nodalCorrectionSequence_step_x a b c s₀)
  obtain ⟨ylim, hylim_mem, hyclose⟩ := hlim g (nodalCorrectionSequence_step_y a b c s₀)
  have hQlim (n : ℕ) :
      a * xlim ^ 2 + b * xlim * ylim + c * ylim ^ 2 -
        (a * f n ^ 2 + b * f n * g n + c * g n ^ 2) ∈ (maximalIdeal R) ^ n :=
    nodalQuadratic_sub_mem_of_coord_sub_mem (maximalIdeal R) n a b c xlim ylim (f n) (g n)
      (hxlim_mem n) (hylim_mem n)
  have hQall (n : ℕ) : a * xlim ^ 2 + b * xlim * ylim + c * ylim ^ 2 ∈
      (maximalIdeal R) ^ n := by
    have hq : a * f n ^ 2 + b * f n * g n + c * g n ^ 2 ∈ (maximalIdeal R) ^ n :=
      Ideal.pow_le_pow_right (by omega) (S n).2.2.2.1
    simpa using Ideal.add_mem _ (hQlim n) hq
  have hQzero : a * xlim ^ 2 + b * xlim * ylim + c * ylim ^ 2 = 0 := by
    apply (IsAdicComplete.toIsHausdorff (I := maximalIdeal R) (M := R)).haus
    intro n
    change a * xlim ^ 2 + b * xlim * ylim + c * ylim ^ 2 ≡
      0 [SMOD (maximalIdeal R) ^ n • ⊤]
    rw [SModEq.sub_mem]
    simpa [smul_eq_mul, Ideal.mul_top] using hQall n
  let s₂ := S 2
  have hfx₂ : f 2 ∈ maximalIdeal R := s₂.2.1
  have hgy₂ : g 2 ∈ maximalIdeal R := s₂.2.2.1
  have hpow2 : (maximalIdeal R) ^ 2 ≤ maximalIdeal R := Ideal.pow_le_self two_ne_zero
  have hxlim_local : xlim ∈ maximalIdeal R := by
    simpa [sub_add_cancel] using Ideal.add_mem _ (hpow2 (hxlim_mem 2)) hfx₂
  have hylim_local : ylim ∈ maximalIdeal R := by
    simpa [sub_add_cancel] using Ideal.add_mem _ (hpow2 (hylim_mem 2)) hgy₂
  have hgrad₂ : Ideal.span ({2 * a * f 2 + b * g 2, b * f 2 + 2 * c * g 2} : Set R) =
      maximalIdeal R := s₂.2.2.2.2
  have hgrad' := nodal_gradient_span_stable a b c (f 2) (g 2)
    (xlim - f 2) (ylim - g 2) hfx₂ hgy₂ (hxlim_mem 2) (hylim_mem 2) hgrad₂
  have hgradlim : Ideal.span ({2 * a * xlim + b * ylim, b * xlim + 2 * c * ylim} : Set R) =
      maximalIdeal R := by
    simpa [sub_add_cancel] using hgrad'
  exact ⟨xlim, ylim, hxlim_local, hylim_local, hQzero, hgradlim, hxclose, hyclose⟩

private theorem coefficients_mem_maximalIdeal_of_quadratic_relation
    {R : Type*} [CommRing R] [IsRegularLocalRing R] (x y a b c : R)
    (hspan : Ideal.span ({x, y} : Set R) = maximalIdeal R)
    (hrank : (maximalIdeal R).spanFinrank = 2)
    (hrel : a * x ^ 2 + b * x * y + c * y ^ 2 ∈ (maximalIdeal R) ^ 3) :
    a ∈ maximalIdeal R ∧ b ∈ maximalIdeal R ∧ c ∈ maximalIdeal R := by
  have hgen : Ideal.ofList [x, y] = maximalIdeal R := by
    have hset : ({r | r ∈ [x, y]} : Set R) = {x, y} := by
      ext r
      simp [eq_comm, or_comm]
    simpa only [Ideal.ofList, hset] using hspan
  have hlen : [x, y].length = (maximalIdeal R).spanFinrank := by simp [hrank]
  have hreg :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).1
      [x, y] hgen hlen |>.1
  have hqr := Stacks.QuasiregularSequence.isRegular_isQuasiregularSeq_self [x, y] hreg
  let coeff : (Fin [x, y].length → ℕ) → R := fun I =>
    if I = ![2, 0] then a else if I = ![1, 1] then b else if I = ![0, 2] then c else 0
  have hant : Finset.Nat.antidiagonalTuple 2 2 = {![0, 2], ![1, 1], ![2, 0]} := by decide
  have hsum : (∑ I ∈ Finset.Nat.antidiagonalTuple [x, y].length 2,
      Stacks.QuasiregularSequence.listPow [x, y] I • coeff I) =
      a * x ^ 2 + b * x * y + c * y ^ 2 := by
    simp [hant, coeff, Stacks.QuasiregularSequence.listPow]
    ring
  have hsumMem : (∑ I ∈ Finset.Nat.antidiagonalTuple [x, y].length 2,
      Stacks.QuasiregularSequence.listPow [x, y] I • coeff I) ∈
      (Ideal.ofList [x, y] ^ (2 + 1)) • (⊤ : Submodule R R) := by
    rw [hsum, hgen]
    simpa [smul_eq_mul, Ideal.mul_top] using hrel
  have ha := hqr 2 coeff hsumMem ![2, 0] (by simp [hant])
  have hb := hqr 2 coeff hsumMem ![1, 1] (by simp [hant])
  have hc := hqr 2 coeff hsumMem ![0, 2] (by simp [hant])
  simpa [coeff, hgen, smul_eq_mul, Ideal.mul_top] using And.intro ha (And.intro hb hc)

private theorem not_isRegularLocalRing_of_hasNodalQuadraticRelation
    (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hnodal : HasNodalQuadraticRelation A) : ¬ IsRegularLocalRing A := by
  intro hregular
  let : IsRegularLocalRing A := hregular
  obtain ⟨q, x, y, e, a, b, c, hx, hy, hq, hdet, hrel⟩ := hnodal
  have hgrad := nodal_gradient_generates_maximalIdeal x y e a b c hx hy hdet
  have hspan := span_pair_eq_maximal_of_nodal_gradient_span x y a b c hdet hgrad
  have hrank : (maximalIdeal A).spanFinrank = 2 := by
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      Module.finrank_eq_card_basis e]
    simp [BinaryIndex]
  obtain ⟨ha, hb, hc⟩ :=
    coefficients_mem_maximalIdeal_of_quadratic_relation x.1 y.1 a b c hspan hrank hrel
  apply hdet
  simp [(residue_eq_zero_iff a).2 ha, (residue_eq_zero_iff b).2 hb, (residue_eq_zero_iff c).2 hc]

private theorem ringKrullDim_eq_one_of_isReduced_and_hasNodalQuadraticRelation
    (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hred : IsReduced A) (hnodal : HasNodalQuadraticRelation A) :
    ringKrullDim A = 1 := by
  let : IsReduced A := hred
  have hcot : Module.finrank (ResidueField A) (CotangentSpace A) = 2 :=
    finrank_cotangentSpace_eq_two_of_hasNodalQuadraticRelation hnodal
  have hspan : (maximalIdeal A).spanFinrank = 2 := by
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hcot]
  have hdimle : ringKrullDim A ≤ (2 : WithBot ℕ∞) := by
    calc
      ringKrullDim A ≤ ((maximalIdeal A).spanFinrank : WithBot ℕ∞) :=
        ringKrullDim_le_spanFinrank_maximalIdeal A
      _ = 2 := by rw [hspan]; norm_num
  have hdimne2 : ringKrullDim A ≠ 2 := by
    intro hdim
    have hregular : IsRegularLocalRing A :=
      IsRegularLocalRing.of_spanFinrank_maximalIdeal_le A (by rw [hspan, hdim]; norm_num)
    exact (not_isRegularLocalRing_of_hasNodalQuadraticRelation A hnodal) hregular
  have hdimne0 : ringKrullDim A ≠ 0 := by
    intro hdim
    let : Ring.KrullDimLE 0 A :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
    have hzero : Module.finrank (ResidueField A) (CotangentSpace A) = 0 :=
      finrank_cotangentSpace_eq_zero_iff.mpr Ring.KrullDimLE.isField_of_isReduced
    omega
  have htop : ringKrullDim A ≠ ⊤ := ringKrullDim_ne_top
  have hbot : ringKrullDim A ≠ ⊥ := ringKrullDim_ne_bot
  lift ringKrullDim A to ℕ∞ using hbot with d hd
  lift d to ℕ using (by simpa using htop) with n hn
  have hn2 : n ≤ 2 := WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hdimle)
  have hnne2 : n ≠ 2 := fun he => hdimne2 (by norm_num [he])
  have hnne0 : n ≠ 0 := fun he => hdimne0 (by norm_num [he])
  have hne : n = 1 := by omega
  norm_num [hne]

private theorem depth_eq_one_of_isReduced_and_hasNodalQuadraticRelation
    (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hred : IsReduced A) (hnodal : HasNodalQuadraticRelation A) :
    Module.depth A (maximalIdeal A) A = 1 := by
  let : IsReduced A := hred
  exact IsLocalRing.depth_eq_one_of_isReduced
    (ringKrullDim_eq_one_of_isReduced_and_hasNodalQuadraticRelation A hred hnodal)

private theorem isReduced_of_isReduced_maximalIdeal_completion
    (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (h : IsReduced (AdicCompletion (maximalIdeal A) A)) : IsReduced A := by
  exact isReduced_of_injective (algebraMap A (AdicCompletion (maximalIdeal A) A))
    (AdicCompletion.of_injective (maximalIdeal A) A)

private theorem exists_surjective_nodal_series_map_of_complete_relation
    (R : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (σ : ResidueField R →+* R)
    (hσ : (residue R).comp σ = RingHom.id (ResidueField R))
    (a b c : ResidueField R) (hdet : 4 * a * c - b ^ 2 ≠ 0)
    (x₀ y₀ : R) (hx₀ : x₀ ∈ maximalIdeal R) (hy₀ : y₀ ∈ maximalIdeal R)
    (hrel : σ a * x₀ ^ 2 + σ b * x₀ * y₀ + σ c * y₀ ^ 2 ∈ (maximalIdeal R) ^ 3)
    (hgrad : Ideal.span
      ({2 * σ a * x₀ + σ b * y₀, σ b * x₀ + 2 * σ c * y₀} : Set R) = maximalIdeal R) :
    ∃ F : MvPowerSeries (Fin 2) (ResidueField R) →+* R,
      Function.Surjective F ∧ F (nodalBinaryQuadratic a b c) = 0 ∧
        F (MvPowerSeries.X 0) - x₀ ∈ (maximalIdeal R) ^ 2 ∧
        F (MvPowerSeries.X 1) - y₀ ∈ (maximalIdeal R) ^ 2 ∧
        (∀ z, F (MvPowerSeries.C z) = σ z) := by
  obtain ⟨x, y, hx, hy, hQ, hgrad', hxclose, hyclose⟩ :=
    exists_exact_nodal_quadratic_root (σ a) (σ b) (σ c) x₀ y₀ hx₀ hy₀ hrel hgrad
  have hσ' (z : ResidueField R) : residue R (σ z) = z := RingHom.congr_fun hσ z
  have hdetR : residue R (4 * σ a * σ c - (σ b) ^ 2) ≠ 0 := fun hzero =>
    hdet (by simpa [map_sub, map_mul, map_pow, map_ofNat, hσ'] using hzero)
  have hspan := span_pair_eq_maximal_of_nodal_gradient_span
    (⟨x, hx⟩ : maximalIdeal R) (⟨y, hy⟩ : maximalIdeal R)
    (σ a) (σ b) (σ c) hdetR hgrad'
  let coords : Fin 2 → R := ![x, y]
  have hcoordsSpan : Ideal.span (Set.range coords) = maximalIdeal R := by
    rw [Matrix.range_cons_cons_empty]
    exact hspan
  obtain ⟨F, hsurj, hX, hC⟩ :=
    exists_surjective_mvPowerSeries_of_residueSection R 2 coords hcoordsSpan σ hσ
  have hxF : F (MvPowerSeries.X 0) = x := hX 0
  have hyF : F (MvPowerSeries.X 1) = y := hX 1
  refine ⟨F, hsurj, ?_, ?_, ?_, hC⟩
  · exact (map_nodalBinaryQuadratic F σ x y hC hxF hyF a b c).trans hQ
  · simpa [hxF] using hxclose
  · simpa [hyF] using hyclose


private theorem ringKrullDim_mvPowerSeries_fin_two (K : Type*) [Field K] :
    ringKrullDim (MvPowerSeries (Fin 2) K) = 2 := by
  let : IsRegularLocalRing (MvPowerSeries (Fin 2) K) :=
    isRegularLocalRing_mvPowerSeries K 2
  rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace
    (MvPowerSeries (Fin 2) K)).mp inferInstance,
    Stacks.MvPowerSeries.RegularParameters.finrank_cotangentSpace_field]
  norm_num

private theorem maximalIdeal_mvPowerSeries_eq_span_X
    (K : Type*) [Field K] (n : ℕ) :
    maximalIdeal (MvPowerSeries (Fin n) K) =
      Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) K)) := by
  classical
  refine le_antisymm ?_ (Ideal.span_le.mpr ?_)
  · intro f hf
    have hzero := Stacks.MvPowerSeries.RegularParameters.constantCoeff_eq_zero_of_mem_maximalIdeal
      hf
    have hmem :=
      Stacks.MvPowerSeries.RegularParameters.QuotInitVars.mem_span_X_image_of_coeff_eq_zero
        Finset.univ f
      (fun α hα => by
        have : α = 0 := Finsupp.ext fun i => hα i (Finset.mem_univ i)
        simpa [this] using hzero)
    simpa using hmem
  · rintro _ ⟨i, rfl⟩
    change MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) K)
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp

/-- The maximal ideal of a two-variable power series ring is spanned by the two variables. -/
private theorem span_pair_X_eq_maximalIdeal_mvPowerSeries_fin_two (K : Type*) [Field K] :
    Ideal.span ({MvPowerSeries.X 0, MvPowerSeries.X 1} : Set (MvPowerSeries (Fin 2) K)) =
      maximalIdeal (MvPowerSeries (Fin 2) K) := by
  rw [maximalIdeal_mvPowerSeries_eq_span_X K 2]
  congr 1
  ext z
  simp [Fin.exists_fin_two, eq_comm]

private theorem nodalBinaryQuadratic_not_mem_cube_maximalIdeal
    {K : Type u} [Field K] (a b c : K) (hdet : 4 * a * c - b ^ 2 ≠ 0) :
    nodalBinaryQuadratic a b c ∉ (maximalIdeal (MvPowerSeries (Fin 2) K)) ^ 3 := by
  let P := MvPowerSeries (Fin 2) K
  let : IsRegularLocalRing P := isRegularLocalRing_mvPowerSeries K 2
  have hspan := span_pair_X_eq_maximalIdeal_mvPowerSeries_fin_two K
  have hrank : (maximalIdeal P).spanFinrank = 2 := by
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      Stacks.MvPowerSeries.RegularParameters.finrank_cotangentSpace_field]
  intro hQ
  have hrel : MvPowerSeries.C a * MvPowerSeries.X 0 ^ 2 +
      MvPowerSeries.C b * MvPowerSeries.X 0 * MvPowerSeries.X 1 +
      MvPowerSeries.C c * MvPowerSeries.X 1 ^ 2 ∈ (maximalIdeal P) ^ 3 := by
    simpa [nodalBinaryQuadratic, mul_assoc] using hQ
  obtain ⟨ha, hb, hc⟩ :=
    coefficients_mem_maximalIdeal_of_quadratic_relation
      (MvPowerSeries.X (R := K) 0) (MvPowerSeries.X (R := K) 1)
      (MvPowerSeries.C a) (MvPowerSeries.C b) (MvPowerSeries.C c)
      hspan hrank hrel
  have ha0 : a = 0 := by
    simpa using Stacks.MvPowerSeries.RegularParameters.constantCoeff_eq_zero_of_mem_maximalIdeal ha
  have hb0 : b = 0 := by
    simpa using Stacks.MvPowerSeries.RegularParameters.constantCoeff_eq_zero_of_mem_maximalIdeal hb
  have hc0 : c = 0 := by
    simpa using Stacks.MvPowerSeries.RegularParameters.constantCoeff_eq_zero_of_mem_maximalIdeal hc
  exact hdet (by simp [ha0, hb0, hc0])

private theorem image_regular_sequences_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) :
    List.map e '' {rs : List R | (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular R rs} =
      {ss : List S | (∀ s ∈ ss, s ∈ I.map e) ∧ RingTheory.Sequence.IsRegular S ss} := by
  have hmem : ∀ a : R, e a ∈ I.map e ↔ a ∈ I := fun _ => by simp
  ext ss
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨rs, ⟨hI, hrs⟩, rfl⟩
    refine ⟨fun s hs => ?_, (isRegular_ringEquiv_congr e rs).mp hrs⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
    exact (hmem r).mpr (hI r hr)
  · rintro ⟨hI, hss⟩
    have hmap : (ss.map e.symm).map e = ss := by simp [List.map_map, Function.comp_def]
    refine ⟨ss.map e.symm, ⟨fun r hr => ?_,
      (isRegular_ringEquiv_congr e _).mpr (by rw [hmap]; exact hss)⟩, hmap⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact (hmem _).mp (by simpa using hI s hs)

private theorem depth_self_eq_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) :
    Module.depth R I R = Module.depth S (I.map e) S := by
  have htop : I • (⊤ : Submodule R R) = ⊤ ↔
      (I.map e) • (⊤ : Submodule S S) = ⊤ := by
    simp only [smul_eq_mul, Ideal.mul_top, ← Ideal.comap_symm, Ideal.comap_eq_top_iff]
  simp only [Module.depth, htop, ← image_regular_sequences_ringEquiv e I,
    iSup_image, List.length_map]

open IsRegularLocalRing in
private theorem kernel_principal_of_surjective_binary_series_map
    {K : Type u} {R : Type v} [Field K] [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (F : MvPowerSeries (Fin 2) K →+* R) (hF : Function.Surjective F)
    (hdepth : Module.depth R (maximalIdeal R) R = 1) :
    ∃ f : MvPowerSeries (Fin 2) K,
      f ≠ 0 ∧ f ∈ maximalIdeal (MvPowerSeries (Fin 2) K) ∧
        RingHom.ker F = Ideal.span {f} := by
  let P := MvPowerSeries (Fin 2) K
  let : IsRegularLocalRing P := isRegularLocalRing_mvPowerSeries K 2
  let I := RingHom.ker F
  let Q := P ⧸ I
  have : IsLocalHom F := IsLocalHom.of_surjective F hF
  have hI : I ≤ maximalIdeal P := by
    rw [← IsLocalRing.maximalIdeal_comap F]
    exact Ideal.comap_mono bot_le
  let e : Q ≃+* R := RingHom.quotientKerEquivOfSurjective hF
  let : IsLocalRing Q := e.symm.isLocalRing
  have hdepthQ : Module.depth Q (maximalIdeal Q) Q = 1 := by
    have h := depth_self_eq_of_ringEquiv e (maximalIdeal Q)
    rw [IsLocalRing.map_ringEquiv_maximalIdeal e] at h
    exact h.trans hdepth
  have hdepthasP : Module.depth P (maximalIdeal P) Q = 1 := by
    have h := Module.depth_eq_depth_map_algebraMap
      (A := P) (B := Q) (M := Q) Ideal.Quotient.mk_surjective (maximalIdeal P)
    rw [IsLocalRing.map_maximalIdeal_of_surjective (algebraMap P Q)
      (show Function.Surjective (algebraMap P Q) from Ideal.Quotient.mk_surjective)] at h
    exact h.trans hdepthQ
  exact exists_ne_zero_mem_maximalIdeal_and_eq_span_singleton_of_quotient_depth_eq_one
    (ringKrullDim_mvPowerSeries_fin_two K) I hI hdepthasP

private theorem kernel_le_square_of_cotangent_basis
    {K : Type u} {R : Type v} [Field K] [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (F : MvPowerSeries (Fin 2) K →+* R) (hF : Function.Surjective F)
    (x y : maximalIdeal R)
    (e : Module.Basis (BinaryIndex (ResidueField R))
      (ResidueField R) (CotangentSpace R))
    (hx : F (MvPowerSeries.X 0) = x.1)
    (hy : F (MvPowerSeries.X 1) = y.1)
    (he₀ : e ⟨0⟩ = (maximalIdeal R).toCotangent x)
    (he₁ : e ⟨1⟩ = (maximalIdeal R).toCotangent y) :
    RingHom.ker F ≤ (maximalIdeal (MvPowerSeries (Fin 2) K)) ^ 2 := by
  let P := MvPowerSeries (Fin 2) K
  let : IsRegularLocalRing P := isRegularLocalRing_mvPowerSeries K 2
  have : IsLocalHom F := IsLocalHom.of_surjective F hF
  have hkerM : RingHom.ker F ≤ maximalIdeal P := by
    rw [← IsLocalRing.maximalIdeal_comap F]
    exact Ideal.comap_mono bot_le
  intro p hp
  have hpM : p ∈ maximalIdeal P := hkerM hp
  have hpcc : MvPowerSeries.constantCoeff p = 0 :=
    Stacks.MvPowerSeries.RegularParameters.constantCoeff_eq_zero_of_mem_maximalIdeal hpM
  obtain ⟨g, _, hdecomp⟩ :=
    Stacks.MvPowerSeries.RegularParameters.exists_sum_X_mul_of_constantCoeff_eq_zero p hpcc
  have hFp : F p = 0 := RingHom.mem_ker.mp hp
  have hEq : x.1 * F (g 0) + y.1 * F (g 1) = 0 := by
    rw [hdecomp] at hFp
    simpa [Fin.sum_univ_two, hx, hy] using hFp
  let z : maximalIdeal R :=
    ⟨x.1 * F (g 0) + y.1 * F (g 1),
      Ideal.add_mem _ (Ideal.mul_mem_right _ _ x.2) (Ideal.mul_mem_right _ _ y.2)⟩
  have hz : z = F (g 0) • x + F (g 1) • y := by
    apply Subtype.ext
    change x.1 * F (g 0) + y.1 * F (g 1) =
      F (g 0) * x.1 + F (g 1) * y.1
    ring
  have hz0 : (maximalIdeal R).toCotangent z = 0 := by simp [show z = 0 from Subtype.ext hEq]
  rw [hz, map_add, map_smul, map_smul, ← he₀, ← he₁] at hz0
  have hlin : residue R (F (g 0)) • e ⟨0⟩ +
      residue R (F (g 1)) • e ⟨1⟩ = 0 := hz0
  have hg₀zero : residue R (F (g 0)) = 0 := by
    simpa using congrArg (fun v : CotangentSpace R => e.repr v ⟨0⟩) hlin
  have hg₁zero : residue R (F (g 1)) = 0 := by
    simpa using congrArg (fun v : CotangentSpace R => e.repr v ⟨1⟩) hlin
  have hg₀ : g 0 ∈ maximalIdeal P := by
    rw [← IsLocalRing.maximalIdeal_comap F]
    exact (residue_eq_zero_iff _).mp hg₀zero
  have hg₁ : g 1 ∈ maximalIdeal P := by
    rw [← IsLocalRing.maximalIdeal_comap F]
    exact (residue_eq_zero_iff _).mp hg₁zero
  have hX₀ : (MvPowerSeries.X (R := K) 0) ∈ maximalIdeal P := by
    rw [Stacks.MvPowerSeries.RegularParameters.mem_maximalIdeal_iff_constantCoeff_eq_zero_field]
    simp
  have hX₁ : (MvPowerSeries.X (R := K) 1) ∈ maximalIdeal P := by
    rw [Stacks.MvPowerSeries.RegularParameters.mem_maximalIdeal_iff_constantCoeff_eq_zero_field]
    simp
  rw [hdecomp]
  simp only [Fin.sum_univ_two]
  exact Ideal.add_mem _
    (by simpa [pow_two] using Ideal.mul_mem_mul hX₀ hg₀)
    (by simpa [pow_two] using Ideal.mul_mem_mul hX₁ hg₁)

private theorem kernel_eq_nodalQuadratic_span_of_second_order_kernel
    {K : Type u} {R : Type v} [Field K] [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R]
    (F : MvPowerSeries (Fin 2) K →+* R) (hF : Function.Surjective F)
    (hdepth : Module.depth R (maximalIdeal R) R = 1)
    (hkerSq : RingHom.ker F ≤ (maximalIdeal (MvPowerSeries (Fin 2) K)) ^ 2)
    (a b c : K) (hdet : 4 * a * c - b ^ 2 ≠ 0)
    (hQ : F (nodalBinaryQuadratic a b c) = 0) :
    RingHom.ker F = Ideal.span {nodalBinaryQuadratic a b c} := by
  obtain ⟨f, _, _, hker⟩ :=
    kernel_principal_of_surjective_binary_series_map F hF hdepth
  have hqmem : nodalBinaryQuadratic a b c ∈ Ideal.span {f} := hker ▸ RingHom.mem_ker.mpr hQ
  obtain ⟨g, hgf⟩ := Ideal.mem_span_singleton'.mp hqmem
  have hfSq : f ∈ (maximalIdeal (MvPowerSeries (Fin 2) K)) ^ 2 :=
    hkerSq (hker.symm ▸ Ideal.mem_span_singleton_self f)
  have hgnot : g ∉ maximalIdeal (MvPowerSeries (Fin 2) K) := by
    intro hg
    apply nodalBinaryQuadratic_not_mem_cube_maximalIdeal a b c hdet
    rw [← hgf]
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using Ideal.mul_mem_mul hg hfSq
  have hgunit : IsUnit g := IsLocalRing.notMem_maximalIdeal.mp hgnot
  rw [hker, ← hgf]
  exact (Ideal.span_singleton_mul_left_unit hgunit f).symm

private theorem exists_nodal_series_map_of_complete_depth_one
    (k : Type u) (R : Type v) [Field k] [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [Algebra k R]
    [IsAdicComplete (maximalIdeal R) R]
    (hsep : Algebra.IsSeparableExtension k (ResidueField R))
    (hdepth : Module.depth R (maximalIdeal R) R = 1)
    (hnodal : HasNodalQuadraticRelation R) :
    ∃ a b c : ResidueField R,
      4 * a * c - b ^ 2 ≠ 0 ∧
        ∃ (σ : ResidueField R →ₐ[k] R)
          (F : MvPowerSeries (Fin 2) (ResidueField R) →+* R),
          Function.Surjective F ∧
          RingHom.ker F = Ideal.span {nodalBinaryQuadratic a b c} ∧
          (∀ z, F (MvPowerSeries.C z) = σ z) := by
  obtain ⟨q, x, y, e, a₀, b₀, c₀, hx, hy, hq, hdet, hrel⟩ := hnodal
  obtain ⟨σ, hσ⟩ := exists_residueField_algHom_section hsep
  have hσres (z : ResidueField R) : residue R (σ z) = z := AlgHom.congr_fun hσ z
  let a : ResidueField R := residue R a₀
  let b : ResidueField R := residue R b₀
  let c : ResidueField R := residue R c₀
  have hdetK : 4 * a * c - b ^ 2 ≠ 0 := by
    simpa [a, b, c, map_sub, map_mul, map_pow, map_ofNat] using hdet
  have ha : a₀ - σ a ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simp [a, map_sub, hσres]
  have hb : b₀ - σ b ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simp [b, map_sub, hσres]
  have hc : c₀ - σ c ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simp [c, map_sub, hσres]
  have hrelσ : σ a * x.1 ^ 2 + σ b * x.1 * y.1 + σ c * y.1 ^ 2 ∈
      (maximalIdeal R) ^ 3 :=
    nodalQuadratic_coeff_change_mod_cube (maximalIdeal R) x.1 y.1
      a₀ b₀ c₀ (σ a) (σ b) (σ c) x.2 y.2 ha hb hc hrel
  have hdetR : residue R (4 * σ a * σ c - (σ b) ^ 2) ≠ 0 := fun hz =>
    hdetK (by simpa [map_sub, map_mul, map_pow, map_ofNat, hσres] using hz)
  have hgrad := nodal_gradient_generates_maximalIdeal x y e
    (σ a) (σ b) (σ c) hx hy hdetR
  have hσring : (residue R).comp σ.toRingHom = RingHom.id (ResidueField R) := RingHom.ext hσres
  obtain ⟨F, hF, hQ, hclose₀, hclose₁, hC⟩ :=
    exists_surjective_nodal_series_map_of_complete_relation R σ.toRingHom hσring
      a b c hdetK x.1 y.1 x.2 y.2 hrelσ hgrad
  have hFx₀ : F (MvPowerSeries.X 0) ∈ maximalIdeal R := by
    simpa using Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero hclose₀) x.2
  have hFx₁ : F (MvPowerSeries.X 1) ∈ maximalIdeal R := by
    simpa using Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero hclose₁) y.2
  let xF : maximalIdeal R := ⟨F (MvPowerSeries.X 0), hFx₀⟩
  let yF : maximalIdeal R := ⟨F (MvPowerSeries.X 1), hFx₁⟩
  have heF₀ : e ⟨0⟩ = (maximalIdeal R).toCotangent xF := by
    rw [hx, Ideal.toCotangent_eq]
    simpa [xF, neg_sub] using ((maximalIdeal R ^ 2).neg_mem hclose₀)
  have heF₁ : e ⟨1⟩ = (maximalIdeal R).toCotangent yF := by
    rw [hy, Ideal.toCotangent_eq]
    simpa [yF, neg_sub] using ((maximalIdeal R ^ 2).neg_mem hclose₁)
  have hkerSq := kernel_le_square_of_cotangent_basis F hF xF yF e rfl rfl heF₀ heF₁
  have hker := kernel_eq_nodalQuadratic_span_of_second_order_kernel
    F hF hdepth hkerSq a b c hdetK hQ
  exact ⟨a, b, c, hdetK, σ, F, hF, hker, hC⟩

private theorem exists_nodal_algEquiv_of_complete_depth_one
    (k : Type u) (R : Type v) [Field k] [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [Algebra k R]
    [IsAdicComplete (maximalIdeal R) R]
    (hsep : Algebra.IsSeparableExtension k (ResidueField R))
    (hdepth : Module.depth R (maximalIdeal R) R = 1)
    (hnodal : HasNodalQuadraticRelation R) :
    ∃ a b c : ResidueField R,
      4 * a * c - b ^ 2 ≠ 0 ∧
        Nonempty (R ≃ₐ[k]
          (MvPowerSeries (Fin 2) (ResidueField R) ⧸
            Ideal.span {nodalBinaryQuadratic a b c})) := by
  obtain ⟨a, b, c, hdet, σ, F, hF, hker, hC⟩ :=
    exists_nodal_series_map_of_complete_depth_one k R hsep hdepth hnodal
  let K := ResidueField R
  let P := MvPowerSeries (Fin 2) K
  let I : Ideal P := Ideal.span {nodalBinaryQuadratic a b c}
  let e : (P ⧸ I) ≃+* R :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hF)
  have he (p : P) : e (Ideal.Quotient.mk I p) = F p := by
    change (RingHom.quotientKerEquivOfSurjective hF)
      ((Ideal.quotEquivOfEq hker.symm) (Ideal.Quotient.mk I p)) = F p
    rw [Ideal.quotEquivOfEq_mk]
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hF p
  have hbase (t : k) : algebraMap k (P ⧸ I) t =
      Ideal.Quotient.mk I (algebraMap k P t) := by
    simpa only [Ideal.Quotient.mkₐ_eq_mk] using
      ((Ideal.Quotient.mkₐ k I).commutes t).symm
  have hFcomm (t : k) : F (algebraMap k P t) = algebraMap k R t := by
    rw [MvPowerSeries.algebraMap_apply, hC]
    exact σ.commutes t
  have hcomm (t : k) : e (algebraMap k (P ⧸ I) t) = algebraMap k R t := by
    rw [hbase, he, hFcomm]
  exact ⟨a, b, c, hdet, ⟨(AlgEquiv.ofRingEquiv hcomm).symm⟩⟩

private theorem hasNodalQuadraticRelation_adicCompletion
    (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hnodal : HasNodalQuadraticRelation A) :
    HasNodalQuadraticRelation (AdicCompletion (maximalIdeal A) A) := by
  let B := AdicCompletion (maximalIdeal A) A
  let η : A →+* B := algebraMap A B
  obtain ⟨q, x, y, e, a, b, c, hx, hy, hq, hdet, hrel⟩ := hnodal
  have hspanA : Ideal.span ({(x : A), (y : A)} : Set A) = maximalIdeal A :=
    span_pair_eq_maximal_of_nodal_gradient_span x y a b c hdet
      (nodal_gradient_generates_maximalIdeal x y e a b c hx hy hdet)
  have hxB : η x.1 ∈ maximalIdeal B := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem η x.2
  have hyB : η y.1 ∈ maximalIdeal B := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem η y.2
  let xB : maximalIdeal B := ⟨η x.1, hxB⟩
  let yB : maximalIdeal B := ⟨η y.1, hyB⟩
  have hspanB : Ideal.span ({(xB : B), (yB : B)} : Set B) = maximalIdeal B := by
    calc
      Ideal.span ({(xB : B), (yB : B)} : Set B) =
          Ideal.map η (Ideal.span ({(x : A), (y : A)} : Set A)) := by
            rw [Ideal.map_span]
            congr 1
            ext z
            simp [xB, yB, η]
      _ = Ideal.map η (maximalIdeal A) := by rw [hspanA]
      _ = maximalIdeal B := AdicCompletion.maximalIdeal_eq_map.symm
  have hfinB : Module.finrank (ResidueField B) (CotangentSpace B) = 2 := by
    have hfinA : Module.finrank (ResidueField A) (CotangentSpace A) = 2 := by
      rw [Module.finrank_eq_card_basis e]
      simp [BinaryIndex]
    have hspanfin := AdicCompletion.spanFinrank_maximalIdeal_eq (R := A)
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at hspanfin
    exact hspanfin.trans hfinA
  obtain ⟨eB, heB₀, heB₁⟩ :=
    exists_cotangent_basis_of_pair_generators_and_finrank_two B xB yB hspanB hfinB
  have hdetB : residue B (4 * η a * η c - (η b) ^ 2) ≠ 0 := by
    intro hz
    have hmap := ResidueField.map_residue η (4 * a * c - b ^ 2)
    have hzero : (ResidueField.map η) (residue A (4 * a * c - b ^ 2)) = 0 := by
      simpa [map_sub, map_mul, map_pow, map_ofNat] using hmap.symm.trans hz
    exact hdet (RingHom.injective (ResidueField.map η) hzero)
  have hrelB : η a * xB.1 ^ 2 + η b * xB.1 * yB.1 + η c * yB.1 ^ 2 ∈
      (maximalIdeal B) ^ 3 := by
    have h := Ideal.mem_map_of_mem η hrel
    rw [Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map] at h
    simpa [xB, yB, η] using h
  exact (hasNodalQuadraticRelation_iff_exists_basis B).2
    ⟨xB, yB, eB, η a, η b, η c, heB₀, heB₁, hdetB, hrelB⟩

private theorem exists_approx_adicCompletion
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (n : ℕ) (z : AdicCompletion (maximalIdeal A) A) :
    ∃ x : A, z - algebraMap A (AdicCompletion (maximalIdeal A) A) x ∈
      (maximalIdeal (AdicCompletion (maximalIdeal A) A)) ^ n := by
  let m := maximalIdeal A
  let B := AdicCompletion m A
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (m ^ n • ⊤ : Submodule A A)
    (AdicCompletion.eval m A n z)
  refine ⟨x, ?_⟩
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
  rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval m.fg_of_isNoetherianRing]
  change AdicCompletion.eval m A n (z - AdicCompletion.of m A x) = 0
  rw [map_sub, AdicCompletion.eval_of]
  exact sub_eq_zero.mpr hx.symm

private theorem mem_pow_of_mem_adicCompletion
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (n : ℕ) (x : A)
    (h : algebraMap A (AdicCompletion (maximalIdeal A) A) x ∈
      (maximalIdeal (AdicCompletion (maximalIdeal A) A)) ^ n) :
    x ∈ (maximalIdeal A) ^ n := by
  let m := maximalIdeal A
  let B := AdicCompletion m A
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow] at h
  rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval m.fg_of_isNoetherianRing] at h
  change AdicCompletion.eval m A n (AdicCompletion.of m A x) = 0 at h
  rw [AdicCompletion.eval_of] at h
  have hx : x ∈ (m ^ n • ⊤ : Submodule A A) := by
    simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using h
  simpa only [Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id,
    Submodule.restrictScalars_mem] using hx

private theorem finrank_cotangentSpace_eq_of_surjective_square_kernel
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hsurj : Function.Surjective (algebraMap R S))
    (hker : RingHom.ker (algebraMap R S) ≤ (maximalIdeal R) ^ 2) :
    Module.finrank (ResidueField R) (CotangentSpace R) =
      Module.finrank (ResidueField S) (CotangentSpace S) := by
  let f := algebraMap R S
  let mR := maximalIdeal R
  let mS := maximalIdeal S
  have heq : mS.comap f = RingHom.ker f ⊔ mR := by
    rw [IsLocalRing.maximalIdeal_comap f]
    exact (sup_eq_right.mpr (hker.trans (Ideal.pow_le_self two_ne_zero))).symm
  let F := Ideal.mapCotangent mR mS (Algebra.ofId R S)
    (le_of_le_of_eq le_sup_right heq.symm)
  have hFsurj : Function.Surjective F :=
    Ideal.mapCotangent_surjective_of_comap_eq hsurj heq
  have hFinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, Ideal.mapCotangent_ker_of_surjective hsurj heq, eq_bot_iff,
      Submodule.map_le_iff_le_comap]
    exact fun x hx => (Ideal.toCotangent_eq_zero mR x).mpr (hker (Ideal.mem_inf.mp hx).1)
  have hres : Function.Bijective (ResidueField.map f) := by
    refine ⟨RingHom.injective _, fun z => ?_⟩
    obtain ⟨s, rfl⟩ := residue_surjective z
    obtain ⟨r, rfl⟩ := hsurj s
    exact ⟨residue R r, ResidueField.map_residue f r⟩
  have hcompat : ∀ (r : ResidueField R) (x : CotangentSpace R),
      F (r • x) = (ResidueField.map f r) • F x := by
    intro r x
    obtain ⟨s, rfl⟩ := residue_surjective r
    change F (s • x) = (f s) • F x
    exact (map_smul F s x).trans (IsScalarTower.algebraMap_smul (A := S) s (F x)).symm
  let E : CotangentSpace R ≃+ CotangentSpace S :=
    (LinearEquiv.ofBijective F ⟨hFinj, hFsurj⟩).toAddEquiv
  simpa [Module.finrank, CotangentSpace, mR, mS] using
    congrArg Cardinal.toNat (lift_rank_eq_of_equiv_equiv (ResidueField.map f) E hres hcompat)

private theorem hasNodalQuadraticRelation_iff_exists_generating_pair
    (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    HasNodalQuadraticRelation A ↔
      ∃ x y a b c : A,
        x ∈ maximalIdeal A ∧ y ∈ maximalIdeal A ∧
        Ideal.span ({x, y} : Set A) = maximalIdeal A ∧
        Module.finrank (ResidueField A) (CotangentSpace A) = 2 ∧
        residue A (4 * a * c - b ^ 2) ≠ 0 ∧
        a * x ^ 2 + b * x * y + c * y ^ 2 ∈ (maximalIdeal A) ^ 3 := by
  constructor
  · intro h
    obtain ⟨x, y, e, a, b, c, hx, hy, hdet, hrel⟩ :=
      (hasNodalQuadraticRelation_iff_exists_basis A).mp h
    have hspan := span_pair_eq_maximal_of_nodal_gradient_span x y a b c hdet
      (nodal_gradient_generates_maximalIdeal x y e a b c hx hy hdet)
    have hfin : Module.finrank (ResidueField A) (CotangentSpace A) = 2 := by
      rw [Module.finrank_eq_card_basis e]
      simp [BinaryIndex]
    exact ⟨x.1, y.1, a, b, c, x.2, y.2, hspan, hfin, hdet, hrel⟩
  · rintro ⟨x, y, a, b, c, hx, hy, hspan, hfin, hdet, hrel⟩
    let x' : maximalIdeal A := ⟨x, hx⟩
    let y' : maximalIdeal A := ⟨y, hy⟩
    obtain ⟨e, he₀, he₁⟩ :=
      exists_cotangent_basis_of_pair_generators_and_finrank_two A x' y' hspan hfin
    exact (hasNodalQuadraticRelation_iff_exists_basis A).mpr
      ⟨x', y', e, a, b, c, he₀, he₁, hdet, hrel⟩

private theorem hasNodalQuadraticRelation_of_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (e : A ≃+* B) (h : HasNodalQuadraticRelation A) :
    HasNodalQuadraticRelation B := by
  let : IsLocalHom e.toRingHom :=
    IsLocalHom.of_surjective e.toRingHom e.surjective
  obtain ⟨x, y, a, b, c, hx, hy, hspan, hfin, hdet, hrel⟩ :=
    (hasNodalQuadraticRelation_iff_exists_generating_pair A).mp h
  have hmx : e x ∈ maximalIdeal B := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact Ideal.mem_map_of_mem e hx
  have hmy : e y ∈ maximalIdeal B := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
    exact Ideal.mem_map_of_mem e hy
  have hspan' : Ideal.span ({e x, e y} : Set B) = maximalIdeal B := by
    calc
      Ideal.span ({e x, e y} : Set B) =
          (Ideal.span ({x, y} : Set A)).map e := by
        rw [Ideal.map_span]
        congr 1
        ext z
        simp
      _ = (maximalIdeal A).map e := by rw [hspan]
      _ = maximalIdeal B := IsLocalRing.map_ringEquiv_maximalIdeal e
  have hfin' : Module.finrank (ResidueField B) (CotangentSpace B) = 2 := by
    have heq := Ideal.spanFinrank_map_eq_of_ringEquiv e (maximalIdeal A)
    rw [IsLocalRing.map_ringEquiv_maximalIdeal e,
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at heq
    exact heq.trans hfin
  have hdet' : residue B (4 * e a * e c - (e b) ^ 2) ≠ 0 := by
    intro hz
    have hzero : (ResidueField.map e.toRingHom)
        (residue A (4 * a * c - b ^ 2)) = 0 := by
      rw [ResidueField.map_residue]
      simpa [map_sub, map_mul, map_pow, map_ofNat] using hz
    exact hdet (RingHom.injective (ResidueField.map e.toRingHom)
      (by simpa using hzero))
  have hrel' : e a * (e x) ^ 2 + e b * e x * e y + e c * (e y) ^ 2 ∈
      (maximalIdeal B) ^ 3 := by
    have hmap := Ideal.mem_map_of_mem e hrel
    rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal e] at hmap
    simpa [map_add, map_mul, map_pow] using hmap
  exact (hasNodalQuadraticRelation_iff_exists_generating_pair B).mpr
    ⟨e x, e y, e a, e b, e c, hmx, hmy, hspan', hfin', hdet', hrel'⟩

private theorem quadratic_eval_mem_square
    {R : Type*} [CommRing R] (m : Ideal R) (a b c x y : R)
    (hx : x ∈ m) (hy : y ∈ m) :
    a * x ^ 2 + b * x * y + c * y ^ 2 ∈ m ^ 2 := by
  rw [pow_two]
  have hxx : x * x ∈ m * m := Ideal.mul_mem_mul hx hx
  have hxy : x * y ∈ m * m := Ideal.mul_mem_mul hx hy
  have hyy : y * y ∈ m * m := Ideal.mul_mem_mul hy hy
  have hsum := Ideal.add_mem (m * m)
    (Ideal.add_mem (m * m)
      (Ideal.mul_mem_left (m * m) a hxx)
      (Ideal.mul_mem_left (m * m) b hxy))
    (Ideal.mul_mem_left (m * m) c hyy)
  convert hsum using 1; ring

private theorem span_pair_eq_maximal_of_close_mod_square
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (x y x' y' : maximalIdeal A)
    (hspan : Ideal.span ({(x : A), (y : A)} : Set A) = maximalIdeal A)
    (hx : (x' : A) - x ∈ (maximalIdeal A) ^ 2)
    (hy : (y' : A) - y ∈ (maximalIdeal A) ^ 2) :
    Ideal.span ({(x' : A), (y' : A)} : Set A) = maximalIdeal A := by
  let m := maximalIdeal A
  have hcx : m.toCotangent x' = m.toCotangent x := m.toCotangent_eq.mpr hx
  have hcy : m.toCotangent y' = m.toCotangent y := m.toCotangent_eq.mpr hy
  have hset : m.toCotangent '' ({x', y'} : Set m) =
      m.toCotangent '' ({x, y} : Set m) := by
    rw [Set.image_pair, Set.image_pair, hcx, hcy]
  have hspancot : Submodule.span (ResidueField A)
      (m.toCotangent '' ({x, y} : Set m)) = ⊤ :=
    (CotangentSpace.span_image_eq_top_iff (s := ({x, y} : Set m))).2
      (span_pair_subtype_eq_top_of_ideal_span_eq_maximal x y hspan)
  exact span_pair_eq_maximal_of_cotangent_span x' y' (hset ▸ hspancot)

private theorem quadratic_eval_sub_mem_cube_of_coord_sub_mem_square
    {R : Type*} [CommRing R] (m : Ideal R)
    (a b c x y x' y' : R)
    (hx : x ∈ m) (hy : y ∈ m) (hx' : x' ∈ m) (hy' : y' ∈ m)
    (hxx' : x - x' ∈ m ^ 2) (hyy' : y - y' ∈ m ^ 2) :
    (a * x ^ 2 + b * x * y + c * y ^ 2) -
      (a * x' ^ 2 + b * x' * y' + c * y' ^ 2) ∈ m ^ 3 := by
  have hprod (u v : R) (hu : u ∈ m ^ 2) (hv : v ∈ m) : u * v ∈ m ^ 3 := by
    rw [show (3 : ℕ) = 2 + 1 by omega, pow_add, pow_one]
    exact Ideal.mul_mem_mul hu hv
  have h₁ : a * (x - x') * (x + x') ∈ m ^ 3 := by
    convert Ideal.mul_mem_left _ a (hprod _ _ hxx' (Ideal.add_mem _ hx hx')) using 1; ring
  have h₂ : b * (x - x') * y ∈ m ^ 3 := by
    convert Ideal.mul_mem_left _ b (hprod _ _ hxx' hy) using 1; ring
  have h₃ : b * x' * (y - y') ∈ m ^ 3 := by
    convert Ideal.mul_mem_left _ b (hprod _ _ hyy' hx') using 1; ring
  have h₄ : c * (y - y') * (y + y') ∈ m ^ 3 := by
    convert Ideal.mul_mem_left _ c (hprod _ _ hyy' (Ideal.add_mem _ hy hy')) using 1; ring
  have heq : (a * x ^ 2 + b * x * y + c * y ^ 2) -
      (a * x' ^ 2 + b * x' * y' + c * y' ^ 2) =
      a * (x - x') * (x + x') + b * (x - x') * y +
        b * x' * (y - y') + c * (y - y') * (y + y') := by ring
  rw [heq]
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ h₁ h₂) h₃) h₄

private theorem hasNodalQuadraticRelation_of_adicCompletion
    (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hB : HasNodalQuadraticRelation (AdicCompletion (maximalIdeal A) A)) :
    HasNodalQuadraticRelation A := by
  let B := AdicCompletion (maximalIdeal A) A
  let η : A →+* B := algebraMap A B
  let mA := maximalIdeal A
  let mB := maximalIdeal B
  let : IsNoetherianRing B := AdicCompletion.isNoetherianRing mA
  obtain ⟨xb, yb, ab, bb, cb, hxb, hyb, hspanB, hfinB, hdetB, hrelB⟩ :=
    (hasNodalQuadraticRelation_iff_exists_generating_pair B).mp hB
  obtain ⟨xa, hxa⟩ := exists_approx_adicCompletion A 2 xb
  obtain ⟨ya, hya⟩ := exists_approx_adicCompletion A 2 yb
  obtain ⟨aa, haa⟩ := exists_approx_adicCompletion A 1 ab
  obtain ⟨ba, hba⟩ := exists_approx_adicCompletion A 1 bb
  obtain ⟨ca, hca⟩ := exists_approx_adicCompletion A 1 cb
  have hηx : η xa ∈ mB := by
    rw [show η xa = xb - (xb - η xa) by ring]
    exact Ideal.sub_mem _ hxb (Ideal.pow_le_self two_ne_zero hxa)
  have hηy : η ya ∈ mB := by
    rw [show η ya = yb - (yb - η ya) by ring]
    exact Ideal.sub_mem _ hyb (Ideal.pow_le_self two_ne_zero hya)
  have hxA : xa ∈ mA := by
    simpa only [pow_one, mA] using mem_pow_of_mem_adicCompletion A 1 xa
      (by simpa only [pow_one, η, mB] using hηx)
  have hyA : ya ∈ mA := by
    simpa only [pow_one, mA] using mem_pow_of_mem_adicCompletion A 1 ya
      (by simpa only [pow_one, η, mB] using hηy)
  have hspanB' : Ideal.span ({η xa, η ya} : Set B) = mB := by
    apply span_pair_eq_maximal_of_close_mod_square B
      (⟨xb, hxb⟩ : maximalIdeal B) (⟨yb, hyb⟩ : maximalIdeal B)
      (⟨η xa, hηx⟩ : maximalIdeal B) (⟨η ya, hηy⟩ : maximalIdeal B)
      hspanB
    · simpa [neg_sub] using neg_mem hxa
    · simpa [neg_sub] using neg_mem hya
  let : Module.FaithfullyFlat A B :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson mA
      (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  have hspanA : Ideal.span ({xa, ya} : Set A) = mA := by
    apply Ideal.map_injective_of_faithfullyFlat (B := B)
    calc
      Ideal.map η (Ideal.span ({xa, ya} : Set A)) =
          Ideal.span ({η xa, η ya} : Set B) := by
        rw [Ideal.map_span]
        congr 1
        ext z
        simp
      _ = mB := hspanB'
      _ = Ideal.map η mA := by
        simpa only [η, mA, mB] using (AdicCompletion.maximalIdeal_eq_map (R := A))
  have hfinA : Module.finrank (ResidueField A) (CotangentSpace A) = 2 := by
    have heq := AdicCompletion.spanFinrank_maximalIdeal_eq (R := A)
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at heq
    exact heq.symm.trans hfinB
  have hresCoeff (z : B) (w : A) (h : z - η w ∈ mB) :
      residue B z = residue B (η w) := by
    have hzero : residue B (z - η w) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h
    simpa [map_sub, sub_eq_zero] using hzero
  have haa' : ab - η aa ∈ mB := by simpa [η, mB] using haa
  have hba' : bb - η ba ∈ mB := by simpa [η, mB] using hba
  have hca' : cb - η ca ∈ mB := by simpa [η, mB] using hca
  have hdetB' : residue B (η (4 * aa * ca - ba ^ 2)) ≠ 0 := by
    have ha := hresCoeff ab aa haa'
    have hb := hresCoeff bb ba hba'
    have hc := hresCoeff cb ca hca'
    simpa [map_sub, map_mul, map_pow, map_ofNat, ha, hb, hc] using hdetB
  have hdetA : residue A (4 * aa * ca - ba ^ 2) ≠ 0 := fun hz => hdetB' (by
    rw [← ResidueField.map_residue η (4 * aa * ca - ba ^ 2), hz, map_zero])
  have hrelCoeff : η aa * xb ^ 2 + η ba * xb * yb + η ca * yb ^ 2 ∈ mB ^ 3 :=
    nodalQuadratic_coeff_change_mod_cube mB xb yb ab bb cb
      (η aa) (η ba) (η ca) hxb hyb haa' hba' hca' hrelB
  have hdiff : (η aa * xb ^ 2 + η ba * xb * yb + η ca * yb ^ 2) -
      (η aa * (η xa) ^ 2 + η ba * η xa * η ya + η ca * (η ya) ^ 2) ∈ mB ^ 3 :=
    quadratic_eval_sub_mem_cube_of_coord_sub_mem_square mB
      (η aa) (η ba) (η ca) xb yb (η xa) (η ya)
      hxb hyb hηx hηy hxa hya
  have hrelMapped : η aa * (η xa) ^ 2 + η ba * η xa * η ya +
      η ca * (η ya) ^ 2 ∈ mB ^ 3 := by
    have heq : η aa * (η xa) ^ 2 + η ba * η xa * η ya + η ca * (η ya) ^ 2 =
        (η aa * xb ^ 2 + η ba * xb * yb + η ca * yb ^ 2) -
          ((η aa * xb ^ 2 + η ba * xb * yb + η ca * yb ^ 2) -
            (η aa * (η xa) ^ 2 + η ba * η xa * η ya + η ca * (η ya) ^ 2)) := by ring
    exact heq ▸ Ideal.sub_mem _ hrelCoeff hdiff
  have hrelA : aa * xa ^ 2 + ba * xa * ya + ca * ya ^ 2 ∈ mA ^ 3 := by
    apply mem_pow_of_mem_adicCompletion A 3
    simpa [map_add, map_mul, map_pow] using hrelMapped
  exact (hasNodalQuadraticRelation_iff_exists_generating_pair A).mpr
    ⟨xa, ya, aa, ba, ca, hxA, hyA, hspanA, hfinA, hdetA, hrelA⟩

private theorem isSeparableExtension_of_algEquiv
    {k K K' : Type*} [Field k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] (e : K ≃ₐ[k] K')
    (hsep : Algebra.IsSeparableExtension k K) :
    Algebra.IsSeparableExtension k K' := by
  let p := ringExpChar k
  have hpow := ((Algebra.isSeparableExtension_tfae k K p).out 1 2).mp hsep
  apply ((Algebra.isSeparableExtension_tfae k K' p).out 2 1).mp
  intro s hs
  have hs' : LinearIndependent k (fun x : s => e.symm x.1) :=
    hs.map_of_surjective_injectiveₛ (RingEquiv.refl k) e.symm.toAddMonoidHom
      (RingEquiv.refl k).surjective e.symm.injective (by simp)
  have hp' : LinearIndependent k (fun x : s => (e.symm x.1) ^ p) :=
    (linearIndepOn_range_iff hs'.injective (· ^ p)).mp
      (hpow _ hs'.linearIndepOn_id)
  have hh := hp'.map_of_surjective_injectiveₛ (RingEquiv.refl k)
    e.toAddMonoidHom (RingEquiv.refl k).surjective e.injective (by simp)
  change LinearIndependent k (fun x : s => e (e.symm x.1 ^ p)) at hh
  change LinearIndependent k (fun x : s => (x.1 : K') ^ p)
  simpa only [map_pow, e.apply_symm_apply] using hh

private noncomputable def residueFieldAlgEquiv_adicCompletion
    (k : Type u) (A : Type v) [Field k] [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] :
    ResidueField A ≃ₐ[k]
      ResidueField (AdicCompletion (maximalIdeal A) A) := by
  let B := AdicCompletion (maximalIdeal A) A
  let η : A →+* B := algebraMap A B
  let e : ResidueField A ≃+* ResidueField B :=
    RingEquiv.ofBijective (ResidueField.map η)
      (AdicCompletion.residueField_map_bijective A)
  apply AlgEquiv.ofRingEquiv (f := e)
  intro z
  change e (residue A (algebraMap k A z)) =
    residue B (algebraMap k B z)
  rw [show e (residue A (algebraMap k A z)) =
      residue B (η (algebraMap k A z)) from
    ResidueField.map_residue η _, IsScalarTower.algebraMap_apply k A B]

private noncomputable def mvPowerSeriesMapAlgEquiv
    {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (e : K ≃ₐ[k] L) :
    MvPowerSeries (Fin 2) K ≃ₐ[k] MvPowerSeries (Fin 2) L := by
  refine AlgEquiv.ofBijective (MvPowerSeries.mapAlgHom (σ := Fin 2) e.toAlgHom) ⟨?_, ?_⟩
  · intro f g h
    ext n
    apply e.injective
    simpa [MvPowerSeries.mapAlgHom_apply] using
      congrArg (MvPowerSeries.coeff n) h
  · intro g
    refine ⟨MvPowerSeries.map (σ := Fin 2) e.symm.toRingHom g, ?_⟩
    ext n
    simp [MvPowerSeries.mapAlgHom_apply]

private noncomputable def nodalQuotientAlgEquiv
    {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (e : K ≃ₐ[k] L) (a b c : K) :
    (MvPowerSeries (Fin 2) K ⧸ Ideal.span {nodalBinaryQuadratic a b c}) ≃ₐ[k]
      (MvPowerSeries (Fin 2) L ⧸
        Ideal.span {nodalBinaryQuadratic (e a) (e b) (e c)}) := by
  let E := mvPowerSeriesMapAlgEquiv e
  have hQ : E (nodalBinaryQuadratic a b c) =
      nodalBinaryQuadratic (e a) (e b) (e c) := by
    change MvPowerSeries.map (σ := Fin 2) e.toRingHom
      (nodalBinaryQuadratic a b c) = _
    simp [nodalBinaryQuadratic, mul_assoc]
  have hI : Ideal.span {nodalBinaryQuadratic (e a) (e b) (e c)} =
      (Ideal.span {nodalBinaryQuadratic a b c}).map E.toRingEquiv.toRingHom := by
    rw [Ideal.map_span]
    simp [hQ]
  exact Ideal.quotientEquivAlg _ _ E hI

private theorem isUnit_of_dvd_binary_series_variables
    {K : Type*} [Field K] (f : MvPowerSeries (Fin 2) K)
    (h₀ : f ∣ MvPowerSeries.X 0) (h₁ : f ∣ MvPowerSeries.X 1) :
    IsUnit f := by
  by_contra hunit
  let P := MvPowerSeries (Fin 2) K
  let m := maximalIdeal P
  have hf : f ∈ m := (mem_maximalIdeal f).mpr (mem_nonunits_iff.mpr hunit)
  have hm : m = Ideal.span ({MvPowerSeries.X 0, MvPowerSeries.X 1} : Set P) :=
    (span_pair_X_eq_maximalIdeal_mvPowerSeries_fin_two K).symm
  have hprincipal : m = Ideal.span {f} := by
    refine le_antisymm ?_ (Ideal.span_le.mpr (by simpa using hf))
    rw [hm, Ideal.span_le, Set.pair_subset_iff]
    exact ⟨Ideal.mem_span_singleton.mpr h₀, Ideal.mem_span_singleton.mpr h₁⟩
  have hfin : Module.finrank (ResidueField P) (CotangentSpace P) ≤ 1 := by
    apply (IsLocalRing.finrank_cotangentSpace_le_one_iff).mpr
    change m.IsPrincipal
    exact hprincipal ▸ inferInstance
  rw [Stacks.MvPowerSeries.RegularParameters.finrank_cotangentSpace_field] at hfin
  omega

private theorem dvd_pair_of_dvd_nodal_gradient
    {R : Type*} [CommRing R] (a b c x y f : R)
    (hdet : IsUnit (4 * a * c - b ^ 2))
    (hg₀ : f ∣ 2 * a * x + b * y)
    (hg₁ : f ∣ b * x + 2 * c * y) :
    f ∣ x ∧ f ∣ y := by
  have h₀ := Ideal.mem_span_singleton.mpr hg₀
  have h₁ := Ideal.mem_span_singleton.mpr hg₁
  obtain ⟨hx, hy⟩ := mem_of_nodal_gradient_mem (Ideal.span {f}) a b c x y hdet h₀ h₁
  exact ⟨Ideal.mem_span_singleton.mp hx, Ideal.mem_span_singleton.mp hy⟩

private theorem pderiv_zero_nodalBinaryQuadratic
    {K : Type*} [Field K] (a b c : K) :
    MvPowerSeries.pderiv (R := K) (0 : Fin 2) (nodalBinaryQuadratic a b c) =
      MvPowerSeries.C (2 * a) * MvPowerSeries.X 0 +
        MvPowerSeries.C b * MvPowerSeries.X 1 := by
  simp [nodalBinaryQuadratic, Derivation.leibniz,
    MvPowerSeries.pderiv_X_of_ne, mul_assoc]
  simp only [map_ofNat]
  ring

private theorem pderiv_one_nodalBinaryQuadratic
    {K : Type*} [Field K] (a b c : K) :
    MvPowerSeries.pderiv (R := K) (1 : Fin 2) (nodalBinaryQuadratic a b c) =
      MvPowerSeries.C b * MvPowerSeries.X 0 +
        MvPowerSeries.C (2 * c) * MvPowerSeries.X 1 := by
  simp [nodalBinaryQuadratic, Derivation.leibniz,
    MvPowerSeries.pderiv_X_of_ne, mul_assoc]
  simp only [map_ofNat]
  ring

private theorem dvd_pderiv_of_square_dvd
    {K : Type*} [Field K] (f q : MvPowerSeries (Fin 2) K) (i : Fin 2)
    (h : f * f ∣ q) : f ∣ MvPowerSeries.pderiv (R := K) i q := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨f * MvPowerSeries.pderiv (R := K) i g +
    2 * MvPowerSeries.pderiv (R := K) i f * g, ?_⟩
  simp only [Derivation.leibniz]
  ring

private theorem squarefree_nodalBinaryQuadratic
    {K : Type*} [Field K] (a b c : K)
    (hdet : 4 * a * c - b ^ 2 ≠ 0) :
    Squarefree (nodalBinaryQuadratic a b c) := by
  intro f hsq
  let P := MvPowerSeries (Fin 2) K
  have hg₀ : f ∣ 2 * MvPowerSeries.C a * MvPowerSeries.X 0 +
      MvPowerSeries.C b * MvPowerSeries.X 1 := by
    have h := dvd_pderiv_of_square_dvd f (nodalBinaryQuadratic a b c) 0 hsq
    rw [pderiv_zero_nodalBinaryQuadratic] at h
    simpa [map_mul, map_ofNat] using h
  have hg₁ : f ∣ MvPowerSeries.C b * MvPowerSeries.X 0 +
      2 * MvPowerSeries.C c * MvPowerSeries.X 1 := by
    have h := dvd_pderiv_of_square_dvd f (nodalBinaryQuadratic a b c) 1 hsq
    rw [pderiv_one_nodalBinaryQuadratic] at h
    simpa [map_mul, map_ofNat] using h
  have hdetP : IsUnit (4 * MvPowerSeries.C a * MvPowerSeries.C c -
      (MvPowerSeries.C b : P) ^ 2) := by
    simpa [map_sub, map_mul, map_pow, map_ofNat] using
      (isUnit_iff_ne_zero.mpr hdet).map (MvPowerSeries.C : K →+* P)
  obtain ⟨h₀, h₁⟩ := dvd_pair_of_dvd_nodal_gradient
    (MvPowerSeries.C a : P) (MvPowerSeries.C b) (MvPowerSeries.C c)
    (MvPowerSeries.X 0) (MvPowerSeries.X 1) f hdetP hg₀ hg₁
  exact isUnit_of_dvd_binary_series_variables f h₀ h₁

private theorem isReduced_nodalBinaryQuadratic_quotient
    {K : Type*} [Field K] (a b c : K)
    (hdet : 4 * a * c - b ^ 2 ≠ 0) :
    IsReduced (MvPowerSeries (Fin 2) K ⧸
      Ideal.span {nodalBinaryQuadratic a b c}) := by
  let P := MvPowerSeries (Fin 2) K
  let : IsRegularLocalRing P := isRegularLocalRing_mvPowerSeries K 2
  let : UniqueFactorizationMonoid P :=
    IsRegularLocalRing.uniqueFactorizationMonoid P
  exact (Ideal.isRadical_iff_quotient_reduced _).mp
    (isRadical_iff_span_singleton.mp (squarefree_nodalBinaryQuadratic a b c hdet).isRadical)

private theorem hasNodalQuadraticRelation_nodalBinaryQuadratic_quotient
    {K : Type*} [Field K] (a b c : K)
    (hdet : 4 * a * c - b ^ 2 ≠ 0)
    [IsLocalRing (MvPowerSeries (Fin 2) K ⧸
      Ideal.span {nodalBinaryQuadratic a b c})] :
    HasNodalQuadraticRelation
      (MvPowerSeries (Fin 2) K ⧸ Ideal.span {nodalBinaryQuadratic a b c}) := by
  let P := MvPowerSeries (Fin 2) K
  let I : Ideal P := Ideal.span {nodalBinaryQuadratic a b c}
  let Q := P ⧸ I
  let f : P →+* Q := Ideal.Quotient.mk I
  let : IsNoetherianRing Q := inferInstance
  let : IsLocalHom f := IsLocalHom.of_surjective f Ideal.Quotient.mk_surjective
  let mP := maximalIdeal P
  let mQ := maximalIdeal Q
  have hxP : MvPowerSeries.X (0 : Fin 2) ∈ mP := by
    change MvPowerSeries.X (0 : Fin 2) ∈ maximalIdeal P
    rw [maximalIdeal_mvPowerSeries_eq_span_X K 2]
    exact Ideal.subset_span ⟨0, rfl⟩
  have hyP : MvPowerSeries.X (1 : Fin 2) ∈ mP := by
    change MvPowerSeries.X (1 : Fin 2) ∈ maximalIdeal P
    rw [maximalIdeal_mvPowerSeries_eq_span_X K 2]
    exact Ideal.subset_span ⟨1, rfl⟩
  have hq2 : nodalBinaryQuadratic a b c ∈ mP ^ 2 := by
    simpa [nodalBinaryQuadratic, mul_assoc] using
      quadratic_eval_mem_square mP (MvPowerSeries.C a) (MvPowerSeries.C b)
        (MvPowerSeries.C c) (MvPowerSeries.X 0) (MvPowerSeries.X 1) hxP hyP
  have hIle : I ≤ mP ^ 2 := Ideal.span_le.mpr (by simpa [I] using hq2)
  have hker : RingHom.ker (algebraMap P Q) ≤ mP ^ 2 := by
    simpa [I, Q, f] using hIle
  have hfin : Module.finrank (ResidueField Q) (CotangentSpace Q) = 2 := by
    have heq := finrank_cotangentSpace_eq_of_surjective_square_kernel P Q
      Ideal.Quotient.mk_surjective hker
    rw [Stacks.MvPowerSeries.RegularParameters.finrank_cotangentSpace_field] at heq
    simpa using heq.symm
  let x : Q := f (MvPowerSeries.X 0)
  let y : Q := f (MvPowerSeries.X 1)
  let α : Q := f (MvPowerSeries.C a)
  let β : Q := f (MvPowerSeries.C b)
  let γ : Q := f (MvPowerSeries.C c)
  have hx : x ∈ mQ := by
    change x ∈ maximalIdeal Q
    rw [← IsLocalRing.map_maximalIdeal_of_surjective f Ideal.Quotient.mk_surjective]
    exact Ideal.mem_map_of_mem f hxP
  have hy : y ∈ mQ := by
    change y ∈ maximalIdeal Q
    rw [← IsLocalRing.map_maximalIdeal_of_surjective f Ideal.Quotient.mk_surjective]
    exact Ideal.mem_map_of_mem f hyP
  have hmP : mP = Ideal.span ({MvPowerSeries.X 0, MvPowerSeries.X 1} : Set P) :=
    (span_pair_X_eq_maximalIdeal_mvPowerSeries_fin_two K).symm
  have hspan : Ideal.span ({x, y} : Set Q) = mQ := by
    calc
      Ideal.span ({x, y} : Set Q) = Ideal.map f mP := by
        rw [hmP, Ideal.map_span]
        congr 1
        ext z
        simp [x, y]
      _ = mQ := IsLocalRing.map_maximalIdeal_of_surjective f
        Ideal.Quotient.mk_surjective
  have hdetQ : residue Q (4 * α * γ - β ^ 2) ≠ 0 := by
    let σ : K →+* ResidueField Q :=
      (residue Q).comp (f.comp MvPowerSeries.C)
    have hσ : σ (4 * a * c - b ^ 2) ≠ 0 :=
      fun hz => hdet ((RingHom.injective σ) (by simpa using hz))
    simpa [σ, α, β, γ, map_sub, map_mul, map_pow, map_ofNat] using hσ
  have hrel : α * x ^ 2 + β * x * y + γ * y ^ 2 ∈ mQ ^ 3 := by
    have hzero : f (nodalBinaryQuadratic a b c) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    have hmap := map_nodalBinaryQuadratic f (f.comp MvPowerSeries.C)
      x y (by intro z; rfl) rfl rfl a b c
    have heq : α * x ^ 2 + β * x * y + γ * y ^ 2 = 0 := by
      simpa [α, β, γ] using hmap.symm.trans hzero
    exact heq ▸ (mQ ^ 3).zero_mem
  exact (hasNodalQuadraticRelation_iff_exists_generating_pair Q).mpr
    ⟨x, y, α, β, γ, hx, hy, hspan, hfin, hdetQ, hrel⟩


/-- The maximal-ideal completion of `A` is, as a `k`-algebra, a two-variable power-series
hypersurface defined by a nondegenerate binary quadratic form. -/
@[sga "7 XV 1.2.2" "The case n = 1", sga "7 XVII 1.2" "Two-variable case (n = 2"]
public def HasNodalCompletion (k : Type u) (A : Type v) [Field k] [CommRing A]
    [IsLocalRing A] [Algebra k A] : Prop :=
  ∃ a b c : ResidueField A,
    4 * a * c - b ^ 2 ≠ 0 ∧
      Nonempty
        (AdicCompletion (maximalIdeal A) A ≃ₐ[k]
          (MvPowerSeries (Fin 2) (ResidueField A) ⧸
            Ideal.span {nodalBinaryQuadratic a b c}))

/-- The reduced characterization of a nodal Noetherian local algebra over a field. -/
public def IsNodalAlgebra (k : Type u) (A : Type v) [Field k] [CommRing A]
    [IsLocalRing A] [Algebra k A] : Prop :=
  Algebra.IsSeparableExtension k (ResidueField A) ∧
    IsReduced A ∧ HasNodalQuadraticRelation A

private theorem hasNodalCompletion_of_depth_eq_one
    (k : Type u) (A : Type v) [Field k] [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [Algebra k A]
    (hsep : Algebra.IsSeparableExtension k (ResidueField A))
    (hdepth : Module.depth A (maximalIdeal A) A = 1)
    (hnodal : HasNodalQuadraticRelation A) :
    HasNodalCompletion k A := by
  let B := AdicCompletion (maximalIdeal A) A
  let : IsNoetherianRing B := AdicCompletion.isNoetherianRing (maximalIdeal A)
  let e := residueFieldAlgEquiv_adicCompletion k A
  have hsepB : Algebra.IsSeparableExtension k (ResidueField B) :=
    isSeparableExtension_of_algEquiv e hsep
  have hdepthB : Module.depth B (maximalIdeal B) B = 1 :=
    (depth_adicCompletion_maximalIdeal (A := A)).symm ▸ hdepth
  have hnodalB : HasNodalQuadraticRelation B :=
    hasNodalQuadraticRelation_adicCompletion A hnodal
  obtain ⟨aB, bB, cB, hdetB, ⟨F⟩⟩ :=
    exists_nodal_algEquiv_of_complete_depth_one k B hsepB hdepthB hnodalB
  let a := e.symm aB
  let b := e.symm bB
  let c := e.symm cB
  have hdet : 4 * a * c - b ^ 2 ≠ 0 := fun hz =>
    hdetB (by simpa [a, b, c, map_sub, map_mul, map_pow, map_ofNat] using congrArg e hz)
  have ha : e a = aB := e.apply_symm_apply aB
  have hb : e b = bB := e.apply_symm_apply bB
  have hc : e c = cB := e.apply_symm_apply cB
  let Q := nodalQuotientAlgEquiv e a b c
  rw [ha, hb, hc] at Q
  exact ⟨a, b, c, hdet, ⟨F.trans Q.symm⟩⟩

/-- For a Noetherian local algebra over a field, the following are equivalent: it is reduced with
a nondegenerate quadratic relation on its two-dimensional cotangent space; it has depth one with
the same relation; and its completion is a two-variable power-series hypersurface defined by a
nondegenerate quadratic form. In all three conditions the residue-field extension is
separable. -/
@[stacks 0C49]
public theorem isNodalAlgebra_tfae (k : Type u) (A : Type v) [Field k] [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] :
    List.TFAE [
      IsNodalAlgebra k A,
      Algebra.IsSeparableExtension k (ResidueField A) ∧
        Module.depth A (maximalIdeal A) A = 1 ∧ HasNodalQuadraticRelation A,
      Algebra.IsSeparableExtension k (ResidueField A) ∧ HasNodalCompletion k A] := by
  let P₁ := IsNodalAlgebra k A
  let P₂ := Algebra.IsSeparableExtension k (ResidueField A) ∧
    Module.depth A (maximalIdeal A) A = 1 ∧ HasNodalQuadraticRelation A
  let P₃ := Algebra.IsSeparableExtension k (ResidueField A) ∧ HasNodalCompletion k A
  have h12 : P₁ → P₂ := by
    rintro ⟨hsep, hred, hnodal⟩
    exact ⟨hsep, depth_eq_one_of_isReduced_and_hasNodalQuadraticRelation A hred hnodal,
      hnodal⟩
  have h23 : P₂ → P₃ := by
    rintro ⟨hsep, hdepth, hnodal⟩
    exact ⟨hsep, hasNodalCompletion_of_depth_eq_one k A hsep hdepth hnodal⟩
  have h31 : P₃ → P₁ := by
    rintro ⟨hsep, a, b, c, hdet, ⟨e⟩⟩
    let B := AdicCompletion (maximalIdeal A) A
    let Q := MvPowerSeries (Fin 2) (ResidueField A) ⧸
      Ideal.span {nodalBinaryQuadratic a b c}
    let : Nontrivial Q := e.symm.toEquiv.nontrivial
    let : IsLocalRing Q := IsLocalRing.of_surjective' e.toRingHom e.surjective
    let : IsNoetherianRing Q := inferInstance
    let : IsReduced Q := isReduced_nodalBinaryQuadratic_quotient a b c hdet
    have hBred : IsReduced B := isReduced_of_injective e.toRingHom e.injective
    have hAred : IsReduced A :=
      isReduced_of_isReduced_maximalIdeal_completion A hBred
    have hQnodal : HasNodalQuadraticRelation Q :=
      hasNodalQuadraticRelation_nodalBinaryQuadratic_quotient a b c hdet
    have hBnodal : HasNodalQuadraticRelation B :=
      hasNodalQuadraticRelation_of_ringEquiv e.symm.toRingEquiv hQnodal
    have hAnodal : HasNodalQuadraticRelation A :=
      hasNodalQuadraticRelation_of_adicCompletion A hBnodal
    exact ⟨hsep, hAred, hAnodal⟩
  change List.TFAE [P₁, P₂, P₃]
  exact List.tfae_of_cycle
    (by simpa [List.isChain_cons_cons] using
      (⟨h12, h23⟩ : (P₁ → P₂) ∧ (P₂ → P₃))) h31

end Stacks.Curves
