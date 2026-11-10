module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.DegreeSeparable
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaBranches.LowerBound
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Defs
import all StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The delta invariant of a node is one

Let `A` be a nodal local algebra over a field `k`, and let
`A' = integralClosure A (FractionRing A)` be its normalization. Then `𝔪 A'` is contained in the
image of `A`, the image of `A` is a coatom among the `A`-submodules of `A'`, and
`Ring.deltaInvariant A = 1`.

## Main results

* `Stacks.Curves.mul_generator_mem_range_algebraMap_stableIdealQuotient`: on the affine blow-up
  chart `R[I/y]`, multiplication by `y` lands in the image of `R`.
* `Stacks.Curves.map_maximalIdeal_le_range_algebraMap_integralClosure`: for a nodal local algebra,
  `𝔪 A'` is contained in the image of `A`.
* `Stacks.Curves.isCoatom_range_algebraMap_of_finrank_eq_two`: a criterion for the image of `A` in
  an `A`-algebra to be a coatom, through a surjection onto a two-dimensional algebra over the
  residue field.
* `Stacks.Curves.isCoatom_range_algebraMap_integralClosure_of_isNodalAlgebra`: the image of `A` in
  `A'` is a coatom among `A`-submodules.
* `Stacks.Curves.deltaInvariant_eq_one_of_isNodalAlgebra`: the delta invariant of a node is one.
* `Stacks.Curves.ringKrullDim_eq_one_of_isNodalAlgebra`: a node has dimension one.
* `Stacks.Curves.numberOfGeometricBranchesOfLocalRing_le_two_of_isNodalAlgebra`: a Nagata node has
  at most two geometric branches.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
-/


@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

/-! ### Multiplication by the generator on the blow-up chart -/

/-- On the blow-up chart `R[I/y] = y⁻¹ I`, multiplication by `y` lands in the image of `R`. -/
public theorem mul_generator_mem_range_algebraMap_stableIdealQuotient
    {R Q : Type*} [CommRing R] [CommRing Q] [Algebra R Q]
    (I : Ideal R) (y : I) (u : Qˣ) (hu : (u : Q) = algebraMap R Q y.1)
    (hI : I * I = Ideal.span {y.1} * I)
    (z : stableIdealQuotient I y u hu hI) :
    algebraMap R ↥(stableIdealQuotient I y u hu hI) y.1 * z ∈
      LinearMap.range (Algebra.linearMap R ↥(stableIdealQuotient I y u hu hI)) := by
  obtain ⟨w, hw, hwz⟩ := z.2
  refine ⟨w, Subtype.ext ?_⟩
  change algebraMap R Q w = algebraMap R Q y.1 * (z : Q)
  rw [← hwz]
  change algebraMap R Q w = algebraMap R Q y.1 * (↑(u⁻¹) * algebraMap R Q w)
  rw [← hu, Units.mul_inv_cancel_left]

/-! ### The conductor of a node contains its maximal ideal -/

section

attribute [local instance] residueFieldAlgebraQuotient

/-- For a nodal local algebra `A` with normalization `A'`, the ideal `𝔪 A'` is contained in the
image of `A`. -/
public theorem map_maximalIdeal_le_range_algebraMap_integralClosure
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A)
    {t : ↥(integralClosure A (FractionRing A))}
    (ht : t ∈ (maximalIdeal A).map (algebraMap A ↥(integralClosure A (FractionRing A)))) :
    t ∈ LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) := by
  classical
  obtain ⟨x, y, e, a, b, c, hx, hy, ha, hdisc, hrel⟩ :=
    exists_nodalQuadraticRelation_nonzero k A hA
  have hxy := maximalIdeal_eq_span_of_cotangent_basis x y e hx hy
  have hm := maximalIdeal_sq_eq_span_mul_of_quadratic_relation x y hxy a b c
    ((residue_ne_zero_iff_isUnit a).mp ha) hrel
  have hy0 : y.1 ≠ 0 := by
    intro hz
    apply e.ne_zero ⟨1⟩
    rw [hy, show y = 0 from Subtype.ext hz, map_zero]
  have : IsReduced A := hA.2.1
  have hyr := mem_nonZeroDivisors_of_maximalIdeal_sq_eq_span_mul y.1 hy0 hm
  let Q := FractionRing A
  let u : Qˣ := (IsLocalization.map_units Q (⟨y.1, hyr⟩ : nonZeroDivisors A)).unit
  have hu : (u : Q) = algebraMap A Q y.1 := IsUnit.unit_spec _
  have hm' : maximalIdeal A * maximalIdeal A = Ideal.span {y.1} * maximalIdeal A := by
    simpa only [pow_two] using hm
  have hinj : Function.Injective (algebraMap A Q) := IsFractionRing.injective A Q
  let B := stableIdealQuotient (maximalIdeal A) y u hu hm'
  let J := (maximalIdeal A).map (algebraMap A B)
  obtain ⟨eB⟩ := stableIdealQuotient_fibre_equiv_adjoinRoot x y u hu hm' hinj e hx hy a b c ha
    hrel
  have hd : 4 * residue A a * residue A c - residue A b ^ 2 ≠ 0 := by
    simpa only [map_sub, map_mul, map_pow, map_ofNat] using hdisc
  have : IsReduced (AdjoinRoot (Polynomial.C (residue A a) * Polynomial.X ^ 2 +
      Polynomial.C (residue A b) * Polynomial.X + Polynomial.C (residue A c))) :=
    isReduced_adjoinRoot_quadratic _ _ _ hd
  have hred : IsReduced (B ⧸ J) :=
    ⟨fun z hz => eB.injective (by rw [map_zero]; exact (hz.map eB.toRingHom).eq_zero)⟩
  have hspan : J = Ideal.span {algebraMap A B y.1} :=
    stableIdealQuotient_map_eq_span (maximalIdeal A) y u hu hm' hinj
  have hrad : (Ideal.span {algebraMap A B y.1}).IsRadical :=
    hspan ▸ (Ideal.isRadical_iff_quotient_reduced J).mpr hred
  have : Module.Finite A B := stableIdealQuotient_finite _ _ _ _ _
    (maximalIdeal A).fg_of_isNoetherianRing
  have : Ring.KrullDimLE 1 A := krullDimLE_one_of_maximalIdeal_sq_le_span y
    (hm.le.trans Ideal.mul_le_left)
  have hB : B = integralClosure A Q := eq_integralClosure_of_finite_of_radical_span B y hyr hrad
  let eN : B ≃ₐ[A] integralClosure A Q := Subalgebra.equivOfEq B _ hB
  have hmapeq : (maximalIdeal A).map (algebraMap A ↥(integralClosure A Q)) =
      J.map eN.toRingHom := by
    rw [show J = (maximalIdeal A).map (algebraMap A ↥B) from rfl, Ideal.map_map]
    congr 1
  obtain ⟨s, hs, hst⟩ :=
    (Ideal.mem_map_iff_of_surjective eN.toRingHom eN.surjective).mp (hmapeq ▸ ht)
  rw [hspan] at hs
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hs
  obtain ⟨w, hw⟩ :=
    mul_generator_mem_range_algebraMap_stableIdealQuotient (maximalIdeal A) y u hu hm' z
  refine ⟨w, ?_⟩
  rw [Algebra.linearMap_apply, ← hst, ← eN.commutes w]
  exact congrArg eN (by simpa only [Algebra.linearMap_apply] using hw.trans hz.symm)

end

/-! ### A coatom criterion for the image of a ring in a two-dimensional modification -/

/-- Let `A` be a local ring with residue field `κ`, let `S` be an `A`-algebra, and let `π : S → T`
be a surjection onto a two-dimensional `κ`-algebra whose kernel is contained in the image of `A`
and which sends the image of `A` onto `κ · 1`. Then the image of `A` is a coatom in the lattice of
`A`-submodules of `S`. -/
public theorem isCoatom_range_algebraMap_of_finrank_eq_two
    (A : Type*) [CommRing A] [IsLocalRing A] (S : Type*) [CommRing S] [Algebra A S]
    (T : Type*) [CommRing T] [Algebra (ResidueField A) T] [Module.Finite (ResidueField A) T]
    (π : S →+* T) (hsurj : Function.Surjective π)
    (hker : ∀ t : S, π t = 0 → t ∈ LinearMap.range (Algebra.linearMap A S))
    (hπ : ∀ w : A, π (algebraMap A S w) = algebraMap (ResidueField A) T (residue A w))
    (hrank : Module.finrank (ResidueField A) T = 2) :
    IsCoatom (LinearMap.range (Algebra.linearMap A S)) := by
  classical
  have hnontriv : Nontrivial T :=
    Module.nontrivial_of_finrank_pos (R := ResidueField A) (by rw [hrank]; omega)
  have hspan1 : Module.finrank (ResidueField A)
      ↥(Submodule.span (ResidueField A) {(1 : T)}) = 1 :=
    finrank_span_singleton one_ne_zero
  have hclass : ∀ w : A, π (algebraMap A S w) = residue A w • (1 : T) := fun w => by
    rw [Algebra.smul_def, mul_one, hπ]
  have hsub : ∀ z s : S, π z = π s → ∃ v : A, z = algebraMap A S v + s := fun z s h => by
    obtain ⟨v, hv⟩ := hker (z - s) (by rw [map_sub, h, sub_self])
    exact ⟨v, by rw [show algebraMap A S v = z - s from hv, sub_add_cancel]⟩
  have hmem : ∀ t : S, π t ∈ Submodule.span (ResidueField A) {(1 : T)} →
      t ∈ LinearMap.range (Algebra.linearMap A S) := by
    intro t htm
    obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp htm
    obtain ⟨w, rfl⟩ := residue_surjective α
    obtain ⟨v, hv⟩ := hsub t (algebraMap A S w) (by rw [hclass, hα])
    exact ⟨v + w, by rw [Algebra.linearMap_apply, map_add]; exact hv.symm⟩
  constructor
  · intro htop
    have hsurj1 : Submodule.span (ResidueField A) {(1 : T)} = ⊤ := by
      refine top_le_iff.mp fun z _ => ?_
      obtain ⟨t, rfl⟩ := hsurj z
      obtain ⟨w, hw⟩ : t ∈ LinearMap.range (Algebra.linearMap A S) := htop ▸ Submodule.mem_top
      rw [show t = algebraMap A S w from hw.symm, hclass]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    rw [hsurj1, finrank_top, hrank] at hspan1
    omega
  · intro P hP
    obtain ⟨t, htP, htN⟩ := IsConcreteLE.exists_of_lt hP
    have hnot : π t ∉ Submodule.span (ResidueField A) {(1 : T)} := fun hc => htN (hmem t hc)
    have hlt : Submodule.span (ResidueField A) {(1 : T)} <
        Submodule.span (ResidueField A) {(1 : T), π t} := by
      refine lt_of_le_of_ne (Submodule.span_mono (by simp)) fun hc => hnot ?_
      rw [hc]
      exact Submodule.subset_span (by simp)
    have hfull : Submodule.span (ResidueField A) {(1 : T), π t} = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by
        have := Submodule.finrank_lt_finrank_of_lt hlt
        have := Submodule.finrank_le (Submodule.span (ResidueField A) {(1 : T), π t})
        omega)
    refine top_le_iff.mp fun z _ => ?_
    have hz : π z ∈ Submodule.span (ResidueField A) {(1 : T), π t} := by
      rw [hfull]
      exact Submodule.mem_top
    rw [Submodule.mem_span_pair] at hz
    obtain ⟨α, β, hαβ⟩ := hz
    obtain ⟨p, rfl⟩ := residue_surjective α
    obtain ⟨q, rfl⟩ := residue_surjective β
    have hqt : π (algebraMap A S q * t) = residue A q • π t := by
      rw [map_mul, hπ, Algebra.smul_def]
    obtain ⟨v, hv⟩ := hsub z (algebraMap A S p + algebraMap A S q * t)
      (by rw [map_add, hclass, hqt, hαβ])
    rw [hv, ← Algebra.smul_def]
    exact P.add_mem (hP.le ⟨v, rfl⟩) (P.add_mem (hP.le ⟨p, rfl⟩) (P.smul_mem q htP))

/-! ### The image of the ring is a coatom in its normalization -/

/-- For a nodal local algebra `A`, the image of `A` in its normalization `A'` is a coatom in the
lattice of `A`-submodules of `A'`. -/
public theorem isCoatom_range_algebraMap_integralClosure_of_isNodalAlgebra
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A) :
    IsCoatom (LinearMap.range
      (Algebra.linearMap A ↥(integralClosure A (FractionRing A)))) := by
  have : Module.Finite (ResidueField A) (quadraticAlgebra A) :=
    finite_quadraticAlgebra_of_isNodalAlgebra k A hA
  have hr : Module.finrank (ResidueField A) (quadraticAlgebra A) = 2 :=
    finrank_quadraticAlgebra_of_isNodalAlgebra k A hA
  refine @isCoatom_range_algebraMap_of_finrank_eq_two A _ _
    ↥(integralClosure A (FractionRing A)) _ _ (quadraticAlgebra A) _
    (instAlgebraResidueFieldQuadraticAlgebra A) ‹_›
    (Ideal.Quotient.mk ((maximalIdeal A).map
      (algebraMap A ↥(integralClosure A (FractionRing A)))))
    Ideal.Quotient.mk_surjective (fun t ht => ?_) (fun w => rfl) hr
  exact map_maximalIdeal_le_range_algebraMap_integralClosure k A hA
    (Ideal.Quotient.eq_zero_iff_mem.mp ht)

/-! ### The delta invariant -/

/-- The delta invariant of a Noetherian nodal local algebra is one. -/
@[sga "7 X 2.24" "more general"]
public theorem deltaInvariant_eq_one_of_isNodalAlgebra
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A) :
    Ring.deltaInvariant A = 1 :=
  Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.2
    (isCoatom_range_algebraMap_integralClosure_of_isNodalAlgebra k A hA))

/-! ### Dimension and the number of geometric branches -/

/-- A Noetherian nodal local algebra has Krull dimension one. -/
public theorem ringKrullDim_eq_one_of_isNodalAlgebra
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A) :
    ringKrullDim A = 1 :=
  ringKrullDim_eq_one_of_isReduced_and_hasNodalQuadraticRelation A hA.2.1 hA.2.2

/-- A nodal Nagata local algebra has at most two geometric branches. -/
public theorem numberOfGeometricBranchesOfLocalRing_le_two_of_isNodalAlgebra
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    (hNagata : IsNagataRing A) (hA : IsNodalAlgebra k A) :
    numberOfGeometricBranchesOfLocalRing A ≤ 2 := by
  have : IsNoetherianRing A := hNagata.isNoetherianRing
  have : IsReduced A := hA.2.1
  have hbound := Ring.deltaInvariant_ge_numberOfGeometricBranches_sub_one A hNagata
    (ringKrullDim_eq_one_of_isNodalAlgebra k A hA)
  rw [deltaInvariant_eq_one_of_isNodalAlgebra k A hA] at hbound
  rw [show (2 : ℕ∞) = 1 + 1 from rfl]
  exact tsub_le_iff_right.mp hbound

end Stacks.Curves

end
