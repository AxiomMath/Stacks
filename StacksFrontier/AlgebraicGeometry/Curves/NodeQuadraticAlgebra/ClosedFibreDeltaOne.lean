module

public import Mathlib.RingTheory.SimpleModule.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Defs

/-!
# The closed fibre of a normalization of delta invariant one

Let `A` be a local ring with maximal ideal `𝔪` and `A' = integralClosure A (FractionRing A)`. If
`Ring.deltaInvariant A = 1`, that is, `A' ⧸ A` is a simple `A`-module, then `𝔪 A'` lies in the
image of `A`, `A' = A + A t` for every `t ∈ A' ∖ A`, and the closed fibre `A' ⧸ 𝔪 A'` is
two-dimensional over the residue field, with basis `1` and the class of `t`. The first two
statements hold for any `A`-algebra `S` with `S ⧸ A` simple.

## Main results

* `Stacks.Curves.map_maximalIdeal_restrictScalars_le_range_of_isSimpleModule`: if `S ⧸ A` is
  simple, then `𝔪 S` lies in the image of `A`.
* `Stacks.Curves.exists_notMem_range_sup_span_singleton_eq_top_of_isSimpleModule`: if `S ⧸ A` is
  simple, then `S = A + A t` for some `t` outside the image of `A`.
* `Stacks.Curves.map_maximalIdeal_ne_top_of_isSimpleModule`: if `S ⧸ A` is simple, then `𝔪 S` is a
  proper ideal.
* `Stacks.Curves.mem_maximalIdeal_of_algebraMap_mem_map_of_isSimpleModule`: if `S ⧸ A` is simple,
  then `𝔪` is the contraction of `𝔪 S`.
* `Stacks.Curves.exists_linearIndependent_quadraticAlgebra_of_deltaInvariant_eq_one`: for delta
  invariant one, `1` and the class of a generator `t` are linearly independent and span the closed
  fibre, and `a + b t ∈ 𝔪 A'` forces `a, b ∈ 𝔪`.
* `Stacks.Curves.finrank_quadraticAlgebra_eq_two_of_deltaInvariant_eq_one`: for delta invariant
  one, the closed fibre is two-dimensional over the residue field.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0C3T](https://stacks.math.columbia.edu/tag/0C3T)
-/


@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

/-! ### One-step extensions of a local ring -/

section General

variable (A : Type u) [CommRing A] [IsLocalRing A] (S : Type v) [CommRing S] [Algebra A S]

/-- If `S ⧸ A` is a simple `A`-module, then `𝔪 S` is contained in the image of `A`. -/
public theorem map_maximalIdeal_restrictScalars_le_range_of_isSimpleModule
    (h : IsSimpleModule A (S ⧸ LinearMap.range (Algebra.linearMap A S))) :
    ((maximalIdeal A).map (algebraMap A S)).restrictScalars A ≤
      LinearMap.range (Algebra.linearMap A S) := by
  have hann : Module.annihilator A (S ⧸ LinearMap.range (Algebra.linearMap A S))
      = maximalIdeal A :=
    eq_maximalIdeal (@IsSimpleModule.annihilator_isMaximal _ _ A _ _ h)
  rw [← Ideal.smul_top_eq_map, Submodule.smul_le]
  intro a ha s _
  have ha' : a ∈ Module.annihilator A (S ⧸ LinearMap.range (Algebra.linearMap A S)) := by
    rwa [hann]
  have h0 := Module.mem_annihilator.mp ha' ((LinearMap.range (Algebra.linearMap A S)).mkQ s)
  rwa [← map_smul, ← LinearMap.mem_ker, Submodule.ker_mkQ] at h0

omit [IsLocalRing A] in
/-- If `S ⧸ A` is a simple `A`-module, then `S = A + A t` for some `t` outside the image of `A`. -/
public theorem exists_notMem_range_sup_span_singleton_eq_top_of_isSimpleModule
    (h : IsSimpleModule A (S ⧸ LinearMap.range (Algebra.linearMap A S))) :
    ∃ t : S, t ∉ LinearMap.range (Algebra.linearMap A S) ∧
      LinearMap.range (Algebra.linearMap A S) ⊔ Submodule.span A {t} = ⊤ := by
  have hco : IsCoatom (LinearMap.range (Algebra.linearMap A S)) :=
    isSimpleModule_iff_isCoatom.mp h
  obtain ⟨t, -, ht⟩ := SetLike.exists_of_lt hco.lt_top
  refine ⟨t, ht, hco.2 _ (lt_of_le_of_ne le_sup_left fun hc => ht ?_)⟩
  exact hc ▸ (le_sup_right (b := Submodule.span A {t})
    (Submodule.mem_span_singleton_self t))

/-- If `S ⧸ A` is a simple `A`-module, then `𝔪 S` is a proper ideal of `S`. -/
public theorem map_maximalIdeal_ne_top_of_isSimpleModule
    (h : IsSimpleModule A (S ⧸ LinearMap.range (Algebra.linearMap A S))) :
    (maximalIdeal A).map (algebraMap A S) ≠ ⊤ := by
  intro htop
  have hle := map_maximalIdeal_restrictScalars_le_range_of_isSimpleModule A S h
  rw [htop] at hle
  exact (isSimpleModule_iff_isCoatom.mp h).1 (eq_top_iff.2 fun x _ => hle (by trivial))

/-- If `S ⧸ A` is a simple `A`-module and `algebraMap A S a ∈ 𝔪 S`, then `a ∈ 𝔪`. -/
public theorem mem_maximalIdeal_of_algebraMap_mem_map_of_isSimpleModule
    (h : IsSimpleModule A (S ⧸ LinearMap.range (Algebra.linearMap A S))) {a : A}
    (ha : algebraMap A S a ∈ (maximalIdeal A).map (algebraMap A S)) :
    a ∈ maximalIdeal A := by
  by_contra hna
  exact map_maximalIdeal_ne_top_of_isSimpleModule A S h
    (Ideal.eq_top_of_isUnit_mem _ ha ((notMem_maximalIdeal.mp hna).map (algebraMap A S)))

end General

/-! ### The closed fibre of the normalization -/

section ClosedFibre

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- In the closed fibre of the normalization, the class of the image of `a ∈ A` is
`residue A a • 1`. -/
public theorem quotient_mk_algebraMap_integralClosure (a : A) :
    Ideal.Quotient.mk ((maximalIdeal A).map
        (algebraMap A ↥(integralClosure A (FractionRing A))))
          (algebraMap A ↥(integralClosure A (FractionRing A)) a)
      = residue A a • (1 : quadraticAlgebra A) := by
  rw [Algebra.smul_def, mul_one]
  rfl

/-- In the closed fibre of the normalization, the class of `a t` is `residue A a` times the class
of `t`. -/
public theorem quotient_mk_algebraMap_mul_integralClosure
    (a : A) (t : ↥(integralClosure A (FractionRing A))) :
    Ideal.Quotient.mk ((maximalIdeal A).map
        (algebraMap A ↥(integralClosure A (FractionRing A))))
          (algebraMap A ↥(integralClosure A (FractionRing A)) a * t)
      = residue A a • (Ideal.Quotient.mk ((maximalIdeal A).map
          (algebraMap A ↥(integralClosure A (FractionRing A)))) t) := by
  rw [map_mul, quotient_mk_algebraMap_integralClosure, Algebra.smul_def, Algebra.smul_def]
  ring

/-- If `Ring.deltaInvariant A = 1`, with `A'` the normalization of `A`, then there is `t ∈ A'` such
that `𝔪 A'` lies in the image of `A`, `A' = A + A t`, the elements `1` and the class of `t` are
linearly independent and span the closed fibre `A' ⧸ 𝔪 A'` over the residue field, and
`a + b t ∈ 𝔪 A'` forces `a, b ∈ 𝔪`. -/
public theorem exists_linearIndependent_quadraticAlgebra_of_deltaInvariant_eq_one
    (hdelta : Ring.deltaInvariant A = 1) :
    ∃ t : ↥(integralClosure A (FractionRing A)),
      (((maximalIdeal A).map
          (algebraMap A ↥(integralClosure A (FractionRing A)))).restrictScalars A ≤
        LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A)))) ∧
      (LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) ⊔
        Submodule.span A {t} = ⊤) ∧
      LinearIndependent (ResidueField A)
        ![(1 : quadraticAlgebra A), Ideal.Quotient.mk ((maximalIdeal A).map
          (algebraMap A ↥(integralClosure A (FractionRing A)))) t] ∧
      ⊤ ≤ Submodule.span (ResidueField A) (Set.range
        ![(1 : quadraticAlgebra A), Ideal.Quotient.mk ((maximalIdeal A).map
          (algebraMap A ↥(integralClosure A (FractionRing A)))) t]) ∧
      (∀ lam mu : A,
        algebraMap A ↥(integralClosure A (FractionRing A)) lam +
            algebraMap A ↥(integralClosure A (FractionRing A)) mu * t ∈
          (maximalIdeal A).map (algebraMap A ↥(integralClosure A (FractionRing A))) →
        lam ∈ maximalIdeal A ∧ mu ∈ maximalIdeal A) := by
  classical
  set B := ↥(integralClosure A (FractionRing A))
  set R := LinearMap.range (Algebra.linearMap A B)
  set J := (maximalIdeal A).map (algebraMap A B)
  have hsimple : IsSimpleModule A (B ⧸ R) := Module.length_eq_one_iff.mp hdelta
  have hJle : (J.restrictScalars A) ≤ R :=
    map_maximalIdeal_restrictScalars_le_range_of_isSimpleModule A B hsimple
  obtain ⟨t, htnot, htop⟩ :=
    exists_notMem_range_sup_span_singleton_eq_top_of_isSimpleModule A B hsimple
  refine ⟨t, hJle, htop, ?_⟩
  have hpair : ∀ a₁ a₂ : A, algebraMap A B a₁ + algebraMap A B a₂ * t ∈ J →
      a₁ ∈ maximalIdeal A ∧ a₂ ∈ maximalIdeal A := by
    intro a₁ a₂ hkey
    have ha₂ : a₂ ∈ maximalIdeal A := by
      by_contra hna
      obtain ⟨a₂', ha₂'⟩ : ∃ a₂' : A, a₂' * a₂ = 1 := by
        obtain ⟨u, hu⟩ := notMem_maximalIdeal.mp hna
        exact ⟨↑u⁻¹, by rw [← hu]; exact u.inv_mul⟩
      obtain ⟨b, hb⟩ : algebraMap A B a₂ * t ∈ R := by
        have h1 : algebraMap A B a₁ ∈ R := ⟨a₁, rfl⟩
        simpa using sub_mem (hJle hkey) h1
      refine htnot ⟨a₂' * b, ?_⟩
      have hb' : algebraMap A B b = algebraMap A B a₂ * t := hb
      simp only [Algebra.linearMap_apply, map_mul]
      rw [hb', ← mul_assoc, ← map_mul, ha₂', map_one, one_mul]
    refine ⟨mem_maximalIdeal_of_algebraMap_mem_map_of_isSimpleModule A B hsimple ?_, ha₂⟩
    have hz : algebraMap A B a₂ * t ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, quotient_mk_algebraMap_mul_integralClosure,
        (residue_eq_zero_iff a₂).mpr ha₂, zero_smul]
    simpa using sub_mem hkey hz
  have hli : LinearIndependent (ResidueField A)
      ![(1 : quadraticAlgebra A), Ideal.Quotient.mk J t] := by
    rw [LinearIndependent.pair_iff]
    intro c₁ c₂ hc
    obtain ⟨a₁, rfl⟩ := residue_surjective c₁
    obtain ⟨a₂, rfl⟩ := residue_surjective c₂
    obtain ⟨h₁, h₂⟩ := hpair a₁ a₂ (by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_add,
        quotient_mk_algebraMap_integralClosure, quotient_mk_algebraMap_mul_integralClosure]
      exact hc)
    exact ⟨(residue_eq_zero_iff a₁).mpr h₁, (residue_eq_zero_iff a₂).mpr h₂⟩
  have hsp : ⊤ ≤ Submodule.span (ResidueField A)
      (Set.range ![(1 : quadraticAlgebra A), Ideal.Quotient.mk J t]) := by
    intro z _
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) z
    have hs : s ∈ R ⊔ Submodule.span A {t} := htop ▸ Submodule.mem_top
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hs
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [show (Algebra.linearMap A B) a = algebraMap A B a from rfl,
        quotient_mk_algebraMap_integralClosure]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · rw [show c • t = algebraMap A B c * t from (Algebra.smul_def c t),
        quotient_mk_algebraMap_mul_integralClosure]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  exact ⟨hli, hsp, hpair⟩

/-- The closed fibre of the normalization of a local ring of delta invariant one is two-dimensional
over the residue field. -/
public theorem finrank_quadraticAlgebra_eq_two_of_deltaInvariant_eq_one
    (hdelta : Ring.deltaInvariant A = 1) :
    Module.finrank (ResidueField A) (quadraticAlgebra A) = 2 := by
  obtain ⟨_t, -, -, hli, hsp, -⟩ :=
    exists_linearIndependent_quadraticAlgebra_of_deltaInvariant_eq_one A hdelta
  simpa using Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)

end ClosedFibre

end Stacks.Curves

end
