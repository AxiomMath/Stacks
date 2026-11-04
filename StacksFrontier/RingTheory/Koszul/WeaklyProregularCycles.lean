module

public import StacksFrontier.RingTheory.Koszul.WeaklyProregular
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.KoszulTateComparison

/-!
# Weak proregularity on cycles, and Noetherian rings

Let `f₁, …, f_r` be elements of a commutative ring `R` and let `K_n` be the Koszul algebra on
`f₁ ^ n, …, f_r ^ n`. Weak proregularity (Stacks 0H1E) asks that for every `n` some transition
homomorphism `K_m → K_n` with `m > n` be zero on cohomology outside degree `0`. Since `K_n` is the
exterior algebra of `Rʳ` with the contraction against `(f₁ ^ n, …, f_r ^ n)` as differential, this
says, element by element, that every cycle of positive exterior degree of `K_m` is carried to a
boundary of `K_n`: the condition `DividedPowers.TateResolution.KillsKoszulHomology` that Tate's
comparison of Tag 0GZ4 consumes. This file proves the two readings equivalent, and deduces from
Stacks 0921 that a sequence in a Noetherian ring is weakly proregular.

## Main results

* `HomologicalComplex.homologyMap_eq_zero_of_forall_mem_range`: a map of complexes of modules
  carrying every cycle of a degree into the image of the differential is zero on homology there.
* `Koszul.isWeaklyProregular_iff_killsKoszulHomology`: weak proregularity is the existence, for
  every `n ≥ 1`, of an `N > n` such that `K_N → K_n` carries every cycle of positive exterior
  degree to a boundary.
* `Koszul.isWeaklyProregular_of_isNoetherianRing`: **a finite sequence of elements of a
  Noetherian ring is weakly proregular.**

## References

* [Stacks Project, Tag 0H1E](https://stacks.math.columbia.edu/tag/0H1E)
* [Stacks Project, Tag 0921](https://stacks.math.columbia.edu/tag/0921)
* [Stacks Project, Tag 0GZ4](https://stacks.math.columbia.edu/tag/0GZ4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace HomologicalComplex

/-- A map of complexes is zero on homology iff it sends cycles to zero in the opcycles. -/
private theorem homologyMap_eq_zero_iff_iCycles_comp {R : Type u} [CommRing R] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex (ModuleCat.{u} R) c} (φ : K ⟶ L) (i : ι) :
    homologyMap φ i = 0 ↔ K.iCycles i ≫ φ.f i ≫ L.pOpcycles i = 0 := by
  have h1 : K.homologyπ i ≫ homologyMap φ i ≫ L.homologyι i =
      K.iCycles i ≫ φ.f i ≫ L.pOpcycles i := by
    rw [← Category.assoc, homologyπ_naturality, Category.assoc, homology_π_ι,
      ← Category.assoc, cyclesMap_i, Category.assoc]
  rw [← h1, ← cancel_epi (K.homologyπ i), ← cancel_mono (L.homologyι i)]
  simp

/-- A map of complexes of modules which carries every cycle of degree `i` into the image of the
differential arriving in degree `i` induces the zero map on homology in degree `i`. -/
theorem homologyMap_eq_zero_of_forall_mem_range {R : Type u} [CommRing R] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex (ModuleCat.{u} R) c} (φ : K ⟶ L) (i : ι)
    (h : ∀ x : K.X i, K.d i (c.next i) x = 0 →
      φ.f i x ∈ LinearMap.range (L.d (c.prev i) i).hom) :
    homologyMap φ i = 0 := by
  rw [homologyMap_eq_zero_iff_iCycles_comp]
  ext y
  have hy : K.d i (c.next i) (K.iCycles i y) = 0 := by
    rw [← ModuleCat.comp_apply, K.iCycles_d]
    rfl
  exact ((L.sc i).moduleCat_pOpcycles_eq_zero_iff _).2 (h _ hy)

/-- `homologyMap_eq_zero_of_forall_mem_range`, with the differentials into and out of degree `i`
taken between given related indices. -/
theorem homologyMap_eq_zero_of_forall_mem_range' {R : Type u} [CommRing R] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex (ModuleCat.{u} R) c} (φ : K ⟶ L)
    {h i k : ι} (hhi : c.Rel h i) (hik : c.Rel i k)
    (hφ : ∀ x : K.X i, K.d i k x = 0 → φ.f i x ∈ LinearMap.range (L.d h i).hom) :
    homologyMap φ i = 0 := by
  refine homologyMap_eq_zero_of_forall_mem_range φ i fun x hx => ?_
  rw [c.prev_eq' hhi]
  rw [c.next_eq' hik] at hx
  exact hφ x hx

/-- Conversely, a map of complexes of modules which is zero on homology in degree `i` carries
every cycle of degree `i` into the image of the differential arriving in degree `i`, taken from
any index related to `i`. -/
theorem mem_range_d_of_homologyMap_eq_zero {R : Type u} [CommRing R] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex (ModuleCat.{u} R) c} (φ : K ⟶ L)
    {h i k : ι} (hhi : c.Rel h i) (hik : c.Rel i k) (hφ : homologyMap φ i = 0)
    {x : K.X i} (hx : K.d i k x = 0) : φ.f i x ∈ LinearMap.range (L.d h i).hom := by
  have hzero := (homologyMap_eq_zero_iff_iCycles_comp φ i).1 hφ
  have hx' : K.d i (c.next i) x = 0 := by rwa [c.next_eq' hik]
  obtain ⟨y, hiy⟩ : ∃ y : ↑(K.cycles i), K.iCycles i y = x :=
    ⟨(K.sc i).moduleCatCyclesIso.inv ⟨x, hx'⟩,
      (K.sc i).moduleCatCyclesIso_inv_iCycles_apply ⟨x, hx'⟩⟩
  have h2 : L.pOpcycles i (φ.f i (K.iCycles i y)) = 0 := by
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← Category.assoc, Category.assoc, hzero]
    rfl
  rw [hiy] at h2
  have h3 := ((L.sc i).moduleCat_pOpcycles_eq_zero_iff (φ.f i x)).1 h2
  change φ.f i x ∈ LinearMap.range (L.d (c.prev i) i).hom at h3
  rwa [c.prev_eq' hhi] at h3

end HomologicalComplex

namespace Koszul

open DividedPowers.TateResolution

variable {R : Type u} [CommRing R] {r : ℕ}

attribute [local implicit_reducible] powAlgebra cohomologicalDifferentialGradedAlgebra
  DifferentialGradedModule.toCochainComplex

/-- The cohomological degree `-(j + 1)` of `K_n` is the exterior degree `j + 1`. -/
theorem powAlgebra_grading_neg_succ (f : Fin r → R) (n j : ℕ) :
    (powAlgebra f n).grading (-((j + 2 : ℕ) : ℤ) + 1) = exteriorGrade R (Fin r → R) (j + 1) := by
  rw [show -((j + 2 : ℕ) : ℤ) + 1 = -((j + 1 : ℕ) : ℤ) by omega]
  exact powAlgebra_grading_neg_natCast f n (j + 1)

/-- **Weak proregularity on cycles.** A sequence is weakly proregular exactly when for every
`n ≥ 1` there is an `N > n` such that the transition homomorphism `K_N → K_n` carries every
cycle of positive exterior degree to a boundary. -/
theorem isWeaklyProregular_iff_killsKoszulHomology (f : Fin r → R) :
    IsWeaklyProregular f ↔
      ∀ n : ℕ, 1 ≤ n → ∃ N : ℕ, n < N ∧ ∀ j : ℕ, KillsKoszulHomology f n N j := by
  constructor
  · intro hf n hn
    obtain ⟨N, hN, hzero⟩ := hf n hn
    refine ⟨N, hN, fun j x hx hdx => ?_⟩
    set p : ℤ := -((j + 2 : ℕ) : ℤ) with hp
    have hx' : x ∈ (powAlgebra f N).grading (p + 1) := by rwa [powAlgebra_grading_neg_succ]
    obtain ⟨⟨y, hyp⟩, hy⟩ := HomologicalComplex.mem_range_d_of_homologyMap_eq_zero
      (powTransition f hn hN.le).toCochainMap (c := ComplexShape.up ℤ) (h := p) (i := p + 1)
      (k := p + 1 + 1) rfl rfl (hzero (p + 1) (by omega)) (x := ⟨x, hx'⟩)
      (by rw [DifferentialGradedModule.toCochainComplex_d]; exact Subtype.ext hdx)
    change y ∈ (powAlgebra f n).grading p at hyp
    have h := congrArg Subtype.val hy
    rw [DifferentialGradedModule.toCochainComplex_d] at h
    exact ⟨y, by rwa [hp, powAlgebra_grading_neg_natCast] at hyp, h⟩
  · intro hf n hn
    obtain ⟨N, hN, hkill⟩ := hf n hn
    refine ⟨N, hN, fun i hi => ?_⟩
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = -((j + 2 : ℕ) : ℤ) + 1 := ⟨(-i - 1).toNat, by omega⟩
      refine HomologicalComplex.homologyMap_eq_zero_of_forall_mem_range'
        (c := ComplexShape.up ℤ) _ (h := -((j + 2 : ℕ) : ℤ)) (k := -((j + 2 : ℕ) : ℤ) + 1 + 1)
        rfl rfl fun x hx => ?_
      obtain ⟨x, hx0⟩ := x
      have hxm : x ∈ exteriorGrade R (Fin r → R) (j + 1) := by
        change x ∈ (powAlgebra f N).grading _ at hx0
        rwa [powAlgebra_grading_neg_succ] at hx0
      have hdx := congrArg Subtype.val hx
      rw [DifferentialGradedModule.toCochainComplex_d] at hdx
      obtain ⟨y, hy, hdy⟩ := hkill j x hxm hdx
      have hy' : y ∈ (powAlgebra f n).grading (-((j + 2 : ℕ) : ℤ)) := by
        rwa [powAlgebra_grading_neg_natCast]
      refine ⟨⟨y, hy'⟩, ?_⟩
      rw [DifferentialGradedModule.toCochainComplex_d]
      exact Subtype.ext hdy
    · exact (isZero_homology_powCochain f n (Or.inr hpos)).eq_of_tgt _ _

/-- **A finite sequence of elements of a Noetherian ring is weakly proregular.** This is the
Artin–Rees argument of Stacks 0921. -/
theorem isWeaklyProregular_of_isNoetherianRing [IsNoetherianRing R] (f : Fin r → R) :
    IsWeaklyProregular f := by
  refine (isWeaklyProregular_iff_killsKoszulHomology f).2 fun n _ => ?_
  obtain ⟨N, hN, h⟩ := exists_killsKoszulHomology f n
  exact ⟨N + 1, by omega, fun j => killsKoszulHomology_of_le f hN (Nat.le_succ N) (h j)⟩

end Koszul
