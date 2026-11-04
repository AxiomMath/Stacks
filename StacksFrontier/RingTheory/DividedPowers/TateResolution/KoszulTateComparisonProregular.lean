module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.KoszulTateComparison
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.TateTowerLift
public import StacksFrontier.RingTheory.Koszul.WeaklyProregularCycles

/-! # Tate resolutions interpolating between Koszul algebras of a weakly proregular sequence

Let `R` be a ring and `f₁, …, f_r ∈ R`, and write `K_m` for the Koszul divided power algebra
`R⟨ξ₁, …, ξ_r⟩` with `ξᵢ` of degree one and `d(ξᵢ) = fᵢ^m`, with transition maps
`K_M → K_m`, `ξᵢ ↦ fᵢ^(M-m) ξᵢ`. Tag 0GZ4 states, over a Noetherian ring, that for every `n` there
is an `N ≥ n` and a divided power differential graded algebra `A` resolving
`R/(f₁^N, …, f_r^N)` with maps `K_N → A → R/(f₁^N, …, f_r^N)` and `A → K_n` whose composites are
the canonical map and the transition map. This file proves the same statement for a weakly
proregular sequence (Stacks 0H1E) and every exponent `n ≥ 1`, without any finiteness hypothesis
on `R`, at the price of the finiteness of the resolution in each degree.

The Noetherian hypothesis enters the proof of Tag 0GZ4 in two places. The first is the
Artin--Rees input that some transition map into `K_n` kills the homology in positive degrees;
for a weakly proregular sequence this is the definition, read on cycles by
`Koszul.isWeaklyProregular_iff_killsKoszulHomology`. The second is the acyclicity of Tate's
degreewise finite tower, which needs a finite spanning family of the cycles in each degree.
Here that tower is replaced by Tate's tower killing **every** cycle of positive degree
(`DividedPowers.TateResolution.tateColimit`), which is acyclic with no hypothesis; it has the
same base, the ring `R` with `r` variables of degree one killing `f₁^N, …, f_r^N`, so the map
`K_N → A`, `ξᵢ ↦ Tᵢ`, is constructed as before, and the map `A → K_n` is built stage by stage
along the same chain of exponents.

## Main definitions

* `DividedPowers.TateResolution.koszulTateFullAlgebra` — the colimit of Tate's tower over `R`
  killing the `N`-th powers, with its differential
  `DividedPowers.TateResolution.koszulTateFullDifferential`, its coefficients
  `DividedPowers.TateResolution.koszulTateFullCoefficient`, its variables
  `DividedPowers.TateResolution.koszulTateFullVariable` and its augmentation
  `DividedPowers.TateResolution.koszulTateFullAugmentation`.

## Main results

* `DividedPowers.TateResolution.exists_koszulTateFullAlpha` and
  `DividedPowers.TateResolution.exists_koszulTateFullBeta` — the two maps `K_N → A` and
  `A → K_n`.
* `DividedPowers.TateResolution.exists_tateResolution_koszulPowers_of_killsKoszulHomology` —
  Tag 0GZ4 for a sequence whose transition maps eventually kill the positive Koszul homology.
* `DividedPowers.TateResolution.exists_tateResolution_koszulPowers_of_isWeaklyProregular` —
  Tag 0GZ4 for a weakly proregular sequence.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 0GZ4](https://stacks.math.columbia.edu/tag/0GZ4)
* [Stacks Project, Tag 0H1E](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public section

namespace DividedPowers.TateResolution

open scoped ExteriorAlgebra

universe u

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

attribute [local instance] TateDatum.dga TateDatum.compatible

section Tower

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The full Koszul Tate algebra: the colimit of Tate's tower over `R` killing the `N`-th powers
in degree zero and every cycle in positive degrees. -/
public noncomputable abbrev koszulTateFullAlgebra (f : Fin r → R) (N : ℕ) :
    GradedDPAlgebra.{u, u} R :=
  tateColimit (koszulTateBase f N)

/-- Its differential. -/
public noncomputable abbrev koszulTateFullDifferential (f : Fin r → R) (N : ℕ) :
    (koszulTateFullAlgebra f N).carrier →ₗ[R] (koszulTateFullAlgebra f N).carrier :=
  tateColimitDifferential (koszulTateBase f N)

/-- Its degree-zero algebra, which is `R`. -/
public noncomputable def koszulTateFullCoefficient (f : Fin r → R) (N : ℕ) :
    R →ₐ[R] (koszulTateFullAlgebra f N).carrier :=
  (tateCoefficient (koszulTateBase f N)).hom

/-- Its variables, indexed together with their degrees. -/
public noncomputable def koszulTateFullVariable (f : Fin r → R) (N : ℕ)
    (j : Σ n : ℕ, tateIndex (koszulTateBase f N) n) :
    (koszulTateFullAlgebra f N).carrier :=
  tateVariable (koszulTateBase f N) j.1 j.2

/-- Each variable of the full Koszul Tate algebra is homogeneous of its prescribed degree. -/
public theorem koszulTateFullVariable_mem (f : Fin r → R) (N : ℕ)
    (j : Σ n : ℕ, tateIndex (koszulTateBase f N) n) :
    koszulTateFullVariable f N j ∈ (koszulTateFullAlgebra f N).grade (j.1 + 1) :=
  tateVariable_mem (koszulTateBase f N) j.1 j.2

/-- The degree-zero algebra of the full Koszul Tate algebra lands in degree zero. -/
public theorem koszulTateFullCoefficient_mem_grade_zero (f : Fin r → R) (N : ℕ) (p : R) :
    koszulTateFullCoefficient f N p ∈ (koszulTateFullAlgebra f N).grade 0 :=
  (tateCoefficient (koszulTateBase f N)).map_grade 0 _ (mem_degreeZeroGrade_zero R R _)

/-- The degree-zero algebra of the full Koszul Tate algebra is a subalgebra. -/
public theorem koszulTateFullCoefficient_injective (f : Fin r → R) (N : ℕ) :
    Function.Injective (koszulTateFullCoefficient f N) :=
  tateInclusion_injective (koszulTateBase f N) 0

/-- **The degree-zero part of the full Koszul Tate algebra is `R`.** No step of the tower adds
anything in degree zero, and the base has nothing of positive degree. -/
public theorem mem_koszulTateFullAlgebra_grade_zero_iff (f : Fin r → R) (N : ℕ)
    (a : (koszulTateFullAlgebra f N).carrier) :
    a ∈ (koszulTateFullAlgebra f N).grade 0 ↔ ∃ p : R, koszulTateFullCoefficient f N p = a := by
  refine ⟨fun ha => ?_, fun ⟨p, hp⟩ => hp ▸ koszulTateFullCoefficient_mem_grade_zero f N p⟩
  obtain ⟨z, -, hz⟩ := exists_tateInclusion_eq_of_mem_grade (koszulTateBase f N) 0 ha
  exact ⟨z, hz⟩

/-- The augmentation onto `R/(f₁^N, …, f_r^N)` exists: the morphism out of the colimit restricting
to the quotient map on the coefficients and killing every variable. -/
public theorem exists_koszulTateFullAugmentation (f : Fin r → R) (N : ℕ) :
    ∃ F : GradedDPHom (koszulTateFullAlgebra f N)
        (degreeZeroDPAlgebra R (R ⧸ koszulPowerIdeal f N)),
      (∀ p : R, F.hom (koszulTateFullCoefficient f N p) =
          Ideal.Quotient.mk (koszulPowerIdeal f N) p) ∧
        ∀ (n : ℕ) (j : tateIndex (koszulTateBase f N) n),
          F.hom (tateVariable (koszulTateBase f N) n j) = 0 :=
  tateColimit_exists_gradedDPHom (koszulTateBase f N)
    (degreeZeroDPAlgebra R (R ⧸ koszulPowerIdeal f N))
    (degreeZeroDPHom R R (degreeZeroDPAlgebra R (R ⧸ koszulPowerIdeal f N))
      (show R →ₐ[R] R ⧸ koszulPowerIdeal f N from Ideal.Quotient.mkₐ R (koszulPowerIdeal f N))
      (fun _ => mem_degreeZeroGrade_zero R (R ⧸ koszulPowerIdeal f N) _))
    (fun _ _ => 0) (fun _ _ => Submodule.zero_mem _)

/-- **The augmentation of the full Koszul Tate algebra** onto `R/(f₁^N, …, f_r^N)`. -/
public noncomputable def koszulTateFullAugmentation (f : Fin r → R) (N : ℕ) :
    GradedDPHom (koszulTateFullAlgebra f N) (degreeZeroDPAlgebra R (R ⧸ koszulPowerIdeal f N)) :=
  (exists_koszulTateFullAugmentation f N).choose

/-- The augmentation is the quotient map on the degree-zero algebra. -/
public theorem koszulTateFullAugmentation_coefficient (f : Fin r → R) (N : ℕ) (p : R) :
    (koszulTateFullAugmentation f N).hom (koszulTateFullCoefficient f N p) =
      Ideal.Quotient.mk (koszulPowerIdeal f N) p :=
  (exists_koszulTateFullAugmentation f N).choose_spec.1 p

/-- The augmentation kills every variable. -/
public theorem koszulTateFullAugmentation_variable (f : Fin r → R) (N : ℕ)
    (j : Σ n : ℕ, tateIndex (koszulTateBase f N) n) :
    (koszulTateFullAugmentation f N).hom (koszulTateFullVariable f N j) = 0 :=
  (exists_koszulTateFullAugmentation f N).choose_spec.2 j.1 j.2

/-- The augmentation kills the positive-degree part: its target is concentrated in degree
zero. -/
public theorem koszulTateFullAugmentation_positive (f : Fin r → R) (N : ℕ) {n : ℕ} (hn : n ≠ 0)
    {a : (koszulTateFullAlgebra f N).carrier} (ha : a ∈ (koszulTateFullAlgebra f N).grade n) :
    (koszulTateFullAugmentation f N).hom a = 0 :=
  eq_zero_of_mem_degreeZeroDPAlgebra_grade R _ hn
    ((koszulTateFullAugmentation f N).map_grade n a ha)

/-- The differential of the full Koszul Tate algebra vanishes in degree zero. -/
public theorem koszulTateFullDifferential_grade_zero (f : Fin r → R) (N : ℕ)
    {x : (koszulTateFullAlgebra f N).carrier} (hx : x ∈ (koszulTateFullAlgebra f N).grade 0) :
    koszulTateFullDifferential f N x = 0 :=
  IsDifferentialGradedAlgebra.d_grade_zero (𝒜 := (koszulTateFullAlgebra f N).grade)
    (d := koszulTateFullDifferential f N)
    (self := tateColimitDga (koszulTateBase f N)) hx

/-- The differential of the full Koszul Tate algebra satisfies the signed Leibniz rule. -/
public theorem koszulTateFullDifferential_leibniz (f : Fin r → R) (N : ℕ) {i k : ℕ}
    {x y : (koszulTateFullAlgebra f N).carrier} (hx : x ∈ (koszulTateFullAlgebra f N).grade i)
    (hy : y ∈ (koszulTateFullAlgebra f N).grade k) :
    koszulTateFullDifferential f N (x * y) =
      koszulTateFullDifferential f N x * y +
        (-1 : R) ^ i • (x * koszulTateFullDifferential f N y) :=
  IsDifferentialGradedAlgebra.leibniz (𝒜 := (koszulTateFullAlgebra f N).grade)
    (d := koszulTateFullDifferential f N)
    (self := tateColimitDga (koszulTateBase f N)) hx hy

/-- The finite variable stages of the full Koszul Tate algebra cover it. -/
public theorem koszulTateFullAlgebra_finite_support (f : Fin r → R) (N : ℕ)
    (x : (koszulTateFullAlgebra f N).carrier) :
    ∃ T : Finset (Σ n : ℕ, tateIndex (koszulTateBase f N) n),
      x ∈ finiteVariableStage (koszulTateFullAlgebra f N).gamma (koszulTateFullCoefficient f N)
        (koszulTateFullVariable f N) T :=
  tateColimit_finite_support (koszulTateBase f N) x

/-- **The augmentation kills the boundary of every variable.** For a variable of degree one the
boundary is one of the powers `fᵢ^N`, which the quotient map kills; in higher degree the boundary
is homogeneous of positive degree, where the augmentation vanishes. -/
public theorem koszulTateFullAugmentation_differential_variable (f : Fin r → R) (N : ℕ)
    (j : Σ n : ℕ, tateIndex (koszulTateBase f N) n) :
    (koszulTateFullAugmentation f N).hom
      (koszulTateFullDifferential f N (koszulTateFullVariable f N j)) = 0 := by
  obtain ⟨n, j⟩ := j
  rw [koszulTateFullVariable, tateColimitDifferential_variable (koszulTateBase f N) n j]
  match n with
  | 0 =>
      refine (koszulTateFullAugmentation_coefficient f N
        (tateCycle (koszulTateBase f N) 0 j)).trans ?_
      exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_koszulPowerIdeal f N j.down)
  | m + 1 =>
      refine koszulTateFullAugmentation_positive f N (Nat.succ_ne_zero m) ?_
      exact (tateInclusion (koszulTateBase f N) (m + 1)).map_grade (m + 1) _
        (tateCycle_mem (koszulTateBase f N) (m + 1) j)

/-- Only one homogeneous component of a homogeneous element is nonzero, so the augmentation kills
the boundary of each component as soon as it kills the boundary of the element. -/
public theorem koszulTateFullAugmentation_differential_gradedPart (f : Fin r → R) (N : ℕ) {k : ℕ}
    {x : (koszulTateFullAlgebra f N).carrier} (hx : x ∈ (koszulTateFullAlgebra f N).grade k)
    (h : (koszulTateFullAugmentation f N).hom (koszulTateFullDifferential f N x) = 0) (m : ℕ) :
    (koszulTateFullAugmentation f N).hom (koszulTateFullDifferential f N
      (gradedPart (koszulTateFullAlgebra f N).grade x m)) = 0 := by
  by_cases hm : k = m
  · subst hm
    rwa [gradedPart_of_mem_same _ hx]
  · rw [gradedPart_of_mem_ne _ hx hm, map_zero, map_zero]

/-- The elements all of whose homogeneous components have their boundary killed by the
augmentation form a subring: closure under multiplication is the Leibniz rule. -/
public noncomputable def koszulTateFullBoundaryKernel (f : Fin r → R) (N : ℕ) :
    Subring (koszulTateFullAlgebra f N).carrier where
  carrier := {x | ∀ m : ℕ, (koszulTateFullAugmentation f N).hom
    (koszulTateFullDifferential f N (gradedPart (koszulTateFullAlgebra f N).grade x m)) = 0}
  zero_mem' := by
    intro m
    rw [gradedPart_zero, map_zero, map_zero]
  one_mem' := by
    refine koszulTateFullAugmentation_differential_gradedPart f N
      (SetLike.one_mem_graded (koszulTateFullAlgebra f N).grade) ?_
    rw [koszulTateFullDifferential_grade_zero f N
      (SetLike.one_mem_graded (koszulTateFullAlgebra f N).grade), map_zero]
  add_mem' := by
    intro x y hx hy m
    rw [gradedPart_add, map_add, map_add, hx m, hy m, add_zero]
  neg_mem' := by
    intro x hx m
    rw [gradedPart_neg, map_neg, map_neg, hx m, neg_zero]
  mul_mem' := by
    intro x y hx hy m
    obtain ⟨s, hs⟩ := exists_gradedPart_decomposition (koszulTateFullAlgebra f N).grade x
    obtain ⟨t, ht⟩ := exists_gradedPart_decomposition (koszulTateFullAlgebra f N).grade y
    have hxy : gradedPart (koszulTateFullAlgebra f N).grade (x * y) m =
        ∑ i ∈ s, ∑ k ∈ t, gradedPart (koszulTateFullAlgebra f N).grade
          (gradedPart (koszulTateFullAlgebra f N).grade x i *
            gradedPart (koszulTateFullAlgebra f N).grade y k) m := by
      conv_lhs => rw [hs, ht]
      exact gradedPart_mul_sum (koszulTateFullAlgebra f N).grade _ _ m
    rw [hxy, map_sum, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : i + k = m
    · rw [gradedPart_mul_homogeneous _ (gradedPart_mem _ x i) (gradedPart_mem _ y k) hik,
        koszulTateFullDifferential_leibniz f N (gradedPart_mem _ x i) (gradedPart_mem _ y k),
        map_add, map_mul, hx i, zero_mul, zero_add, map_smul, map_mul, hy k, mul_zero,
        smul_zero]
    · rw [gradedPart_mul_homogeneous_of_ne _ (gradedPart_mem _ x i) (gradedPart_mem _ y k) hik,
        map_zero, map_zero]

/-- A homogeneous element whose boundary the augmentation kills lies in the subring. -/
public theorem mem_koszulTateFullBoundaryKernel_of_mem_grade (f : Fin r → R) (N : ℕ) {k : ℕ}
    {x : (koszulTateFullAlgebra f N).carrier} (hx : x ∈ (koszulTateFullAlgebra f N).grade k)
    (h : (koszulTateFullAugmentation f N).hom (koszulTateFullDifferential f N x) = 0) :
    x ∈ koszulTateFullBoundaryKernel f N :=
  koszulTateFullAugmentation_differential_gradedPart f N hx h

/-- The degree-zero algebra lies in the subring: the differential vanishes in degree zero. -/
public theorem koszulTateFullCoefficient_mem_koszulTateFullBoundaryKernel (f : Fin r → R) (N : ℕ)
    (p : R) :
    koszulTateFullCoefficient f N p ∈ koszulTateFullBoundaryKernel f N := by
  refine mem_koszulTateFullBoundaryKernel_of_mem_grade f N
    (koszulTateFullCoefficient_mem_grade_zero f N p) ?_
  rw [koszulTateFullDifferential_grade_zero f N (koszulTateFullCoefficient_mem_grade_zero f N p),
    map_zero]

/-- Every variable lies in the subring. -/
public theorem koszulTateFullVariable_mem_koszulTateFullBoundaryKernel (f : Fin r → R) (N : ℕ)
    (j : Σ n : ℕ, tateIndex (koszulTateBase f N) n) :
    koszulTateFullVariable f N j ∈ koszulTateFullBoundaryKernel f N :=
  mem_koszulTateFullBoundaryKernel_of_mem_grade f N (koszulTateFullVariable_mem f N j)
    (koszulTateFullAugmentation_differential_variable f N j)

/-- **Every divided power of a variable lies in the subring.** It is homogeneous, and by
compatibility of the divided powers with the differential its boundary has the boundary of the
variable as a factor. -/
public theorem dpow_koszulTateFullVariable_mem_koszulTateFullBoundaryKernel (f : Fin r → R) (N : ℕ)
    (j : Σ n : ℕ, tateIndex (koszulTateBase f N) n) (n : ℕ) :
    (koszulTateFullAlgebra f N).gamma.dpow n (koszulTateFullVariable f N j) ∈
      koszulTateFullBoundaryKernel f N := by
  by_cases hpos : koszulTateFullVariable f N j ∈ positiveEvenPart (koszulTateFullAlgebra f N).grade
  · match n with
    | 0 =>
        rw [(koszulTateFullAlgebra f N).gamma.dpow_zero hpos]
        exact one_mem _
    | n + 1 =>
        have htail : (koszulTateFullAugmentation f N).hom
            (koszulTateFullDifferential f N
              ((koszulTateFullAlgebra f N).gamma.dpow (n + 1)
                (koszulTateFullVariable f N j))) = 0 := by
          rw [(tateColimitCompatible (koszulTateBase f N)).d_dpow
              (Nat.succ_ne_zero n) hpos, map_mul,
            koszulTateFullAugmentation_differential_variable f N j, zero_mul]
        rcases positiveEven_homogeneous_eq_zero_or_grade (koszulTateFullAlgebra f N).grade
          (koszulTateFullVariable_mem f N j) hpos with hzero | ⟨d, hd⟩
        · refine mem_koszulTateFullBoundaryKernel_of_mem_grade f N (k := 0) ?_ htail
          simpa using (koszulTateFullAlgebra f N).gamma.dpow_mem_grade (d := 0)
            (Nat.succ_ne_zero n) hpos (by rw [hzero]; exact Submodule.zero_mem _)
        · refine mem_koszulTateFullBoundaryKernel_of_mem_grade f N
            (k := 2 * (n + 1) * (d + 1)) ?_ htail
          exact (koszulTateFullAlgebra f N).gamma.dpow_mem_grade (Nat.succ_ne_zero n) hpos
            (hd ▸ koszulTateFullVariable_mem f N j)
  · rw [(koszulTateFullAlgebra f N).gamma.dpow_null hpos]
    exact zero_mem _

/-- **The augmentation kills every boundary.** -/
public theorem koszulTateFullAugmentation_differential (f : Fin r → R) (N : ℕ)
    (x : (koszulTateFullAlgebra f N).carrier) :
    (koszulTateFullAugmentation f N).hom (koszulTateFullDifferential f N x) = 0 := by
  obtain ⟨T, hT⟩ := koszulTateFullAlgebra_finite_support f N x
  have hx : x ∈ koszulTateFullBoundaryKernel f N :=
    finiteVariableStage_map_mem_subring (koszulTateFullAlgebra f N).gamma
      (koszulTateFullCoefficient f N) (koszulTateFullVariable f N) T
      (AlgHom.id R (koszulTateFullAlgebra f N).carrier) (koszulTateFullBoundaryKernel f N)
      (fun p => koszulTateFullCoefficient_mem_koszulTateFullBoundaryKernel f N p)
      (fun j _ => koszulTateFullVariable_mem_koszulTateFullBoundaryKernel f N j)
      (fun j _ n => dpow_koszulTateFullVariable_mem_koszulTateFullBoundaryKernel f N j n) hT
  obtain ⟨s, hs⟩ := exists_gradedPart_decomposition (koszulTateFullAlgebra f N).grade x
  conv_lhs => rw [hs]
  rw [map_sum, map_sum]
  exact Finset.sum_eq_zero fun m _ => hx m

/-- **Exactness in degree zero.** A degree-zero element killed by the augmentation lies in the
ideal, hence is a combination of the powers `fᵢ^N`, hence is the boundary of the corresponding
combination of the degree-one variables. -/
public theorem exists_koszulTateFullDifferential_boundary_of_grade_zero (f : Fin r → R) (N : ℕ)
    {a : (koszulTateFullAlgebra f N).carrier} (ha : a ∈ (koszulTateFullAlgebra f N).grade 0)
    (haug : (koszulTateFullAugmentation f N).hom a = 0) :
    ∃ b : (koszulTateFullAlgebra f N).carrier, b ∈ (koszulTateFullAlgebra f N).grade 1 ∧
      koszulTateFullDifferential f N b = a := by
  classical
  let _ : Fintype (tateIndex (koszulTateBase f N) 0) :=
    inferInstanceAs (Fintype (ULift.{u} (Fin r)))
  obtain ⟨p, hp⟩ := (mem_koszulTateFullAlgebra_grade_zero_iff f N a).1 ha
  have hpI : p ∈ koszulPowerIdeal f N := Ideal.Quotient.eq_zero_iff_mem.1 <| by
    rwa [← koszulTateFullAugmentation_coefficient f N p, hp]
  obtain ⟨c, hc⟩ : ∃ c : Fin r → R, ∑ i, c i * f i ^ N = p := by
    rw [koszulPowerIdeal, show Ideal.span (Set.range fun i => f i ^ N)
        = Submodule.span R (Set.range fun i => f i ^ N) from rfl,
      Submodule.mem_span_range_iff_exists_fun] at hpI
    simpa [smul_eq_mul] using hpI
  have hdga := tateColimitDga (koszulTateBase f N)
  obtain ⟨b, hb, hdb⟩ := exists_boundary_of_gradeZero_combination
    (koszulTateFullAlgebra f N).grade (koszulTateFullDifferential f N)
    (fun j : tateIndex (koszulTateBase f N) 0 => koszulTateFullCoefficient f N (f j.down ^ N))
    (fun j => tateVariable (koszulTateBase f N) 0 j) 0
    (fun j => tateVariable_mem (koszulTateBase f N) 0 j)
    (fun j => tateColimitDifferential_variable (koszulTateBase f N) 0 j)
    Finset.univ (fun j => koszulTateFullCoefficient f N (c j.down))
    (fun _ => koszulTateFullCoefficient_mem_grade_zero f N _)
  refine ⟨b, hb, hdb.trans ?_⟩
  rw [← hp]
  simp_rw [← map_mul]
  rw [← map_sum]
  refine congrArg (koszulTateFullCoefficient f N) ?_
  exact Eq.trans (Fintype.sum_equiv Equiv.ulift _
    (fun i : Fin r => c i * f i ^ N) (fun j => rfl)) hc

/-- **Exactness in positive degrees.** Tate's tower kills every cycle of positive degree, so this
needs no hypothesis on `R`. -/
public theorem exists_koszulTateFullDifferential_boundary_of_cycle (f : Fin r → R) (N n : ℕ)
    {a : (koszulTateFullAlgebra f N).carrier}
    (ha : a ∈ (koszulTateFullAlgebra f N).grade (n + 1))
    (hda : koszulTateFullDifferential f N a = 0) :
    ∃ b : (koszulTateFullAlgebra f N).carrier, b ∈ (koszulTateFullAlgebra f N).grade (n + 2) ∧
      koszulTateFullDifferential f N b = a :=
  exists_tateColimitDifferential_boundary_of_cycle (koszulTateBase f N) n ha hda

/-- The full Koszul Tate algebra has degree-zero coefficients and homogeneous variables. -/
public instance koszulTateFullIsHomogeneousVariableFamily (f : Fin r → R) (N : ℕ) :
    IsHomogeneousVariableFamily (koszulTateFullAlgebra f N).grade (koszulTateFullCoefficient f N)
      (koszulTateFullVariable f N) where
  coefficient_mem := koszulTateFullCoefficient_mem_grade_zero f N
  variable_homogeneous j := ⟨j.1 + 1, koszulTateFullVariable_mem f N j⟩

/-- **The full Koszul Tate algebra is free on its coefficients and its variables**: the mapping
property of the colimit of the tower. -/
public theorem koszulTateFullAlgebra_hasVariableMappingProperty (f : Fin r → R) (N : ℕ) :
    HasVariableMappingProperty (koszulTateFullAlgebra f N).gamma (koszulTateFullCoefficient f N)
      (koszulTateFullVariable f N) := by
  intro E g hg t ht
  obtain ⟨F, hF1, hF2⟩ := tateColimit_exists_gradedDPHom (koszulTateBase f N) E
    (degreeZeroDPHom R R E g hg) (fun n j => t ⟨n, j⟩) (fun n j => ht ⟨n, j⟩)
  exact ⟨F.hom.toRingHom, hF1, fun j => hF2 j.1 j.2, F.map_grade, F.map_dpow⟩

/-- **The full Koszul Tate algebra is a graded divided power polynomial algebra over `R`**, on
the variables adjoined by the tower. -/
public noncomputable def koszulTateFullPolynomial (f : Fin r → R) (N : ℕ) :
    GradedDividedPowerPolynomial (koszulTateFullAlgebra f N).grade (koszulTateFullAlgebra f N).gamma
      (koszulTateFullCoefficient f N) :=
  gradedDividedPowerPolynomialOfMappingProperty (koszulTateFullAlgebra f N).gamma
    (koszulTateFullCoefficient f N) (koszulTateFullVariable f N) (koszulTateFullVariable_mem f N)
    (koszulTateFullCoefficient_injective f N) (koszulTateFullAlgebra_finite_support f N)
    (koszulTateFullAlgebra_hasVariableMappingProperty f N)

end Tower

section Comparison

variable {R : Type u} [CommRing R] {r : ℕ}

/-- **The map `K_N → A` of Tag 0GZ4.** The `i`-th Koszul generator is sent to the degree-one
variable killing `fᵢ^N`, which exists because the base of the tower prescribes one variable per
index `i`. -/
public theorem exists_koszulTateFullAlpha (f : Fin r → R) (N : ℕ) :
    ∃ α : ExteriorAlgebra R (Fin r → R) →ₐ[R] (koszulTateFullAlgebra f N).carrier,
      (∀ i : Fin r, α (exteriorGen R r i) = koszulTateFullVariable f N ⟨0, ULift.up i⟩) ∧
      (∀ (m : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
        x ∈ exteriorGrade R (Fin r → R) m → α x ∈ (koszulTateFullAlgebra f N).grade m) ∧
      (∀ x, α (koszulPowerDifferential f N x) = koszulTateFullDifferential f N (α x)) ∧
      (∀ (k : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
        x ∈ positiveEvenPart (exteriorGrade R (Fin r → R)) →
          α ((exteriorDividedPowerStructure R r).dpow k x) =
            (koszulTateFullAlgebra f N).gamma.dpow k (α x)) := by
  have hdt : ∀ i : Fin r,
      koszulTateFullDifferential f N (koszulTateFullVariable f N ⟨0, ULift.up i⟩) =
      algebraMap R (koszulTateFullAlgebra f N).carrier (f i ^ N) := by
    intro i
    rw [koszulTateFullVariable,
      tateColimitDifferential_variable (koszulTateBase f N) 0 (ULift.up i)]
    exact (koszulTateFullCoefficient f N).commutes (f i ^ N)
  exact exists_algHom_exterior_of_mem_grade_one R r (koszulTateFullAlgebra f N).grade
    (koszulTateFullAlgebra f N).gamma (koszulTateFullDifferential f N)
    (tateColimitDga (koszulTateBase f N)) (fun i => f i ^ N)
    (fun i => koszulTateFullVariable f N ⟨0, ULift.up i⟩)
    (fun i => koszulTateFullVariable_mem f N ⟨0, ULift.up i⟩) hdt

/-- **Tate's lifting argument of Tag 0GZ4, for the full Tate tower.** Suppose that for every
`a ≥ 1` some transition map `K_b → K_a` with `b > a` sends every cycle of positive degree to a
boundary. Then for every `n ≥ 1` there is an `N ≥ n` and a morphism of differential graded divided
power algebras `A → K_n` out of the full Tate resolution of `R/(f₁^N, …, f_r^N)` which is the
identity of `R` in degree zero and sends the degree-one variable killing `fᵢ^N` to
`fᵢ^(N-n) ξᵢ`.

The map is built stage by stage along the tower. The target of the stage `k` is the Koszul
algebra of an exponent `e k`, the exponents decreasing from `N` to `n` along a chain whose
consecutive transition maps kill the homology in positive degrees; a cycle of degree `k` of the
stage therefore has a boundary as its image in the next Koszul algebra, which is the value given
to the variable killing it. Above degree `r` the Koszul algebra vanishes, so the remaining
variables are sent to zero and the exponent stays at `n`. -/
public theorem exists_koszulTateFullBeta (f : Fin r → R)
    (kills : ∀ a : ℕ, 1 ≤ a → ∃ b : ℕ, a < b ∧ ∀ j : ℕ, KillsKoszulHomology f a b j)
    {n : ℕ} (one_le : 1 ≤ n) :
    ∃ N : ℕ, n ≤ N ∧
      ∃ β : GradedDPHom (koszulTateFullAlgebra f N) (koszulGradedDPAlgebra R r),
        (∀ a, β.hom (koszulTateFullDifferential f N a) =
            koszulPowerDifferential f n (β.hom a)) ∧
          (∀ p : R, β.hom (koszulTateFullCoefficient f N p) =
              algebraMap R (ExteriorAlgebra R (Fin r → R)) p) ∧
            ∀ i : Fin r, β.hom (koszulTateFullVariable f N ⟨0, ULift.up i⟩) =
              koszulPowerTransitionHom f N n (exteriorGen R r i) := by
  classical
  have hex : ∀ a : ℕ, ∃ b : ℕ, a ≤ b ∧ ∀ j, 1 ≤ a → KillsKoszulHomology f a b j := by
    intro a
    by_cases ha : 1 ≤ a
    · obtain ⟨b, hab, hb⟩ := kills a ha
      exact ⟨b, hab.le, fun j _ => hb j⟩
    · exact ⟨a, le_rfl, fun _ h => absurd h ha⟩
  obtain ⟨m, hm0, hmono, hchain⟩ :=
    exists_monotone_chain (fun a b j => 1 ≤ a → KillsKoszulHomology f a b j) n r hex
  have hmmono : Monotone m := monotone_nat_of_le_succ hmono
  have hmpos : ∀ i, 1 ≤ m i := fun i => one_le.trans (hm0.symm.trans_le (hmmono i.zero_le))
  refine ⟨m r, hm0.symm.trans_le (hmmono r.zero_le), ?_⟩
  set N := m r
  set A₀ := koszulTateBase f N
  set ee : ℕ → ℕ := fun k => m (r - (k - 1))
  have hee1 : ee 1 = N := rfl
  have heesucc : ∀ k, ee (k + 1) = m (r - k) := fun _ => rfl
  have heeanti : ∀ k, ee (k + 1) ≤ ee k := fun k => hmmono (by omega)
  have heen : ∀ k, n ≤ ee k := fun _ => hm0.symm.trans_le (hmmono (Nat.zero_le _))
  have hkk : ∀ k : ℕ, KillsKoszulHomology f (ee (k + 2)) (ee (k + 1)) k := by
    intro k
    by_cases hk : k < r
    · rw [heesucc, heesucc]
      exact (show r - (k + 1) + 1 = r - k by omega) ▸ hchain (r - (k + 1)) (by omega) k (hmpos _)
    · have h1 : ee (k + 1) = n := by rw [heesucc, show r - k = 0 by omega, hm0]
      have h2 : ee (k + 2) = n := by rw [heesucc, show r - (k + 1) = 0 by omega, hm0]
      rw [h1, h2]
      exact killsKoszulHomology_of_lt f n n (by omega)
  -- the morphism out of the base: the structure map of the Koszul algebra
  have hbase : ∀ p : (tateAlgebra A₀ 0).carrier,
      Algebra.ofId R (ExteriorAlgebra R (Fin r → R)) p ∈
        (koszulGradedDPAlgebra R r).grade 0 :=
    fun p => SetLike.algebraMap_mem_graded (exteriorGrade R (Fin r → R)) p
  set G0 : GradedDPHom (tateAlgebra A₀ 0) (koszulGradedDPAlgebra R r) :=
    degreeZeroDPHom R R (koszulGradedDPAlgebra R r)
      (Algebra.ofId R (ExteriorAlgebra R (Fin r → R))) hbase
  have hG0val : ∀ p : R, G0.hom p = algebraMap R (ExteriorAlgebra R (Fin r → R)) p :=
    fun _ => rfl
  have hG0d : ∀ (e : ℕ) (a : (tateAlgebra A₀ 0).carrier),
      G0.hom (tateDifferential A₀ 0 a) = koszulPowerDifferential f e (G0.hom a) := by
    intro e a
    have hR : koszulPowerDifferential f e (G0.hom a) = 0 :=
      IsDifferentialGradedAlgebra.d_grade_zero
        (self := isDifferentialGradedAlgebra_koszulPowerDifferential f e) (hbase a)
    rw [show tateDifferential A₀ 0 a = 0 from rfl, hR]
    exact _root_.map_zero G0.hom
  -- the first step: the degree-one variables go to the Koszul generators
  have hcomp : ∀ {k a b : ℕ} (G : GradedDPHom (tateAlgebra A₀ k) (koszulGradedDPAlgebra R r)),
      b ≤ a → (∀ x, G.hom (tateDifferential A₀ k x) = koszulPowerDifferential f a (G.hom x)) →
      ∀ x, ((koszulTransitionDPHom f a b).comp G).hom (tateDifferential A₀ k x) =
        koszulPowerDifferential f b (((koszulTransitionDPHom f a b).comp G).hom x) := by
    intro k a b G hba hG x
    change koszulPowerTransitionHom f a b (G.hom (tateDifferential A₀ k x)) =
      koszulPowerDifferential f b (koszulPowerTransitionHom f a b (G.hom x))
    rw [hG x]
    exact koszulPowerTransitionHom_differential f hba (G.hom x)
  have hdt0 : ∀ j : tateIndex A₀ 0,
      koszulPowerDifferential f (ee 1) (exteriorGen R r j.down) =
        ((koszulTransitionDPHom f (ee 0) (ee 1)).comp G0).hom (tateCycle A₀ 0 j) := by
    intro j
    show _ = koszulPowerTransitionHom f (ee 0) (ee 1) (G0.hom (f j.down ^ N))
    rw [hG0val, AlgHom.commutes, hee1, koszulPowerDifferential_exteriorGen]
  obtain ⟨G1, hG1res, hG1gen, hG1d⟩ :=
    tateStep_exists_gradedDPHom_comm_differential A₀ 0 (koszulGradedDPAlgebra R r)
      (koszulPowerDifferential f (ee 1))
      (isDifferentialGradedAlgebra_koszulPowerDifferential f (ee 1))
      (isCompatibleWithDifferential_koszulPowerDifferential f (ee 1))
      ((koszulTransitionDPHom f (ee 0) (ee 1)).comp G0)
      (hcomp G0 (heeanti 0) (hG0d (ee 0)))
      (fun j => exteriorGen R r j.down) (fun j => exteriorGen_mem R r j.down) hdt0
  -- the inductive step
  have hstep : ∀ (k : ℕ)
      (G : GradedDPHom (tateAlgebra A₀ (k + 1)) (koszulGradedDPAlgebra R r)),
      (∀ a, G.hom (tateDifferential A₀ (k + 1) a) =
        koszulPowerDifferential f (ee (k + 1)) (G.hom a)) →
      ∃ G' : GradedDPHom (tateAlgebra A₀ (k + 2)) (koszulGradedDPAlgebra R r),
        (∀ a, G'.hom (tateDifferential A₀ (k + 2) a) =
            koszulPowerDifferential f (ee (k + 2)) (G'.hom a)) ∧
          ∀ x, G'.hom ((tateStep A₀ (k + 1)).hom x) =
            koszulPowerTransitionHom f (ee (k + 1)) (ee (k + 2)) (G.hom x) := by
    intro k G hG
    have hvals : ∀ j : tateIndex A₀ (k + 1),
        ∃ t : ExteriorAlgebra R (Fin r → R), t ∈ (koszulGradedDPAlgebra R r).grade (k + 2) ∧
          koszulPowerDifferential f (ee (k + 2)) t =
            ((koszulTransitionDPHom f (ee (k + 1)) (ee (k + 2))).comp G).hom
              (tateCycle A₀ (k + 1) j) := by
      intro j
      have hz : G.hom (tateDifferential A₀ (k + 1)
          (tateCycle A₀ (k + 1) j)) = 0 := by
        rw [tateCycle_cycle A₀ (k + 1) j]
        exact _root_.map_zero G.hom
      exact hkk k _ (G.map_grade (k + 1) _ (tateCycle_mem A₀ (k + 1) j))
        ((hG (tateCycle A₀ (k + 1) j)).symm.trans hz)
    choose t ht hdt using hvals
    obtain ⟨G', hG'res, -, hG'd⟩ :=
      tateStep_exists_gradedDPHom_comm_differential A₀ (k + 1) (koszulGradedDPAlgebra R r)
        (koszulPowerDifferential f (ee (k + 2)))
        (isDifferentialGradedAlgebra_koszulPowerDifferential f (ee (k + 2)))
        (isCompatibleWithDifferential_koszulPowerDifferential f (ee (k + 2)))
        ((koszulTransitionDPHom f (ee (k + 1)) (ee (k + 2))).comp G)
        (hcomp G (heeanti (k + 1)) hG) t ht hdt
    exact ⟨G', hG'd, hG'res⟩
  -- iterate the step
  let Seq : (k : ℕ) → {G : GradedDPHom (tateAlgebra A₀ (k + 1)) (koszulGradedDPAlgebra R r) //
      ∀ a, G.hom (tateDifferential A₀ (k + 1) a) =
        koszulPowerDifferential f (ee (k + 1)) (G.hom a)} := fun k =>
    Nat.rec (motive := fun k =>
        {G : GradedDPHom (tateAlgebra A₀ (k + 1)) (koszulGradedDPAlgebra R r) //
        ∀ a, G.hom (tateDifferential A₀ (k + 1) a) =
          koszulPowerDifferential f (ee (k + 1)) (G.hom a)})
      ⟨G1, hG1d⟩ (fun k p => ⟨(hstep k p.1 p.2).choose, (hstep k p.1 p.2).choose_spec.1⟩) k
  let G : (k : ℕ) → GradedDPHom (tateAlgebra A₀ k) (koszulGradedDPAlgebra R r) := fun k =>
    Nat.rec (motive := fun k => GradedDPHom (tateAlgebra A₀ k) (koszulGradedDPAlgebra R r))
      G0 (fun k _ => (Seq k).1) k
  have hGd : ∀ (k : ℕ) (a : (tateAlgebra A₀ k).carrier),
      (G k).hom (tateDifferential A₀ k a) =
        koszulPowerDifferential f (ee k) ((G k).hom a) := by
    intro k
    match k with
    | 0 => exact hG0d (ee 0)
    | k + 1 => exact (Seq k).2
  have hGres : ∀ (k : ℕ) (x : (tateAlgebra A₀ k).carrier),
      (G (k + 1)).hom ((tateStep A₀ k).hom x) =
        koszulPowerTransitionHom f (ee k) (ee (k + 1)) ((G k).hom x) := by
    intro k
    match k with
    | 0 => exact hG1res
    | k + 1 => exact (hstep k (Seq k).1 (Seq k).2).choose_spec.2
  -- pass to the colimit
  let H : (k : ℕ) → GradedDPHom (tateAlgebra A₀ k) (koszulGradedDPAlgebra R r) := fun k =>
    (koszulTransitionDPHom f (ee k) n).comp (G k)
  have hHstep : ∀ (k : ℕ) (x : (tateAlgebra A₀ k).carrier),
      (H (k + 1)).hom ((tateStep A₀ k).hom x) = (H k).hom x := fun k x =>
    (DFunLike.congr_arg (koszulPowerTransitionHom f (ee (k + 1)) n) (hGres k x)).trans
      (koszulPowerTransitionHom_comp f (heen (k + 1)) (heeanti k) ((G k).hom x))
  have hHd : ∀ (k : ℕ) (a : (tateAlgebra A₀ k).carrier),
      (H k).hom (tateDifferential A₀ k a) = koszulPowerDifferential f n ((H k).hom a) :=
    fun k => hcomp (G k) (heen k) (hGd k)
  obtain ⟨F, hFres, hFd⟩ := tateColimit_exists_gradedDPHom_of_family A₀
    (koszulGradedDPAlgebra R r)
    (koszulPowerDifferential f n) H hHstep hHd
  refine ⟨F, hFd, fun p => ?_, fun i => ?_⟩
  · refine (hFres 0 p).trans ?_
    show koszulPowerTransitionHom f (ee 0) n (G0.hom p) = _
    rw [hG0val, AlgHom.commutes]
  · rw [koszulTateFullVariable, tateVariable, hFres 1 (tateGenerator A₀ 0 (ULift.up i))]
    show koszulPowerTransitionHom f (ee 1) n ((G 1).hom (tateGenerator A₀ 0 (ULift.up i)))
      = _
    rw [show (G 1).hom (tateGenerator A₀ 0 (ULift.up i)) = exteriorGen R r i from
      hG1gen (ULift.up i), hee1]

end Comparison

section Main

variable {R : Type u} [CommRing R] {r : ℕ}

/-- **Tag 0GZ4, when the transition maps eventually kill the Koszul homology.** Let `R` be a ring
and `f₁, …, f_r ∈ R`. Write `K_m` for the Koszul divided power algebra `R⟨ξ₁, …, ξ_r⟩` with `ξᵢ`
of degree one and `d(ξᵢ) = fᵢ^m`, and `K_M → K_m` for the transition map `ξᵢ ↦ fᵢ^(M-m) ξᵢ`.
Suppose that for every `a ≥ 1` some transition map `K_b → K_a` with `b > a` sends every cycle of
positive degree to a boundary. Then for every `n ≥ 1` there is an `N ≥ n` and maps
`K_N → A → R/(f₁^N, …, f_r^N)` and `A → K_n` such that `(A, d, γ)` is a divided power
differential graded algebra as in Definition 09PJ, `A → R/(f₁^N, …, f_r^N)` is a
quasi-isomorphism, the composition `K_N → A → R/(f₁^N, …, f_r^N)` is the canonical map, the
composition `K_N → A → K_n` is the transition map, `A₀ = R → R/(f₁^N, …, f_r^N)` is the canonical
surjection, `A` is a graded divided power polynomial algebra over `R`, and `A → K_n` is a
homomorphism of differential graded `R`-algebras compatible with divided powers inducing the
canonical map `R/(f₁^N, …, f_r^N) → R/(f₁^n, …, f_r^n)` on homology in degree zero. -/
public theorem exists_tateResolution_koszulPowers_of_killsKoszulHomology (f : Fin r → R)
    (kills : ∀ a : ℕ, 1 ≤ a → ∃ b : ℕ, a < b ∧ ∀ j : ℕ, KillsKoszulHomology f a b j)
    {n : ℕ} (one_le : 1 ≤ n) :
    ∃ (N : ℕ) (hN : n ≤ N) (A : GradedDPAlgebra.{u, u} R) (d : A.carrier →ₗ[R] A.carrier)
        (ι : R →ₐ[R] A.carrier) (ε : A.carrier →ₐ[R] R ⧸ koszulPowerIdeal f N)
        (α : ExteriorAlgebra R (Fin r → R) →ₐ[R] A.carrier)
        (β : A.carrier →ₐ[R] ExteriorAlgebra R (Fin r → R)),
      -- (1) `(A, d, γ)` is as in Definition 09PJ
      IsDifferentialGradedAlgebra A.grade d ∧ IsCompatibleWithDifferential A.gamma d ∧
      -- (6) a graded divided power polynomial algebra over `R`
      Nonempty (GradedDividedPowerPolynomial A.grade A.gamma ι) ∧
      -- (5) `A₀ = R`, and `A₀ → R/(f₁^N, …, f_r^N)` is the canonical surjection
      Function.Injective ι ∧
      (∀ a : A.carrier, a ∈ A.grade 0 ↔ ∃ c : R, ι c = a) ∧
      (∀ c : R, ε (ι c) = Ideal.Quotient.mk (koszulPowerIdeal f N) c) ∧
      -- (2) `ε` is a quasi-isomorphism onto `R/(f₁^N, …, f_r^N)`
      Function.Surjective ε ∧
      (∀ (k : ℕ) (a : A.carrier), 0 < k → a ∈ A.grade k → ε a = 0) ∧
      (∀ a : A.carrier, ε (d a) = 0) ∧
      (∀ a : A.carrier, a ∈ A.grade 0 → ε a = 0 → ∃ b ∈ A.grade 1, d b = a) ∧
      (∀ (k : ℕ) (a : A.carrier), a ∈ A.grade (k + 1) → d a = 0 →
        ∃ b ∈ A.grade (k + 2), d b = a) ∧
      -- `α : K_N → A` is a morphism of differential graded divided power algebras
      (∀ (k : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
        x ∈ exteriorGrade R (Fin r → R) k → α x ∈ A.grade k) ∧
      (∀ x, α (koszulPowerDifferential f N x) = d (α x)) ∧
      (∀ (k : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
        x ∈ positiveEvenPart (exteriorGrade R (Fin r → R)) →
          α ((exteriorDividedPowerStructure R r).dpow k x) = A.gamma.dpow k (α x)) ∧
      -- (7) `β : A → K_n` is a morphism of differential graded divided power algebras
      (∀ (k : ℕ) (a : A.carrier), a ∈ A.grade k → β a ∈ exteriorGrade R (Fin r → R) k) ∧
      (∀ a, β (d a) = koszulPowerDifferential f n (β a)) ∧
      (∀ (k : ℕ) (a : A.carrier), a ∈ positiveEvenPart A.grade →
        β (A.gamma.dpow k a) = (exteriorDividedPowerStructure R r).dpow k (β a)) ∧
      -- (3) the composition `K_N → A → R/(f₁^N, …, f_r^N)` is the canonical map
      (∀ x, ε (α x) = koszulPowerAugmentation f N x) ∧
      -- (4) the composition `K_N → A → K_n` is the transition map
      (∀ x, β (α x) = koszulPowerTransitionHom f N n x) ∧
      -- (7) `β` is the identity of `R` in degree zero, hence induces the canonical map
      -- `R/(f₁^N, …, f_r^N) → R/(f₁^n, …, f_r^n)` on homology in degree zero
      (∀ c : R, β (ι c) = algebraMap R (ExteriorAlgebra R (Fin r → R)) c) ∧
      (∀ a : A.carrier, a ∈ A.grade 0 →
        koszulPowerAugmentation f n (β a) =
          Ideal.Quotient.factor (koszulPowerIdeal_le_of_le f hN) (ε a)) := by
  obtain ⟨N, hnN, β, hβd, hβcoeff, hβvar⟩ := exists_koszulTateFullBeta f kills one_le
  obtain ⟨α, hαgen, hαgrade, hαd, hαdpow⟩ := exists_koszulTateFullAlpha f N
  refine ⟨N, hnN, koszulTateFullAlgebra f N, koszulTateFullDifferential f N,
    koszulTateFullCoefficient f N,
    (koszulTateFullAugmentation f N).hom, α, β.hom,
    tateColimitDga (koszulTateBase f N), tateColimitCompatible (koszulTateBase f N),
    ⟨koszulTateFullPolynomial f N⟩,
    koszulTateFullCoefficient_injective f N,
    mem_koszulTateFullAlgebra_grade_zero_iff f N, koszulTateFullAugmentation_coefficient f N, ?_,
    fun k a hk ha => koszulTateFullAugmentation_positive f N (by omega) ha,
    koszulTateFullAugmentation_differential f N,
    fun a ha haug => exists_koszulTateFullDifferential_boundary_of_grade_zero f N ha haug,
    fun k a ha hda => exists_koszulTateFullDifferential_boundary_of_cycle f N k ha hda,
    hαgrade, hαd, hαdpow, β.map_grade, hβd, fun k a ha => (β.map_dpow k a ha).symm,
    ?_, ?_, hβcoeff, ?_⟩
  · intro z
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨koszulTateFullCoefficient f N c, (koszulTateFullAugmentation_coefficient f N c).trans hc⟩
  · have hcomp : (koszulTateFullAugmentation f N).hom.comp α = koszulPowerAugmentation f N := by
      refine ExteriorAlgebra.hom_ext (LinearMap.ext fun p => ?_)
      show (koszulTateFullAugmentation f N).hom (α (ExteriorAlgebra.ι R p)) =
        koszulPowerAugmentation f N (ExteriorAlgebra.ι R p)
      rw [koszulPowerAugmentation_ι, ι_eq_sum_exteriorGen, map_sum, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_mul, map_mul, hαgen i,
        koszulTateFullAugmentation_variable f N ⟨0, ULift.up i⟩, mul_zero]
    exact AlgHom.congr_fun hcomp
  · have hcomp : β.hom.comp α = koszulPowerTransitionHom f N n := by
      refine ExteriorAlgebra.hom_ext (LinearMap.ext fun p => ?_)
      show β.hom (α (ExteriorAlgebra.ι R p)) =
        koszulPowerTransitionHom f N n (ExteriorAlgebra.ι R p)
      rw [ι_eq_sum_exteriorGen, map_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, map_mul, hαgen i, hβvar i, AlgHom.commutes, AlgHom.commutes]
      congr 1
      exact ((koszulPowerTransitionHom f N n).commutes (p i)).symm
    exact AlgHom.congr_fun hcomp
  · intro a ha
    obtain ⟨c, rfl⟩ := (mem_koszulTateFullAlgebra_grade_zero_iff f N a).1 ha
    refine Eq.trans (congrArg (koszulPowerAugmentation f n) (hβcoeff c)) ?_
    refine Eq.trans (koszulPowerAugmentation_algebraMap f n c) ?_
    refine Eq.trans (Ideal.Quotient.factor_mk (koszulPowerIdeal_le_of_le f hnN) c).symm ?_
    exact congrArg (Ideal.Quotient.factor (koszulPowerIdeal_le_of_le f hnN))
      (koszulTateFullAugmentation_coefficient f N c).symm

/-- **Tag 0GZ4 for a weakly proregular sequence.** Let `R` be a ring and let `f₁, …, f_r ∈ R` be
weakly proregular (Stacks 0H1E). Then for every `n ≥ 1` there is an `N ≥ n` and a divided power
differential graded algebra `A`, a graded divided power polynomial algebra over `R` resolving
`R/(f₁^N, …, f_r^N)`, with maps `K_N → A → R/(f₁^N, …, f_r^N)` and `A → K_n` as in
`DividedPowers.TateResolution.exists_tateResolution_koszulPowers_of_killsKoszulHomology`: weak
proregularity is exactly the vanishing of the transition maps on Koszul homology that it needs,
by `Koszul.isWeaklyProregular_iff_killsKoszulHomology`. -/
public theorem exists_tateResolution_koszulPowers_of_isWeaklyProregular (f : Fin r → R)
    (proregular : Koszul.IsWeaklyProregular f) {n : ℕ} (one_le : 1 ≤ n) :
    ∃ (N : ℕ) (hN : n ≤ N) (A : GradedDPAlgebra.{u, u} R) (d : A.carrier →ₗ[R] A.carrier)
        (ι : R →ₐ[R] A.carrier) (ε : A.carrier →ₐ[R] R ⧸ koszulPowerIdeal f N)
        (α : ExteriorAlgebra R (Fin r → R) →ₐ[R] A.carrier)
        (β : A.carrier →ₐ[R] ExteriorAlgebra R (Fin r → R)),
      -- (1) `(A, d, γ)` is as in Definition 09PJ
      IsDifferentialGradedAlgebra A.grade d ∧ IsCompatibleWithDifferential A.gamma d ∧
      -- (6) a graded divided power polynomial algebra over `R`
      Nonempty (GradedDividedPowerPolynomial A.grade A.gamma ι) ∧
      -- (5) `A₀ = R`, and `A₀ → R/(f₁^N, …, f_r^N)` is the canonical surjection
      Function.Injective ι ∧
      (∀ a : A.carrier, a ∈ A.grade 0 ↔ ∃ c : R, ι c = a) ∧
      (∀ c : R, ε (ι c) = Ideal.Quotient.mk (koszulPowerIdeal f N) c) ∧
      -- (2) `ε` is a quasi-isomorphism onto `R/(f₁^N, …, f_r^N)`
      Function.Surjective ε ∧
      (∀ (k : ℕ) (a : A.carrier), 0 < k → a ∈ A.grade k → ε a = 0) ∧
      (∀ a : A.carrier, ε (d a) = 0) ∧
      (∀ a : A.carrier, a ∈ A.grade 0 → ε a = 0 → ∃ b ∈ A.grade 1, d b = a) ∧
      (∀ (k : ℕ) (a : A.carrier), a ∈ A.grade (k + 1) → d a = 0 →
        ∃ b ∈ A.grade (k + 2), d b = a) ∧
      -- `α : K_N → A` is a morphism of differential graded divided power algebras
      (∀ (k : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
        x ∈ exteriorGrade R (Fin r → R) k → α x ∈ A.grade k) ∧
      (∀ x, α (koszulPowerDifferential f N x) = d (α x)) ∧
      (∀ (k : ℕ) (x : ExteriorAlgebra R (Fin r → R)),
        x ∈ positiveEvenPart (exteriorGrade R (Fin r → R)) →
          α ((exteriorDividedPowerStructure R r).dpow k x) = A.gamma.dpow k (α x)) ∧
      -- (7) `β : A → K_n` is a morphism of differential graded divided power algebras
      (∀ (k : ℕ) (a : A.carrier), a ∈ A.grade k → β a ∈ exteriorGrade R (Fin r → R) k) ∧
      (∀ a, β (d a) = koszulPowerDifferential f n (β a)) ∧
      (∀ (k : ℕ) (a : A.carrier), a ∈ positiveEvenPart A.grade →
        β (A.gamma.dpow k a) = (exteriorDividedPowerStructure R r).dpow k (β a)) ∧
      -- (3) the composition `K_N → A → R/(f₁^N, …, f_r^N)` is the canonical map
      (∀ x, ε (α x) = koszulPowerAugmentation f N x) ∧
      -- (4) the composition `K_N → A → K_n` is the transition map
      (∀ x, β (α x) = koszulPowerTransitionHom f N n x) ∧
      -- (7) `β` is the identity of `R` in degree zero, hence induces the canonical map
      -- `R/(f₁^N, …, f_r^N) → R/(f₁^n, …, f_r^n)` on homology in degree zero
      (∀ c : R, β (ι c) = algebraMap R (ExteriorAlgebra R (Fin r → R)) c) ∧
      (∀ a : A.carrier, a ∈ A.grade 0 →
        koszulPowerAugmentation f n (β a) =
          Ideal.Quotient.factor (koszulPowerIdeal_le_of_le f hN) (ε a)) :=
  exists_tateResolution_koszulPowers_of_killsKoszulHomology f
    ((Koszul.isWeaklyProregular_iff_killsKoszulHomology f).1 proregular) one_le

end Main

end DividedPowers.TateResolution

end
