module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.GradedBasis
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SquareZeroLiftData

/-! # The comparison map of the square-zero lift, stage by stage and degree by degree

`StacksFrontier/RingTheory/DividedPowers/TateResolution/SquareZeroLiftData.lean` builds the algebra
`B` lifting a graded divided power polynomial algebra `A` along a surjection `q : R' → R`, as the
colimit of an `ω`-tower, and the comparison map `π : B → A`, and proves `π` surjective. This file
refines that surjectivity in two directions at once, which is what the construction of the lifted
differential needs.

The lifted differential is built by induction along the tower: extending it across the step from
the `n`-th stage to the next requires a prescribed value for each variable of degree `n + 1`,
namely an element of the `n`-th stage, homogeneous of degree `n`, lifting the differential of that
variable. Such an element exists because `π` restricted to the `n`-th stage is already onto the
degree-`n` part `𝒜 n` of `A` — variables of degree greater than `n` cannot occur in a monomial of
degree `n`, so nothing beyond the `n`-th stage is needed.

## Main definitions

* `DividedPowers.TateResolution.liftTowerInclusion` — the morphism from a stage of the tower into
  the lifted algebra.
* `DividedPowers.TateResolution.liftStageRingHom` — the comparison map restricted to a stage,
  as a ring homomorphism to `A`.

## Main results

* `DividedPowers.TateResolution.exists_mem_grade_liftStage` — the degreewise refinement of
  `DividedPowers.TateResolution.liftHom_surjective`: every element of `𝒜 n` is the image, under
  the comparison map, of an element of the `n`-th stage of the tower which is homogeneous of
  degree `n`.
* `DividedPowers.TateResolution.liftStageRingHom_range_grade` — the surjectivity half of that
  statement, before the degree is arranged.
* `DividedPowers.TateResolution.liftStageRingHom_step`,
  `DividedPowers.TateResolution.liftStageRingHom_chainMap` and
  `DividedPowers.TateResolution.liftStageRingHom_dpow` — the comparison map is compatible with
  the transition morphisms of the tower and with the divided powers.
* `DividedPowers.TateResolution.exists_stage_pair_mem_grade` — two homogeneous elements of the
  lifted algebra come from homogeneous elements of a common stage, which is what lets the Leibniz
  rule be checked one stage at a time.
* `DividedPowers.TateResolution.exists_mem_grade_of_mem_range` — a degree-preserving ring
  homomorphism whose range contains a homogeneous element contains a homogeneous preimage of it of
  the same degree, and `DividedPowers.TateResolution.mem_positiveEvenPart_of_ringHom` — such a map
  carries the positive even part into the positive even part.

## Implementation notes

That `π` restricted to the `n`-th stage is onto `𝒜 n` is proved from the monomial basis of
`StacksFrontier/RingTheory/DividedPowers/TateResolution/GradedBasis.lean`. An element of `𝒜 n`
expands as a combination of divided power monomials of weight `n`, and every variable in the
support of such a monomial has degree at most `n`; the divided powers of a variable of degree at
most `n` lie in the range of the `n`-th stage, because the variable itself is adjoined at the
stage of its degree and the transition morphisms of the tower preserve divided powers. The range
being a subring, the whole combination lies in it. The degree is then arranged afterwards, by
taking the degree-`n` component of any preimage: the comparison map preserves degrees, so it
carries that component to the degree-`n` component of the original, which is the original.

The divided powers of a variable of *odd* degree need no transport: the `k`-th divided power of
such a variable is its `k`-th power, which is in the range because the range is a subring.

## References

* [Stacks Project, Tag 09PN](https://stacks.math.columbia.edu/tag/09PN)
* [Stacks Project, Tag 09PS](https://stacks.math.columbia.edu/tag/09PS)
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w z

attribute [local instance] GradedDPAlgebra.ring GradedDPAlgebra.algebra
  GradedDPAlgebra.graded GradedDPAlgebra.strict

attribute [local instance] gradedLimitGradedAlgebra gradedLimitStrictlyGradedComm

section Homogeneous

variable {R₁ : Type*} {R₂ : Type*} {A₁ : Type*} {A₂ : Type*}
  [CommRing R₁] [CommRing R₂] [Ring A₁] [Ring A₂] [Algebra R₁ A₁] [Algebra R₂ A₂]
  (𝒜₁ : ℕ → Submodule R₁ A₁) [GradedAlgebra 𝒜₁] (𝒜₂ : ℕ → Submodule R₂ A₂) [GradedAlgebra 𝒜₂]

/-- A degree-preserving ring homomorphism commutes with taking a homogeneous component. The two
gradings may be over different ground rings: only additivity of the map is used. -/
public theorem gradedPart_ringHom (φ : A₁ →+* A₂)
    (hφ : ∀ (m : ℕ) (b : A₁), b ∈ 𝒜₁ m → φ b ∈ 𝒜₂ m) (b : A₁) (m : ℕ) :
    gradedPart 𝒜₂ (φ b) m = φ (gradedPart 𝒜₁ b m) := by
  induction b using DirectSum.Decomposition.inductionOn 𝒜₁ with
  | zero => rw [map_zero, gradedPart_zero, gradedPart_zero, map_zero]
  | @homogeneous i b =>
      rcases eq_or_ne i m with rfl | him
      · rw [gradedPart_of_mem_same 𝒜₁ b.2, gradedPart_of_mem_same 𝒜₂ (hφ i b b.2)]
      · rw [gradedPart_of_mem_ne 𝒜₁ b.2 him, gradedPart_of_mem_ne 𝒜₂ (hφ i b b.2) him, map_zero]
  | add b c hb hc => rw [map_add, gradedPart_add, gradedPart_add, hb, hc, map_add]

/-- A degree-preserving ring homomorphism is surjective in each degree onto the part of its range
in that degree: a homogeneous element of the range of degree `n` is the image of a homogeneous
element of degree `n`, namely of the degree-`n` component of any preimage. -/
public theorem exists_mem_grade_of_mem_range (φ : A₁ →+* A₂)
    (hφ : ∀ (m : ℕ) (b : A₁), b ∈ 𝒜₁ m → φ b ∈ 𝒜₂ m) (n : ℕ) {x : A₂} (hx : x ∈ 𝒜₂ n)
    (hxr : x ∈ φ.range) : ∃ b : A₁, b ∈ 𝒜₁ n ∧ φ b = x := by
  obtain ⟨b, rfl⟩ := hxr
  refine ⟨gradedPart 𝒜₁ b n, gradedPart_mem 𝒜₁ b n, ?_⟩
  rw [← gradedPart_ringHom 𝒜₁ 𝒜₂ φ hφ b n, gradedPart_of_mem_same 𝒜₂ hx]

omit [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂] in
/-- A degree-preserving ring homomorphism carries the positive even part into the positive even
part. -/
public theorem mem_positiveEvenPart_of_ringHom (φ : A₁ →+* A₂)
    (hφ : ∀ (m : ℕ) (b : A₁), b ∈ 𝒜₁ m → φ b ∈ 𝒜₂ m) {z : A₁}
    (hz : z ∈ positiveEvenPart 𝒜₁) : φ z ∈ positiveEvenPart 𝒜₂ := by
  induction hz using Submodule.iSup_induction' with
  | mem k x hx => exact Submodule.mem_iSup_of_mem k (hφ _ x hx)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy

end Homogeneous

section Stage

variable {R' : Type u} {R : Type v} {A : Type w} {σ : Type z}
  [CommRing R'] [CommRing R] [Ring A] [Algebra R A]
  (q : R' →+* R) {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] [IsStrictlyGradedComm 𝒜]
  {γ : DividedPowerStructure 𝒜} {ι : MvPolynomial σ R →ₐ[R] A}
  (hpoly : GradedDividedPowerPolynomial 𝒜 γ ι)

/-- The morphism from the `n`-th stage of the tower lifting `A` into the lifted algebra. -/
public noncomputable abbrev liftTowerInclusion (n : ℕ) :
    GradedDPHom (liftTowerStage (R' := R') hpoly n) (liftAlgebra (R' := R') hpoly) :=
  towerInclusion.{u, max v w z, w} (liftBase R' σ R A) (liftIndex hpoly) n

/-- The comparison morphism of the lift, restricted to the `n`-th stage of the tower: a ring
homomorphism from that stage to `A`. -/
public noncomputable def liftStageRingHom (n : ℕ) :
    (liftTowerStage (R' := R') hpoly n).carrier →+* A :=
  (liftRingHom q hpoly).comp (liftTowerInclusion (R' := R') hpoly n).hom.toRingHom

/-- The comparison morphism on a stage is the comparison morphism after the inclusion of that
stage. -/
public theorem liftStageRingHom_apply (n : ℕ)
    (y : (liftTowerStage (R' := R') hpoly n).carrier) :
    liftStageRingHom q hpoly n y =
      liftRingHom q hpoly ((liftTowerInclusion (R' := R') hpoly n).hom y) := rfl

/-- The comparison morphism on a stage preserves homogeneous degrees. -/
public theorem liftStageRingHom_mem_grade (n m : ℕ)
    (y : (liftTowerStage (R' := R') hpoly n).carrier)
    (hy : y ∈ (liftTowerStage (R' := R') hpoly n).grade m) :
    liftStageRingHom q hpoly n y ∈ 𝒜 m :=
  liftHom_mem_grade q hpoly m _ ((liftTowerInclusion (R' := R') hpoly n).map_grade m y hy)

/-- The comparison morphisms on the stages are compatible with the transition morphisms of the
tower. -/
public theorem liftStageRingHom_chainMap {n k : ℕ} (h : n ≤ k)
    (y : (liftTowerStage (R' := R') hpoly n).carrier) :
    liftStageRingHom q hpoly k
        ((chainMap (liftTowerStage (R' := R') hpoly) (liftTowerStep (R' := R') hpoly) h).hom y) =
      liftStageRingHom q hpoly n y := by
  rw [liftStageRingHom_apply, liftStageRingHom_apply]
  exact congrArg (liftRingHom q hpoly)
    (chainColimitInclusion_chainMap (liftTowerStage (R' := R') hpoly)
      (liftTowerStep (R' := R') hpoly) h y)

/-- The comparison morphisms on the stages are compatible with the steps of the tower. -/
public theorem liftStageRingHom_step (n : ℕ) (y : (liftTowerStage (R' := R') hpoly n).carrier) :
    liftStageRingHom q hpoly (n + 1) ((liftTowerStep (R' := R') hpoly n).hom y) =
      liftStageRingHom q hpoly n y := by
  rw [liftStageRingHom_apply, liftStageRingHom_apply]
  exact congrArg (liftRingHom q hpoly)
    (chainColimitInclusion_step (liftTowerStage (R' := R') hpoly)
      (liftTowerStep (R' := R') hpoly) n y)

/-- The comparison morphism on a stage is a morphism of divided powers. -/
public theorem liftStageRingHom_dpow (n m : ℕ) (z : (liftTowerStage (R' := R') hpoly n).carrier)
    (hz : z ∈ positiveEvenPart (liftTowerStage (R' := R') hpoly n).grade) :
    liftStageRingHom q hpoly n ((liftTowerStage (R' := R') hpoly n).gamma.dpow m z) =
      γ.dpow m (liftStageRingHom q hpoly n z) := by
  have hz' : (liftTowerInclusion (R' := R') hpoly n).hom z ∈
      positiveEvenPart (liftAlgebra (R' := R') hpoly).grade :=
    mem_positiveEvenPart_of_ringHom (liftTowerStage (R' := R') hpoly n).grade
      (liftAlgebra (R' := R') hpoly).grade (liftTowerInclusion (R' := R') hpoly n).hom.toRingHom
      (fun k b hb => (liftTowerInclusion (R' := R') hpoly n).map_grade k b hb) hz
  rw [liftStageRingHom_apply, liftStageRingHom_apply,
    ← chainColimitInclusion_dpow (liftTowerStage (R' := R') hpoly)
      (liftTowerStep (R' := R') hpoly) n m z hz,
    ← liftHom_dpow q hpoly m _ hz']

/-- Every element of the base of the tower is homogeneous of degree zero: the base is the
polynomial ring `R'[xᵢ]` placed in degree zero. -/
public theorem mem_liftTowerStage_zero_grade_zero
    (y : (liftTowerStage (R' := R') hpoly 0).carrier) :
    y ∈ (liftTowerStage (R' := R') hpoly 0).grade 0 :=
  mem_degreeZeroGrade_zero R' (ULift.{max u v w z} (MvPolynomial σ R')) y

/-- The range of the comparison morphism grows along the tower. -/
private theorem liftStageRingHom_mem_range_of_le {n k : ℕ} (h : n ≤ k) {x : A}
    (hx : x ∈ (liftStageRingHom q hpoly n).range) : x ∈ (liftStageRingHom q hpoly k).range := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(chainMap (liftTowerStage (R' := R') hpoly) (liftTowerStep (R' := R') hpoly) h).hom y,
    liftStageRingHom_chainMap q hpoly h y⟩

/-- The comparison morphism sends the generator of the `m`-th step to the matching variable. -/
private theorem liftStageRingHom_towerGenerator (m : ℕ) (j : hpoly.indices m) :
    liftStageRingHom q hpoly (m + 1) (liftTowerGenerator (R' := R') hpoly m (ULift.up j)) =
      hpoly.generator ⟨m, j⟩ :=
  liftRingHom_variable q hpoly m j

/-- The image of a coefficient of `A` reduced along `q` lies in the range of the comparison
morphism on any stage: a coefficient comes from the base of the tower. -/
public theorem liftStageRingHom_coefficient_mem_range (n : ℕ) (p : MvPolynomial σ R') :
    ι (MvPolynomial.map q p) ∈ (liftStageRingHom q hpoly n).range :=
  liftStageRingHom_mem_range_of_le q hpoly (Nat.zero_le n)
    ⟨(liftBaseEquiv R' σ R A).symm p, liftRingHom_coefficient q hpoly p⟩

/-- Every coefficient of `A` lies in the range of the comparison morphism on any stage, the
reduction of coefficients along a surjection being surjective. -/
public theorem liftStageRingHom_coeff_mem_range (hq : Function.Surjective q) (n : ℕ)
    (p : MvPolynomial σ R) : ι p ∈ (liftStageRingHom q hpoly n).range := by
  obtain ⟨p', rfl⟩ := MvPolynomial.map_surjective q hq p
  exact liftStageRingHom_coefficient_mem_range q hpoly n p'

/-- A variable of degree at most `n` lies in the range of the comparison morphism on the `n`-th
stage: it is adjoined at the stage of its degree, which the tower reaches by then. -/
public theorem liftStageRingHom_generator_mem_range {n m : ℕ} (hm : m < n)
    (j : hpoly.indices m) :
    hpoly.generator ⟨m, j⟩ ∈ (liftStageRingHom q hpoly n).range :=
  liftStageRingHom_mem_range_of_le q hpoly hm
    ⟨_, liftStageRingHom_towerGenerator q hpoly m j⟩

/-- Every divided power of a variable of even degree at most `n` lies in the range of the
comparison morphism on the `n`-th stage: the variable has a divided power at the stage of its
degree, and the comparison morphism carries it to the divided power of its image. -/
public theorem liftStageRingHom_dpow_generator_mem_range {n m : ℕ} (hm : m < n)
    (j : hpoly.indices m) (he : Even (m + 1)) (k : ℕ) :
    γ.dpow k (hpoly.generator ⟨m, j⟩) ∈ (liftStageRingHom q hpoly n).range := by
  obtain ⟨e, hepos, hek⟩ : ∃ e : ℕ, 0 < e ∧ m + 1 = 2 * e := by
    obtain ⟨e, he⟩ := he
    exact ⟨e, by omega, by omega⟩
  have hg : liftTowerGenerator (R' := R') hpoly m (ULift.up j) ∈
      positiveEvenPart (liftTowerStage (R' := R') hpoly (m + 1)).grade :=
    mem_positiveEvenPart_of_mem_grade _ hepos
      (hek ▸ towerGenerator_mem.{u, max v w z, w} (liftBase R' σ R A) (liftIndex hpoly) m
        (ULift.up j))
  refine liftStageRingHom_mem_range_of_le q hpoly hm
    ⟨(liftTowerStage (R' := R') hpoly (m + 1)).gamma.dpow k
      (liftTowerGenerator (R' := R') hpoly m (ULift.up j)), ?_⟩
  rw [liftStageRingHom_dpow q hpoly (m + 1) k _ hg, liftStageRingHom_towerGenerator]

/-- Every divided power of a variable of degree at most `n` lies in the range of the comparison
morphism on the `n`-th stage. For a variable of odd degree the divided power is an ordinary power,
which is in the range because the range is a subring. -/
public theorem liftStageRingHom_variablePower_mem_range {n : ℕ} (jv : hpoly.Variable)
    (hj : hpoly.varDegree jv ≤ n) (k : ℕ) :
    hpoly.variablePower jv k ∈ (liftStageRingHom q hpoly n).range := by
  obtain ⟨m, jm⟩ := jv
  have hm : m < n := by
    simp only [GradedDividedPowerPolynomial.varDegree] at hj
    omega
  rw [GradedDividedPowerPolynomial.variablePower]
  split_ifs with hodd
  · exact pow_mem (liftStageRingHom_generator_mem_range q hpoly hm jm) k
  · exact liftStageRingHom_dpow_generator_mem_range q hpoly hm jm
      (Nat.not_odd_iff_even.1 hodd) k

/-- Every divided power monomial of degree `n` lies in the range of the comparison morphism on the
`n`-th stage: each variable in its support has degree at most `n`. -/
public theorem liftStageRingHom_monomial_mem_range [LinearOrder hpoly.Variable]
    {n : ℕ} {ν : hpoly.Variable →₀ ℕ} (hν : hpoly.weight ν = n) :
    hpoly.monomial ν ∈ (liftStageRingHom q hpoly n).range := by
  rw [GradedDividedPowerPolynomial.monomial]
  refine list_prod_mem fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨jv, hjv, rfl⟩ := hx
  exact liftStageRingHom_variablePower_mem_range q hpoly jv
    (hν ▸ GradedDividedPowerPolynomial.varDegree_le_weight ((Finset.mem_sort _).1 hjv)) _

/-- The comparison morphism on the `n`-th stage is onto the degree-`n` part of `A`: an element of
`𝒜 n` expands as a combination of divided power monomials of degree `n`, and both the monomials
and the coefficients lie in the range. -/
public theorem liftStageRingHom_range_grade (hq : Function.Surjective q) (n : ℕ) {x : A}
    (hx : x ∈ 𝒜 n) : x ∈ (liftStageRingHom q hpoly n).range := by
  classical
  let _ : LinearOrder hpoly.Variable := IsWellOrder.linearOrder WellOrderingRel
  obtain ⟨c, hc, rfl⟩ := hpoly.exists_monomialSumMap_eq n hx
  rw [GradedDividedPowerPolynomial.monomialSumMap_apply]
  exact Subring.sum_mem _ fun ν hν => mul_mem
    (liftStageRingHom_monomial_mem_range q hpoly (hc ν hν).2)
    (liftStageRingHom_coeff_mem_range q hpoly hq n (c ν))

/-- Two homogeneous elements of the lifted algebra come from homogeneous elements of a common
stage of the tower, of the same degrees. -/
public theorem exists_stage_pair_mem_grade (i k : ℕ)
    {x y : (liftAlgebra (R' := R') hpoly).carrier}
    (hx : x ∈ (liftAlgebra (R' := R') hpoly).grade i)
    (hy : y ∈ (liftAlgebra (R' := R') hpoly).grade k) :
    ∃ (N : ℕ) (u v : (liftTowerStage (R' := R') hpoly N).carrier),
      u ∈ (liftTowerStage (R' := R') hpoly N).grade i ∧
        v ∈ (liftTowerStage (R' := R') hpoly N).grade k ∧
        (liftTowerInclusion (R' := R') hpoly N).hom u = x ∧
        (liftTowerInclusion (R' := R') hpoly N).hom v = y := by
  obtain ⟨n₁, u, hu, hux⟩ :=
    (chainColimit_mem_grade_iff (liftTowerStage (R' := R') hpoly)
      (liftTowerStep (R' := R') hpoly) i x).1 hx
  obtain ⟨n₂, v, hv, hvy⟩ :=
    (chainColimit_mem_grade_iff (liftTowerStage (R' := R') hpoly)
      (liftTowerStep (R' := R') hpoly) k y).1 hy
  refine ⟨max n₁ n₂,
    (chainMap (liftTowerStage (R' := R') hpoly) (liftTowerStep (R' := R') hpoly)
      (le_max_left n₁ n₂)).hom u,
    (chainMap (liftTowerStage (R' := R') hpoly) (liftTowerStep (R' := R') hpoly)
      (le_max_right n₁ n₂)).hom v,
    (chainMap (liftTowerStage (R' := R') hpoly) (liftTowerStep (R' := R') hpoly)
      (le_max_left n₁ n₂)).map_grade i u hu,
    (chainMap (liftTowerStage (R' := R') hpoly) (liftTowerStep (R' := R') hpoly)
      (le_max_right n₁ n₂)).map_grade k v hv, ?_, ?_⟩
  · rw [chainColimitInclusion_chainMap (liftTowerStage (R' := R') hpoly)
      (liftTowerStep (R' := R') hpoly) (le_max_left n₁ n₂) u]
    exact hux
  · rw [chainColimitInclusion_chainMap (liftTowerStage (R' := R') hpoly)
      (liftTowerStep (R' := R') hpoly) (le_max_right n₁ n₂) v]
    exact hvy

/-- The degreewise refinement of `DividedPowers.TateResolution.liftHom_surjective`: every element
of `𝒜 n` is the image under the comparison morphism of an element of the `n`-th stage of the
tower which is homogeneous of degree `n`.

This is what the inductive construction of the lifted differential consumes: extending the
differential across the variables of degree `n + 1` needs a value of degree `n` at the `n`-th
stage for each of them. -/
public theorem exists_mem_grade_liftStage (hq : Function.Surjective q) (n : ℕ) {x : A}
    (hx : x ∈ 𝒜 n) :
    ∃ y : (liftTowerStage (R' := R') hpoly n).carrier,
      y ∈ (liftTowerStage (R' := R') hpoly n).grade n ∧ liftStageRingHom q hpoly n y = x :=
  exists_mem_grade_of_mem_range (liftTowerStage (R' := R') hpoly n).grade 𝒜
    (liftStageRingHom q hpoly n) (fun m b hb => liftStageRingHom_mem_grade q hpoly n m b hb) n hx
    (liftStageRingHom_range_grade q hpoly hq n hx)

end Stage

end DividedPowers.TateResolution

end
