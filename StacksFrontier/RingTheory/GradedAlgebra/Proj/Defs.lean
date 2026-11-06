module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar

@[expose] public section


variable {A : Type*} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The homogeneous spectrum `Proj 𝒜` of a graded ring: the set of homogeneous prime
ideals `𝔭` of `A` with `𝒜₊ ⊄ 𝔭`, topologized by the subspace topology from `Spec A`. -/
@[stacks 00JN, ega "II 2.3.1" "set of graded primes", ega "III 4.3.13"]
abbrev Proj : Type _ := ProjectiveSpectrum 𝒜

/-- The inclusion of `Proj 𝒜` into `Spec A` sending a homogeneous prime ideal to the
underlying prime ideal. -/
def Proj.toSpec : Proj 𝒜 → PrimeSpectrum A :=
  fun p => ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩

/-- The prime ideal of `A` underlying `Proj.toSpec 𝒜 p` is the ideal of the homogeneous prime
ideal `p`. -/
@[simp]
theorem Proj.toSpec_asIdeal (p : Proj 𝒜) :
    (Proj.toSpec 𝒜 p).asIdeal = p.asHomogeneousIdeal.toIdeal :=
  rfl

/-- Injectivity of `Proj.toSpec`: a point of `Proj 𝒜` is determined by its
underlying prime ideal in `Spec A`. -/
theorem Proj.toSpec_injective : Function.Injective (Proj.toSpec 𝒜) :=
  fun _ _ hpq => ProjectiveSpectrum.ext <| HomogeneousIdeal.toIdeal_injective <|
    congrArg PrimeSpectrum.asIdeal hpq

/-- The Zariski topology on `Proj 𝒜` agrees with the topology induced from
`PrimeSpectrum A` along `Proj.toSpec`. -/
@[ega "II 2.3.3"]
theorem Proj.isInducing_toSpec : Topology.IsInducing (Proj.toSpec 𝒜) := by
  refine ⟨TopologicalSpace.ext_iff_isClosed.mpr fun U => ?_⟩
  rw [isClosed_induced_iff]
  refine ⟨fun hU => ?_, ?_⟩
  · rw [ProjectiveSpectrum.isClosed_iff_zeroLocus] at hU
    obtain ⟨s, rfl⟩ := hU
    exact ⟨PrimeSpectrum.zeroLocus s, PrimeSpectrum.isClosed_zeroLocus s, rfl⟩
  · rintro ⟨W, hW, rfl⟩
    rw [PrimeSpectrum.isClosed_iff_zeroLocus_ideal] at hW
    obtain ⟨I, rfl⟩ := hW
    exact ProjectiveSpectrum.isClosed_zeroLocus 𝒜 I

/-- `Proj.toSpec` is a topological embedding of `Proj 𝒜` into `Spec A`. -/
theorem Proj.isEmbedding_toSpec : Topology.IsEmbedding (Proj.toSpec 𝒜) :=
  ⟨Proj.isInducing_toSpec 𝒜, Proj.toSpec_injective 𝒜⟩

-- ===== merged from StacksDraft.Ch10.Sec57.Tag00JO =====

/-!
# The graded primes of a graded ring with a homogeneous unit of positive degree

Let `S` be a `ℤ`-graded ring (commutative, with unit) containing a homogeneous
invertible element of positive degree, i.e. an element `f ∈ S_d` for some integer
`d > 0` that is a unit of `S`. Let `S₀` be the degree-`0` subring.

Let `G ⊆ Spec(S)` be the set of `ℤ`-graded primes of `S`, that is, the prime ideals
`q ⊆ S` that are homogeneous (graded) ideals, equipped with the subspace topology
induced from the Zariski topology on `Spec(S)`.

The inclusion `ι : S₀ ↪ S` induces a continuous map on spectra
`Spec(ι) : Spec(S) → Spec(S₀)`, `q ↦ q ∩ S₀`. Let `Φ : G → Spec(S₀)` be its
restriction to `G`.

Then `Φ` is a homeomorphism.

## Conventions

A `ℤ`-graded ring is a commutative ring `A` with a family of additive subgroups
`𝒜 : ℤ → σ` and `[GradedRing 𝒜]`, which packages the decomposition `A = ⨁ n, 𝒜 n`
together with `𝒜 m * 𝒜 n ⊆ 𝒜 (m+n)` and `1 ∈ 𝒜 0`.  The degree-`0` subring `S₀` is
`SetLike.GradeZero.subring 𝒜`.  An ideal of a graded ring is homogeneous when it is
`Ideal.IsHomogeneous 𝒜`, Mathlib's form of "generated by homogeneous elements", which is
equivalent to being stable under taking homogeneous components.  Finally `PrimeSpectrum A`
is `Spec(A)` with the Zariski topology and `PrimeSpectrum.comap` the induced map on
spectra, which for the inclusion `S₀ ↪ S` is `q ↦ q ∩ S₀`.

## Outline

Write `S = ⨁ₙ Sₙ`, let `f ∈ 𝒜 d` be the homogeneous unit with `d > 0`, and put
`g := f⁻¹ ∈ 𝒜 (-d)`.  That `Φ` is a homeomorphism follows from
`isHomeomorph_iff_continuous_isClosedMap_bijective`: `Φ` is continuous, a closed map, and
bijective.

Both the closed-map property and injectivity rest on one criterion: for a homogeneous
prime `q` and a homogeneous `s ∈ 𝒜 n`,

  `s ∈ q ↔ s^d · wₙ ∈ q`,   where `wₙ` is a unit of degree `-n·d`, for instance `f^(-n)`.

Indeed `s^d ∈ 𝒜 (n·d)` and `wₙ ∈ 𝒜 (-(n·d))`, so `s^d·wₙ ∈ 𝒜 0 = S₀`, and the condition
`s^d·wₙ ∈ q` is therefore a condition on `q ∩ S₀ = Φ q`.  Forwards it is immediate, `q`
being an ideal; backwards, `wₙ` is a unit so `wₙ ∉ q`, and `q` prime with `s^d·wₙ ∈ q`
gives `s^d ∈ q`, hence `s ∈ q`.  So `Φ q` determines the membership of every homogeneous
element of `q`.
-/

@[expose] public section

open scoped DirectSum

variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℤ → σ) [GradedRing 𝒜]

/-- `A` contains a *homogeneous invertible element of positive degree*
if there is an integer `d > 0` and a unit `f` of `A` with `f ∈ 𝒜 d`. -/
def HasHomogeneousUnitOfPosDegree : Prop :=
  ∃ d : ℤ, 0 < d ∧ ∃ f : A, f ∈ 𝒜 d ∧ IsUnit f

/-- The degree-`0` subring `S₀ ⊆ S`. -/
@[ega "II 2.1.1"]
abbrev gradeZeroSubring : Subring A := SetLike.GradeZero.subring 𝒜

/-- The set `G ⊆ Spec(S)` of `ℤ`-graded (homogeneous) primes of `S`,
i.e. the prime ideals whose underlying ideal is a homogeneous ideal. It carries the
subspace topology induced from the Zariski topology on `Spec(S)`. -/
def gradedPrimes : Set (PrimeSpectrum A) :=
  {q : PrimeSpectrum A | q.asIdeal.IsHomogeneous 𝒜}

/-- The comparison map `Φ : G → Spec(S₀)`, `q ↦ q ∩ S₀`, obtained by
restricting the continuous map `Spec(ι) = PrimeSpectrum.comap ι` (`ι : S₀ ↪ S`) to the
subspace `G` of graded primes. -/
noncomputable def gradedPrimesComparison :
    gradedPrimes 𝒜 → PrimeSpectrum (gradeZeroSubring 𝒜) :=
  fun q => PrimeSpectrum.comap (gradeZeroSubring 𝒜).subtype q.val

/-- **Continuity of `Φ`.** `Φ` is the restriction to the subspace `G` of the continuous
map `PrimeSpectrum.comap ι` (`ι : S₀ ↪ S`); a restriction of a continuous map along the
subspace inclusion is continuous. -/
theorem gradedPrimesComparison_continuous :
    Continuous (gradedPrimesComparison 𝒜) :=
  (PrimeSpectrum.continuous_comap (gradeZeroSubring 𝒜).subtype).comp continuous_subtype_val

/-- the inverse of a homogeneous unit lies in the
negated degree. -/
theorem mem_neg_of_mul_eq_one' (d : ℤ) (f g : A) (hu : IsUnit f) (hf : f ∈ 𝒜 d)
    (hfg : f * g = 1) : g ∈ 𝒜 (-d) := by
  classical
  have hcancel : ∀ n : ℤ, n ≠ -d → (GradedRing.proj 𝒜 n) g = 0 := by
    intro n hn
    have hcoe : (↑(((DirectSum.decompose 𝒜) (f * g)) (d + n)) : A)
        = f * ↑(((DirectSum.decompose 𝒜) g) n) :=
      DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 hf
    have h1 : (↑(((DirectSum.decompose 𝒜) (f * g)) (d + n)) : A) = 0 := by
      rw [hfg, DirectSum.decompose_of_mem_ne 𝒜 (i := 0) (j := d+n)
        SetLike.GradedOne.one_mem (by omega)]
    have hfp : f * (GradedRing.proj 𝒜 n) g = 0 := by
      rw [GradedRing.proj_apply, ← hcoe, h1]
    exact (hu.mul_right_eq_zero).mp hfp
  have hg : g = (GradedRing.proj 𝒜 (-d)) g := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 g]
    rw [GradedRing.proj_apply, Finset.sum_eq_single (-d)]
    · intro b _ hbk
      rw [← GradedRing.proj_apply]
      exact hcancel b hbk
    · intro hk
      simp only [DFinsupp.mem_support_toFun, ne_eq, not_not] at hk
      rw [hk]
      rfl
  rw [hg, GradedRing.proj_apply]
  exact SetLike.coe_mem _

/-- integer powers of a homogeneous unit. -/
theorem unit_zpow_mem' (d : ℤ) (u : Aˣ) (hu : (↑u : A) ∈ 𝒜 d) (n : ℤ) :
    (↑(u ^ n) : A) ∈ 𝒜 (n * d) := by
  have hinv : (↑u⁻¹ : A) ∈ 𝒜 (-d) :=
    mem_neg_of_mul_eq_one' 𝒜 d _ _ u.isUnit hu (by rw [u.mul_inv])
  refine Int.induction_on n ?_ ?_ ?_
  · simpa using SetLike.GradedOne.one_mem
  · intro k ih
    have heq : (↑(u ^ (k+1 : ℤ)) : A) = ↑(u^(k:ℤ)) * ↑u := by
      rw [zpow_add_one]
      rfl
    rw [heq]
    have hm := SetLike.mul_mem_graded ih hu
    rwa [show (k:ℤ) * d + d = (k+1) * d by ring] at hm
  · intro k ih
    have heq : (↑(u ^ (-(k:ℤ)-1) : Aˣ) : A) = ↑(u^(-(k:ℤ))) * ↑u⁻¹ := by
      rw [show (-(k:ℤ)-1) = -(k:ℤ) + (-1) by ring, zpow_add, zpow_neg_one]
      rfl
    rw [heq]
    have hm := SetLike.mul_mem_graded ih hinv
    rwa [show (-(k:ℤ)) * d + -d = (-(k:ℤ)-1) * d by ring] at hm

/-- the key membership criterion via a unit. -/
theorem key_criterion' (q : Ideal A) (hq : q.IsPrime) (d : ℕ) (hd : 0 < d) (s w : A)
    (hw : IsUnit w) : (s ∈ q ↔ s^d * w ∈ q) :=
  ⟨fun h => Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem q h _ hd), fun h =>
    hq.mem_of_pow_mem _ ((hq.mem_or_mem h).resolve_right
      fun hc => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hc hw))⟩

/-- If `s ∈ 𝒜 n` and `u` is a unit of degree `d`, then `s ^ d * u ^ (-n)` has degree `0`. -/
theorem pow_mul_unit_zpow_neg_mem_gradeZeroSubring {d : ℕ} {dz : ℤ} (hd : (d : ℤ) = dz)
    {u : Aˣ} (hu : (↑u : A) ∈ 𝒜 dz) {n : ℤ} {s : A} (hs : s ∈ 𝒜 n) :
    s ^ d * ↑(u ^ (-n)) ∈ gradeZeroSubring 𝒜 := by
  have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded d hs) (unit_zpow_mem' 𝒜 dz u hu (-n))
  rwa [show d • n + -n * dz = 0 by rw [nsmul_eq_mul, hd]; ring] at h

/-- A homogeneous unit of positive degree gives a unit of a positive natural degree. -/
private theorem exists_unit_mem_nat_degree {σ A : Type*} [CommRing A] [SetLike σ A]
    (𝒜 : ℤ → σ) (hf : ∃ d : ℤ, 0 < d ∧ ∃ f : A, f ∈ 𝒜 d ∧ IsUnit f) :
    ∃ (d : ℕ) (u : Aˣ), 0 < d ∧ (↑u : A) ∈ 𝒜 (d : ℤ) := by
  obtain ⟨dz, hdz, f, hfmem, hfu⟩ := hf
  lift dz to ℕ using hdz.le
  exact ⟨dz, hfu.unit, by omega, by rwa [IsUnit.unit_spec]⟩

/-- **Injectivity of `Φ`.** A homogeneous prime `q` is determined by `q ∩ S₀`: for
homogeneous `s ∈ 𝒜 n` we have `s ∈ q ↔ s^d·wₙ ∈ q ∩ S₀`. -/
theorem gradedPrimesComparison_injective (hf : HasHomogeneousUnitOfPosDegree 𝒜) :
    Function.Injective (gradedPrimesComparison 𝒜) := by
  obtain ⟨d, u, hd, hu⟩ := exists_unit_mem_nat_degree 𝒜 hf
  intro q q' h
  have hagree : ∀ x (hx : x ∈ gradeZeroSubring 𝒜), x ∈ q.val.asIdeal ↔ x ∈ q'.val.asIdeal := by
    intro x hx
    have h1 : (⟨x, hx⟩ : gradeZeroSubring 𝒜) ∈ (gradedPrimesComparison 𝒜 q).asIdeal
        ↔ (⟨x, hx⟩ : gradeZeroSubring 𝒜) ∈ (gradedPrimesComparison 𝒜 q').asIdeal := by
      rw [h]
    simpa [gradedPrimesComparison, PrimeSpectrum.comap_asIdeal] using h1
  have hhom (i : ℤ) (s : A) (hs : s ∈ 𝒜 i) : s ∈ q.val.asIdeal ↔ s ∈ q'.val.asIdeal := by
    rw [key_criterion' q.val.asIdeal q.val.isPrime _ hd s _ (u ^ (-i)).isUnit,
      key_criterion' q'.val.asIdeal q'.val.isPrime _ hd s _ (u ^ (-i)).isUnit]
    exact hagree _ (pow_mul_unit_zpow_neg_mem_gradeZeroSubring 𝒜 rfl hu hs)
  refine Subtype.ext (PrimeSpectrum.ext (Ideal.ext fun x => ?_))
  rw [q.property.mem_iff, q'.property.mem_iff]
  exact forall_congr' fun i => hhom i _ (SetLike.coe_mem _)

/-- The ideal `Ψ p ⊆ S` attached to an ideal `p ⊆ S₀`: `x ∈ Ψ p` iff `xₙ · t ∈ p` for every
`n` and every `t ∈ 𝒜 (-n)`. -/
def gradeZeroIdealExtension (p : Ideal (gradeZeroSubring 𝒜)) : Ideal A where
  carrier := {x | ∀ n : ℤ, ∀ t ∈ 𝒜 (-n), GradedRing.proj 𝒜 n x * t ∈
    p.toAddSubgroup.map (gradeZeroSubring 𝒜).subtype.toAddMonoidHom}
  add_mem' {x y} hx hy n t ht := by
    rw [map_add, add_mul]
    exact add_mem (hx n t ht) (hy n t ht)
  zero_mem' n t _ := by
    rw [map_zero, zero_mul]
    exact zero_mem _
  smul_mem' c x hx := by
    induction c using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero =>
      intro n t _
      rw [zero_smul, map_zero, zero_mul]
      exact zero_mem _
    | @homogeneous i c =>
      intro n t ht
      have h := DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 (j := n - i) (b := x) c.2
      rw [show i + (n - i) = n by ring] at h
      have hct : ↑c * t ∈ 𝒜 (-(n - i)) := by
        have := SetLike.mul_mem_graded c.2 ht
        rwa [show i + -n = -(n - i) by ring] at this
      convert hx (n - i) _ hct using 1
      rw [smul_eq_mul, GradedRing.proj_apply, GradedRing.proj_apply, h]
      ring
    | add a b ha hb =>
      intro n t ht
      rw [add_smul, map_add, add_mul]
      exact add_mem (ha n t ht) (hb n t ht)

/-- `x ∈ Ψ p` iff `xₙ · t ∈ p` for every `n` and every `t ∈ 𝒜 (-n)`. -/
theorem mem_gradeZeroIdealExtension {p : Ideal (gradeZeroSubring 𝒜)} {x : A} :
    x ∈ gradeZeroIdealExtension 𝒜 p ↔ ∀ n : ℤ, ∀ t ∈ 𝒜 (-n), GradedRing.proj 𝒜 n x * t ∈
      p.toAddSubgroup.map (gradeZeroSubring 𝒜).subtype.toAddMonoidHom :=
  Iff.rfl

/-- A homogeneous `x ∈ 𝒜 i` lies in `Ψ p` iff `x · t ∈ p` for every `t ∈ 𝒜 (-i)`. -/
theorem mem_gradeZeroIdealExtension_of_mem {p : Ideal (gradeZeroSubring 𝒜)} {i : ℤ} {x : A}
    (hx : x ∈ 𝒜 i) : x ∈ gradeZeroIdealExtension 𝒜 p ↔
      ∀ t ∈ 𝒜 (-i), x * t ∈ p.toAddSubgroup.map (gradeZeroSubring 𝒜).subtype.toAddMonoidHom := by
  rw [mem_gradeZeroIdealExtension]
  refine ⟨fun h t ht => ?_, fun h n t ht => ?_⟩
  · have := h i t ht
    rwa [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx] at this
  · obtain rfl | hin := eq_or_ne i n
    · rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 hx]
      exact h t ht
    · rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 hx hin, zero_mul]
      exact zero_mem _

/-- The ideal `Ψ p` is homogeneous. -/
theorem gradeZeroIdealExtension_isHomogeneous (p : Ideal (gradeZeroSubring 𝒜)) :
    (gradeZeroIdealExtension 𝒜 p).IsHomogeneous 𝒜 := by
  intro i x hx
  rw [mem_gradeZeroIdealExtension_of_mem 𝒜 (SetLike.coe_mem _)]
  intro t ht
  have := (mem_gradeZeroIdealExtension 𝒜).1 hx i t ht
  rwa [GradedRing.proj_apply] at this

/-- `Ψ p ∩ S₀ = p`. -/
theorem comap_gradeZeroIdealExtension (p : Ideal (gradeZeroSubring 𝒜)) :
    (gradeZeroIdealExtension 𝒜 p).comap (gradeZeroSubring 𝒜).subtype = p := by
  ext ⟨a, ha⟩
  rw [Ideal.mem_comap, Subring.subtype_apply,
    mem_gradeZeroIdealExtension_of_mem 𝒜 (i := 0) (show a ∈ 𝒜 0 from ha)]
  refine ⟨fun h => ?_, fun h t ht => ?_⟩
  · obtain ⟨b, hb, hba⟩ := AddSubgroup.mem_map.1 (h 1 (by simpa using SetLike.GradedOne.one_mem))
    rwa [show b = ⟨a, ha⟩ from Subtype.ext (hba.trans (mul_one a))] at hb
  · rw [neg_zero] at ht
    exact AddSubgroup.mem_map_of_mem (gradeZeroSubring 𝒜).subtype.toAddMonoidHom
      (K := p.toAddSubgroup) (p.mul_mem_right ⟨t, ht⟩ h)

/-- If `p` is a proper ideal of `S₀`, then `Ψ p` is a proper ideal of `S`. -/
theorem gradeZeroIdealExtension_ne_top {p : Ideal (gradeZeroSubring 𝒜)} (hp : p ≠ ⊤) :
    gradeZeroIdealExtension 𝒜 p ≠ ⊤ := fun h =>
  hp (by rw [← comap_gradeZeroIdealExtension 𝒜 p, h, Ideal.comap_top])

/-- If `p` is a prime ideal of `S₀`, then `Ψ p` is a prime ideal of `S`. -/
theorem gradeZeroIdealExtension_isPrime (p : Ideal (gradeZeroSubring 𝒜)) [hp : p.IsPrime] :
    (gradeZeroIdealExtension 𝒜 p).IsPrime := by
  refine (gradeZeroIdealExtension_isHomogeneous 𝒜 p).isPrime_of_homogeneous_mem_or_mem
    (gradeZeroIdealExtension_ne_top 𝒜 hp.ne_top) ?_
  rintro x y ⟨a, hxa⟩ ⟨b, hyb⟩ hxy
  rw [mem_gradeZeroIdealExtension_of_mem 𝒜 (SetLike.mul_mem_graded hxa hyb)] at hxy
  rw [mem_gradeZeroIdealExtension_of_mem 𝒜 hxa, mem_gradeZeroIdealExtension_of_mem 𝒜 hyb]
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨t₀, ht₀, hnt₀⟩, ⟨t₁, ht₁, hnt₁⟩⟩ := hcon
  have hx0 : x * t₀ ∈ 𝒜 0 := by simpa using SetLike.mul_mem_graded hxa ht₀
  have hy0 : y * t₁ ∈ 𝒜 0 := by simpa using SetLike.mul_mem_graded hyb ht₁
  have ht : t₀ * t₁ ∈ 𝒜 (-(a + b)) := by
    have := SetLike.mul_mem_graded ht₀ ht₁
    rwa [neg_add]
  obtain ⟨c, hc, hce⟩ := AddSubgroup.mem_map.1 (hxy _ ht)
  have hc' : c = ⟨x * t₀, hx0⟩ * ⟨y * t₁, hy0⟩ :=
    Subtype.ext (hce.trans (by ring : x * y * (t₀ * t₁) = x * t₀ * (y * t₁)))
  rcases hp.mem_or_mem (hc' ▸ hc) with h | h
  · exact hnt₀ (AddSubgroup.mem_map_of_mem _ (K := p.toAddSubgroup) (x := ⟨_, hx0⟩) h)
  · exact hnt₁ (AddSubgroup.mem_map_of_mem _ (K := p.toAddSubgroup) (x := ⟨_, hy0⟩) h)

/-- **Surjectivity of `Φ`.** Every prime `p ⊆ S₀` is `Ψ p ∩ S₀`. -/
theorem gradedPrimesComparison_surjective : Function.Surjective (gradedPrimesComparison 𝒜) :=
  fun p => ⟨⟨⟨_, gradeZeroIdealExtension_isPrime 𝒜 p.asIdeal⟩,
    gradeZeroIdealExtension_isHomogeneous 𝒜 _⟩,
    PrimeSpectrum.ext (comap_gradeZeroIdealExtension 𝒜 _)⟩

/-- **Bijectivity of `Φ`.** `Φ` is a bijection from `G` (homogeneous primes of `S`) onto
`Spec(S₀)`.

For injectivity: if `q, q'` are homogeneous primes with `q ∩ S₀ = q' ∩ S₀`, then by the
criterion above, for every homogeneous `s ∈ 𝒜 n` we have `s ∈ q ↔ s^d·wₙ ∈ q∩S₀` and
likewise for `q'`; since `q∩S₀ = q'∩S₀` these agree, so `q` and `q'` have the same
homogeneous elements; homogeneous ideals are determined by their homogeneous elements,
hence `q = q'`.  (This direction uses the unit `f`.)

For surjectivity: given a prime `p ⊆ S₀`, define the homogeneous ideal `Ψ p := ⨁ₙ (Ψ p)ₙ`
with `(Ψ p)ₙ := { s ∈ 𝒜 n : ∀ t ∈ 𝒜 (-n), s·t ∈ p }`. Then:
  * each `(Ψ p)ₙ` is an additive subgroup and `𝒜 m · (Ψ p)ₙ ⊆ (Ψ p)(m+n)` (since for
    `a ∈ 𝒜 m`, `t ∈ 𝒜 (-(m+n))`, `(a·s)·t = s·(a·t)` with `a·t ∈ 𝒜 (-n)`), so `Ψ p`
    is a homogeneous ideal;
  * `(Ψ p) ∩ S₀ = p` exactly: taking `t = 1 ∈ 𝒜 0` gives `⊆ p`; `p` an ideal gives `⊇ p`;
  * `Ψ p` is proper: `1 ∉ p`;
  * `Ψ p` is prime: by `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem`, check
    homogeneous `x ∈ 𝒜 m`, `y ∈ 𝒜 n` with `x·y ∈ Ψ p`. If `x ∉ Ψ p` and `y ∉ Ψ p`, pick
    `t₀ ∈ 𝒜 (-m)`, `t₁ ∈ 𝒜 (-n)` with `x·t₀ ∉ p`, `y·t₁ ∉ p`; then
    `(x·t₀)(y·t₁) = (x·y)(t₀·t₁) ∈ p` with `t₀·t₁ ∈ 𝒜 (-(m+n))`, contradicting `p` prime.
Hence `Φ (Ψ p) = p`.  Surjectivity does not need the unit. -/
theorem gradedPrimesComparison_bijective
    (hf : HasHomogeneousUnitOfPosDegree 𝒜) :
    Function.Bijective (gradedPrimesComparison 𝒜) :=
  ⟨gradedPrimesComparison_injective 𝒜 hf, gradedPrimesComparison_surjective 𝒜⟩

/-- **The membership criterion.** For a homogeneous prime `q`, a unit `u` of degree `d > 0`
and `s ∈ 𝒜 n`, `s ∈ q ↔ s ^ d * u ^ (-n) ∈ Φ q`. -/
theorem mem_iff_pow_mul_mem_gradedPrimesComparison {d : ℕ} {dz : ℤ} (hd : (d : ℤ) = dz)
    (hd₀ : 0 < d) {u : Aˣ} (hu : (↑u : A) ∈ 𝒜 dz) (q : gradedPrimes 𝒜) {n : ℤ} {s : A}
    (hs : s ∈ 𝒜 n) : s ∈ q.val.asIdeal ↔
      (⟨_, pow_mul_unit_zpow_neg_mem_gradeZeroSubring 𝒜 hd hu hs⟩ : gradeZeroSubring 𝒜) ∈
        (gradedPrimesComparison 𝒜 q).asIdeal :=
  key_criterion' _ q.val.isPrime d hd₀ s _ (u ^ (-n)).isUnit

/-- **`Φ` is a closed map.** Closed subsets of the subspace `G` have the form
`{ q ∈ G : 𝔞 ⊆ q }` for a homogeneous ideal `𝔞 ⊆ S` (one may replace any ideal by the
homogeneous ideal generated by the homogeneous components of its elements without changing
which homogeneous primes contain it). For such `𝔞`, choose a homogeneous generating set;
by the criterion above, for a homogeneous generator `s ∈ 𝒜 n`, `s ∈ q ↔ s^d·wₙ ∈ Φ q`. Let
`𝔟 ⊆ S₀` be the ideal generated by `{ s^d·wₙ : s a homogeneous generator of 𝔞 }`. Then for
`q ∈ G`,  `𝔞 ⊆ q  ↔  𝔟 ⊆ Φ q`, i.e. `Φ` maps the closed set `V(𝔞) ∩ G` onto the closed
set `V(𝔟)` (using surjectivity for the onto direction). Hence `Φ` sends closed sets to
closed sets. -/
theorem gradedPrimesComparison_isClosedMap
    (hf : HasHomogeneousUnitOfPosDegree 𝒜) :
    IsClosedMap (gradedPrimesComparison 𝒜) := by
  classical
  obtain ⟨dn, u, hdn, hu_mem⟩ := exists_unit_mem_nat_degree 𝒜 hf
  intro C hC
  rw [isClosed_induced_iff] at hC
  obtain ⟨t, ht_closed, ht_eq⟩ := hC
  rw [PrimeSpectrum.isClosed_iff_zeroLocus] at ht_closed
  obtain ⟨s, rfl⟩ := ht_closed
  set H : HomogeneousIdeal 𝒜 := Ideal.homogeneousHull 𝒜 (Ideal.span s)
  set T : Set (gradeZeroSubring 𝒜) :=
    { y | ∃ (n : ℤ) (sA : A), sA ∈ 𝒜 n ∧ sA ∈ H.toIdeal ∧ (y : A) = sA^dn * ↑(u^(-n)) }
  have hCmem : ∀ q : gradedPrimes 𝒜, q ∈ C ↔ Ideal.span s ≤ q.val.asIdeal := by
    intro q
    rw [← ht_eq, Set.mem_preimage, PrimeSpectrum.mem_zeroLocus]
    exact Ideal.span_le.symm
  have hequiv : ∀ q : gradedPrimes 𝒜,
      (Ideal.span s ≤ q.val.asIdeal) ↔ (T ⊆ (gradedPrimesComparison 𝒜 q).asIdeal) := by
    intro q
    constructor
    · rintro hsq y ⟨n, sA, hsAn, hsAH, hyeq⟩
      rw [SetLike.mem_coe, show y = ⟨_, pow_mul_unit_zpow_neg_mem_gradeZeroSubring 𝒜 rfl hu_mem
        hsAn⟩ from Subtype.ext hyeq]
      exact (mem_iff_pow_mul_mem_gradedPrimesComparison 𝒜 rfl hdn hu_mem q hsAn).mp
        ((Ideal.homogeneousHull.gc 𝒜 (Ideal.span s) ⟨q.val.asIdeal, q.property⟩).mpr hsq hsAH)
    · intro hTq
      refine (Ideal.le_toIdeal_homogeneousHull 𝒜 (Ideal.span s)).trans fun a ha => ?_
      rw [q.property.mem_iff]
      intro i
      exact (mem_iff_pow_mul_mem_gradedPrimesComparison 𝒜 rfl hdn hu_mem q
        (SetLike.coe_mem _)).mpr (hTq ⟨i, _, SetLike.coe_mem _, H.isHomogeneous i ha, rfl⟩)
  rw [PrimeSpectrum.isClosed_iff_zeroLocus]
  refine ⟨T, Set.ext fun P => ?_⟩
  rw [PrimeSpectrum.mem_zeroLocus]
  constructor
  · rintro ⟨q, hqC, rfl⟩
    exact (hequiv q).mp ((hCmem q).mp hqC)
  · intro hTP
    obtain ⟨q, rfl⟩ := gradedPrimesComparison_surjective 𝒜 P
    exact ⟨q, (hCmem q).mpr ((hequiv q).mpr hTP), rfl⟩

/-- Let `S` be a `ℤ`-graded ring containing a homogeneous invertible
element of positive degree. Then the comparison map `Φ : G → Spec(S₀)`,
`q ↦ q ∩ S₀`, from the space of `ℤ`-graded primes of `S` (with the subspace topology) to
`Spec(S₀)`, is a homeomorphism. -/
@[stacks 00JO]
theorem gradedPrimesComparison_isHomeomorph
    (hf : HasHomogeneousUnitOfPosDegree 𝒜) :
    IsHomeomorph (gradedPrimesComparison 𝒜) :=
  isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨gradedPrimesComparison_continuous 𝒜, gradedPrimesComparison_isClosedMap 𝒜 hf,
      gradedPrimesComparison_bijective 𝒜 hf⟩

-- ===== merged from StacksDraft.Ch10.Sec57.Tag00JQ =====


/-!
# Proj of a polynomial ring in one variable

Let `R` be a ring and `S = R[X]` with `deg X = 1`. The natural map
`Proj(S) → Spec(R)` is a bijection and in fact a homeomorphism.

We model `R[X]` as `MvPolynomial (Fin 1) R` carrying its standard grading by total
degree (`homogeneousSubmodule (Fin 1) R`), so that `X` is homogeneous of degree `1`.
The natural map sends a homogeneous prime `𝔭` of `S` to its contraction
`𝔭 ∩ R = (C)⁻¹ 𝔭` along the structural inclusion `R → S`, i.e. `PrimeSpectrum.comap`
of the algebra map.
-/


open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type*) [CommRing R]

/-- The grading on `S = R[X]` by total degree, with `deg X = 1`. -/
@[ega "II 3.1.7" "special case", ega "II 8.2.2" "8.2.2.2, special case"]
abbrev grading : ℕ → Submodule R (MvPolynomial (Fin 1) R) :=
  homogeneousSubmodule (Fin 1) R

/-- The natural map `Proj(R[X]) → Spec(R)`, sending a homogeneous prime ideal `𝔭`
to its contraction `𝔭 ∩ R` along the inclusion `R → R[X]`. -/
noncomputable def projToSpec (p : ProjectiveSpectrum (grading R)) : PrimeSpectrum R :=
  PrimeSpectrum.comap (algebraMap R (MvPolynomial (Fin 1) R))
    ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩

/-- The projection of `R[X]` to its degree `i` part is `homogeneousComponent i`. -/
lemma proj_grading_eq_homogeneousComponent (i : ℕ) (f : MvPolynomial (Fin 1) R) :
    GradedRing.proj (grading R) i f = homogeneousComponent i f := by
  rw [GradedRing.proj_apply, ← DirectSum.Decomposition.decompose'_eq]
  exact decomposition.decompose'_apply f i

/-- In one variable, every exponent is `Finsupp.single 0 k`. -/
lemma exists_eq_single_zero (m : Fin 1 →₀ ℕ) : ∃ k, m = Finsupp.single 0 k :=
  ⟨m 0, Finsupp.ext fun i => by rw [Subsingleton.elim i 0, Finsupp.single_eq_same]⟩

/-- In one variable, the degree `n` homogeneous component of `f` is the single monomial
`aₙ Xⁿ`. -/
lemma homogeneousComponent_fin_one (n : ℕ) (f : MvPolynomial (Fin 1) R) :
    homogeneousComponent n f = C (f.coeff (Finsupp.single 0 n)) * X 0 ^ n := by
  ext m
  obtain ⟨k, rfl⟩ := exists_eq_single_zero m
  rw [C_mul_X_pow_eq_monomial, coeff_homogeneousComponent, coeff_monomial, Finsupp.degree_single]
  obtain rfl | h := eq_or_ne k n
  · simp
  · simp [h, Ne.symm h]

variable {R}

/-- A point of `Proj(R[X])` does not contain `X`. -/
lemma X_notMem_projectiveSpectrum (p : ProjectiveSpectrum (grading R)) :
    (X 0 : MvPolynomial (Fin 1) R) ∉ p.asHomogeneousIdeal.toIdeal := by
  intro hX
  refine p.not_irrelevant_le fun f hf => ?_
  rw [HomogeneousIdeal.mem_irrelevant_iff, proj_grading_eq_homogeneousComponent,
    homogeneousComponent_zero, C_eq_zero] at hf
  rw [← HomogeneousIdeal.mem_iff,
    mem_iff_homogeneousComponent_mem p.asHomogeneousIdeal.isHomogeneous]
  rintro (_ | n)
  · rw [homogeneousComponent_zero, hf, C_0]
    exact Ideal.zero_mem _
  · rw [homogeneousComponent_fin_one]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hX _ n.succ_pos)

/-- A point of `Proj(R[X])` contains a polynomial if and only if it contains all of its
coefficients. -/
lemma C_coeff_mem_iff (p : ProjectiveSpectrum (grading R)) (f : MvPolynomial (Fin 1) R) :
    (∀ m, C (f.coeff m) ∈ p.asHomogeneousIdeal.toIdeal) ↔ f ∈ p.asHomogeneousIdeal.toIdeal := by
  refine ⟨fun h => ?_, fun hf m => ?_⟩
  · rw [mem_iff_homogeneousComponent_mem p.asHomogeneousIdeal.isHomogeneous]
    intro n
    rw [homogeneousComponent_fin_one]
    exact Ideal.mul_mem_right _ _ (h _)
  · obtain ⟨k, rfl⟩ := exists_eq_single_zero m
    have := homogeneousComponent_mem_of_mem p.asHomogeneousIdeal.isHomogeneous hf k
    rw [homogeneousComponent_fin_one] at this
    exact (p.isPrime.mem_or_mem this).resolve_right fun hX =>
      X_notMem_projectiveSpectrum p (p.isPrime.mem_of_pow_mem _ hX)

/-- The extension `𝔮 R[X]` of a prime `𝔮` of `R`, as a point of `Proj(R[X])`. -/
noncomputable def specToProj (q : PrimeSpectrum R) : ProjectiveSpectrum (grading R) where
  asHomogeneousIdeal := ⟨Ideal.map C q.asIdeal, by
    rw [Ideal.map]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨a, -, rfl⟩
    exact ⟨0, (mem_homogeneousSubmodule 0 _).2 (isHomogeneous_C _ a)⟩⟩
  isPrime := by
    have : (Ideal.map C q.asIdeal : Ideal (MvPolynomial (Fin 1) R)).IsPrime := by
      rw [← Ideal.mk_ker (I := q.asIdeal), ← MvPolynomial.ker_map]
      exact RingHom.ker_isPrime _
    exact this
  not_irrelevant_le h := by
    have hX : (X 0 : MvPolynomial (Fin 1) R) ∈ HomogeneousIdeal.irrelevant (grading R) := by
      rw [HomogeneousIdeal.mem_irrelevant_iff, proj_grading_eq_homogeneousComponent,
        homogeneousComponent_zero, coeff_zero_X, C_0]
    have := mem_map_C_iff.1 (h hX) (Finsupp.single 0 1)
    exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using this))

/-- A polynomial lies in `specToProj q` if and only if all of its coefficients lie in `q`. -/
lemma mem_specToProj_iff (q : PrimeSpectrum R) (f : MvPolynomial (Fin 1) R) :
    f ∈ (specToProj q).asHomogeneousIdeal.toIdeal ↔ ∀ m, f.coeff m ∈ q.asIdeal :=
  mem_map_C_iff

/-- The prime `projToSpec R p` of `R` is the contraction of `p` along `C`. -/
lemma projToSpec_asIdeal (p : ProjectiveSpectrum (grading R)) :
    (projToSpec R p).asIdeal = p.asHomogeneousIdeal.toIdeal.comap C := by
  rw [projToSpec, PrimeSpectrum.comap_asIdeal, MvPolynomial.algebraMap_eq]

/-- `projToSpec` and `specToProj` are inverse bijections. -/
noncomputable def projToSpecEquiv : ProjectiveSpectrum (grading R) ≃ PrimeSpectrum R where
  toFun := projToSpec R
  invFun := specToProj
  left_inv p := by
    refine ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective (Ideal.ext fun f => ?_))
    rw [mem_specToProj_iff, ← C_coeff_mem_iff p f]
    simp [projToSpec_asIdeal]
  right_inv q := by
    refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
    rw [projToSpec_asIdeal, Ideal.mem_comap, mem_specToProj_iff]
    refine ⟨fun h => by simpa using h 0, fun h m => ?_⟩
    rw [coeff_C]
    split_ifs
    exacts [h, q.asIdeal.zero_mem]

/-- The map `projToSpec R` from `Proj(R[X])` to `Spec(R)` is continuous. -/
lemma continuous_projToSpec : Continuous (projToSpec R) :=
  (PrimeSpectrum.continuous_comap _).comp (Proj.isInducing_toSpec (grading R)).continuous

/-- The map `specToProj` from `Spec(R)` to `Proj(R[X])` is continuous. -/
lemma continuous_specToProj : Continuous (specToProj (R := R)) := by
  refine continuous_iff_isClosed.2 fun Z hZ => ?_
  obtain ⟨s, rfl⟩ := (ProjectiveSpectrum.isClosed_iff_zeroLocus (grading R) Z).1 hZ
  convert PrimeSpectrum.isClosed_zeroLocus {a | ∃ f ∈ s, ∃ m, f.coeff m = a} using 1
  ext q
  simp only [Set.mem_preimage, ProjectiveSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus]
  refine ⟨fun h => ?_, fun h f hf => (mem_specToProj_iff q f).2 fun m => h ⟨f, hf, m, rfl⟩⟩
  rintro _ ⟨f, hf, m, rfl⟩
  exact (mem_specToProj_iff q f).1 (h hf) m

/-- The natural map `Proj(R[X]) → Spec(R)` is a bijection and a homeomorphism. -/
@[stacks 00JQ, ega "II 3.1.7" "partial"]
theorem projToSpec_isHomeomorph : IsHomeomorph (projToSpec R) :=
  (Homeomorph.mk projToSpecEquiv continuous_projToSpec continuous_specToProj).isHomeomorph

