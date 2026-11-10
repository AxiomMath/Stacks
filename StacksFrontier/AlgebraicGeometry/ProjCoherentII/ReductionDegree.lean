module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOpenSections
public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.Noetherian
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseDegreeOneAdjoin
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseFiniteness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree the Veronese reduction of Tag 0B5R runs at

The source of [Stacks, Tag 0B5R] fixes `d` to be "the lcm of the degrees of the generators of `A`
over `A_0`", and then uses four separate properties of it:

* `A` is a finite module over `A⁽ᵈ⁾`, and the Veronese part of a finite graded module is a finite
  `A⁽ᵈ⁾`-module — this is what makes the reduction descend;
* `A⁽ᵈ⁾` is generated in degree one over `(A⁽ᵈ⁾)₀ = A₀`, so the whole degree-one theory of
  [Stacks, Tag 0AG6] applies on `X' = Proj A⁽ᵈ⁾`;
* the standard opens of the homogeneous elements of degree `d` cover `X = Proj A`, which is what
  part (6) of the tag needs;
* consequently the ratio locus `W_d` of [Stacks, Tag 01MU] is all of `X`, which is what makes the
  twist of a twist `(ℱ(q))(dn) ≅ ℱ(dn + q)` an isomorphism.

Only the first of the four is literally about the lcm, so a single `d` carrying all four is
obtained as a common multiple: of the lcm `L` of the generator degrees, of the `d₀` of
[Stacks, Tag 0EGH] above which the Veronese subring is generated in degree one, and of a `d₁`
whose degree-`d₁` standard opens cover `X`.

The first property survives the passage from `L` to a multiple `d` of `L` because the finiteness
statements are about *a* finite family of positive-degree homogeneous generators, and a family
may be enlarged: appending `0 ∈ A_d` to it changes neither the subalgebra it generates nor the
degrees that already occur, and raises the lcm of the degrees from `L` to `d`.

## Main results

* `Stacks.Veronese.finite_veroneseSubring_of_lcm_dvd`,
  `Stacks.Veronese.finite_veroneseSubmodule_of_lcm_dvd`,
  `Stacks.Veronese.isNoetherianRing_veroneseSubring_of_lcm_dvd`: the three finiteness statements
  of `StacksFrontier/RingTheory/GradedAlgebra/VeroneseFiniteness.lean` at any positive multiple
  of the lcm of the generator degrees.
* `Stacks.AlgebraicGeometry.ProjCoherentII.exists_reductionDegree`: **the degree.** For a
  Noetherian graded ring there are homogeneous generators and a positive `d`, divisible by the
  lcm of their degrees, such that `A⁽ᵈ⁾` is generated in degree one, the degree-`d` standard
  opens cover `Proj A`, and the ratio locus of `d` is everything.

## References

* [Stacks Project, Tag 0B5R](https://stacks.math.columbia.edu/tag/0B5R)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 0EGH](https://stacks.math.columbia.edu/tag/0EGH)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
-/

@[expose] public noncomputable section

namespace Stacks.Veronese

universe u w t

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

section Enlarge

variable {r : ℕ} (f : Fin r → A) (deg : Fin r → ℕ) {d : ℕ}

/-- A finite family of positive-degree homogeneous generators may be enlarged by `0` in degree
`d`, which makes the lcm of the degrees equal to any common multiple `d` of the old degrees. -/
private theorem exists_generators_lcm_eq
    (hdeg : ∀ i, 0 < deg i) (hf : ∀ i, f i ∈ 𝒜 (deg i))
    (hgen : Algebra.adjoin (gradeZero 𝒜) (Set.range f) = ⊤)
    (hd : 0 < d) (hdvd : Finset.univ.lcm deg ∣ d) :
    ∃ (g : Fin (r + 1) → A) (e : Fin (r + 1) → ℕ), (∀ i, 0 < e i) ∧ (∀ i, g i ∈ 𝒜 (e i)) ∧
      Algebra.adjoin (gradeZero 𝒜) (Set.range g) = ⊤ ∧ Finset.univ.lcm e = d := by
  refine ⟨Fin.snoc f 0, Fin.snoc deg d, ?_, ?_, ?_, ?_⟩
  · refine Fin.lastCases ?_ fun i => ?_
    · simpa using hd
    · simpa using hdeg i
  · refine Fin.lastCases ?_ fun i => ?_
    · simp
    · simpa using hf i
  · refine top_le_iff.mp ?_
    rw [← hgen]
    refine Algebra.adjoin_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨i.castSucc, by simp⟩
  · refine Nat.dvd_antisymm (Finset.lcm_dvd fun i _ => ?_) ?_
    · induction i using Fin.lastCases with
      | last => simp
      | cast j => simpa using dvd_trans (Finset.dvd_lcm (Finset.mem_univ j)) hdvd
    · simpa using Finset.dvd_lcm (f := Fin.snoc (α := fun _ => ℕ) deg d)
        (Finset.mem_univ (Fin.last r))

end Enlarge

variable {r : ℕ} {f : Fin r → A} {deg : Fin r → ℕ} {d : ℕ}

/-- The graded ring is finite over `A⁽ᵈ⁾` for every positive `d` divisible by the lcm of the
degrees of a finite family of positive-degree homogeneous generators, not only for the lcm
itself. -/
public theorem finite_veroneseSubring_of_lcm_dvd (hdeg : ∀ i, 0 < deg i)
    (hf : ∀ i, f i ∈ 𝒜 (deg i)) (hgen : Algebra.adjoin (gradeZero 𝒜) (Set.range f) = ⊤)
    (hd : 0 < d) (hdvd : Finset.univ.lcm deg ∣ d) :
    Module.Finite (veroneseSubring 𝒜 d) A := by
  obtain ⟨g, e, h1, h2, h3, h4⟩ := exists_generators_lcm_eq 𝒜 f deg hdeg hf hgen hd hdvd
  have h := finite_veroneseSubring 𝒜 g e h1 h2 h3
  rwa [h4] at h

/-- The Veronese subring is Noetherian for every positive `d` divisible by the lcm of the
generator degrees. -/
@[ega "II 2.1.7" "special case"]
public theorem isNoetherianRing_veroneseSubring_of_lcm_dvd [IsNoetherianRing A]
    (hdeg : ∀ i, 0 < deg i) (hf : ∀ i, f i ∈ 𝒜 (deg i))
    (hgen : Algebra.adjoin (gradeZero 𝒜) (Set.range f) = ⊤)
    (hd : 0 < d) (hdvd : Finset.univ.lcm deg ∣ d) :
    IsNoetherianRing (veroneseSubring 𝒜 d) := by
  obtain ⟨g, e, h1, h2, h3, h4⟩ := exists_generators_lcm_eq 𝒜 f deg hdeg hf hgen hd hdvd
  have h := isNoetherianRing_veroneseSubring 𝒜 g e h1 h2 h3
  rwa [h4] at h

/-- The Veronese part of a finite graded module is a finite `A⁽ᵈ⁾`-module for every positive
`d` divisible by the lcm of the generator degrees. -/
@[ega "II 2.1.6" "(iii), special case"]
public theorem finite_veroneseSubmodule_of_lcm_dvd [IsNoetherianRing A]
    (hdeg : ∀ i, 0 < deg i) (hf : ∀ i, f i ∈ 𝒜 (deg i))
    (hgen : Algebra.adjoin (gradeZero 𝒜) (Set.range f) = ⊤)
    (hd : 0 < d) (hdvd : Finset.univ.lcm deg ∣ d)
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (ℳ : ℤ → AddSubgroup M) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] :
    Module.Finite (veroneseSubring 𝒜 d) (veroneseSubmodule 𝒜 ℳ d) := by
  obtain ⟨g, e, h1, h2, h3, h4⟩ := exists_generators_lcm_eq 𝒜 f deg hdeg hf hgen hd hdvd
  have h := finite_veroneseSubmodule 𝒜 g e h1 h2 h3 ℳ
  rwa [h4] at h

end Stacks.Veronese

namespace Stacks.AlgebraicGeometry.ProjCoherentII

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The degree-zero part of a Noetherian graded ring is Noetherian. -/
public theorem isNoetherianRing_gradeZero [IsNoetherianRing S] : IsNoetherianRing (𝒮 0) :=
  ((GradedRing.isNoetherianRing_iff_isNoetherianRing_gradeZero_and_irrelevant_fg 𝒮).mp
    inferInstance).1

/-- The degree the Veronese reduction of [Stacks, Tag 0B5R] runs at. For a Noetherian graded
ring `S` there are finitely many homogeneous generators `f i` of positive degrees `deg i` over
`S₀`, and a positive `d` divisible by the lcm of those degrees, such that

* `S⁽ᵈ⁾` is generated in degree one over its degree-zero part,
* the standard opens of the homogeneous elements of degree `d` cover `Proj S`,
* the ratio locus of `d` of [Stacks, Tag 01MU] is all of `Proj S`.

The `d` is a common multiple of three numbers: the lcm of the generator degrees, the bound of
[Stacks, Tag 0EGH] above which the Veronese subring is generated in degree one, and a degree
whose standard opens already cover the quasi-compact `Proj S`. -/
@[ega "II 2.1.6" "(v), special case"]
public theorem exists_reductionDegree [IsNoetherianRing S] :
    ∃ (r : ℕ) (f : Fin r → S) (deg : Fin r → ℕ) (d : ℕ),
      (∀ i, 0 < deg i) ∧ (∀ i, f i ∈ 𝒮 (deg i)) ∧
      Algebra.adjoin (Stacks.Veronese.gradeZero 𝒮) (Set.range f) = ⊤ ∧
      0 < d ∧ Finset.univ.lcm deg ∣ d ∧
      Stacks.Veronese.VeroneseGeneratedInDegOne 𝒮 d ∧
      AlgebraicGeometry.Proj.degreeOpen 𝒮 d = ⊤ ∧
      Stacks.AlgebraicGeometry.ProjShared.ratioLocus 𝒮 d = ⊤ := by
  classical
  have hft : Algebra.FiniteType (𝒮 0) S :=
    Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing 𝒮
  obtain ⟨r, f, deg, hdeg, hfdeg, hgen⟩ :=
    Stacks.Veronese.homogeneous_generators_of_finiteType 𝒮 hft
  obtain ⟨d₀, hd₀, hall⟩ := Stacks.Veronese.veronese_generated_in_deg_one_of_finiteType 𝒮 hft
  obtain ⟨d₁, hd₁, hcov⟩ := exists_pos_degreeOpen_eq_top 𝒮
  set L : ℕ := Finset.univ.lcm deg with hL
  have hLpos : 0 < L := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [hL, Finset.lcm_eq_zero_iff] at h0
    obtain ⟨i, -, hi⟩ := h0
    have := hdeg i
    omega
  set d : ℕ := L * (d₀ * d₁) with hd_def
  have hdpos : 0 < d := by positivity
  have hLd : L ∣ d := ⟨d₀ * d₁, rfl⟩
  have hd₀d : d₀ ∣ d := ⟨L * d₁, by rw [hd_def]; ring⟩
  have hd₁d : d₁ ∣ d := ⟨L * d₀, by rw [hd_def]; ring⟩
  have hdeg1 : AlgebraicGeometry.Proj.degreeOpen 𝒮 d = ⊤ :=
    top_le_iff.mp (hcov.ge.trans (AlgebraicGeometry.Proj.degreeOpen_le_of_dvd 𝒮 hd₁d hdpos))
  refine ⟨r, f, deg, d, hdeg, hfdeg, hgen, hdpos, hLd, hall d hdpos hd₀d, hdeg1, ?_⟩
  refine Stacks.AlgebraicGeometry.ProjShared.ratioLocus_eq_top_of_iSup_basicOpen_eq_top 𝒮 ?_
  rw [← hdeg1]
  rfl

end Stacks.AlgebraicGeometry.ProjCoherentII

end
