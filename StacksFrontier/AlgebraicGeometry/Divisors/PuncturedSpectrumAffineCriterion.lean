module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.AlgebraicGeometry.Divisors.PuncturedSpectrumAffineCriterion.Algebra
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine
public import StacksCore.Tactic.StacksAttribute

/-!
# Affineness of the punctured spectrum, and complements of affine opens

Let `(A, 𝔪)` be a Noetherian local ring.  Stacks Tag 0BCR says that the punctured spectrum
`U = Spec A ∖ {𝔪}` is affine if and only if `dim A ≤ 1`.  The implication from the dimension bound
is elementary and is proved in
`StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine`; this file proves the
converse and assembles the equivalence.

The converse is the nonstandard argument of the source.  One first reduces to `A` reduced, which
is legitimate because the punctured spectrum of `A ⧸ nilradical A` is the base change of `U` along
the closed immersion `Spec (A ⧸ nilradical A) → Spec A`, hence again affine, while the primes of
the two rings agree.  For `A` reduced and of positive dimension, prime avoidance produces an
`f ∈ 𝔪` lying in no minimal prime, so a nonzerodivisor.  Writing `B = Γ(U, 𝒪_U)`, three facts hold
and are proved here from the fact that `Γ(Spec A, D(g))` is simultaneously a localization of `A`
and of `B` away from `g`, for every `g ∈ 𝔪`:

* the images of `𝔪` generate the unit ideal of `B`, because the `D(g)` with `g ∈ 𝔪` cover `U`;
* a power of each `g ∈ 𝔪` carries every element of `B` into the image of `A`;
* `f` acts injectively on `B`.

The ring-theoretic consequence — that `f` generates the unit ideal of `B` — is
`Stacks.Divisors.span_singleton_eq_top_of_forall_exists_pow_smul_mem_range`, proved by the length
argument of the source in the companion file `…/PuncturedSpectrumAffineCriterion/Algebra.lean`.
Geometrically it says `D(f) = U`, i.e. `𝔪` is the only prime containing `f`; Krull's principal
ideal theorem then gives `dim A = height 𝔪 ≤ 1`.

The last section deduces Stacks Tag 0BCU: for an open subscheme `U` of a locally Noetherian
scheme `X` whose inclusion is affine, the local ring at the generic point `ξ` of an irreducible
component of `X ∖ U` has dimension at most one, with equality when `ξ` lies in the closure of
`U`.  Pulling `U` back along `Spec 𝒪_{X,ξ} → X` gives the punctured spectrum of the stalk, which
is affine; so this is Tag 0BCR at the stalk.

## Main results

* `Stacks.Divisors.eq_maximalIdeal_of_isAffineOpen_puncturedSpectrum` — for an affine punctured
  spectrum, a nonzerodivisor in the maximal ideal lies in no other prime.
* `Stacks.Divisors.isAffineOpen_puncturedSpectrum_quotient` — affineness of the punctured spectrum
  passes to quotients.
* `Stacks.Divisors.isAffineOpen_puncturedSpectrum_iff_krullDimLE_one` — Stacks Tag 0BCR.
* `Stacks.Divisors.krullDimLE_one_stalk_at_genericPoint_compl_affineOpenImmersion` and
  `Stacks.Divisors.ringKrullDim_stalk_at_genericPoint_compl_affineOpenImmersion_eq_one` —
  Stacks Tag 0BCU.

## References

* [EGA IV, Corollaire 21.12.7]
* [Stacks Project, Tag 0BCR](https://stacks.math.columbia.edu/tag/0BCR)
* [Stacks Project, Tag 0BCU](https://stacks.math.columbia.edu/tag/0BCU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Opposite

universe u

namespace Stacks.Divisors

/-- The sections of the structure sheaf of `Spec A` over an open subset form an `A`-algebra,
namely `AlgebraicGeometry.StructureSheaf.openAlgebra` at the spelling `Γ(Spec A, U)`. -/
scoped instance algebraSections (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens) :
    Algebra A Γ(Spec (.of A), U) :=
  StructureSheaf.openAlgebra A (op U)

variable {A : Type u} [CommRing A]

/-- The restriction maps of the structure sheaf of `Spec A` are `A`-algebra maps. -/
private lemma map_algebraMap {U W : (Spec (.of A)).Opens} (h : W ≤ U) (a : A) :
    ((Spec (.of A)).presheaf.map (homOfLE h).op).hom (algebraMap A Γ(Spec (.of A), U) a)
      = algebraMap A Γ(Spec (.of A), W) a := rfl

/-- The basic open set of the image of `g : A` in the sections over `U` is `U ∩ D(g)`. -/
private lemma basicOpen_algebraMap (U : (Spec (.of A)).Opens) (g : A) :
    (Spec (.of A)).basicOpen (algebraMap A Γ(Spec (.of A), U) g)
      = U ⊓ PrimeSpectrum.basicOpen g := by
  have h : algebraMap A Γ(Spec (.of A), U) g
      = ((Spec (.of A)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          ((Scheme.ΓSpecIso (.of A)).inv g) := rfl
  rw [h, Scheme.basicOpen_res, basicOpen_eq_of_affine]

/-- Restricting the image of `a : A` in the sections over `U` to a basic open of `U` gives the
image of `a` there. -/
private lemma algebraMap_algebraMap (U : (Spec (.of A)).Opens) (β : Γ(Spec (.of A), U)) (a : A) :
    algebraMap Γ(Spec (.of A), U) Γ(Spec (.of A), (Spec (.of A)).basicOpen β)
        (algebraMap A Γ(Spec (.of A), U) a)
      = algebraMap A Γ(Spec (.of A), (Spec (.of A)).basicOpen β) a := rfl

/-- If `U` is an affine open of `Spec A` containing `D(g)`, then the sections over the basic open
of the image of `g` in `Γ(Spec A, U)` form the localization of `A` away from `g`. -/
private lemma isLocalization_away_basicOpen_algebraMap {U : (Spec (.of A)).Opens} {g : A}
    (hgU : PrimeSpectrum.basicOpen g ≤ U) :
    IsLocalization.Away g
      Γ(Spec (.of A), (Spec (.of A)).basicOpen (algebraMap A Γ(Spec (.of A), U) g)) := by
  have h : (Spec (.of A)).basicOpen (algebraMap A Γ(Spec (.of A), U) g)
      = PrimeSpectrum.basicOpen g := by
    rw [basicOpen_algebraMap]
    exact inf_eq_right.2 hgU
  rw [h]
  exact StructureSheaf.IsLocalization.to_basicOpen A g

/-- If `U` is an affine open containing `D(g)`, a section over `U` whose restriction to `D(g)`
vanishes is killed by a power of `g`. -/
private lemma exists_pow_smul_eq_zero_of_map_eq_zero {U : (Spec (.of A)).Opens}
    (hU : IsAffineOpen U) {g : A} {x : Γ(Spec (.of A), U)}
    (hx : algebraMap Γ(Spec (.of A), U)
      Γ(Spec (.of A), (Spec (.of A)).basicOpen (algebraMap A Γ(Spec (.of A), U) g)) x = 0) :
    ∃ k : ℕ, g ^ k • x = 0 := by
  have := hU.isLocalization_basicOpen (algebraMap A Γ(Spec (.of A), U) g)
  obtain ⟨⟨_, k, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (algebraMap A Γ(Spec (.of A), U) g)) _ _).1 hx
  exact ⟨k, by simpa [Algebra.smul_def] using hm⟩

/-- **Inverting an element of the maximal ideal collapses `Γ(U)` onto `A`.**  If `U` is an affine
open of `Spec A` containing `D(g)`, then `Γ(Spec A, U)` and `A` have the same localization away
from `g`, so a power of `g` carries any section over `U` into the image of `A`. -/
private lemma exists_pow_smul_mem_range {U : (Spec (.of A)).Opens} (hU : IsAffineOpen U)
    {g : A} (hgU : PrimeSpectrum.basicOpen g ≤ U) (b : Γ(Spec (.of A), U)) :
    ∃ (N : ℕ) (a : A), algebraMap A Γ(Spec (.of A), U) a = g ^ N • b := by
  have := isLocalization_away_basicOpen_algebraMap hgU
  set β := algebraMap A Γ(Spec (.of A), U) g
  obtain ⟨⟨a, s⟩, hx⟩ := IsLocalization.surj (M := Submonoid.powers g)
    (algebraMap Γ(Spec (.of A), U) Γ(Spec (.of A), (Spec (.of A)).basicOpen β) b)
  dsimp only at hx
  obtain ⟨n, hn⟩ := s.2
  rw [← hn, mul_comm] at hx
  have hzero : algebraMap Γ(Spec (.of A), U) Γ(Spec (.of A), (Spec (.of A)).basicOpen β)
      (g ^ n • b - algebraMap A Γ(Spec (.of A), U) a) = 0 := by
    rw [map_sub, algebraMap_algebraMap, Algebra.smul_def, map_mul, algebraMap_algebraMap, hx,
      sub_self]
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_map_eq_zero hU hzero
  rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hk
  exact ⟨k + n, g ^ k * a, by rw [map_mul, ← Algebra.smul_def, hk]⟩

variable [IsLocalRing A]

/-- For `g` in the maximal ideal, `D(g)` lies in the punctured spectrum. -/
theorem basicOpen_le_puncturedSpectrum {g : A} (hg : g ∈ maximalIdeal A) :
    PrimeSpectrum.basicOpen g ≤ puncturedSpectrum A := by
  rintro _ hp (rfl : _ = closedPoint A)
  exact hp hg

/-- A point of the punctured spectrum avoids some element of the maximal ideal. -/
theorem exists_mem_maximalIdeal_notMem_of_mem_puncturedSpectrum {p : PrimeSpectrum A}
    (hp : p ∈ puncturedSpectrum A) : ∃ g ∈ maximalIdeal A, g ∉ p.asIdeal := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  exact hp (show p = closedPoint A from PrimeSpectrum.ext
    (show p.asIdeal = maximalIdeal A from
      le_antisymm (le_maximalIdeal p.isPrime.ne_top) h))

/-- **The maximal ideal generates the unit ideal of `Γ(U)`.**  If the basic opens `D(g)` for `g` in
the maximal ideal cover the affine open `U`, then the images of those `g` span `Γ(Spec A, U)`. -/
private lemma map_maximalIdeal_eq_top {U : (Spec (.of A)).Opens} (hU : IsAffineOpen U)
    (hcov : ∀ p : PrimeSpectrum A, p ∈ U → ∃ g ∈ maximalIdeal A, g ∉ p.asIdeal) :
    Ideal.map (algebraMap A Γ(Spec (.of A), U)) (maximalIdeal A) = ⊤ := by
  rw [Ideal.map, ← hU.self_le_iSup_basicOpen_iff]
  intro p hp
  obtain ⟨g, hg, hgp⟩ := hcov p hp
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨_, g, hg, rfl⟩, ?_⟩
  rw [basicOpen_algebraMap]
  exact ⟨hp, hgp⟩

/-- **A nonzerodivisor of `A` in the maximal ideal stays a nonzerodivisor on `Γ(U)`.**  A section
killed by `f` restricts to zero on each `D(g)` with `g` in the maximal ideal, because there the
sections are a localization of `A`; as those `g` span the unit ideal, the section vanishes. -/
private lemma algebraMap_mem_nonZeroDivisors {U : (Spec (.of A)).Opens} (hU : IsAffineOpen U)
    (hle : ∀ g ∈ maximalIdeal A, PrimeSpectrum.basicOpen g ≤ U)
    (hmB : Ideal.map (algebraMap A Γ(Spec (.of A), U)) (maximalIdeal A) = ⊤)
    {f : A} (hf : f ∈ nonZeroDivisors A) :
    algebraMap A Γ(Spec (.of A), U) f ∈ nonZeroDivisors Γ(Spec (.of A), U) := by
  have main : ∀ b : Γ(Spec (.of A), U),
      algebraMap A Γ(Spec (.of A), U) f * b = 0 → b = 0 := by
    intro b hb
    set J : Ideal Γ(Spec (.of A), U) :=
      LinearMap.ker (LinearMap.toSpanSingleton Γ(Spec (.of A), U) _ b) with hJ
    have hmemJ : ∀ c : Γ(Spec (.of A), U), c * b = 0 → c ∈ J := by
      intro c hc
      rw [hJ, LinearMap.mem_ker]
      simpa [LinearMap.toSpanSingleton] using hc
    have hrad : ∀ g ∈ maximalIdeal A, algebraMap A Γ(Spec (.of A), U) g ∈ J.radical := by
      intro g hg
      have := isLocalization_away_basicOpen_algebraMap (hle g hg)
      have hfnzd := IsLocalization.nonZeroDivisors_le_comap (M := Submonoid.powers g)
        (S := Γ(Spec (.of A), (Spec (.of A)).basicOpen (algebraMap A Γ(Spec (.of A), U) g))) hf
      obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_map_eq_zero (g := g) hU
        ((mem_nonZeroDivisors_iff.1 hfnzd).1 _ (by
          rw [← algebraMap_algebraMap, ← map_mul, hb, map_zero]))
      exact ⟨k, hmemJ _ (by simpa [Algebra.smul_def] using hk)⟩
    have hJtop : J = ⊤ := by
      have hspan : Ideal.span ((algebraMap A Γ(Spec (.of A), U)) '' (maximalIdeal A : Set A))
          ≤ J.radical := by
        rw [Ideal.span_le]
        rintro _ ⟨g, hg, rfl⟩
        exact hrad g hg
      have hone : (1 : Γ(Spec (.of A), U)) ∈ J.radical :=
        (hmB ▸ hspan : (⊤ : Ideal Γ(Spec (.of A), U)) ≤ J.radical) Submodule.mem_top
      obtain ⟨n, hn⟩ := hone
      rw [one_pow] at hn
      exact Ideal.eq_top_of_isUnit_mem _ hn isUnit_one
    have hb1 : (1 : Γ(Spec (.of A), U)) ∈ J := hJtop ▸ Submodule.mem_top
    rw [hJ, LinearMap.mem_ker] at hb1
    simpa [LinearMap.toSpanSingleton] using hb1
  exact mem_nonZeroDivisors_iff.2 ⟨main, fun b hb => main b (by rw [mul_comm]; exact hb)⟩

/-- Let `U` be an affine open of `Spec A` covered by the basic opens `D(g)` with `g` in the maximal
ideal, each of which it contains.  Then every nonzerodivisor `f` in the maximal ideal has
`D(f) = U`.

Indeed `Γ(Spec A, U)` satisfies the hypotheses of the algebraic core: the maximal ideal
generates its unit ideal, a power of each `g ∈ 𝔪` carries a section into the image of `A`, and
`f` acts injectively.  The core then says `f` generates the unit ideal of `Γ(Spec A, U)`, which
means exactly that `D(f)` is all of `U`. -/
private theorem basicOpen_eq_of_isAffineOpen [IsNoetherianRing A]
    {U : (Spec (.of A)).Opens} (hU : IsAffineOpen U)
    (hle : ∀ g ∈ maximalIdeal A, PrimeSpectrum.basicOpen g ≤ U)
    (hcov : ∀ p : PrimeSpectrum A, p ∈ U → ∃ g ∈ maximalIdeal A, g ∉ p.asIdeal)
    {f : A} (hfm : f ∈ maximalIdeal A) (hf : f ∈ nonZeroDivisors A) :
    PrimeSpectrum.basicOpen f = U := by
  have hmB := map_maximalIdeal_eq_top hU hcov
  have hspan := span_singleton_eq_top_of_forall_exists_pow_smul_mem_range hmB
    (fun g hg b => exists_pow_smul_mem_range hU (hle g hg) b) hfm
    (algebraMap_mem_nonZeroDivisors hU hle hmB hf)
  have hiSup := (hU.iSup_basicOpen_eq_self_iff
    (s := {algebraMap A Γ(Spec (.of A), U) f})).2 (by simpa using hspan)
  have hbo : (Spec (.of A)).basicOpen (algebraMap A Γ(Spec (.of A), U) f) = U := by
    simpa using hiSup
  rw [basicOpen_algebraMap] at hbo
  exact (inf_eq_right.2 (hle f hfm)).symm.trans hbo

/-- If the punctured spectrum of a Noetherian local ring is affine, then a nonzerodivisor in the
maximal ideal lies in no prime other than the maximal ideal. -/
theorem eq_maximalIdeal_of_isAffineOpen_puncturedSpectrum [IsNoetherianRing A]
    (hU : IsAffineOpen (puncturedSpectrum A))
    {f : A} (hfm : f ∈ maximalIdeal A) (hf : f ∈ nonZeroDivisors A)
    {p : Ideal A} (hp : p.IsPrime) (hfp : f ∈ p) : p = maximalIdeal A := by
  have hbo := basicOpen_eq_of_isAffineOpen hU (fun g hg => basicOpen_le_puncturedSpectrum hg)
    (fun _ hq => exists_mem_maximalIdeal_notMem_of_mem_puncturedSpectrum hq) hfm hf
  have hnot : (⟨p, hp⟩ : PrimeSpectrum A) ∉ PrimeSpectrum.basicOpen f := fun h => h hfp
  rw [hbo] at hnot
  exact congrArg PrimeSpectrum.asIdeal (not_not.1 hnot)

/-- For a local ring `A` and an ideal `I` with `A ⧸ I` local, the maximal ideal of `A ⧸ I` pulls
back to the maximal ideal of `A`. -/
theorem comap_maximalIdeal_quotient (I : Ideal A) [IsLocalRing (A ⧸ I)] :
    (maximalIdeal (A ⧸ I)).comap (Ideal.Quotient.mk I) = maximalIdeal A := by
  have : (maximalIdeal (A ⧸ I)).IsMaximal := maximalIdeal.isMaximal _
  exact eq_maximalIdeal
    (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)

/-- The punctured spectrum of `A ⧸ I` is the preimage of the punctured spectrum of `A` under
`Spec (A ⧸ I) → Spec A`. -/
private lemma preimage_puncturedSpectrum (I : Ideal A) [IsLocalRing (A ⧸ I)] :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ⁻¹ᵁ puncturedSpectrum A
      = puncturedSpectrum (A ⧸ I) := by
  have hcp : PrimeSpectrum.comap (Ideal.Quotient.mk I) (closedPoint (A ⧸ I)) = closedPoint A :=
    PrimeSpectrum.ext (comap_maximalIdeal_quotient I)
  have hinj := PrimeSpectrum.comap_injective_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  apply TopologicalSpace.Opens.ext
  ext q
  show ¬PrimeSpectrum.comap (Ideal.Quotient.mk I) q = closedPoint A ↔ ¬q = closedPoint (A ⧸ I)
  exact not_congr ⟨fun he => hinj (he.trans hcp.symm), fun he => he ▸ hcp⟩

/-- **Affineness of the punctured spectrum passes to a quotient.**  The punctured spectrum of
`A ⧸ I` is the base change of that of `A` along the closed immersion `Spec (A ⧸ I) → Spec A`, and
a base change of an affine morphism over an affine scheme is affine. -/
theorem isAffineOpen_puncturedSpectrum_quotient (I : Ideal A) [IsLocalRing (A ⧸ I)]
    (hU : IsAffineOpen (puncturedSpectrum A)) :
    IsAffineOpen (puncturedSpectrum (A ⧸ I)) := by
  have : IsAffine (puncturedSpectrum A).toScheme := hU
  rw [← preimage_puncturedSpectrum I]
  exact IsAffine.of_isPullback (isPullback_morphismRestrict
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (puncturedSpectrum A))

variable [IsNoetherianRing A]

/-- If the punctured spectrum of a Noetherian local ring of positive dimension is affine, then some
element of the maximal ideal has the maximal ideal as its only prime, so the maximal ideal is
minimal over a principal ideal.

The ring is replaced by its reduction, whose punctured spectrum is again affine; there an element
of the maximal ideal avoiding every minimal prime is a nonzerodivisor, so the previous theorem
applies, and primes are unchanged by passing to the reduction. -/
theorem exists_mem_maximalIdeal_maximalIdeal_mem_minimalPrimes
    (hU : IsAffineOpen (puncturedSpectrum A)) (h0 : ¬ Ring.KrullDimLE 0 A) :
    ∃ f ∈ maximalIdeal A, maximalIdeal A ∈ (Ideal.span {f}).minimalPrimes := by
  obtain ⟨f, hfm, hf⟩ := exists_mem_maximalIdeal_notMem_minimalPrimes A h0
  have hnil : nilradical A ≤ maximalIdeal A := nilradical_le_prime _
  have hnt : Nontrivial (A ⧸ nilradical A) :=
    Ideal.Quotient.nontrivial_iff.mpr fun h =>
      (maximalIdeal.isMaximal A).ne_top (top_le_iff.1 (h ▸ hnil))
  have hloc : IsLocalRing (A ⧸ nilradical A) :=
    .of_surjective' _ Ideal.Quotient.mk_surjective
  have hU' := isAffineOpen_puncturedSpectrum_quotient (nilradical A) hU
  have hcm := comap_maximalIdeal_quotient (A := A) (nilradical A)
  have hf'm : Ideal.Quotient.mk (nilradical A) f ∈ maximalIdeal (A ⧸ nilradical A) := by
    rw [← hcm] at hfm
    exact hfm
  have hmain : ∀ x : A, Ideal.Quotient.mk (nilradical A) f * Ideal.Quotient.mk (nilradical A) x
      = 0 → Ideal.Quotient.mk (nilradical A) x = 0 := by
    intro x hx
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
    obtain ⟨n, hn⟩ := hx
    rw [mul_pow] at hn
    refine Ideal.Quotient.eq_zero_iff_mem.2 ?_
    rw [nilradical_eq_sInf, Submodule.mem_sInf]
    intro P hP
    have hPp : Ideal.IsPrime P := hP
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := P) bot_le
    have hQp : Q.IsPrime := hQ.1.1
    refine hQP ?_
    have : x ^ n ∈ Q := by
      rcases hQp.mem_or_mem (hn ▸ Q.zero_mem : f ^ n * x ^ n ∈ Q) with h | h
      · exact absurd (hQp.mem_of_pow_mem n h) (hf Q hQ)
      · exact h
    exact hQp.mem_of_pow_mem n this
  have hf'nzd : Ideal.Quotient.mk (nilradical A) f ∈ nonZeroDivisors (A ⧸ nilradical A) := by
    refine mem_nonZeroDivisors_iff.2 ⟨fun y hy => ?_, fun y hy => ?_⟩ <;>
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    · exact hmain x hy
    · exact hmain x (by rw [mul_comm]; exact hy)
  have key : ∀ p : Ideal A, p.IsPrime → f ∈ p → p = maximalIdeal A := by
    intro p hp hfp
    have hker : nilradical A ≤ p := nilradical_le_prime (H := hp) _
    have hpp : (p.map (Ideal.Quotient.mk (nilradical A))).IsPrime :=
      Ideal.map_isPrime_of_surjective (H := hp) Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hker)
    have heq := eq_maximalIdeal_of_isAffineOpen_puncturedSpectrum hU' hf'm hf'nzd hpp
      (Ideal.mem_map_of_mem _ hfp)
    have h1 : (p.map (Ideal.Quotient.mk (nilradical A))).comap
        (Ideal.Quotient.mk (nilradical A)) = p := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact sup_eq_left.2 hker
    rw [← h1, heq, hcm]
  refine ⟨f, hfm, ⟨⟨maximalIdeal.isMaximal A |>.isPrime, ?_⟩, ?_⟩⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hfm
  · intro q hq _
    exact le_of_eq (key q hq.1 (hq.2 (Ideal.mem_span_singleton_self f))).symm

variable (A) in
/-- The punctured spectrum of a Noetherian local ring is affine if and only if the ring has Krull
dimension at most one. -/
@[stacks 0BCR, ega "IV 21.12.9" "special case"]
theorem isAffineOpen_puncturedSpectrum_iff_krullDimLE_one :
    IsAffineOpen (puncturedSpectrum A) ↔ Ring.KrullDimLE 1 A := by
  refine ⟨fun hU => ?_, isAffineOpen_puncturedSpectrum_of_krullDimLE_one A⟩
  by_cases h0 : Ring.KrullDimLE 0 A
  · have := h0
    infer_instance
  obtain ⟨f, -, hmin⟩ := exists_mem_maximalIdeal_maximalIdeal_mem_minimalPrimes hU h0
  have hheight := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
    (Ideal.span {f}) (maximalIdeal A) hmin
  rw [Ring.krullDimLE_iff, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast hheight

section Complement

open TopologicalSpace Limits

variable {X : Scheme.{u}}

/-- The preimage of `U` under `Spec 𝒪_{X,ξ} → X` is the punctured spectrum of the stalk, when `ξ`
is the generic point of an irreducible component of the complement of `U`.

A point of `Spec 𝒪_{X,ξ}` maps into `X` to a point specializing to `ξ`.  If such an image lay
outside `U` then its closure inside the complement would be contained in a component containing
`ξ`, hence in `Z`; as `ξ` is the generic point of `Z` the two points would specialize to each
other, so the point is the closed point. -/
private lemma fromSpecStalk_preimage_eq_puncturedSpectrum (U : X.Opens)
    {Z : Set ↑((U : Set X)ᶜ)} (hZ : Z ∈ irreducibleComponents ↑((U : Set X)ᶜ))
    {ξ : ↑((U : Set X)ᶜ)} (hξ : IsGenericPoint ξ Z) :
    X.fromSpecStalk (ξ : X) ⁻¹ᵁ U = puncturedSpectrum (X.presheaf.stalk (ξ : X)) := by
  classical
  set A := X.presheaf.stalk (ξ : X)
  set f := X.fromSpecStalk (ξ : X)
  have hfclosed : f (closedPoint A) = (ξ : X) := Scheme.fromSpecStalk_closedPoint
  apply Opens.ext
  ext p
  show f p ∈ U ↔ p ∈ ({closedPoint A} : Set (PrimeSpectrum A))ᶜ
  constructor
  · intro hpU hp
    subst p
    rw [hfclosed] at hpU
    exact ξ.2 hpU
  · intro hp
    by_contra hpU
    set y : ↑((U : Set X)ᶜ) := ⟨f p, hpU⟩ with hy
    have hspec : (f p) ⤳ (ξ : X) := by
      have hrange : f p ∈ Set.range f := ⟨p, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hrange
      exact hrange
    have hspec' : y ⤳ ξ := Topology.IsInducing.subtypeVal.specializes_iff.1 hspec
    obtain ⟨W, hW, hCW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure ({y} : Set ↑((U : Set X)ᶜ))) isIrreducible_singleton.closure
    have hξW : ξ ∈ W := hCW (by simpa [specializes_iff_mem_closure] using hspec')
    have hZW : Z ⊆ W := by
      rw [← hξ.def]
      exact (isClosed_of_mem_irreducibleComponents W hW).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hξW)
    have hback : (ξ : X) ⤳ f p :=
      (hξ.specializes (hZ.2 hW.1 hZW (hCW (subset_closure (Set.mem_singleton y))))).map
        continuous_subtype_val
    have hpoint : f p = (ξ : X) := (inseparable_iff_specializes_and.mpr ⟨hspec, hback⟩).eq
    exact hp (f.isEmbedding.injective (by rw [hfclosed, hpoint]))

/-- The preimage of an affine open immersion under any morphism from an affine scheme is an
affine open: it is the base change of the inclusion of `U`. -/
private lemma isAffineOpen_fromSpecStalk_preimage (U : X.Opens) [IsAffineHom U.ι] (ξ : X) :
    IsAffineOpen (X.fromSpecStalk ξ ⁻¹ᵁ U) :=
  IsAffine.of_isIso (isPullback_morphismRestrict (X.fromSpecStalk ξ) U).isoPullback.hom

/-- Let `U` be an open subscheme of a locally Noetherian scheme `X` whose inclusion is affine.  At
the generic point `ξ` of an irreducible component of `X ∖ U` the local ring has Krull dimension at
most one.

Pulling `U` back along `Spec 𝒪_{X,ξ} → X` gives the punctured spectrum of `𝒪_{X,ξ}`, which is
affine because the inclusion of `U` is; so Tag 0BCR applies. -/
@[stacks 0BCU "dimension bound",
  ega "IV 21.12.7" "codimension ≤ 1",
  sga "6 II 2.2.6" "dim ≤ 1 at maximal pts", sga "2 V 3.4"]
theorem krullDimLE_one_stalk_at_genericPoint_compl_affineOpenImmersion
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (U : X.Opens) [IsAffineHom U.ι]
    {Z : Set ↑((U : Set X)ᶜ)} (hZ : Z ∈ irreducibleComponents ↑((U : Set X)ᶜ))
    {ξ : ↑((U : Set X)ᶜ)} (hξ : IsGenericPoint ξ Z) :
    Ring.KrullDimLE 1 (X.presheaf.stalk (ξ : X)) :=
  (isAffineOpen_puncturedSpectrum_iff_krullDimLE_one _).1 <|
    fromSpecStalk_preimage_eq_puncturedSpectrum U hZ hξ ▸ isAffineOpen_fromSpecStalk_preimage U _

/-- A point in the closure of an open subscheme of a locally Noetherian scheme is specialized to
by a point of that open.

Work in an affine open `V` containing the point.  Its space is Noetherian, hence sober with
finitely many irreducible components, so the closure of `V ∩ U` has a generic point in the
component through the given point; being generic it lies in the dense open `V ∩ U`. -/
private lemma exists_mem_open_specializes_of_mem_closure
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens) {ξ : X}
    (hξ : ξ ∈ closure (U : Set X)) : ∃ η : X, η ∈ U ∧ η ⤳ ξ := by
  classical
  obtain ⟨V, hVaff, hξV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := ξ) (U := ⊤) (Set.mem_univ ξ)
  set Y := V.toScheme
  set xV : Y := ⟨ξ, hξV⟩ with hxV
  set W : Y.Opens := V.ι ⁻¹ᵁ U with hW
  have hclV : xV ∈ closure (W : Set Y) := by
    refine mem_closure_iff.2 fun O hO hxO => ?_
    obtain ⟨y, hyO, hyU⟩ := mem_closure_iff.1 hξ (Subtype.val '' O)
      (V.2.isOpenEmbedding_subtypeVal.isOpenMap O hO) ⟨xV, hxO, rfl⟩
    obtain ⟨z, hzO, rfl⟩ := hyO
    exact ⟨z, hzO, hyU⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hVaff⟩
  have : NoetherianSpace Y := noetherianSpace_of_isAffineOpen V hVaff
  set C : Set Y := closure (W : Set Y) with hC
  have : NoetherianSpace C := NoetherianSpace.of_subset (Set.subset_univ C)
  have : QuasiSober C :=
    Topology.IsClosedEmbedding.quasiSober (Topology.IsClosedEmbedding.subtypeVal isClosed_closure)
  set xC : C := ⟨xV, hclV⟩ with hxC
  obtain ⟨D, hD, hxD⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({xC} : Set C)) isIrreducible_singleton.closure
  set η : genericPoints C := genericPoints.ofComponent ⟨D, hD⟩ with hη
  have hηD : IsGenericPoint η.1 D := genericPoints.isGenericPoint_ofComponent ⟨D, hD⟩
  set W' : Set C := {c | (c.1 : Y) ∈ W} with hW'
  have hW'open : IsOpen W' := W.2.preimage continuous_subtype_val
  have hW'dense : closure W' = Set.univ := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    have himage : Subtype.val '' W' = (W : Set Y) := by
      ext y
      exact ⟨fun ⟨_, hzW, hz⟩ => hz ▸ hzW, fun hyW => ⟨⟨y, subset_closure hyW⟩, hyW, rfl⟩⟩
    rw [himage]
    exact Set.eq_univ_iff_forall.2 fun c => c.2
  obtain ⟨O, hOopen, hOne, hOD⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent D hD
  obtain ⟨c, hcW, hcO⟩ := (closure_inter_open_nonempty_iff hOopen).1
    (by rw [hW'dense]; exact hOne.mono fun c hc => ⟨trivial, hc⟩)
  have hηW : η.1 ∈ W' := (hηD.mem_open_set_iff hW'open).2 ⟨c, hOD hcO, hcW⟩
  exact ⟨V.ι η.1.1, hηW,
    (hηD.specializes (hxD (subset_closure (Set.mem_singleton xC)))).map
      (continuous_subtype_val.comp continuous_subtype_val)⟩

/-- With the hypotheses of
`Stacks.Divisors.krullDimLE_one_stalk_at_genericPoint_compl_affineOpenImmersion`, if `U` is dense
or `ξ` lies in the closure of `U`, then the local ring at `ξ` has dimension exactly one.

Some point of `U` specializes to `ξ`, so it is a point of `Spec 𝒪_{X,ξ}` other than the closed
point; hence the dimension is positive. -/
@[stacks 0BCU "equality in the closure",
  ega "IV 21.12.7" "codimension = 1 if dense",
  sga "6 II 2.2.6" "dim = 1 case"]
theorem ringKrullDim_stalk_at_genericPoint_compl_affineOpenImmersion_eq_one
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (U : X.Opens) [IsAffineHom U.ι]
    {Z : Set ↑((U : Set X)ᶜ)} (hZ : Z ∈ irreducibleComponents ↑((U : Set X)ᶜ))
    {ξ : ↑((U : Set X)ᶜ)} (hξ : IsGenericPoint ξ Z)
    (hξU : Dense (U : Set X) ∨ (ξ : X) ∈ closure (U : Set X)) :
    ringKrullDim (X.presheaf.stalk (ξ : X)) = 1 := by
  set A := X.presheaf.stalk (ξ : X)
  obtain ⟨η, hηU, hηξ⟩ :=
    exists_mem_open_specializes_of_mem_closure X U (hξU.elim (fun h => h ξ) id)
  obtain ⟨p, hp⟩ : η ∈ Set.range (X.fromSpecStalk (ξ : X)) := by
    rw [Scheme.range_fromSpecStalk]; exact hηξ
  have hpne : p ≠ closedPoint A := by
    intro he
    subst p
    rw [Scheme.fromSpecStalk_closedPoint] at hp
    exact ξ.2 (hp.symm ▸ hηU)
  have hnot0 : ¬ Ring.KrullDimLE 0 A := by
    intro h0
    have hpmax : p.asIdeal.IsMaximal := (Ring.krullDimLE_zero_iff.1 h0) p.asIdeal p.2
    exact hpne (PrimeSpectrum.ext (by rw [eq_maximalIdeal hpmax]; rfl))
  exact le_antisymm
    (Ring.krullDimLE_iff.1
      (krullDimLE_one_stalk_at_genericPoint_compl_affineOpenImmersion X U hZ hξ))
    (Order.succ_le_of_lt (lt_of_not_ge fun h => hnot0 (Ring.krullDimLE_iff.2 h)))

end Complement

end Stacks.Divisors

