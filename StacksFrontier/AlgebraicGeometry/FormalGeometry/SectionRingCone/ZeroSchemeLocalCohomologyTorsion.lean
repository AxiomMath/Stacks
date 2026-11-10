module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingCone.FibreDepthDimension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingCone.LocalCohomologyTorsion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionRingCone.ProjPointInvariants

/-!
# The local cohomology of the section ring is killed by a power of the section

Let `k` be a field, `X` a proper scheme over `k`, `L` an ample invertible `𝒪_X`-module with
section ring `A = ⨁_{n ≥ 0} Γ(X, L^{⊗ n})`, and `s₁ ∈ A₁` a degree-one section. Let
`t₁, …, t_r ∈ A₁` be degree-one sections whose nonvanishing opens cover `X`, and
`I = (t₁, …, t_r)`. Assume that at every point `x` of the nonvanishing open `X_{s₁}`

`depth(𝒪_{X, x}) + dim({x}‾) > 1`.

Then a single power of `s₁` kills `H^j_I(A)` for every `j ≤ 2`.

This is the annihilation claim in the proof of [Stacks, Tag 0EL1] at `σ = 1`, for the section ring
itself. The proof is the source's, through Faltings' annihilator theorem [Stacks, Tag 0EFC] as
`Stacks.Algebraization.SectionRingCone.exists_pow_smul_localCohomologyModule_eq_zero_of_depth`:

* every prime of `A` containing `I` contains the irrelevant ideal, because the points of `X` are
  the relevant homogeneous primes of `A` and the `X_{t_i}` cover `X`; in particular such a prime
  contains `s₁`, so `V(I) ⊆ V(s₁)`, and it is a maximal ideal;
* at a prime `𝔭` not containing `s₁` the homogeneous core of `𝔭` is the homogeneous prime of a
  point `x ∈ X_{s₁}`, and the fibre dichotomy of the punctured cone
  (`Stacks.Algebraization.SectionRingCone.depth_add_trdeg_add_one_le_depthAddRelativeDim`) bounds
  `depth(A_𝔭) + dim((A/𝔭)_𝔮)` below by `depth(𝒪_{X,x}) + dim({x}‾) + 1 > 2`.

The local ring and the dimension of the closure at `x` are read on `Proj A` through
`Stacks.Algebraization.SectionRingCone.depth_stalk_eq_depth_atPrime` and
`Stacks.Algebraization.SectionRingCone.dimClosureAt_eq_trdeg_residueField_atPrime`.

## Main results

* `Stacks.Algebraization.SectionRingCone.irrelevant_le_of_span_le` — a prime containing the
  degree-one sections of a cover contains the irrelevant ideal.
* `Stacks.Algebraization.SectionRingCone.exists_pow_smul_localCohomologyModule_sectionRing_eq_zero`
  — the power of `s₁` killing `H^j_I(A)`, `j ≤ 2`.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace HomogeneousLocalization
open Stacks.GradedSections (powSections sectionRing)
open Stacks.AmpleFiniteAvoidance (grading nvOpen)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.AlgebraicGeometry.GradedProperCohomology (specAlgebraRingHom)

universe u

namespace Stacks.Algebraization.SectionRingCone

/-- In the extended integers, a bound `> 1` becomes a bound `> 2` after adding one. -/
theorem two_lt_add_one_of_one_lt {a : EInt} (h : ((1 : ℤ) : EInt) < a) :
    ((2 : ℤ) : EInt) < a + 1 := by
  induction a using WithBotTop.rec with
  | bot => exact absurd h (by simp)
  | top =>
    rw [show ((⊤ : EInt)) + 1 = (⊤ : EInt) from rfl]
    change (WithBot.some (WithTop.some (2 : ℤ))) < (WithBot.some (⊤ : WithTop ℤ))
    exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)
  | coe y =>
    rw [← Stacks.Algebraization.intCast_one_eq_one, ← Stacks.Chow.coe_add_coe_eq_coe_add]
    exact WithBotTop.coe_lt_coe.2 (by have := WithBotTop.coe_lt_coe.1 h; omega)

/-- **Depth of a homogeneous localization at equal primes.** The depths of
`HomogeneousLocalization.AtPrime 𝒜 P` and `HomogeneousLocalization.AtPrime 𝒜 P'` agree when
`P = P'`. -/
theorem depth_atPrime_congr {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {P P' : Ideal A} [P.IsPrime] [P'.IsPrime] (h : P = P') :
    Module.depth (AtPrime 𝒜 P) (IsLocalRing.maximalIdeal (AtPrime 𝒜 P)) (AtPrime 𝒜 P) =
      Module.depth (AtPrime 𝒜 P') (IsLocalRing.maximalIdeal (AtPrime 𝒜 P')) (AtPrime 𝒜 P') := by
  subst h
  rfl

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

attribute [local instance] isPrime_asHomogeneousIdeal_toIdeal

variable (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
  (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- A degree-one element of the section ring lies in the irrelevant ideal. -/
theorem of_one_mem_irrelevant (a : powSections L 1) :
    DirectSum.of (powSections L) 1 a ∈ (HomogeneousIdeal.irrelevant (grading L)).toIdeal :=
  (Stacks.ExternalGrading.mem_irrelevant_iff_degree_zero_eq_zero _).2
    (DirectSum.of_eq_of_ne _ _ _ (by decide))

include g hL in
/-- **A prime containing the degree-one sections of a cover contains the irrelevant ideal.** If
the nonvanishing opens of degree-one sections `t_j` cover `X`, then a prime `q` of the section
ring containing every `t_j` contains `A₊`: otherwise its homogeneous core is the homogeneous prime
of a point `x` of `X`, which lies in some `X_{t_j}`, so `t_j` is outside that core, although `t_j`
is a homogeneous element of `q`. -/
theorem irrelevant_le_of_span_le {r : ℕ} (fam : Fin r → powSections L 1)
    (hcov : ⨆ j, nvOpen L (fam j) = ⊤) (q : Ideal (sectionRing L)) [q.IsPrime]
    (hq : Ideal.span (Set.range fun j => DirectSum.of (powSections L) 1 (fam j)) ≤ q) :
    (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤ q := by
  by_contra hrel
  obtain ⟨x, hx⟩ := exists_asHomogeneousIdeal_eq_homogeneousCore L k g hL q hrel
  have hxmem : x ∈ (⨆ j, nvOpen L (fam j) : X.Opens) := by rw [hcov]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxmem
  refine (mem_nvOpen_iff_notMem_asHomogeneousIdeal L hL one_pos (fam j) x).1 hj ?_
  rw [hx]
  exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem
    ⟨1, Stacks.ExternalGrading.of_mem_summand 1 _⟩ (hq (Ideal.subset_span ⟨j, rfl⟩))

/-- The fibre dichotomy bound of
`Stacks.Algebraization.SectionRingCone.depth_add_trdeg_add_one_le_depthAddRelativeDim`, read at
a prime `P` equal to the homogeneous core of `p`. -/
theorem depth_add_trdeg_add_one_le_depthAddRelativeDim_of_eq
    {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    [IsNoetherianRing A] {k' : Type*} [Field k'] [Algebra k' A] [Algebra.FiniteType k' A]
    (hk : ∀ c : k', algebraMap k' A c ∈ 𝒜 0)
    (p q : PrimeSpectrum A) (hq : q.asIdeal.IsMaximal) (hpq : p.asIdeal ≤ q.asIdeal)
    {f : A} (hf : f ∈ 𝒜 1) (hfp : f ∉ p.asIdeal) (P : Ideal A) [P.IsPrime]
    (hP : coreIdeal 𝒜 p.asIdeal = P) :
    letI := degreeZeroAlgebra 𝒜 hk P.primeCompl
    enatToEInt (Module.depth (AtPrime 𝒜 P) (IsLocalRing.maximalIdeal (AtPrime 𝒜 P))
        (AtPrime 𝒜 P)) +
      krullDimToEInt ((Cardinal.toENat (Algebra.trdeg k'
        (IsLocalRing.ResidueField (AtPrime 𝒜 P))) : WithBot ℕ∞)) + 1 ≤
      depthAddRelativeDim A A p q := by
  subst hP
  exact depth_add_trdeg_add_one_le_depthAddRelativeDim 𝒜 hk p q hq hpq hf hfp

include g hL in
/-- **A power of a degree-one section kills the low-degree local cohomology of the section ring.**
Let `X` be proper over a field `k`, `L` ample and invertible, `s₁` a degree-one section, and
`t_j` degree-one sections whose nonvanishing opens cover `X`, with `I = (t_j)`. If
`depth(𝒪_{X,x}) + dim({x}‾) > 1` at every point of `X_{s₁}`, then some power of `s₁` kills
`H^j_I(A)` for every `j ≤ 2`. -/
theorem exists_pow_smul_localCohomologyModule_sectionRing_eq_zero
    (s₁ : powSections L 1)
    (hdepth : ∀ x : X, x ∈ nvOpen L s₁ →
      enatToEInt (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x)) + krullDimToEInt (dimClosureAt X x) > ((1 : ℤ) : EInt))
    {r : ℕ} (fam : Fin r → powSections L 1) (hcov : ⨆ j, nvOpen L (fam j) = ⊤)
    (hI : (Ideal.span (Set.range fun j => DirectSum.of (powSections L) 1 (fam j))).FG) :
    ∃ c : ℕ, ∀ j : ℤ, j ≤ 2 → ∀ x : Stacks.LocalCohomology.localCohomologyModule (sectionRing L)
        (Ideal.span (Set.range fun j => DirectSum.of (powSections L) 1 (fam j))) hI
        (ModuleCat.of (sectionRing L) (sectionRing L)) j,
      (DirectSum.of (powSections L) 1 s₁) ^ c • x = 0 := by
  let := sectionRingAlgebra L k g
  have := finiteType_sectionRing L k g hL
  have := isNoetherianRing_sectionRing L k g hL
  set I := Ideal.span (Set.range fun j => DirectSum.of (powSections L) 1 (fam j))
  set f := DirectSum.of (powSections L) 1 s₁
  have hk : ∀ c : k, algebraMap k (sectionRing L) c ∈ grading L 0 :=
    sectionRingAlgebra_mem_grading_zero L k g
  have hf1 : f ∈ grading L 1 := Stacks.ExternalGrading.of_mem_summand 1 _
  have hrel : ∀ q ∈ PrimeSpectrum.zeroLocus (I : Set (sectionRing L)),
      (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤ q.asIdeal := fun q hq =>
    irrelevant_le_of_span_le k g L hL fam hcov q.asIdeal hq
  exact exists_pow_smul_localCohomologyModule_eq_zero_of_depth k (sectionRing L)
    (sectionRing L) I hI f
    (fun q hq => Set.singleton_subset_iff.2 (hrel q hq (of_one_mem_irrelevant L s₁))) 2
    (fun p q hfp hq hpq => by
      have hqmax := isMaximal_sectionRing_of_irrelevant_le L k g q.asIdeal (hrel q hq)
      have hpirr : ¬ (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤ p.asIdeal :=
        fun h => hfp (h (of_one_mem_irrelevant L s₁))
      obtain ⟨x, hx⟩ := exists_asHomogeneousIdeal_eq_homogeneousCore L k g hL p.asIdeal hpirr
      have hxs : x ∈ nvOpen L s₁ := by
        refine (mem_nvOpen_iff_notMem_asHomogeneousIdeal L hL one_pos s₁ x).2 ?_
        rw [hx]
        exact fun h => hfp (Ideal.toIdeal_homogeneousCore_le (grading L) p.asIdeal h)
      have hP : coreIdeal (grading L) p.asIdeal =
          ((projHomOfIsAmple L hL) x).asHomogeneousIdeal.toIdeal :=
        congrArg HomogeneousIdeal.toIdeal hx.symm
      have hB := depth_add_trdeg_add_one_le_depthAddRelativeDim_of_eq (grading L) hk p q hqmax
        hpq hf1 hfp _ hP
      let := degreeZeroAlgebra (grading L) hk
        ((projHomOfIsAmple L hL) x).asHomogeneousIdeal.toIdeal.primeCompl
      have h1 := hdepth x hxs
      rw [depth_stalk_eq_depth_atPrime L k g hL x,
        dimClosureAt_eq_trdeg_residueField_atPrime L k g hL x (fun c => rfl)] at h1
      exact (two_lt_add_one_of_one_lt h1).trans_le hB)

end Monoidal

end Stacks.Algebraization.SectionRingCone

end
