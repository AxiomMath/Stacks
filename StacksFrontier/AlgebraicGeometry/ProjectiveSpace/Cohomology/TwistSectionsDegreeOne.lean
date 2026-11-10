module

public import StacksFrontier.AlgebraicGeometry.Cohomology.SectionsSurjective
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneStep.Coproduct
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneStep.Polynomial
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistSectionsFiniteness
public import StacksCore.Tactic.StacksAttribute

/-!
# The twisted global sections of a coherent sheaf on `ℙⁿ_R` are generated in degree one

Let `R` be a Noetherian ring, `n ≥ 0` and `ℱ` a coherent sheaf on `ℙⁿ_R = Proj R[T₀, …, Tₙ]`.
Above some degree every global section of `ℱ(d)` is a combination of global sections of `ℱ(d - 1)`
with linear forms as coefficients. This is the one geometric step
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/TwistSectionsFiniteness.lean` left
standing as the hypothesis `hstep`, and with it **[Stacks, Tag 01YS] clause (5)** — finiteness of
the graded `R[T₀, …, Tₙ]`-module `⨁_{d ≥ k} H⁰(ℙⁿ_R, ℱ(d))` — is proved here.

The argument is the source's. Present `ℱ` as a quotient `φ : ⨁_j 𝒪(dⱼ) ⟶ ℱ` (clause (1) of the
same tag) and let `𝒦 = ker φ`, which is coherent. For `d` large `H¹(ℙⁿ_R, 𝒦(d))` vanishes by
clause (4), so `Γ(ℙⁿ_R, ⨁_j 𝒪(dⱼ)(d)) → Γ(ℙⁿ_R, ℱ(d))` is surjective; the sections of the direct
sum are the sums of the sections of the summands, and for a single twisting sheaf the degree-one
generation is
`Stacks.ProjectiveSpace.Cohomology.exists_sum_homogeneousScalar_twistingSheaf`, valid as soon as
`dⱼ + d ≥ 0`. The degree-one combinations are carried along `φ` because the maps induced on
twisted global sections commute with the graded action of [Stacks, Tag 03GK].

## Main results

* `Stacks.ProjectiveSpace.Cohomology.mem_degreeOneSections_twistingSheaf`: degree-one generation
  for a twisting sheaf on `ℙⁿ_R`, in the subgroup form.
* `Stacks.ProjectiveSpace.Cohomology.surjective_twistedSectionsAddHom_of_isZero_firstCohomology`:
  a surjection of modules whose kernel has vanishing `H¹` after twisting is surjective on twisted
  global sections.
* `Stacks.ProjectiveSpace.Cohomology.exists_forall_mem_degreeOneSections_of_isCoherent`:
  **degree-one generation for a coherent sheaf, in all large degrees.**
* `Stacks.ProjectiveSpace.Cohomology.exists_forall_subset_span_twistedGlobalSectionsGrading`: the
  same read on the graded module, which is the hypothesis `hstep` of
  `Stacks.ProjectiveSpace.Cohomology.moduleFinite_truncation_of_span_grading`.
* `Stacks.ProjectiveSpace.Cohomology.moduleFinite_truncation_of_isCoherent`:
  **[Stacks, Tag 01YS] clause (5).**

## Implementation notes

Surjectivity on global sections is taken from
`Stacks.Cohomology.epi_map_of_isZero_rightDerived_one` at the functor
`SheafOfModules.evaluation (projRingSheaf R n) (op ⊤)` rather than from
`Stacks.Cohomology.surjective_sections_of_isZero_firstCohomology`, which is the same statement read
through `Stacks.Cohomology.sectionsFunctor` of the scheme `ℙⁿ_R` and lands in the abelian-group
spelling `Γ(ℳ, U)` of a section group. The twisted section groups of this development are
`ModuleCat` objects, and staying inside `ModuleCat` is what lets `ModuleCat.epi_iff_surjective`
produce the surjectivity of the very function
`Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.twistedSectionsAddHom` is built from.

The degree is always written `(1 : ℤ) + d`, and the step down from `d` to `d - 1` in `hstep` is
made by substituting `d = 1 + e`: the degree occurs inside the type of a section, so `d - 1` at
the source would need a transport, whereas the *grading* is a submodule of one fixed module and
its degree can be rewritten freely.

## References

* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite DirectSum
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistFunctor (twistFunctor)
open Stacks.AlgebraicGeometry.ProjTwistedSections
open Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep
open Stacks.AlgebraicGeometry.ProjSerreDevissage (isCoherent_of_isBilimit)
open Stacks.ProjectiveCohomology (polyGrading)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

namespace Stacks.ProjectiveSpace.Cohomology

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### Degree-one generation for a twisting sheaf -/

/-- **The twisted global sections of a twisting sheaf on `ℙⁿ_R` are generated in degree one**, in
the subgroup form: for `e + d ≥ 0` every global section of `𝒪(e)(1 + d)` is a combination of
global sections of `𝒪(e)(d)` with linear forms as coefficients. -/
theorem mem_degreeOneSections_twistingSheaf (e d : ℤ) (hed : 0 ≤ e + d)
    (s : twistedSectionsComponent (polyGrading R n)
      (twistingSheaf (polyGrading R n) e) ((1 : ℤ) + d)) :
    s ∈ degreeOneSections (polyGrading R n) (twistingSheaf (polyGrading R n) e) d := by
  obtain ⟨r, a, t, hs⟩ := exists_sum_homogeneousScalar_twistingSheaf R n e d hed s
  rw [hs]
  exact mem_degreeOneSections_of_sum (polyGrading R n)
    (twistingSheaf (polyGrading R n) e) d a t

/-! ### Surjectivity on twisted global sections -/

/-- **Sections of a surjection are surjective where the first cohomology of the kernel
vanishes.** For an epimorphism `φ : 𝒢 ⟶ ℱ` of `𝒪_{ℙⁿ_R}`-modules whose kernel has
`H¹(ℙⁿ_R, (ker φ)(d)) = 0`, the induced map `Γ(ℙⁿ_R, 𝒢(d)) → Γ(ℙⁿ_R, ℱ(d))` is surjective: the
twist of the kernel sequence is short exact because `𝒪(d)` is invertible on `ℙⁿ_R`, and the long
exact sequence of sections then has nothing to obstruct the lift. -/
theorem surjective_twistedSectionsAddHom_of_isZero_firstCohomology
    {F G : SheafOfModules.{u} (projRingSheaf R n)} (φ : G ⟶ F) [Epi φ] (d : ℤ)
    (hz : IsZero (Hgroup (projRingSheaf R n) ⊤ 1
      (twistSheafOfModules (polyGrading R n) (kernel φ) d))) :
    Function.Surjective (twistedSectionsAddHom (polyGrading R n) φ d) := by
  have hse : (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).ShortExact :=
    ShortComplex.shortExact_mk_kernel_ι φ
  have hseT : ((ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).map
      (twistFunctor (polyGrading R n) d)).ShortExact :=
    Stacks.AlgebraicGeometry.TwistFlatness.shortExact_map_twistFunctor_of_adjoin_degree_one
      (polyGrading R n) (Stacks.ProjectiveSpace.SerreVanishing.adjoin_range_one_polyGrading R n)
      d hse
  have hzero : IsZero (((_root_.SheafOfModules.evaluation.{u} (projRingSheaf R n)
        (op (⊤ : Opens (ProjectiveSpectrum.top (polyGrading R n))))).rightDerived 1).obj
        ((ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).map
          (twistFunctor (polyGrading R n) d)).X₁) :=
    (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      (projRingSheaf R n) ⊤ 1
      (twistSheafOfModules (polyGrading R n) (kernel φ) d)).mpr hz
  have hepi := Stacks.Cohomology.epi_map_of_isZero_rightDerived_one
    (_root_.SheafOfModules.evaluation.{u} (projRingSheaf R n)
      (op (⊤ : Opens (ProjectiveSpectrum.top (polyGrading R n))))) hseT hzero
  exact (ModuleCat.epi_iff_surjective _).1 hepi

/-! ### Degree-one generation for a coherent sheaf -/

/-- **The twisted global sections of a coherent sheaf on `ℙⁿ_R` are generated in degree one in all
large degrees.** There is a `B` such that for every `d ≥ B` each global section of `ℱ(1 + d)` is a
combination of global sections of `ℱ(d)` with linear forms as coefficients.

This is the source's argument: a presentation `φ : ⨁_j 𝒪(dⱼ) ⟶ ℱ` by twists (clause (1)), the
eventual vanishing of `H¹` of the twists of the coherent kernel (clause (4)), the degree-one
generation of each `𝒪(dⱼ)` above `-dⱼ`, and additivity over the finite direct sum. -/
theorem exists_forall_mem_degreeOneSections_of_isCoherent [IsNoetherianRing R]
    (F : SheafOfModules.{u} (projRingSheaf R n))
    (hF : _root_.SheafOfModules.IsCoherent F) :
    ∃ B : ℤ, ∀ d : ℤ, B ≤ d →
      ∀ s : twistedSectionsComponent (polyGrading R n) F ((1 : ℤ) + d),
        s ∈ degreeOneSections (polyGrading R n) F d := by
  classical
  obtain ⟨r, dj, b, hb, φ, hφ⟩ :=
    Stacks.ProjectiveSpace.SerreVanishing.hasTwistQuotients_polyGrading R n F hF
  have : Epi φ := hφ
  have hpt : _root_.SheafOfModules.IsCoherent b.pt :=
    isCoherent_of_isBilimit (polyGrading R n) hb
      fun j => isCoherent_twistingSheaf_polyGrading R n (dj j)
  have hFc : _root_.SheafOfModules.IsCoherent F := hF
  have hker : _root_.SheafOfModules.IsCoherent (kernel φ) :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_kernel φ
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.ProjectiveSpace.SerreVanishing.exists_isZero_Hgroup_twist_of_isCoherent R n 1
      Nat.one_pos (kernel φ) hker
  refine ⟨max d₀ (∑ j : Fin r, max (-(dj j)) 0), fun d hd s => ?_⟩
  have hd₀d : d₀ ≤ (1 : ℤ) + d := by
    have := le_trans (le_max_left d₀ (∑ j : Fin r, max (-(dj j)) 0)) hd
    omega
  have hdj : ∀ j : Fin r, 0 ≤ dj j + d := by
    intro j
    have h1 : max (-(dj j)) 0 ≤ ∑ k : Fin r, max (-(dj k)) 0 :=
      Finset.single_le_sum (f := fun k : Fin r => max (-(dj k)) 0)
        (fun k _ => le_max_right (-(dj k)) 0) (Finset.mem_univ j)
    have h2 : -(dj j) ≤ max (-(dj j)) 0 := le_max_left _ _
    have h3 : (∑ k : Fin r, max (-(dj k)) 0) ≤ d :=
      le_trans (le_max_right d₀ (∑ k : Fin r, max (-(dj k)) 0)) hd
    omega
  obtain ⟨s', rfl⟩ := surjective_twistedSectionsAddHom_of_isZero_firstCohomology R n φ
    ((1 : ℤ) + d) (hd₀ ((1 : ℤ) + d) hd₀d) s
  exact map_mem_degreeOneSections (polyGrading R n) φ d
    (mem_degreeOneSections_of_isBilimit (polyGrading R n) hb d
      (fun j z => mem_degreeOneSections_twistingSheaf R n (dj j) d (hdj j) z) s')

/-! ### Clause (5) -/

section AnyGrading

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- A degree-one combination of sections of `ℱ(d)` lies, as a homogeneous element of
`⨁_{m ∈ ℤ} Γ(Proj 𝒮, ℱ(m))`, in the `S`-span of the degree-`d` piece: the characterizing
formula `TwistedGlobalSectionsModule.smul_homogeneous` identifies the graded action of
[Stacks, Tag 03GK] on sections with multiplication by a degree-one element in the graded module.

Nothing here is special to `ℙⁿ_R`; the statement is for an arbitrary graded ring, which is what
`Stacks.Blowup.exists_forall_subset_span_twistedGlobalSectionsGrading_reesGrading` needs on the
blowup. -/
theorem mem_span_grading_of_mem_degreeOneSections
    (F : SheafOfModules.{u}
      (Stacks.AlgebraicGeometry.ProjTwistFunctor.projRingSheaf 𝒮))
    (D : TwistedGlobalSectionsModule 𝒮 F) (d : ℤ)
    {s : twistedSectionsComponent 𝒮 F ((1 : ℤ) + d)}
    (hs : s ∈ degreeOneSections 𝒮 F d) :
    letI := D.moduleInst
    (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m)
        ((1 : ℤ) + d) s : twistedGlobalSections 𝒮 F) ∈
      Submodule.span S (twistedGlobalSectionsGrading 𝒮 F d :
        Set (twistedGlobalSections 𝒮 F)) := by
  let := D.moduleInst
  refine (AddSubgroup.closure_le (AddSubgroup.comap
    (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((1 : ℤ) + d))
    (Submodule.span S (twistedGlobalSectionsGrading 𝒮 F d :
      Set (twistedGlobalSections 𝒮 F))).toAddSubgroup)).mpr ?_ hs
  rintro x ⟨a, t, rfl⟩
  refine AddSubgroup.mem_comap.mpr ?_
  change (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((1 : ℤ) + d)
      (homogeneousScalarTwistedSections 𝒮 F 1 d a t)) ∈
    Submodule.span S (twistedGlobalSectionsGrading 𝒮 F d :
      Set (twistedGlobalSections 𝒮 F))
  have hmem : (a : S) •
      (DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) d t :
        twistedGlobalSections 𝒮 F) ∈
      Submodule.span S (twistedGlobalSectionsGrading 𝒮 F d :
        Set (twistedGlobalSections 𝒮 F)) :=
    Submodule.smul_mem _ _ (Submodule.subset_span ((DirectSum.mem_rangeGrading ℤ
      (fun m : ℤ => twistedSectionsComponent 𝒮 F m) d _).mpr ⟨t, rfl⟩))
  rw [D.smul_homogeneous 1 d a t] at hmem
  exact hmem

/-- **Degree-one generation of the sections, read on the graded module.** If above a degree `B`
every section of `ℱ(1 + d)` is a degree-one combination of sections of `ℱ(d)`, then above `B`
every homogeneous piece of `⨁_{m ∈ ℤ} Γ(Proj 𝒮, ℱ(m))` lies in the `S`-span of the piece one
degree below. This is the hypothesis `hstep` of
`Stacks.AlgebraicGeometry.ProjTwistedSections.moduleFinite_twistedGlobalSectionsTruncation`.

The step down from `d` to `d - 1` is made by substituting `d = 1 + e`: the degree occurs inside
the type of a section, so `d - 1` at the source would need a transport, whereas the *grading* is a
submodule of one fixed module and its degree can be rewritten freely.

Nothing here is special to `ℙⁿ_R` either; the graded ring is arbitrary, which is what
`Stacks.Blowup.exists_forall_subset_span_twistedGlobalSectionsGrading_reesGrading` needs. -/
theorem subset_span_grading_of_forall_mem_degreeOneSections
    (F : SheafOfModules.{u}
      (Stacks.AlgebraicGeometry.ProjTwistFunctor.projRingSheaf 𝒮))
    (D : TwistedGlobalSectionsModule 𝒮 F) (B : ℤ)
    (hB : ∀ d : ℤ, B ≤ d → ∀ s : twistedSectionsComponent 𝒮 F ((1 : ℤ) + d),
      s ∈ degreeOneSections 𝒮 F d) :
    letI := D.moduleInst
    ∀ d : ℤ, B < d →
      (twistedGlobalSectionsGrading 𝒮 F d : Set (twistedGlobalSections 𝒮 F)) ⊆
        Submodule.span S (twistedGlobalSectionsGrading 𝒮 F (d - 1) :
          Set (twistedGlobalSections 𝒮 F)) := by
  let := D.moduleInst
  intro d hd
  obtain ⟨e, rfl⟩ : ∃ e : ℤ, d = 1 + e := ⟨d - 1, by ring⟩
  have hsub : (1 : ℤ) + e - 1 = e := by ring
  rw [hsub]
  intro x hx
  obtain ⟨s, rfl⟩ := (DirectSum.mem_rangeGrading ℤ
    (fun m : ℤ => twistedSectionsComponent 𝒮 F m) ((1 : ℤ) + e) x).mp hx
  exact mem_span_grading_of_mem_degreeOneSections 𝒮 F D e (hB e (by omega) s)

end AnyGrading

/-- **The hypothesis `hstep` of
`Stacks.ProjectiveSpace.Cohomology.moduleFinite_truncation_of_span_grading`, discharged.** For
`ℱ` coherent on `ℙⁿ_R` over a Noetherian ring there is a `B` such that above it every homogeneous
piece of `⨁_{m ∈ ℤ} Γ(ℙⁿ_R, ℱ(m))` lies in the `R[T₀, …, Tₙ]`-span of the piece one degree
below. -/
theorem exists_forall_subset_span_twistedGlobalSectionsGrading [IsNoetherianRing R]
    (F : SheafOfModules.{u} (projRingSheaf R n))
    (hF : _root_.SheafOfModules.IsCoherent F)
    (D : TwistedGlobalSectionsModule (polyGrading R n) F) :
    ∃ B : ℤ, letI := D.moduleInst
      ∀ d : ℤ, B < d →
        (twistedGlobalSectionsGrading (polyGrading R n) F d :
            Set (twistedGlobalSections (polyGrading R n) F)) ⊆
          Submodule.span (MvPolynomial (Fin (n + 1)) R)
            (twistedGlobalSectionsGrading (polyGrading R n) F (d - 1) :
              Set (twistedGlobalSections (polyGrading R n) F)) := by
  obtain ⟨B, hB⟩ := exists_forall_mem_degreeOneSections_of_isCoherent R n F hF
  exact ⟨B, subset_span_grading_of_forall_mem_degreeOneSections (polyGrading R n) F D B hB⟩

/-- **[Stacks, Tag 01YS] clause (5).** Let `R` be a Noetherian ring, `n ≥ 0` and `ℱ` a coherent
sheaf on `ℙⁿ_R = Proj R[T₀, …, Tₙ]`. For every `k ∈ ℤ` the graded `R[T₀, …, Tₙ]`-module
`⨁_{d ≥ k} H⁰(ℙⁿ_R, ℱ(d))` is a finite `R[T₀, …, Tₙ]`-module.

The proof is the source's sandwich, now with both halves available: each homogeneous piece
`Γ(ℙⁿ_R, ℱ(d))` is a finite `R`-module by clause (3) at `i = 0`, and above some degree every
piece lies in the span of the piece one degree below
(`exists_forall_subset_span_twistedGlobalSectionsGrading`), so finitely many pieces generate. -/
@[stacks 01YS "(5) finiteness of the graded module of twisted global sections",
  sga "2 XII 5.3" "clause (a), case i = 0"]
theorem moduleFinite_truncation_of_isCoherent [IsNoetherianRing R]
    (F : SheafOfModules.{u} (projRingSheaf R n))
    (hF : _root_.SheafOfModules.IsCoherent F)
    (D : TwistedGlobalSectionsModule (polyGrading R n) F) (k : ℤ) :
    letI := D.moduleInst
    Module.Finite (MvPolynomial (Fin (n + 1)) R)
      (TwistedGlobalSectionsModule.truncation (polyGrading R n) F D k) := by
  obtain ⟨B, hB⟩ := exists_forall_subset_span_twistedGlobalSectionsGrading R n F hF D
  exact moduleFinite_truncation_of_span_grading R n F hF D k B hB

/-- **[Stacks, Tag 01YS] clause (5) at the canonical graded module.** The same statement for the
`R[T₀, …, Tₙ]`-module structure of
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsModule`, which is the one
[Stacks, Tag 03GK] constructs. -/
theorem moduleFinite_truncation_twistedGlobalSectionsModule [IsNoetherianRing R]
    (F : SheafOfModules.{u} (projRingSheaf R n))
    (hF : _root_.SheafOfModules.IsCoherent F) (k : ℤ) :
    letI := (Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsModule
      (polyGrading R n) F).moduleInst
    Module.Finite (MvPolynomial (Fin (n + 1)) R)
      (TwistedGlobalSectionsModule.truncation (polyGrading R n) F
        (Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsModule
      (polyGrading R n) F) k) :=
  moduleFinite_truncation_of_isCoherent R n F hF
    (Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsModule
      (polyGrading R n) F) k

end Stacks.ProjectiveSpace.Cohomology

end
