module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRegularity
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRestrictionCanonical
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneSequenceCoherent

/-!
# Castelnuovo–Mumford regularity of the restriction to a hyperplane

Let `k` be a field, `n ≥ 1`, `ℱ` a coherent sheaf on `ℙⁿ_k` and `s` a global section of `𝒪(1)`
vanishing at no associated point of `ℱ`. Write `i : H ⟶ ℙⁿ_k` for the hyperplane cut out by `s`
and `𝒢 = i^*ℱ`. [Stacks, Tag 08A5] says that if `ℱ` is `m`-regular then `𝒢` is `m`-regular on
`H ≅ ℙ^{n-1}_k`. This file proves it for that hyperplane, with `𝒢` the restriction itself.

## Main results

* `AlgebraicGeometry.isMRegular_pullback_hyperplaneι_of_nonvanishing`: for **every** section `s`
  of `𝒪(1)` vanishing at no associated point of `ℱ`, every identification `φ : ℙ^{n-1}_k ≅ H`
  and every identification `θ1` of `𝒪(1)` along it, `m`-regularity of `ℱ` gives `m`-regularity
  of `(φ ≫ i)^*ℱ = φ^*𝒢` on `ℙ^{n-1}_k`. No hypothesis on `k`.
* `AlgebraicGeometry.isMRegular_hyperplaneRestriction_of_nonvanishing`: **[Stacks, Tag 08A5]**,
  in the situation of [Stacks, Tag 08A0]. For **every** nonzero section `s` of `𝒪(1)` vanishing
  at no associated point of `ℱ`: the sequence `0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_*i^*ℱ ⟶ 0` of Tag 08A0 is
  short exact, its hyperplane is `ℙ^{n-1}_k` as in [Stacks, Tag 089Z], and along every such
  identification the restriction of an `m`-regular `ℱ` is `m`-regular.
* `AlgebraicGeometry.exists_hyperplane_isMRegular_pullback`: over an infinite field such a
  section exists, which is the existence half of [Stacks, Tag 08A0].

## The mathematics

The proof of the source is the long exact cohomology sequence of the twisted restriction
sequences `0 ⟶ ℱ(d-1) ⟶ ℱ(d) ⟶ i_*𝒢(d) ⟶ 0`; that argument is
`AlgebraicGeometry.isMRegular_of_hyperplaneRestriction`, which takes the sequences as its input
`AlgebraicGeometry.HasHyperplaneRestrictionSequences`. Here they are **built** for the hyperplane
of `s`, with `𝒢` the restriction of `ℱ`:

* the sequence in degree `d` is `AlgebraicGeometry.exists_shortExact_twistSectionMul_unit` at
  `d - 1`: multiplication by `s` is injective on `ℱ(d-1)` because `s` vanishes at no associated
  point of `ℱ(d-1)`, these being those of `ℱ`
  (`AlgebraicGeometry.associatedPoints_projectiveTwist`), and its cokernel is `j_*j^*(ℱ(d))`
  for `j = φ ≫ i`;
* `j^*(ℱ(d)) ≅ (j^*ℱ)(d)` is `AlgebraicGeometry.pullbackTwistIso`, the comparison of
  [Stacks, Tag 01CD] followed by the identification `j^*𝒪(d) ≅ 𝒪(d)` that
  `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTwistOverIso` builds from `θ1`.

Over an infinite field the section is `AlgebraicGeometry.exists_form_section_nonvanishing`, the
choice of [Stacks, Tag 08A0], and the identification of its hyperplane with `ℙ^{n-1}_k`, with
`θ1`, is `AlgebraicGeometry.exists_iso_zeroScheme_projectiveSpaceOverRing`
([Stacks, Tag 089Z]).

## References

* [Stacks Project, Tag 08A5](https://stacks.math.columbia.edu/tag/08A5)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 089Z](https://stacks.math.columbia.edu/tag/089Z)
* [Stacks Project, Tag 0EGK](https://stacks.math.columbia.edu/tag/0EGK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.ProjectiveCohomology (polyGrading)

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra
  Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

open CategoryTheory.MonoidalCategory
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication
open Stacks.AlgebraicGeometry.ProjectiveSpaceHyperplaneSection
  (shortExact_hyperplaneUnit_of_nonvanishing)

/-- Projective space over a field is locally Noetherian. -/
private theorem isLocallyNoetherian_projectiveSpaceOverRing (k : Type u) [Field k] (n : ℕ) :
    IsLocallyNoetherian (projectiveSpaceOverRing n (CommRingCat.of k)) :=
  projectiveSpaceOver_isLocallyNoetherian n (Spec (CommRingCat.of k))

/-- The two spellings of the nonvanishing locus of a section of `𝒪(1)` agree. -/
private theorem nonvanishingLocus_eq_ample_nonvanishingLocus (k : Type u) [Field k] (n : ℕ)
    (s : (twistOver n (Spec (CommRingCat.of k)) 1).sections) :
    Stacks.SheafOfModules.nonvanishingLocus (twistOver n (Spec (CommRingCat.of k)) 1) s
      = Stacks.Ample.nonvanishingLocus (twistOver n (Spec (CommRingCat.of k)) 1)
        (PresheafOfModules.sections.eval s (op ⊤)) :=
  Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq
    (projectiveSpaceOverRing n (CommRingCat.of k))
    (twistOver n (Spec (CommRingCat.of k)) 1) s

/-- A section of `𝒪(1)` vanishing at no associated point of `ℱ` is nonvanishing on an open
neighbourhood of every associated point of each twist `ℱ(d)`. -/
theorem exists_opens_subset_nonvanishingLocus_of_associatedPoints_subset (k : Type u) [Field k]
    (n : ℕ) (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
    (s : (twistOver n (Spec (CommRingCat.of k)) 1).sections)
    (hs : Stacks.Divisors.associatedPoints F ⊆
      Stacks.SheafOfModules.nonvanishingLocus (twistOver n (Spec (CommRingCat.of k)) 1) s)
    (d : ℤ) :
    ∀ x ∈ Stacks.Divisors.associatedPoints
      (Stacks.RelativeVeryAmple.tensorModules
        (projectiveSpaceOverRing n (CommRingCat.of k)) F
        (twistOver n (Spec (CommRingCat.of k)) d)),
      ∃ W : (projectiveSpaceOverRing n (CommRingCat.of k)).Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (twistOver n (Spec (CommRingCat.of k)) 1) s := by
  have hnv := nonvanishingLocus_eq_ample_nonvanishingLocus k n s
  intro x hx
  have hA : Stacks.Divisors.associatedPoints
      (Stacks.RelativeVeryAmple.tensorModules
        (projectiveSpaceOverRing n (CommRingCat.of k)) F
        (twistOver n (Spec (CommRingCat.of k)) d))
      = Stacks.Divisors.associatedPoints F :=
    associatedPoints_projectiveTwist n F d
  have hx' : x ∈ Stacks.Ample.nonvanishingLocus
      (twistOver n (Spec (CommRingCat.of k)) 1)
      (PresheafOfModules.sections.eval s (op ⊤)) := by
    rw [← hnv]
    exact hs (hA.subset hx)
  refine ⟨Stacks.NonvanishingOpen.nonvanishingOpen
    (projectiveSpaceOverRing n (CommRingCat.of k))
    (twistOver n (Spec (CommRingCat.of k)) 1)
    (PresheafOfModules.sections.eval s (op ⊤)), hx', fun y hy => ?_⟩
  rw [hnv]
  exact hy

/-- For a section `s` of `𝒪(1)` vanishing at no associated point of a coherent `ℱ` on `ℙⁿ_k`, the
sequence `0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_*i^*ℱ ⟶ 0` of [Stacks, Tag 08A0] is short exact. -/
theorem exists_shortExact_hyperplaneUnit_of_associatedPoints_subset (k : Type u) [Field k]
    (n : ℕ) (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) [F.IsCoherent]
    (s : (twistOver n (Spec (CommRingCat.of k)) 1).sections)
    (hs : Stacks.Divisors.associatedPoints F ⊆
      Stacks.SheafOfModules.nonvanishingLocus (twistOver n (Spec (CommRingCat.of k)) 1) s) :
    ∃ w : twistSectionMulNegOne n (Spec (CommRingCat.of k)) F s ≫
        hyperplaneUnit n (Spec (CommRingCat.of k)) F s = 0,
      (ShortComplex.mk (twistSectionMulNegOne n (Spec (CommRingCat.of k)) F s)
        (hyperplaneUnit n (Spec (CommRingCat.of k)) F s) w).ShortExact := by
  have : IsLocallyNoetherian (projectiveSpaceOverRing n (CommRingCat.of k)) :=
    projectiveSpaceOver_isLocallyNoetherian n (Spec (CommRingCat.of k))
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : (projectiveTwist n F (-1)).IsCoherent := isCoherent_projectiveTwist n F (-1)
  have : (projectiveTwist n F (-1)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have := isQuasicoherent_tensorModules_twistOver_tensor k n F (-1)
  exact shortExact_hyperplaneUnit_of_nonvanishing n (Spec (CommRingCat.of k)) F s
    (exists_opens_subset_nonvanishingLocus_of_associatedPoints_subset k n F s hs (-1))

/-- **The restriction of an `m`-regular sheaf to a hyperplane avoiding its associated points is
`m`-regular.** Let `k` be a field, `n ≥ 1`, `ℱ` a coherent sheaf on `ℙⁿ_k` and `s` a global
section of `𝒪(1)` vanishing at no associated point of `ℱ`; let `i : H ⟶ ℙⁿ_k` be the hyperplane
of `s`, `φ : ℙ^{n-1}_k ≅ H` an identification and `θ1 : (φ ≫ i)^*𝒪(1) ≅ 𝒪(1)` one of the
degree-one twists along it. If `ℱ` is `m`-regular then so is `(φ ≫ i)^*ℱ`, the restriction
`i^*ℱ` read on `ℙ^{n-1}_k` through `φ`.

The restriction sequences `0 ⟶ ℱ(d-1) ⟶ ℱ(d) ⟶ (φ ≫ i)_*((φ ≫ i)^*ℱ)(d) ⟶ 0` are
`AlgebraicGeometry.exists_shortExact_twistSectionMul_unit` at `d - 1`, the condition on `s` being
the same in every degree because twisting does not change associated points, with its third term
rewritten by `AlgebraicGeometry.pullbackTwistIso`; the cohomological argument is
`AlgebraicGeometry.isMRegular_of_hyperplaneRestriction`. -/
theorem isMRegular_pullback_hyperplaneι_of_nonvanishing (k : Type u) [Field k] (n : ℕ)
    (hn : 1 ≤ n) (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) [F.IsCoherent]
    (s : (twistOver n (Spec (CommRingCat.of k)) 1).sections)
    (hs : Stacks.Divisors.associatedPoints F ⊆
      Stacks.SheafOfModules.nonvanishingLocus (twistOver n (Spec (CommRingCat.of k)) 1) s)
    (φ : projectiveSpaceOverRing (n - 1) (CommRingCat.of k) ≅
      (hyperplane n (Spec (CommRingCat.of k)) s).subscheme)
    (θ1 : (Scheme.Modules.pullback (φ.hom ≫ hyperplaneι n (Spec (CommRingCat.of k)) s)).obj
        (twistOver n (Spec (CommRingCat.of k)) 1) ≅
      twistOver (n - 1) (Spec (CommRingCat.of k)) 1)
    (m : ℤ) (hF : IsMRegular k n F m) :
    haveI := projectiveSpaceOver_isLocallyNoetherian (n - 1) (Spec (CommRingCat.of k))
    haveI := isCoherent_pullback (φ.hom ≫ hyperplaneι n (Spec (CommRingCat.of k)) s) F
    IsMRegular k (n - 1)
      ((Scheme.Modules.pullback (φ.hom ≫ hyperplaneι n (Spec (CommRingCat.of k)) s)).obj F) m := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have := isLocallyNoetherian_projectiveSpaceOverRing k (p + 1)
  have := isLocallyNoetherian_projectiveSpaceOverRing k p
  set i := hyperplaneι (p + 1) (Spec (CommRingCat.of k)) s with hi
  set j : projectiveSpaceOverRing p (CommRingCat.of k) ⟶
      projectiveSpaceOverRing (p + 1) (CommRingCat.of k) := φ.hom ≫ i with hj
  have : IsAffineHom j := by
    rw [hj]
    infer_instance
  have : ((Scheme.Modules.pullback j).obj F).IsCoherent := isCoherent_pullback j F
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hq1 : ∀ d : ℤ, (projectiveTwist (p + 1) F d).IsQuasicoherent := by
    intro d
    have : (projectiveTwist (p + 1) F d).IsCoherent := isCoherent_projectiveTwist (p + 1) F d
    exact isQuasicoherent_of_isCoherent _
  have hses : HasHyperplaneRestrictionSequences (p + 1) F
      ((Scheme.Modules.pullback j).obj F) j := by
    intro d
    have := hq1 (d - 1)
    have := isQuasicoherent_tensorModules_twistOver_tensor k (p + 1) F (d - 1)
    obtain ⟨w0, hSE⟩ := exists_shortExact_twistSectionMul_unit (p + 1)
      (Spec (CommRingCat.of k)) F s (d - 1)
      (exists_opens_subset_nonvanishingLocus_of_associatedPoints_subset k (p + 1) F s hs (d - 1)) φ
    exact exists_shortExact_of_objIso hSE (Iso.refl _)
      (eqToIso (congrArg (projectiveTwist (p + 1) F) (show d - 1 + 1 = d by ring)))
      ((Scheme.Modules.pushforward j).mapIso (pullbackTwistIso j F
          (Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTwistOverIso p
            (Spec (CommRingCat.of k)) i φ θ1) (d - 1 + 1)) ≪≫
        eqToIso (congrArg (fun e => (Scheme.Modules.pushforward j).obj
          (projectiveTwist p ((Scheme.Modules.pullback j).obj F) e))
          (show d - 1 + 1 = d by ring)))
  exact isMRegular_of_hyperplaneRestriction k (p + 1) hn F m
    ((Scheme.Modules.pullback j).obj F) j hses hF

/-- **[Stacks, Tag 08A5] together with the existence of its hyperplane.** Let `k` be an infinite
field, `n ≥ 1` and `ℱ` a coherent sheaf on `ℙⁿ_k`. Then the situation of [Stacks, Tag 08A0]
exists — and in it Tag 08A5 holds, by
`AlgebraicGeometry.isMRegular_hyperplaneRestriction_of_nonvanishing`: a nonzero global section `s`
of `𝒪(1)`, chosen to vanish at no associated point of `ℱ`, for which the sequence

`0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_*𝒢 ⟶ 0`,   `i : H ⟶ ℙⁿ_k` the hyperplane of `s`, `𝒢 = i^*ℱ`,

is short exact, its arrows being multiplication by `s`
(`…ProjectiveSpaceSectionMultiplication.twistSectionMulNegOne`) and restriction to `H`
(`…ProjectiveSpaceSectionMultiplication.hyperplaneUnit`). Then there is an identification
`φ : ℙ^{n-1}_k ≅ H` ([Stacks, Tag 089Z]) such that, for every `m`, if `ℱ` is `m`-regular then
`𝒢` is `m`-regular on `H ≅ ℙ^{n-1}_k`, i.e. `φ^*𝒢 = (φ ≫ i)^*ℱ` is `m`-regular on `ℙ^{n-1}_k`.

The section is `AlgebraicGeometry.exists_form_section_nonvanishing`, the choice of
[Stacks, Tag 08A0] and the only place where `k` has to be infinite; the sequence is
`…ProjectiveSpaceHyperplaneSection.shortExact_hyperplaneUnit_of_nonvanishing`; `φ` and the
degree-one twist along it are `AlgebraicGeometry.exists_iso_zeroScheme_projectiveSpaceOverRing`;
and the regularity is `AlgebraicGeometry.isMRegular_pullback_hyperplaneι_of_nonvanishing`, which
holds for every section avoiding the associated points of `ℱ` and every identification of its
hyperplane, over any field. -/
theorem exists_hyperplane_isMRegular_pullback (k : Type u) [Field k] [Infinite k] (n : ℕ)
    (hn : 1 ≤ n) (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) [F.IsCoherent] :
    ∃ s : (twistOver n (Spec (CommRingCat.of k)) 1).sections,
      PresheafOfModules.sections.eval s (op ⊤) ≠ 0 ∧
      Stacks.Divisors.associatedPoints F ⊆
        Stacks.SheafOfModules.nonvanishingLocus (twistOver n (Spec (CommRingCat.of k)) 1) s ∧
      (∃ w : twistSectionMulNegOne n (Spec (CommRingCat.of k)) F s ≫
          hyperplaneUnit n (Spec (CommRingCat.of k)) F s = 0,
        (ShortComplex.mk (twistSectionMulNegOne n (Spec (CommRingCat.of k)) F s)
          (hyperplaneUnit n (Spec (CommRingCat.of k)) F s) w).ShortExact) ∧
      ∃ φ : projectiveSpaceOverRing (n - 1) (CommRingCat.of k) ≅
          (hyperplane n (Spec (CommRingCat.of k)) s).subscheme,
        ∀ m : ℤ, IsMRegular k n F m →
          haveI := projectiveSpaceOver_isLocallyNoetherian (n - 1) (Spec (CommRingCat.of k))
          haveI := isCoherent_pullback (φ.hom ≫ hyperplaneι n (Spec (CommRingCat.of k)) s) F
          IsMRegular k (n - 1)
            ((Scheme.Modules.pullback
              (φ.hom ≫ hyperplaneι n (Spec (CommRingCat.of k)) s)).obj F) m := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have := isLocallyNoetherian_projectiveSpaceOverRing k (p + 1)
  obtain ⟨f, hf, v, hf0, hv, hsub⟩ := exists_form_section_nonvanishing k (p + 1) F
  set s := (Stacks.NonvanishingSpelling.sectionsEquiv
    (projectiveSpaceOverRing (p + 1) (CommRingCat.of k))
    (twistOver (p + 1) (Spec (CommRingCat.of k)) 1)).symm v with hs
  have hsv : PresheafOfModules.sections.eval s (op ⊤) = v := by
    rw [hs, ← Stacks.NonvanishingSpelling.sectionsEquiv_apply, Equiv.apply_symm_apply]
  rw [← hsv] at hv hsub
  have hnv := nonvanishingLocus_eq_ample_nonvanishingLocus k (p + 1) s
  have hsF : Stacks.Divisors.associatedPoints F ⊆
      Stacks.SheafOfModules.nonvanishingLocus
        (twistOver (p + 1) (Spec (CommRingCat.of k)) 1) s := by
    rwa [hnv]
  obtain ⟨w, hSE⟩ := exists_shortExact_hyperplaneUnit_of_associatedPoints_subset k (p + 1) F s hsF
  obtain ⟨φ, ⟨eφ⟩, -⟩ := exists_iso_zeroScheme_projectiveSpaceOverRing k p f hf hf0
    (PresheafOfModules.sections.eval s (op ⊤)) hv
  refine ⟨s, ?_, hsF, ⟨w, hSE⟩, φ, fun m hF => ?_⟩
  · intro h0
    refine degreeSection_one_ne_zero k (p + 1) hf hf0 ?_
    rw [← hv, h0]
    exact map_zero _
  · exact isMRegular_pullback_hyperplaneι_of_nonvanishing k (p + 1) hn F s hsF φ eφ m hF

/-- **[Stacks, Tag 08A5].** Let `k` be a field, `n ≥ 1`, `ℱ` a coherent sheaf on `ℙⁿ_k`, and let
`s` be a **nonzero** global section of `𝒪(1)` vanishing at no associated point of `ℱ` — the
hyperplane section of [Stacks, Tag 08A0], which over an infinite field always exists
(`AlgebraicGeometry.exists_hyperplane_isMRegular_pullback`). Write `i : H ⟶ ℙⁿ_k` for its
hyperplane and `𝒢 = i^*ℱ`. Then

* the sequence `0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_*𝒢 ⟶ 0` of Tag 08A0 is short exact, its arrows being
  multiplication by `s` and restriction to `H`;
* `H ≅ ℙ^{n-1}_k` as in [Stacks, Tag 089Z]: there is an identification `φ : ℙ^{n-1}_k ≅ H`, over
  `Spec k`, along which `𝒪(1)` restricts to `𝒪(1)`;
* and, for **every** such identification `φ` (one along which `𝒪(1)` restricts to `𝒪(1)`) and
  every `m`, if `ℱ` is `m`-regular then `𝒢` is `m`-regular on `H ≅ ℙ^{n-1}_k`, that is
  `φ^*𝒢 = (φ ≫ i)^*ℱ` is `m`-regular on `ℙ^{n-1}_k`.

The identification of Tag 089Z is not unique — it depends on a choice of coordinates on the
hyperplane — so the regularity is asserted for all of them rather than for one. The field need
not be infinite once `s` is given: that hypothesis of Tag 08A0 is used only to choose `s`.

The sequence is `…ProjectiveSpaceHyperplaneSection.shortExact_hyperplaneUnit_of_nonvanishing`;
the identification is `AlgebraicGeometry.exists_iso_zeroScheme_projectiveSpaceOverRing` applied
to the degree-one form presenting
`s` (`Stacks.ProjectiveSpace.Cohomology.exists_degreeSection_eq`); the regularity is
`AlgebraicGeometry.isMRegular_pullback_hyperplaneι_of_nonvanishing`. -/
@[stacks 08A5 "in the situation of Tag 08A0, for every nonzero section s of O(1) avoiding the \
associated points of F: the sequence of Tag 08A0 is short exact, H(s) ≅ P^{n-1}_k as in Tag 089Z, \
and along every such identification the restriction of an m-regular F is m-regular"]
theorem isMRegular_hyperplaneRestriction_of_nonvanishing (k : Type u) [Field k] (n : ℕ)
    (hn : 1 ≤ n) (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) [F.IsCoherent]
    (s : (twistOver n (Spec (CommRingCat.of k)) 1).sections)
    (hs0 : PresheafOfModules.sections.eval s (op ⊤) ≠ 0)
    (hs : Stacks.Divisors.associatedPoints F ⊆
      Stacks.SheafOfModules.nonvanishingLocus (twistOver n (Spec (CommRingCat.of k)) 1) s) :
    (∃ w : twistSectionMulNegOne n (Spec (CommRingCat.of k)) F s ≫
          hyperplaneUnit n (Spec (CommRingCat.of k)) F s = 0,
        (ShortComplex.mk (twistSectionMulNegOne n (Spec (CommRingCat.of k)) F s)
          (hyperplaneUnit n (Spec (CommRingCat.of k)) F s) w).ShortExact) ∧
      (∃ φ : projectiveSpaceOverRing (n - 1) (CommRingCat.of k) ≅
          (hyperplane n (Spec (CommRingCat.of k)) s).subscheme,
        Nonempty ((Scheme.Modules.pullback
            (φ.hom ≫ hyperplaneι n (Spec (CommRingCat.of k)) s)).obj
              (twistOver n (Spec (CommRingCat.of k)) 1) ≅
            twistOver (n - 1) (Spec (CommRingCat.of k)) 1) ∧
          φ.hom ≫ hyperplaneι n (Spec (CommRingCat.of k)) s ≫
              (projectiveSpaceOverRing n (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) =
            projectiveSpaceOverRing (n - 1) (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) ∧
      ∀ φ : projectiveSpaceOverRing (n - 1) (CommRingCat.of k) ≅
          (hyperplane n (Spec (CommRingCat.of k)) s).subscheme,
        Nonempty ((Scheme.Modules.pullback
            (φ.hom ≫ hyperplaneι n (Spec (CommRingCat.of k)) s)).obj
              (twistOver n (Spec (CommRingCat.of k)) 1) ≅
            twistOver (n - 1) (Spec (CommRingCat.of k)) 1) →
        ∀ m : ℤ, IsMRegular k n F m →
          haveI := projectiveSpaceOver_isLocallyNoetherian (n - 1) (Spec (CommRingCat.of k))
          haveI := isCoherent_pullback (φ.hom ≫ hyperplaneι n (Spec (CommRingCat.of k)) s) F
          IsMRegular k (n - 1)
            ((Scheme.Modules.pullback
              (φ.hom ≫ hyperplaneι n (Spec (CommRingCat.of k)) s)).obj F) m := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  have := isLocallyNoetherian_projectiveSpaceOverRing k (p + 1)
  obtain ⟨l, hl⟩ := Stacks.ProjectiveSpace.Cohomology.exists_degreeSection_eq (A := k) (p + 1) 1
    (ConcreteCategory.hom (twistGammaTopIso k (p + 1)).hom
      (PresheafOfModules.sections.eval s (op ⊤)))
  have hl0 : (l : MvPolynomial (Fin (p + 2)) k) ≠ 0 := by
    intro h
    apply hs0
    have h0 : ConcreteCategory.hom (twistGammaTopIso k (p + 1)).hom
        (PresheafOfModules.sections.eval s (op ⊤)) = 0 := by
      rw [← hl, show l = 0 from Subtype.ext h]
      exact map_zero (Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear k (p + 1) 1)
    rw [← Iso.hom_inv_id_apply (twistGammaTopIso k (p + 1))
      (PresheafOfModules.sections.eval s (op ⊤)), h0, map_zero]
    rfl
  obtain ⟨φ, ⟨eφ⟩, hφover⟩ := exists_iso_zeroScheme_projectiveSpaceOverRing k p l.1 l.2 hl0
    (PresheafOfModules.sections.eval s (op ⊤)) hl.symm
  obtain ⟨w, hSE⟩ := exists_shortExact_hyperplaneUnit_of_associatedPoints_subset k (p + 1) F s hs
  exact ⟨⟨w, hSE⟩, ⟨φ, ⟨eφ⟩, hφover⟩, fun ψ ⟨θ1⟩ m hF =>
    isMRegular_pullback_hyperplaneι_of_nonvanishing k (p + 1) hn F s hs ψ θ1 m hF⟩

end AlgebraicGeometry

end
