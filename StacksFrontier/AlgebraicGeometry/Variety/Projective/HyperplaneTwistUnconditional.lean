module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRestrictionConstruction
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneSequenceCoherent

/-!
# [Stacks, Tag 0EGK] on `ℙⁿ_k`

Let `k` be an infinite field, let `n = m + 1 ≥ 1` and let `ℱ` be a coherent sheaf on `ℙⁿ_k`.
[Stacks, Tag 08A0] produces a nonzero global section `s` of `𝒪(1)`, the hyperplane `H = Z(s)`
with its inclusion `i : H ⟶ ℙⁿ_k`, the restriction `𝒢 = i^*ℱ` and the short exact sequence

`0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_*𝒢 ⟶ 0`,

and [Stacks, Tag 089Z] identifies `H` with `ℙ^{n-1}_k`. [Stacks, Tag 0EGK] is the remark that in
that situation

* the twists match along the identification, `𝒪_H(d) = i^*𝒪_{ℙⁿ_k}(d)` for **every** `d ∈ ℤ`;
* for every `d ∈ ℤ` the twisted sequence `0 ⟶ ℱ(d-1) ⟶ ℱ(d) ⟶ i_*(𝒢(d)) ⟶ 0` is short exact,
  tensoring by `𝒪(d)` being exact and the projection formula ([Stacks, Tag 01E8]) identifying
  `i_*(𝒢(d))` with `i_*𝒢 ⊗ 𝒪(d)`;
* and the resulting long exact cohomology sequences

  `H^j(ℙⁿ_k, ℱ(d-1)) ⟶ H^j(ℙⁿ_k, ℱ(d)) ⟶ H^j(H, 𝒢(d)) ⟶ H^{j+1}(ℙⁿ_k, ℱ(d-1))`

  have their third term computed on `H`, a closed immersion being affine so that
  [Stacks, Tag 089W] applies.

This file states all of that on the hypotheses of the source — `k` an infinite field and `ℱ`
coherent — and nothing else.

## Main results

* `AlgebraicGeometry.exists_iso_pullbackTwistOver_zeroScheme`: **the first clause.** The zero
  scheme of a global section of `𝒪(1)` coming from a nonzero degree-one form is `ℙ^{n-1}_k`, and
  along that identification `𝒪(d)` pulls back to `𝒪(d)` for every `d ∈ ℤ`, not only for `d = 1`.
* `AlgebraicGeometry.exists_hyperplane_pullbackTwistOver`: the same conclusion in the shape the
  hyperplane-restriction induction consumes — over an infinite field, a coherent sheaf `ℱ` on
  `ℙ^{m+1}_k` admits a hyperplane inclusion `j : ℙᵐ_k ⟶ ℙ^{m+1}_k`, a closed immersion and
  affine, cut out by a section of `𝒪(1)` that vanishes at no associated point of `ℱ`, along
  which `𝒪(d)` pulls back to `𝒪(d)` in every degree.
* `AlgebraicGeometry.isQuasicoherent_twistModule_pullback`: the twist of a restricted
  quasi-coherent module is quasi-coherent.
* `AlgebraicGeometry.exists_hyperplane_twistedSequence_cohomology`: **the whole remark.**

## The mathematics

Three results from the library are assembled.

The section and the untwisted sequence are [Stacks, Tag 08A0]:
`AlgebraicGeometry.exists_form_section_nonvanishing` chooses a global section of `𝒪(1)` coming
from a nonzero degree-one form `f` and vanishing at no associated point of `ℱ(-1)` — the only
step at which `k` has to be infinite — and
`…ProjectiveSpaceHyperplaneSection.shortExact_hyperplaneUnit_of_nonvanishing` turns that into the
short exact sequence, its quasi-coherence hypotheses on `ℱ(-1)` and `ℱ(-1) ⊗ 𝒪(1)` holding for a
coherent `ℱ` by [Stacks, Tag 0GQM]. That `s ≠ 0` is
`AlgebraicGeometry.degreeSection_one_ne_zero` read across the comparison of models.

The identification of the hyperplane with `ℙᵐ_k` is [Stacks, Tag 089Z] on the base-change model,
`AlgebraicGeometry.exists_iso_zeroScheme_projectiveSpaceOverRing`; the passage from its
degree-one twist comparison to every degree is
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTwistOverIso`.

The twisted sequence and its cohomology are
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.shortExact_twistedSequence` and
`…HyperplaneTwistSequence.exact_cohomology_twistedSequence`, which are stated for an arbitrary
closed immersion and an arbitrary invertible module and therefore ask for the untwisted short
exact sequence and for quasi-coherence of `𝒢(d)`. Both are supplied here: the first by the two
paragraphs above, after `Stacks.RelativeVeryAmple.tensorModulesMapIso` has rewritten the source
`ℱ ⊗ 𝒪(-1)` of multiplication by `s` as the tensor-power spelling `ℱ ⊗ 𝒪(1)^{⊗ -1}` that the
twist uses; the second by `AlgebraicGeometry.isQuasicoherent_twistModule_pullback`, since `𝒢` is
the inverse image of a coherent — hence quasi-coherent — module and `𝒪_H(d)` is invertible.

## References

* [Stacks Project, Tag 0EGK](https://stacks.math.columbia.edu/tag/0EGK)
* [Stacks Project, Tag 089Z](https://stacks.math.columbia.edu/tag/089Z)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.Cohomology.FormalFunctions (cohomologyDeltaFunctor)
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication
open Stacks.Ample (IsInvertibleModule tensorPowModule)
open Stacks.AlgebraicGeometry.ProjectiveSpaceHyperplaneSection
  (shortExact_hyperplaneUnit_of_nonvanishing)
open Stacks.ProjectiveCohomology (polyGrading)

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### The Serre twists on the hyperplane -/

/-- **[Stacks, Tag 0EGK], the Serre twists on a hyperplane of `ℙ^{m+1}_k`, in every integer
degree.**

Let `v` be a global section of `𝒪(1)` on `ℙ^{m+1}_k` corresponding to a nonzero degree-one form
`f` on `Proj k[T₀, …, T_{m+1}]`. Then the zero scheme `H = Z(v)` admits an isomorphism
`φ : ℙᵐ_k ≅ H` along which, for **every** `d ∈ ℤ`, the pullback of `𝒪_{ℙ^{m+1}}(d)` is
`𝒪_{ℙᵐ}(d)`.

The degree-one case is [Stacks, Tag 089Z] on the base-change model,
`AlgebraicGeometry.exists_iso_zeroScheme_projectiveSpaceOverRing`; the passage from it to every
degree is `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTwistOverIso`. -/
@[stacks 0EGK "the Serre twists on the hyperplane in every degree, the degree-one case being \
this chapter's own [Stacks, Tag 089Z] on the base-change model"]
theorem exists_iso_pullbackTwistOver_zeroScheme (k : Type u) [Field k] (m : ℕ)
    (f : MvPolynomial (Fin (m + 2)) k) (hf : f ∈ polyGrading k (m + 1) 1) (hf0 : f ≠ 0)
    (v : Γ(twistOver (m + 1) (Spec (CommRingCat.of k)) 1, ⊤))
    (hv : ConcreteCategory.hom (twistGammaTopIso k (m + 1)).hom v
      = degreeSection (polyGrading k (m + 1)) 1 ⟨f, hf⟩) :
    ∃ φ : projectiveSpaceOverRing m (CommRingCat.of k) ≅
        (AlgebraicGeometry.zeroScheme (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
          (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v).subscheme,
      ∀ d : ℤ, Nonempty ((Scheme.Modules.pullback (φ.hom ≫
          (AlgebraicGeometry.zeroScheme (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
            (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v).subschemeι)).obj
        (twistOver (m + 1) (Spec (CommRingCat.of k)) d)
          ≅ twistOver m (Spec (CommRingCat.of k)) d) := by
  obtain ⟨φ, ⟨e⟩, -⟩ := exists_iso_zeroScheme_projectiveSpaceOverRing k m f hf hf0 v hv
  exact ⟨φ, fun d => ⟨Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTwistOverIso
    m (Spec (CommRingCat.of k)) _ φ e d⟩⟩

/-- **The hyperplane of [Stacks, Tag 08A0] carries the twist comparisons of [Stacks, Tag 0EGK]
in every degree.** Let `k` be an infinite field and let `ℱ` be a coherent sheaf on `ℙ^{m+1}_k`.
Then there are a global section `v` of `𝒪(1)` vanishing at no associated point of `ℱ` — so that
multiplication by `v` is injective on `ℱ(d)` and the restriction sequence of
[Stacks, Tag 08A0] exists — and an isomorphism `φ : ℙᵐ_k ≅ Z(v)` along which `𝒪(d)` pulls back
to `𝒪(d)` for every `d ∈ ℤ`.

The section is `AlgebraicGeometry.exists_form_section_nonvanishing`, the only step needing `k`
infinite; the twist comparisons are `exists_iso_pullbackTwistOver_zeroScheme` above. The
composite `φ.hom ≫ (AlgebraicGeometry.zeroScheme …).subschemeι` is the hyperplane inclusion
`j : ℙᵐ_k ⟶ ℙ^{m+1}_k`; it is a closed immersion and affine by instance search, an isomorphism
followed by a closed immersion being both. -/
theorem exists_hyperplane_pullbackTwistOver (k : Type u) [Field k] [Infinite k] (m : ℕ)
    (F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules) (hFc : F.IsCoherent) :
    ∃ (v : Γ(twistOver (m + 1) (Spec (CommRingCat.of k)) 1, ⊤))
      (φ : projectiveSpaceOverRing m (CommRingCat.of k) ≅
        (AlgebraicGeometry.zeroScheme (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
          (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v).subscheme),
      Stacks.Divisors.associatedPoints F ⊆
          Stacks.Ample.nonvanishingLocus (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v ∧
        ∀ d : ℤ, Nonempty ((Scheme.Modules.pullback (φ.hom ≫
            (AlgebraicGeometry.zeroScheme (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
              (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v).subschemeι)).obj
          (twistOver (m + 1) (Spec (CommRingCat.of k)) d)
            ≅ twistOver m (Spec (CommRingCat.of k)) d) := by
  have : F.IsCoherent := hFc
  obtain ⟨f, hf, v, hf0, hv, hsub⟩ := exists_form_section_nonvanishing k (m + 1) F
  obtain ⟨φ, he⟩ := exists_iso_pullbackTwistOver_zeroScheme k m f hf hf0 v hv
  exact ⟨v, φ, hsub, he⟩

/-! ### Quasi-coherence of the twists on the hyperplane -/

/-- **The twist of a restricted quasi-coherent module is quasi-coherent.** For a morphism
`i : H ⟶ X` of schemes, an invertible `𝒪_X`-module `L` and a quasi-coherent `𝒪_X`-module `ℱ`,
the module `(i^*ℱ)(d) = i^*ℱ ⊗_{𝒪_H} (i^*L)^{⊗ d}` is quasi-coherent for every `d ∈ ℤ`.

The inverse image `i^*ℱ` is quasi-coherent by [Stacks, Tag 01BG], the power `(i^*L)^{⊗ d}` is
quasi-coherent because `i^*L` is invertible ([Stacks, Tag 0B8M]), and a tensor product of
quasi-coherent modules is quasi-coherent ([Stacks, Tag 01CE]). -/
theorem isQuasicoherent_twistModule_pullback {Hy X : Scheme.{u}} (i : Hy ⟶ X)
    (L : X.Modules) [IsInvertibleModule X L] (F : X.Modules) (hF : F.IsQuasicoherent)
    (d : ℤ) :
    (twistModule Hy ((Scheme.Modules.pullback i).obj L)
      ((Scheme.Modules.pullback i).obj F) d).IsQuasicoherent :=
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent Hy.toRingedSpace _ _
    (@Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback Hy X i F hF)
    (Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule
      ((Scheme.Modules.pullback i).obj L) d)

/-! ### The remark -/

section Remark

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

open CategoryTheory.MonoidalCategory

/-! #### The steps of the proof

The proof below assembles four steps, each stated in full and proved separately above the
remark. The first two are the two halves of [Stacks, Tag 08A0] in this situation — the choice of
the section together with the identification of its hyperplane, and the passage from the sequence
of that tag to the twist spelling the twisted sequence is built from — and the last two are the
two general clauses of
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/HyperplaneTwistSequence.lean` instantiated at the
hyperplane. Each of them mentions `twistedSequence`, `hyperplaneι`, `hyperplaneUnit` and
`hyperplane`, all reducible abbreviations over the pullback presentation of `ℙ^{m+1}_k`, so each
costs the elaborator a sizeable unfolding; stating them separately lets each unfolding be paid
once, against its own heartbeat budget, instead of all of them inside the single term that proves
the remark. -/

/-- **The section of [Stacks, Tag 08A0] together with the identification of its hyperplane.**
Over an infinite field `k`, a coherent sheaf `ℱ` on `ℙ^{m+1}_k` admits a global section `s` of
`𝒪(1)` which is nonzero, whose hyperplane `V(s)` is `ℙᵐ_k` compatibly with the twists in every
degree, and which vanishes at no associated point of `ℱ ⊗ 𝒪(-1)` — the last being exactly the
hypothesis `…ProjectiveSpaceHyperplaneSection.shortExact_hyperplaneUnit_of_nonvanishing` asks
for.

The section is `AlgebraicGeometry.exists_form_section_nonvanishing`, read across
`Stacks.NonvanishingSpelling.sectionsEquiv` into the `sections` spelling, the only step at which
`k` has to be infinite; that it is nonzero is `AlgebraicGeometry.degreeSection_one_ne_zero`; and
the identification of the hyperplane is `exists_iso_pullbackTwistOver_zeroScheme` above. -/
private theorem exists_section_hyperplaneIso_nonvanishing (k : Type u) [Field k] [Infinite k]
    (m : ℕ) (F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules)
    [F.IsCoherent] :
    ∃ s : (twistOver (m + 1) (Spec (CommRingCat.of k)) 1).sections,
      PresheafOfModules.sections.eval s (op ⊤) ≠ 0 ∧
      (∃ φ : projectiveSpaceOverRing m (CommRingCat.of k) ≅
          (hyperplane (m + 1) (Spec (CommRingCat.of k)) s).subscheme,
        ∀ d : ℤ, Nonempty ((Scheme.Modules.pullback
              (φ.hom ≫ hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj
            (twistOver (m + 1) (Spec (CommRingCat.of k)) d)
              ≅ twistOver m (Spec (CommRingCat.of k)) d)) ∧
      ∀ x ∈ Stacks.Divisors.associatedPoints
          (Stacks.RelativeVeryAmple.tensorModules
            (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) F
            (twistOver (m + 1) (Spec (CommRingCat.of k)) (-1))),
        ∃ W : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Opens, x ∈ W ∧ ∀ y ∈ W,
          y ∈ Stacks.SheafOfModules.nonvanishingLocus
            (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) s := by
  have : IsLocallyNoetherian (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) :=
    projectiveSpaceOver_isLocallyNoetherian (m + 1) (Spec (CommRingCat.of k))
  have : (projectiveTwist (m + 1) F (-1)).IsCoherent :=
    isCoherent_projectiveTwist (m + 1) F (-1)
  obtain ⟨f, hf, v, hf0, hv, hsub⟩ :=
    exists_form_section_nonvanishing k (m + 1) (projectiveTwist (m + 1) F (-1))
  set s := (Stacks.NonvanishingSpelling.sectionsEquiv
    (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
    (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)).symm v with hs
  have hsv : PresheafOfModules.sections.eval s (op ⊤) = v := by
    rw [hs, ← Stacks.NonvanishingSpelling.sectionsEquiv_apply, Equiv.apply_symm_apply]
  rw [← hsv] at hv hsub
  have hnv : Stacks.SheafOfModules.nonvanishingLocus
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) s
      = Stacks.Ample.nonvanishingLocus (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)
        (PresheafOfModules.sections.eval s (op ⊤)) :=
    Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq
      (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
      (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) s
  obtain ⟨φ, htw⟩ := exists_iso_pullbackTwistOver_zeroScheme k m f hf hf0 _ hv
  refine ⟨s, ?_, ⟨φ, htw⟩, fun x hx => ?_⟩
  · intro h0
    refine degreeSection_one_ne_zero k (m + 1) hf hf0 ?_
    rw [← hv, h0]
    exact map_zero _
  · refine ⟨Stacks.NonvanishingOpen.nonvanishingOpen
      (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
      (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)
      (PresheafOfModules.sections.eval s (op ⊤)), hsub hx, fun y hy => ?_⟩
    rw [hnv]
    exact hy

/-- **The sequence of [Stacks, Tag 08A0] with its first term read as a twist.** Given a global
section `s` of `𝒪(1)` on `ℙ^{m+1}_k` vanishing at no associated point of `ℱ ⊗ 𝒪(-1)`, there is a
morphism `a : ℱ(-1) ⟶ ℱ` fitting into a short exact sequence `0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_*𝒢 ⟶ 0`.

`…ProjectiveSpaceHyperplaneSection.shortExact_hyperplaneUnit_of_nonvanishing` provides that
sequence with `ℱ ⊗ 𝒪(-1)` as its first term; `Stacks.RelativeVeryAmple.tensorModulesMapIso`
rewrites that source as the tensor-power spelling `ℱ ⊗ 𝒪(1)^{⊗ -1}` which `twistModule` — and
hence `twistedSequence` — uses, and transporting a short exact sequence along an isomorphism of
short complexes keeps it short exact. The quasi-coherence hypotheses of that tag hold because
`ℱ` is coherent, by [Stacks, Tag 0GQM] for `ℱ ⊗ 𝒪(-1)` and by [Stacks, Tag 01CE] for its further
tensor product with `𝒪(1)`. -/
private theorem exists_shortExact_twistModule_hyperplaneUnit (k : Type u) [Field k] (m : ℕ)
    (F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules) [F.IsCoherent]
    (s : (twistOver (m + 1) (Spec (CommRingCat.of k)) 1).sections)
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints
        (Stacks.RelativeVeryAmple.tensorModules
          (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) F
          (twistOver (m + 1) (Spec (CommRingCat.of k)) (-1))),
      ∃ W : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) s) :
    ∃ (a : twistModule (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F (-1) ⟶ F)
      (w : a ≫ hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s = 0),
      (ShortComplex.mk a
        (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) w).ShortExact := by
  have : IsLocallyNoetherian (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) :=
    projectiveSpaceOver_isLocallyNoetherian (m + 1) (Spec (CommRingCat.of k))
  have hFq : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : (Stacks.RelativeVeryAmple.tensorModules
          (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) F
          (twistOver (m + 1) (Spec (CommRingCat.of k)) (-1))
      ⊗ twistOver (m + 1) (Spec (CommRingCat.of k)) 1).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent
        (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).ringCatSheaf).prop_of_iso
      (Stacks.AmplePullbackPart1.tensorIsoTensorModules
        (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
        (Stacks.RelativeVeryAmple.tensorModules
          (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) F
          (twistOver (m + 1) (Spec (CommRingCat.of k)) (-1)))
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)).symm
      inferInstance
  obtain ⟨w, hSE⟩ :=
    shortExact_hyperplaneUnit_of_nonvanishing (m + 1) (Spec (CommRingCat.of k)) F s hW
  set τ := Stacks.RelativeVeryAmple.tensorModulesMapIso
    (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) (Iso.refl F)
    (tensorPowModuleProjectiveTwistIso (m + 1) (Spec (CommRingCat.of k)) (-1)) with hτ
  set a := τ.hom ≫ twistSectionMulNegOne (m + 1) (Spec (CommRingCat.of k)) F s with ha
  have wa : a ≫ hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s = 0 := by
    rw [ha, Category.assoc, w, comp_zero]
  have hiso : (ShortComplex.mk (twistSectionMulNegOne (m + 1) (Spec (CommRingCat.of k)) F s)
        (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) w)
      ≅ ShortComplex.mk a (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) wa :=
    ShortComplex.isoMk τ.symm (Iso.refl _) (Iso.refl _) (by simp [ha]) (by simp)
  exact ⟨a, wa, ShortComplex.shortExact_of_iso hiso hSE⟩

/-- **The twisted sequence at a hyperplane of `ℙ^{m+1}_k` is short exact.**
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.shortExact_twistedSequence` at the closed
immersion `i : V(s) ⟶ ℙ^{m+1}_k`, the invertible module `𝒪(1)`, the restriction `𝒢 = i^*ℱ` and
the unit `g : ℱ ⟶ i_*𝒢`, with all of its arguments written out. -/
private theorem shortExact_twistedSequence_hyperplane (k : Type u) [Field k] (m : ℕ)
    (F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules)
    (s : (twistOver (m + 1) (Spec (CommRingCat.of k)) 1).sections)
    (a : twistModule (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
      (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F (-1) ⟶ F)
    (w : a ≫ hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s = 0)
    (hS : (ShortComplex.mk a
      (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) w).ShortExact) (d : ℤ) :
    (twistedSequence (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
      (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F
      ((Scheme.Modules.pullback (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj F) a
      (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) w d).ShortExact :=
  shortExact_twistedSequence (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
    (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F _ a _ w hS d

/-- **The long exact cohomology sequence of the twisted sequence at a hyperplane of `ℙ^{m+1}_k`.**
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.exact_cohomology_twistedSequence` at the same
data as `shortExact_twistedSequence_hyperplane`, its quasi-coherence hypothesis `hG` being the
one `isQuasicoherent_twistModule_pullback` supplies for a quasi-coherent `ℱ`. -/
private theorem exact_cohomology_twistedSequence_hyperplane (k : Type u) [Field k] (m : ℕ)
    (F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules)
    (s : (twistOver (m + 1) (Spec (CommRingCat.of k)) 1).sections)
    (a : twistModule (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
      (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F (-1) ⟶ F)
    (w : a ≫ hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s = 0)
    (hS : (ShortComplex.mk a
      (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) w).ShortExact) (d : ℤ)
    (hG : (twistModule (hyperplane (m + 1) (Spec (CommRingCat.of k)) s).subscheme
      ((Scheme.Modules.pullback (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1))
      ((Scheme.Modules.pullback
        (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj F) d).IsQuasicoherent)
    (j : ℕ) :
    Function.Exact
        (((cohomologyDeltaFunctor
            (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))).functor j).map
          (twistedSequence (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
            (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F
            ((Scheme.Modules.pullback
              (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj F) a
            (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) w d).f)
        (cohomologyToHyperplaneMap (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
          (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F
          ((Scheme.Modules.pullback (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj F) a
          (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) w d hG j) ∧
      Function.Exact
        (cohomologyToHyperplaneMap (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
          (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F
          ((Scheme.Modules.pullback (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj F) a
          (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) w d hG j)
        (cohomologyConnectingMap (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
          (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F
          ((Scheme.Modules.pullback (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj F) a
          (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) w hS d hG j) ∧
      Function.Exact
        (cohomologyConnectingMap (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
          (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F
          ((Scheme.Modules.pullback (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj F) a
          (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) w hS d hG j)
        (((cohomologyDeltaFunctor
            (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))).functor (j + 1)).map
          (twistedSequence (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
            (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F
            ((Scheme.Modules.pullback
              (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj F) a
            (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) w d).f) :=
  exact_cohomology_twistedSequence (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
    (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F _ a _ w hS d hG j

/-- **[Stacks, Tag 0EGK] in full.** Let `k` be an infinite field and let `ℱ` be a coherent sheaf
on `ℙ^{m+1}_k`. Then there are a nonzero global section `s` of `𝒪(1)`, an isomorphism
`φ : ℙᵐ_k ≅ H` of `ℙᵐ_k` with the hyperplane `H = Z(s)` and, writing `i : H ⟶ ℙ^{m+1}_k` for the
inclusion and `𝒢 = i^*ℱ`, a short exact sequence

`0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_*𝒢 ⟶ 0`

such that

* `𝒪_H(d) = i^*𝒪_{ℙ^{m+1}}(d)` along `φ`, for every `d ∈ ℤ`;
* for every `d ∈ ℤ` the twisted sequence `0 ⟶ ℱ(d-1) ⟶ ℱ(d) ⟶ i_*(𝒢(d)) ⟶ 0` is short exact;
* and for every `d ∈ ℤ` and every `j` the four-term sequence

  `H^j(ℙ^{m+1}_k, ℱ(d-1)) ⟶ H^j(ℙ^{m+1}_k, ℱ(d)) ⟶ H^j(H, 𝒢(d)) ⟶ H^{j+1}(ℙ^{m+1}_k, ℱ(d-1))`

  is exact at each of its three inner spots, its third term being cohomology on `H` and its
  connecting map the canonical one of the cohomological `δ`-functor of [Stacks, Tag 071H] read
  through the comparison of [Stacks, Tag 089W].

The index is written `m + 1` rather than `n` with `1 ≤ n` so that the hyperplane is `ℙᵐ_k` with
no truncated subtraction. The first clause is `exists_iso_pullbackTwistOver_zeroScheme`, the
untwisted sequence is [Stacks, Tag 08A0] and the two remaining clauses are
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.shortExact_twistedSequence` and
`…HyperplaneTwistSequence.exact_cohomology_twistedSequence`, whose quasi-coherence input is
`isQuasicoherent_twistModule_pullback`. -/
@[stacks 0EGK "the whole remark in the situation of Tags 089Z and 08A0: the hyperplane is \
P^m_k with O_H(d) = i^*O(d) in every degree, the twisted sequence \
0 → F(d-1) → F(d) → i_*(G(d)) → 0 is short exact for every d, and its long exact cohomology \
sequence has H^j(H, G(d)) as its third term"]
theorem exists_hyperplane_twistedSequence_cohomology (k : Type u) [Field k] [Infinite k]
    (m : ℕ) (F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules)
    [F.IsCoherent] :
    ∃ (s : (twistOver (m + 1) (Spec (CommRingCat.of k)) 1).sections)
      (φ : projectiveSpaceOverRing m (CommRingCat.of k) ≅
        (hyperplane (m + 1) (Spec (CommRingCat.of k)) s).subscheme)
      (a : twistModule (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
          (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F (-1) ⟶ F)
      (w : a ≫ hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s = 0)
      (hS : (ShortComplex.mk a
        (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) w).ShortExact),
      let X := projectiveSpaceOverRing (m + 1) (CommRingCat.of k)
      let G := (Scheme.Modules.pullback
        (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj F
      let g := hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s
      let hG := fun d : ℤ => isQuasicoherent_twistModule_pullback
        (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F (isQuasicoherent_of_isCoherent F) d
      PresheafOfModules.sections.eval s (op ⊤) ≠ 0 ∧
      (∀ d : ℤ, Nonempty ((Scheme.Modules.pullback
            (φ.hom ≫ hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj
          (twistOver (m + 1) (Spec (CommRingCat.of k)) d)
            ≅ twistOver m (Spec (CommRingCat.of k)) d)) ∧
      ∀ d : ℤ,
        (twistedSequence (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
          (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F G a g w d).ShortExact ∧
        ∀ j : ℕ,
          Function.Exact (((cohomologyDeltaFunctor X).functor j).map
              (twistedSequence (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
                (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F G a g w d).f)
            (cohomologyToHyperplaneMap (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
              (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F G a g w d (hG d) j) ∧
          Function.Exact
              (cohomologyToHyperplaneMap (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
                (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F G a g w d (hG d) j)
              (cohomologyConnectingMap (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
                (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F G a g w hS d (hG d) j) ∧
          Function.Exact
              (cohomologyConnectingMap (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
                (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F G a g w hS d (hG d) j)
              (((cohomologyDeltaFunctor X).functor (j + 1)).map
                (twistedSequence (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)
                  (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F G a g w d).f) := by
  obtain ⟨s, h0, ⟨φ, htw⟩, hW⟩ := exists_section_hyperplaneIso_nonvanishing k m F
  obtain ⟨a, w, hS⟩ := exists_shortExact_twistModule_hyperplaneUnit k m F s hW
  exact ⟨s, φ, a, w, hS, h0, htw, fun d =>
    ⟨shortExact_twistedSequence_hyperplane k m F s a w hS d,
      fun j => exact_cohomology_twistedSequence_hyperplane k m F s a w hS d _ j⟩⟩

end Remark

end AlgebraicGeometry

end
