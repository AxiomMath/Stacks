module

import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DominateByNormalizedBlowUps.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.NormalizedBlowUpChainComp
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ResolutionByNormalizedBlowUpsPort
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.SingularLocusFinite
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ModificationCurve
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.DominatingStageRational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteCaseStepCompletedStalk

/-!
# Assembling a resolution by normalized blowups from the singular points of a dominating stage

Let `(A, 𝔪)` be a two-dimensional Noetherian local normal domain and `X ⟶ Spec A` a resolution
of singularities. The proof of [Stacks, Tag 0BGM] dominates `X` by a chain of normalized blowups
`Z ⟶ Spec A` ([Stacks, Tag 0BBT]), observes that the normal surface `Z` has finitely many
singular points, and resolves those by normalized blowups of the spectra of their local rings,
which then assemble into a resolution by normalized blowups of `Z` and hence of `Spec A`.

This file carries out that bookkeeping — Steps 2, 3 and 5 of the source's proof — and reduces the
remaining mathematics to one local statement about the singular points of a normal modification
which dominates the resolution: that the spectrum of the local ring at such a point has a
resolution by normalized blowups. In the source that local statement is the content of
[Stacks, Tags 0B4Q, 0BG0, 0BBV, 0BFY and 0BGE]. It enters below as the hypothesis `hlocal`; no
attribute for Tag 0BGM is attached here.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_eq_of_isModification_spec`: a modification of the
  spectrum of a Noetherian local domain has the dimension of that ring.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isResolution_of_isAdicComplete`: over a
  complete base, a resolution of singularities whose dominating normal modifications have local
  resolutions by normalized blowups at their singular points gives a resolution by normalized
  blowups of the base.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isResolution_of_local`: the same over an
  arbitrary two-dimensional Noetherian local normal domain, the local statement being required
  over complete bases only.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isResolution_of_rational`: Steps 1 to 5
  of [Stacks, Tag 0BGM]. Step 4, the rationality of the singular points of a dominating stage,
  is `AlgebraicGeometry.definesRationalSingularity_stalk_of_mem_singularLocus`. The local input
  is then needed only at singular points whose local ring defines a rational singularity: that is
  the content of [Stacks, Tags 0BBV, 0BFY and 0BGE].

## Implementation notes

The globalization `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_local` is phrased in
terms of the normalization of the scheme it globalizes over. The dominating stage `Z` is normal,
so its normalization `N` is isomorphic to it; rather than transporting singular points and local
rings along that isomorphism, the local statement is applied to `N` itself, which is again a
normal modification of `Spec A` dominating the resolution.

Over a complete base the singular locus of `N` is finite because `N` is of finite type over
`Spec A` and normal of dimension at most two ([Stacks, Tag 07R5] gives the J-2 property). The
general case is reduced to the complete one by
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isResolution_of_complete`.

## References

* [Stacks Project, Tag 0BGM](https://stacks.math.columbia.edu/tag/0BGM)
* [Stacks Project, Tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT)
* [Stacks Project, Tag 0BFY](https://stacks.math.columbia.edu/tag/0BFY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **A modification of the spectrum of a Noetherian local domain has the dimension of that
ring.** A proper morphism is closed and a birational morphism of integral schemes of finite type
over a Noetherian base preserves dimension. -/
theorem topologicalKrullDim_eq_of_isModification_spec (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsDomain A] {Z : Scheme.{u}} (g : Z ⟶ Spec (.of A))
    (hg : IsModification g) : topologicalKrullDim Z = ringKrullDim A := by
  let : IsProper g := hg.2.1
  let : IsIntegral Z := hg.2.2
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact hg.1.topologicalKrullDim_eq_of_isClosedMap g.isClosedMap

/-- **Steps 2, 3 and 5 of [Stacks, Tag 0BGM] over a complete base.** Let `A` be a complete
two-dimensional Noetherian local normal domain and `f : X ⟶ Spec A` a resolution of
singularities. Suppose that for every normal modification `Z ⟶ Spec A` which factors through
`f`, the spectrum of the local ring of `Z` at each singular point has a resolution by normalized
blowups. Then `Spec A` has a resolution by normalized blowups.

The resolution is dominated by a chain of normalized blowups `Z ⟶ Spec A` ([Stacks, Tag 0BBT]);
`Z` is normal with finitely many singular points, the local resolutions at those points
globalize over `Z`, and the chain over `Z` composes with the chain reaching `Z`. -/
theorem hasResolutionByNormalizedBlowUps_of_isResolution_of_isAdicComplete
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    [IsAdicComplete (maximalIdeal A) A] (hdim : ringKrullDim A = 2)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsResolution f)
    (hlocal : ∀ (Z : Scheme.{u}) [IsNormal Z] (g : Z ⟶ Spec (.of A)) (h : Z ⟶ X),
      IsModification g → h ≫ f = g → ∀ z ∈ singularLocus Z,
        HasResolutionByNormalizedBlowUps (Spec (Z.presheaf.stalk z))) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) := by
  let : IsProper f := hf.1.2.1
  let : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have hNagata : IsNagataScheme (Spec (.of A)) :=
    isNagataScheme_spec_of_isNagataRing _ IsNagataRing.of_isPrecomplete_maximalIdeal
  have hdimA : topologicalKrullDim (Spec (.of A)) = 2 := by
    show topologicalKrullDim (PrimeSpectrum A) = 2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim]
  -- Step 2: dominate the resolution by a chain of normalized blowups.
  obtain ⟨Z, g, h, hchain, hhg⟩ :=
    Stacks.ResolutionOfSurfaces.exists_normalizedBlowUpChain_dominating hNagata hdimA f hf.1.1
  have hgmod : IsModification g := isModification_of_normalizedBlowUpChain hdimA hchain
  let : IsProper g := hgmod.2.1
  let : IsIntegral Z := hgmod.2.2
  let : IsNormal Z := hchain.isNormal
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  let : CompactSpace Z := (quasiCompact_iff_compactSpace g).mp inferInstance
  let : IsNoetherian Z := {}
  have hdimZ : topologicalKrullDim Z = 2 := by
    rw [topologicalKrullDim_eq_of_isModification_spec A g hgmod, hdim]
  -- Step 3: the normalization of the stage, its finitely many singular points.
  let hZ : ∀ U : Z.Opens, IsCompact (U : Set Z) → (irreducibleComponents U).Finite :=
    Stacks.ResolutionOfSurfaces.finite_irreducibleComponents_isCompactOpen_of_isNoetherian
  let N := Z.normalizationScheme hZ
  let ν := Scheme.normalization Z hZ
  let : IsIso ν := (Scheme.isIso_normalization_iff_isNormal Z hZ).2 inferInstance
  let : IsNormal N := Scheme.isNormal_normalizationScheme Z hZ
  let : IsLocallyNoetherian N := isLocallyNoetherian_of_isOpenImmersion ν
  let : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace ν
  let : IsNoetherian N := {}
  have hνmod : IsModification (ν ≫ g) :=
    ⟨(isBirational_of_iso (asIso ν)).comp hgmod.1, inferInstance,
      IsIntegral.of_isIso (inv ν)⟩
  have hdimN : topologicalKrullDim N ≤ 2 := (topologicalKrullDim_le_of_isIntegralHom ν).trans_eq
    hdimZ
  have hsing : (singularLocus N).Finite :=
    finite_singularLocus_of_locallyOfFiniteType_over_completeLocalRing A (ν ≫ g) hdimN
  -- Step 5: globalize the local resolutions and compose with the chain reaching the stage.
  have hZres : HasResolutionByNormalizedBlowUps Z :=
    hasResolutionByNormalizedBlowUps_of_local Z hZ hdimZ inferInstance hsing
      fun y hy => hlocal N (ν ≫ g) (ν ≫ h) hνmod (by rw [Category.assoc, hhg]) y hy
  exact hasResolutionByNormalizedBlowUps_of_chain hchain hZres

/-- **Steps 1, 2, 3 and 5 of [Stacks, Tag 0BGM].** Let `A` be a two-dimensional Noetherian local
normal domain whose spectrum has a resolution of singularities. Suppose that over every complete
two-dimensional Noetherian local normal domain `B`, for every resolution `X ⟶ Spec B` and every
normal modification `Z ⟶ Spec B` factoring through it, the spectrum of the local ring of `Z` at
each singular point has a resolution by normalized blowups. Then `Spec A` has a resolution by
normalized blowups.

The case of a complete base is
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isResolution_of_isAdicComplete`, and the
general case reduces to it along the completion by
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isResolution_of_complete`. -/
theorem hasResolutionByNormalizedBlowUps_of_isResolution_of_local
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hdim : ringKrullDim A = 2)
    (hres : ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f)
    (hlocal : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
      [IsNormalDomain B] [IsAdicComplete (maximalIdeal B) B], ringKrullDim B = 2 →
      ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of B)), IsResolution f →
      ∀ (Z : Scheme.{u}) [IsNormal Z] (g : Z ⟶ Spec (.of B)) (h : Z ⟶ X),
        IsModification g → h ≫ f = g → ∀ z ∈ singularLocus Z,
          HasResolutionByNormalizedBlowUps (Spec (Z.presheaf.stalk z))) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) :=
  hasResolutionByNormalizedBlowUps_of_isResolution_of_complete A hdim hres
    fun B _ _ _ _ _ hdimB ⟨X, f, hf⟩ =>
      hasResolutionByNormalizedBlowUps_of_isResolution_of_isAdicComplete B hdimB f hf
        (hlocal B hdimB X f hf)

/-- **Steps 2 to 5 of [Stacks, Tag 0BGM] over a complete base.** Let `A` be a complete
two-dimensional Noetherian local normal domain and `f : X ⟶ Spec(A)` a resolution of
singularities. Suppose that whenever a normal modification `Z ⟶ Spec(A)` has a singular point
whose local ring defines a rational singularity, that local ring has a resolution by normalized
blowups. Then `Spec(A)` has a resolution by normalized blowups.

Step 4 shows that the local rings at the singular points of a stage dominating `f` define rational
singularities: `AlgebraicGeometry.definesRationalSingularity_stalk_of_mem_singularLocus`. Its
hypothesis `h0B4Q` stands for [Stacks, Tag 0B4Q]. The hypothesis `hrational` is the content of
[Stacks, Tags 0BBV, 0BFY and 0BGE]. -/
theorem hasResolutionByNormalizedBlowUps_of_isResolution_of_isAdicComplete_of_rational
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    [IsAdicComplete (maximalIdeal A) A] (hdim : ringKrullDim A = 2)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsResolution f)
    (h0B4Q : ∀ (B : Type u) [CommRing B] [IsDomain B] [IsRegularLocalRing B] [IsNagataRing B],
      ringKrullDim B = 2 → DefinesRationalSingularity B)
    (hrational : ∀ (Z : Scheme.{u}) [IsNormal Z] (g : Z ⟶ Spec (.of A)), IsModification g →
      ∀ z ∈ singularLocus Z, DefinesRationalSingularity (Z.presheaf.stalk z) →
        HasResolutionByNormalizedBlowUps (Spec (Z.presheaf.stalk z))) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) :=
  hasResolutionByNormalizedBlowUps_of_isResolution_of_isAdicComplete A hdim f hf
    fun Z _ g h hg hhg z hz => hrational Z g hg z hz
      (definesRationalSingularity_stalk_of_mem_singularLocus A hdim h0B4Q f hf
        (fun x ↦ have : IsProper f := hf.1.isProper
          isNagataRing_stalk_of_locallyOfFiniteType_of_isPrecomplete A f x) g h hg hhg z hz)

/-- **Steps 1 to 5 of [Stacks, Tag 0BGM].** Let `A` be a two-dimensional Noetherian local normal
domain whose spectrum has a resolution of singularities. Suppose that over every complete
two-dimensional Noetherian local normal domain `B`, whenever a normal modification of `Spec(B)`
has a singular point whose local ring defines a rational singularity, that local ring has a
resolution by normalized blowups. Then `Spec(A)` has a resolution by normalized blowups.

The hypothesis `h0B4Q` is that of
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isResolution_of_isAdicComplete_of_rational`.
The hypothesis `hrational` is the content of [Stacks, Tags 0BBV, 0BFY and 0BGE]. -/
theorem hasResolutionByNormalizedBlowUps_of_isResolution_of_rational
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hdim : ringKrullDim A = 2)
    (hres : ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f)
    (h0B4Q : ∀ (B : Type u) [CommRing B] [IsDomain B] [IsRegularLocalRing B] [IsNagataRing B],
      ringKrullDim B = 2 → DefinesRationalSingularity B)
    (hrational : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
      [IsNormalDomain B] [IsAdicComplete (maximalIdeal B) B], ringKrullDim B = 2 →
      ∀ (Z : Scheme.{u}) [IsNormal Z] (g : Z ⟶ Spec (.of B)), IsModification g →
        ∀ z ∈ singularLocus Z, DefinesRationalSingularity (Z.presheaf.stalk z) →
          HasResolutionByNormalizedBlowUps (Spec (Z.presheaf.stalk z))) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) :=
  hasResolutionByNormalizedBlowUps_of_isResolution_of_complete A hdim hres
    fun B _ _ _ _ _ hdimB ⟨_, f, hf⟩ =>
      hasResolutionByNormalizedBlowUps_of_isResolution_of_isAdicComplete_of_rational B hdimB f hf
        h0B4Q (hrational B hdimB)

end AlgebraicGeometry

end
