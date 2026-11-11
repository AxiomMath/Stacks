module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.EssSurjFlatDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.FormallySmoothEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.IndSmoothFiniteEtaleModel
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PuritySmoothEssSurj
public import StacksFrontier.RingTheory.FormallySmooth.CompletionRegular

/-!
# Ramanujam--Samuel for finite étale covers of a formally smooth local algebra

Let `A → B` be a local homomorphism of Noetherian local rings. Assume `A` has depth at least two,
`A → B` is formally smooth for the `𝔪_B`-adic topology, and `dim(B) > dim(A)`. For any open
`V ⊆ Y = Spec B` which contains every prime `𝔮` of `B` with `𝔮 ∩ A ≠ 𝔪_A` and the prime `𝔪_A B`,
the functor `FÉt_Y ⟶ FÉt_V` is an equivalence. In particular purity holds for `B`. This is
[Stacks, Tag 0EYC], proved here under exactly its hypotheses.

## Main results

* `Stacks.FundamentalGroup.essSurj_finiteEtaleBaseChange_of_formallySmoothNAdic` — essential
  surjectivity, the source's argument after its first paragraph.
* `Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_of_formallySmoothNAdic_of_depth` —
  **[Stacks, Tag 0EYC]**, the equivalence `FÉt_Y ⟶ FÉt_V`.
* `Stacks.FundamentalGroup.hasPurity_of_formallySmoothNAdic` — **[Stacks, Tag 0EYC]**, purity
  for `B`.

These two theorems are the registrations of [Stacks, Tag 0EYC]; together they are its complete
statement. `isEquivalence_finiteEtaleBaseChange_of_formallySmoothNAdic` in
`FormallySmoothEquivalence` is the step assembling the equivalence from its two halves.

## References

* [Stacks Project, Tag 07ED](https://stacks.math.columbia.edu/tag/07ED)
* [Stacks Project, Tag 07GC](https://stacks.math.columbia.edu/tag/07GC)
* [Stacks Project, Tag 07NP](https://stacks.math.columbia.edu/tag/07NP)
* [Stacks Project, Tag 07PM](https://stacks.math.columbia.edu/tag/07PM)
* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 0EYB](https://stacks.math.columbia.edu/tag/0EYB)
* [Stacks Project, Tag 0EYC](https://stacks.math.columbia.edu/tag/0EYC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing UniformSpace

universe u

namespace Stacks.FundamentalGroup

/-- At the closed point of `Spec A` the local ring has depth at least two when `A` does. -/
public theorem two_le_depth_stalk_of_asIdeal_eq_maximalIdeal (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A) (s : Spec (.of A))
    (hs : s.asIdeal = maximalIdeal A) :
    (2 : ℕ∞) ≤ Module.depth ((Spec (.of A)).presheaf.stalk s)
      (maximalIdeal ((Spec (.of A)).presheaf.stalk s)) ((Spec (.of A)).presheaf.stalk s) := by
  have : s.asIdeal.IsPrime := s.isPrime
  let : Algebra A ((Spec (.of A)).presheaf.stalk s) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of A) s
  have : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk s) s.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of A) s
  exact two_le_depth_of_isLocalization_atPrime_of_flat A A hdepth s.asIdeal
    (by rw [hs]; rfl) _

/-- A formally smooth (for the `𝔪_B`-adic topology) local homomorphism of Noetherian local rings
is flat. -/
private theorem flat_of_formallySmoothNAdic (A B : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (hsmooth : RingHom.FormallySmoothNAdic.{u} (algebraMap A B) (maximalIdeal B)) :
    Module.Flat A B := by
  have h := flat_of_isFormallySmooth_maximalIdeal_adic (algebraMap A B) hsmooth
  rwa [toAlgebra_algebraMap] at h

/-- **Essential surjectivity in [Stacks, Tag 0EYC].** Let `A → B` be a local homomorphism of
Noetherian local rings with `depth(A) ≥ 2` and `A → B` formally smooth for the `𝔪_B`-adic
topology, and let `V ⊆ Spec B` be an open containing every prime `𝔮` with `𝔮 ∩ A ≠ 𝔪_A` and the
prime `𝔪_A B`. Then every finite étale cover of `V` extends to a finite étale cover of `Spec B`.

This is the source's argument after its first paragraph. `B` is flat over `A`
([Stacks, Tag 07NP]). By the flat-base-change compatibility of the extension of
[Stacks, Tag 0EY6] (`essSurj_finiteEtaleBaseChange_of_flat_of_surjective`) it suffices to treat
the completions `A^ → B^` and the inverse image of `V`; the completed map is formally smooth
([Stacks, Tag 07ED]), hence regular ([Stacks, Tag 07PM]) and a filtered colimit of smooth
algebras ([Stacks, Tag 07GC]), and `𝔪_{A^} B^` is a prime of the inverse image of `V` over the
closed point. A cover then comes from a smooth affine `A^`-scheme with an open satisfying the
hypotheses of [Stacks, Tag 0EYB] (`exists_smooth_affine_model_of_indSmooth`), and
[Stacks, Tag 0EYB] (`essSurj_finiteEtaleBaseChange_of_smooth`) extends it. -/
public theorem essSurj_finiteEtaleBaseChange_of_formallySmoothNAdic (A B : Type u) [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (hsmooth : RingHom.FormallySmoothNAdic.{u} (algebraMap A B) (maximalIdeal B))
    (V : (Spec (.of B)).Opens)
    (hV₁ : ∀ q : PrimeSpectrum B, q.asIdeal.comap (algebraMap A B) ≠ maximalIdeal A → q ∈ V)
    (hV₂ : ∀ q : PrimeSpectrum B,
      q.asIdeal = Ideal.map (algebraMap A B) (maximalIdeal A) → q ∈ V) :
    (finiteEtaleBaseChange V.ι).EssSurj := by
  have hflat := flat_of_formallySmoothNAdic A B hsmooth
  let : WithIdeal A := ⟨maximalIdeal A⟩
  let : WithIdeal B := ⟨maximalIdeal B⟩
  have hAfg : (maximalIdeal A).FG := IsNoetherian.noetherian _
  have hBfg : (maximalIdeal B).FG := IsNoetherian.noetherian _
  have : IsNoetherianRing (Completion A) := isNoetherianRing_uniformCompletion (maximalIdeal A)
  have : IsNoetherianRing (Completion B) := isNoetherianRing_uniformCompletion (maximalIdeal B)
  have : IsLocalRing (Completion A) := isLocalRing_uniformCompletion hAfg
  have : IsLocalRing (Completion B) := isLocalRing_uniformCompletion hBfg
  let a : A →+* Completion A := Completion.coeRingHom
  let b : B →+* Completion B := Completion.coeRingHom
  have hcont := (algebraMap A B).continuous_adic_of_isLocalHom
  let fhat : Completion A →+* Completion B := Completion.mapRingHom (algebraMap A B) hcont
  let : Algebra (Completion A) (Completion B) := fhat.toAlgebra
  have : IsLocalHom (algebraMap (Completion A) (Completion B)) :=
    isLocalHom_mapRingHom hAfg hBfg _ hcont
  have hcomm : fhat.comp a = b.comp (algebraMap A B) :=
    RingHom.ext (Completion.mapRingHom_coe hcont)
  have hflatA : a.FaithfullyFlat :=
    faithfullyFlat_coeRingHom _ (by rw [ringJacobson_eq_maximalIdeal])
  have hflatB : b.FaithfullyFlat :=
    faithfullyFlat_coeRingHom _ (by rw [ringJacobson_eq_maximalIdeal])
  have hdepthHat : (2 : ℕ∞) ≤ Module.depth (Completion A) (maximalIdeal (Completion A))
      (Completion A) := by
    have : Module.Flat A (Completion A) := RingHom.flat_algebraMap_iff.mp hflatA.flat
    have : IsLocalHom (algebraMap A (Completion A)) := isLocalHom_coeRingHom hAfg
    rw [Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal A (Completion A)]
    exact hdepth.trans le_self_add
  let g : Spec (.of (Completion B)) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom b)
  have hg := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom b)).mpr hflatB
  have : Flat g := hg.1
  have : Surjective g := hg.2
  let Vhat : (Spec (.of (Completion B))).Opens := g ⁻¹ᵁ V
  refine essSurj_finiteEtaleBaseChange_of_flat_of_surjective V.ι g Vhat.ι (g ∣_ V)
    (isPullback_morphismRestrict g V).flip
    (fun x hx => two_le_depth_stalk_of_notMem_of_flat A B hdepth V hV₁ x
      (by rwa [Scheme.Opens.opensRange_ι] at hx)) ?_
  have hVhat : ∀ q : PrimeSpectrum (Completion B),
      q.asIdeal.comap (algebraMap (Completion A) (Completion B)) ≠ maximalIdeal (Completion A) →
        q ∈ Vhat := by
    intro q hq
    refine hV₁ (PrimeSpectrum.comap b q) fun hcontract =>
      hq (le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_)
    rw [maximalIdeal_uniformCompletion_eq_map hAfg, Ideal.map_le_iff_le_comap]
    change maximalIdeal A ≤ (q.asIdeal.comap fhat).comap a
    rw [Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
    exact hcontract.ge
  let qhat : PrimeSpectrum (Completion B) :=
    ⟨(maximalIdeal (Completion A)).map (algebraMap (Completion A) (Completion B)),
      isPrime_map_maximalIdeal_of_formallySmoothNAdic _
        (formallySmoothNAdic_completion_mapRingHom (algebraMap A B) hsmooth)⟩
  have hgeneric : qhat.asIdeal = ((maximalIdeal A).map (algebraMap A B)).map b := by
    change (maximalIdeal (Completion A)).map fhat = _
    rw [maximalIdeal_uniformCompletion_eq_map hAfg, Ideal.map_map, hcomm, ← Ideal.map_map]
  have : Module.FaithfullyFlat (Completion A) (Completion B) := by
    have : Module.Flat (Completion A) (Completion B) :=
      (isRegularRingHom_completion_mapRingHom (algebraMap A B) hsmooth).1
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hpoint : ∃ q : PrimeSpectrum (Completion B), q ∈ Vhat ∧
      q.asIdeal.comap (algebraMap (Completion A) (Completion B)) =
        maximalIdeal (Completion A) := by
    refine ⟨qhat, hV₂ (PrimeSpectrum.comap b qhat) ?_,
      Ideal.comap_map_eq_self_of_faithfullyFlat _⟩
    change qhat.asIdeal.comap b = _
    rw [hgeneric]
    have : Module.FaithfullyFlat B (Completion B) :=
      RingHom.faithfullyFlat_algebraMap_iff.mp hflatB
    exact Ideal.comap_map_eq_self_of_faithfullyFlat _
  refine ⟨fun W => ?_⟩
  obtain ⟨X, f, U, hsm, -, hU₁, hU₂, himp⟩ :=
    exists_smooth_affine_model_of_indSmooth (Completion A) (Completion B)
      (indSmooth_completion_mapRingHom (algebraMap A B) hsmooth) Vhat hVhat hpoint W
  have := hsm
  refine himp
    (essSurj_finiteEtaleBaseChange_of_smooth f U (fun s hs x hx => hU₁ x fun hc => ?_) hU₂)
  have h2 := two_le_depth_stalk_of_asIdeal_eq_maximalIdeal (Completion A) hdepthHat s
    (by rw [← (show f.base x = s from hx), hc]; rfl)
  exact absurd (h2.trans hs) (by norm_num)

/-- **[Stacks, Tag 0EYC]** (Ramanujam--Samuel for finite étale covers). Let `A → B` be a local
homomorphism of Noetherian local rings. Assume `A` has depth at least two, `A → B` is formally
smooth for the `𝔪_B`-adic topology, and `dim(B) > dim(A)`. For any open `V ⊆ Y = Spec B` which
contains every prime `𝔮 ⊆ B` with `𝔮 ∩ A ≠ 𝔪_A` (`hV₁`) and the prime `𝔪_A B` (`hV₂`, phrased as
a condition on the points of `Spec B`), the restriction functor `FÉt_Y ⟶ FÉt_V` is an
equivalence.

Full faithfulness is the source's first paragraph,
`isEquivalence_finiteEtaleBaseChange_of_formallySmoothNAdic`; flatness of `A → B` is
[Stacks, Tag 07NP]; essential surjectivity is
`essSurj_finiteEtaleBaseChange_of_formallySmoothNAdic`. The hypothesis `dim(B) > dim(A)` is the
source's own; it is what makes the punctured spectrum an open as in the tag (see
`hasPurity_of_formallySmoothNAdic`) and is not needed for the equivalence itself. -/
@[stacks 0EYC "the equivalence FÉt_Y → FÉt_V for a local homomorphism A → B of Noetherian \
local rings with depth(A) ≥ 2, formally smooth for the 𝔪_B-adic topology, with dim(B) > dim(A), \
and any open V of Spec B containing every prime 𝔮 with 𝔮 ∩ A ≠ 𝔪_A and the prime 𝔪_A B; \
flatness of A → B and essential surjectivity are proved here",
  sga "1 XIII 4.7" "special case"]
public theorem isEquivalence_finiteEtaleBaseChange_of_formallySmoothNAdic_of_depth
    (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A]
    [IsNoetherianRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (hsmooth : RingHom.FormallySmoothNAdic.{u} (algebraMap A B) (maximalIdeal B))
    (hdim : ringKrullDim A < ringKrullDim B)
    (V : (Spec (.of B)).Opens)
    (hV₁ : ∀ q : PrimeSpectrum B, q.asIdeal.comap (algebraMap A B) ≠ maximalIdeal A → q ∈ V)
    (hV₂ : ∀ q : PrimeSpectrum B,
      q.asIdeal = Ideal.map (algebraMap A B) (maximalIdeal A) → q ∈ V) :
    (finiteEtaleBaseChange V.ι).IsEquivalence :=
  have hflat := flat_of_formallySmoothNAdic A B hsmooth
  isEquivalence_finiteEtaleBaseChange_of_formallySmoothNAdic A B hdepth hsmooth hdim V hV₁ hV₂
    hflat (essSurj_finiteEtaleBaseChange_of_formallySmoothNAdic A B hdepth hsmooth V hV₁ hV₂)

/-- **[Stacks, Tag 0EYC], "in particular purity holds for `B`".** Let `A → B` be a local
homomorphism of Noetherian local rings with `depth(A) ≥ 2`, formally smooth for the `𝔪_B`-adic
topology, with `dim(B) > dim(A)`. Then every finite étale cover of the punctured spectrum of `B`
extends to a finite étale cover of `Spec B`.

The punctured spectrum is an open as in the tag: condition (1) because the closed point contracts
to `𝔪_A`, condition (2) because `𝔪_A B ≠ 𝔪_B`, which is where `dim(A) < dim(B)` enters
(`mem_puncturedSpectrum_of_eq_map_maximalIdeal_of_ringKrullDim_lt`). -/
@[stacks 0EYC "the clause 'in particular purity holds for B': every finite étale cover of the \
punctured spectrum of B extends to Spec B, for A → B as in the tag (Noetherian local, local \
homomorphism, depth(A) ≥ 2, formally smooth for the 𝔪_B-adic topology, dim(B) > dim(A))"]
public theorem hasPurity_of_formallySmoothNAdic (A B : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (hsmooth : RingHom.FormallySmoothNAdic.{u} (algebraMap A B) (maximalIdeal B))
    (hdim : ringKrullDim A < ringKrullDim B) :
    HasPurity B :=
  essSurj_finiteEtaleBaseChange_of_formallySmoothNAdic A B hdepth hsmooth
    (Stacks.puncturedSpectrum B)
    (mem_puncturedSpectrum_of_comap_ne_maximalIdeal_of_isLocalHom A B)
    (mem_puncturedSpectrum_of_eq_map_maximalIdeal_of_ringKrullDim_lt A B hdim)

end Stacks.FundamentalGroup

end
