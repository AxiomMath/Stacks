module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.AffineFormalOpenBasis
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumGlobalSectionsIso
public import StacksFrontier.AlgebraicGeometry.Thickenings
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The basic opens of the formal spectrum of an admissible ring

Let `A` be an admissible topological ring and `f ∈ A`. Write `A_{\{f\}}` for the completion of
the localization `A_f` along the ideals of definition of `A`
(`AlgebraicGeometry.SpfwBasicOpen.localizedCompletion`). The source (Stacks, Section 87.2,
Tag 0AHY) lists, among the facts "one should check" about the formal spectrum, that

* `A_{\{f\}}` is admissible too;
* `(Spf A_{\{f\}}, 𝒪_{Spf A_{\{f\}}})` is isomorphic to `(D(f) ∩ Spf A, 𝒪_{Spf A}|_{D(f) ∩ Spf A})`;
* `Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) = A_{\{f\}}` as topological rings.

These are proved here, by transporting McQuillan's version along the weak ideals of definition
(`AlgebraicGeometry.SpfwBasicOpen.localizationSpectrumIso`) through the identification
`Spf A = Spfw A` of an admissible ring (`AlgebraicGeometry.spfIsoSpfw`), and reading the global
sections of `Spf A_{\{f\}}` through `AlgebraicGeometry.spfGammaIso`.

## Main results

* `AlgebraicGeometry.isAdmissible_localizedCompletion`: `A_{\{f\}}` is admissible.
* `AlgebraicGeometry.spfLocalizedCompletionMap`,
  `AlgebraicGeometry.isOpenImmersion_spfLocalizedCompletionMap` and
  `AlgebraicGeometry.range_spfLocalizedCompletionMap_base`: the open immersion
  `Spf A_{\{f\}} → Spf A` with image `D(f) ∩ Spf A`.
* `AlgebraicGeometry.spfBasicOpenRestrictIso`: the isomorphism
  `(D(f) ∩ Spf A, 𝒪_{Spf A}|) ≅ (Spf A_{\{f\}}, 𝒪_{Spf A_{\{f\}}})`.
* `AlgebraicGeometry.isAffineFormalOpen_spfBasicOpen`: `D(f) ∩ Spf A` is an affine formal open.
* `AlgebraicGeometry.spfBasicOpenGammaIso`: `Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) ≅ A_{\{f\}}` as
  topological rings.

## References

* [EGA I, 10.1.4]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopologicalRing
open TopologicalRing.CompletionOver AlgebraicGeometry.SpfwBasicOpen

namespace AlgebraicGeometry

universe u

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]

/-- An admissible topological ring is weakly admissible. -/
theorem isWeaklyAdmissible_of_isAdmissible (hA : IsAdmissible A) : IsWeaklyAdmissible A :=
  ⟨⟨hA.1.choose, isWeakIdealOfDefinition_of_isIdealOfDefinition hA.1.choose_spec⟩,
    hA.2.2, hA.2.1⟩

/-- **The completed localization `A_{\{f\}}` of an admissible ring is admissible** (EGA I 10.1.4):
its topology is induced from `A`, so the canonical map `A → A_{\{f\}}` is taut and carries an ideal
of definition of `A` to one of `A_{\{f\}}`, and it is complete and separated, being a completion. -/
@[stacks 0AHY "the ring A_{f} is admissible too"]
theorem isAdmissible_localizedCompletion (hA : IsAdmissible A) (f : A) :
    IsAdmissible (localizedCompletion A f) :=
  ⟨RingHom.isPreAdmissible_of_isTaut (canonicalMap (algebraMap A (Localization.Away f)))
    (TopologicalRing.isTaut_canonicalMap _ (isWeaklyAdmissible_of_isAdmissible A hA).1) hA.1,
    ⟨inferInstance, inferInstance⟩⟩

/-- The open immersion `Spf A_{\{f\}} → Spf A` onto `D(f) ∩ Spf A`, for an admissible ring `A`. -/
noncomputable def spfLocalizedCompletionMap (hA : IsAdmissible A) (f : A) :
    Spf (localizedCompletion A f) ⟶ Spf A :=
  (spfIsoSpfw _ (isAdmissible_localizedCompletion A hA f).1).hom ≫
    localizationSpectrumMap A (isWeaklyAdmissible_of_isAdmissible A hA) f ≫
      (spfIsoSpfw A hA.1).inv

/-- `Spf A_{\{f\}} → Spf A` is an open immersion. -/
theorem isOpenImmersion_spfLocalizedCompletionMap (hA : IsAdmissible A) (f : A) :
    PresheafedSpace.IsOpenImmersion (spfLocalizedCompletionMap A hA f) := by
  have := PresheafedSpace.IsOpenImmersion.ofIso
    (spfIsoSpfw _ (isAdmissible_localizedCompletion A hA f).1)
  have := localizationSpectrumMap_isOpenImmersion A (isWeaklyAdmissible_of_isAdmissible A hA) f
  have := PresheafedSpace.IsOpenImmersion.ofIso (spfIsoSpfw A hA.1).symm
  exact inferInstanceAs (PresheafedSpace.IsOpenImmersion (_ ≫ _ ≫ _))

/-- The image of `Spf A_{\{f\}} → Spf A` is `D(f) ∩ Spf A`. -/
theorem range_spfLocalizedCompletionMap_base (hA : IsAdmissible A) (f : A) :
    Set.range (spfLocalizedCompletionMap A hA f).base = (spfBasicOpen A f : Set (spfSpace A)) := by
  ext (p : spfSpace A)
  exact (mem_range_localizationBase A (isWeaklyAdmissible_of_isAdmissible A hA) f p).trans Iff.rfl

/-- **Stacks 0AHY**: for an admissible ring `A` and `f ∈ A`, the open
`(D(f) ∩ Spf A, 𝒪_{Spf A}|_{D(f) ∩ Spf A})` of the formal spectrum is isomorphic to
`(Spf A_{\{f\}}, 𝒪_{Spf A_{\{f\}}})`. -/
@[stacks 0AHY "(Spf A_{f}, 𝒪) is isomorphic to (D(f) ∩ Spf A, 𝒪_{Spf A}|_{D(f) ∩ Spf A})"]
noncomputable def spfBasicOpenRestrictIso (hA : IsAdmissible A) (f : A) :
    (Spf A).restrict (f := (spfBasicOpen A f).inclusion')
      (spfBasicOpen A f).isOpenEmbedding' ≅ Spf (localizedCompletion A f) :=
  haveI := PresheafedSpace.IsOpenImmersion.ofRestrict (Spf A)
    (f := (spfBasicOpen A f).inclusion') (spfBasicOpen A f).isOpenEmbedding'
  haveI := isOpenImmersion_spfLocalizedCompletionMap A hA f
  PresheafedSpace.IsOpenImmersion.isoOfRangeEq
    ((Spf A).ofRestrict (f := (spfBasicOpen A f).inclusion') (spfBasicOpen A f).isOpenEmbedding')
    (spfLocalizedCompletionMap A hA f)
    (Subtype.range_coe_subtype.trans (range_spfLocalizedCompletionMap_base A hA f).symm)

/-- `D(f) ∩ Spf A` is an affine formal open subscheme of `Spf A`, with ring `A_{\{f\}}`. -/
theorem isAffineFormalOpen_spfBasicOpen (hA : IsAdmissible A) (f : A) :
    IsAffineFormalOpen (spfLTRS A hA.1) (spfBasicOpen A f) :=
  ⟨TopCommRingCat.of (localizedCompletion A f), inferInstance,
    isAdmissible_localizedCompletion A hA f, ⟨spfBasicOpenRestrictIso A hA f⟩⟩

/-- The image of the whole of `Spf A_{\{f\}}` under the open immersion into `Spf A` is
`D(f) ∩ Spf A`. -/
theorem spfLocalizedCompletionMap_opensFunctor_top (hA : IsAdmissible A) (f : A) :
    letI := isOpenImmersion_spfLocalizedCompletionMap A hA f
    (PresheafedSpace.IsOpenImmersion.opensFunctor (spfLocalizedCompletionMap A hA f)).obj ⊤ =
      spfBasicOpen A f := by
  ext1
  change _ '' Set.univ = _
  exact Set.image_univ.trans (range_spfLocalizedCompletionMap_base A hA f)

/-- **Stacks 0AHY**: for an admissible ring `A` and `f ∈ A`,
`Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) = A_{\{f\}}` as topological rings. The other description
`Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) = lim (A/I_λ)_f` of the source is
`AlgebraicGeometry.spfBasicOpenIsoOn`. -/
@[stacks 0AHY "Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) = A_{f} as topological rings"]
noncomputable def spfBasicOpenGammaIso (hA : IsAdmissible A) (f : A) :
    (spfPresheaf A).obj (op (spfBasicOpen A f)) ≅ TopCommRingCat.of (localizedCompletion A f) :=
  letI := isOpenImmersion_spfLocalizedCompletionMap A hA f
  (spfPresheaf A).mapIso (eqToIso (congrArg op
      (spfLocalizedCompletionMap_opensFunctor_top A hA f))).symm ≪≫
    (asIso (PresheafedSpace.IsOpenImmersion.invApp (spfLocalizedCompletionMap A hA f) ⊤)).symm ≪≫
    (spfGammaIso (localizedCompletion A f) (isAdmissible_localizedCompletion A hA f)).symm

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- For ideals of definition `J ⊆ I` of a topological ring, the morphism
`Spec (A/I) → Spec (A/J)` is a thickening, because `I ^ n ⊆ J` for some `n`: every element of
the kernel `I/J` of `A/J → A/I` is nilpotent, so every prime of `A/J` contains that kernel. -/
theorem isThickening_specMap_factor_of_isIdealOfDefinition {I J : Ideal A}
    (hI : IsIdealOfDefinition I) (hJ : IsIdealOfDefinition J) (hJI : J ≤ I) :
    Stacks.Thickenings.IsThickening (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJI))) := by
  refine ⟨IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective hJI), ?_⟩
  change Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.factor hJI))
  obtain ⟨n, hn⟩ := hI.exists_pow_le hJ.1
  intro q
  have hq : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor hJI)) := by
    rw [range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective hJI),
      PrimeSpectrum.mem_zeroLocus]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∈ I := by
      rw [SetLike.mem_coe, RingHom.mem_ker, Ideal.Quotient.factor_mk,
        Ideal.Quotient.eq_zero_iff_mem] at hx
      exact hx
    refine q.isPrime.mem_of_pow_mem n ?_
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (hn (Ideal.pow_mem_pow ha n))]
    exact q.asIdeal.zero_mem
  exact hq

/-- **Stacks 0AHY: the formal spectrum of an admissible topological ring.** For an admissible
topological ring `A` (with its ideals of definition `I_λ`, which form a fundamental system of
neighbourhoods of `0`):

* for `I_λ ⊆ I_μ` the morphism `Spec (A/I_μ) → Spec (A/I_λ)` is a thickening;
* each `Spec (A/I_λ) → Spf A` is a homeomorphism onto the space of open primes;
* `𝒪_{Spf A} = lim 𝒪_λ` is a sheaf of topological rings whose stalks are local rings, so
  `(Spf A, 𝒪_{Spf A})` is a locally topologically ringed space;
* `Γ(Spf A, 𝒪_{Spf A}) = A` as topological rings;
* for `f ∈ A`, `Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) = A_{\{f\}} = lim (A/I_λ)_f` as topological rings,
  `A_{\{f\}}` is admissible, and `(Spf A_{\{f\}}, 𝒪)` is isomorphic to
  `(D(f) ∩ Spf A, 𝒪_{Spf A}|_{D(f) ∩ Spf A})`.

The remaining assertions of the section are recorded separately: the bijection
`Mor_{LTRS}(Spf B, Spf A) = Hom_cont(A, B)` is Stacks 0AHZ
(`AlgebraicGeometry.bijective_spfLTRSMap`), the full faithfulness of
`Schemes → Formal Schemes` is Stacks 0AI0, the identification `Spf A = Spec A` for discrete `A`
is `AlgebraicGeometry.isAdmissible_discrete` and `AlgebraicGeometry.discreteSpecSpfIsoOn`, and the
adjunction and equivalence of pseudo-discrete sheaves are
`AlgebraicGeometry.pseudoDiscreteSetSheafAdjunction` and
`AlgebraicGeometry.pseudoDiscreteSetSheafEquivalence` (sets),
`AlgebraicGeometry.pseudoDiscreteGroupSheafAdjunction` and
`AlgebraicGeometry.pseudoDiscreteGroupSheafEquivalence` (groups),
`AlgebraicGeometry.pseudoDiscreteSheafAdjunction` and
`AlgebraicGeometry.pseudoDiscreteSheafEquivalence` (rings), and
`AlgebraicGeometry.pseudoDiscreteModuleSheafAdjunction` and
`AlgebraicGeometry.pseudoDiscreteModuleSheafEquivalence` (modules over a ring). -/
@[stacks 0AHY "the formal spectrum (Spf A, 𝒪_{Spf A}) of an admissible topological ring"]
theorem spf_isThickening_isIso_isSheaf_isLocalRing_basicOpen (hA : IsAdmissible A) :
    (IsFundamentalIdealSystem A IsIdealOfDefinition) ∧
    (∀ (I J : IdealsOfDefinition A) (hJI : J.1 ≤ I.1),
      Stacks.Thickenings.IsThickening
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJI)))) ∧
    (∀ I : IdealsOfDefinition A, IsIso (spfOfQuotient A I)) ∧
    (spfPresheaf A).IsSheaf ∧
    (∀ x : spfSpace A, IsLocalRing ((spfPresheaf A).stalk x).α) ∧
    IsIso (spfGammaHom A) ∧
    (∀ f : A,
      Nonempty ((spfPresheaf A).obj (op (spfBasicOpen A f)) ≅
        TopCommRingCat.of (localizedCompletion A f)) ∧
      Nonempty ((spfPresheaf A).obj (op (spfBasicOpen A f)) ≅
        limit (spfAwayDiagramOn A IsIdealOfDefinition f)) ∧
      IsAdmissible (localizedCompletion A f) ∧
      Nonempty ((Spf A).restrict (f := (spfBasicOpen A f).inclusion')
        (spfBasicOpen A f).isOpenEmbedding' ≅ Spf (localizedCompletion A f))) :=
  ⟨isFundamentalIdealSystem_isIdealOfDefinition hA.1,
    fun I J hJI => isThickening_specMap_factor_of_isIdealOfDefinition A I.2 J.2 hJI,
    fun _ => inferInstance,
    isSheaf_spfPresheaf A hA.1,
    isLocalRing_stalk_spfPresheaf A hA.1,
    isIso_spfGammaHom A hA,
    fun f => ⟨⟨spfBasicOpenGammaIso A hA f⟩,
      ⟨spfBasicOpenIsoOn A IsIdealOfDefinition
        (isWeaklyPreAdmissible_of_isPreAdmissible hA.1) f⟩,
      isAdmissible_localizedCompletion A hA f, ⟨spfBasicOpenRestrictIso A hA f⟩⟩⟩

end AlgebraicGeometry

end
