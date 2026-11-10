module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSchemeIsMcQuillan
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOver
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The affine formal open subschemes form a basis

For a weakly admissible ring `A` and `f ∈ A`, the open `D(f)` of `Spfw A` is McQuillan's formal
spectrum of the completion `A_{f}` of `A_f` along the weak ideals of definition of `A`: the
quotients `A_{f} / ker(A_{f} → A_f / I A_f)` are the localizations `(A/I)_f`, and the kernels are
initial among the weak ideals of definition of `A_{f}` because its topology is induced from `A`.
When `A` is admissible so is `A_{f}`, and McQuillan's formal spectrum of an admissible ring is its
formal spectrum (`AlgebraicGeometry.spfIsoSpfw`). Hence the basic opens of an affine formal open
subscheme are affine formal open subschemes (EGA I 10.1.4), and the affine formal open subschemes
of a formal scheme à la EGA form a basis of its topology — the geometric input of the locality
statements of Stacks 0AIW.

## Main results

* `AlgebraicGeometry.exists_affineFormalOpen_le`: inside an affine formal open subscheme, every
  neighbourhood of a point contains an affine formal open neighbourhood.
* `AlgebraicGeometry.IsFormalScheme.exists_isAffineFormalOpen_mem_le`: the affine formal open
  subschemes of a formal scheme à la EGA form a basis.

## References

* [EGA I, 10.1.4]
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY)
* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopologicalRing
open TopologicalRing.CompletionOver

namespace AlgebraicGeometry

universe u

namespace SpfwBasicOpen

/-- Pseudo-discretisation commutes with restriction along an open embedding, as functors. -/
noncomputable def pseudoDiscreteRestrictFunctorIso
    {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : Topology.IsOpenEmbedding f) :
    pseudoDiscreteFunctor ⋙
      (Functor.whiskeringLeft _ _ TopCommRingCat).obj hf.functor.op ≅
    (Functor.whiskeringLeft _ _ CommRingCat).obj hf.functor.op ⋙
      pseudoDiscreteFunctor :=
  NatIso.ofComponents (fun F => (pseudoDiscreteWhiskerIso f hf F).symm)
    (by
      intro F G η
      ext U x
      rfl)

section

variable {R S : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

/-- The continuous map of spaces of open primes induced by a continuous ring homomorphism. -/
def weakSpfMapBase (φ : R →+* S) (hφ : Continuous φ) :
    spfSpace S ⟶ spfSpace R :=
  TopCat.ofHom ⟨fun p => ⟨PrimeSpectrum.comap φ p.1, p.2.preimage hφ⟩,
    ((PrimeSpectrum.continuous_comap φ).comp continuous_subtype_val).subtype_mk _⟩

/-- The map of structure sheaves of `Spec (R/I) → Spec (S/K)` induced by `R → S`, for weak ideals
of definition `I ⊆ φ⁻¹(K)`, viewed on the spaces of open primes. -/
noncomputable def spfComponentOnMap (φ : R →+* S) (hφ : Continuous φ)
    (I : WeakIdealsOfDefinition R) (K : WeakIdealsOfDefinition S)
    (hIK : I.1 ≤ K.1.comap φ) :
    spfComponentOn R I ⟶ weakSpfMapBase φ hφ _* spfComponentOn S K :=
  Functor.whiskerLeft _ (Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ hIK))).c

/-- The maps `spfComponentOnMap` are compatible with the transition maps of the two inverse
systems. -/
theorem spfComponentOnMap_naturality (φ : R →+* S) (hφ : Continuous φ)
    {I J : WeakIdealsOfDefinition R} {K L : WeakIdealsOfDefinition S}
    (hIJ : I.1 ≤ J.1) (hKL : K.1 ≤ L.1)
    (hIK : I.1 ≤ K.1.comap φ) (hJL : J.1 ≤ L.1.comap φ) :
    spfTransitionOn R hIJ ≫ spfComponentOnMap φ hφ J L hJL =
      spfComponentOnMap φ hφ I K hIK ≫
        Functor.whiskerLeft (Opens.map (weakSpfMapBase φ hφ)).op
          (spfTransitionOn S hKL) := by
  have heq : Spec.map (CommRingCat.ofHom (Ideal.quotientMap L.1 φ hJL)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hIJ)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hKL)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ hIK)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    rfl
  refine NatTrans.ext (funext fun V => ?_)
  have hh := Scheme.Hom.congr_app heq
    ((Opens.map (spfOfQuotientOn R I)).obj V.unop)
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hIJ))).c.app
      (op ((Opens.map (spfOfQuotientOn R I)).obj V.unop)) ≫
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap L.1 φ hJL))).c.app _ =
    ((Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ hIK))).c.app
      (op ((Opens.map (spfOfQuotientOn R I)).obj V.unop)) ≫
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hKL))).c.app _) ≫
      (Spec (spfQuotientOn S L)).presheaf.map (𝟙 _) at hh
  rw [(Spec (spfQuotientOn S L)).presheaf.map_id] at hh
  exact hh.trans (Category.comp_id _)

end

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] (hA : IsWeaklyAdmissible A)

/-- The completion `A_{f}` of the localization `A_f` along the weak ideals of definition of `A`. -/
abbrev localizedCompletion (f : A) := CompletionOver (algebraMap A (Localization.Away f))

/-- The kernel of the projection `A_{f} → A_f / I A_f`, a weak ideal of definition of `A_{f}`. -/
def completionKernel (f : A) (I : WeakIdealsOfDefinition A) :
    WeakIdealsOfDefinition (localizedCompletion A f) :=
  ⟨RingHom.ker (projection (algebraMap A (Localization.Away f)) I),
    TopologicalRing.projection_ker_isWeakIdealOfDefinition _ I⟩

/-- The canonical map `A → A_{f}` carries `I` into the kernel of the projection at `I`. -/
theorem le_comap_completionKernel (f : A) (I : WeakIdealsOfDefinition A) :
    I.1 ≤ (completionKernel A f I).1.comap
      (canonicalMap (algebraMap A (Localization.Away f))) := by
  intro a ha
  change projection (algebraMap A (Localization.Away f)) I
    (canonicalMap (algebraMap A (Localization.Away f)) a) = 0
  rw [projection_canonicalMap, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ ha

/-- The kernel of the projection at `I` grows with `I`. -/
theorem completionKernel_mono (f : A) : Monotone (completionKernel A f) := by
  intro I J hIJ x hx
  change projection _ J x = 0
  change projection _ I x = 0 at hx
  have h := x.2 I J hIJ
  change transitionMap (algebraMap A (Localization.Away f)) hIJ
    (projection (algebraMap A (Localization.Away f)) I x) =
    projection (algebraMap A (Localization.Away f)) J x at h
  rw [← h, hx, map_zero]

/-- The kernels of the projections, as a functor between the posets of weak ideals of
definition. -/
def completionKernelFunctor (f : A) :
    WeakIdealsOfDefinition A ⥤ WeakIdealsOfDefinition (localizedCompletion A f) :=
  (completionKernel_mono A f).functor

include hA in
/-- The kernels of the projections are initial among the weak ideals of definition of `A_{f}`,
whose topology is induced from `A` (`isTaut_canonicalMap`). -/
theorem completionKernelFunctor_initial (f : A) :
    (completionKernelFunctor A f).Initial := by
  have : IsCodirectedOrder (WeakIdealsOfDefinition A) :=
    ⟨fun I J => ⟨spfIndexMeet A I J,
      (show I.1 ⊓ J.1 ≤ I.1 from inf_le_left),
      (show I.1 ⊓ J.1 ≤ J.1 from inf_le_right)⟩⟩
  apply (completionKernel_mono A f).initial_functor_iff.mpr
  intro K
  have hb := ((RingHom.isTaut_iff_hasBasis_isWeakIdealOfDefinition
    (canonicalMap (algebraMap A (Localization.Away f)))
    (TopologicalRing.continuous_canonicalMap _)
    hA).mp
    (TopologicalRing.isTaut_canonicalMap _ hA.1)).2
  obtain ⟨I, hI, hIK⟩ := hb.mem_iff.mp (K.2.1.mem_nhds K.1.zero_mem)
  refine ⟨⟨I, hI⟩, ?_⟩
  change RingHom.ker (projection (algebraMap A (Localization.Away f)) ⟨I, hI⟩) ≤ K.1
  rw [TopologicalRing.CompletionOver.ker_projection_eq_closure]
  exact hIK

/-- The map `A/I → A_{f} / ker` induced by the canonical map. -/
def quotientLocalizationMap (f : A) (I : WeakIdealsOfDefinition A) :
    A ⧸ I.1 →+* localizedCompletion A f ⧸ (completionKernel A f I).1 :=
  Ideal.quotientMap _ (canonicalMap (algebraMap A (Localization.Away f)))
    (le_comap_completionKernel A f I)

/-- The quotient of `A_{f}` by the kernel of the projection at `I` is `A_f / I A_f`. -/
noncomputable def completionQuotientEquiv (f : A) (I : WeakIdealsOfDefinition A) :
    localizedCompletion A f ⧸ (completionKernel A f I).1 ≃+*
      Localization.Away f ⧸ I.1.map (algebraMap A (Localization.Away f)) :=
  RingHom.quotientKerEquivOfSurjective
    (f := projection (algebraMap A (Localization.Away f)) I)
    (TopologicalRing.CompletionOver.projection_surjective _ I)

/-- Through `completionQuotientEquiv`, the map `A/I → A_{f}/ker` is the localization map. -/
theorem completionQuotientEquiv_comp (f : A) (I : WeakIdealsOfDefinition A) :
    (completionQuotientEquiv A f I).toRingHom.comp (quotientLocalizationMap A f I) =
      algebraMap (A ⧸ I.1)
        (Localization.Away f ⧸ I.1.map (algebraMap A (Localization.Away f))) := by
  ext a
  rfl

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- `A_f / I A_f` is the localization of `A/I` at the image of `f`. -/
theorem isLocalization_away_quotient (f : A) (I : WeakIdealsOfDefinition A) :
    IsLocalization.Away (Ideal.Quotient.mk I.1 f)
      (Localization.Away f ⧸ I.1.map (algebraMap A (Localization.Away f))) := by
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers, IsLocalization.Away,
    Ideal.Quotient.algebraMap_eq] using
    (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ I.1) (Submonoid.powers f))
      (Localization.Away f ⧸ I.1.map (algebraMap A (Localization.Away f))))

/-- `Spec (A_{f}/ker) → Spec (A/I)` is an open immersion: it is the localization at `f`. -/
theorem quotientLocalization_isOpenImmersion (f : A) (I : WeakIdealsOfDefinition A) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (quotientLocalizationMap A f I))) := by
  let R := Localization.Away f ⧸ I.1.map (algebraMap A (Localization.Away f))
  have := isLocalization_away_quotient A f I
  let e := (completionQuotientEquiv A f I).toCommRingCatIso
  have heq : CommRingCat.ofHom (quotientLocalizationMap A f I) =
      CommRingCat.ofHom (algebraMap (A ⧸ I.1) R) ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change CommRingCat.ofHom ((completionQuotientEquiv A f I).toRingHom.comp
      (quotientLocalizationMap A f I)) = _
    exact congrArg CommRingCat.ofHom (completionQuotientEquiv_comp A f I)
  rw [heq, Spec.map_comp]
  have := IsOpenImmersion.of_isLocalization (S := R) (Ideal.Quotient.mk I.1 f)
  infer_instance

/-- The map `Spf A_{f} → Spf A` of spaces of open primes. -/
noncomputable def localizationBase (f : A) :
    spfSpace (localizedCompletion A f) ⟶ spfSpace A :=
  weakSpfMapBase (canonicalMap (algebraMap A (Localization.Away f)))
    (TopologicalRing.continuous_canonicalMap _)

/-- The map of spaces of open primes is the map of spectra of the quotients. -/
theorem localizationBase_comp_quotient (f : A) (I : WeakIdealsOfDefinition A) :
    spfOfQuotientOn (localizedCompletion A f) (completionKernel A f I) ≫
        localizationBase A f =
      (Spec.map (CommRingCat.ofHom (quotientLocalizationMap A f I))).base ≫
        spfOfQuotientOn A I := by
  rfl

include hA in
/-- The map of spaces of open primes is an open embedding. -/
theorem localizationBase_isOpenEmbedding (f : A) :
    Topology.IsOpenEmbedding (localizationBase A f) := by
  obtain ⟨I⟩ : Nonempty (WeakIdealsOfDefinition A) := ⟨weaklyPreAdmissibleSpfIndex A hA.1⟩
  have := isIso_spfOfQuotientOn (localizedCompletion A f) (completionKernel A f I)
  have := isIso_spfOfQuotientOn A I
  have := quotientLocalization_isOpenImmersion A f I
  have heq : localizationBase A f =
      inv (spfOfQuotientOn (localizedCompletion A f) (completionKernel A f I)) ≫
      (Spec.map (CommRingCat.ofHom (quotientLocalizationMap A f I))).base ≫
      spfOfQuotientOn A I := by
    rw [← localizationBase_comp_quotient, IsIso.inv_hom_id_assoc]
  rw [heq]
  exact (TopCat.homeoOfIso (asIso (spfOfQuotientOn A I))).isOpenEmbedding.comp
    ((Spec.map (CommRingCat.ofHom (quotientLocalizationMap A f I))).isOpenEmbedding.comp
      (TopCat.homeoOfIso (asIso (spfOfQuotientOn (localizedCompletion A f)
        (completionKernel A f I)))).symm.isOpenEmbedding)

/-- The map of the structure sheaves of the quotient spectra at `I`. -/
noncomputable def localizationComponentMap (f : A) (I : WeakIdealsOfDefinition A) :
    spfComponentOn A I ⟶
      (localizationBase A f) _* spfComponentOn (localizedCompletion A f)
        (completionKernel A f I) :=
  Functor.whiskerLeft _ (Spec.map (CommRingCat.ofHom (quotientLocalizationMap A f I))).c

/-- Pushing forward along an open embedding and restricting back is the identity. -/
noncomputable def restrictPushforwardIso
    {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : Topology.IsOpenEmbedding f)
    (F : X.Presheaf CommRingCat.{u}) : hf.functor.op ⋙ f _* F ≅ F :=
  NatIso.ofComponents (fun U => F.mapIso (eqToIso (show
      (Opens.map f).obj (hf.functor.obj U.unop) = U.unop from
        SetLike.coe_injective (Set.preimage_image_eq _ hf.injective))).symm.op)
    (by
      intro U V i
      dsimp
      simp only [← F.map_comp]
      congr 1)

/-- A point of `Spf A_{f}` in `S` maps to the point of `Spf A` given by `p ∈ Spec (A/I)` exactly
when `p` comes from a point of `Spec (A_{f}/ker)` lying over `S`. -/
private theorem exists_mem_localizationBase_eq_iff (f : A) (I : WeakIdealsOfDefinition A)
    (S : Set (spfSpace (localizedCompletion A f))) (p : PrimeSpectrum (A ⧸ I.1)) :
    (∃ w ∈ S, localizationBase A f w = spfOfQuotientOn A I p) ↔
      ∃ q, spfOfQuotientOn (localizedCompletion A f) (completionKernel A f I) q ∈ S ∧
        Spec.map (CommRingCat.ofHom (quotientLocalizationMap A f I)) q = p := by
  have := isIso_spfOfQuotientOn A I
  have := isIso_spfOfQuotientOn (localizedCompletion A f) (completionKernel A f I)
  let eA : PrimeSpectrum (A ⧸ I.1) ≃ₜ spfSpace A :=
    TopCat.homeoOfIso (asIso (spfOfQuotientOn A I))
  let eB := TopCat.homeoOfIso (asIso
    (spfOfQuotientOn (localizedCompletion A f) (completionKernel A f I)))
  change (∃ w ∈ S, localizationBase A f w = eA p) ↔ ∃ q, eB q ∈ S ∧ _ = p
  constructor
  · rintro ⟨w, hw, heq⟩
    obtain ⟨q, rfl⟩ := eB.surjective w
    exact ⟨q, hw, eA.injective heq⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨eB q, hq, rfl⟩

/-- The image of an open of `Spf A_{f}`, pulled back to `Spec (A/I)`, is the image of its
pullback to `Spec (A_{f}/ker)`. -/
theorem localization_preimage_image (f : A) (I : WeakIdealsOfDefinition A)
    (hf : Topology.IsOpenEmbedding (localizationBase A f))
    (U : Opens (spfSpace (localizedCompletion A f))) :
    (Opens.map (spfOfQuotientOn A I)).obj (hf.functor.obj U) =
      (quotientLocalization_isOpenImmersion A f I).base_open.functor.obj
        ((Opens.map (spfOfQuotientOn (localizedCompletion A f)
          (completionKernel A f I))).obj U) :=
  SetLike.ext fun p => exists_mem_localizationBase_eq_iff A f I U p

/-- The map of structure sheaves at `I` is an isomorphism over the image of every open. -/
theorem localizationComponentMap_isIso (f : A) (I : WeakIdealsOfDefinition A)
    (hf : Topology.IsOpenEmbedding (localizationBase A f))
    (U : Opens (spfSpace (localizedCompletion A f))) :
    IsIso ((localizationComponentMap A f I).app (op (hf.functor.obj U))) := by
  change IsIso ((Spec.map (CommRingCat.ofHom (quotientLocalizationMap A f I))).c.app
    (op ((Opens.map (spfOfQuotientOn A I)).obj (hf.functor.obj U))))
  rw [localization_preimage_image A f I hf U]
  exact (quotientLocalization_isOpenImmersion A f I).c_iso _

/-- The maps of structure sheaves are compatible with the transition maps. -/
theorem localizationComponentMap_naturality (f : A)
    {I J : WeakIdealsOfDefinition A} (h : I ≤ J) :
    spfTransitionOn A h ≫ localizationComponentMap A f J =
      localizationComponentMap A f I ≫
        Functor.whiskerLeft (Opens.map (localizationBase A f)).op
          (spfTransitionOn (localizedCompletion A f) (completionKernel_mono A f h)) :=
  spfComponentOnMap_naturality (canonicalMap (algebraMap A (Localization.Away f)))
    (TopologicalRing.continuous_canonicalMap _) h (completionKernel_mono A f h)
    (le_comap_completionKernel A f I) (le_comap_completionKernel A f J)

/-- The maps of structure sheaves, as a map of inverse systems. -/
noncomputable def localizationComponentDiagramMap (f : A) :
    spfDiagramOn A IsWeakIdealOfDefinition ⟶ completionKernelFunctor A f ⋙
      spfDiagramOn (localizedCompletion A f) IsWeakIdealOfDefinition ⋙
        TopCat.Presheaf.pushforward CommRingCat (localizationBase A f) where
  app I := localizationComponentMap A f I
  naturality _ _ h := localizationComponentMap_naturality A f (leOfHom h)

/-- `restrictPushforwardIso`, as a natural isomorphism. -/
noncomputable def restrictPushforwardFunctorIso
    {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : Topology.IsOpenEmbedding f) :
    TopCat.Presheaf.pushforward CommRingCat f ⋙
      (Functor.whiskeringLeft _ _ CommRingCat).obj hf.functor.op ≅
        𝟭 (X.Presheaf CommRingCat) :=
  NatIso.ofComponents (restrictPushforwardIso hf) fun η =>
    NatTrans.ext (funext fun _ => (η.naturality _).symm)

/-- The inverse system of `Spfw A`, restricted to the image of `Spf A_{f}`, is the inverse system
of `Spfw A_{f}` reindexed along the kernels of the projections. -/
noncomputable def localizationRestrictedDiagramIso (f : A)
    (hf : Topology.IsOpenEmbedding (localizationBase A f)) :
    spfDiagramOn A IsWeakIdealOfDefinition ⋙
        (Functor.whiskeringLeft _ _ CommRingCat).obj hf.functor.op ≅
      completionKernelFunctor A f ⋙
        spfDiagramOn (localizedCompletion A f) IsWeakIdealOfDefinition := by
  let R := (Functor.whiskeringLeft _ _ CommRingCat).obj hf.functor.op
  let η := Functor.whiskerRight (localizationComponentDiagramMap A f) R
  letI : IsIso η := by
    have (I : WeakIdealsOfDefinition A) : IsIso (η.app I) := by
      have (U : (Opens (spfSpace (localizedCompletion A f)))ᵒᵖ) :
          IsIso ((η.app I).app U) :=
        localizationComponentMap_isIso A f I hf U.unop
      exact NatIso.isIso_of_isIso_app _
    exact NatIso.isIso_of_isIso_app _
  exact asIso η ≪≫
    Functor.isoWhiskerLeft (completionKernelFunctor A f ⋙
        spfDiagramOn (localizedCompletion A f) IsWeakIdealOfDefinition)
      (restrictPushforwardFunctorIso hf)

/-- The image of `Spec (A_{f}/ker) → Spec (A/I)` is the basic open of `f`. -/
theorem range_quotientLocalization (f : A) (I : WeakIdealsOfDefinition A) :
    Set.range (PrimeSpectrum.comap (quotientLocalizationMap A f I)) =
      (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I.1 f) : Set (PrimeSpectrum (A ⧸ I.1))) := by
  let R := Localization.Away f ⧸ I.1.map (algebraMap A (Localization.Away f))
  have := isLocalization_away_quotient A f I
  let e := (completionQuotientEquiv A f I).toCommRingCatIso
  have he : Function.Surjective
      (PrimeSpectrum.comap (completionQuotientEquiv A f I).toRingHom) :=
    (TopCat.homeoOfIso ((Scheme.forgetToTop).mapIso (asIso (Spec.map e.hom)))).surjective
  have hc := congrArg PrimeSpectrum.comap (completionQuotientEquiv_comp A f I)
  rw [PrimeSpectrum.comap_comp] at hc
  rw [← PrimeSpectrum.localization_away_comap_range R (Ideal.Quotient.mk I.1 f), ← hc,
    Set.range_comp, he.range_eq, Set.image_univ]

include hA in
/-- The image of `Spf A_{f} → Spf A` is `D(f)`. -/
theorem mem_range_localizationBase (f : A) (p : spfSpace A) :
    p ∈ Set.range (localizationBase A f) ↔ f ∉ p.1.asIdeal := by
  obtain ⟨I⟩ : Nonempty (WeakIdealsOfDefinition A) := ⟨weaklyPreAdmissibleSpfIndex A hA.1⟩
  have := isIso_spfOfQuotientOn A I
  obtain ⟨r, rfl⟩ := (TopCat.homeoOfIso (asIso (spfOfQuotientOn A I))).surjective p
  change (∃ w, localizationBase A f w = spfOfQuotientOn A I r) ↔
    r ∈ (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I.1 f) : Set (PrimeSpectrum (A ⧸ I.1)))
  rw [← range_quotientLocalization A f I]
  refine Iff.trans (by simp) ((exists_mem_localizationBase_eq_iff A f I Set.univ r).trans ?_)
  simp only [Set.mem_univ, true_and]
  exact Iff.rfl

/-- The structure sheaf of `Spfw A` restricted to `D(f)` is that of `Spfw A_{f}`: the limits agree
because the kernels of the projections are initial. -/
noncomputable def weakSpfRestrictIso (hA : IsWeaklyAdmissible A) (f : A)
    (hf : Topology.IsOpenEmbedding (localizationBase A f)) :
    hf.functor.op ⋙ spfPresheafOn A IsWeakIdealOfDefinition ≅
      spfPresheafOn (localizedCompletion A f) IsWeakIdealOfDefinition := by
  let R := (Functor.whiskeringLeft _ _ TopCommRingCat).obj hf.functor.op
  let K := completionKernelFunctor A f
  have := completionKernelFunctor_initial A hA f
  let G := spfDiagramOn (localizedCompletion A f) IsWeakIdealOfDefinition ⋙ pseudoDiscreteFunctor
  letI : ∀ U, HasLimit (G.flip.obj U) := fun _ =>
    HasLimit.mk ⟨TopCommRingCat.limitCone _, TopCommRingCat.limitConeIsLimit _⟩
  letI : HasLimit G := CategoryTheory.Limits.functorCategoryHasLimit G
  exact preservesLimitIso R (spfDiagramOn A IsWeakIdealOfDefinition ⋙ pseudoDiscreteFunctor) ≪≫
    HasLimit.isoOfNatIso
      ((Functor.isoWhiskerLeft (spfDiagramOn A IsWeakIdealOfDefinition)
          (pseudoDiscreteRestrictFunctorIso hf)) ≪≫
        Functor.isoWhiskerRight (localizationRestrictedDiagramIso A f hf)
          pseudoDiscreteFunctor) ≪≫
    Functor.Initial.limitIso K
      (spfDiagramOn (localizedCompletion A f) IsWeakIdealOfDefinition ⋙ pseudoDiscreteFunctor)

include hA in
/-- `Spfw A` restricted to `D(f)` is `Spfw A_{f}`. -/
noncomputable def localizationSpectrumIso (f : A)
    (hf : Topology.IsOpenEmbedding (localizationBase A f)) :
    (Spfw A).restrict hf ≅ Spfw (localizedCompletion A f) :=
  PresheafedSpace.isoOfComponents (Iso.refl _) (weakSpfRestrictIso A hA f hf)

include hA in
/-- The open immersion `Spfw A_{f} → Spfw A` onto `D(f)`. -/
noncomputable def localizationSpectrumMap (f : A) :
    Spfw (localizedCompletion A f) ⟶ Spfw A :=
  (localizationSpectrumIso A hA f (localizationBase_isOpenEmbedding A hA f)).inv ≫
    (Spfw A).ofRestrict (localizationBase_isOpenEmbedding A hA f)

/-- The inverse of an isomorphism onto a restriction, followed by the inclusion, is an open
immersion. -/
private theorem isOpenImmersion_inv_comp_ofRestrict {C : Type*} [Category C] {X : PresheafedSpace C}
    {U : TopCat} {j : U ⟶ X.carrier} (hj : Topology.IsOpenEmbedding j) {Y : PresheafedSpace C}
    (e : X.restrict hj ≅ Y) : PresheafedSpace.IsOpenImmersion (e.inv ≫ X.ofRestrict hj) :=
  PresheafedSpace.IsOpenImmersion.comp (H := PresheafedSpace.IsOpenImmersion.ofIso e.symm)
    (hg := PresheafedSpace.IsOpenImmersion.ofRestrict X hj) _ _

include hA in
/-- `Spfw A_{f} → Spfw A` is an open immersion. -/
theorem localizationSpectrumMap_isOpenImmersion (f : A) :
    PresheafedSpace.IsOpenImmersion (localizationSpectrumMap A hA f) := by
  exact isOpenImmersion_inv_comp_ofRestrict _
    (localizationSpectrumIso A hA f (localizationBase_isOpenEmbedding A hA f))

include hA in
/-- Every neighbourhood of a point of `Spfw A` contains the image of some `Spfw A_{f}`
containing the point. -/
theorem exists_localization_range_le (U : Opens (spfSpace A))
    (x : spfSpace A) (hx : x ∈ U) :
    ∃ f : A, x ∈ Set.range (localizationSpectrumMap A hA f).base ∧
      Set.range (localizationSpectrumMap A hA f).base ⊆ (U : Set (spfSpace A)) := by
  have hb := PrimeSpectrum.isTopologicalBasis_basic_opens.induced
    (Subtype.val : spfSpace A → PrimeSpectrum A)
  obtain ⟨W, ⟨S, ⟨f, rfl⟩, rfl⟩, hxW, hWU⟩ :=
    hb.mem_nhds_iff.mp (U.isOpen.mem_nhds hx)
  refine ⟨f, ?_, ?_⟩
  · change x ∈ Set.range (localizationBase A f)
    exact (mem_range_localizationBase A hA f x).mpr hxW
  · intro y hy
    change y ∈ Set.range (localizationBase A f) at hy
    exact hWU ((mem_range_localizationBase A hA f y).mp hy)

end

end SpfwBasicOpen

/-- The image of an open immersion from the formal spectrum of an admissible ring is an affine
formal open. -/
theorem isAffineFormalOpen_range_of_isOpenImmersion (X : LTRS.{u}) (B : TopCommRingCat.{u})
    [IsLinearTopology B.α B.α] (hB : TopologicalRing.IsAdmissible B.α)
    {g : Spfw B.α ⟶ X.toPresheafedSpace} (hg : PresheafedSpace.IsOpenImmersion g) :
    IsAffineFormalOpen X ⟨Set.range g.base, hg.base_open.isOpen_range⟩ := by
  let U : Opens X := ⟨Set.range g.base, hg.base_open.isOpen_range⟩
  let : PresheafedSpace.IsOpenImmersion
      (X.toPresheafedSpace.ofRestrict (f := U.inclusion') U.isOpenEmbedding') :=
    PresheafedSpace.IsOpenImmersion.ofRestrict X.toPresheafedSpace
      (f := U.inclusion') U.isOpenEmbedding'
  exact ⟨B, inferInstance, hB, ⟨PresheafedSpace.IsOpenImmersion.isoOfRangeEq
    (X.toPresheafedSpace.ofRestrict (f := U.inclusion') U.isOpenEmbedding') g
    Subtype.range_coe_subtype ≪≫ (spfIsoSpfw B.α hB.1).symm⟩⟩

open SpfwBasicOpen in
/-- **The affine formal open subschemes of an affine formal open form a basis of it.** Inside an
affine formal open `V ≅ Spf A`, every open neighbourhood of a point contains the image of a basic
open `D(f) ≅ Spf A_{f}`, which is an affine formal open subscheme: `A_{f}` is admissible, its
topology being induced from `A` (EGA I 10.1.4). -/
theorem exists_affineFormalOpen_le
    (X : LTRS.{u}) (V W : Opens X) (hV : IsAffineFormalOpen X V)
    (hWV : W ≤ V) (x : X) (hx : x ∈ W) :
    ∃ U : Opens X, U ≤ W ∧ x ∈ U ∧ IsAffineFormalOpen X U := by
  obtain ⟨A, hlin, hAd, ⟨chart⟩⟩ := hV
  let := hlin
  have hA : IsWeaklyAdmissible A.α :=
    ⟨⟨hAd.1.choose, isWeakIdealOfDefinition_of_isIdealOfDefinition hAd.1.choose_spec⟩,
      hAd.2.2, hAd.2.1⟩
  let e := chart ≪≫ spfIsoSpfw A.α hAd.1
  let φ : Spfw A.α ⟶ X.toPresheafedSpace :=
    e.inv ≫ X.toPresheafedSpace.ofRestrict V.isOpenEmbedding'
  let hφ : PresheafedSpace.IsOpenImmersion φ :=
    isOpenImmersion_inv_comp_ofRestrict V.isOpenEmbedding' e
  let ey : V ≃ₜ spfSpace A.α :=
    TopCat.homeoOfIso ((PresheafedSpace.forget _).mapIso e)
  let y : spfSpace A.α := ey ⟨x, hWV hx⟩
  have hy : φ.base y = x := by
    change (ey.symm (ey ⟨x, hWV hx⟩)).val = x
    simp
  obtain ⟨f, ⟨z, hz⟩, hf⟩ := exists_localization_range_le A.α hA
    ((Opens.map φ.base).obj W) y (show φ.base y ∈ W by rwa [hy])
  let g : Spfw (localizedCompletion A.α f) ⟶ X.toPresheafedSpace :=
    localizationSpectrumMap A.α hA f ≫ φ
  let hg : PresheafedSpace.IsOpenImmersion g :=
    PresheafedSpace.IsOpenImmersion.comp
      (H := localizationSpectrumMap_isOpenImmersion A.α hA f) (hg := hφ) _ _
  have hAf := RingHom.isPreAdmissible_of_isTaut
    (canonicalMap (algebraMap A.α (Localization.Away f)))
    (TopologicalRing.isTaut_canonicalMap _ hA.1) hAd.1
  refine ⟨⟨Set.range g.base, hg.base_open.isOpen_range⟩, ?_, ?_,
    isAffineFormalOpen_range_of_isOpenImmersion X (TopCommRingCat.of (localizedCompletion A.α f))
      ⟨hAf, ⟨inferInstance, inferInstance⟩⟩ hg⟩
  · rintro t ⟨w, rfl⟩
    exact hf ⟨w, rfl⟩
  · refine ⟨z, ?_⟩
    change φ.base ((localizationSpectrumMap A.α hA f).base z) = x
    rw [hz, hy]

/-- **The affine formal open subschemes of a formal scheme à la EGA form a basis of its
topology.** -/
@[ega "I 10.4.3"]
theorem IsFormalScheme.exists_isAffineFormalOpen_mem_le {X : LTRS.{u}} (hX : IsFormalScheme X)
    {W : Opens X} {x : X} (hx : x ∈ W) :
    ∃ U : Opens X, U ≤ W ∧ x ∈ U ∧ IsAffineFormalOpen X U := by
  obtain ⟨V, hxV, hV⟩ := (isFormalScheme_iff_forall_isAffineFormalOpen X).mp hX x
  obtain ⟨U, hU, hxU, hUaff⟩ := exists_affineFormalOpen_le X V (V ⊓ W) hV inf_le_left x ⟨hxV, hx⟩
  exact ⟨U, hU.trans inf_le_right, hxU, hUaff⟩

end AlgebraicGeometry

end
