module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupStrictTransformSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCompositeCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupStrictTransformSpaceEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismClosedImmersionLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperLimitOfFinitePresentationEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionAfterAdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformFlatCompositionUnassumed
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformIsoNearClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformOverAdmissibleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionIntoQuotientStackSubspace
import all StacksFrontier.AlgebraicGeometry.Spaces.ProperFiniteLocallyFreeOverOpenBlowup

/-!
# A proper morphism made an isomorphism near a closure by an admissible blowup

Let `S` be a scheme and let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with
`Y` quasi-compact and quasi-separated.  Let `V ⊆ Y` be a quasi-compact open subspace and let
`T ⊆ |V|` be a closed subset such that `f` is an isomorphism over an open neighbourhood of `T`
in `V`.  Stacks 0F47 asserts that there is a `V`-admissible blowup `Y' ⟶ Y` such that the
strict transform `f' : X' ⟶ Y'` of `f` is an isomorphism over an open neighbourhood of the
closure of `T` in `|Y'|`.

The source applies Stacks 087F, which is
`AlgebraicGeometry.Space.exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp`,
proved from Stacks 087E and 0868 in the form corrected by a separatedness hypothesis; it is
applied here to a proper, hence separated, morphism.  The proof is otherwise the source's.

## Main results

* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isIso_strictTransform_near_closure`:
  Stacks 0F47.

## Implementation notes

Let `T'` be the complement in `|V|` of the given neighbourhood of `T`; the source takes the
complement of the largest open over which `f` is an isomorphism, but any closed set disjoint from
`T` off which `f` is an isomorphism serves.  Since `|V|` is spectral (Stacks 0A4G) there are
disjoint constructible closed subsets `Tc ⊇ T` and `T'c ⊇ T'`, and Stacks 0F46 gives a
`V`-admissible blowup `b₁ : Y₁ ⟶ Y` in which their closures `K, K'` are disjoint.

The source then works over `Y₀ = Y₁ ∖ K'` and applies Stacks 087F there, which requires `Y₀` to
be quasi-compact.  The complement of the closure of a constructible set need not be
quasi-compact, so here `Y₀` is instead a quasi-compact open with `K ⊆ Y₀ ⊆ Y₁ ∖ K'`, which exists
because `K` is closed in the spectral space `|Y₁|`.  Over `V₁ ∩ Y₀`, where `V₁ = b₁⁻¹(V)`, the
strict transform `X₁ ⟶ Y₁` of `f` is an isomorphism, so Stacks 087F gives a
`V₁ ∩ Y₀`-admissible blowup `Y'₀ ⟶ Y₀` whose strict transform is an open immersion.  Its centre
extends to a centre of finite presentation on `Y₁` disjoint from `V₁` (the closed-subspace form
of Stacks 0853, which is what Stacks 086D rests on), and `Y'` is the blowup of `Y₁` in it.  The
composite `Y' ⟶ Y₁ ⟶ Y` is the blowup of `Y` in the composite centre of Stacks 0860, which misses
`V`.

The strict transform with respect to the composite is identified with the iterated strict
transform by Stacks 0868, part (2)
(`AlgebraicGeometry.Space.exists_strictTransformSpace_comp_iso_unconditional`); this is the step
the source abbreviates as "after replacing `Y` by a `V`-admissible blowup".  The iterated strict
transform restricts over `Y'₀ ⊆ Y'` to the strict transform of `X₁ ×_{Y₁} Y₀` by Stacks 0863
part (2), in the form `AlgebraicGeometry.Space.exists_strictTransform_eq_preimage_of_isEtale`.
Being proper and an open immersion, it is an isomorphism over its image, which is closed in `Y'₀`
and contains every point over `T`; so it contains the closure of `T`.

"Isomorphism over an open subspace `W`" is the statement that the base change
`f⁻¹(W) ⟶ W` of `f` along the inclusion of `W` is an isomorphism, written
`IsIso (pullback.snd f W.ι)`.

## References

* [Stacks Project, Tag 0F47](https://stacks.math.columbia.edu/tag/0F47)
* [Stacks Project, Tag 0F3W](https://stacks.math.columbia.edu/tag/0F3W)
* [Stacks Project, Tag 087F](https://stacks.math.columbia.edu/tag/087F)
* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 0868](https://stacks.math.columbia.edu/tag/0868)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 0860](https://stacks.math.columbia.edu/tag/0860)
* [Stacks Project, Tag 0A4G](https://stacks.math.columbia.edu/tag/0A4G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Stacks 0F47 -/

/-- **Stacks 0F47.**  Let `S` be a scheme, let
`f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with `Y` quasi-compact and
quasi-separated, let `V ⊆ Y` be a quasi-compact open subspace and let `T ⊆ |V|` be a closed
subset such that `f` is an isomorphism over an open neighbourhood `W ⊆ V` of `T`.  Then there
is a `V`-admissible blowup `b : Y' ⟶ Y` such that the strict transform `f' : X' ⟶ Y'` of `f`
is an isomorphism over an open neighbourhood `W'` of the closure of `T` in `|Y'|`.

The centre `Yc` of the blowup is recorded, since the strict transform is taken relative to it.
The closure of `T` in `|Y'|` is the closure of the set of points of `Y'` mapping into the image of
`T` in `|Y|`.  Quasi-compactness and quasi-separatedness of `X` are not used and are omitted.

Stacks 087F enters in its corrected form,
`AlgebraicGeometry.Space.exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp`,
applied to a proper, hence separated, morphism.  See the module documentation for the proof. -/
theorem exists_isAdmissibleBlowup_isIso_strictTransform_near_closure
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS}
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (V : OpenSubspaces B S hS Y.1) (hVqc : IsQuasiCompactSpace B S hS V.1.toFunctor)
    (T : Set (points B S hS V.1.toFunctor)) (hT : IsClosed T)
    (hW : ∃ W : OpenSubspaces B S hS Y.1, W.1 ≤ V.1 ∧
      pointsMap B S hS _ V.1.ι '' T ⊆ subspacePointSet B S hS Y.1 W.1 ∧
      IsIso (pullback.snd f.hom W.1.ι)) :
    ∃ (Y' : AlgebraicSpaces B S hS) (b : Y' ⟶ Y) (Yc : ClosedSubspaces B S hS Y.1),
      IsAdmissibleBlowup B S hS V b ∧ IsFinitePresentation B S hS Yc.1.ι ∧
        Disjoint (subspacePointSet B S hS Y.1 V.1) (subspacePointSet B S hS Y.1 Yc.1) ∧
          IsBlowupAlong B S hS Yc b ∧
            ∃ W' : OpenSubspaces B S hS Y'.1,
              closure (pointsMap B S hS _ b.hom ⁻¹' (pointsMap B S hS _ V.1.ι '' T)) ⊆
                  subspacePointSet B S hS Y'.1 W'.1 ∧
                IsIso (pullback.snd
                  (strictTransformSpaceToBlowUp B S hS f b (Yc.1.preimage b.hom)).hom
                  W'.1.ι) := by
  classical
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  obtain ⟨W, hWV, hTW, hWiso⟩ := hW
  -- the topology of `|V|`
  have : CompactSpace (points B S hS V.1.toFunctor) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS V.2.1 hVqc
  have hVemb : Topology.IsOpenEmbedding (pointsMap B S hS _ V.1.ι) :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_pointsMap B S hS _)
      (pointsMap_injective_of_mono B S hS _) (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ V.2.2)
  have : QuasiSeparatedSpace (points B S hS Y.1) :=
    quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated B S hS Y.1 Y.2 hYqs
  have : QuasiSeparatedSpace (points B S hS V.1.toFunctor) := hVemb.quasiSeparatedSpace
  have : PrespectralSpace (points B S hS V.1.toFunctor) := prespectralSpace_points B S hS _ V.2.1
  -- the complement `T'` of the locus over which `f` is an isomorphism
  set T' : Set (points B S hS V.1.toFunctor) :=
    pointsMap B S hS _ V.1.ι ⁻¹' (subspacePointSet B S hS Y.1 W.1)ᶜ with hT'def
  have hWopen : IsOpen (subspacePointSet B S hS Y.1 W.1) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS _ W.2.2
  have hT' : IsClosed T' :=
    hWopen.isClosed_compl.preimage (continuous_pointsMap B S hS _)
  have hTT' : Disjoint T T' :=
    Set.disjoint_left.2 fun t ht ht' => ht' (hTW ⟨t, ht, rfl⟩)
  obtain ⟨Tc, T'c, hTc, hT'c, hcTc, hcT'c, hTTc, hT'T'c, hTcT'c⟩ :=
    Topology.exists_isConstructible_isClosed_supersets_of_disjoint hT hT' hTT'
  -- the first blowup separates the closures of `Tc` and `T'c`
  obtain ⟨Y₁, b₁, ⟨Z₁, hZ₁fp, hZ₁V, hb₁⟩, hsep⟩ :=
    exists_isAdmissibleBlowup_disjoint_closure hZ hYqc hYqs V hVqc Tc T'c hTc hT'c hcTc hcT'c
      hTcT'c
  have hb₁P := isProper_of_isBlowupAlong_of_isFinitePresentation B S hS Z₁ b₁ hZ₁fp hb₁
  obtain ⟨hY₁qc, hY₁qs⟩ :=
    isQuasiCompactSpace_and_isAbsolutelyQuasiSeparated_of_isBlowupAlong hZ hYqc hYqs hZ₁fp hb₁
  have : CompactSpace (points B S hS Y₁.1) :=
    compactSpace_points_of_isQuasiCompactSpace B S hS Y₁.2 hY₁qc
  have : QuasiSeparatedSpace (points B S hS Y₁.1) :=
    quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated B S hS Y₁.1 Y₁.2 hY₁qs
  have : PrespectralSpace (points B S hS Y₁.1) := prespectralSpace_points B S hS _ Y₁.2
  -- a quasi-compact open `Y₀` between the two closures
  obtain ⟨G, hGc, hGo, hKG, hGK'⟩ := PrespectralSpace.exists_isCompact_and_isOpen_between
    isClosed_closure.isCompact isClosed_closure.isOpen_compl
    (Set.subset_compl_iff_disjoint_right.2 hsep)
  set Y₀s := openSubspaceOfPoints B S hS Y₁.1 G with hY₀s
  have hY₀ : IsOpenSubspace B S hS Y₀s := isOpenSubspace_openSubspaceOfPoints B S hS Y₁.2 G hGo
  have hY₀pts : subspacePointSet B S hS Y₁.1 Y₀s = G :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS G
  have hY₀qc : IsQuasiCompactSpace B S hS Y₀s.toFunctor :=
    isQuasiCompactSpace_openSubspaceOfPoints hGo hGc
  have hY₀qs : IsAbsolutelyQuasiSeparated B S hS hZ Y₀s.toFunctor :=
    isAbsolutelyQuasiSeparated_of_mono B S hS hZ hY₀.1 Y₀s.ι inferInstance hY₁qs
  set Y₀ : AlgebraicSpaces B S hS := ⟨Y₀s.toFunctor, hY₀.1⟩ with hY₀def
  set v : Y₀ ⟶ Y₁ := ObjectProperty.homMk Y₀s.ι with hv
  -- the strict transform of `f` along `b₁`
  set f₁ := strictTransformSpaceToBlowUp B S hS f b₁ (Z₁.1.preimage b₁.hom) with hf₁def
  have hf₁ : IsProper B S hS f₁.hom := isProper_strictTransformSpaceToBlowUp_of_isProper f b₁ _ hf
  set V₁ : OpenSubspaces B S hS Y₁.1 :=
    ⟨V.1.preimage b₁.hom, isOpenSubspace_preimage B S hS b₁.hom V.1 Y.2 Y₁.2 V.2⟩ with hV₁
  have hV₁qc : IsQuasiCompactSpace B S hS V₁.1.toFunctor :=
    isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS Y.2 Y₁.2 b₁.hom hb₁P.2.1.2 V.2 hVqc
  have hWZ₁ : Disjoint (subspacePointSet B S hS Y.1 W.1) (subspacePointSet B S hS Y.1 Z₁.1) :=
    hZ₁V.mono_left (range_pointsMap_ι_le B S hS hWV)
  have hf₁W : IsIso (pullback.snd f₁.hom (W.1.preimage b₁.hom).ι) :=
    isIso_pullbackSnd_strictTransformSpaceToBlowUp f b₁ Z₁ hb₁ W hWZ₁ hWiso
  -- the restriction of `f₁` over `Y₀`
  have hX₁₀ : IsOpenSubspace B S hS (Y₀s.preimage f₁.hom) :=
    isOpenSubspace_preimage B S hS f₁.hom Y₀s Y₁.2
      (strictTransformSpace B S hS f b₁ (Z₁.1.preimage b₁.hom)).2 hY₀
  set X₁₀ : AlgebraicSpaces B S hS := ⟨(Y₀s.preimage f₁.hom).toFunctor, hX₁₀.1⟩ with hX₁₀def
  set u : X₁₀ ⟶ strictTransformSpace B S hS f b₁ (Z₁.1.preimage b₁.hom) :=
    ObjectProperty.homMk (Y₀s.preimage f₁.hom).ι with hu
  set w : X₁₀ ⟶ Y₀ := ObjectProperty.homMk (Y₀s.fromPreimage f₁.hom) with hw
  have hsq : IsPullback u.hom w.hom f₁.hom v.hom :=
    (Subfunctor.isPullback_preimage f₁.hom Y₀s).flip
  have hsqA : IsPullback u w f₁ v :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) hsq
  have hwP : IsProper B S hS w.hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback hsqA hf₁
  set U₀ : OpenSubspaces B S hS Y₀.1 :=
    ⟨V₁.1.preimage Y₀s.ι, isOpenSubspace_preimage B S hS Y₀s.ι V₁.1 Y₁.2 hY₀.1 V₁.2⟩ with hU₀
  -- the points of `V₁ ∩ Y₀` lie over the locus `W` where `f` is an isomorphism
  have hU₀W : V₁.1 ⊓ Y₀s ≤ W.1.preimage b₁.hom := by
    refine le_of_subspacePointSet_subset Y₁.2 (isOpenSubspace_inf B S hS Y₁.2 _ _ V₁.2 hY₀)
      (isOpenSubspace_preimage B S hS b₁.hom W.1 Y.2 Y₁.2 W.2) ?_
    rintro x hx
    rw [subspacePointSet_inf] at hx
    obtain ⟨hxV, hxG⟩ := hx
    rw [hY₀pts] at hxG
    show x ∈ Set.range (pointsMap B S hS _ (W.1.preimage b₁.hom).ι)
    rw [range_pointsMap_preimage_ι]
    have hxV' : pointsMap B S hS _ b₁.hom x ∈ subspacePointSet B S hS Y.1 V.1 := by
      have := hxV
      rw [show subspacePointSet B S hS Y₁.1 V₁.1 = Set.range (pointsMap B S hS _
        (V.1.preimage b₁.hom).ι) from rfl, range_pointsMap_preimage_ι] at this
      exact this
    by_contra hxW
    obtain ⟨t, ht⟩ := hxV'
    refine hGK' hxG (subset_closure ⟨t, hT'T'c ?_, ht⟩)
    show pointsMap B S hS _ V.1.ι t ∈ (subspacePointSet B S hS Y.1 W.1)ᶜ
    rw [ht]
    exact hxW
  have hw_iso : IsIso (pullback.snd w.hom U₀.1.ι) := by
    refine isIso_pullbackSnd_of_isPullback_of_isIso_comp hsq U₀.1.ι ?_
    have hle : Subfunctor.range (U₀.1.ι ≫ Y₀s.ι) ≤ W.1.preimage b₁.hom := by
      refine le_trans ?_ hU₀W
      rintro T _ ⟨y, rfl⟩
      exact ⟨y.2, y.1.2⟩
    exact isIso_pullbackSnd_of_eq_comp _ _ _ (Subfunctor.lift_ι (U₀.1.ι ≫ Y₀s.ι) hle).symm hf₁W
  have hU₀qc : IsQuasiCompactSpace B S hS U₀.1.toFunctor := by
    refine isQuasiCompactSpace_of_isOpenImmersion_of_isCompact U₀.2.1 (U₀.1.ι ≫ Y₀s.ι)
      (isOpenImmersion_comp B S hS _ _ U₀.2.2 hY₀.2) ?_
    have hr : Set.range (pointsMap B S hS _ U₀.1.ι) =
        pointsMap B S hS _ Y₀s.ι ⁻¹' subspacePointSet B S hS Y₁.1 V₁.1 :=
      range_pointsMap_preimage_ι B S hS Y₀s.ι V₁.1
    rw [pointsMap_comp, Set.range_comp, hr, Set.image_preimage_eq_inter_range]
    show IsCompact (subspacePointSet B S hS Y₁.1 V₁.1 ∩ subspacePointSet B S hS Y₁.1 Y₀s)
    rw [hY₀pts]
    exact (isCompact_range_of_isQuasiCompactSpace B S hS V₁.2 hV₁qc).inter_of_isOpen hGc
      (isOpen_range_pointsMap_of_isOpenImmersion B S hS _ V₁.2.2) hGo
  -- Stacks 087F over `Y₀`
  obtain ⟨Y'₀, c₀, Z'₀, hZ'₀fp, hZ'₀U₀, hc₀, -, hopen⟩ :=
    exists_isBlowupAlong_isOpenImmersion_strictTransformSpaceToBlowUp hZ w U₀ hY₀qc hY₀qs hU₀qc
      hwP.2.1 hwP.1 hw_iso
      (fun g hX hY hf hqc hqs =>
        exists_integralFiniteSystem_isClosedImmersion_of_isFinite g hX hY hf hqc hqs)
      (fun f hX hY hft hsep hqc hqs => by
        obtain ⟨X', i, f', hX', hi, hf'sep, hf'fp, hif⟩ :=
          exists_isClosedImmersion_isSeparated_isFinitePresentation_of_isFiniteType B S hS hX hY f
            hft hsep hqc hqs
        exact ⟨X', f', i, hX', hf'sep, hf'fp, hi, hif⟩)
  -- the centre extends to `Y₁` (Stacks 0853 in the form of 086D)
  obtain ⟨Z's, hZ'c, hZ'fp, hZ'V₁, hZ'Y₀⟩ := exists_closedSubspace_extension_disjoint hZ hY₁qc
    hY₁qs V₁.1 Y₀s V₁.2 hY₀ hV₁qc hY₀qc Z'₀.1 Z'₀.2 hZ'₀fp hZ'₀U₀
  set Z' : ClosedSubspaces B S hS Y₁.1 := ⟨Z's, hZ'c⟩ with hZ'def
  obtain ⟨Y', c, hc⟩ := exists_isBlowupAlong_of_isFinitePresentation Z' hZ'fp
  -- the composite blowup (Stacks 0860)
  obtain ⟨Yc, hYcfp, hYccomp, hYcb⟩ :=
    exists_isCompositeCentre_isBlowupAlong_of_isQuasiCompactSpace hZ hYqc hYqs hb₁ hZ₁fp hc hZ'fp
  have hYcV : Disjoint (subspacePointSet B S hS Y.1 V.1) (subspacePointSet B S hS Y.1 Yc.1) := by
    have hY : subspacePointSet B S hS Y.1 Yc.1 = subspacePointSet B S hS Y.1 Z₁.1 ∪
        pointsMap B S hS Y₁.1 b₁.hom '' subspacePointSet B S hS Y₁.1 Z'.1 := hYccomp
    rw [hY]
    refine Set.disjoint_union_right.2 ⟨hZ₁V, Set.disjoint_left.2 fun y hyV ⟨z, hz, hzy⟩ => ?_⟩
    refine Set.disjoint_left.1 hZ'V₁ ?_ hz
    show z ∈ Set.range (pointsMap B S hS _ (V.1.preimage b₁.hom).ι)
    rw [range_pointsMap_preimage_ι, Set.mem_preimage, hzy]
    exact hyV
  -- Stacks 0863 (2): the strict transform over `Y₀`
  have hvE : IsEtale B S hS v.hom := isEtale_ι_of_isOpenSubspace hY₀
  have huE : IsEtale B S hS u.hom := isEtale_ι_of_isOpenSubspace hX₁₀
  have hcomm : u ≫ f₁ = w ≫ v := ObjectProperty.hom_ext _ hsq.w
  have hpre : preimageClosedSubspace v Z' = Z'₀ := Subtype.ext hZ'Y₀
  have hv' : IsBlowupAlong B S hS (preimageClosedSubspace v Z') c₀ := hpre ▸ hc₀
  obtain ⟨m, can, hsqm, hcanE, hcanS, hcanB, hcanP, hST⟩ :=
    exists_strictTransform_eq_preimage_of_isEtale B S hS hc hvE huE hcomm hv'
      (strictTransform_exists_of_isEffectiveCartierDivisor B S hS f₁ c
        (preimageClosedSubspace c Z') hc.isPullbackDefined)
  -- Stacks 0868: the strict transform along the composite
  obtain ⟨k, j, -, hk, hj⟩ :=
    exists_strictTransformSpace_comp_iso_unconditional B S hS f b₁ c Z₁ Z' Yc hb₁ hc hYccomp hYcb
  refine ⟨Y', c ≫ b₁, Yc, ⟨Yc, hYcfp, hYcV, hYcb⟩, hYcfp, hYcV, hYcb, ?_⟩
  -- the three strict transforms
  set F₀ := strictTransformSpaceToBlowUp B S hS w c₀ (Z'₀.1.preimage c₀.hom) with hF₀
  set F'' := strictTransformSpaceToBlowUp B S hS f₁ c (Z'.1.preimage c.hom) with hF''
  set F' := strictTransformSpaceToBlowUp B S hS f (c ≫ b₁) (Yc.1.preimage (c ≫ b₁).hom)
    with hF'
  have hF''F' : F'' = j.hom ≫ F' := by
    simp only [hF'', hF', strictTransformSpaceToBlowUp]
    rw [← Category.assoc, hj, Category.assoc, hk]
  have hF₀P : IsProper B S hS F₀.hom := isProper_strictTransformSpaceToBlowUp_of_isProper w c₀ _ hwP
  have : Mono F₀.hom := mono_of_isOpenImmersion B S hS _ hopen
  set O₀ := Subfunctor.range F₀.hom with hO₀def
  have hO₀ : IsOpenSubspace B S hS O₀ :=
    isOpenSubspace_range_of_isOpenImmersion_of_isAlgebraicSpace B S hS F₀.hom
      (strictTransformSpace B S hS w c₀ _).2 hopen
  have hm : IsOpenImmersion B S hS m.hom := isOpenImmersion_of_isPullback B S hS hsqm hY₀.2
  have hι : IsOpenImmersion B S hS (O₀.ι ≫ m.hom) := isOpenImmersion_comp B S hS _ _ hO₀.2 hm
  have : Mono (O₀.ι ≫ m.hom) := mono_of_isOpenImmersion B S hS _ hι
  set W's := Subfunctor.range (O₀.ι ≫ m.hom) with hW's
  have hW' : IsOpenSubspace B S hS W's :=
    isOpenSubspace_range_of_isOpenImmersion_of_isAlgebraicSpace B S hS _ hO₀.1 hι
  refine ⟨⟨W's, hW'⟩, ?_, ?_⟩
  · intro x hx
    -- the points over `T` lie over the closure `K` of the points over `Tc`
    have hβ : pointsMap B S hS _ (c ≫ b₁).hom ⁻¹' (pointsMap B S hS _ V.1.ι '' T) ⊆
        pointsMap B S hS _ c.hom ⁻¹'
          closure (pointsMap B S hS _ b₁.hom ⁻¹' (pointsMap B S hS _ V.1.ι '' Tc)) := by
      rintro y ⟨t, ht, hty⟩
      refine subset_closure ⟨t, hTTc ht, ?_⟩
      rw [hty]
      exact pointsMap_comp_apply B S hS c.hom b₁.hom y
    have hxK := closure_minimal hβ
      (isClosed_closure.preimage (continuous_pointsMap B S hS c.hom)) hx
    -- the points of `Y'` over `Y₀` come from `Y'₀`
    have hrange_m : ∀ y, pointsMap B S hS _ c.hom y ∈ G →
        y ∈ Set.range (pointsMap B S hS _ m.hom) := by
      intro y hy
      rw [← hY₀pts] at hy
      obtain ⟨g₀, hg₀⟩ := hy
      obtain ⟨p, -, hp⟩ := exists_points_of_isPullback B S hS
        (AlgebraicSpaces.isPullback_hom B S hS hsqm) g₀ y hg₀
      exact ⟨p, hp⟩
    obtain ⟨x₀, rfl⟩ := hrange_m x (hKG hxK)
    -- the range of `F₀` is closed, and contains the points of `Y'₀` over `T`
    have hrangeF₀ : IsClosed (Set.range (pointsMap B S hS _ F₀.hom)) :=
      (isClosed_of_universallyClosed B S hS Y'₀.2 F₀.hom hF₀P.2.2).isClosed_range
    have hF₀iso : IsIso (pullback.snd F₀.hom (U₀.1.preimage c₀.hom).ι) :=
      isIso_pullbackSnd_strictTransformSpaceToBlowUp w c₀ Z'₀ hc₀ U₀ hZ'₀U₀ hw_iso
    have hA₀ : pointsMap B S hS _ m.hom ⁻¹'
        (pointsMap B S hS _ (c ≫ b₁).hom ⁻¹' (pointsMap B S hS _ V.1.ι '' T)) ⊆
          Set.range (pointsMap B S hS _ F₀.hom) := by
      rintro y₀ ⟨t, -, ht⟩
      have hcm : pointsMap B S hS _ v.hom (pointsMap B S hS _ c₀.hom y₀) =
          pointsMap B S hS _ c.hom (pointsMap B S hS _ m.hom y₀) := by
        rw [← pointsMap_comp_apply, ← pointsMap_comp_apply]
        exact congrArg (fun k => pointsMap B S hS _ k y₀) (congrArg (fun k => k.hom) hsqm.w)
      have h1 : y₀ ∈ Set.range (pointsMap B S hS _ (U₀.1.preimage c₀.hom).ι) := by
        rw [range_pointsMap_preimage_ι, Set.mem_preimage]
        show pointsMap B S hS _ c₀.hom y₀ ∈
          Set.range (pointsMap B S hS _ (V₁.1.preimage Y₀s.ι).ι)
        rw [range_pointsMap_preimage_ι, Set.mem_preimage]
        show pointsMap B S hS _ v.hom (pointsMap B S hS _ c₀.hom y₀) ∈ _
        rw [hcm]
        show _ ∈ Set.range (pointsMap B S hS _ (V.1.preimage b₁.hom).ι)
        rw [range_pointsMap_preimage_ι, Set.mem_preimage]
        refine ⟨t, ?_⟩
        rw [ht]
        exact pointsMap_comp_apply B S hS c.hom b₁.hom _
      obtain ⟨q, hq⟩ := h1
      obtain ⟨p, hp⟩ := pointsMap_surjective_of_isIso B S hS
        (pullback.snd F₀.hom (U₀.1.preimage c₀.hom).ι) q
      refine ⟨pointsMap B S hS _ (pullback.fst F₀.hom (U₀.1.preimage c₀.hom).ι) p, ?_⟩
      rw [← pointsMap_comp_apply, pullback.condition, pointsMap_comp_apply, hp, hq]
    have hmopen : IsOpenMap (pointsMap B S hS _ m.hom) :=
      isOpenMap_pointsMap_of_isOpenImmersion B S hS _ hm
    have hx₀ : x₀ ∈ closure (pointsMap B S hS _ m.hom ⁻¹'
        (pointsMap B S hS _ (c ≫ b₁).hom ⁻¹' (pointsMap B S hS _ V.1.ι '' T))) := by
      rw [← hmopen.preimage_closure_eq_closure_preimage (continuous_pointsMap B S hS _)]
      exact hx
    obtain ⟨z, hz⟩ := closure_minimal hA₀ hrangeF₀ hx₀
    show _ ∈ subspacePointSet B S hS Y'.1 W's
    rw [subspacePointSet_range]
    refine ⟨pointsMap B S hS _ (Subfunctor.toRange F₀.hom) z, ?_⟩
    rw [pointsMap_comp_apply, ← pointsMap_comp_apply B S hS (Subfunctor.toRange F₀.hom),
      Subfunctor.toRange_ι, hz]
  · -- `F₀` is an isomorphism over its range
    have hA1 : IsIso (pullback.snd F₀.hom O₀.ι) := by
      have hk : IsIso (pullback.snd O₀.ι O₀.ι) :=
        isIso_pullbackSnd_of_isPullback (IsKernelPair.id_of_mono O₀.ι) inferInstance
      exact isIso_pullbackSnd_of_eq (Subfunctor.toRange_ι F₀.hom) rfl
        (isIso_pullbackSnd_iso_comp (asIso (Subfunctor.toRange F₀.hom)) O₀.ι O₀.ι hk)
    -- the strict transform over `Y'₀` is the base change of the one over `Y'`
    rw [hpre] at hST
    obtain ⟨φ, hS1⟩ := exists_isPullback_of_eq_preimage can.hom hST
    have hS2 : IsPullback can.hom (strictTransformPullbackToBlowUp B S hS w c₀).hom
        (strictTransformPullbackToBlowUp B S hS f₁ c).hom m.hom :=
      IsPullback.of_cube pullback.condition pullback.condition hsq
        (AlgebraicSpaces.isPullback_hom B S hS hsqm) (AlgebraicSpaces.isPullback_hom B S hS hcanP)
        (congrArg (fun k => k.hom) hcanB)
    have hQ : IsPullback φ F₀.hom F''.hom m.hom := hS1.paste_vert hS2
    have hA3 : IsIso (pullback.snd F''.hom (O₀.ι ≫ m.hom)) :=
      isIso_pullbackSnd_of_isPullback ((IsPullback.of_hasPullback F₀.hom O₀.ι).paste_horiz hQ) hA1
    have hA4 : IsIso (pullback.snd F''.hom W's.ι) :=
      isIso_pullbackSnd_of_isIso_comp F''.hom W's.ι (asIso (Subfunctor.toRange (O₀.ι ≫ m.hom)))
        (isIso_pullbackSnd_of_eq rfl (Subfunctor.toRange_ι _).symm hA3)
    let jP : (strictTransformSpace B S hS f₁ c (Z'.1.preimage c.hom)).1 ≅
        (strictTransformSpace B S hS f (c ≫ b₁) (Yc.1.preimage (c ≫ b₁).hom)).1 :=
      { hom := j.hom.hom, inv := j.inv.hom,
        hom_inv_id := congrArg (fun k => k.hom) j.hom_inv_id,
        inv_hom_id := congrArg (fun k => k.hom) j.inv_hom_id }
    refine isIso_pullbackSnd_of_eq ?_ rfl (isIso_pullbackSnd_iso_comp jP.symm F''.hom W's.ι hA4)
    rw [hF''F']
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ F'.hom) (congrArg (fun k => k.hom) j.inv_hom_id)).trans
        (Category.id_comp _))

end AlgebraicGeometry.Space
