module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Finite
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.BaseFieldExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.IsoOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Components
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.PurelyInseparableField
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Reduction
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.QuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# Normalization after a finite purely inseparable extension

For a scheme of finite type over a field `k` there is a finite purely inseparable extension
`k'/k` over which the normalization of the base change becomes geometrically normal.

## Main results

* `AlgebraicGeometry.exists_isPurelyInseparable_isGeometricallyNormal_normalization` is the
  existence of such an extension.
* `AlgebraicGeometry.isGeometricallyNormal_of_isNormal_of_perfectField`: a normal scheme over a
  perfect field is geometrically normal.

## Implementation notes

An algebraic `k`-scheme is a scheme whose structure morphism is locally of finite type and
quasi-compact, and the base change to `k'` is the categorical pullback of that structure
morphism along `Spec k' ⟶ Spec k`, viewed over `k'` by the first projection.

The extension is found inside the perfect closure `k^perf` of `k`, taken in an algebraic
closure: the normalization over `k^perf` is normal, hence geometrically normal because
`k^perf` is perfect, and it is of finite presentation, so it is the base change of a finite
morphism over a finite subextension. Bijectivity on generic points and the closed immersion
over a dense open descend to that subextension because the comparison morphism is a flat
surjective universal homeomorphism, and they identify the descended morphism with the
normalization morphism there.

## References

* [Stacks Project, Tag 0BXT](https://stacks.math.columbia.edu/tag/0BXT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

open CommRingCat

/-- Over a perfect field every finite purely inseparable extension is trivial, so a normal
scheme over a perfect field is geometrically normal. -/
public theorem isGeometricallyNormal_of_isNormal_of_perfectField (k : Type u) [Field k]
    [PerfectField k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsNormal Y] :
    IsGeometricallyNormal f := by
  refine ((geometricallyNormal_tfae k Y f).out 4 1).mp ?_
  intro L _ _ _ _
  have _ : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  have _ : IsIso (ofHom (algebraMap k L)) := (RingEquiv.ofBijective (algebraMap k L)
    ⟨FaithfulSMul.algebraMap_injective k L,
      IsPurelyInseparable.surjective_algebraMap_of_isSeparable k L⟩).toCommRingCatIso.isIso_hom
  exact isNormal_of_iso (asIso (pullback.fst f (Spec.map (ofHom (algebraMap k L)))))

/-! ### Recognizing the normalization morphism -/

/-- A quasi-compact universally closed morphism whose image contains every generic point of the
target is surjective. -/
private theorem surjective_of_genericPoints_subset_range {A B : Scheme.{u}} (f : A ⟶ B)
    [QuasiCompact f] [UniversallyClosed f] (hf : genericPoints B ⊆ Set.range f) :
    Surjective f :=
  have : IsDominant f := (isDominant_iff_genericPoints_subset_range f).mpr hf
  inferInstance

/-- A morphism of schemes over a Noetherian target that bijects generic points and restricts to
an isomorphism over a dense open is birational: the generic points lie in the dense open, where
the stalk maps are those of an isomorphism. -/
private theorem isBirational_of_bijOn_genericPoints_of_isIso_morphismRestrict
    {A B : Scheme.{u}} [NoetherianSpace B] (f : A ⟶ B)
    (hbij : Set.BijOn f (genericPoints A) (genericPoints B))
    (U : B.Opens) (hU : Dense (U : Set B)) [IsIso (f ∣_ U)] : IsBirational f := by
  refine ⟨hbij, fun x hx ↦ ?_⟩
  have hxU : x ∈ f ⁻¹ᵁ U := mem_of_mem_genericPoints_of_dense U hU (hbij.mapsTo hx)
  exact (MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _)
    (morphismRestrictStalkMap f U ⟨x, hxU⟩)).mp
    (((isIso_iff_isIso_stalkMap (f ∣_ U)).mp inferInstance).2 ⟨x, hxU⟩)

/-- A finite morphism onto an algebraic `k`-scheme from a normal scheme which bijects generic
points and restricts to a closed immersion over a dense open is the normalization morphism. -/
private theorem exists_iso_normalizationSchemeOverField (k : Type u) [Field k]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]
    (f : Y ⟶ X) [IsFinite f] [IsNormal Y]
    (hbij : Set.BijOn f (genericPoints Y) (genericPoints X))
    (U : X.Opens) (hU : Dense (U : Set X)) [IsClosedImmersion (f ∣_ U)] :
    ∃ e : Y ≅ normalizationSchemeOverField k p,
      e.hom ≫ normalizationOverField k p = f := by
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  have _ : IsReduced Y := isReduced_of_isNormal Y
  have _ : IsReduced X.nilradical.subscheme := isReduced_nilradical_subscheme X
  obtain ⟨a, ha, -⟩ := Scheme.existsUnique_lift_nilradical_subschemeι f
  set r := X.nilradical.subschemeι with hrdef
  -- The three schemes in play are algebraic over `k`, hence Noetherian.
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have _ : IsNoetherian X := ⟨⟩
  have _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ p)
  have _ : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ p)
  have _ : IsNoetherian Y := ⟨⟩
  have _ : IsLocallyNoetherian X.nilradical.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (r ≫ p)
  have _ : CompactSpace X.nilradical.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (r ≫ p)
  have _ : IsNoetherian X.nilradical.subscheme := ⟨⟩
  -- The factorization through the reduction is finite and bijective on generic points.
  have _ : IsFinite (a ≫ r) := ha ▸ ‹IsFinite f›
  have _ : IsFinite a := IsFinite.of_comp a r
  let er := X.homeomorphNilradicalSubscheme
  have hra (y : Y) : er (a y) = f y := congrArg (fun q : Y ⟶ X ↦ q y) ha
  have hb : Set.BijOn a (genericPoints Y) (genericPoints X.nilradical.subscheme) := by
    convert (Homeomorph.bijOn_genericPoints er.symm).comp hbij
    funext y
    rw [Function.comp_apply, ← hra y, Homeomorph.symm_apply_apply]
  have _ : Surjective a :=
    surjective_of_genericPoints_subset_range a fun _ hz ↦ Set.image_subset_range _ _ (hb.surjOn hz)
  -- Over the dense open the factorization is a surjective closed immersion, hence an iso.
  have hV : Dense ((r ⁻¹ᵁ U : X.nilradical.subscheme.Opens) : Set X.nilradical.subscheme) :=
    hU.preimage er.isOpenMap
  have _ : IsClosedImmersion ((a ≫ r) ∣_ U) := ha ▸ ‹IsClosedImmersion (f ∣_ U)›
  have _ : IsClosedImmersion ((a ∣_ r ⁻¹ᵁ U) ≫ (r ∣_ U)) :=
    morphismRestrict_comp a r U ▸ ‹IsClosedImmersion ((a ≫ r) ∣_ U)›
  have _ : IsClosedImmersion (a ∣_ r ⁻¹ᵁ U) :=
    IsClosedImmersion.of_comp_isClosedImmersion _ (r ∣_ U)
  have _ : Surjective (a ∣_ r ⁻¹ᵁ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict a (r ⁻¹ᵁ U)).flip ‹Surjective a›
  have _ : IsIso (a ∣_ r ⁻¹ᵁ U) := isIso_of_isClosedImmersion_of_surjective _
  have hbir : IsBirational a :=
    isBirational_of_bijOn_genericPoints_of_isIso_morphismRestrict a hb (r ⁻¹ᵁ U) hV
  -- Hence it is the normalization of the reduction, which is the normalization of `X`.
  obtain ⟨e₁, he₁⟩ :=
    Scheme.exists_iso_normalizationScheme_of_isIntegralHom_of_isBirational
      (X.finite_irreducibleComponents_reduction hX) a
      (fun W hW ↦ finite_irreducibleComponents_of_locallyOfFiniteType k (f ≫ p)
        (a ⁻¹ᵁ W) (a.isCompact_preimage hW))
      (fun W _ ↦ hbir.morphismRestrict W)
  obtain ⟨e₂, he₂⟩ := X.exists_normalizationScheme_iso_reduction hX
  refine ⟨e₁ ≪≫ e₂.symm, ?_⟩
  have hinv : e₂.inv ≫ X.normalization hX =
      X.nilradical.subscheme.normalization (X.finite_irreducibleComponents_reduction hX) ≫ r := by
    rw [← he₂, Iso.inv_hom_id_assoc]
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hinv, ← Category.assoc, he₁, ha]

/-! ### Descent of closed immersions, and the normalization over a dense open -/

/-- The restriction of an isomorphism to an open of the target is a closed immersion. -/
private theorem isClosedImmersion_morphismRestrict_of_isIso {A B : Scheme.{u}} (f : A ⟶ B)
    [IsIso f] (U : B.Opens) : IsClosedImmersion (f ∣_ U) := inferInstance

/-- A closed immersion descends along a flat surjective quasi-compact morphism. -/
private theorem isClosedImmersion_of_isPullback {A B C S : Scheme.{u}}
    {a : A ⟶ B} {b : A ⟶ C} {f : B ⟶ S} {g : C ⟶ S} (h : IsPullback a b f g)
    [Surjective g] [Flat g] [QuasiCompact g] [IsClosedImmersion b] : IsClosedImmersion f := by
  have hsnd : IsClosedImmersion (pullback.snd f g) := by
    rw [← h.isoPullback_inv_snd]
    infer_instance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsClosedImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hsnd

/-- A dense open over which the base change of `f` along a flat surjective quasi-compact
homeomorphism is a closed immersion produces a dense open over which `f` is a closed
immersion. -/
private theorem exists_dense_isClosedImmersion_of_isHomeomorph
    {Y A B : Scheme.{u}} (f : Y ⟶ A) (g : B ⟶ A) [Flat g] [Surjective g] [QuasiCompact g]
    (hg : IsHomeomorph (g : B → A)) (V : B.Opens) (hV : Dense (V : Set B))
    [IsClosedImmersion (pullback.snd f g ∣_ V)] :
    ∃ U : A.Opens, Dense (U : Set A) ∧ IsClosedImmersion (f ∣_ U) := by
  let e := hg.homeomorph
  let U : A.Opens := ⟨e.symm ⁻¹' V, V.2.preimage e.symm.continuous⟩
  have hU : Dense (U : Set A) := hV.preimage e.symm.isOpenMap
  have hUV : g ⁻¹ᵁ U = V := by
    ext x
    change e.symm (e x) ∈ V ↔ x ∈ V
    simp
  have hci : IsClosedImmersion (pullback.snd f g ∣_ g ⁻¹ᵁ U) := by
    rw [hUV]
    infer_instance
  have hpre : (pullback.snd f g) ⁻¹ᵁ (g ⁻¹ᵁ U) =
      (pullback.fst f g) ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ (pullback.snd f g) ⁻¹ᵁ (g ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
    simp
  have hsq := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g)
    (US := U) (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U) le_rfl le_rfl
    (UY := (pullback.snd f g) ⁻¹ᵁ (g ⁻¹ᵁ U)) hpre
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at hsq
  have hsurjr : Surjective (g ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict g U).flip ‹Surjective g›
  have hflatr : Flat (g ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict g U).flip ‹Flat g›
  have hqcr : QuasiCompact (g ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict g U).flip ‹QuasiCompact g›
  exact ⟨U, hU, isClosedImmersion_of_isPullback hsq⟩

/-- The normalization morphism of an algebraic `k`-scheme bijects generic points and is a closed
immersion over a dense open: both descend from the reduction, where it is birational. -/
private theorem bijOn_genericPoints_normalizationOverField (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p] :
    Set.BijOn (normalizationOverField k p)
        (genericPoints (normalizationSchemeOverField k p)) (genericPoints X) ∧
      ∃ U : X.Opens, Dense (U : Set X) ∧
        IsClosedImmersion (normalizationOverField k p ∣_ U) := by
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  have hred : IsReduced X.nilradical.subscheme := isReduced_nilradical_subscheme X
  have hX' := X.finite_irreducibleComponents_reduction hX
  obtain ⟨e, he⟩ := X.exists_normalizationScheme_iso_reduction hX
  have hbir : IsBirational (X.nilradical.subscheme.normalization hX') :=
    X.nilradical.subscheme.isBirational_normalization hX'
  let er := X.homeomorphNilradicalSubscheme
  have hln : IsLocallyNoetherian X.nilradical.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (X.nilradical.subschemeι ≫ p)
  have hcs : CompactSpace X.nilradical.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (X.nilradical.subschemeι ≫ p)
  have hns : IsNoetherian X.nilradical.subscheme := ⟨⟩
  have hfc : Finite (irreducibleComponents X.nilradical.subscheme) :=
    NoetherianSpace.finite_irreducibleComponents
  have hnfin : IsFinite (X.nilradical.subscheme.normalization hX') :=
    isFinite_normalizationOverField k (X.nilradical.subschemeι ≫ p)
  have hnft : LocallyOfFiniteType (X.nilradical.subscheme.normalization hX') := inferInstance
  have hnqc : QuasiCompact (X.nilradical.subscheme.normalization hX') := inferInstance
  have hlnn : IsLocallyNoetherian (X.nilradical.subscheme.normalizationScheme hX') :=
    LocallyOfFiniteType.isLocallyNoetherian (X.nilradical.subscheme.normalization hX')
  have hcsn : CompactSpace (X.nilradical.subscheme.normalizationScheme hX') :=
    QuasiCompact.compactSpace_of_compactSpace (X.nilradical.subscheme.normalization hX')
  have hnsn : IsNoetherian (X.nilradical.subscheme.normalizationScheme hX') := ⟨⟩
  have hfcn : Finite (irreducibleComponents (X.nilradical.subscheme.normalizationScheme hX')) :=
    NoetherianSpace.finite_irreducibleComponents
  refine ⟨?_, ?_⟩
  · have hcomp := (Homeomorph.bijOn_genericPoints er).comp
      (hbir.bijOn.comp (bijOn_genericPoints_of_iso e))
    have heq : ((er : X.nilradical.subscheme → X) ∘
        (((X.nilradical.subscheme.normalization hX') :
            (X.nilradical.subscheme.normalizationScheme hX') → X.nilradical.subscheme) ∘
          ((e.hom : (normalizationSchemeOverField k p) → _)))) =
        (normalizationOverField k p : (normalizationSchemeOverField k p) → X) := by
      funext z
      exact congrArg (fun q : (normalizationSchemeOverField k p) ⟶ X ↦ q z) he
    exact heq ▸ hcomp
  · obtain ⟨V, hV, hiso⟩ := exists_dense_open_isIso_morphismRestrict_of_isBirational
      (X.nilradical.subscheme.normalization hX') hbir (Or.inl hnqc) (Or.inl ⟨hnft, hred⟩)
    let U : X.Opens := ⟨er.symm ⁻¹' V, V.2.preimage er.symm.continuous⟩
    have hU : Dense (U : Set X) := hV.preimage er.symm.isOpenMap
    have hUV : X.nilradical.subschemeι ⁻¹ᵁ U = V := by
      ext x
      change er.symm (er x) ∈ V ↔ x ∈ V
      simp
    have hci : IsClosedImmersion (X.nilradical.subscheme.normalization hX' ∣_
        X.nilradical.subschemeι ⁻¹ᵁ U) := by
      rw [hUV]
      have hi := hiso
      infer_instance
    have hcr : IsClosedImmersion (X.nilradical.subschemeι ∣_ U) := inferInstance
    have hcomp : IsClosedImmersion ((X.nilradical.subscheme.normalization hX' ≫
        X.nilradical.subschemeι) ∣_ U) := by
      rw [morphismRestrict_comp]
      exact @IsClosedImmersion.comp _ _ _ _ _ hci hcr
    have hce : IsClosedImmersion (e.hom ∣_ (X.nilradical.subscheme.normalization hX' ≫
        X.nilradical.subschemeι) ⁻¹ᵁ U) := inferInstance
    have hfinal : normalizationOverField k p =
        e.hom ≫ (X.nilradical.subscheme.normalization hX' ≫ X.nilradical.subschemeι) := he.symm
    refine ⟨U, hU, ?_⟩
    rw [hfinal, morphismRestrict_comp]
    exact @IsClosedImmersion.comp _ _ _ _ _ hce hcomp

/-! ### Spreading out over the finite subextensions -/

/-- The base change of a morphism to a field along an extension of that field is locally of
finite type. -/
private instance locallyOfFiniteType_pullbackFst_spectrumMap (k E : Type u) [Field k] [Field E]
    [Algebra k E] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    LocallyOfFiniteType (pullback.fst (spectrumMap k E) p) :=
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (spectrumMap k E) p).flip ‹LocallyOfFiniteType p›

/-- The base change of a quasi-compact morphism to a field along an extension of that field is
quasi-compact. -/
private instance quasiCompact_pullbackFst_spectrumMap (k E : Type u) [Field k] [Field E]
    [Algebra k E] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [QuasiCompact p] :
    QuasiCompact (pullback.fst (spectrumMap k E) p) :=
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (spectrumMap k E) p).flip ‹QuasiCompact p›

section SpreadOut

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]

/-- Every stage of the diagram of base changes is a compact scheme. -/
private instance compactSpace_fextPullbackDiagram_obj (i : (FExt k K)ᵒᵖ) :
    CompactSpace ((fextPullbackDiagram (k := k) (K := K) X p).obj i) :=
  @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.fst (spectrumMap k i.unop.1) p)
    (quasiCompact_pullbackFst_spectrumMap k i.unop.1 p) inferInstance

/-- Every stage of the diagram of base changes is locally Noetherian. -/
private instance isLocallyNoetherian_fextPullbackDiagram_obj (i : (FExt k K)ᵒᵖ) :
    IsLocallyNoetherian ((fextPullbackDiagram (k := k) (K := K) X p).obj i) :=
  @LocallyOfFiniteType.isLocallyNoetherian _ _ (pullback.fst (spectrumMap k i.unop.1) p)
    (locallyOfFiniteType_pullbackFst_spectrumMap k i.unop.1 p) inferInstance

/-- Every stage of the diagram of base changes is quasi-separated. -/
private instance quasiSeparatedSpace_fextPullbackDiagram_obj (i : (FExt k K)ᵒᵖ) :
    QuasiSeparatedSpace ((fextPullbackDiagram (k := k) (K := K) X p).obj i) :=
  (isLocallyNoetherian_fextPullbackDiagram_obj k K p i).quasiSeparatedSpace

omit [LocallyOfFiniteType p] [QuasiCompact p] in
/-- The leg of the limit cone at a finite subextension `E` is the base change of `Spec K ⟶ Spec E`
along the structure morphism of the stage `E`. -/
private theorem isPullback_fextPullbackCone_π (i : (FExt k K)ᵒᵖ) :
    IsPullback ((fextPullbackCone (k := k) (K := K) X p).π.app i)
      (pullback.fst (spectrumMap k K) p) (pullback.fst (spectrumMap k i.unop.1) p)
      (Spec.map (ofHom (algebraMap i.unop.1 K))) := by
  have hfst : (fextPullbackCone (k := k) (K := K) X p).π.app i ≫
      pullback.fst (spectrumMap k i.unop.1) p =
      pullback.fst (spectrumMap k K) p ≫ Spec.map (ofHom (algebraMap i.unop.1 K)) := by
    dsimp [fextPullbackCone, fextOverCone]
    exact pullback.lift_fst _ _ _
  have hsnd : (fextPullbackCone (k := k) (K := K) X p).π.app i ≫
      pullback.snd (spectrumMap k i.unop.1) p = pullback.snd (spectrumMap k K) p := by
    dsimp [fextPullbackCone, fextOverCone]
    exact pullback.lift_snd _ _ _
  have hfield : Spec.map (ofHom (algebraMap i.unop.1 K)) ≫ spectrumMap k i.unop.1 =
      spectrumMap k K := by
    dsimp [spectrumMap]
    rw [← Spec.map_comp, Spec.map_inj]
    exact congrArg ofHom (IsScalarTower.algebraMap_eq k i.unop.1 K).symm
  have hwide : IsPullback ((fextPullbackCone (k := k) (K := K) X p).π.app i ≫
      pullback.snd (spectrumMap k i.unop.1) p) (pullback.fst (spectrumMap k K) p) p
      (Spec.map (ofHom (algebraMap i.unop.1 K)) ≫ spectrumMap k i.unop.1) := by
    rw [hsnd, hfield]
    exact (IsPullback.of_hasPullback _ _).flip
  exact (IsPullback.paste_horiz_iff
    (IsPullback.of_hasPullback (spectrumMap k i.unop.1) p).flip hfst).mp hwide

/-- **Spreading out.** A finite morphism onto the base change of `p` to an algebraic extension
`K/k` is the base change of a finite morphism onto the base change of `p` to some finite
subextension of `K/k`. -/
private theorem exists_finiteDimensional_isFinite_model
    {W : Scheme.{u}} (ν : W ⟶ pullback (spectrumMap k K) p) [IsFinite ν] :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E) (Z : Scheme.{u})
      (μ : Z ⟶ pullback (spectrumMap k E) p) (_ : IsFinite μ)
      (q : pullback (spectrumMap k K) p ⟶ pullback (spectrumMap k E) p)
      (_ : IsPullback q (pullback.fst (spectrumMap k K) p)
            (pullback.fst (spectrumMap k E) p) (Spec.map (ofHom (algebraMap E K))))
      (φ : pullback μ q ≅ W), φ.hom ≫ ν = pullback.snd μ q := by
  classical
  let D := fextPullbackDiagram (k := k) (K := K) X p
  let c := fextPullbackCone (k := k) (K := K) X p
  have hclim : IsLimit c := fextPullbackConeIsLimit (k := k) (K := K) X p
  have _ : ∀ {i j : (FExt k K)ᵒᵖ} (e : i ⟶ j), IsAffineHom (D.map e) := fun e ↦
    fextPullbackTransition_isAffineHom X p e
  have hfp : FinitePresentation (Over.mk ν).hom := finitePresentation_of_finiteType ν
  obtain ⟨i, Yᵢ, hYᵢ, ⟨eY⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hclim (Over.mk ν) hfp
  let Bᵢ : Over (D.obj i) := Over.mk (𝟙 (D.obj i))
  let fᵢ : Yᵢ ⟶ Bᵢ := Over.homMk Yᵢ.hom (Category.comp_id _)
  have hft : LocallyOfFiniteType Yᵢ.hom :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := Yᵢ.hom)).mp hYᵢ.1
  have hqc : QuasiCompact Yᵢ.hom := hYᵢ.2.1
  have hcY : CompactSpace Yᵢ.left := QuasiCompact.compactSpace_of_compactSpace Yᵢ.hom
  have hqsY : QuasiSeparatedSpace Yᵢ.left :=
    (LocallyOfFiniteType.isLocallyNoetherian Yᵢ.hom).quasiSeparatedSpace
  have hftf : LocallyOfFiniteType fᵢ.left := hft
  have hcB : CompactSpace Bᵢ.left := compactSpace_fextPullbackDiagram_obj k K p i
  have hqsB : QuasiSeparatedSpace Bᵢ.left := quasiSeparatedSpace_fextPullbackDiagram_obj k K p i
  have hcD : CompactSpace (D.obj i) := compactSpace_fextPullbackDiagram_obj k K p i
  have hqsD : QuasiSeparatedSpace (D.obj i) := quasiSeparatedSpace_fextPullbackDiagram_obj k K p i
  -- The model becomes finite after base change to `K`.
  let α : ((Over.pullback (c.π.app i)).obj Yᵢ).left ≅ W := (Over.forget c.pt).mapIso eY.symm
  have hν : α.hom ≫ ν = pullback.snd Yᵢ.hom (c.π.app i) := Over.w eY.inv
  have hbaseπ : ((Over.pullback (c.π.app i)).map fᵢ).left ≫
      pullback.snd (𝟙 (D.obj i)) (c.π.app i) = pullback.snd Yᵢ.hom (c.π.app i) :=
    pullback.lift_snd _ _ _
  have hαiso : IsIso α.hom := α.isIso_hom
  have hfin₀ : IsFinite (((Over.pullback (c.π.app i)).map fᵢ).left ≫
      pullback.snd (𝟙 (D.obj i)) (c.π.app i)) := by
    rw [hbaseπ, ← hν]
    exact MorphismProperty.comp_mem _ _ _ inferInstance ‹IsFinite ν›
  have _ : IsFinite ((Over.pullback (c.π.app i)).map fᵢ).left :=
    IsFinite.of_comp _ (pullback.snd (𝟙 (D.obj i)) (c.π.app i))
  -- Hence it is already finite at some earlier stage.
  obtain ⟨j, g, hfin⟩ := exists_isFinite_baseChange_of_isLimit D c hclim i Yᵢ Bᵢ fᵢ
  have hbase : ((Over.pullback (D.map g)).map fᵢ).left ≫
      pullback.snd (𝟙 (D.obj i)) (D.map g) = pullback.snd Yᵢ.hom (D.map g) :=
    pullback.lift_snd _ _ _
  have hfinZ : IsFinite (pullback.snd Yᵢ.hom (D.map g)) := by
    rw [← hbase]
    infer_instance
  let ψ : (Over.pullback (c.π.app i)).obj Yᵢ ≅
      (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map g)).obj Yᵢ) :=
    (eqToIso (congrArg (fun a ↦ Over.pullback a) (c.w g).symm)).app Yᵢ ≪≫
      (Over.pullbackComp (c.π.app j) (D.map g)).app Yᵢ
  exact ⟨j.unop.1, j.unop.2, ((Over.pullback (D.map g)).obj Yᵢ).left,
    ((Over.pullback (D.map g)).obj Yᵢ).hom, hfinZ, c.π.app j,
    isPullback_fextPullbackCone_π k K p j,
    (Over.forget c.pt).mapIso (eY ≪≫ ψ).symm, Over.w (eY ≪≫ ψ).inv⟩

end SpreadOut

/-! ### The theorem -/

/-- Geometric normality transports along an isomorphism over the base field. -/
public theorem isGeometricallyNormal_of_iso (k : Type u) [Field k] {X Y : Scheme.{u}}
    (e : X ≅ Y) (pY : Y ⟶ Spec (.of k)) (pX : X ⟶ Spec (.of k)) (he : e.hom ≫ pY = pX)
    (hY : IsGeometricallyNormal pY) : IsGeometricallyNormal pX := by
  refine ((geometricallyNormal_tfae k X pX).out 1 2).mpr ?_
  have hY2 : ∀ (L : Type u) [Field L] [Algebra k L],
      IsNormal (pullback pY (Spec.map (ofHom (algebraMap k L)))) :=
    ((geometricallyNormal_tfae k Y pY).out 1 2).mp hY
  intro L _ _
  exact @isNormal_of_iso _ _ ((Over.forget _).mapIso
    ((Over.pullback (Spec.map (ofHom (algebraMap k L)))).mapIso
      (Over.isoMk e he : Over.mk pX ≅ Over.mk pY))) (hY2 L)

/-- Universal homeomorphisms are stable under base change. -/
private instance universalHomeomorphism_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@UniversalHomeomorphism.{u}) where
  of_isPullback sq hg := by
    rw [universalHomeomorphism_iff] at hg ⊢
    exact MorphismProperty.of_isPullback sq hg

/-- The spectrum of a field extension is flat and surjective over the spectrum of the base. -/
private theorem flat_and_surjective_spectrumMap (E F : Type u) [Field E] [Field F] [Algebra E F] :
    Flat (spectrumMap E F) ∧ Surjective (spectrumMap E F) :=
  (flat_and_surjective_SpecMap_iff (ofHom (algebraMap E F))).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)

/-- The statement of Tag 0BXT relative to a fixed perfect, purely inseparable algebraic extension
`K/k`: the finite subextension can be found inside `K`. -/
private theorem exists_finiteDimensional_isGeometricallyNormal_normalizationOverField
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    [IsPurelyInseparable k K] [PerfectField K] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] :
    ∃ (E : IntermediateField k K) (_ : FiniteDimensional k E),
      IsGeometricallyNormal (normalizationOverField (E : Type u)
          (pullback.fst (spectrumMap k (E : Type u)) p) ≫
        pullback.fst (spectrumMap k (E : Type u)) p) := by
  classical
  have hνK : IsFinite (normalizationOverField K (pullback.fst (spectrumMap k K) p)) :=
    isFinite_normalizationOverField K (pullback.fst (spectrumMap k K) p)
  have hnormK :
      IsNormal (normalizationSchemeOverField K (pullback.fst (spectrumMap k K) p)) :=
    Scheme.isNormal_normalizationScheme _ _
  obtain ⟨hbijK, UK, hUK, hciK⟩ :=
    bijOn_genericPoints_normalizationOverField K (pullback.fst (spectrumMap k K) p)
  obtain ⟨E, hEfin, Z, μ, hfinμ, q, hq, φ, hφ⟩ := exists_finiteDimensional_isFinite_model k K p
    (normalizationOverField K (pullback.fst (spectrumMap k K) p))
  have := hEfin
  have := hfinμ
  -- The comparison morphism `q` is flat, surjective, quasi-compact and a homeomorphism.
  obtain ⟨hfl, hsu⟩ := flat_and_surjective_spectrumMap (E : Type u) K
  have hqflat : Flat q := MorphismProperty.of_isPullback hq.flip hfl
  have hqsurj : Surjective q := MorphismProperty.of_isPullback hq.flip hsu
  have hqqc : QuasiCompact q :=
    MorphismProperty.of_isPullback hq.flip
      (inferInstance : QuasiCompact (spectrumMap (E : Type u) K))
  have hpiEK : IsPurelyInseparable (E : Type u) K :=
    IsPurelyInseparable.tower_top k (E : Type u) K
  have huhEK : UniversalHomeomorphism (spectrumMap (E : Type u) K) :=
    @universalHomeomorphism_specMap_algebraMap (E : Type u) K _ _ _ hpiEK
  have hquh : UniversalHomeomorphism q := MorphismProperty.of_isPullback hq.flip huhEK
  have hqhomeo := @universalHomeomorphism_isHomeomorph _ _ q hquh
  -- `Z` is normal, since its base change to `K` is the normalization over `K`.
  have hnpull : IsNormal (pullback μ q) := @isNormal_of_iso _ _ φ hnormK
  have hflatfst : Flat (pullback.fst μ q) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback μ q).flip hqflat
  have hsurjfst : Surjective (pullback.fst μ q) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback μ q).flip hqsurj
  have hquhfst : UniversalHomeomorphism (pullback.fst μ q) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback μ q).flip hquh
  have hZnormal : IsNormal Z :=
    @isNormal_of_flat_surjective _ _ (pullback.fst μ q) hflatfst hsurjfst hnpull
  -- `μ` bijects generic points, and is a closed immersion over a dense open.
  have hbijsnd : Set.BijOn (pullback.snd μ q)
      (genericPoints (pullback μ q : Scheme.{u}))
      (genericPoints (pullback (spectrumMap k K) p : Scheme.{u})) := by
    have hcc := hbijK.comp (bijOn_genericPoints_of_iso φ)
    have heq : (⇑(normalizationOverField K (pullback.fst (spectrumMap k K) p)) ∘ ⇑φ.hom) =
        ⇑(pullback.snd μ q) := by
      funext x
      exact congrArg (fun r : (pullback μ q : Scheme.{u}) ⟶
        (pullback (spectrumMap k K) p : Scheme.{u}) ↦ r x) hφ
    exact heq ▸ hcc
  have hfsthomeo := @universalHomeomorphism_isHomeomorph _ _ (pullback.fst μ q) hquhfst
  have hbijZ : Set.BijOn μ (genericPoints Z)
      (genericPoints (pullback (spectrumMap k (E : Type u)) p : Scheme.{u})) := by
    have hcc := (Homeomorph.bijOn_genericPoints hqhomeo.homeomorph).comp
      (hbijsnd.comp (Homeomorph.bijOn_genericPoints hfsthomeo.homeomorph.symm))
    have heq : (⇑q ∘ (⇑(pullback.snd μ q) ∘ ⇑hfsthomeo.homeomorph.symm)) = ⇑μ := by
      funext z
      have hd : (pullback.fst μ q) (hfsthomeo.homeomorph.symm z) = z :=
        hfsthomeo.homeomorph.apply_symm_apply z
      have hc := congrArg (fun r : (pullback μ q : Scheme.{u}) ⟶
        (pullback (spectrumMap k (E : Type u)) p : Scheme.{u}) ↦
          r (hfsthomeo.homeomorph.symm z)) (pullback.condition (f := μ) (g := q))
      simp only [Scheme.Hom.comp_apply] at hc
      change q ((pullback.snd μ q) (hfsthomeo.homeomorph.symm z)) = μ z
      rw [← hc, hd]
    exact heq ▸ hcc
  have hciφ : IsClosedImmersion (pullback.snd μ q ∣_ UK) := by
    have hfφ : pullback.snd μ q =
        φ.hom ≫ normalizationOverField K (pullback.fst (spectrumMap k K) p) := hφ.symm
    have hiso1 : IsIso φ.hom := φ.isIso_hom
    rw [hfφ, morphismRestrict_comp]
    exact @IsClosedImmersion.comp _ _ _ _ _
      (@isClosedImmersion_morphismRestrict_of_isIso _ _ φ.hom hiso1 _) hciK
  obtain ⟨UE, hUE, hciμ⟩ :=
    exists_dense_isClosedImmersion_of_isHomeomorph μ q hqhomeo UK hUK
  -- Hence `μ` is the normalization morphism at the stage `E`.
  have := hciμ
  obtain ⟨ε, hε⟩ := exists_iso_normalizationSchemeOverField (E : Type u)
    (pullback.fst (spectrumMap k (E : Type u)) p) μ hbijZ UE hUE
  -- The base change of `Z` to `K` is normal and `K` is perfect, so `Z` is geometrically normal.
  refine ⟨E, hEfin, ?_⟩
  have hpaste := (IsPullback.of_hasPullback μ q).paste_vert hq
  have hnK : IsNormal (pullback (μ ≫ pullback.fst (spectrumMap k (E : Type u)) p)
      (Spec.map (ofHom (algebraMap (E : Type u) K)))) :=
    @isNormal_of_iso _ _ hpaste.isoPullback.symm hnpull
  have hgnE : IsGeometricallyNormal (μ ≫ pullback.fst (spectrumMap k (E : Type u)) p) := by
    rw [isGeometricallyNormal_iff_baseChange (E : Type u) K Z
      (μ ≫ pullback.fst (spectrumMap k (E : Type u)) p)]
    exact @isGeometricallyNormal_of_isNormal_of_perfectField K _ _ _ _ hnK
  refine isGeometricallyNormal_of_iso (E : Type u) ε.symm
    (μ ≫ pullback.fst (spectrumMap k (E : Type u)) p) _ ?_ hgnE
  rw [Iso.symm_hom, ← hε]
  simp

/-- **Stacks Project, Tag 0BXT.** Let `k` be a field and `X` an algebraic `k`-scheme. There is a
finite purely inseparable extension `k'/k` such that the normalization of `X_{k'}` is
geometrically normal over `k'`. -/
@[stacks 0BXT]
public theorem exists_isPurelyInseparable_isGeometricallyNormal_normalization
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (_ : Module.Finite k k')
      (_ : IsPurelyInseparable k k'),
      IsGeometricallyNormal (normalizationOverField k' (pullback.fst (spectrumMap k k') p) ≫
        pullback.fst (spectrumMap k k') p) := by
  have : Algebra.IsAlgebraic k (perfectClosure k (AlgebraicClosure k)) :=
    IsPurelyInseparable.isAlgebraic k _
  obtain ⟨E, hE, hgn⟩ := exists_finiteDimensional_isGeometricallyNormal_normalizationOverField
    k (perfectClosure k (AlgebraicClosure k)) p
  exact ⟨(E : Type u), inferInstance, inferInstance, hE, inferInstance, hgn⟩

end AlgebraicGeometry
