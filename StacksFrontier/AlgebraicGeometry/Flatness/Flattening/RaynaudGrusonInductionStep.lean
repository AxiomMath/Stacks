module

public import Mathlib
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FlatteningNeighborhoodDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeMapOnAffineChart
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeMapSectionsInjectivity
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackRestrict
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleSquare
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectExtension

/-!
# The induction step of the Raynaud–Gruson flattening theorem

[Stacks, Tag 0815] is an induction on `d = max_{s ∈ S} dim Supp(ℱ_s)`. After the reductions of
the source — étale locality on source and target ([Stacks, Tag 0814]) and the elementary
dévissage ([Stacks, Tag 057S]) — the module to be flattened sits on a *smooth affine* morphism
with geometrically integral fibres of dimension `d`, and [Stacks, Tag 0811] has made it finite
locally free on an open surjecting onto the base.

This file is the step the source then takes, in two stages.

**On one affine chart of the base.** Choose a map `β : 𝒪^{⊕ r} ⟶ ℱ` from a finite free module
which is an isomorphism on an open `W` surjecting onto the base — this is
`AlgebraicGeometry.exists_affineOpen_freeMap_isIso_surjective`. Then:

* `β` is universally injective on sections
  (`AlgebraicGeometry.universallyInjective_schemeApp_of_isIso_on_open`, which is
  [Stacks, Tag 05IA] and [Stacks, Tag 05CL]), hence a monomorphism, and its cokernel sequence
  stays short exact after every base change of the base;
* the cokernel `ℋ` is still of finite presentation and flat over `U`, so it satisfies the
  hypotheses of the theorem;
* the fibre supports of `ℋ` have *strictly smaller* dimension
  (`AlgebraicGeometry.topologicalKrullDim_supp_cokernel_fiber_lt`), because `β` is an
  isomorphism at the generic point of every fibre;
* so the inductive hypothesis flattens `ℋ`, and the short exact sequence of strict transforms
  ([Stacks, Tag 080W]) carries flatness back to `ℱ`, the free term being flat over the base
  already.

**From the charts to the base.** The charts produced above cover the base, and
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_baseOpens`
assembles a single centre from a centre over a neighbourhood of each point of the base.

## Main definitions

* `AlgebraicGeometry.HasFlatteningCentre` is the flatness assertion of [Stacks, Tag 0815] for
  one datum, in the vocabulary of the étale-local descent.
* `AlgebraicGeometry.ModuleFlatteningCentreBelow` is that assertion for every datum whose fibre
  supports have dimension below a given bound — the statement the induction is run on.

## Main results

* `AlgebraicGeometry.hasFlatteningCentre_of_freeMap`: the chart step.
* `AlgebraicGeometry.hasFlatteningCentre_of_fiberFree`: **the induction step of
  [Stacks, Tag 0815]**, from a module free of finite rank near every point of an open surjecting
  onto the base.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 080W](https://stacks.math.columbia.edu/tag/080W)
* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
* [Stacks Project, Tag 05CL](https://stacks.math.columbia.edu/tag/05CL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The flatness assertion of [Stacks, Tag 0815] for one datum.** There is a centre `ℐ` on
`S`, finitely presented as a closed subscheme and supported away from `U`, such that the strict
transform of `ℱ` along the blowup of `S` in `ℐ` is flat over that blowup.

This is the conclusion of the étale-local descent
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf`, minus its
`Stacks.Blowup.IsAdmissibleBlowup` conjunct, which those two conditions already imply by
`Stacks.Blowup.isAdmissibleBlowup_blowUpToBase`. -/
def HasFlatteningCentre {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (U : S.Opens) : Prop :=
  ∃ I : S.IdealSheafData,
    FinitePresentation I.subschemeι ∧
    Disjoint (U : Set S) (I.support : Set S) ∧
    IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F)

/-- **The statement the induction of [Stacks, Tag 0815] is run on**: the flatness assertion for
every datum all of whose fibre supports have dimension `< n`. -/
def ModuleFlatteningCentreBelow (n : ℕ) : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [LocallyOfFinitePresentation f] [F.IsQuasicoherent] [F.IsFiniteType]
    (U : S.Opens), IsCompact (U : Set S) →
    ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation →
    IsFlatOver (f ∣_ U).toLRSHom.toShHom ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F) →
    (∀ s : S, topologicalKrullDim (SheafOfModules.supp
      ((Scheme.Modules.pullback (f.fiberι s)).obj F)) < (n : WithBot ℕ∞)) →
    HasFlatteningCentre f F U

/-! ### The chart step -/

/-- **The chart step of the induction of [Stacks, Tag 0815].** Let `f : X ⟶ S` be a morphism of
affine schemes, smooth of relative dimension `n` with geometrically integral fibres, let `ℱ` be a
quasi-coherent module of finite type on `X` which is of finite presentation and flat over a
quasi-compact open `U ⊆ S`, and let `β : 𝒪_X^{⊕ r} ⟶ ℱ` be a map from a finite free module which
is an isomorphism on an open `W₂ ⊆ X` surjecting onto `S`. Granted the flattening theorem in
fibre-support dimension `< n`, `ℱ` has a flattening centre avoiding `U`.

The cokernel of `β` has fibre supports of dimension `< n`, because the fibres of `f` have
dimension `n` and `β` is an isomorphism at the generic point of each of them; so the inductive
hypothesis applies to it, and the short exact sequence of strict transforms carries flatness
back. -/
theorem hasFlatteningCentre_of_freeMap {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [LocallyOfFinitePresentation f] (n : ℕ)
    [SmoothOfRelativeDimension n f] [GeometricallyIntegral f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    {r : ℕ} (β : (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ F)
    (W₂ : X.Opens) (hsurj : Function.Surjective (W₂.ι ≫ f).base)
    (hiso : IsIso ((Scheme.Modules.pullback W₂.ι).map β))
    (U : S.Opens) (hU : IsCompact (U : Set S))
    (hFfp : ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation)
    (hFflat : IsFlatOver (f ∣_ U).toLRSHom.toShHom
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj F))
    (ih : ModuleFlatteningCentreBelow.{u} n) :
    HasFlatteningCentre f F U := by
  have _ : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hUV : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens) := by simp
  have hα := universallyInjective_schemeApp_of_isIso_on_open f β W₂ hsurj hiso hUV
  have _ : (cokernel β).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel β
  have _ : (cokernel β).IsFiniteType := Scheme.Modules.isFiniteType_cokernel β inferInstance
  let C : ShortComplex X.Modules := ShortComplex.cokernelSequence β
  have hCse : C.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact β
      mono_f := mono_of_universallyInjective_sections_of_isAffine f β hUV hα
      epi_g := inferInstance }
  have _ : C.X₁.IsQuasicoherent := inferInstanceAs
    ((∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent)
  have _ : C.X₂.IsQuasicoherent := inferInstanceAs F.IsQuasicoherent
  have _ : C.X₃.IsQuasicoherent := inferInstanceAs (cokernel β).IsQuasicoherent
  have _ : ∀ t : S, Nonempty (f.fiber t) := fun t ↦ ⟨genericPoint (f.fiber t)⟩
  obtain ⟨J, hJfp, hJdisj, hJflat⟩ := ih f (cokernel β) U hU
    (Stacks.Modules.isFinitePresentation_pullback_cokernel f F _ U hFfp β)
    (isFlatOver_restrict_cokernel_of_universallyInjective_sections_of_isAffine f β U hUV hα hFflat)
    (topologicalKrullDim_supp_cokernel_fiber_lt f β W₂ hsurj hiso
      fun s ↦ (fiberDimension_eq_of_smoothOfRelativeDimension n f s).le)
  have h₁ : IsFlatOver f.toLRSHom.toShHom
      (∐ fun _ : Fin r => SheafOfModules.unit X.ringCatSheaf : X.Modules) := fun x ↦
    isFlatOverAt_of_free_stalk f _ x (Stacks.StalkFreeBridge.free_stalk_coproductUnit r x)
  exact ⟨J, hJfp, hJdisj,
    isFlatOver_strictTransformSheaf_middle_of_shortExact f J C
      (fun {T'} g ↦ shortExact_map_pullback_of_universallyInjective_of_isAffine f C hCse hUV
        (universallyInjective_moduleSpecΓ_of_sections f β (isAffineOpen_top X) hUV hα) g)
      h₁ hJflat⟩

/-! ### From the charts to the base -/

/-- **The induction step of [Stacks, Tag 0815].** Let `q : Z ⟶ T` be an affine morphism, smooth
of relative dimension `n` with geometrically integral fibres, let `M` be a quasi-coherent module
of finite type on `Z` which is of finite presentation and flat over a quasi-compact open `W` of
`T`, and let `M` be free of some finite rank near every point of an open `V ⊆ Z` surjecting onto
`T`. Granted the
flattening theorem in fibre-support dimension `< n`, `M` has a flattening centre avoiding `W`.

Around each point of `T`
`AlgebraicGeometry.exists_affineOpen_freeMap_isIso_surjective` produces an affine open carrying
the free map that `AlgebraicGeometry.hasFlatteningCentre_of_freeMap` consumes, and
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_baseOpens`
assembles the resulting centres into one on `T`. -/
theorem hasFlatteningCentre_of_fiberFree {Z T : Scheme.{u}} [CompactSpace T]
    [QuasiSeparatedSpace T] [CompactSpace Z] (q : Z ⟶ T) [IsAffineHom q]
    [LocallyOfFinitePresentation q] (n : ℕ) [SmoothOfRelativeDimension n q]
    [GeometricallyIntegral q] (M : Z.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (W : T.Opens) (hWc : IsCompact (W : Set T))
    (hMfp : ((Scheme.Modules.pullback (q ⁻¹ᵁ W).ι).obj M).IsFinitePresentation)
    (hMflat : IsFlatOver (q ∣_ W).toLRSHom.toShHom
      ((Scheme.Modules.pullback (q ⁻¹ᵁ W).ι).obj M))
    (V : Z.Opens)
    (hVfree : ∀ z : Z, z ∈ V → ∃ (W : Z.Opens) (n : ℕ), z ∈ W ∧ W ≤ V ∧
      Nonempty (M.over W ≅ SheafOfModules.free.{u} (ULift.{u} (Fin n))))
    (hVsurj : Function.Surjective (V.ι ≫ q).base)
    (ih : ModuleFlatteningCentreBelow.{u} n) :
    HasFlatteningCentre q M W := by
  have _ : Smooth q := SmoothOfRelativeDimension.smooth n q
  refine (exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_baseOpens q M W hWc
    fun t ↦ ?_).elim fun I ⟨hIfp, hIdisj, _, hIflat⟩ ↦ ⟨I, hIfp, hIdisj, hIflat⟩
  obtain ⟨A, htA, hA, r, β, W₂, hAsurj, hWiso⟩ :=
    exists_affineOpen_freeMap_isIso_surjective q M V hVfree hVsurj t
  refine ⟨A, htA, hA.isCompact, ?_⟩
  have _ : IsAffine A.toScheme := hA
  have _ : IsAffine (q ⁻¹ᵁ A).toScheme := hA.preimage q
  have _ : CompactSpace A.toScheme := isCompact_iff_compactSpace.mp hA.isCompact
  have _ : QuasiSeparatedSpace A.toScheme := quasiSeparatedSpace_of_quasiSeparated A.ι
  have _ : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  have _ : SmoothOfRelativeDimension n (q ∣_ A) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict q A).flip inferInstance
  have _ : GeometricallyIntegral (q ∣_ A) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict q A).flip inferInstance
  have _ : ((Scheme.Modules.pullback (q ⁻¹ᵁ A).ι).obj M).IsQuasicoherent :=
    @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
      (q ⁻¹ᵁ A).ι.toLRSHom.toShHom M
      (inferInstanceAs (SheafOfModules.IsQuasicoherent (R := Z.ringCatSheaf) M))
  have _ : ((Scheme.Modules.pullback (q ⁻¹ᵁ A).ι).obj M).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (q ⁻¹ᵁ A).ι.toLRSHom.toShHom M
  have hpre : (q ∣_ A) ⁻¹ᵁ (A.ι ⁻¹ᵁ W) = (q ⁻¹ᵁ A).ι ⁻¹ᵁ (q ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
  have hMAfp : ((Scheme.Modules.pullback ((q ∣_ A) ⁻¹ᵁ (A.ι ⁻¹ᵁ W)).ι).obj
      ((Scheme.Modules.pullback (q ⁻¹ᵁ A).ι).obj M)).IsFinitePresentation := by
    rw [hpre]
    exact Stacks.Modules.isFinitePresentation_pullback_on_preimage (q ⁻¹ᵁ A).ι M (q ⁻¹ᵁ W) hMfp
  have hMAflat : IsFlatOver ((q ∣_ A) ∣_ (A.ι ⁻¹ᵁ W)).toLRSHom.toShHom
      ((Scheme.Modules.pullback ((q ∣_ A) ⁻¹ᵁ (A.ι ⁻¹ᵁ W)).ι).obj
        ((Scheme.Modules.pullback (q ⁻¹ᵁ A).ι).obj M)) := by
    refine isFlatOver_restrict_of_flatOnPreimage (q ∣_ A) _ (A.ι ⁻¹ᵁ W) fun x hx ↦ ?_
    refine isFlatOverAt_pullback_of_etale_square q (q ∣_ A) (q ⁻¹ᵁ A).ι A.ι M
      (morphismRestrict_ι q A).symm x ?_
    refine isFlatOverAt_of_open_restriction q M W ((q ⁻¹ᵁ A).ι x) ?_ hMflat
    have hx' : A.ι ((q ∣_ A) x) ∈ W := hx
    rwa [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply] at hx'
  exact hasFlatteningCentre_of_freeMap (q ∣_ A) n
    ((Scheme.Modules.pullback (q ⁻¹ᵁ A).ι).obj M) β W₂ hAsurj hWiso
    (A.ι ⁻¹ᵁ W) (isCompact_preimage_ι_of_quasiSeparatedSpace W A hWc hA.isCompact)
    hMAfp hMAflat ih

end AlgebraicGeometry

end
