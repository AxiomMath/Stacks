module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleSurjective
public import StacksFrontier.AlgebraicGeometry.Blowup.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOffExceptional
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.AffineChartFlatteningFromInduction
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FlatteningBlowupFromAffineCase
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreFreeBlowup0811
public import StacksFrontier.AlgebraicGeometry.Flatness.RaynaudGrusonFlattening0815
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.V.PhVStratification
public import StacksFrontier.AlgebraicGeometry.Topologies.V.SchemeTheoreticImageValuative
public import StacksCore.Tactic.StacksAttribute

/-!
# Steps 4 and 5 of Stacks 0ETR

Stacks 0ETR says that a family of morphisms locally of finite presentation is a ph covering if
and only if it is a V covering. In
`StacksFrontier.AlgebraicGeometry.Topologies.V.PhVStratification` the whole of it is reduced to
`AlgebraicGeometry.StandardVCoveringDenseFlatHasModification`, the fourth paragraph of the
source's proof: a standard V covering of an affine scheme which is already flat over a
quasi-compact scheme-theoretically dense open of the base admits a flattening modification.

This file discharges that reduction from the Raynaud–Gruson flattening theorem of
[Stacks, Tag 0815], carried as `AlgebraicGeometry.FinitePresentationHasFlatteningBlowup`, and
then supplies that theorem from
`AlgebraicGeometry.finitePresentationHasFlatteningBlowup`. So Stacks 0ETR is proved here, as
`AlgebraicGeometry.isPHCovering_iff_isVCovering`; the two brackets around the flattening, steps
3 and 6, were already unconditional.

## Main results

* `AlgebraicGeometry.flat_pullback_snd_sigmaDesc`: the projection `(∐ A_κ) ×_T W ⟶ W` is flat as
  soon as each `A_κ ×_T W ⟶ W` is. This is what lets the flattening theorem be applied to the
  coproduct of the members of the covering, so that a *single* blowup serves them all.
* `AlgebraicGeometry.Spec_map_base_genericPoint_eq` and
  `AlgebraicGeometry.Spec_map_base_eq_genericPoint`: an injective ring map of domains carries the
  generic point to the generic point, and the spectrum of a field has only the generic point to
  carry.
* `AlgebraicGeometry.isSchemeTheoreticallyDominant_Spec_map_algebraMap_of_isFractionRing`: the
  inclusion of the generic point of the spectrum of a domain is scheme-theoretically dominant.
* `AlgebraicGeometry.exists_mem_range_strictTransformMap_sigmaDesc_of_isStandardVCovering`:
  **step 5** — for a standard V covering of an affine scheme and *any* centre on the base, the
  strict transform of the coproduct of the members is surjective over the blowup.
* `AlgebraicGeometry.hasFlatFppfModification_of_flat_strictTransformMap_sigmaDesc`: the
  flattening modification assembled from a centre whose strict transform is flat.
* `AlgebraicGeometry.standardVCoveringDenseFlatHasModification_of_flatteningBlowup`: **steps 4
  and 5** — `AlgebraicGeometry.FinitePresentationHasFlatteningBlowup` implies
  `AlgebraicGeometry.StandardVCoveringDenseFlatHasModification`.
* `AlgebraicGeometry.standardVCoveringHasPHRefinement_of_flatteningBlowup`: hence the whole of
  `AlgebraicGeometry.StandardVCoveringHasPHRefinement`.
* `AlgebraicGeometry.isPHCovering_iff_isVCovering_of_flatteningBlowup`: **Stacks 0ETR itself**,
  with [Stacks, Tag 0815] as its single named dependency.
* `AlgebraicGeometry.isPHCovering_iff_isVCovering_of_affineChartFlatteningCentre`: the same, with
  the dependency sharpened to the *affine* case of 0815's flatness assertion,
  `AlgebraicGeometry.FinitePresentationHasAffineChartFlatteningCentre`, which is where the
  Raynaud–Gruson induction lives.
* `AlgebraicGeometry.isPHCovering_iff_isVCovering_of_genericFibreFlatteningBlowup`: the same,
  with the dependency sharpened all the way to
  `AlgebraicGeometry.FinitePresentationHasGenericFibreFlatteningBlowup`, an input *stronger*
  than [Stacks, Tag 0811] which this development does not prove and no longer needs; it is kept
  as the record of that sharper reduction.
* `AlgebraicGeometry.standardVCoveringDenseFlatHasModification` and
  `AlgebraicGeometry.standardVCoveringHasPHRefinement`: those two predicates, with nothing
  granted.
* `AlgebraicGeometry.isPHCovering_iff_isVCovering`: **[Stacks, Tag 0ETR]**, with nothing
  granted, and `AlgebraicGeometry.isHCovering_iff_isVCovering` the reading of it that defines
  an h covering.

## Implementation notes

**One blowup for the whole family.** [Stacks, Tag 0815] flattens one morphism, and
`AlgebraicGeometry.HasFlatFppfModification` asks for one base over which *every* member becomes
flat. The source gets this by applying the flattening theorem to `∐ f_i`, and so does this file.
What is then needed of the strict transform `X'` of `∐ A_κ` is only that it be cut into pieces
over the members, and that is a decomposition into *open* subschemes
`X'_κ = (X' ⟶ ∐ A_κ)⁻¹(A_κ)`: no statement identifying the strict transform of a coproduct with
the coproduct of the strict transforms is needed, and none is proved here. The maps
`X'_κ ⟶ A_κ` are `AlgebraicGeometry.IsOpenImmersion.lift` of the projection to `∐ A_κ`.

**No further admissible blowup.** The source, before running its valuative argument, replaces the
blowup by a further `U`-admissible blowup so as to make the inverse image of `U` *scheme
theoretically* dense upstairs (Remark 38.30.1, [Stacks, Tag 080Y]). That step is not needed here.
The valuative argument asks for a valuation ring whose generic point maps into a locus over which
the closed immersion of the strict transform into the base change is an isomorphism, and
`Stacks.Blowup.isIso_strictTransformι_restrict` says that the complement of the exceptional
divisor is such a locus, with no hypothesis at all; that complement is scheme-theoretically dense
in the blowup because the exceptional divisor is an effective Cartier divisor
(`Stacks.Blowup.isSchemeTheoreticallyDense_compl_support_exceptionalIdeal`). So the dense open the
argument runs over is the complement of the exceptional divisor rather than the inverse image of
`U`, and no second blowup — nor any domination of two blowups by a third — enters.

**The valuative diagram.** [Stacks, Tag 02JQ] is used in its ideal-sheaf form,
`AlgebraicGeometry.exists_valuationRing_diagram_of_mem_support_ker`, applied to the inclusion
of the complement of the exceptional divisor: that inclusion is quasi-compact, because the
complement of an effective Cartier divisor is affine over the ambient scheme, and
scheme-theoretically dominant, so every point of the blowup is in the support of its kernel ideal
sheaf. The standard V covering then provides an extension of valuation rings `R ⊆ W`, and the
morphism `Spec W ⟶ (∐ A_κ) ×_T T'` it assembles is lifted into the strict transform by
`Stacks.Blowup.exists_unique_lift_strictTransformι`, whose scheme-theoretically dominant morphism
is the inclusion of the generic point `Spec (Frac W) ⟶ Spec W`. That the generic point of
`Spec W` lies over the generic point of `Spec R`, and that the closed point lies over the closed
point, are the two places where injectivity and locality of `R ⊆ W` are used.

## References

* [Stacks Project, Tag 0ETR](https://stacks.math.columbia.edu/tag/0ETR)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 081P](https://stacks.math.columbia.edu/tag/081P)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 02JQ](https://stacks.math.columbia.edu/tag/02JQ)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-! ### Flatness of a projection out of a coproduct -/

/-- Flatness of a projection `X ×_T W ⟶ W` only depends on the morphism `X ⟶ T` up to
equality, a dependence `CategoryTheory.Limits.pullback.snd` hides from `rw`. -/
theorem flat_pullback_snd_of_eq {X W T : Scheme.{u}} {f f' : X ⟶ T} (hf : f = f') (g : W ⟶ T)
    [Flat (pullback.snd f' g)] : Flat (pullback.snd f g) := by
  subst hf
  infer_instance

/-- Flatness of the projection `(∐ A_κ) ×_T W ⟶ W` follows from flatness of each
`A_κ ×_T W ⟶ W`: the base changes of the coproduct inclusions form an open cover of the
coproduct's base change, and flatness is local at the source. -/
theorem flat_pullback_snd_sigmaDesc {T W : Scheme.{u}} {K : Type v} [Small.{u} K]
    {A : K → Scheme.{u}} (a : ∀ κ, A κ ⟶ T) (g : W ⟶ T)
    (h : ∀ κ, Flat (pullback.snd (a κ) g)) : Flat (pullback.snd (Sigma.desc a) g) := by
  have : MorphismProperty.RespectsIso (@Flat.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Flat.{u})
    ((sigmaOpenCover A).pullback₁ (pullback.fst (Sigma.desc a) g))]
  intro κ
  change Flat (pullback.fst (pullback.fst (Sigma.desc a) g) (Sigma.ι A κ) ≫
    pullback.snd (Sigma.desc a) g)
  rw [← pullbackSymmetry_hom_comp_snd (pullback.fst (Sigma.desc a) g) (Sigma.ι A κ),
    Category.assoc,
    ← pullbackRightPullbackFstIso_hom_snd (Sigma.desc a) g (Sigma.ι A κ)]
  have _ : Flat (pullback.snd (a (κ : K)) g) := h κ
  have _ : Flat (pullback.snd (Sigma.ι A (κ : K) ≫ Sigma.desc a) g) :=
    flat_pullback_snd_of_eq (Sigma.ι_comp_desc _ _) g
  infer_instance

/-! ### The generic point of the spectrum of a domain -/

/-- An injective ring homomorphism of domains carries the generic point of the spectrum of its
target to the generic point of the spectrum of its source: both are the zero ideal, and the
preimage of the zero ideal is the kernel. -/
theorem Spec_map_base_genericPoint_eq {R S : Type u} [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] (φ : R →+* S) (hφ : Function.Injective φ) :
    (Spec.map (CommRingCat.ofHom φ)).base (genericPoint (Spec (.of S))) =
      genericPoint (Spec (.of R)) := by
  rw [genericPoint_eq_bot_of_affine (.of S), genericPoint_eq_bot_of_affine (.of R)]
  exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot φ).mp hφ)

/-- The spectrum of a field has one point, so every point of it is carried to the generic point
of the spectrum of a domain injecting into that field. -/
theorem Spec_map_base_eq_genericPoint {R L : Type u} [CommRing R] [IsDomain R] [Field L]
    (φ : R →+* L) (hφ : Function.Injective φ) (z : Spec (.of L)) :
    (Spec.map (CommRingCat.ofHom φ)).base z = genericPoint (Spec (.of R)) := by
  rw [show z = genericPoint (Spec (.of L)) from Subsingleton.elim _ _]
  exact Spec_map_base_genericPoint_eq φ hφ

/-- The inclusion of the generic point of the spectrum of a domain — the morphism `Spec K ⟶
Spec R` induced by the inclusion of `R` into a fraction field `K` of it — is
scheme-theoretically dominant: `R` injects into `K`, so the kernel ideal sheaf is zero. -/
theorem isSchemeTheoreticallyDominant_Spec_map_algebraMap_of_isFractionRing
    (R : Type u) [CommRing R] [IsDomain R] (F : Type u) [Field F] [Algebra R F]
    [IsFractionRing R F] :
    IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap R F))) := by
  have hdom : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R F))) := by
    rw [isDominant_iff]
    change DenseRange (PrimeSpectrum.comap (algebraMap R F))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R F)]
    exact bot_le
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/-! ### The valuative step -/

/-- **Step 5 of the Stacks proof of 0ETR.** Let `{a_κ : A_κ ⟶ T}` be a standard V covering of an
affine scheme and let `I` be *any* centre on `T`. Then the strict transform of `∐ A_κ` along the
blowup of `T` in `I` is **surjective** over the blowup.

This is the valuative argument of the fourth paragraph of the Stacks proof. Given a point `t` of
the blowup `T'`, the complement `Ω` of the exceptional divisor is scheme-theoretically dense in
`T'` (`Stacks.Blowup.isSchemeTheoreticallyDense_compl_support_exceptionalIdeal`), so
[Stacks, Tag 02JQ]
(`AlgebraicGeometry.exists_valuationRing_diagram_of_mem_support_ker`) supplies a valuation
ring `R` with a morphism `Spec R ⟶ T'` carrying the closed point to `t` and the generic point
into `Ω`. The standard V covering property applied to `Spec R ⟶ T' ⟶ T` yields an extension of
valuation rings `R ⊆ W`, an index `κ` and a morphism `Spec W ⟶ A_κ` over `T`; the two together
give `Spec W ⟶ (∐ A_κ) ×_T T'`, whose generic point lands away from the inverse image of the
exceptional divisor, so it factors through the strict transform by
`Stacks.Blowup.exists_unique_lift_strictTransformι`. The image of the closed point of `Spec W`
is then a point of the strict transform over `t`, because `R ⊆ W` is a local homomorphism.

The Stacks proof instead arranges, by a further admissible blowup (Remark 38.30.1), that the
inverse image of the dense open `U ⊆ T` be scheme-theoretically dense upstairs, and takes the
generic point into it. That extra blowup is unnecessary here: the strict transform contains the
whole base change over the complement of the exceptional divisor
(`Stacks.Blowup.isIso_strictTransformι_restrict`), and that complement is
scheme-theoretically dense with no hypothesis at all. -/
theorem exists_mem_range_strictTransformMap_sigmaDesc_of_isStandardVCovering
    {T : Scheme.{u}} (hT : IsAffine T) {K : Type u} (hK : Finite K) {A : K → Scheme.{u}}
    (hA : ∀ κ, IsAffine (A κ)) (a : ∀ κ, A κ ⟶ T)
    (hstd : @IsStandardVCovering T hT K hK A hA a) (I : T.IdealSheafData)
    (t : Stacks.Blowup.blowUp I) :
    t ∈ Set.range (Stacks.Blowup.strictTransformMap (Sigma.desc a) I).base := by
  classical
  set Ω : (Stacks.Blowup.blowUp I).Opens :=
    (Stacks.Blowup.exceptionalIdeal I).support.compl with hΩ
  -- The complement of the exceptional divisor is a scheme-theoretically dense open whose
  -- inclusion is quasi-compact.
  have _ : IsAffineHom (Scheme.Opens.ι Ω) :=
    Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal_reesData I)
  have _ : IsSchemeTheoreticallyDominant (Scheme.Opens.ι Ω) :=
    Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDominant_of_dense Ω
      (Stacks.Blowup.isSchemeTheoreticallyDense_compl_support_exceptionalIdeal I)
  have ht : t ∈ (Scheme.Opens.ι Ω).ker.support := by
    rw [IsSchemeTheoreticallyDominant.ker_eq_bot (Scheme.Opens.ι Ω)]
    exact trivial
  -- A valuation ring reaching `t` whose generic point lands in that open.
  obtain ⟨R, _, _, _, F, _, _, _, g', h', hsq, hclosed⟩ :=
    exists_valuationRing_diagram_of_mem_support_ker (Scheme.Opens.ι Ω) t ht
  have hgenR : h'.base (genericPoint (Spec (.of R))) ∈ (Ω : Set (Stacks.Blowup.blowUp I)) := by
    have h1 := congrArg
      (fun k : Spec (.of F) ⟶ Stacks.Blowup.blowUp I ↦ k.base (genericPoint (Spec (.of F)))) hsq
    simp only [Scheme.Hom.comp_apply,
      Spec_map_base_genericPoint_eq (algebraMap R F) (IsFractionRing.injective R F)] at h1
    rw [← h1, ← Scheme.Opens.range_ι Ω]
    exact Set.mem_range_self _
  -- The standard V covering lifts the valuation ring, after an extension of it.
  obtain ⟨Wv, _, _, _, e, ⟨heinj, helocal⟩, κ, q, hq⟩ :=
    hstd R (h' ≫ Stacks.Blowup.blowUpToBase I)
  have _ : IsSchemeTheoreticallyDominant
      (Spec.map (CommRingCat.ofHom (algebraMap Wv (FractionRing Wv)))) :=
    isSchemeTheoreticallyDominant_Spec_map_algebraMap_of_isFractionRing Wv (FractionRing Wv)
  -- The induced morphism to the base change `(∐ A_κ) ×_T T'`.
  set ψ : Spec (.of Wv) ⟶ Stacks.Blowup.blowUp I := Spec.map (CommRingCat.ofHom e) ≫ h' with hψ
  have hcond : (q ≫ Sigma.ι A κ) ≫ Sigma.desc a = ψ ≫ Stacks.Blowup.blowUpToBase I := by
    rw [Category.assoc, Sigma.ι_comp_desc, hψ, Category.assoc]
    exact hq.symm
  set p := pullback.lift (q ≫ Sigma.ι A κ) ψ hcond with hp
  have hmsnd : p ≫ Stacks.Blowup.blowUpPullbackToBlowUp (Sigma.desc a) I = ψ :=
    pullback.lift_snd _ _ _
  -- Its generic point lands away from the inverse image of the exceptional divisor.
  have hi : Set.range (Spec.map (CommRingCat.ofHom (algebraMap Wv (FractionRing Wv))) ≫ p) ⊆
      (Stacks.Blowup.exceptionalPullbackCompl (Sigma.desc a) I :
        Set (Stacks.Blowup.blowUpPullback (Sigma.desc a) I)) := by
    rintro _ ⟨z, rfl⟩
    refine Stacks.Blowup.preimage_le_exceptionalPullbackCompl (Sigma.desc a) I
      (W := Ω) le_rfl ?_
    change (Stacks.Blowup.blowUpPullbackToBlowUp (Sigma.desc a) I) _ ∈ Ω
    rw [← Scheme.Hom.comp_apply, Category.assoc, hmsnd, hψ, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply,
      Spec_map_base_eq_genericPoint (algebraMap Wv (FractionRing Wv))
        (IsFractionRing.injective Wv (FractionRing Wv)) z,
      Spec_map_base_genericPoint_eq e heinj]
    exact hgenR
  -- Hence it factors through the strict transform, and the closed point goes to `t`.
  obtain ⟨l, hl, -⟩ := Stacks.Blowup.exists_unique_lift_strictTransformι (Sigma.desc a) I _ _ hi
  refine ⟨l (IsLocalRing.closedPoint Wv), ?_⟩
  have hfac : l ≫ Stacks.Blowup.strictTransformMap (Sigma.desc a) I = ψ := by
    rw [Stacks.Blowup.strictTransformMap, ← Category.assoc, hl, hmsnd]
  have h3 := congrArg (fun k : Spec (.of Wv) ⟶ Stacks.Blowup.blowUp I ↦
    k (IsLocalRing.closedPoint Wv)) hfac
  refine h3.trans ((congrArg _ (IsLocalRing.comap_closedPoint e)).trans hclosed)

/-! ### The flattened family -/

/-- **The flattening modification of Stacks 0ETR, from a flattening centre.** Suppose the strict
transform of `∐ A_κ` along the blowup of the affine `T` in `I` is flat, and suppose the blowup
morphism is proper and surjective. Then the standard V covering `{a_κ}` admits the flattening
modification of `AlgebraicGeometry.HasFlatFppfModification`.

The family over the blowup is the strict transform `X'` of `∐ A_κ`, cut into the open pieces
`X'_κ` lying over the members `A_κ ⊆ ∐ A_κ`. Each piece is flat and locally of finite
presentation over the blowup — the second by [Stacks, Tag 081P], in the hypothesis-free form
`Stacks.Blowup.locallyOfFinitePresentation_strictTransformMap_of_flat` — and the pieces are
jointly surjective because the strict transform itself is, by
`AlgebraicGeometry.exists_mem_range_strictTransformMap_sigmaDesc_of_isStandardVCovering`.

Taking the strict transform of the *coproduct* is what makes one blowup serve all the members at
once; the source applies its flattening theorem to `∐ f_i` for the same reason. -/
theorem hasFlatFppfModification_of_flat_strictTransformMap_sigmaDesc
    {T : Scheme.{u}} (hT : IsAffine T) {K : Type u} (hK : Finite K) {A : K → Scheme.{u}}
    (hA : ∀ κ, IsAffine (A κ)) (a : ∀ κ, A κ ⟶ T)
    (hstd : @IsStandardVCovering T hT K hK A hA a) (I : T.IdealSheafData)
    (hbproper : IsProper (Stacks.Blowup.blowUpToBase I))
    (hbsurj : Surjective (Stacks.Blowup.blowUpToBase I))
    [LocallyOfFinitePresentation (Sigma.desc a)]
    [Flat (Stacks.Blowup.strictTransformMap (Sigma.desc a) I)] :
    HasFlatFppfModification a := by
  classical
  have _ : LocallyOfFinitePresentation (Stacks.Blowup.strictTransformMap (Sigma.desc a) I) :=
    Stacks.Blowup.locallyOfFinitePresentation_strictTransformMap_of_flat (Sigma.desc a) I
  set X' : Scheme.{u} := Stacks.Blowup.strictTransform (Sigma.desc a) I with hX'
  set c : X' ⟶ Stacks.Blowup.blowUp I := Stacks.Blowup.strictTransformMap (Sigma.desc a) I
    with hc
  set s : X' ⟶ ∐ A := Stacks.Blowup.strictTransformToSource (Sigma.desc a) I with hs
  set W : K → X'.Opens := fun κ ↦ s ⁻¹ᵁ (Sigma.ι A κ).opensRange with hW
  have hrange : ∀ κ, Set.range ((W κ).ι ≫ s).base ⊆ Set.range (Sigma.ι A κ).base := by
    rintro κ _ ⟨x, rfl⟩
    exact x.2
  set d : ∀ κ, (W κ).toScheme ⟶ A κ := fun κ ↦
    IsOpenImmersion.lift (Sigma.ι A κ) ((W κ).ι ≫ s) (hrange κ) with hd
  have hdfac : ∀ κ, d κ ≫ Sigma.ι A κ = (W κ).ι ≫ s := fun κ ↦
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨Stacks.Blowup.blowUp I, Stacks.Blowup.blowUpToBase I, hbproper, hbsurj,
    fun κ ↦ (W κ).toScheme, fun κ ↦ (W κ).ι ≫ c, d,
    fun κ ↦ inferInstance, fun κ ↦ inferInstance, fun κ ↦ ?_, fun t ↦ ?_⟩
  · calc d κ ≫ a κ = d κ ≫ Sigma.ι A κ ≫ Sigma.desc a := by rw [Sigma.ι_comp_desc]
      _ = ((W κ).ι ≫ s) ≫ Sigma.desc a := by rw [← Category.assoc, hdfac κ]
      _ = (W κ).ι ≫ s ≫ Sigma.desc a := Category.assoc _ _ _
      _ = (W κ).ι ≫ c ≫ Stacks.Blowup.blowUpToBase I := by
          rw [hs, hc, Stacks.Blowup.strictTransformToSource_comp]
      _ = ((W κ).ι ≫ c) ≫ Stacks.Blowup.blowUpToBase I := (Category.assoc _ _ _).symm
  · obtain ⟨z, hz⟩ := exists_mem_range_strictTransformMap_sigmaDesc_of_isStandardVCovering
      hT hK hA a hstd I t
    obtain ⟨κ, y, hy⟩ := (sigmaOpenCover A).exists_eq (s z)
    exact ⟨κ, ⟨z, ⟨y, hy⟩⟩, hz⟩

/-! ### Steps 4 and 5 of Stacks 0ETR -/

/-- **Steps 4 and 5 of the Stacks proof of 0ETR, granted Stacks 0815.** The flattening theorem
of [Stacks, Tag 0815] implies `AlgebraicGeometry.StandardVCoveringDenseFlatHasModification`, the
one thing the rest of the proof of Stacks 0ETR in this development is reduced to.

The theorem is applied to the coproduct `∐ A_κ ⟶ T` of the members of the covering, which is a
morphism of affine schemes locally of finite presentation, and to the open `U ⊆ T` which is the
range of the given quasi-compact scheme-theoretically dominant open immersion `j`. That open is
quasi-compact because `T` is, and the family becomes flat over it because it does over `j`
(`AlgebraicGeometry.flat_pullback_snd_sigmaDesc` assembles the members into the coproduct). The
blowup it produces is proper because its centre is of finite presentation
(`Stacks.Blowup.isProper_blowUpToBase`) and surjective because `U` is dense
(`Stacks.Blowup.surjective_blowUpToBase`), density being topological density of the range of a
scheme-theoretically dominant morphism. The rest is
`AlgebraicGeometry.hasFlatFppfModification_of_flat_strictTransformMap_sigmaDesc`. -/
theorem standardVCoveringDenseFlatHasModification_of_flatteningBlowup
    (H : FinitePresentationHasFlatteningBlowup.{u}) :
    StandardVCoveringDenseFlatHasModification.{u} := by
  intro T hT K hK A hA a hlfp hstd V j _ _ _ hflat
  have _ : IsAffine T := hT
  have _ : Finite K := hK
  have _ : ∀ κ, IsAffine (A κ) := hA
  have _ : ∀ κ, LocallyOfFinitePresentation (a κ) := hlfp
  have _ : IsAffine (∐ A) := inferInstance
  have _ : LocallyOfFinitePresentation (Sigma.desc a) :=
    HasRingHomProperty.instIsZariskiLocalAtSource.sigmaDesc fun κ ↦ hlfp κ
  have _ : MorphismProperty.RespectsIso (@Flat.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace j
  -- The range of `j` is a quasi-compact topologically dense open of the base.
  have hUcompact : IsCompact ((j.opensRange : T.Opens) : Set T) := isCompact_range j.continuous
  have hdenseU : Dense ((j.opensRange : T.Opens) : Set T) := by
    have hs := Scheme.Hom.support_ker j
    rw [IsSchemeTheoreticallyDominant.ker_eq_bot j] at hs
    rw [dense_iff_closure_eq]
    change closure (Set.range j.base) = Set.univ
    rw [← hs]
    simp
  -- The coproduct of the family is flat over it.
  have hVflat : ∀ κ, Flat (pullback.snd (a κ) (Scheme.Opens.ι j.opensRange)) := by
    intro κ
    have _ := hflat κ
    rw [← Scheme.Hom.isoOpensRange_inv_comp j]
    exact flat_pullback_snd_comp (a κ) j _
  have hUflat : Flat ((Sigma.desc a).resLE j.opensRange
      ((Sigma.desc a) ⁻¹ᵁ j.opensRange) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict,
      ← MorphismProperty.cancel_left_of_respectsIso @Flat
        (pullbackRestrictIsoRestrict (Sigma.desc a) j.opensRange).hom
        ((Sigma.desc a) ∣_ j.opensRange),
      pullbackRestrictIsoRestrict_hom_morphismRestrict]
    exact flat_pullback_snd_sigmaDesc a _ hVflat
  -- Stacks 0815 supplies the flattening centre.
  obtain ⟨I, hIfp, hIdisj, hIflat⟩ := H (Sigma.desc a) j.opensRange hUcompact hUflat
  have _ : Flat (Stacks.Blowup.strictTransformMap (Sigma.desc a) I) := hIflat
  exact hasFlatFppfModification_of_flat_strictTransformMap_sigmaDesc hT hK hA a hstd I
    (Stacks.Blowup.isProper_blowUpToBase I
      ((Stacks.Flatness.finitePresentation_subschemeι_iff I).mp hIfp))
    (Stacks.Blowup.surjective_blowUpToBase hdenseU hIfp hIdisj)

/-- **Stacks 0ETR, granted Stacks 0815.** Every standard V covering of an affine scheme by
morphisms locally of finite presentation is refined by a standard ph covering, granted the
Raynaud–Gruson flattening theorem. This is the one step of the proof of Stacks 0ETR that uses
that theorem; `AlgebraicGeometry.standardVCoveringHasPHRefinement` is this with the theorem
supplied. -/
theorem standardVCoveringHasPHRefinement_of_flatteningBlowup
    (H : FinitePresentationHasFlatteningBlowup.{u}) :
    StandardVCoveringHasPHRefinement.{u} :=
  standardVCoveringHasPHRefinement_of_modification
    (standardVCoveringDenseFlatHasModification_of_flatteningBlowup H)

/-- **Stacks 0ETR, with a single named dependency.** For a family of morphisms locally of finite
presentation, being a ph covering and being a V covering are equivalent — granted the
Raynaud–Gruson flattening theorem of [Stacks, Tag 0815] and nothing else.

Every other input of the Stacks proof is unconditional in this development; see the module
documentation of `StacksFrontier.AlgebraicGeometry.Topologies.V.PhVTfae` for the inventory. -/
theorem isPHCovering_iff_isVCovering_of_flatteningBlowup
    (H : FinitePresentationHasFlatteningBlowup.{u}) {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hfp : ∀ i, LocallyOfFinitePresentation (f i)) :
    IsPHCovering X f ↔ IsVCovering X f :=
  isPHCovering_iff_isVCovering_of_standardVCoveringHasPHRefinement
    (standardVCoveringHasPHRefinement_of_flatteningBlowup H) X f hfp

/-- **Stacks 0ETR from the affine Raynaud–Gruson case.** The equivalence of ph coverings and V
coverings for families locally of finite presentation follows from
`AlgebraicGeometry.FinitePresentationHasAffineChartFlatteningCentre` — the affine case of the
flatness assertion of [Stacks, Tag 0815], where the induction on the maximum fibre-support
dimension lives — and nothing else.

Every reduction between 0ETR and that induction is a theorem of this development, so this
records where the mathematical content sits rather than an outstanding dependency; the predicate
itself holds, and 0ETR with it — see `AlgebraicGeometry.isPHCovering_iff_isVCovering` below. -/
theorem isPHCovering_iff_isVCovering_of_affineChartFlatteningCentre
    (H : FinitePresentationHasAffineChartFlatteningCentre.{u}) {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hfp : ∀ i, LocallyOfFinitePresentation (f i)) :
    IsPHCovering X f ↔ IsVCovering X f :=
  isPHCovering_iff_isVCovering_of_flatteningBlowup
    (finitePresentationHasFlatteningBlowup_of_affineChartFlatteningCentre H) X f hfp

/-- **Stacks 0ETR off the flattening input of the Raynaud-Gruson induction.** The equivalence of
ph coverings and V coverings for families locally of finite presentation follows from
`AlgebraicGeometry.FinitePresentationHasGenericFibreFlatteningBlowup` — which is more than
[Stacks, Tag 0811] concludes, that tag being proved outright — and nothing else.

Everything between that input and 0ETR is a theorem of this development: the Raynaud-Gruson
induction of [Stacks, Tag 0815] on the maximum fibre-support dimension
(`AlgebraicGeometry.moduleFlatteningCentreBelow`), its reading on the affine charts
(`finitePresentationHasAffineChartFlatteningCentre_of_genericFibreFlatteningBlowup`), and the
six steps of the proof of 0ETR. -/
theorem isPHCovering_iff_isVCovering_of_genericFibreFlatteningBlowup
    (H : FinitePresentationHasGenericFibreFlatteningBlowup.{u}) {T : Scheme.{u}} {I : Type v}
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hfp : ∀ i, LocallyOfFinitePresentation (f i)) :
    IsPHCovering X f ↔ IsVCovering X f :=
  isPHCovering_iff_isVCovering_of_affineChartFlatteningCentre
    (finitePresentationHasAffineChartFlatteningCentre_of_genericFibreFlatteningBlowup H) X f hfp

/-! ### Stacks 0ETR -/

/-- **Steps 4 and 5 of the Stacks proof of 0ETR, with nothing granted.** A standard V covering
of an affine scheme by morphisms locally of finite presentation which is already flat over a
quasi-compact scheme-theoretically dense open of the base admits a flattening modification.

The flattening theorem these steps reduce to is
`AlgebraicGeometry.finitePresentationHasFlatteningBlowup`, the morphism form of the flattening
assertion of [Stacks, Tag 0815], which the Raynaud–Gruson induction proves from
[Stacks, Tag 0811]. -/
theorem standardVCoveringDenseFlatHasModification :
    StandardVCoveringDenseFlatHasModification.{u} :=
  standardVCoveringDenseFlatHasModification_of_flatteningBlowup
    finitePresentationHasFlatteningBlowup.{u}

/-- **The last input of Stacks 0ETR, with nothing granted.** Every standard V covering of an
affine scheme by morphisms locally of finite presentation is refined by a standard ph covering.

This is `AlgebraicGeometry.standardVCoveringDenseFlatHasModification` above, bracketed by the
generic flatness reduction and the recognition of the flattened family as a ph covering, which
`StacksFrontier/AlgebraicGeometry/Topologies/V/PhVStratification.lean` supplies unconditionally. -/
theorem standardVCoveringHasPHRefinement : StandardVCoveringHasPHRefinement.{u} :=
  standardVCoveringHasPHRefinement_of_modification standardVCoveringDenseFlatHasModification.{u}

/-- **Stacks 0ETR.** A family of morphisms of schemes which are locally of finite presentation
is a ph covering if and only if it is a V covering.

The implication from a ph covering to a V covering is
`AlgebraicGeometry.isVCovering_of_isPHCovering` and needs nothing; the converse is the six-step
argument of the source, whose last input — the refinement of a standard V covering of an affine
scheme by a standard ph covering, `AlgebraicGeometry.StandardVCoveringHasPHRefinement` — is
`AlgebraicGeometry.standardVCoveringHasPHRefinement` above. -/
@[stacks 0ETR "the equivalence of (1) and (2) for a family locally of finite presentation, \
which is the whole of the lemma"]
theorem isPHCovering_iff_isVCovering {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ T) (hfp : ∀ i, LocallyOfFinitePresentation (f i)) :
    IsPHCovering X f ↔ IsVCovering X f :=
  isPHCovering_iff_isVCovering_of_standardVCoveringHasPHRefinement
    standardVCoveringHasPHRefinement.{u} X f hfp

/-- **An h covering is the same thing as a family of morphisms locally of finite presentation
which is a V covering**, the form in which the source states the definition of an h covering.
This is `AlgebraicGeometry.isPHCovering_iff_isVCovering`, Stacks 0ETR, with the local finite
presentation of the members carried along. -/
theorem isHCovering_iff_isVCovering {T : Scheme.{u}} {I : Type v} (X : I → Scheme.{u})
    (f : ∀ i, X i ⟶ T) :
    IsHCovering X f ↔ (∀ i, LocallyOfFinitePresentation (f i)) ∧ IsVCovering X f :=
  isHCovering_iff_isVCovering_of_standardVCoveringHasPHRefinement
    standardVCoveringHasPHRefinement.{u} X f

end AlgebraicGeometry

end
