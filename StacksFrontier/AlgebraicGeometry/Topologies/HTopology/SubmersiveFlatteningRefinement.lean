module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleSurjective
public import StacksFrontier.AlgebraicGeometry.Blowup.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOffExceptional
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreFreeBlowup0811
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.DiscreteValuationSpecialization
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.DenseOpen
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.DenseFlatSubmersiveReduction
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SubmersiveSpecialization
public import StacksFrontier.AlgebraicGeometry.Topologies.V.FppfAffineDomination
public import StacksFrontier.AlgebraicGeometry.Topologies.V.PhVFlatteningModification

/-!
# Steps 3 to 5 of Stacks 0ETT, and Stacks 0ETT

Over a Noetherian scheme a finite family of finite type morphisms whose disjoint-union morphism
is universally submersive is an h covering. The reduction of this to the case of a family which
is flat over a dense open of the base is carried out in
`StacksFrontier.AlgebraicGeometry.Topologies.HTopology.DenseFlatSubmersiveReduction`; this file
discharges that case, which is steps 3 to 5 of the source's proof, and so proves Stacks 0ETT.

Everything is done for the *single* morphism `∐ X i ⟶ X`, which is legitimate because a family
of morphisms locally of finite type is a ph covering exactly when its disjoint-union morphism is
one (Stacks 0ET9, `AlgebraicGeometry.isPHCovering_tfae`).

## Main results

* `AlgebraicGeometry.surjective_strictTransformMap_of_universallySubmersive`: **step 4** — for a
  universally submersive morphism of finite type to a Noetherian scheme and *any* centre on the
  base, the strict transform along the blowup in that centre is surjective over the blowup.
* `AlgebraicGeometry.isPHCovering_unit_of_universallySubmersive_of_denseFlat`: **steps 3 to 5**
  for a single morphism — a universally submersive morphism of finite type to a Noetherian
  scheme which is flat over a dense open of the base is a ph covering.
* `AlgebraicGeometry.denseFlatUniversallySubmersiveHasPHRefinement` and
  `AlgebraicGeometry.universallySubmersiveHasPHRefinement`: the two predicates carried by the
  conditional forms of Stacks 0ETT (1) ⟹ (2), with nothing granted.
* `AlgebraicGeometry.isHCovering_of_universallySubmersive_of_isNoetherian`: **Stacks 0ETT (1) ⟹
  (2)**, and `AlgebraicGeometry.universallySubmersive_sigmaDesc_iff_isHCovering_of_isNoetherian`:
  **Stacks 0ETT**, both with nothing granted.

## Implementation notes

**One blowup for the whole family.** The Raynaud–Gruson flattening theorem of Stacks 0815 —
available here as `AlgebraicGeometry.finitePresentationHasFlatteningBlowup` — flattens one
morphism, so it is applied to `∐ f i`, exactly as the source does. The family is then never
reassembled: the ph covering produced over the blowup is the singleton consisting of the strict
transform of `∐ X i`, and Stacks 0ET9 turns a ph covering of the base refining the singleton
family `{∐ X i ⟶ X}` into one refining `{X i ⟶ X}`. So no statement identifying the strict
transform of a coproduct with the coproduct of the strict transforms is needed, and none is
proved here.

**No further admissible blowup.** Before running its valuative argument the source replaces the
blowup by a further `U`-admissible blowup, so as to make the inverse image of the dense open `U`
scheme-theoretically dense upstairs (Stacks 080Y). That step is not needed. The valuative
argument asks for a dense open of the blowup over which the strict transform is the plain base
change, and `Stacks.Blowup.isIso_strictTransformι_restrict` says that the complement of the
exceptional divisor is such an open, with no hypothesis at all; that complement is
scheme-theoretically dense because the exceptional divisor is an effective Cartier divisor
(`Stacks.Blowup.isSchemeTheoreticallyDense_compl_support_exceptionalIdeal`), hence topologically
dense, which is what Stacks 0CM2 consumes. So no second blowup, and no domination of two blowups
by a third, enters.

**The valuative diagram.** Stacks 0CM2 —
`AlgebraicGeometry.nonempty_discreteValuationSpecialization` — is applied to the inclusion of
that complement: it is quasi-compact, the complement of an effective Cartier divisor being
affine over the ambient scheme, and the blowup of a Noetherian
scheme is Noetherian, so every point of the blowup is reached by a discrete valuation ring whose
generic point lands in the complement. Universal submersiveness then supplies, by
`AlgebraicGeometry.exists_specializes_closedPoint_of_universallySubmersive` — step 4 of the
source — a specialization in the base change along that discrete valuation ring lying over the
generic and the closed point. Its generalization lies over the complement of the exceptional
divisor, hence inside the strict transform; the strict transform is a closed subscheme, so the
specialization lies in it too, and it lies over the given point of the blowup.

## References

* [Stacks Project, Tag 040H](https://stacks.math.columbia.edu/tag/040H)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 0CM2](https://stacks.math.columbia.edu/tag/0CM2)
* [Stacks Project, Tag 0DBI](https://stacks.math.columbia.edu/tag/0DBI)
* [Stacks Project, Tag 0DBT](https://stacks.math.columbia.edu/tag/0DBT)
* [Stacks Project, Tag 0DES](https://stacks.math.columbia.edu/tag/0DES)
* [Stacks Project, Tag 0ET9](https://stacks.math.columbia.edu/tag/0ET9)
* [Stacks Project, Tag 0ETT](https://stacks.math.columbia.edu/tag/0ETT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- A point of an open over which a morphism restricts to an isomorphism lies in the range of
that morphism: the restriction is an isomorphism, so it hits the point, and the restriction
composed with the inclusion of the open is the inclusion of its preimage composed with the
morphism (`AlgebraicGeometry.morphismRestrict_ι`). -/
private theorem mem_range_of_isIso_morphismRestrict {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (V : Z.Opens) [IsIso (g ∣_ V)] {z : Z} (hz : z ∈ V) : z ∈ Set.range g.base := by
  obtain ⟨v, hv⟩ : z ∈ Set.range (Scheme.Opens.ι V).base := by
    rwa [Scheme.Opens.range_ι]
  obtain ⟨y, hy⟩ := (g ∣_ V).surjective v
  refine ⟨(g ⁻¹ᵁ V).ι.base y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hy, hv]

/-- A compact scheme locally of finite type over a Noetherian scheme is Noetherian. -/
private theorem isNoetherian_source_of_locallyOfFiniteType {S X : Scheme.{u}} [IsNoetherian X]
    (g : S ⟶ X) [LocallyOfFiniteType g] [CompactSpace S] : IsNoetherian S :=
  have := LocallyOfFiniteType.isLocallyNoetherian g
  ⟨⟩

/-- The complement of the exceptional divisor of a blowup is topologically dense. -/
theorem dense_compl_support_exceptionalIdeal {X : Scheme.{u}} (ℐ : X.IdealSheafData) :
    Dense (((Stacks.Blowup.exceptionalIdeal ℐ).support.compl :
      (Stacks.Blowup.blowUp ℐ).Opens) : Set (Stacks.Blowup.blowUp ℐ)) := by
  have _ : IsSchemeTheoreticallyDominant (Scheme.Opens.ι
      ((Stacks.Blowup.exceptionalIdeal ℐ).support.compl : (Stacks.Blowup.blowUp ℐ).Opens)) :=
    Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDominant_of_dense _
      (Stacks.Blowup.isSchemeTheoreticallyDense_compl_support_exceptionalIdeal ℐ)
  have hs := Scheme.Hom.support_ker (Scheme.Opens.ι
    ((Stacks.Blowup.exceptionalIdeal ℐ).support.compl : (Stacks.Blowup.blowUp ℐ).Opens))
  rw [IsSchemeTheoreticallyDominant.ker_eq_bot _] at hs
  rw [dense_iff_closure_eq, ← Scheme.Opens.range_ι, ← hs]
  simp

/-- The generic point of the spectrum of the discrete valuation ring of a
`DiscreteValuationSpecialization` of `f` lands in the range of `f`. -/
theorem DiscreteValuationSpecialization.toTarget_genericPoint_mem_range {X Y : Scheme.{u}}
    {f : X ⟶ Y} {y : Y} (D : DiscreteValuationSpecialization f y) :
    D.toTarget.base (_root_.genericPoint (Spec (CommRingCat.of D.valuationRing))) ∈
      Set.range f.base := by
  have h₁ := congrArg (fun k : Spec (CommRingCat.of D.fractionField) ⟶ Y ↦
    k.base (_root_.genericPoint (Spec (CommRingCat.of D.fractionField)))) D.commutes
  simp only [Scheme.Spec_map, Quiver.Hom.unop_op, Scheme.Hom.comp_apply,
    Spec_map_base_genericPoint_eq (algebraMap D.valuationRing D.fractionField)
      (IsFractionRing.injective D.valuationRing D.fractionField)] at h₁
  rw [h₁]
  exact Set.mem_range_self _

/-- **Step 4 of the Stacks proof of 0ETT (1) ⟹ (2).** Let `f : W ⟶ X` be a quasi-compact
morphism locally of finite type to a Noetherian scheme which is universally submersive, and let
`ℐ` be *any* centre on `X`. Then the strict transform of `W` along the blowup of `X` in `ℐ` is
**surjective** over the blowup.

This is the valuative argument of the source. The complement `Ω` of the exceptional divisor is
scheme-theoretically dense in the blowup
(`Stacks.Blowup.isSchemeTheoreticallyDense_compl_support_exceptionalIdeal`), hence topologically
dense, so Stacks 0CM2 (`AlgebraicGeometry.nonempty_discreteValuationSpecialization`) reaches a
given point `t` of the blowup by a discrete valuation ring `A`: a morphism `Spec A ⟶ S'` carrying
the closed point to `t` and the generic point into `Ω`. Universal submersiveness of `f` produces,
by `AlgebraicGeometry.exists_specializes_closedPoint_of_universallySubmersive`, a specialization
`w' ⤳ w` in `W ×_X Spec A` with `w'` over the generic point of `Spec A` and `w` over its closed
point. Pushing it into `W ×_X S'`, the image of `w'` lies over `Ω`, where the closed immersion of
the strict transform is an isomorphism (`Stacks.Blowup.isIso_strictTransformι_restrict`), so it
lies in the strict transform; the strict transform has closed range, so the image of `w` lies in
it as well, and that point lies over `t`.

Nothing here uses `ℐ`: the centre only has to be flattening for the *next* step. -/
theorem surjective_strictTransformMap_of_universallySubmersive {W X : Scheme.{u}}
    [IsNoetherian X] (f : W ⟶ X) [LocallyOfFiniteType f] [QuasiCompact f]
    (hsub : UniversallySubmersive f) (ℐ : X.IdealSheafData) :
    Surjective (Stacks.Blowup.strictTransformMap f ℐ) := by
  have _ : CompactSpace (Stacks.Blowup.blowUp ℐ) :=
    QuasiCompact.compactSpace_of_compactSpace (Stacks.Blowup.blowUpToBase ℐ)
  have _ : IsNoetherian (Stacks.Blowup.blowUp ℐ) :=
    isNoetherian_source_of_locallyOfFiniteType (Stacks.Blowup.blowUpToBase ℐ)
  have _ : IsAffineHom (Scheme.Opens.ι
      ((Stacks.Blowup.exceptionalIdeal ℐ).support.compl : (Stacks.Blowup.blowUp ℐ).Opens)) :=
    Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal_reesData ℐ)
  refine ⟨fun t ↦ ?_⟩
  obtain ⟨D⟩ := nonempty_discreteValuationSpecialization (Scheme.Opens.ι
      ((Stacks.Blowup.exceptionalIdeal ℐ).support.compl : (Stacks.Blowup.blowUp ℐ).Opens)) t
    (by simpa only [Scheme.Opens.range_ι] using dense_compl_support_exceptionalIdeal ℐ t)
  have hgen : D.toTarget.base (genericPoint (Spec (CommRingCat.of D.valuationRing))) ∈
      (((Stacks.Blowup.exceptionalIdeal ℐ).support.compl : (Stacks.Blowup.blowUp ℐ).Opens) :
        Set (Stacks.Blowup.blowUp ℐ)) := by
    simpa only [Scheme.Opens.range_ι] using D.toTarget_genericPoint_mem_range
  obtain ⟨w, w', hw, hw', hspec⟩ :=
    exists_specializes_closedPoint_of_universallySubmersive f hsub D.valuationRing
      (D.toTarget ≫ Stacks.Blowup.blowUpToBase ℐ)
  have hcond : pullback.fst f (D.toTarget ≫ Stacks.Blowup.blowUpToBase ℐ) ≫ f =
      (pullback.snd f (D.toTarget ≫ Stacks.Blowup.blowUpToBase ℐ) ≫ D.toTarget) ≫
        Stacks.Blowup.blowUpToBase ℐ :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  have hlsnd : ∀ z, (Stacks.Blowup.blowUpPullbackToBlowUp f ℐ).base
      ((pullback.lift _ _ hcond).base z) = D.toTarget.base
        ((pullback.snd f (D.toTarget ≫ Stacks.Blowup.blowUpToBase ℐ)).base z) := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd, Scheme.Hom.comp_apply]
  have hw'mem : (pullback.lift _ _ hcond).base w' ∈ Stacks.Blowup.exceptionalPullbackCompl f ℐ := by
    refine Stacks.Blowup.preimage_le_exceptionalPullbackCompl f ℐ
      (W := (Stacks.Blowup.exceptionalIdeal ℐ).support.compl) le_rfl ?_
    change (Stacks.Blowup.blowUpPullbackToBlowUp f ℐ).base ((pullback.lift _ _ hcond).base w') ∈
      ((Stacks.Blowup.exceptionalIdeal ℐ).support.compl : (Stacks.Blowup.blowUp ℐ).Opens)
    rw [hlsnd w', hw']
    exact hgen
  have hrange : (pullback.lift _ _ hcond).base w ∈
      Set.range (Stacks.Blowup.strictTransformι f ℐ).base :=
    (hspec.map (pullback.lift _ _ hcond).continuous).mem_closed
      (Stacks.Blowup.strictTransformι f ℐ).isClosedEmbedding.isClosed_range
      (mem_range_of_isIso_morphismRestrict (Stacks.Blowup.strictTransformι f ℐ)
        (Stacks.Blowup.exceptionalPullbackCompl f ℐ) hw'mem)
  obtain ⟨x, hx⟩ := hrange
  refine ⟨x, ?_⟩
  change (Stacks.Blowup.blowUpPullbackToBlowUp f ℐ).base
    ((Stacks.Blowup.strictTransformι f ℐ).base x) = t
  rw [hx, hlsnd w, hw]
  exact D.maps_closedPoint

/-- **Steps 3 to 5 of the Stacks proof of 0ETT (1) ⟹ (2), for a single morphism.** A
quasi-compact morphism `f : W ⟶ X` locally of finite type to a Noetherian scheme which is
universally submersive and flat over a dense open `U` of the base is a ph covering of `X`.

Step 3 is the Raynaud–Gruson flattening theorem,
`AlgebraicGeometry.finitePresentationHasFlatteningBlowup`: it supplies a `U`-admissible centre
`ℐ` after whose blowup the strict transform of `W` is flat.
That blowup is proper, the base being Noetherian, and surjective because `U` is dense
(`Stacks.Blowup.surjective_blowUpToBase`); the strict transform is locally of finite presentation
over it by the finite presentation half of Stacks 0815
(`Stacks.Blowup.locallyOfFinitePresentation_strictTransformMap_of_flat`) and surjective by step 4,
`AlgebraicGeometry.surjective_strictTransformMap_of_universallySubmersive`. So the strict
transform is an fppf covering of the blowup, hence a ph covering of it by Stacks 0DBT, the blowup
is a ph covering of `X` by Stacks 0DES, and Stacks 0DBI part (2) binds the two into a ph covering
of `X` refining `f` through `Stacks.Blowup.strictTransformToSource`. Stacks 0ET9 then recognizes
`f` itself as a ph covering. -/
theorem isPHCovering_unit_of_universallySubmersive_of_denseFlat {W X : Scheme.{u}}
    [IsNoetherian X] (f : W ⟶ X) [LocallyOfFiniteType f] [QuasiCompact f]
    (hsub : UniversallySubmersive f) (U : X.Opens) (hU : Dense (U : Set X))
    (hflat : Flat (pullback.snd f U.ι)) :
    IsPHCovering (fun _ : Unit ↦ W) (fun _ ↦ f) := by
  have _ : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace f
  have _ : QuasiSeparatedSpace X := ⟨fun _ _ _ _ _ _ ↦ NoetherianSpace.isCompact _⟩
  have _ : LocallyOfFinitePresentation f :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have _ : MorphismProperty.RespectsIso (@Flat.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hUflat : Flat (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    rwa [Scheme.Hom.resLE_eq_morphismRestrict,
      ← MorphismProperty.cancel_left_of_respectsIso @Flat
        (pullbackRestrictIsoRestrict f U).hom (f ∣_ U),
      pullbackRestrictIsoRestrict_hom_morphismRestrict]
  obtain ⟨ℐ, hIfp, hIdisj, hIflat⟩ :=
    finitePresentationHasFlatteningBlowup.{u} f U (NoetherianSpace.isCompact _) hUflat
  have _ : Flat (Stacks.Blowup.strictTransformMap f ℐ) := hIflat
  have _ : LocallyOfFinitePresentation (Stacks.Blowup.strictTransformMap f ℐ) :=
    Stacks.Blowup.locallyOfFinitePresentation_strictTransformMap_of_flat f ℐ
  have _ : Surjective (Stacks.Blowup.strictTransformMap f ℐ) :=
    surjective_strictTransformMap_of_universallySubmersive f hsub ℐ
  have _ : Surjective (Stacks.Blowup.blowUpToBase ℐ) :=
    Stacks.Blowup.surjective_blowUpToBase hU hIfp hIdisj
  have hinner : IsPHCovering (fun _ : Unit ↦ Stacks.Blowup.strictTransform f ℐ)
      (fun _ ↦ Stacks.Blowup.strictTransformMap f ℐ) :=
    IsPHCovering.of_mem_fppfPrecoverage _ _ ((Scheme.ofArrows_mem_precoverage_iff
      (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr
        ⟨fun x ↦ ⟨(), (surjective_iff (Stacks.Blowup.strictTransformMap f ℐ)).1 inferInstance x⟩,
          fun _ ↦ ⟨inferInstance, inferInstance⟩⟩)
  have hbind : IsPHCovering (fun _ : Σ _ : Unit, Unit ↦ Stacks.Blowup.strictTransform f ℐ)
      (fun _ ↦ Stacks.Blowup.strictTransformMap f ℐ ≫ Stacks.Blowup.blowUpToBase ℐ) :=
    isPHCovering_bind
      (PreZeroHypercover.mk Unit (fun _ ↦ Stacks.Blowup.blowUp ℐ)
        (fun _ ↦ Stacks.Blowup.blowUpToBase ℐ))
      (surjective_proper_isPHCovering (Stacks.Blowup.blowUpToBase ℐ))
      (fun _ ↦ PreZeroHypercover.mk Unit (fun _ ↦ Stacks.Blowup.strictTransform f ℐ)
        (fun _ ↦ Stacks.Blowup.strictTransformMap f ℐ))
      (fun _ ↦ hinner)
  have Φ : (PreZeroHypercover.mk (Σ _ : Unit, Unit)
      (fun _ ↦ Stacks.Blowup.strictTransform f ℐ)
      (fun _ ↦ Stacks.Blowup.strictTransformMap f ℐ ≫ Stacks.Blowup.blowUpToBase ℐ) :
        PreZeroHypercover.{0} X).Hom
      (PreZeroHypercover.mk Unit (fun _ ↦ W) (fun _ ↦ f)) :=
    { s₀ := fun _ ↦ ()
      h₀ := fun _ ↦ Stacks.Blowup.strictTransformToSource f ℐ
      w₀ := fun _ ↦ Stacks.Blowup.strictTransformToSource_comp f ℐ }
  refine ((isPHCovering_tfae (fun _ : Unit ↦ W) (fun _ ↦ f) fun _ ↦ inferInstance).out 2 1).1 ?_
  exact ⟨(Σ _ : Unit, Unit), _, _, hbind, ⟨Φ⟩⟩

/-- **Steps 3 to 5 of the Stacks proof of 0ETT (1) ⟹ (2), with nothing granted.** A finite
family of morphisms of finite type to a Noetherian scheme whose disjoint-union morphism is
universally submersive and which is flat over a dense open of the base is refined by a ph
covering.

The problem is transported to the single morphism `∐ X i ⟶ X`, which is again quasi-compact and
locally of finite type and over which the family is flat
(`AlgebraicGeometry.flat_pullback_snd_sigmaDesc`), by the two outer equivalences of Stacks 0ET9;
`AlgebraicGeometry.isPHCovering_unit_of_universallySubmersive_of_denseFlat` settles it there. -/
theorem denseFlatUniversallySubmersiveHasPHRefinement :
    DenseFlatUniversallySubmersiveHasPHRefinement.{u, v} := by
  intro X _ I _ _ Y f hft hqc hsub U hUdense hflat
  have _ : ∀ i, LocallyOfFiniteType (f i) := hft
  have _ : ∀ i, QuasiCompact (f i) := hqc
  have _ : LocallyOfFiniteType (Sigma.desc f) := locallyOfFiniteType_sigmaDesc f
  have _ : ∀ i, CompactSpace (Y i) := fun i ↦ QuasiCompact.compactSpace_of_compactSpace (f i)
  have _ : CompactSpace (∐ Y : Scheme.{u}) := by
    rw [← isCompact_univ_iff]
    have huniv : (Set.univ : Set (∐ Y : Scheme.{u})) = ⋃ i, Set.range (Sigma.ι Y i).base := by
      ext p
      simp only [Set.mem_univ, true_iff, Set.mem_iUnion]
      obtain ⟨i, y, hy⟩ := (sigmaOpenCover Y).exists_eq p
      exact ⟨i, y, hy⟩
    rw [huniv]
    exact isCompact_iUnion fun i ↦ isCompact_range (Sigma.ι Y i).continuous
  have _ : IsNoetherian (∐ Y : Scheme.{u}) :=
    isNoetherian_source_of_locallyOfFiniteType (Sigma.desc f)
  have hph : IsPHCovering (fun _ : Unit ↦ (∐ Y : Scheme.{u})) (fun _ ↦ Sigma.desc f) :=
    isPHCovering_unit_of_universallySubmersive_of_denseFlat (Sigma.desc f) hsub U hUdense
      (flat_pullback_snd_sigmaDesc f U.ι hflat)
  exact ((isPHCovering_tfae Y f hft).out 1 2).1 (((isPHCovering_tfae Y f hft).out 3 1).1 hph)

/-- **The geometric input of Stacks 0ETT, with nothing granted.** A finite family of morphisms of
finite type to a Noetherian scheme whose disjoint-union morphism is universally submersive is
refined by a ph covering.

This is `AlgebraicGeometry.denseFlatUniversallySubmersiveHasPHRefinement` above fed to the
generic flatness reduction `AlgebraicGeometry.UniversallySubmersiveHasPHRefinement.of_denseFlat`,
which is steps 1 and 2 of the source's proof. -/
theorem universallySubmersiveHasPHRefinement : UniversallySubmersiveHasPHRefinement.{u, v} :=
  .of_denseFlat denseFlatUniversallySubmersiveHasPHRefinement.{u, v}

/-- **Stacks 0ETT, (1) implies (2).** A finite family of morphisms of finite type to a Noetherian
scheme whose disjoint-union morphism is universally submersive is an h covering.

This is `AlgebraicGeometry.isHCovering_of_universallySubmersive` with its
hypothesis supplied by `AlgebraicGeometry.universallySubmersiveHasPHRefinement`. -/
@[stacks 0ETT "(1) implies (2)"]
theorem isHCovering_of_universallySubmersive_of_isNoetherian {X : Scheme.{u}} [IsNoetherian X]
    {I : Type v} [Finite I] [Small.{u} I] {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ X)
    [∀ i, LocallyOfFiniteType (f i)] [∀ i, QuasiCompact (f i)]
    (hsub : UniversallySubmersive (Sigma.desc f)) : IsHCovering Y f :=
  isHCovering_of_universallySubmersive
    universallySubmersiveHasPHRefinement.{u, v} f hsub

/-- **Stacks 0ETT.** For a finite family `{X i ⟶ X}` of morphisms of finite type to a Noetherian
scheme `X`, the morphism `∐ X i ⟶ X` is universally submersive if and only if the family is an h
covering.

The implication from the h covering condition is
`AlgebraicGeometry.universallySubmersive_sigmaDesc_of_isHCovering` and needs neither finiteness
nor the Noetherian hypothesis; the converse is
`AlgebraicGeometry.isHCovering_of_universallySubmersive_of_isNoetherian` above. -/
@[stacks 0ETT]
theorem universallySubmersive_sigmaDesc_iff_isHCovering_of_isNoetherian {X : Scheme.{u}}
    [IsNoetherian X] {I : Type v} [Finite I] [Small.{u} I] {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ X)
    [∀ i, LocallyOfFiniteType (f i)] [∀ i, QuasiCompact (f i)] :
    UniversallySubmersive (Sigma.desc f) ↔ IsHCovering Y f :=
  ⟨isHCovering_of_universallySubmersive_of_isNoetherian f,
    universallySubmersive_sigmaDesc_of_isHCovering⟩

end AlgebraicGeometry

end
