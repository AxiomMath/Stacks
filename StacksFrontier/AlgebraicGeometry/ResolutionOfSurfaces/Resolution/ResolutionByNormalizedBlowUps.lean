module

public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.RegularBaseChange
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.Normalization.NormalizedBlowUpDescentExtra
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Nagata
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpReduction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.NormalizedBlowUps
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending a resolution by normalized blowups from the completion

Let `(A, 𝔪)` be a Noetherian local normal domain whose completion `A^` is a normal Nagata ring.
If `Spec A^` has a resolution of singularities by normalized blowups, then so does `Spec A`: the
sequence of normalized blowups upstairs descends, stage by stage, to a sequence of normalized
blowups over `Spec A`, every stage of which is proper over `Spec A` and whose total space is
regular.

## Main results

* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_adicCompletion`: the descent.

## Implementation notes

The sequence of normalized blowups over `Spec A` and its stagewise cartesian squares over the
given sequence come from [Stacks, Tag 0BGA]. That tag produces
`AlgebraicGeometry.NormalizedBlowUpSeq`, whose base case is the identity of the base, and carries
properness of the top stage only, because `AlgebraicGeometry.NormalizedBlowUpSeq.properties` needs
a Nagata base and `Spec A` is not known to be one. The chain of [Stacks, Tag 0BGL] demands
properness of *every* stage over the base, so properness is proved here for every stage, by
induction over the descent: a normalized blowup is the normalization of a blowup, so each step is
separated and universally closed — the blowup morphism of an ideal sheaf of finite type on a
locally Noetherian scheme is proper and a normalization morphism is integral — while being locally
of finite type is descended along the completion morphism, which is surjective, flat and
quasi-compact, from the stage upstairs, proper because `Spec A^` is Nagata.

The base case of a chain is the normalization of the base rather than the base itself. Over a
normal base that normalization is an isomorphism, so the two sequences differ stage by stage by
isomorphisms over the base. Downwards, from the chain over `Spec A^` to a sequence over `Spec A^`,
that comparison is `AlgebraicGeometry.factorsAsNormalizedPointBlowups_of_normalizedBlowUpChain`;
upwards, from the descended sequence over `Spec A` to a chain over `Spec A`, the isomorphism is
propagated with `AlgebraicGeometry.exists_isPullback_normalizedBlowUp_comap`, an isomorphism being
flat and a preimmersion and the reduced point at a point pulling back to the reduced point at its
image. Regularity and properness are transported along those isomorphisms.

That `A^` is a Nagata ring is carried as a hypothesis, as it is in Tag 0BGA: it is
[Stacks, Tag 0335] item (2) for a Noetherian complete local ring, which is not available here.

Regularity descends by the proper case of [Stacks, Tag 0BG6], which compares a scheme proper over
`Spec A` with its base change to `A^`; that base change is the given sequence, by the cartesian
square of Tag 0BGA.

### What Stacks 0BGM still needs

No attribute for that tag is carried here. The statement of [Stacks, Tag 0BGM] is that a
two-dimensional Noetherian local normal ring whose spectrum has a resolution of singularities has
a resolution by normalized blowups, and what this file proves is only the source's first step, the
reduction to the complete case: the hypothesis here is a resolution by normalized blowups of
`Spec A^`, not a resolution of singularities of `Spec A`. The source's remaining steps dominate
the given resolution by normalized blowups ([Stacks, Tag 0BBT], available as
`Stacks.ResolutionOfSurfaces.exists_normalizedBlowUpChain_dominating`), observe that the resulting
normal surface has finitely many singular points, all of them rational singularities by
[Stacks, Tags 0B4Q and 0BG0], and then resolve those points in two further passes. Each pass needs
an input that no declaration outside the tagged statements concludes: [Stacks, Tag 0BBV], which
blows up the singular closed points of a rational surface singularity until the dualizing module
is invertible, and [Stacks, Tag 0BGE], which resolves a rational double point.

Checked tag by tag, that residue is smaller than the two names suggest: the inputs of those two
tags are largely available. Of the eight tags the source's proof of Tag 0BBV cites, seven are
carried:
[Stacks, Tag 0ESN] on the strict transform of a module after a Fitting blowup
(`AlgebraicGeometry.isFiniteLocallyFreeOfRank_strictTransform_of_dense` and its siblings in
`Blowup/Transform/FittingFlatten.lean`), Tag 0BBT, Tag 0AWX
(`Dualizing.IsRegularLocalRing.isGorensteinLocalRing`), Tag 0AGR
(`AlgebraicGeometry.isRegular_blowUp_maximalIdeal`), Tag 0AWK
(`Stacks.Duality.IsDualizingModuleOf.isCoherent` and the support and `(S₂)` clauses), Tag 0B64
(`AlgebraicGeometry.BlowUpDualizing.nonempty_dualizingSheafOverField_iso_curveTwist`), and — over
its own named carried hypothesis rather than unconditionally — Tag 0BBU
(`AlgebraicGeometry.RationalSingularitySituation.bijective_trace`). Dualizing complexes and
dualizing modules, for rings and for schemes, are developed at length in `RingTheory/Dualizing/`
and `AlgebraicGeometry/Duality/`. The eighth is [Stacks, Tag 0B4Z], and it is the only structural
gap under Tag 0BBV: it is carried as a hypothesis wherever it is needed, under the name
`AlgebraicGeometry.BlowUpMaximalIdealIsNormal` in
`RationalDoublePoints/BlowUpCompletionNormal.lean`.

Of the assembly itself, Steps 3 and 5 no longer need anything. The chain over `Spec A` reaching
the dominating stage and the chain over that stage compose, by
`AlgebraicGeometry.exists_normalizedBlowUpChain_comp`, so a resolution by normalized blowups of
the stage gives one of `Spec A` by
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_chain`; the stage is normal by
`AlgebraicGeometry.NormalizedBlowUpChain.isNormal`; it has finitely many singular points by
`AlgebraicGeometry.finite_singularLocus_of_locallyOfFiniteType_over_completeLocalRing`, the base
being complete after Step 1 and the stage proper over it; and local resolutions at those points
assemble into one over the stage by
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_local`. What is left between this file and
Tag 0BGM is therefore Tag 0BBV over Tag 0B4Z, Tag 0BGE, and the rationality of the singular
local rings of the dominating stage — Step 4's first half, which is Tag 0B4Q together with Tag
0BG0 in its local-ring form,
`AlgebraicGeometry.definesRationalSingularity_stalk_of_isModification`.

## References

* [Stacks Project, Tag 0BGA](https://stacks.math.columbia.edu/tag/0BGA)
* [Stacks Project, Tag 0BGL](https://stacks.math.columbia.edu/tag/0BGL)
* [Stacks Project, Tag 0BG6](https://stacks.math.columbia.edu/tag/0BG6)
* [Stacks Project, Tag 0BGM](https://stacks.math.columbia.edu/tag/0BGM)
* [Stacks Project, Tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Properness of the stages of a descended sequence -/

/-- The morphism from the spectrum of the completion of a Noetherian local ring is surjective,
flat and quasi-compact: the completion is faithfully flat, the maximal ideal being contained in
the Jacobson radical, and the morphism is affine. -/
@[ega "IV 8.11.4" "partial", sga "1 IV 3.2" "special case"]
private theorem surjective_flat_quasiCompact_specMapAdicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (specMapAdicCompletion A) := by
  have hff : Module.FaithfullyFlat A (AdicCompletion (maximalIdeal A) A) :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson _
      (by rw [← Ideal.jacobson_bot]; exact IsLocalRing.maximalIdeal_le_jacobson ⊥)
  obtain ⟨hflat, hsurj⟩ := (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap A (AdicCompletion (maximalIdeal A) A)))).mpr
    (by rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]; exact hff)
  exact ⟨⟨hsurj, hflat⟩, inferInstance⟩

/-- The normalized blowup at a closed point of a locally Noetherian scheme is separated and
universally closed: the blowup morphism is proper, the ideal sheaf of a point of a locally
Noetherian scheme being of finite type, and the normalization morphism is integral. -/
private theorem isSeparated_and_universallyClosed_normalizedBlowUp {X : Scheme.{u}}
    [IsLocallyNoetherian X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    IsSeparated (Stacks.Blowup.normalizedBlowUp X hX x hx) ∧
      UniversallyClosed (Stacks.Blowup.normalizedBlowUp X hX x hx) := by
  have hfg : ∀ U : X.affineOpens,
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).ideal U).FG := by
    intro U
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    exact IsNoetherian.noetherian _
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  let hfin := Stacks.Blowup.finite_irreducibleComponents_blowUp I hX
  let : IsProper (blowUpToBase I) := isProper_blowUpToBase_of_fg I hfg
  let : IsSeparated (Scheme.normalization (blowUp I) hfin) := IsSeparated.of_isAffineHom _
  refine ⟨?_, ?_⟩
  · change IsSeparated (Scheme.normalization (blowUp I) hfin ≫ blowUpToBase I)
    infer_instance
  · change UniversallyClosed (Scheme.normalization (blowUp I) hfin ≫ blowUpToBase I)
    infer_instance

/-- Every stage of a sequence of normalized blowups over `Spec A` which descends from the
completion is proper over `Spec A`. Being separated and universally closed is read off from the
stage itself, a normalized blowup being the normalization of a blowup; being locally of finite
type is descended from the base change to `A^`, which is proper over `Spec A^` because that base
is Nagata. -/
private theorem isProper_of_normalizedBlowUpSeqDescent
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hnagataB : IsNagataScheme (Spec (.of (AdicCompletion (maximalIdeal A) A))))
    [IsLocallyNoetherian (Spec (.of (AdicCompletion (maximalIdeal A) A)))]
    [IsNormal (Spec (.of (AdicCompletion (maximalIdeal A) A)))]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {g : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))} {p : Y ⟶ X}
    (hdesc : NormalizedBlowUpSeqDescent A X f Y g p) : IsProper f := by
  induction hdesc with
  | refl => infer_instance
  | @blowUp X f Y g p prev hXfin hYfin x hx y hy t hcart ih =>
    let : IsProper f := ih
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    obtain ⟨hsep, huc⟩ := isSeparated_and_universallyClosed_normalizedBlowUp hXfin x hx
    let : IsSeparated (Stacks.Blowup.normalizedBlowUp X hXfin x hx) := hsep
    let : UniversallyClosed (Stacks.Blowup.normalizedBlowUp X hXfin x hx) := huc
    let hdesc' := NormalizedBlowUpSeqDescent.blowUp prev hXfin hYfin x hx y hy t hcart
    have hup : IsProper (Stacks.Blowup.normalizedBlowUp Y hYfin y hy ≫ g) :=
      (hdesc'.seqCompletion.properties hnagataB).2.2.2
    have hlft : LocallyOfFiniteType (Stacks.Blowup.normalizedBlowUp X hXfin x hx ≫ f) :=
      MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType)
        hdesc'.isPullback.flip (surjective_flat_quasiCompact_specMapAdicCompletion A)
        hup.toLocallyOfFiniteType
    exact (isProper_iff _).mpr ⟨inferInstance, inferInstance, hlft⟩

/-! ### Assembling the chain over `Spec A` -/

/-- A sequence of normalized blowups over a normal base `Spec A` which descends from the
completion is, up to an isomorphism over `Spec A`, a chain of normalized blowups in the sense of
Tag 0BGL: over a normal base the normalization step of such a chain is an isomorphism, a
normalized blowup transports along an isomorphism of its base, and properness of every stage is
available for a descended sequence. -/
private theorem exists_normalizedBlowUpChain_of_normalizedBlowUpSeqDescent
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsNormal (Spec (.of A))]
    (hnagataB : IsNagataScheme (Spec (.of (AdicCompletion (maximalIdeal A) A))))
    [IsLocallyNoetherian (Spec (.of (AdicCompletion (maximalIdeal A) A)))]
    [IsNormal (Spec (.of (AdicCompletion (maximalIdeal A) A)))]
    (hAfin : ∀ U : (Spec (.of A)).Opens, IsCompact (U : Set (Spec (.of A))) →
      (irreducibleComponents U).Finite)
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of A)}
    {g : Y ⟶ Spec (.of (AdicCompletion (maximalIdeal A) A))} {p : Y ⟶ X}
    (hdesc : NormalizedBlowUpSeqDescent A X f Y g p) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ Spec (.of A)),
      NormalizedBlowUpChain (Spec (.of A)) hAfin Z q ∧ ∃ e : X ≅ Z, e.hom ≫ q = f := by
  induction hdesc with
  | refl =>
    have : IsIso (Scheme.normalization (Spec (.of A)) hAfin) :=
      (Scheme.isIso_normalization_iff_isNormal _ hAfin).2 inferInstance
    exact ⟨_, _, NormalizedBlowUpChain.normalization inferInstance,
      (asIso (Scheme.normalization (Spec (.of A)) hAfin)).symm, by simp⟩
  | @blowUp X f Y g p prev hXfin hYfin x hx y hy t hcart ih =>
    obtain ⟨Z, q, hchain, e, he⟩ := ih
    have hZfin : ∀ U : Z.Opens, IsCompact (U : Set Z) → (irreducibleComponents U).Finite :=
      finite_irreducibleComponents_of_smooth e.inv hXfin
    have hz : IsClosed ({e.hom x} : Set Z) := by
      have hset : ({e.hom x} : Set Z) = e.inv ⁻¹' ({x} : Set X) := by
        ext z
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        refine ⟨fun hzx => by subst hzx; simp, fun hzx => ?_⟩
        rw [← show e.hom (e.inv z) = z from by simp, hzx]
      rw [hset]
      exact hx.preimage e.inv.continuous
    obtain ⟨_, hideal⟩ :=
      vanishingIdeal_singleton_comap_of_isIso e.hom (e.hom x) hz x rfl
    obtain ⟨m, hm⟩ :=
      exists_isPullback_normalizedBlowUp_comap e.hom hZfin hXfin (e.hom x) hz x hx hideal
    have : IsIso m :=
      (MorphismProperty.IsStableUnderBaseChange.isomorphisms Scheme).of_isPullback hm.flip
        (show MorphismProperty.isomorphisms Scheme e.hom from inferInstance)
    have hmw : m ≫ (Stacks.Blowup.normalizedBlowUp Z hZfin (e.hom x) hz ≫ q) =
        Stacks.Blowup.normalizedBlowUp X hXfin x hx ≫ f := by
      rw [← Category.assoc, hm.w, Category.assoc, he]
    have hproper : IsProper (Stacks.Blowup.normalizedBlowUp X hXfin x hx ≫ f) :=
      isProper_of_normalizedBlowUpSeqDescent A hnagataB
        (NormalizedBlowUpSeqDescent.blowUp prev hXfin hYfin x hx y hy t hcart)
    exact ⟨_, _, hchain.blowUp hZfin (e.hom x) hz
      ((MorphismProperty.cancel_left_of_respectsIso (P := @IsProper) m _).mp (hmw ▸ hproper)),
      asIso m, hmw⟩

/-! ### Descending a resolution by normalized blowups -/

/-- Let `(A, 𝔪)` be a Noetherian local normal domain whose completion `A^` is a normal Nagata
ring. If `Spec A^` has a resolution of singularities by normalized blowups, then so does
`Spec A`. -/
@[ega "IV 7.9.6" "partial"]
theorem hasResolutionByNormalizedBlowUps_of_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hnormal : IsNormalRing (AdicCompletion (maximalIdeal A) A))
    (hnagata : IsNagataRing (AdicCompletion (maximalIdeal A) A))
    (hres : HasResolutionByNormalizedBlowUps
      (Spec (.of (AdicCompletion (maximalIdeal A) A)))) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) := by
  let : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  let : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  let : IsNormal (Spec (.of (AdicCompletion (maximalIdeal A) A))) :=
    isNormal_spec_of_isNormalRing hnormal
  have hNagataB : IsNagataScheme (Spec (.of (AdicCompletion (maximalIdeal A) A))) :=
    isNagataScheme_spec_of_isNagataRing _ hnagata
  let : IsLocallyNoetherian (Spec (.of (AdicCompletion (maximalIdeal A) A))) :=
    ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme _).mp hNagataB).1
  obtain ⟨hBfin, Z, g, hchain, hregZ⟩ := hres
  obtain ⟨W, gW, hpc, e, -⟩ := factorsAsNormalizedPointBlowups_of_normalizedBlowUpChain hchain
  have hseqW : NormalizedBlowUpSeq (Spec (.of (AdicCompletion (maximalIdeal A) A))) W gW :=
    normalizedBlowUpSeq_of_normalizedPointBlowupChain hpc
  obtain ⟨-, hWnoetherian, -, -⟩ := hseqW.properties hNagataB
  let : IsLocallyNoetherian W := hWnoetherian
  have hregW : IsRegular W := isRegular_of_iso e.symm hregZ
  obtain ⟨X, f, p, hdesc, hfproper⟩ :=
    exists_normalizedBlowUpSeqDescent_of_adicCompletion_unconditional A hnormal hseqW
  let : IsProper f := hfproper
  have hregX : IsRegular X := by
    rw [isRegular_pullback_completion_iff A X f]
    let : IsLocallyNoetherian (pullback f (specMapAdicCompletion A)) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f (specMapAdicCompletion A))
    exact isRegular_of_iso hdesc.isPullback.isoPullback.symm hregW
  let hAfin : ∀ U : (Spec (.of A)).Opens, IsCompact (U : Set (Spec (.of A))) →
      (irreducibleComponents U).Finite :=
    SemistableReduction.finite_irreducibleComponents_of_locallyNoetherian (Spec (.of A))
  obtain ⟨V, q, hchainA, d, -⟩ :=
    exists_normalizedBlowUpChain_of_normalizedBlowUpSeqDescent A hNagataB hAfin hdesc
  refine ⟨hAfin, V, q, hchainA, ?_⟩
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsLocallyNoetherian V := isLocallyNoetherian_of_isOpenImmersion d.inv
  exact isRegular_of_iso d.symm hregX

end AlgebraicGeometry

end
