module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalence
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ResolutionByNormalizedBlowUps
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Nagata.CompleteLocalRing

/-!
# Reducing a resolution by normalized blowups to the complete local case

Let `(A, 𝔪)` be a two-dimensional Noetherian local normal domain whose spectrum has a
resolution of singularities. This file transports that datum to the completion `A^` and
discharges, from the resolution alone, the two side conditions under which a resolution by
normalized blowups descends from `Spec A^` to `Spec A`:

* `A^` is a normal ring, because a resolution of `Spec A` is an alteration by a regular scheme
  and so makes the completion of the integral closure of `A` normal;
* `A^` is a Nagata ring, being Noetherian, local and complete.

Together with the fact that a resolution of `Spec A` base-changes to a resolution of `Spec A^`,
this reduces the statement that a two-dimensional Noetherian local normal domain with a
resolution of singularities has a resolution by normalized blowups to its own complete case.

## Main results

* `AlgebraicGeometry.isNormalRing_adicCompletion_of_regular_alteration`: the completion of a
  Noetherian local normal domain carrying an alteration by a regular scheme is normal.
* `AlgebraicGeometry.isResolution_pullback_specMapAdicCompletion`: a resolution of singularities
  of `Spec A` pulls back to one of `Spec A^`.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isResolution_of_adicCompletion`: if
  `Spec A` has a resolution of singularities and `Spec A^` has a resolution by normalized
  blowups, then so does `Spec A`.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isResolution_of_complete`: the
  reduction to the complete case.

## Implementation notes

Normality of `A^` is the composite of two results about an alteration `X ⟶ Spec A` with
`X` regular: the integral closure `B` of `A` in `Frac(A)` is a finite `A`-module and `B^` is
normal ([Stacks, Tag 0BGI], parts (2) and (3)); applying [Stacks, Tag 0BGH] to the pair of
finite `A`-algebras `A ⊆ B` then gives normality of `A^`. Because `A` is already integrally
closed, `B` could equally be replaced by `A` itself, but nothing is gained: the hypothesis of
Tag 0BGH is about the completion of the larger ring, which is the content of Tag 0BGI.

That the base change of a resolution along `Spec A^ ⟶ Spec A` is a resolution needs its source
to be integral, and that is not formal: the base change is reduced because it is regular, and
irreducible because the morphism from the completion is flat, hence generalizing, so the
preimage of the dense open over which the resolution is an isomorphism is dense in the base
change and irreducible there. Regularity itself is the proper case of [Stacks, Tag 0BG6].

### What the complete case still needs

The complete case is carried as a hypothesis, and that hypothesis is where all of the remaining
mathematics of [Stacks, Tag 0BGM] lives. Over a complete base one dominates the given resolution
by a sequence of normalized blowups ([Stacks, Tag 0BBT]), observes that the resulting normal
surface has finitely many singular points, all of them rational singularities ([Stacks, Tags
0B4Q and 0BG0]), and then resolves those points in two further passes. No attribute for Tag
0BGM is carried here.

Two inputs for those passes are available only as their own tagged statements:
[Stacks, Tag 0BBV], which blows up the singular closed points of a rational surface singularity
until the dualizing module is invertible, and [Stacks, Tag 0BGE], which resolves a rational
double point. Of the eight tags the source's proof of Tag 0BBV cites, only [Stacks, Tag 0B4Z] is
likewise missing, and it is carried as a hypothesis where it is needed, as
`AlgebraicGeometry.BlowUpMaximalIdealIsNormal`; the details are recorded in the companion file
`Resolution/ResolutionByNormalizedBlowUps.lean`.

The sufficiency half of [Stacks, Tag 0BFZ], and the base-change functor of [Stacks, Tag 0BFU]
being an equivalence ([Stacks, Tag 0BFV]), are not needed, as for the globalization in
`Resolution/LipmanEquivalencePort.lean`: the route out of the local resolutions is a direct
step-by-step lift, and `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_local` takes it
without either. What remains true is that of Tag 0BFZ only necessity is available, as
`AlgebraicGeometry.FinitePresentationAwayPointsSituation`'s
`factorsAsNormalizedPointBlowups_of_corresponds` records, and of Tag 0BFV only faithfulness —
but Tag 0BGM does not need more.

The bookkeeping of the two passes is in place: the chain over `Spec A` reaching the dominating
stage composes with a chain over that stage by
`AlgebraicGeometry.exists_normalizedBlowUpChain_comp`, the stage is normal by
`AlgebraicGeometry.NormalizedBlowUpChain.isNormal`, it has finitely many singular points by
`AlgebraicGeometry.finite_singularLocus_of_locallyOfFiniteType_over_completeLocalRing` — the base
being complete exactly because of the reduction this file performs — and the local resolutions
assemble by `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_local`. Besides Tags 0BBV and
0BGE, what is left is the rationality of the singular local rings of the dominating stage, which
is Tag 0B4Q together with Tag 0BG0 in its local-ring form,
`AlgebraicGeometry.definesRationalSingularity_stalk_of_isModification`.

## References

* [Stacks Project, Tag 0BGM](https://stacks.math.columbia.edu/tag/0BGM)
* [Stacks Project, Tag 0BGH](https://stacks.math.columbia.edu/tag/0BGH)
* [Stacks Project, Tag 0BGI](https://stacks.math.columbia.edu/tag/0BGI)
* [Stacks Project, Tag 0BG6](https://stacks.math.columbia.edu/tag/0BG6)
* [Stacks Project, Tag 0BAJ](https://stacks.math.columbia.edu/tag/0BAJ)
* [Stacks Project, Tag 032W](https://stacks.math.columbia.edu/tag/032W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### Normality of the completion -/

/-- The completion of a Noetherian local normal domain carrying an alteration by a regular
scheme is a normal ring. The integral closure `B` of `A` in `Frac(A)` is a finite `A`-module
with normal completion by [Stacks, Tag 0BGI], and `A ⊆ B` is a pair of finite `A`-algebras with
`A` normal, so [Stacks, Tag 0BGH] makes the completion of `A` normal. -/
theorem isNormalRing_adicCompletion_of_regular_alteration
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsAlteration f) (hX : IsRegular X) :
    IsNormalRing (AdicCompletion (maximalIdeal A) A) := by
  have hinj : Function.Injective (algebraMap A ↥(integralClosure A (FractionRing A))) :=
    fun a b hab => IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val hab)
  let : Module.Finite A ↥(integralClosure A (FractionRing A)) :=
    module_finite_integralClosure_of_regular_alteration A X f hf hX
  have h := isNormalRing_adicCompletion_of_finite_injective A A
    ↥(integralClosure A (FractionRing A)) hinj (IsNormalRing.of_isIntegrallyClosed A)
    (isNormalRing_adicCompletion_integralClosure_of_regular_alteration A X f hf hX)
  rwa [show (maximalIdeal A).map (algebraMap A A) = maximalIdeal A by simp] at h

/-- The completion of a Noetherian local normal domain whose spectrum has a resolution of
singularities is a normal ring: a resolution of singularities is an alteration. -/
theorem isNormalRing_adicCompletion_of_isResolution
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsResolution f) :
    IsNormalRing (AdicCompletion (maximalIdeal A) A) :=
  isNormalRing_adicCompletion_of_regular_alteration A f (isAlteration_of_isResolution hf) hf.2

/-! ### Base change of a resolution to the completion -/

/-- Base change takes a morphism which is an isomorphism over an open of the target to one which
is an isomorphism over the preimage of that open. -/
private theorem isIso_morphismRestrict_pullback_snd_preimage {X S T : Scheme.{u}}
    (f : X ⟶ S) (k : T ⟶ S) (U : S.Opens) (hU : IsIso (f ∣_ U)) :
    IsIso (pullback.snd f k ∣_ (k ⁻¹ᵁ U)) := by
  have h := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f k)
    (US := U) (UT := k ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U) le_rfl le_rfl
    (UY := pullback.snd f k ⁻¹ᵁ (k ⁻¹ᵁ U)) (by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition,
        inf_idem])
  have hU' : IsIso (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using
    (MorphismProperty.isomorphisms Scheme).of_isPullback h hU'

/-- The preimage of an open containing the generic point of an integral scheme under a
generalizing map is dense: every point of the source has a generalization lying over the generic
point, and that generalization lies in the preimage. -/
private theorem dense_preimage_of_generalizingMap {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) (hf : GeneralizingMap f) (U : Y.Opens)
    (hη : genericPoint Y ∈ U) : Dense (f ⁻¹' (U : Set Y)) := by
  intro x
  obtain ⟨z, hzx, hz⟩ := hf (genericPoint_specializes (f x))
  exact closure_mono (s := {z})
    (Set.singleton_subset_iff.mpr (show f z ∈ U by simpa [hz] using hη))
    (specializes_iff_mem_closure.mp hzx)

/-- The generic point of an integral scheme lies in every nonempty open. -/
private theorem genericPoint_mem_of_nonempty_toScheme {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) (hU : Nonempty U.toScheme) : genericPoint X ∈ U := by
  obtain ⟨v⟩ := hU
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨v.1, trivial, v.2⟩

/-- The preimage under a surjective morphism of an open containing a point is nonempty. -/
private theorem nonempty_preimage_of_surjective {S T : Scheme.{u}} (k : T ⟶ S) [Surjective k]
    (U : S.Opens) {s : S} (hs : s ∈ U) : Nonempty (k ⁻¹ᵁ U).toScheme := by
  obtain ⟨t, rfl⟩ := k.surjective s
  exact ⟨⟨t, hs⟩⟩

/-- A reduced base change of a birational morphism of integral schemes along a faithfully flat
morphism is integral. The open over which the base change is an isomorphism is integral and, the
base change of the flat morphism being generalizing, dense; so the whole space is
irreducible. -/
private theorem isIntegral_pullback_of_flat_of_isIso_morphismRestrict
    {X S T : Scheme.{u}} [IsIntegral X] [IsIntegral S] [IsIntegral T]
    (f : X ⟶ S) (k : T ⟶ S) [Flat k] [Surjective k]
    [IsReduced (pullback f k)] (U : S.Opens) (hη : genericPoint S ∈ U)
    (hU : IsIso (f ∣_ U)) : IsIntegral (pullback f k) := by
  let V := f ⁻¹ᵁ U
  let W := k ⁻¹ᵁ U
  have : Nonempty W.toScheme := nonempty_preimage_of_surjective k U hη
  let : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  let : IsIso (pullback.snd f k ∣_ W) := isIso_morphismRestrict_pullback_snd_preimage f k U hU
  let O := pullback.snd f k ⁻¹ᵁ W
  let : IsIntegral O.toScheme := IsIntegral.of_isIso (inv (pullback.snd f k ∣_ W))
  have hηV : genericPoint X ∈ V :=
    genericPoint_mem_of_nonempty_toScheme V ⟨inv (f ∣_ U) ⟨genericPoint S, hη⟩⟩
  have hdense : Dense (O : Set ↑(pullback f k)) := by
    have heq : O = pullback.fst f k ⁻¹ᵁ V := by
      change pullback.snd f k ⁻¹ᵁ (k ⁻¹ᵁ U) = pullback.fst f k ⁻¹ᵁ (f ⁻¹ᵁ U)
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
    rw [heq]
    exact dense_preimage_of_generalizingMap (pullback.fst f k)
      (Flat.generalizingMap _) V hηV
  have hirr : IsIrreducible (O : Set ↑(pullback f k)) :=
    isIrreducible_iff_irreducibleSpace.mpr (inferInstanceAs (IrreducibleSpace O.toScheme))
  let : IrreducibleSpace ↑(pullback f k) := (irreducibleSpace_def _).mpr (by
    simpa only [hdense.closure_eq, Set.top_eq_univ] using hirr.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- A resolution of singularities of the spectrum of a Noetherian local domain base-changes to a
resolution of singularities of the spectrum of its completion. -/
theorem isResolution_pullback_specMapAdicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    [IsDomain (AdicCompletion (maximalIdeal A) A)]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsResolution f) :
    IsResolution (pullback.snd f (specMapAdicCompletion A)) := by
  let k := specMapAdicCompletion A
  let : IsProper f := hf.1.2.1
  let : IsIntegral X := hf.1.2.2
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  let : Finite (irreducibleComponents X) := finite_irreducibleComponents_of_isNoetherian
  let : Finite (irreducibleComponents (Spec (.of A))) :=
    finite_irreducibleComponents_of_isNoetherian
  have hreg : IsRegular (pullback f k) :=
    (isRegular_pullback_completion_iff A X f).mp hf.2
  have : IsReduced (pullback f k) := by
    have hstalk := ((isRegular_tfae (pullback f k)).out 1 2).mp hreg
    have (x : (pullback f k : Scheme)) : _root_.IsReduced ((pullback f k).presheaf.stalk x) := by
      let : IsRegularLocalRing ((pullback f k).presheaf.stalk x) := hstalk.2 x
      let : IsDomain ((pullback f k).presheaf.stalk x) :=
        IsRegularLocalRing.isDomain ((pullback f k).presheaf.stalk x)
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨_, _⟩ : Flat k ∧ Surjective k := (flat_and_surjective_SpecMap_iff _).mpr (by
    rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom)
  obtain ⟨U, hdense, hiso⟩ := exists_dense_open_isIso_morphismRestrict_of_isBirational
    f hf.1.1 (Or.inr inferInstance) (Or.inl ⟨inferInstance, inferInstance⟩)
  have hη : genericPoint (Spec (.of A)) ∈ U :=
    ((genericPoint_spec (Spec (.of A))).mem_open_set_iff U.isOpen).mpr
      (by simpa using hdense.nonempty)
  let : IsIntegral (pullback f k) :=
    isIntegral_pullback_of_flat_of_isIso_morphismRestrict f k U hη hiso
  let W : (Spec (.of (AdicCompletion (maximalIdeal A) A))).Opens := k ⁻¹ᵁ U
  have hW : Nonempty W.toScheme := nonempty_preimage_of_surjective k U hη
  have hisoW : IsIso (pullback.snd f k ∣_ W) :=
    isIso_morphismRestrict_pullback_snd_preimage f k U hiso
  refine ⟨⟨?_, inferInstance, inferInstance⟩, hreg⟩
  refine isBirational_of_isIso_morphismRestrict (pullback.snd f k) W hisoW ?_ ?_
  · intro x hx
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    exact genericPoint_mem_of_nonempty_toScheme _ ⟨inv (pullback.snd f k ∣_ W) hW.some⟩
  · intro y hy
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hy
    subst hy
    exact genericPoint_mem_of_nonempty_toScheme W hW

/-! ### The reduction to the complete case -/

/-- If `Spec A` has a resolution of singularities and the spectrum of the completion `A^` has a
resolution by normalized blowups, then so does `Spec A`. The two side conditions of the descent
along the completion are supplied by the resolution: `A^` is normal by [Stacks, Tag 0BGI] and
Nagata by [Stacks, Tag 032W]. -/
theorem hasResolutionByNormalizedBlowUps_of_isResolution_of_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsResolution f)
    (hres : HasResolutionByNormalizedBlowUps
      (Spec (.of (AdicCompletion (maximalIdeal A) A)))) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) :=
  hasResolutionByNormalizedBlowUps_of_adicCompletion A
    (isNormalRing_adicCompletion_of_isResolution A f hf)
    IsNagataRing.of_isPrecomplete_maximalIdeal hres

/-- **The resolution by normalized blowups of a two-dimensional Noetherian local normal domain
reduces to the complete case.** If every two-dimensional complete Noetherian local normal domain
whose spectrum has a resolution of singularities has a resolution by normalized blowups, then so
does every two-dimensional Noetherian local normal domain whose spectrum has a resolution of
singularities. The completion `A^` is again a two-dimensional Noetherian local normal domain,
its spectrum inherits a resolution of singularities by base change, and a resolution by
normalized blowups of `Spec A^` descends to `Spec A`. -/
theorem hasResolutionByNormalizedBlowUps_of_isResolution_of_complete
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hdim : ringKrullDim A = 2)
    (hres : ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f)
    (hcomplete : ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
      [IsNormalDomain B] [IsAdicComplete (maximalIdeal B) B], ringKrullDim B = 2 →
      (∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of B)), IsResolution g) →
      HasResolutionByNormalizedBlowUps (Spec (.of B))) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) := by
  obtain ⟨X, f, hf⟩ := hres
  obtain ⟨hdomB, hicB⟩ :=
    (isNormalRing_adicCompletion_of_isResolution A f hf).of_isLocalRing
  let : IsNormalDomain (AdicCompletion (maximalIdeal A) A) := ⟨hdomB, hicB⟩
  exact hasResolutionByNormalizedBlowUps_of_isResolution_of_adicCompletion A f hf
    (hcomplete _ (by rwa [← _root_.ringKrullDim_adicCompletion_maximalIdeal])
      ⟨_, _, isResolution_pullback_specMapAdicCompletion A f hf⟩)

end AlgebraicGeometry

end
