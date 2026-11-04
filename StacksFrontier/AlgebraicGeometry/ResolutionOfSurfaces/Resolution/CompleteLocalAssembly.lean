module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpReduction
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CohomologyModelBridge
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.IrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionDominant
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ModificationCurve
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Assembling a resolution from resolutions of the singular local rings

Both branches of the source's proof of [Stacks, Tag 0BGN] end the same way: a normal modification
`X ⟶ Spec A` with finitely many singular points has been constructed, the spectrum of the local
ring of `X` at each singular point has been shown to have a resolution by normalized blowups, and
"by Lemma 0BFZ we can fit these normalized blowing ups into a corresponding sequence
`Z_n → … → Z_1 → X` and of course `Z_n` is regular too (look at the local rings)". This file
proves that last step, in the form the two branches consume.

## Main results

* `AlgebraicGeometry.HasResolutionByNormalizedBlowUps.of_iso`: a resolution by normalized blowups
  transports along an isomorphism of normal schemes.
* `AlgebraicGeometry.exists_isResolution_of_isModification_of_singularLocus`: a normal
  modification `X ⟶ Spec A` of dimension two with finitely many singular points, at each of which
  the spectrum of the local ring has a resolution by normalized blowups, gives a resolution of
  singularities of `Spec A`.

## Implementation notes

The globalization is `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_local`, which is
stated for the singular points of the normalization of `X`. For normal `X` the normalization is an
isomorphism, so the hypotheses at the singular points of `X` are moved to the normalization by
`AlgebraicGeometry.HasResolutionByNormalizedBlowUps.of_iso` applied to the spectra of the local
rings, which are isomorphic along the stalk maps of the normalization.

## References

* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
* [Stacks Project, Tag 0BFZ](https://stacks.math.columbia.edu/tag/0BFZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A chain of normalized blowups transports along an isomorphism of normal bases.** For an
isomorphism `e : S ≅ S'` of normal schemes, a chain of normalized blowups of `S` is, up to an
isomorphism of the total spaces commuting with `e`, a chain of normalized blowups of `S'`. Over a
normal base the normalization step is an isomorphism, and each normalized blowup transports along
an isomorphism of the scheme being blown up. -/
theorem NormalizedBlowUpChain.exists_of_iso {S S' : Scheme.{u}} [IsNormal S] [IsNormal S']
    (e : S ≅ S')
    {hS : ∀ U : S.Opens, IsCompact (U : Set S) → (irreducibleComponents U).Finite}
    (hS' : ∀ U : S'.Opens, IsCompact (U : Set S') → (irreducibleComponents U).Finite)
    {X : Scheme.{u}} {f : X ⟶ S} (hchain : NormalizedBlowUpChain S hS X f) :
    ∃ (Z : Scheme.{u}) (q : Z ⟶ S'), NormalizedBlowUpChain S' hS' Z q ∧
      ∃ d : X ≅ Z, d.hom ≫ q = f ≫ e.hom := by
  induction hchain with
  | normalization hproper =>
    have := Scheme.isIso_normalization_of_isNormal S hS
    have := Scheme.isIso_normalization_of_isNormal S' hS'
    refine ⟨_, _, NormalizedBlowUpChain.normalization inferInstance,
      asIso (Scheme.normalization S hS) ≪≫ e ≪≫ (asIso (Scheme.normalization S' hS')).symm, ?_⟩
    simp
  | @blowUp X f prev hX x hx hproper ih =>
    obtain ⟨Z, q, hchain, d, hd⟩ := ih
    have hZfin : ∀ U : Z.Opens, IsCompact (U : Set Z) → (irreducibleComponents U).Finite :=
      finite_irreducibleComponents_of_smooth d.inv hX
    have hz : IsClosed ({d.hom x} : Set Z) := by
      have hset : ({d.hom x} : Set Z) = d.inv ⁻¹' ({x} : Set X) := by
        ext z
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        exact ⟨fun hzx => by simp [hzx], fun hzx => by simp [← hzx]⟩
      rw [hset]
      exact hx.preimage d.inv.continuous
    obtain ⟨_, hideal⟩ :=
      vanishingIdeal_singleton_comap_of_isIso d.hom (d.hom x) hz x rfl
    obtain ⟨m, hm⟩ :=
      exists_isPullback_normalizedBlowUp_comap d.hom hZfin hX (d.hom x) hz x hx hideal
    have : IsIso m :=
      (MorphismProperty.IsStableUnderBaseChange.isomorphisms Scheme).of_isPullback hm.flip
        (show MorphismProperty.isomorphisms Scheme d.hom from inferInstance)
    have hmw : m ≫ (Stacks.Blowup.normalizedBlowUp Z hZfin (d.hom x) hz ≫ q) =
        (Stacks.Blowup.normalizedBlowUp X hX x hx ≫ f) ≫ e.hom := by
      rw [← Category.assoc, hm.w, Category.assoc, hd]
      simp only [Category.assoc]
    have hproper' : IsProper ((Stacks.Blowup.normalizedBlowUp X hX x hx ≫ f) ≫ e.hom) := by
      have := hproper
      infer_instance
    exact ⟨_, _, hchain.blowUp hZfin (d.hom x) hz
      ((MorphismProperty.cancel_left_of_respectsIso (P := @IsProper) m _).mp (hmw ▸ hproper')),
      asIso m, hmw⟩

/-- **A resolution by normalized blowups transports along an isomorphism of normal schemes.** -/
theorem HasResolutionByNormalizedBlowUps.of_iso {S S' : Scheme.{u}} [IsNormal S] [IsNormal S']
    [IsLocallyNoetherian S'] (e : S ≅ S') (h : HasResolutionByNormalizedBlowUps S) :
    HasResolutionByNormalizedBlowUps S' := by
  obtain ⟨hS, X, f, hchain, hreg⟩ := h
  have hS' : ∀ U : S'.Opens, IsCompact (U : Set S') → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_of_smooth e.inv hS
  obtain ⟨Z, q, hchainZ, d, -⟩ := hchain.exists_of_iso e hS'
  refine ⟨hS', Z, q, hchainZ, ?_⟩
  have : IsProper q := hchainZ.isProper
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian q
  exact isRegular_of_iso d.symm hreg

/-- **A modification preserves dimension.** A modification of a locally Noetherian integral
scheme has the same dimension as its target: at most, by the dimension inequality with
transcendence degree zero, the function fields being equal; at least, because a proper surjective
morphism lifts specializations. -/
@[sga "6 X 1.4" "(iv), special case"]
theorem topologicalKrullDim_eq_of_isModification {X Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) (hf : IsModification f) :
    topologicalKrullDim X = topologicalKrullDim Y := by
  have : IsIntegral X := hf.source_isIntegral
  have : IsProper f := hf.isProper
  have : IsDominant f := hf.isBirational.isDominant
  refine le_antisymm ?_ ?_
  · let := (functionFieldMap f).toAlgebra
    have : Algebra.IsAlgebraic Y.functionField X.functionField := ⟨fun x => by
      obtain ⟨a, rfl⟩ := hf.isBirational.surjective_functionFieldMap x
      exact isAlgebraic_algebraMap a⟩
    simpa only [trdeg_eq_zero, map_zero, WithBot.coe_zero, add_zero] using
      topologicalKrullDim_le_add_trdeg f
  · exact Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap f
      f.continuous (surjective_of_isProper_of_isBirational f hf.isBirational)
      (Or.inl f.isClosedMap.specializingMap)

/-- A point lies in the singular locus exactly when its image under an isomorphism does: the
stalk maps of an isomorphism are isomorphisms of local rings. -/
theorem mem_singularLocus_iff_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (x : X) :
    e x ∈ singularLocus Y ↔ x ∈ singularLocus X := by
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · exact IsRegularLocalRing.of_ringEquiv (asIso (e.stalkMap x)).commRingCatIsoToRingEquiv
  · exact IsRegularLocalRing.of_ringEquiv (asIso (e.stalkMap x)).commRingCatIsoToRingEquiv.symm

/-- **A normal modification with finitely many singular points, each of whose local rings has a
resolution by normalized blowups, gives a resolution of singularities.** Let `f : X ⟶ Spec A` be
a modification of the spectrum of a two-dimensional Noetherian domain with `X` normal and with
finitely many singular points, and suppose the spectrum of the local ring of `X` at each singular
point has a resolution by normalized blowups. Then `Spec A` has a resolution of singularities.

The local resolutions assemble into a resolution of `X` by normalized blowups
(`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_local`, through the isomorphism of `X`
with its normalization), which is a resolution of singularities of `X`
(`AlgebraicGeometry.exists_resolution_of_hasResolutionByNormalizedBlowUps`); composed with the
modification `f` it is a resolution of `Spec A`. -/
theorem exists_isResolution_of_isModification_of_singularLocus (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsDomain A] {X : Scheme.{u}} [IsNormal X] (f : X ⟶ Spec (.of A))
    (hf : IsModification f) (hdimA : ringKrullDim A = 2)
    (hsing : (singularLocus X).Finite)
    (hloc : ∀ x ∈ singularLocus X,
      HasResolutionByNormalizedBlowUps (Spec (.of (X.presheaf.stalk x)))) :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ Spec (.of A)), IsResolution g := by
  have : IsIntegral X := hf.source_isIntegral
  have : IsProper f := hf.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  have hX := finite_irreducibleComponents_of_isCompact X
  have hdim : topologicalKrullDim X = 2 := by
    rw [topologicalKrullDim_eq_of_isModification f hf, ← hdimA]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A
  have hiso := Scheme.isIso_normalization_of_isNormal X hX
  set ν := Scheme.normalization X hX
  have hsingN : (singularLocus (X.normalizationScheme hX)).Finite := by
    rw [show singularLocus (X.normalizationScheme hX) = ν ⁻¹' singularLocus X from
      Set.ext fun y => (mem_singularLocus_iff_of_isIso ν y).symm]
    exact hsing.preimage ν.isEmbedding.injective.injOn
  have hlocN : ∀ y : X.normalizationScheme hX, y ∈ singularLocus (X.normalizationScheme hX) →
      HasResolutionByNormalizedBlowUps
        (Spec (.of ((X.normalizationScheme hX).presheaf.stalk y))) := by
    intro y hy
    have hx := (mem_singularLocus_iff_of_isIso ν y).mpr hy
    have : IsNormal (X.normalizationScheme hX) := Scheme.isNormal_normalizationScheme X hX
    have : IsLocallyNoetherian (X.normalizationScheme hX) :=
      LocallyOfFiniteType.isLocallyNoetherian ν
    have : Flat (X.fromSpecStalk (ν y)) := flat_fromSpecStalk X (ν y)
    have : Flat ((X.normalizationScheme hX).fromSpecStalk y) :=
      flat_fromSpecStalk (X.normalizationScheme hX) y
    have hn1 : IsNormal (Spec (.of (X.presheaf.stalk (ν y)))) :=
      isNormal_of_flat_preimmersion (X.fromSpecStalk (ν y))
    have : IsNormal (Spec (.of ((X.normalizationScheme hX).presheaf.stalk y))) :=
      isNormal_of_flat_preimmersion ((X.normalizationScheme hX).fromSpecStalk y)
    have : IsLocallyNoetherian (Spec (.of ((X.normalizationScheme hX).presheaf.stalk y))) :=
      isLocallyNoetherian_Spec.mpr inferInstance
    exact @HasResolutionByNormalizedBlowUps.of_iso _ _ hn1 _ _
      (Scheme.Spec.mapIso (asIso (ν.stalkMap y)).op).symm (hloc (ν y) hx)
  have hres := hasResolutionByNormalizedBlowUps_of_local X hX hdim inferInstance hsingN hlocN
  obtain ⟨Z, g, hg⟩ := exists_resolution_of_hasResolutionByNormalizedBlowUps X hdim hres
  exact ⟨Z, g ≫ f, hg.isModification.comp hf, hg.source_isRegular⟩

/-- **A rational singularity admits reduction to rational singularities**, with bound zero: the
first cohomology of the structure sheaf of every normal modification vanishes, so has length
zero. -/
theorem isReductionToRationalSingularitiesPossible_of_definesRationalSingularity (A : Type u)
    [CommRing A] [IsDomain A] (h : DefinesRationalSingularity A) :
    IsReductionToRationalSingularitiesPossible A := by
  refine ⟨0, fun X _ f hf => ?_⟩
  have := (definesRationalSingularity_iff_subsingleton_firstCohomologyAsBaseModule A).mp h X f hf
  rw [Module.length_eq_zero_iff.mpr this]
  simp

end AlgebraicGeometry
