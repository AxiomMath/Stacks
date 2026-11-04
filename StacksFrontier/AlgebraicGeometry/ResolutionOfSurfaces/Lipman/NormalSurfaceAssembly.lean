module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.CompleteLocalAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ExistenceByNormalizedBlowUps
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.FunctionField
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ModificationCurve
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian

/-!
# Assembling resolutions of the local rings of a normal surface

Every branch of the proofs of [Stacks, Tags 0BGM and 0BGN] ends the same way: a normal surface
with finitely many singular points, at each of which the spectrum of the local ring has a
resolution by normalized blowups, has one itself. This file records that step for a normal
scheme directly, together with two pieces of bookkeeping used alongside it.

## Main results

* `Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain.mono`: a chain of normalized blowups
  with centres over `T` has its centres over any larger set.
* `AlgebraicGeometry.isFractionRing_stalk_of_isBirational`: along a birational morphism
  `h : Z ⟶ X` of integral schemes, the function field of `Z` is a fraction field of the local
  ring of `X` at the image of any point, through the stalk map.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isNormal_of_singularLocus`: a normal
  Noetherian integral scheme of dimension two with finitely many singular points, the spectra of
  whose local rings there have resolutions by normalized blowups, has a resolution by normalized
  blowups.
* `AlgebraicGeometry.isModification_of_normalizedBlowUpSeq`: a sequence of normalized blowups
  over the spectrum of a two-dimensional Noetherian local normal Nagata domain is a modification.

## References

* [Stacks Project, Tag 0BGM](https://stacks.math.columbia.edu/tag/0BGM)
* [Stacks Project, Tag 0BGN](https://stacks.math.columbia.edu/tag/0BGN)
* [Stacks Project, Tag 0BFZ](https://stacks.math.columbia.edu/tag/0BFZ)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace Stacks.ResolutionOfSurfaces

/-- A chain of normalized blowups whose centres lie over `T` has its centres over any larger
set. -/
theorem NormalizedPointBlowupChain.mono {X : AlgebraicGeometry.Scheme.{u}} {T T' : Set X}
    (hT : T ⊆ T') {Y : AlgebraicGeometry.Scheme.{u}} {f : Y ⟶ X}
    (h : NormalizedPointBlowupChain X T Y f) : NormalizedPointBlowupChain X T' Y f := by
  induction h with
  | refl => exact .refl
  | step _ hW w hw hwT ih => exact ih.step hW w hw (hT hwT)

end Stacks.ResolutionOfSurfaces

namespace AlgebraicGeometry

/-- The algebra structure `𝒪_{X, h(z)} ⟶ K(Z)` of a morphism `h : Z ⟶ X` with `Z` irreducible:
the stalk map of `h` followed by the inclusion of `𝒪_{Z, z}` into the function field. -/
@[instance_reducible]
noncomputable def stalkFunctionFieldAlgebraOfHom {X Z : Scheme.{u}} [IrreducibleSpace Z]
    (h : Z ⟶ X) (z : Z) : Algebra (X.presheaf.stalk (h.base z)) Z.functionField :=
  ((algebraMap (Z.presheaf.stalk z) Z.functionField).comp (h.stalkMap z).hom).toAlgebra

/-- The stalk map followed by the inclusion into the function field of the source is the
inclusion into the function field of the target followed by the function field map. -/
theorem algebraMap_stalkMap_eq_functionFieldMap {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (h : Z ⟶ X) [IsDominant h] (z : Z) (a : X.presheaf.stalk (h.base z)) :
    algebraMap (Z.presheaf.stalk z) Z.functionField (h.stalkMap z a) =
      (Scheme.Hom.functionFieldMap h)
        (algebraMap (X.presheaf.stalk (h.base z)) X.functionField a) := by
  obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have key : X.presheaf.germ U (h.base z) hU ≫ h.stalkMap z ≫
      Z.presheaf.stalkSpecializes ((genericPoint_spec Z).specializes trivial) =
      X.presheaf.germ U (h.base z) hU ≫
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) ≫
          Scheme.Hom.functionFieldMap h := by
    have e1 : h.stalkMap z ≫
        Z.presheaf.stalkSpecializes ((genericPoint_spec Z).specializes trivial) =
        X.presheaf.stalkSpecializes (h.base.hom.map_specializes
          ((genericPoint_spec Z).specializes trivial)) ≫ h.stalkMap (genericPoint Z) :=
      (Scheme.Hom.stalkSpecializes_stalkMap h _ _ _).symm
    rw [e1, TopCat.Presheaf.germ_stalkSpecializes_assoc,
      TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.functionFieldMap,
      TopCat.Presheaf.germ_stalkSpecializes_assoc]
  exact congr($key s)

/-- **Along a birational morphism `h : Z ⟶ X` of integral schemes, the function field of `Z` is
a fraction field of the local ring of `X` at `h(z)`**, through the stalk map at `z`. -/
theorem isFractionRing_stalk_of_isBirational {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (h : Z ⟶ X) [IsDominant h] (hh : IsBirational h) (z : Z) :
    letI := stalkFunctionFieldAlgebraOfHom h z
    IsFractionRing (X.presheaf.stalk (h.base z)) Z.functionField := by
  let := stalkFunctionFieldAlgebraOfHom h z
  have hfeq : (Scheme.Hom.functionFieldMap h).hom = functionFieldMap h := by
    simp [Scheme.Hom.functionFieldMap, functionFieldMap, TopCat.Presheaf.stalkCongr_hom]
  let e : X.functionField ≃+* Z.functionField :=
    RingEquiv.ofBijective (Scheme.Hom.functionFieldMap h).hom
      ⟨(Scheme.Hom.functionFieldMap h).hom.injective,
        hfeq ▸ hh.surjective_functionFieldMap⟩
  convert (IsLocalization.isLocalization_iff_of_ringEquiv (S := X.functionField)
    (nonZeroDivisors (X.presheaf.stalk (h.base z))) e).mp inferInstance using 1
  exact Algebra.algebra_ext _ _ fun a => algebraMap_stalkMap_eq_functionFieldMap h z a

/-- **A normal Noetherian integral scheme of dimension two with finitely many singular points,
the spectrum of whose local ring at each of them has a resolution by normalized blowups, has a
resolution by normalized blowups.** The local resolutions globalize over the normalization of
`X` (`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_local`), which is isomorphic to
`X`. -/
theorem hasResolutionByNormalizedBlowUps_of_isNormal_of_singularLocus (X : Scheme.{u})
    [IsIntegral X] [IsNoetherian X] [IsNormal X] (hdim : topologicalKrullDim X = 2)
    (hsing : (singularLocus X).Finite)
    (hloc : ∀ x ∈ singularLocus X,
      HasResolutionByNormalizedBlowUps (Spec (.of (X.presheaf.stalk x)))) :
    HasResolutionByNormalizedBlowUps X := by
  have hX := finite_irreducibleComponents_of_isCompact X
  set ν := Scheme.normalization X hX
  have : IsIso ν := (Scheme.isIso_normalization_iff_isNormal X hX).2 inferInstance
  have hsingN : (singularLocus (X.normalizationScheme hX)).Finite := by
    rw [show singularLocus (X.normalizationScheme hX) = ν ⁻¹' singularLocus X from
      Set.ext fun y => (mem_singularLocus_iff_of_isIso ν y).symm]
    exact hsing.preimage ν.isEmbedding.injective.injOn
  have hlocN : ∀ y : X.normalizationScheme hX, y ∈ singularLocus (X.normalizationScheme hX) →
      HasResolutionByNormalizedBlowUps
        (Spec (.of ((X.normalizationScheme hX).presheaf.stalk y))) := by
    intro y hy
    have : IsNormal (X.normalizationScheme hX) := Scheme.isNormal_normalizationScheme X hX
    have : IsLocallyNoetherian (X.normalizationScheme hX) :=
      LocallyOfFiniteType.isLocallyNoetherian ν
    have hnorm : ∀ (S : Scheme.{u}) [IsNormal S] (s : S),
        IsNormal (Spec (.of (S.presheaf.stalk s))) := fun S _ s => by
      have : Flat (S.fromSpecStalk s) := flat_fromSpecStalk S s
      exact isNormal_of_flat_preimmersion (S.fromSpecStalk s)
    have hn1 := hnorm X (ν y)
    have := hnorm (X.normalizationScheme hX) y
    have : IsLocallyNoetherian (Spec (.of ((X.normalizationScheme hX).presheaf.stalk y))) :=
      isLocallyNoetherian_Spec.mpr inferInstance
    exact @HasResolutionByNormalizedBlowUps.of_iso _ _ hn1 _ _
      (Scheme.Spec.mapIso (asIso (ν.stalkMap y)).op).symm
      (hloc (ν y) ((mem_singularLocus_iff_of_isIso ν y).mpr hy))
  exact hasResolutionByNormalizedBlowUps_of_local X hX hdim inferInstance hsingN hlocN

/-- **A sequence of normalized blowups over the spectrum of a two-dimensional Noetherian local
normal Nagata domain is a modification**, and its source is normal, Noetherian and of
dimension two. -/
theorem isModification_of_normalizedBlowUpSeq (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNormalDomain A] (hN : IsNagataRing A) (hdim : ringKrullDim A = 2) {Y : Scheme.{u}}
    {f : Y ⟶ Spec (.of A)} (hseq : NormalizedBlowUpSeq (Spec (.of A)) Y f) :
    IsModification f ∧ IsNormal Y ∧ IsNoetherian Y ∧ topologicalKrullDim Y = 2 := by
  have : IsNoetherianRing A := hN.1
  have : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have hNagata : IsNagataScheme (Spec (.of A)) := isNagataScheme_spec_of_isNagataRing A hN
  have hY0 := finite_irreducibleComponents_of_isCompact (Spec (.of A))
  have hdimS : topologicalKrullDim (Spec (.of A)) = 2 := by
    show topologicalKrullDim (PrimeSpectrum A) = 2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim]
  obtain ⟨-, hYnoeth, hYnormal, hfproper⟩ := hseq.properties hNagata
  obtain ⟨W, g, e, hchain, he⟩ :=
    exists_normalizedBlowUpChain_of_normalizedBlowUpSeq hNagata hY0 hseq
  have hg : IsModification g := isModification_of_normalizedBlowUpChain hdimS hchain
  have hf : IsModification f := by
    rw [← he]
    have : IsIntegral W := hg.source_isIntegral
    have : IsProper g := hg.isProper
    exact ⟨(isBirational_of_iso e).comp hg.1, inferInstance, IsIntegral.of_isIso e.inv⟩
  have : IsProper f := hf.isProper
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian Y := hYnoeth
  have : IsIntegral Y := hf.source_isIntegral
  refine ⟨hf, hYnormal, {}, ?_⟩
  rw [topologicalKrullDim_eq_of_isModification f hf, hdimS]

end AlgebraicGeometry

end
