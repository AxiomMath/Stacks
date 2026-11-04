module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.BlowUpIsProjective
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ExcellentLocalResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Resolutions by normalized blowups are projective

Over an affine Nagata scheme `Y`, the composite `X ⟶ Y` of a finite sequence of normalized
blowups at closed points, starting with the normalization of `Y`
(`AlgebraicGeometry.NormalizedBlowUpChain`, [Stacks, Tag 0BGL]), is H-projective: every stage
carries an ample invertible module since it is H-projective over the affine `Y`; over such a
stage the blowup of a closed point is projective ([Stacks, Tag 02NS],
`Stacks.Blowup.isProjective_blowUpToBase`), hence H-projective ([Stacks, Tag 087S]), and the
normalization is finite, hence H-projective; and H-projective morphisms compose
([Stacks, Tag 01WE]). This is the projectivity of the resolution used in the proof of
[Stacks, Tag 0EA3] ("`W ⟶ Spec(𝒪_{X, x})` is projective (as a sequence of normalized blowing
ups)").

## Main results

* `AlgebraicGeometry.NormalizedBlowUpChain.isProjectiveMorphism`
* `AlgebraicGeometry.exists_isResolution_isProjectiveMorphism_of_isExcellent`: an excellent
  normal local domain of dimension two has an H-projective resolution of singularities.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Every stage of a chain of normalized blowups over an affine Nagata scheme is Nagata, and
H-projective over the base.** -/
theorem NormalizedBlowUpChain.isNagataScheme_and_isProjectiveMorphism {Y : Scheme.{u}}
    [IsAffine Y] (hNagata : IsNagataScheme Y)
    {hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite}
    {X : Scheme.{u}} {f : X ⟶ Y} (hchain : NormalizedBlowUpChain Y hY X f) :
    IsNagataScheme X ∧ IsProjectiveMorphism f := by
  have hM := Stacks.Ample.isAmple_unitModule_of_isAffine Y
  induction hchain with
  | normalization hproper =>
    have : IsFinite (Scheme.normalization Y hY) := Scheme.isFinite_normalization hNagata hY
    exact ⟨isNagataScheme_of_locallyOfFiniteType (Scheme.normalization Y hY) hNagata,
      isProjectiveMorphism_of_isFinite _ _ hM⟩
  | blowUp prev hX x hx hproper ih =>
    obtain ⟨hNagataX, hP⟩ := ih
    have : IsLocallyNoetherian _ :=
      ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme _).mp hNagataX).1
    obtain ⟨L, hLinv, hLample⟩ := exists_isAmple_of_isProjectiveMorphism _ _ hM hP
    have := hLinv
    set I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds _)
    have hblow : IsProjectiveMorphism (blowUpToBase I) :=
      isProjectiveMorphism_of_isQuasiProjective _ L hLample
        (Stacks.Blowup.isQuasiProjective_blowUpToBase I (isFiniteType_of_isLocallyNoetherian I))
    obtain ⟨N, hNinv, hNample⟩ := exists_isAmple_of_isProjectiveMorphism _ L hLample hblow
    have := hNinv
    have hNagataBlow : IsNagataScheme (AlgebraicGeometry.blowUp I) :=
      isNagataScheme_of_locallyOfFiniteType (blowUpToBase I) hNagataX
    have hfin := Stacks.Blowup.finite_irreducibleComponents_blowUp I hX
    have : IsFinite (Scheme.normalization (AlgebraicGeometry.blowUp I) hfin) :=
      Scheme.isFinite_normalization hNagataBlow hfin
    exact ⟨isNagataScheme_of_locallyOfFiniteType
        (Scheme.normalization (AlgebraicGeometry.blowUp I) hfin) hNagataBlow,
      ((isProjectiveMorphism_of_isFinite _ N hNample).comp hblow).comp hP⟩

/-- **A chain of normalized blowups over an affine Nagata scheme is H-projective.** -/
theorem NormalizedBlowUpChain.isProjectiveMorphism {Y : Scheme.{u}} [IsAffine Y]
    (hNagata : IsNagataScheme Y)
    {hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite}
    {X : Scheme.{u}} {f : X ⟶ Y} (hchain : NormalizedBlowUpChain Y hY X f) :
    IsProjectiveMorphism f :=
  (hchain.isNagataScheme_and_isProjectiveMorphism hNagata).2

/-- **An excellent normal local domain of dimension two has an H-projective resolution of
singularities**: the resolution by normalized blowups of
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isExcellent_of_ringKrullDim_eq_two` is
H-projective by `AlgebraicGeometry.NormalizedBlowUpChain.isProjectiveMorphism`. -/
@[sga "6 X 7.17.5" "special case"]
theorem exists_isResolution_isProjectiveMorphism_of_isExcellent
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hexc : IsExcellent A) (hdim : ringKrullDim A = 2) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f ∧ IsProjectiveMorphism f := by
  obtain ⟨hY, X, f, hchain, hreg⟩ :=
    hasResolutionByNormalizedBlowUps_of_isExcellent_of_ringKrullDim_eq_two A hexc hdim
  have hd : topologicalKrullDim (Spec (.of A)) = 2 := by
    rw [← hdim]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A
  exact ⟨X, f, ⟨isModification_of_normalizedBlowUpChain hd hchain, hreg⟩,
    hchain.isProjectiveMorphism
      (isNagataScheme_spec_of_isNagataRing A (isNagataRing_of_isQuasiExcellent hexc.1))⟩

end AlgebraicGeometry

end
