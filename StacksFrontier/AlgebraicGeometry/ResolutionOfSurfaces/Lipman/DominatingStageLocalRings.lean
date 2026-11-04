module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.RationalSingularityResolution
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ResolutionByNormalizedBlowUpsAssembly
public import StacksFrontier.AlgebraicGeometry.Morphisms.DimensionFormula.Formula
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.GenericPoint
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Pullback
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.RingTheory.Dualizing.UbiquityCompleteLocal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The singular points of a normal modification dominating a resolution

Let `B` be a two-dimensional Noetherian complete local normal domain, `f : X ⟶ Spec B` a
resolution of singularities and `g : Z ⟶ Spec B` a normal modification factoring as
`h ≫ f`. The proof of [Stacks, Tag 0BGM] shows that the spectrum of the local ring of `Z` at
each singular point `z` has a resolution by normalized blowups: the local ring of `X` at
`x = h(z)` is regular of dimension two, so defines a rational singularity by [Stacks, Tag 0B4Q];
the local ring of `Z` at `z` dominates it birationally, so defines a rational singularity by
[Stacks, Tag 0BG0]; and it is excellent with a dualizing complex, being essentially of finite
type over `B`, so
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_definesRationalSingularity` applies.

## Main results

* `AlgebraicGeometry.isBirational_of_comp_isModification`: `h` is birational.
* `AlgebraicGeometry.ringKrullDim_stalk_le_of_isBirational`: along a birational morphism locally
  of finite type the local rings do not grow in dimension.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_stalk_of_dominates_isResolution`: the local
  statement above, which is the input `hlocal` of
  `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isResolution_of_local`.
* `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isResolution_of_lipmanInputs`: Tag 0BGM
  from Tags 0B4Q, 0BG0, 0BBV and 0BGE.

## Implementation notes

The tags consumed are arguments, stated exactly as they are stated elsewhere (see
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Lipman.RationalSingularityResolution`);
`hregular` is [Stacks, Tag 0B4Q].

## References

* [Stacks Project, Tag 0BGM](https://stacks.math.columbia.edu/tag/0BGM)
* [Stacks Project, Tag 0B4Q](https://stacks.math.columbia.edu/tag/0B4Q)
* [Stacks Project, Tag 0BG0](https://stacks.math.columbia.edu/tag/0BG0)
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU)
-/

@[expose] public section

open CategoryTheory IsLocalRing

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **A morphism between two modifications of the same integral scheme, compatible with the
maps to it, is birational**, when the modifications have the same dimension as the base: the
only point of the source of a modification above the generic point of the base is its own
generic point. -/
theorem isBirational_of_comp_isModification {X Y Z : Scheme.{u}} [IsIntegral Y]
    {f : X ⟶ Y} {g : Z ⟶ Y} (h : Z ⟶ X) (hf : IsModification f) (hg : IsModification g)
    (hhg : h ≫ f = g) {d : ℕ} (hX : topologicalKrullDim X = (d : WithBot ℕ∞))
    (hY : topologicalKrullDim Y = (d : WithBot ℕ∞)) : IsBirational h := by
  have : IsIntegral X := hf.source_isIntegral
  have : IsProper f := hf.isProper
  refine isBirational_of_comp_of_isBirational h f (hhg ▸ hg.isBirational) hf.isBirational ?_
  rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact ⟨fun hx => eq_genericPoint_of_map_eq_genericPoint_of_dim_eq f f.isClosedMap hX hY hx,
    fun hx => hx ▸ hf.isBirational.genericPoint_eq⟩

/-- **Along a birational morphism locally of finite type of integral schemes over a locally
Noetherian base, the local rings do not grow in dimension**, by the dimension formula of
[Stacks, Tag 02JU]: the extension of function fields is trivial. -/
@[ega "IV 18.9.7.6" "special case"]
theorem ringKrullDim_stalk_le_of_isBirational {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    [IsLocallyNoetherian X] (h : Z ⟶ X) [LocallyOfFiniteType h] (hh : IsBirational h) (z : Z) :
    ringKrullDim (Z.presheaf.stalk z) ≤ ringKrullDim (X.presheaf.stalk (h.base z)) := by
  have : IsDominant h := hh.isDominant
  have H := ringKrullDim_stalk_add_trdeg_residueField_le h z
  let : Algebra X.functionField Z.functionField := h.functionFieldMap.hom.toAlgebra
  have hfeq : (Scheme.Hom.functionFieldMap h).hom = functionFieldMap h := by
    simp [Scheme.Hom.functionFieldMap, functionFieldMap, TopCat.Presheaf.stalkCongr_hom]
  have halg : Algebra.IsAlgebraic X.functionField Z.functionField := ⟨fun a => by
    obtain ⟨b, rfl⟩ := (hfeq ▸ hh.surjective_functionFieldMap :
      Function.Surjective (Scheme.Hom.functionFieldMap h).hom) a
    exact isAlgebraic_algebraMap b⟩
  rw [trdeg_eq_zero_iff.mpr halg] at H
  simp only [map_zero, Nat.cast_zero, add_zero] at H
  exact (le_add_of_nonneg_right (by positivity)).trans H

/-- **The local rings of a normal modification dominating a resolution, at its singular
points, have resolutions by normalized blowups**, granted Tags 0B4Q, 0BBV, 0BGE and 0BG0. This
is the content of Step 4 of the proof of [Stacks, Tag 0BGM]. -/
theorem hasResolutionByNormalizedBlowUps_stalk_of_dominates_isResolution
    (hregular : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A] [IsNagataRing A],
      ringKrullDim A = 2 → (letI := IsRegularLocalRing.isDomain A; DefinesRationalSingularity A))
    (hgorenstein : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      (letI := hN.1; ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧
        ∀ y : Y, ∃ _ : IsNoetherianRing (Y.presheaf.stalk y),
          Dualizing.IsGorensteinLocalRing (Y.presheaf.stalk y))
    (hdoublePoint : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      IsNormalRing (AdicCompletion (maximalIdeal A) A) →
      (letI := hN.1; Dualizing.IsGorensteinLocalRing A) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧ IsRegular Y)
    (hrationalExt : ∀ (A B : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      [CommRing B] [IsLocalRing B] [IsNormalDomain B] [Algebra A B]
      [IsLocalHom (algebraMap A B)] (K : Type u) [Field K] [Algebra A K] [Algebra B K]
      [IsScalarTower A B K] [IsFractionRing A K] [IsFractionRing B K], IsNagataRing A →
      ringKrullDim A = 2 → ringKrullDim B = 2 → Algebra.EssFiniteType A B →
      DefinesRationalSingularity A → DefinesRationalSingularity B)
    (B : Type u) [CommRing B] [IsNoetherianRing B] [IsLocalRing B] [IsNormalDomain B]
    [IsAdicComplete (maximalIdeal B) B] (hdim : ringKrullDim B = 2)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) (hf : IsResolution f)
    (Z : Scheme.{u}) [IsNormal Z] (g : Z ⟶ Spec (.of B)) (h : Z ⟶ X)
    (hg : IsModification g) (hhg : h ≫ f = g) (z : Z) (hz : z ∈ singularLocus Z) :
    HasResolutionByNormalizedBlowUps (Spec (Z.presheaf.stalk z)) := by
  have hBexc : IsExcellent B := (isExcellent_of_standard_classes_and_finiteType.{u, u}).2.1 B
  have : IsLocallyNoetherian (Spec (.of B)) := isLocallyNoetherian_Spec.mpr inferInstance
  have hfmod : IsModification f := hf.isModification
  have : IsIntegral X := hfmod.source_isIntegral
  have : IsIntegral Z := hg.source_isIntegral
  have : IsProper f := hfmod.isProper
  have : IsProper g := hg.isProper
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have : LocallyOfFiniteType (h ≫ f) := hhg ▸ (inferInstance : LocallyOfFiniteType g)
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h f
  have hdimB : topologicalKrullDim (Spec (.of B)) = ((2 : ℕ) : WithBot ℕ∞) := by
    change topologicalKrullDim (PrimeSpectrum B) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim]
    rfl
  have hdimX : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_eq_of_isModification f hfmod).trans hdimB
  have hdimZ : topologicalKrullDim Z = ((2 : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_eq_of_isModification g hg).trans hdimB
  have hh : IsBirational h := isBirational_of_comp_isModification h hfmod hg hhg hdimX hdimB
  have : IsDominant h := hh.isDominant
  let O := Z.presheaf.stalk z
  have : IsNormalDomain O := ⟨IsNormal.stalk_isDomain _, IsNormal.stalk_normal _⟩
  have hOdim : ringKrullDim O = 2 := ringKrullDim_stalk_eq_two_of_mem_singularLocus Z hdimZ.le z hz
  obtain ⟨_, L, hOdual⟩ := exists_isDualizingComplex_stalk_of_locallyOfFiniteType B
    (Dualizing.exists_isDualizingComplex_of_isPrecomplete_maximalIdeal B) g z
  let A := X.presheaf.stalk (h.base z)
  have : IsRegularLocalRing A := hf.source_isRegular.isRegularLocalRing_stalk _
  have : IsNormal X := isNormal_of_isRegular X hf.source_isRegular
  have : IsNormalDomain A := ⟨IsNormal.stalk_isDomain _, IsNormal.stalk_normal _⟩
  have hAN : IsNagataRing A := isNagataRing_of_isQuasiExcellent
    (isExcellent_stalk_of_locallyOfFiniteType hBexc f (h.base z)).1
  have hAdim : ringKrullDim A = 2 :=
    le_antisymm ((le_iSup (fun x : X => ringKrullDim (X.presheaf.stalk x)) (h.base z)).trans
      ((topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X).symm.trans_le hdimX.le))
      (hOdim ▸ ringKrullDim_stalk_le_of_isBirational h hh z)
  let : Algebra A O := (h.stalkMap z).hom.toAlgebra
  let : Algebra A Z.functionField := stalkFunctionFieldAlgebraOfHom h z
  have : IsScalarTower A O Z.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsFractionRing A Z.functionField := isFractionRing_stalk_of_isBirational h hh z
  have : IsLocalHom (algebraMap A O) := inferInstanceAs (IsLocalHom (h.stalkMap z).hom)
  exact hasResolutionByNormalizedBlowUps_of_definesRationalSingularity hgorenstein hdoublePoint
    hrationalExt O (isExcellent_stalk_of_locallyOfFiniteType hBexc g z) ⟨L, hOdual⟩ hOdim
    (hrationalExt A O Z.functionField hAN hAdim hOdim (LocallyOfFiniteType.stalkMap h z)
      (hregular A hAdim))

/-- **[Stacks, Tag 0BGM], from Tags 0B4Q, 0BG0, 0BBV and 0BGE.** A two-dimensional Noetherian
local normal domain whose spectrum has a resolution of singularities has a resolution of
singularities by normalized blowups.

The reduction to the complete case and the domination of the resolution by normalized blowups
are `AlgebraicGeometry.hasResolutionByNormalizedBlowUps_of_isResolution_of_local`; the local
input at the singular points of a dominating stage is
`AlgebraicGeometry.hasResolutionByNormalizedBlowUps_stalk_of_dominates_isResolution`. -/
theorem hasResolutionByNormalizedBlowUps_of_isResolution_of_lipmanInputs
    (hregular : ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A] [IsNagataRing A],
      ringKrullDim A = 2 → (letI := IsRegularLocalRing.isDomain A; DefinesRationalSingularity A))
    (hgorenstein : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      (letI := hN.1; ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧
        ∀ y : Y, ∃ _ : IsNoetherianRing (Y.presheaf.stalk y),
          Dualizing.IsGorensteinLocalRing (Y.presheaf.stalk y))
    (hdoublePoint : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      (hN : IsNagataRing A), ringKrullDim A = 2 → DefinesRationalSingularity A →
      IsNormalRing (AdicCompletion (maximalIdeal A) A) →
      (letI := hN.1; Dualizing.IsGorensteinLocalRing A) →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain (Spec (.of A))
          {IsLocalRing.closedPoint A} Y f ∧ IsRegular Y)
    (hrationalExt : ∀ (A B : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
      [CommRing B] [IsLocalRing B] [IsNormalDomain B] [Algebra A B]
      [IsLocalHom (algebraMap A B)] (K : Type u) [Field K] [Algebra A K] [Algebra B K]
      [IsScalarTower A B K] [IsFractionRing A K] [IsFractionRing B K], IsNagataRing A →
      ringKrullDim A = 2 → ringKrullDim B = 2 → Algebra.EssFiniteType A B →
      DefinesRationalSingularity A → DefinesRationalSingularity B)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hdim : ringKrullDim A = 2)
    (hres : ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f) :
    HasResolutionByNormalizedBlowUps (Spec (.of A)) :=
  hasResolutionByNormalizedBlowUps_of_isResolution_of_local A hdim hres
    fun B _ _ _ _ _ hdimB _ f hf Z _ g h hg hhg z hz =>
      hasResolutionByNormalizedBlowUps_stalk_of_dominates_isResolution hregular hgorenstein
        hdoublePoint hrationalExt B hdimB f hf Z g h hg hhg z hz

end AlgebraicGeometry

end
