module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.LipDFrobeniusKills
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.LipDSeparableGoUp
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayFirstCohomologyDimTwo
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingDefinesRational
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity

/-!
# Reduction to rational singularities from a uniform annihilator of `H¹`

The final step of the Frobenius route to [Stacks, Tag 0B4U]. Let `R → A` be a finite injective
local homomorphism of local normal Nagata domains of dimension two. If a fixed nonzero `c ∈ R`
kills `H¹(Y, 𝒪_Y)` for every normal modification `Y` of `Spec A` which is finite and surjective
over a normal modification of `Spec R`, then reduction to rational singularities is possible for
`A`. The annihilation itself is supplied, from Frobenius data over the punctured spectrum, by
`AlgebraicGeometry.PuncturedRestriction.smul_rightDerived_pushUnit_eq_zero`.

## Main results

* `AlgebraicGeometry.isZero_hgroup_of_isModification_of_isRegularLocalRing`: `H¹(X, 𝒪_X) = 0`
  for a normal modification of the spectrum of a regular local ring of dimension two
  ([Stacks, Tag 0B4Q]), in the abelian-group model.
* `AlgebraicGeometry.isReductionToRationalSingularitiesPossible_of_forall_smul_eq_zero`: the
  reduction above, through [Stacks, Tags 0B49 and 0AXJ].
* `AlgebraicGeometry.smul_firstCohomology_eq_zero_of_frobenius`: the annihilation of
  `H¹(Y, 𝒪_Y)` from Frobenius data.

## References

* [Stacks Project, Tag 0B4U](https://stacks.math.columbia.edu/tag/0B4U)
* [Stacks Project, Tag 0B4Q](https://stacks.math.columbia.edu/tag/0B4Q)
* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

open PuncturedRestriction SeparableGoUp

/-- Over a modification of the spectrum of a regular local ring of dimension two, the first
cohomology of the structure sheaf vanishes, in the abelian-group model. -/
theorem isZero_hgroup_of_isModification_of_isRegularLocalRing (R : Type u) [CommRing R]
    [IsRegularLocalRing R] [IsNagataRing R] (hR : ringKrullDim R = 2) {X : Scheme.{u}}
    [IsNormal X] (f : X ⟶ Spec (.of R))
    (hf : letI := IsRegularLocalRing.isDomain R; IsModification f) :
    IsZero (Hgroup (structureSheafRing X.toLocallyRingedSpace.toRingedSpace) ⊤ 1
      (SheafOfModules.unit (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))) := by
  have := IsRegularLocalRing.isDomain R
  exact (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    X.ringCatSheaf ⊤ 1 _).mp ((isZeroFirstStructureSheafCohomology_iff_isZero_rightDerived X).mp
      (definesRationalSingularity_of_isRegularLocalRing_of_ringKrullDim_eq_two R hR X f hf))

/-- **Reduction to rational singularities from a uniform annihilator over a dominating finite
cover.** Let `R → A` be a finite injective local homomorphism of local normal Nagata domains of
dimension two, and let `c ∈ R` be nonzero. Suppose that whenever a normal modification `Y` of
`Spec A` is finite and surjective over a normal modification `X` of `Spec R`, the image of `c`
kills `H¹(Y, 𝒪_Y)`. Then reduction to rational singularities is possible for `A`: every normal
modification of `Spec A` is dominated by such a `Y` ([Stacks, Tag 0B49], in the form
`AlgebraicGeometry.isDominatedByFiniteOverBase`), its first cohomology is then its own `c`-torsion,
and that is bounded by [Stacks, Tag 0AXJ] and (0AXK). -/
theorem isReductionToRationalSingularitiesPossible_of_forall_smul_eq_zero (R A : Type u)
    [CommRing R] [IsLocalRing R] [IsNormalDomain R] [CommRing A] [IsLocalRing A]
    [IsNormalDomain A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A]
    [IsLocalHom (algebraMap R A)] (hR : IsNagataRing R) (hA : IsNagataRing A)
    (hdimR : ringKrullDim R = 2) (hdimA : ringKrullDim A = 2) (c : R) (hc : c ≠ 0)
    (hkill : ∀ (X Y : Scheme.{u}) [IsNormal X] [IsNormal Y] (f : X ⟶ Spec (.of R))
      (g : Y ⟶ Spec (.of A)) (π : Y ⟶ X), IsModification f → IsModification g → IsFinite π →
        Surjective π → π ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) →
          ∀ x : firstCohomologyAsBaseModule Y g, algebraMap R A c • x = 0) :
    IsReductionToRationalSingularitiesPossible A := by
  have : IsNagataRing A := hA
  have hc' : algebraMap R A c ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R A)).mpr hc
  obtain ⟨N, hN⟩ := exists_uniform_bound_length_quotient_baseToZeroSchemeSections hdimA hc'
  refine ⟨N, fun Y _ g hg => ?_⟩
  have : IsIntegral Y := hg.source_isIntegral
  obtain ⟨Y', X', g', f', π, q, hY', hX', hg', hf', hπ, hπs, hcomm, hq⟩ :=
    isDominatedByFiniteOverBase R A hR hA hdimR hdimA Y g hg
  have hqmod : IsModification q := by
    subst hq
    exact SeparableGoUp.isModification_of_comp hg hg'
  have h1 := length_firstCohomology_le_of_isModification g q hqmod
  rw [hq] at h1
  refine h1.trans ?_
  have htop : Submodule.torsionBy A (firstCohomologyAsBaseModule Y' g') (algebraMap R A c) = ⊤ :=
    eq_top_iff.mpr fun x _ => (Submodule.mem_torsionBy_iff _ _).mpr
      (hkill X' Y' f' g' π hf' hg' hπ hπs hcomm x)
  have hlen : Module.length A (firstCohomologyAsBaseModule Y' g') =
      Module.length A (Submodule.torsionBy A (firstCohomologyAsBaseModule Y' g')
        (algebraMap R A c)) := by
    rw [htop]
    exact Submodule.topEquiv.length_eq.symm
  rw [hlen, ← length_quotient_baseToZeroSchemeSections_eq Y' g' hg' hc']
  exact hN Y' g' hg'

/-- **The image of `c` kills `H¹(Y, 𝒪_Y)`, from Frobenius data.** Let `Y` be a normal modification
of `Spec A` finite and surjective over a normal modification `X` of `Spec R` with
`H¹(X, 𝒪_X) = 0`. Given Frobenius data over the part of `X` lying over the punctured spectrum of
`R` for the image of `c ∈ R`, the image of `c` in `A` kills `H¹(Y, 𝒪_Y)`. -/
theorem smul_firstCohomology_eq_zero_of_frobenius (R A : Type u) [CommRing R] [IsLocalRing R]
    [IsDomain R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A]
    [Algebra R A] [Algebra.IsIntegral R A] [IsLocalHom (algebraMap R A)]
    (hdimA : ringKrullDim A = 2)
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNormal X] [IsNormal Y]
    (f : X ⟶ Spec (.of R))
    (g : Y ⟶ Spec (.of A)) (π : Y ⟶ X) (hg : IsModification g) [IsFinite π] [Surjective π]
    (hcomm : π ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hH : IsZero (Hgroup (structureSheafRing X.toLocallyRingedSpace.toRingedSpace) ⊤ 1
      (SheafOfModules.unit (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))))
    (p : ℕ) [Fact p.Prime] [CharP X.functionField p]
    (hpow : ∀ y : Y.functionField, ∃ k : X.functionField,
      dominantFunctionFieldMap π k = y ^ p)
    (c : R) {n : ℕ} (b : Fin n → Γ(X, ⊤)) (β : Fin n → Γ(Y, ⊤))
    (θ : X.functionField →+ X.functionField)
    (Θ : ∀ U : X.Opens, Γ(X, U) → Γ(X, U))
    (hΘ : ∀ (U : X.Opens), U ≤ f ⁻¹ᵁ Stacks.puncturedSpectrum R →
      ∀ (a : Γ(X, U)) (hU : genericPoint X ∈ U),
        X.presheaf.germ U (genericPoint X) hU (Θ U a) =
          θ (X.presheaf.germ U (genericPoint X) hU a))
    (hid : ∀ (k : X.functionField) (y : Y.functionField), dominantFunctionFieldMap π k = y ^ p →
        dominantFunctionFieldMap π
            (X.presheaf.germ ⊤ (genericPoint X) trivial (baseSection X f c)) * y =
          ∑ i, Y.presheaf.germ ⊤ (genericPoint Y) trivial (β i) *
            dominantFunctionFieldMap π
              (θ (X.presheaf.germ ⊤ (genericPoint X) trivial (b i) * k)))
    (x : firstCohomologyAsBaseModule Y g) : algebraMap R A c • x = 0 := by
  let V := vanishingSituationOfModification A hdimA g hg
  have : IsNormal V.X := ‹IsNormal Y›
  have : IsIntegral V.X := hg.source_isIntegral
  let π' : V.X ⟶ X := π
  have : IsFinite π' := ‹IsFinite π›
  have : Surjective π' := ‹Surjective π›
  have hW : π ⁻¹ᵁ (f ⁻¹ᵁ Stacks.puncturedSpectrum R) = V.preimagePuncturedSpectrum := by
    change (π ≫ f) ⁻¹ᵁ Stacks.puncturedSpectrum R = g ⁻¹ᵁ Stacks.puncturedSpectrum A
    rw [hcomm]
    change g ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ
      Stacks.puncturedSpectrum R) = _
    rw [preimage_puncturedSpectrum_eq]
  let E := (firstCohomologyRestrictEquiv f g π hcomm).trans (firstCohomologyPushforwardEquiv f π)
  let x' : (ModuleCat.restrictScalars (algebraMap R A)).obj (firstCohomologyAsBaseModule Y g) := x
  have h : E (c • x') = E 0 := by
    rw [map_smul, map_zero]
    exact smul_rightDerived_pushUnit_eq_zero V π' p hpow hH _ hW (baseSection X f c) b β θ Θ hΘ hid
      (E x')
  exact E.injective h

end AlgebraicGeometry

end
