module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.AlgebraicGeometry.Models.Normalization
public import StacksFrontier.AlgebraicGeometry.Models.RegularProperModelExists
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionDominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Dimension
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanTheorem
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.Models
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.SingularLocusFinite
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# Existence of resolutions of models of smooth curves

Let `R` be a discrete valuation ring with fraction field `K`, let `C` be a smooth curve over `K`
and let `X ⟶ Spec R` be a model of `C`. Then `X` is a Noetherian integral scheme, it has a
resolution of singularities, and every resolution of singularities of `X` is a model of `C`.

## Main results

* `AlgebraicGeometry.exists_isResolution_and_isModel_comp_of_isModel` — [Stacks, Tag 0C2U].
* `AlgebraicGeometry.exists_isResolution_of_isModel` — the existence of a resolution of a
  Noetherian integral model.

## Implementation notes

Existence is Lipman's theorem (Tag 0BGP) through its condition (4). The model has dimension at
most two by the dimension bound of Tag 0BAG: the transcendence degree of its function field over
`K` is the dimension of a local ring of the generic fibre at a closed point, at most one. In
dimension two the normalization `X^ν` is finite with normal completed local rings by Tag 0C2T,
and its singular locus is finite because `X^ν` is normal of dimension at most two and J-2, being
of finite type over the one-dimensional Noetherian local ring `R` (Tag 07R5). In dimension at
most one the normalization is itself a resolution, a normal scheme of dimension at most one
being regular (Tag 0BX2). That every resolution is a model is
`AlgebraicGeometry.isModel_comp_of_isResolution`, and integrality and Noetherianity of the model
are `Stacks.Models.isIntegral_of_isModel` and `Stacks.Models.isNoetherian_of_isModel`.

## References

* [Stacks Project, Tag 0BGP](https://stacks.math.columbia.edu/tag/0BGP)
* [Stacks Project, Tag 0C2T](https://stacks.math.columbia.edu/tag/0C2T)
* [Stacks Project, Tag 0C2U](https://stacks.math.columbia.edu/tag/0C2U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/-! ### Existence of a resolution -/

namespace AlgebraicGeometry

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The residue field of a model at its generic point has transcendence degree at most one over
the fraction field. The fibre of the model through its generic point is the generic fibre, of
dimension one; at a closed point of that fibre the local ring has dimension equal to this
transcendence degree, and it is a quotient of the local ring of the generic fibre. -/
private theorem residueFieldTranscendenceDegree_genericPoint_le_one {C X : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] (p : X ⟶ Spec (.of R)) [IsIntegral X]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (eX : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    (residueFieldTranscendenceDegree p (genericPoint X) : WithBot ℕ∞) ≤ 1 := by
  let i := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let a := pullback.fst p i
  have : IsOpenImmersion i := Stacks.Models.genericFiberSpec_isOpenImmersion
  have : IsIntegral (pullback p i) := IsIntegral.of_isIso eX.hom
  obtain ⟨z⟩ := (inferInstance : Nonempty (pullback p i : Scheme.{u}))
  have : IrreducibleSpace (p.fiber (p (genericPoint X))) := p.irreducibleSpace_fiber_genericPoint
  have : CompactSpace (p.fiber (p (genericPoint X))) := by
    have : CompactSpace (p ⁻¹' {p (genericPoint X)}) :=
      isCompact_iff_compactSpace.mp (p.isCompact_preimage_singleton _)
    exact (p.fiberHomeo (p (genericPoint X))).symm.compactSpace
  obtain ⟨q, -, hq⟩ := IsClosed.exists_closed_singleton
    (isClosed_univ (X := p.fiber (p (genericPoint X)))) Set.univ_nonempty
  rw [← ringKrullDim_stalk_fiber_eq_residueFieldTrdeg p q hq]
  have hfib : ringKrullDim ((p.fiber (p (genericPoint X))).presheaf.stalk q) ≤
      ringKrullDim (X.presheaf.stalk (p.fiberι (p (genericPoint X)) q)) :=
    ringKrullDim_le_of_surjective _ ((p.fiberι (p (genericPoint X))).stalkMap_surjective q)
  have hmem : p.fiberι (p (genericPoint X)) q ∈ a.opensRange := by
    rw [Scheme.Hom.opensRange_pullbackFst]
    change p (p.fiberι (p (genericPoint X)) q) ∈ Set.range i
    have h1 : p (p.fiberι (p (genericPoint X)) q) = p (genericPoint X) := by
      change _ ∈ p ⁻¹' {p (genericPoint X)}
      rw [← Scheme.Hom.range_fiberι]
      exact ⟨q, rfl⟩
    rw [h1]
    obtain ⟨w, hw⟩ := ((genericPoint_spec X).mem_open_set_iff a.isOpenEmbedding.isOpen_range).mpr
      ⟨a z, Set.mem_univ _, z, rfl⟩
    rw [← hw]
    exact ⟨pullback.snd p i w, (congrArg (fun φ : pullback p i ⟶ Spec (.of R) => φ w)
      (pullback.condition : a ≫ p = pullback.snd p i ≫ i)).symm⟩
  obtain ⟨x', hx'⟩ := hmem
  rw [← hx'] at hfib
  calc ringKrullDim ((p.fiber (p (genericPoint X))).presheaf.stalk q)
      ≤ ringKrullDim (X.presheaf.stalk (a x')) := hfib
    _ = ringKrullDim ((pullback p i).presheaf.stalk x') :=
      ringKrullDim_eq_of_ringEquiv (asIso (a.stalkMap x')).commRingCatIsoToRingEquiv
    _ ≤ topologicalKrullDim (pullback p i : Scheme.{u}) :=
      ringKrullDim_stalk_le_topologicalKrullDim x'
    _ = 1 := by
      rw [← IsHomeomorph.topologicalKrullDim_eq _
        (TopCat.homeoOfIso (asIso eX.hom.base)).isHomeomorph]
      exact IsCurve.topologicalKrullDim_eq_one (k := K) (f := c)

/-- An integral model of a curve has dimension at most two: by Tag 0BAG its dimension is bounded
by the dimension one of `Spec R` plus the transcendence degree of its function field over `K`,
which is the dimension one of the generic fibre. -/
private theorem topologicalKrullDim_le_two_of_isModel {C X : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsCurve K c] (p : X ⟶ Spec (.of R)) [IsIntegral X]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (eX : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :
    topologicalKrullDim X ≤ 2 := by
  have hR : topologicalKrullDim (Spec (.of R)) = 1 := by
    change topologicalKrullDim (PrimeSpectrum R) = 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      IsDiscreteValuationRing.ringKrullDim_eq_one]
  have hsup : (((⨆ ξ : genericPoints X, residueFieldTranscendenceDegree p ξ.1 : ℕ∞)) :
      WithBot ℕ∞) ≤ 1 := by
    have : (⨆ ξ : genericPoints X, residueFieldTranscendenceDegree p ξ.1) ≤ 1 := by
      refine iSup_le fun ξ => ?_
      have hξ : ξ.1 = genericPoint X := by
        change ξ.1 ∈ ({genericPoint X} : Set X)
        rw [← genericPoints_eq_singleton]
        exact ξ.2
      rw [hξ]
      exact_mod_cast residueFieldTranscendenceDegree_genericPoint_le_one c p eX
    exact_mod_cast this
  calc topologicalKrullDim X
      ≤ topologicalKrullDim (Spec (.of R)) +
        (((⨆ ξ : genericPoints X, residueFieldTranscendenceDegree p ξ.1 : ℕ∞)) :
          WithBot ℕ∞) := topologicalKrullDim_le_add_iSup_residueFieldTrdeg p
    _ ≤ 1 + 1 := add_le_add hR.le hsup
    _ = 2 := by norm_num

/-- A model of a smooth curve over `K`, Noetherian and integral, has a resolution of
singularities. In dimension two this is condition (4) of Lipman's theorem (Tag 0BGP), checked
with Tag 0C2T and the J-2 property of `R`; in dimension at most one the normalization is
already regular. -/
theorem exists_isResolution_of_isModel {C X : Scheme.{u}} (c : C ⟶ Spec (.of K)) [Smooth c]
    [IsCurve K c] (p : X ⟶ Spec (.of R)) [IsIntegral X] [IsNoetherian X]
    (eX : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : Stacks.Models.IsModel c p eX) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsResolution f := by
  have : LocallyOfFiniteType p := hX.2.1
  have : QuasiCompact p := hX.2.2.1
  have hY := finite_irreducibleComponents_of_isCompact X
  have hgn : IsGeometricallyNormal c := isGeometricallyNormal_of_smooth c
  have hfin : IsFinite (X.normalization hY) :=
    Stacks.Models.isFinite_normalization_of_isModel c hgn p eX hX hY
  let N := X.normalizationScheme hY
  have : IsNormal N := Scheme.isNormal_normalizationScheme X hY
  have : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian (X.normalization hY)
  have : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace (X.normalization hY)
  have : IsNoetherian N := ⟨⟩
  have hdimN : topologicalKrullDim N ≤ topologicalKrullDim X :=
    topologicalKrullDim_le_of_isIntegralHom (X.normalization hY)
  rcases eq_or_lt_of_le (topologicalKrullDim_le_two_of_isModel c p eX) with h2 | hlt
  · refine ((tfae_exists_isAlteration_isRegular X h2).out 4 2).mp ?_
    exact ⟨hY, hfin, finite_singularLocus_of_isJ2 N (hdimN.trans h2.le)
        (Scheme.isJ2_of_locallyOfFiniteType_over_localRing_of_dim_one R
          (IsDiscreteValuationRing.ringKrullDim_eq_one R) (X.normalization hY ≫ p)),
      fun y _ => Stacks.Models.isNormalRing_adicCompletion_stalk_normalization_of_isModel c hgn p
        eX hX hY y⟩
  · have h1 : topologicalKrullDim X ≤ 1 := by
      have : topologicalKrullDim X < ((1 : ℕ) : WithBot ℕ∞) + 1 := by
        simpa [one_add_one_eq_two] using hlt
      exact_mod_cast ENat.WithBot.lt_add_one_iff.mp this
    exact ⟨N, X.normalization hY, ⟨X.isBirational_normalization hY, inferInstance, inferInstance⟩,
      isRegular_of_isNormal_of_topologicalKrullDim_le_one N (hdimN.trans h1)⟩

/-- **Stacks Project, Tag 0C2U.** Let `X` be a model of a smooth curve `C` over `K`. Then `X` is
a Noetherian integral scheme, there exists a resolution of singularities of `X`, and any
resolution of singularities of `X` is a model of `C`. -/
@[stacks 0C2U]
theorem exists_isResolution_and_isModel_comp_of_isModel {C X : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [Smooth c] [IsCurve K c] (p : X ⟶ Spec (.of R))
    (eX : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hX : Stacks.Models.IsModel c p eX) :
    ∃ (_ : IsIntegral X) (_ : IsNoetherian X),
      (∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsResolution f) ∧
      ∀ (Y : Scheme.{u}) (f : Y ⟶ X), IsResolution f →
        ∃ eY : C ≅ pullback (f ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap R K))),
          Stacks.Models.IsModel c (f ≫ p) eY := by
  have : IsIntegral X := Stacks.Models.isIntegral_of_isModel c p eX hX
  have : IsNoetherian X := Stacks.Models.isNoetherian_of_isModel c p eX hX
  exact ⟨inferInstance, inferInstance, exists_isResolution_of_isModel c p eX hX,
    fun _ f hf => isModel_comp_of_isResolution c p eX hX f hf⟩

end AlgebraicGeometry

end
