module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NodalResolution
public import StacksFrontier.AlgebraicGeometry.Models.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractionStep

/-!
# The resolution of a nodal proper model is a morphism of models

Let `R` be a discrete valuation ring with fraction field `K`, and let `f : X ⟶ Spec R` be a proper
model of a smooth `K`-curve which is at-worst-nodal of relative dimension one with smooth generic
fibre. [Stacks, Tag 0CDE] resolves `X` by a chain `h : Y ⟶ X` of blowups in singular closed
points. Every point of `X` over the generic point of `Spec R` is regular, so no centre of the
chain lies over the generic fibre: `h` is an isomorphism over the generic fibre of `X`. Hence the
identification of the generic fibre of `X` with the curve transports to `Y`, and `Y` is a regular
proper model with `h` a morphism of models.

## Main results

* `Stacks.SemistableReduction.isRegularLocalRing_stalk_of_ne_closedPoint` — the points of a nodal
  family with smooth generic fibre lying over the generic point are regular.
* `Stacks.SemistableReduction.NodalBlowupChain.isIso_genericFiberMap` — a chain of blowups at
  singular points induces an isomorphism of generic fibres.
* `Stacks.SemistableReduction.exists_nodalBlowupChain_isRegular_isModelHom` — the resolution of
  [Stacks, Tag 0CDE] of a nodal proper model is a morphism of proper regular models.

## References

* [Stacks Project, Tag 0CDE](https://stacks.math.columbia.edu/tag/0CDE)
* [Stacks Project, Tag 0C2R](https://stacks.math.columbia.edu/tag/0C2R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.SemistableReduction

open Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The points of the generic fibre of a nodal family with smooth generic fibre are regular.**
If `f : X ⟶ Spec R` is at-worst-nodal of relative dimension one and its fibre over the generic
point is smooth, then the local ring of `X` at every point not over the closed point of `Spec R`
is regular. -/
public theorem isRegularLocalRing_stalk_of_ne_closedPoint {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    (hsmooth : Smooth (f.fiberToSpecResidueField (⊥ : PrimeSpectrum R))) (y : X)
    (hy : f.base y ≠ IsLocalRing.closedPoint R) : IsRegularLocalRing (X.presheaf.stalk y) := by
  have := locallyOfFinitePresentation hf.1.1
  have h : f.base y = (⊥ : PrimeSpectrum R) := PrimeSpectrum.ext (by
    by_contra h0
    exact hy (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      (Ring.DimensionLEOne.maximalOfPrime h0 (f.base y).isPrime))))
  refine isRegularLocalRing_stalk_of_smoothAt f y
    (smoothAt_of_flat_of_smoothAt_fiber f (flat hf.1.1) y ?_)
  rw [← h] at hsmooth
  exact (InfinitesimalLifting.smooth_iff_forall_smoothAt _).mp hsmooth _

/-- **A chain of blowups at singular points is an isomorphism on generic fibres.** For `f` nodal
with smooth generic fibre, every point of the generic fibre of `X` is regular, so the composite
`h : Y ⟶ X` of a `NodalBlowupChain` is an isomorphism over it. -/
public theorem NodalBlowupChain.isIso_genericFiberMap {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
    (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    (hsmooth : Smooth (f.fiberToSpecResidueField (⊥ : PrimeSpectrum R))) {Y : Scheme.{u}}
    {h : Y ⟶ X} (hc : NodalBlowupChain f Y h) :
    IsIso (genericFiberMapOfHomOver (K := K) (h ≫ f) f h rfl) := by
  let ι := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsOpenImmersion ι := genericFiberSpec_isOpenImmersion
  let V : X.Opens := f ⁻¹ᵁ ι.opensRange
  have : IsIso (h ∣_ V) := hc.isIso_morphismRestrict V fun y hy ↦ by
    obtain ⟨t, ht⟩ : f y ∈ Set.range ι := hy
    refine isRegularLocalRing_stalk_of_ne_closedPoint f hf hsmooth y ?_
    rw [← ht]
    exact genericFiberSpec_ne_closedPoint t
  let eg : pullback f ι ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst f ι) V.ι (by
      rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι])
  let ep : pullback (h ≫ f) ι ≅ (h ⁻¹ᵁ V).toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst (h ≫ f) ι) (h ⁻¹ᵁ V).ι (by
      rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι]
      rfl)
  have hm : genericFiberMapOfHomOver (K := K) (h ≫ f) f h rfl = ep.hom ≫ (h ∣_ V) ≫ eg.inv := by
    rw [← cancel_mono (pullback.fst f ι)]
    simp only [genericFiberMapOfHomOver, Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac,
      morphismRestrict_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, ep, eg]
    exact pullback.lift_fst _ _ _
  rw [hm]
  infer_instance

/-- **The resolution of a nodal proper model is a morphism of proper regular models.** Let `R` be
a discrete valuation ring with fraction field `K`, let `c : C ⟶ Spec K` be smooth, and let
`f : X ⟶ Spec R` be a proper model of `C` (via `e`) which is at-worst-nodal of relative dimension
one with smooth generic fibre, `X` quasi-compact. Then the chain `h : Y ⟶ X` of blowups at
singular closed points of [Stacks, Tag 0CDE] has `Y` regular and proper over `R`, and the
identification of the generic fibre transports along `h` to an identification `eY` making
`Y` a model of `C` and `h` a morphism of models. -/
public theorem exists_nodalBlowupChain_isRegular_isModelHom {C X : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [Smooth c] (f : X ⟶ Spec (.of R)) [IsProper f]
    (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    (e : C ≅ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c f e) [CompactSpace X]
    (hsm : Smooth (f.fiberToSpecResidueField (⊥ : PrimeSpectrum R))) :
    ∃ (Y : Scheme.{u}) (h : Y ⟶ X), NodalBlowupChain f Y h ∧ IsRegular Y ∧
      IsProper (h ≫ f) ∧
      ∃ eY : C ≅ pullback (h ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R K))),
        IsModel c (h ≫ f) eY ∧ IsModelHom (h ≫ f) f eY e h := by
  obtain ⟨Y, h, hc, hreg⟩ := exists_nodalBlowupChain_isRegular f hf hsm
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsProper h := hc.isProper
  have hnod := hc.isAtWorstNodalOfRelativeDimensionOne hf
  have := hc.isIso_genericFiberMap (K := K) hf hsm
  let G := genericFiberMapOfHomOver (K := K) (h ≫ f) f h rfl
  refine ⟨Y, h, hc, hreg, inferInstance, e ≪≫ (asIso G).symm, ⟨flat hnod.1.1, inferInstance,
    inferInstance, ?_⟩, rfl, ?_⟩
  · obtain ⟨-, -, -, hc'⟩ := hmod
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc]
    rw [← hc']
    congr 1
    rw [IsIso.inv_comp_eq]
    simp [G, genericFiberMapOfHomOver]
  · simp [G]

end Stacks.SemistableReduction

end
