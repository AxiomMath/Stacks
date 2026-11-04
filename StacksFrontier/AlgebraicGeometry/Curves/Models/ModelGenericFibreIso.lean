module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ContractionStep
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ModelSituation
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrCycleClasses
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupFactorizationStep
public import StacksFrontier.AlgebraicGeometry.RestrictIso

/-!
# Morphisms of models which are isomorphisms away from a closed point

Let `R` be a discrete valuation ring with fraction field `K`. A morphism `g : Y ⟶ X` of
`R`-schemes which is an isomorphism away from a closed point of `X` lying over the closed point of
`Spec R` induces an isomorphism of generic fibres; hence an identification of the generic fibre of
one of them with a curve `C` transports to the other. This applies to the blowup of a regular
proper model in a closed point, which is again a regular proper model.

## Main definitions

* `Stacks.Models.genericFiberMap` — the morphism of generic fibres induced by a morphism over
  `Spec R`.

## Main results

* `Stacks.Models.isIso_genericFiberMap_of_isIso_restrict_compl` — it is an isomorphism when the
  morphism is an isomorphism away from a closed point of the target.
* `Stacks.Models.exists_isModel_pointBlowUp` — the blowup of a regular proper model at a closed
  point is a regular proper model, with compatible identifications of the generic fibre.

## References

* [Stacks Project, Tag 0C2S](https://stacks.math.columbia.edu/tag/0C2S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ResolutionOfSurfaces

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The morphism of generic fibres induced by a morphism `g : Y ⟶ X` over `Spec R`. -/
abbrev genericFiberMap {X Y : Scheme.{u}} (g : Y ⟶ X) (pX : X ⟶ Spec (.of R)) :
    pullback (g ≫ pX) (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶
      pullback pX (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  pullback.map (g ≫ pX) (Spec.map (CommRingCat.ofHom (algebraMap R K))) pX
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) g (𝟙 _) (𝟙 _) (by simp) (by simp)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The first projection commutes with the map of generic fibres. -/
@[reassoc]
theorem genericFiberMap_fst {X Y : Scheme.{u}} (g : Y ⟶ X) (pX : X ⟶ Spec (.of R)) :
    genericFiberMap (K := K) g pX ≫
        pullback.fst pX (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      pullback.fst (g ≫ pX) (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ g := by
  simp [genericFiberMap]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The second projection commutes with the map of generic fibres. -/
@[reassoc]
theorem genericFiberMap_snd {X Y : Scheme.{u}} (g : Y ⟶ X) (pX : X ⟶ Spec (.of R)) :
    genericFiberMap (K := K) g pX ≫
        pullback.snd pX (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      pullback.snd (g ≫ pX) (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  simp [genericFiberMap]

/-- **A morphism which is an isomorphism away from a closed point over the closed point of
`Spec R` is an isomorphism on generic fibres.** -/
theorem isIso_genericFiberMap_of_isIso_restrict_compl {X Y : Scheme.{u}} (g : Y ⟶ X)
    (pX : X ⟶ Spec (.of R)) {z : X} (hz : IsClosed ({z} : Set X))
    (hpz : pX z = IsLocalRing.closedPoint R)
    (hoff : IsIso (g ∣_ (⟨({z} : Set X)ᶜ, hz.isOpen_compl⟩ : X.Opens))) :
    IsIso (genericFiberMap (K := K) g pX) := by
  let ι := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsOpenImmersion ι := genericFiberSpec_isOpenImmersion
  let W : X.Opens := ⟨({z} : Set X)ᶜ, hz.isOpen_compl⟩
  let V : X.Opens := pX ⁻¹ᵁ ι.opensRange
  have hVW : V ≤ W := by
    intro y hy
    obtain ⟨t, ht⟩ : pX y ∈ Set.range ι := hy
    change y ∉ ({z} : Set X)
    rintro (rfl : y = z)
    rw [hpz] at ht
    exact genericFiberSpec_ne_closedPoint t ht
  have : IsIso (g ∣_ V) := Stacks.RestrictIso.isIso_morphismRestrict_of_le g hVW hoff
  let eg : pullback pX ι ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst pX ι) V.ι (by
      rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι])
  let ep : pullback (g ≫ pX) ι ≅ (g ⁻¹ᵁ V).toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst (g ≫ pX) ι) (g ⁻¹ᵁ V).ι (by
      rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι]
      rfl)
  have hm : genericFiberMap (K := K) g pX = ep.hom ≫ (g ∣_ V) ≫ eg.inv := by
    rw [← cancel_mono (pullback.fst pX ι), genericFiberMap_fst]
    simp [ep, eg, morphismRestrict_ι]
    rfl
  rw [hm]
  infer_instance

/-- **The blowup of a regular proper model at a closed point is a regular proper model**, with an
identification of its generic fibre with `C` compatible with the blowup morphism. -/
theorem exists_isModel_pointBlowUp {C V : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsCurve K c]
    [Smooth c] (hproj : Stacks.HProjective.IsHProjective c)
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)] (pV : V ⟶ Spec (.of R))
    (e : C ≅ pullback pV (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c pV e) [IsProper pV] (hreg : IsRegular V) {v : V}
    (hv : IsClosed ({v} : Set V)) :
    ∃ e' : C ≅ pullback (pointBlowUpToBase hv ≫ pV)
        (Spec.map (CommRingCat.ofHom (algebraMap R K))),
      IsModel c (pointBlowUpToBase hv ≫ pV) e' ∧ IsProper (pointBlowUpToBase hv ≫ pV) ∧
        IsRegular (pointBlowUp hv) ∧
        e'.hom ≫ pullback.fst (pointBlowUpToBase hv ≫ pV)
            (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ pointBlowUpToBase hv =
          e.hom ≫ pullback.fst pV (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have hV := isIntegralRegularSurface_of_isModel c hproj pV e hmod hreg
  have hVnoe := hV.isNoetherian
  have hVint := hV.isIntegral
  have hB := isIntegralRegularSurface_blowUp_vanishingIdeal_singleton V v hv hV
  have hBint := hB.isIntegral
  set π := pointBlowUpToBase hv
  have hpv : pV v = IsLocalRing.closedPoint R :=
    eq_closedPoint_of_isClosed_singleton _ (by simpa using pV.isClosedMap _ hv)
  have hoff : IsIso (π ∣_ (⟨({v} : Set V)ᶜ, hv.isOpen_compl⟩ : V.Opens)) :=
    isIso_blowUp_restrict_compl_support
      (Scheme.IdealSheafData.vanishingIdeal (⟨{v}, hv⟩ : Closeds V))
  have hm := isIso_genericFiberMap_of_isIso_restrict_compl (K := K) π pV hv hpv hoff
  have : IsDominant pV := by
    rw [isDominant_iff]
    exact (regularProperModelSituation c hproj pV e hmod hreg).surjective_X_to_R.denseRange
  obtain ⟨-, hlft, hqc, hc⟩ := hmod
  have : IsDominant π := (isBirational_blowUpToBase _
    (vanishingIdeal_singleton_ne_bot hV.topologicalKrullDim_eq v hv)).isDominant
  refine ⟨e ≪≫ (asIso (genericFiberMap (K := K) π pV)).symm,
    ⟨Stacks.Chow.flat_of_isIntegral_of_isDominant _, inferInstance, inferInstance, ?_⟩,
    inferInstance, hB.isRegular, ?_⟩
  all_goals simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  · rwa [← genericFiberMap_snd (K := K) π pV, IsIso.inv_hom_id_assoc]
  · rw [← genericFiberMap_fst, IsIso.inv_hom_id_assoc]

end Stacks.Models

end
