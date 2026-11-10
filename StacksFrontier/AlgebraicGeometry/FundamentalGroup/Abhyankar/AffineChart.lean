module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Affine charts of a finite étale cover of an open subscheme

Let `ψ : Spec R ⟶ X` be an open immersion and `U ⊆ X` an open with `ψ⁻¹(U) = D(φ)`. For a finite
étale `f : Y ⟶ U`, the restriction of `f` over `D(φ) ≅ Spec R_φ` is `Spec B ⟶ Spec R_φ` for a
finite étale `R_φ`-algebra `B`. For an `R`-algebra `T`, base changing along `Spec T ⟶ X` gives
the two pullback squares

* `Spec T_φ ⟶ U` over `Spec T ⟶ X`, and
* `Spec (T_φ ⊗_{R_φ} B) ⟶ Y` over `Spec T_φ ⟶ U`.

## Main definitions

* `AlgebraicGeometry.Abhyankar.chartU`: the map `Spec R_φ ⟶ U`.
* `AlgebraicGeometry.Abhyankar.chartRing`: the ring `B`.

## Main results

* `AlgebraicGeometry.Abhyankar.isPullback_chartU_comp`: the first square.
* `AlgebraicGeometry.Abhyankar.isPullback_chartY_comp`: the second square.

## References

* [Stacks Project, Tag 0EYG](https://stacks.math.columbia.edu/tag/0EYG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Abhyankar

/-- The open range of `Spec A_a ⟶ Spec A` is the basic open `D(a)`. -/
lemma opensRange_SpecMap_away {A : Type u} [CommRing A] (a : A) :
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a)))).opensRange =
      PrimeSpectrum.basicOpen a :=
  TopologicalSpace.Opens.ext (PrimeSpectrum.localization_away_comap_range _ a)

variable {X : Scheme.{u}} (U : X.Opens) {R : CommRingCat.{u}} (ψ : Spec R ⟶ X)
  (φ : R) (hψU : ψ ⁻¹ᵁ U = PrimeSpectrum.basicOpen φ)

include hψU in
/-- The range of `Spec R_φ ⟶ Spec R ⟶ X` is contained in `U`. -/
lemma range_SpecMap_away_comp_subset :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away φ))) ≫ ψ) ⊆
      Set.range U.ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  change (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away φ)))) y ∈ ψ ⁻¹ᵁ U
  rw [hψU, ← opensRange_SpecMap_away]
  exact ⟨y, rfl⟩

/-- The map `Spec R_φ ⟶ U`. -/
def chartU : Spec (.of (Localization.Away φ)) ⟶ U :=
  IsOpenImmersion.lift U.ι (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away φ))) ≫ ψ)
    (range_SpecMap_away_comp_subset U ψ φ hψU)

/-- `chartU` followed by the inclusion `U ⟶ X` is `Spec R_φ ⟶ Spec R ⟶ X`. -/
lemma chartU_ι : chartU U ψ φ hψU ≫ U.ι =
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away φ))) ≫ ψ :=
  IsOpenImmersion.lift_fac _ _ _

/-- `Spec R_φ ⟶ U` is the base change of `U ⊆ X` along `ψ : Spec R ⟶ X`. -/
lemma isPullback_chartU :
    IsPullback (chartU U ψ φ hψU) (Spec.map (CommRingCat.ofHom (algebraMap R _))) U.ι ψ := by
  refine IsOpenImmersion.isPullback _ _ _ _ (chartU_ι U ψ φ hψU).symm ?_
  rw [Scheme.Opens.opensRange_ι, hψU, opensRange_SpecMap_away]

variable (T : Type u) [CommRing T] [Algebra R T]

/-- For an `R`-algebra `T`, `Spec T_φ` is the pullback of `Spec R_φ ⟶ Spec R` along
`Spec T ⟶ Spec R`. -/
lemma isPullback_SpecMap_away :
    IsPullback (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap R T) φ)))
      (Spec.map (CommRingCat.ofHom (algebraMap T (Localization.Away (algebraMap R T φ)))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away φ))))
      (Spec.map (CommRingCat.ofHom (algebraMap R T))) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    change algebraMap T _ (algebraMap R T r) =
      Localization.awayMap (algebraMap R T) φ (algebraMap R _ r)
    exact (IsLocalization.map_eq _ _).symm
  · rw [opensRange_SpecMap_away, opensRange_SpecMap_away]
    ext y
    change φ ∉ (Ideal.comap (algebraMap R T) y.asIdeal) ↔ algebraMap R T φ ∉ y.asIdeal
    rw [Ideal.mem_comap]

/-- **The first square.** For an `R`-algebra `T`, `Spec T_φ ⟶ U` is the base change of `U ⊆ X`
along `Spec T ⟶ Spec R ⟶ X`. -/
lemma isPullback_chartU_comp :
    IsPullback (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap R T) φ)) ≫
        chartU U ψ φ hψU)
      (Spec.map (CommRingCat.ofHom (algebraMap T (Localization.Away (algebraMap R T φ))))) U.ι
      (Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ ψ) :=
  (isPullback_SpecMap_away φ T).paste_horiz (isPullback_chartU U ψ φ hψU)

section Cover

variable {Y : Scheme.{u}} (f : Y ⟶ U) [IsFinite f]

/-- The pullback `Y ×_U Spec R_φ` of a finite morphism is affine. -/
instance : IsAffine (pullback f (chartU U ψ φ hψU)) :=
  isAffine_of_isAffineHom (pullback.snd f (chartU U ψ φ hψU))

/-- The ring map `R_φ → Γ(Y ×_U Spec R_φ)`. -/
def chartRingHom : CommRingCat.of (Localization.Away φ) ⟶
    Γ(pullback f (chartU U ψ φ hψU), ⊤) :=
  Spec.preimage ((pullback f (chartU U ψ φ hψU)).isoSpec.inv ≫ pullback.snd f (chartU U ψ φ hψU))

/-- The ring `B` of the cover over `D(φ)`: `Y ×_U Spec R_φ = Spec B`. -/
abbrev chartRing : Type u := Γ(pullback f (chartU U ψ φ hψU), ⊤)

/-- `B` is an `R_φ`-algebra via `chartRingHom`. -/
instance : Algebra (Localization.Away φ) (chartRing U ψ φ hψU f) :=
  (chartRingHom U ψ φ hψU f).hom.toAlgebra

/-- `Spec B ⟶ Spec R_φ` is the projection `Y ×_U Spec R_φ ⟶ Spec R_φ` under
`Y ×_U Spec R_φ ≅ Spec B`. -/
lemma SpecMap_chartRing :
    Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away φ) (chartRing U ψ φ hψU f))) =
      (pullback f (chartU U ψ φ hψU)).isoSpec.inv ≫ pullback.snd f (chartU U ψ φ hψU) :=
  Spec.map_preimage _

/-- `B` is a finite `R_φ`-algebra. -/
instance : Module.Finite (Localization.Away φ) (chartRing U ψ φ hψU f) := by
  rw [← RingHom.finite_algebraMap]
  apply (IsFinite.SpecMap_iff _).mp
  rw [chartRingHom, Spec.map_preimage]
  infer_instance

/-- If `f` is étale, then `B` is an étale `R_φ`-algebra. -/
instance [Etale f] : Algebra.Etale (Localization.Away φ) (chartRing U ψ φ hψU f) := by
  rw [← RingHom.etale_algebraMap]
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
  rw [chartRingHom, Spec.map_preimage]
  infer_instance

/-- The map `Spec B ⟶ Y`. -/
def chartY : Spec (.of (chartRing U ψ φ hψU f)) ⟶ Y :=
  (pullback f (chartU U ψ φ hψU)).isoSpec.inv ≫ pullback.fst f (chartU U ψ φ hψU)

/-- `Spec B ⟶ Y` is the base change of `f` along `Spec R_φ ⟶ U`. -/
lemma isPullback_chartY :
    IsPullback (chartY U ψ φ hψU f)
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away φ) (chartRing U ψ φ hψU f))))
      f (chartU U ψ φ hψU) := by
  refine (IsPullback.of_hasPullback f (chartU U ψ φ hψU)).of_iso
    (pullback f (chartU U ψ φ hψU)).isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [chartY]
  · simp [SpecMap_chartRing]
  · simp
  · simp

/-- **The second square.** For an `R`-algebra `T`, `Spec (T_φ ⊗_{R_φ} B) ⟶ Y` is the base change
of `f` along `Spec T_φ ⟶ U`. -/
lemma isPullback_chartY_comp :
    letI := (Localization.awayMap (algebraMap R T) φ).toAlgebra
    IsPullback (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          chartRing U ψ φ hψU f →+* Localization.Away (algebraMap R T φ) ⊗[Localization.Away φ]
            chartRing U ψ φ hψU f)) ≫ chartY U ψ φ hψU f)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          Localization.Away (algebraMap R T φ) →+* Localization.Away (algebraMap R T φ) ⊗[
            Localization.Away φ] chartRing U ψ φ hψU f)))
      f (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap R T) φ)) ≫
        chartU U ψ φ hψU) := by
  let := (Localization.awayMap (algebraMap R T) φ).toAlgebra
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct
    (Localization.Away φ) (Localization.Away (algebraMap R T φ))
    (chartRing U ψ φ hψU f))).flip.paste_horiz (isPullback_chartY U ψ φ hψU f)

end Cover

end AlgebraicGeometry.Abhyankar
