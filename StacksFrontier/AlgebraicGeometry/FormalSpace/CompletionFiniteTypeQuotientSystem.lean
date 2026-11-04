module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteType
import all StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteType

/-!
# The quotient system of a relative completion, with no size hypothesis on the site

Let `B` be a weakly admissible topological ring with a quotient system `D` over a scheme `S`
in a big fppf site, and let `f : B → A` be a ring map of finite type. The stages of the
relative completion `A^` are the spectra of the quotients `A / JA`, and these lie in the site
because `Spec (B / J)` does and `B / J → A / JA` is of finite type. So the relative completion
carries a quotient system over `S` with a continuous map from `D` whose underlying ring map is
the canonical one, with no size hypothesis on the site: this is Stacks 0ANM without the
large-site hypothesis of `AlgebraicGeometry.FormalSpace.exists_completionOver_quotientSystem`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_completionOver_quotientSystem_of_finiteType`: the
  quotient system and continuous map of the relative completion, for any site.

## References

* [Stacks Project, Tag 0ANM](https://stacks.math.columbia.edu/tag/0ANM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

section QuotientSystem

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A]

variable (𝔅 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝔅.Contains S)

/-- The spectra of the quotients `A / JA` lie in the site as soon as `f` is of finite type: the
spectrum of `B / J` lies in it, being a stage of the quotient system of `B`. -/
private theorem baseStage_inSite (f : B →+* A)
    (hf : letI : Algebra B A := f.toAlgebra; Algebra.FiniteType B A)
    (D : QuotientSystem 𝔅 S hS B) (J : TopologicalRing.WeakIdealOfDefinitionIndex B) :
    𝔅.Contains (Spec (.of (A ⧸ TopologicalRing.extendedIdeal f J))) := by
  let : Algebra (B ⧸ J.1) (A ⧸ TopologicalRing.extendedIdeal f J) :=
    (baseStageMap f J).toAlgebra
  let : Algebra.FiniteType (B ⧸ J.1) (A ⧸ TopologicalRing.extendedIdeal f J) :=
    RingHom.finiteType_algebraMap.mp (baseStageMap_finiteType f hf J)
  exact Scheme.size_Spec_lt_of_finiteType 𝔅.aleph0_lt_cutoff 𝔅.cutoff_isStrongPrelimit
    (B ⧸ J.1) (A ⧸ TopologicalRing.extendedIdeal f J) (D.inSite J)

/-- Composing `Spec.map` of two ring maps with `g` only depends on the composite ring map. -/
private theorem spec_map_comp_assoc_eq {P Q R : Type u} [CommRing P] [CommRing Q] [CommRing R]
    {Y : Scheme.{u}} (g : Spec (.of P) ⟶ Y) {q₁ : Q →+* R} {q₂ : P →+* Q} {q₃ : P →+* R}
    (h : q₁.comp q₂ = q₃) :
    Spec.map (CommRingCat.ofHom q₁) ≫ Spec.map (CommRingCat.ofHom q₂) ≫ g =
      Spec.map (CommRingCat.ofHom q₃) ≫ g := by
  subst h
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- The quotient system of the relative completion: its stage at a weak ideal of definition
`K` is `Spec` of the quotient, mapping to the base through the stage of a weak ideal of
definition `J` of `B` with `ker (A^ → A/JA) ⊆ K`. -/
private noncomputable def completionOverQuotientSystemOfFiniteType
    [IsTopologicalRing B] [IsLinearTopology B B]
    (f : B →+* A) (hf : letI : Algebra B A := f.toAlgebra; Algebra.FiniteType B A)
    (hB : TopologicalRing.IsWeaklyAdmissible B) (D : QuotientSystem 𝔅 S hS B) :
    QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f) where
  inSite K := by
    let : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (quotientStageMap f (sourceWeakIdeal f hB K) K.1
          (ker_projection_sourceWeakIdeal_le f hB K)))) :=
      IsClosedImmersion.spec_of_surjective _
        (quotientStageMap_surjective f (sourceWeakIdeal f hB K) K.1
          (ker_projection_sourceWeakIdeal_le f hB K))
    exact Scheme.size_lt_of_isClosedImmersion
      (Spec.map (CommRingCat.ofHom
        (quotientStageMap f (sourceWeakIdeal f hB K) K.1
          (ker_projection_sourceWeakIdeal_le f hB K))))
      (baseStage_inSite 𝔅 S hS f hf D (sourceWeakIdeal f hB K))
  overS K :=
    Spec.map (CommRingCat.ofHom
      ((quotientStageMap f (sourceWeakIdeal f hB K) K.1
        (ker_projection_sourceWeakIdeal_le f hB K)).comp
          (baseStageMap f (sourceWeakIdeal f hB K)))) ≫
      D.overS (sourceWeakIdeal f hB K)
  compatible := by
    intro K L hKL
    set I := sourceWeakIdeal f hB K with hI
    set I' := sourceWeakIdeal f hB L with hI'
    have hMI : (weakInf I I').1 ≤ I.1 := inf_le_left
    have hMI' : (weakInf I I').1 ≤ I'.1 := inf_le_right
    have hML : RingHom.ker (TopologicalRing.CompletionOver.projection f (weakInf I I')) ≤
        L.1 := (TopologicalRing.ker_projection_mono f hMI').trans
          (ker_projection_sourceWeakIdeal_le f hB L)
    set qIK := (quotientStageMap f I K.1
      (ker_projection_sourceWeakIdeal_le f hB K)).comp (baseStageMap f I) with hqIK
    set qI'L := (quotientStageMap f I' L.1
      (ker_projection_sourceWeakIdeal_le f hB L)).comp (baseStageMap f I') with hqI'L
    set qML := (quotientStageMap f (weakInf I I') L.1 hML).comp
      (baseStageMap f (weakInf I I')) with hqML
    have hcompK : (Ideal.Quotient.factor hKL).comp
        (qIK.comp (Ideal.Quotient.factor hMI)) = qML := by ext b; rfl
    have hcompL : qI'L.comp (Ideal.Quotient.factor hMI') = qML := by ext b; rfl
    have hcompKScheme := spec_map_comp_assoc_eq (D.overS (weakInf I I')) hcompK
    change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hKL)) ≫
        Spec.map (CommRingCat.ofHom qIK) ≫ D.overS I =
      Spec.map (CommRingCat.ofHom qI'L) ≫ D.overS I'
    rw [← D.compatible (weakInf I I') I hMI, ← D.compatible (weakInf I I') I' hMI']
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] at hcompKScheme
    exact hcompKScheme.trans
      (spec_map_comp_assoc_eq (D.overS (weakInf I I')) hcompL).symm

/-- The canonical continuous map from the base to the relative completion, as a morphism of
quotient systems over `S`. -/
private noncomputable def completionOverContinuousHom
    [IsTopologicalRing B] [IsLinearTopology B B]
    (f : B →+* A) (hf : letI : Algebra B A := f.toAlgebra; Algebra.FiniteType B A)
    (hB : TopologicalRing.IsWeaklyAdmissible B) (D : QuotientSystem 𝔅 S hS B) :
    ContinuousHom D (completionOverQuotientSystemOfFiniteType 𝔅 S hS f hf hB D) where
  toRingHom := TopologicalRing.CompletionOver.canonicalMap f
  continuous := TopologicalRing.continuous_canonicalMap f
  overS := by
    intro J K hJK
    set I := sourceWeakIdeal f hB K with hI
    have hMJ : (weakInf J I).1 ≤ J.1 := inf_le_left
    have hMI : (weakInf J I).1 ≤ I.1 := inf_le_right
    have hMK : RingHom.ker (TopologicalRing.CompletionOver.projection f (weakInf J I)) ≤ K.1 :=
      (TopologicalRing.ker_projection_mono f hMI).trans
        (ker_projection_sourceWeakIdeal_le f hB K)
    set qJK := Ideal.quotientMap K.1 (TopologicalRing.CompletionOver.canonicalMap f) hJK
      with hqJK
    set qIK := (quotientStageMap f I K.1
      (ker_projection_sourceWeakIdeal_le f hB K)).comp (baseStageMap f I) with hqIK
    set qMK := (quotientStageMap f (weakInf J I) K.1 hMK).comp
      (baseStageMap f (weakInf J I)) with hqMK
    have hcompJ : qJK.comp (Ideal.Quotient.factor hMJ) = qMK := by ext b; rfl
    have hcompI : qIK.comp (Ideal.Quotient.factor hMI) = qMK := by ext b; rfl
    change Spec.map (CommRingCat.ofHom qJK) ≫ D.overS J =
      Spec.map (CommRingCat.ofHom qIK) ≫ D.overS I
    rw [← D.compatible (weakInf J I) J hMJ, ← D.compatible (weakInf J I) I hMI]
    exact (spec_map_comp_assoc_eq (D.overS (weakInf J I)) hcompJ).trans
      (spec_map_comp_assoc_eq (D.overS (weakInf J I)) hcompI).symm

/-- **Stacks 0ANM**, with no size hypothesis on the site. A finite type ring map out of a
weakly admissible topological ring over `S` gives the relative completion a quotient system
over `S` and a continuous map from the base whose underlying ring map is the canonical one.
The stages `Spec (A / JA)` lie in the site because `Spec (B / J)` does and `B / J → A / JA` is
of finite type. -/
@[stacks 0ANM "the induced quotient system and continuous map of the relative completion, \
with no size hypothesis on the site"]
theorem exists_completionOver_quotientSystem_of_finiteType
    [IsTopologicalRing B] [IsLinearTopology B B]
    (f : B →+* A) (hf : letI : Algebra B A := f.toAlgebra; Algebra.FiniteType B A)
    (hB : TopologicalRing.IsWeaklyAdmissible B) (D : QuotientSystem 𝔅 S hS B) :
    ∃ (E : QuotientSystem 𝔅 S hS (TopologicalRing.CompletionOver f))
      (g : ContinuousHom D E),
      g.toRingHom = TopologicalRing.CompletionOver.canonicalMap f :=
  ⟨completionOverQuotientSystemOfFiniteType 𝔅 S hS f hf hB D,
    completionOverContinuousHom 𝔅 S hS f hf hB D, rfl⟩

end QuotientSystem

end AlgebraicGeometry.FormalSpace

end
