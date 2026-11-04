/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.IdealSheafRestrict.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertUniversalFamily
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.FibreHilbert
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.BaseFieldInvariance
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation

/-!
# Reading a closed subscheme of `Pn_U` back as a member of `Quot^P`

Let `U` be a scheme of the big fppf site, `k` a field and `e` an isomorphism of `U` with
`Spec k`, and let `i : Z -> Pn_U` be a closed immersion whose composite to `U` is flat and of
finite presentation. If the polarized family `(Z, OO(1)|_Z)` of
`AlgebraicGeometry.hilbertPolarizedFamily` has Hilbert polynomial `P`, then `i` cuts out a member
of `Quot^P_{OO/Pn/Z}(U)` (`AlgebraicGeometry.ProjectiveQuot.hilbertFamilies`) whose quotient is
`i_* OO_Z`.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.unitProjection`: the projection `OO^{+1} -> i_* OO_Z` on
  `Pn_T` attached to a morphism `i : Z -> Pn_T`.
* `AlgebraicGeometry.ProjectiveQuot.familyOfClosedImmersion`: its kernel, as a subobject of
  `OO^{+1}`.
* `AlgebraicGeometry.ProjectiveQuot.quotientFamilyOfClosedImmersionIso`: the quotient by that
  subobject is `i_* OO_Z`.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.epi_structureMap`: the structure-sheaf map `OO_X -> i_* OO_Z`
  of a closed immersion is an epimorphism.
* `AlgebraicGeometry.ProjectiveQuot.fibreHilbert_pushforward_unitModule`: over a base isomorphic
  to the spectrum of a field, the fibrewise Hilbert function of `i_* OO_Z` is the Hilbert function
  of the polarization `OO(1)|_Z` of `Z`.
* `AlgebraicGeometry.hilbertFamilies_of_polarizedHilbertFunction`: a closed subscheme of `Pn_U`,
  flat and of finite presentation over `U` and with `OO(1)|_Z` of Hilbert polynomial `P`, is a
  member of `Quot^P_{OO/Pn/Z}(U)`, with `i_* OO_Z` as its quotient.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 08AB](https://stacks.math.columbia.edu/tag/08AB)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0D3W](https://stacks.math.columbia.edu/tag/0D3W)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0E96](https://stacks.math.columbia.edu/tag/0E96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ClosedImmersionTFAE (isLocallySurjective_c_of_isClosedImmersion)
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
  (isInvertibleModule_twistOver tensorPowModuleProjectiveTwistIso)

namespace AlgebraicGeometry

universe u

namespace ProjectiveQuot

variable {n : ℕ} {T : Scheme.{u}}

/-- The structure-sheaf map of a closed immersion is an epimorphism. -/
theorem epi_structureMap {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Epi (Stacks.IdealSheafRestrict.structureMap i) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    ⟨fun {_} s ↦ (isLocallySurjective_c_of_isClosedImmersion i).imageSieve_mem s⟩

/-- The projection `𝒪^{⊕ 1} ⟶ i_* 𝒪_Z` attached to `i : Z ⟶ ℙⁿ_T`. -/
def unitProjection {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOver n T) :
    freeModule n 1 T ⟶ (Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z) :=
  (freeModuleOneIso n T).hom ≫ Stacks.IdealSheafRestrict.structureMap i

/-- `AlgebraicGeometry.ProjectiveQuot.unitProjection` is an epimorphism for a closed
immersion. -/
theorem epi_unitProjection {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOver n T)
    [IsClosedImmersion i] : Epi (unitProjection i) :=
  @epi_comp _ _ _ _ _ _ inferInstance _ (epi_structureMap i)

/-- The member of `Quot_{𝒪/ℙⁿ/ℤ}(T)` read off a closed immersion `i : Z ⟶ ℙⁿ_T`. -/
def familyOfClosedImmersion {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOver n T) :
    Subobject (freeModule n 1 T) :=
  Subobject.mk (SheafOfModules.Submodule.ker (unitProjection i)).ι

/-- The quotient by that member is `i_* 𝒪_Z`. -/
def quotientFamilyOfClosedImmersionIso {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOver n T)
    [IsClosedImmersion i] :
    quotient (familyOfClosedImmersion i) ≅
      (Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z) :=
  (Stacks.AlgebraicGeometry.Tag01YHTopIdeals.cokernelIsoOfIsoComp
        (Subobject.underlyingIso (SheafOfModules.Submodule.ker (unitProjection i)).ι).symm
        (SheafOfModules.Submodule.ker (unitProjection i)).ι
        (familyOfClosedImmersion i).arrow
        (Subobject.underlyingIso_hom_comp_eq_mk
          (SheafOfModules.Submodule.ker (unitProjection i)).ι)).symm ≪≫
    @Stacks.LefschetzCone.cokernelIsoOfEqKer _ _ _ (unitProjection i) (epi_unitProjection i) _ rfl

/-- Over a base `T` isomorphic to `Spec k`, the fibrewise Hilbert function of `i_* 𝒪_Z` at `t`
is the Hilbert function of `𝒪(1)|_Z`: its value at `d` is the Euler characteristic over `k` of
the `d`-th tensor power of `i^* 𝒪(1)`. -/
theorem fibreHilbert_pushforward_unitModule (k : Type u) [Field k] (e : T ≅ Spec (.of k))
    {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOver n T) [IsClosedImmersion i]
    (hfpF : ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)).IsFinitePresentation)
    (t : T) (d : ℤ)
    (hproperZ : IsProper ((i ≫ (projectiveSpaceOver n T ↘ T)) ≫ e.hom))
    (hinvL : AlgebraicGeometry.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property ((Scheme.Modules.pullback i).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n T)))
    (hcohL : (@Scheme.Modules.tensorPowerModules Z ((Scheme.Modules.pullback i).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n T)) hinvL d).IsCoherent) :
    @fibreHilbert n T ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) hfpF t d =
      @eulerCharacteristic k _ Z ((i ≫ (projectiveSpaceOver n T ↘ T)) ≫ e.hom) hproperZ
        (@Scheme.Modules.tensorPowerModules Z _ hinvL d) hcohL := by
  have := hfpF
  have := hinvL
  have hln : IsLocallyNoetherian (projectiveSpaceOver n T) :=
    LocallyOfFiniteType.isLocallyNoetherian ((projectiveSpaceOver n T ↘ T) ≫ e.hom)
  have hlnZ : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  have hcohZ : (Stacks.Ample.unitModule Z).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit Z
  have hcohF : ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion i _
  have hinvE : AlgebraicGeometry.SheafOfModules.IsInvertible
      (projectiveSpaceOver n T).presheaf (projectiveSpaceOver n T).ringCatSheaf.2
      (twistingSheaf n T d) :=
    (isInvertibleModule_twistOver n T d).toAlgebraicGeometry
  have hcohE : (twistingSheaf n T d).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible _ _
  have hinvpE : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      ((Scheme.Modules.pullback i).obj (twistingSheaf n T d)) :=
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback i.toLRSHom.toShHom _
  have hcohpE : ((Scheme.Modules.pullback i).obj (twistingSheaf n T d)).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible _ _
  have hcohtw : (twist d ((Scheme.Modules.pushforward i).obj
      (Stacks.Ample.unitModule Z))).IsCoherent :=
    @SheafOfModules.tensorSheaf_isCoherent (projectiveSpaceOver n T).toRingedSpace _ _ hcohF hcohE
  have hfptw : (twist d ((Scheme.Modules.pushforward i).obj
      (Stacks.Ample.unitModule Z))).IsFinitePresentation :=
    isFinitePresentation_twist d _ hfpF
  have hcohfib : (fibre t (twist d ((Scheme.Modules.pushforward i).obj
      (Stacks.Ample.unitModule Z)))).IsCoherent := isCoherent_fibre t _
  have hcohfib' : (projectiveTwist n (fibre t ((Scheme.Modules.pushforward i).obj
      (Stacks.Ample.unitModule Z))) d).IsCoherent :=
    isCoherent_of_isFinitePresentation_projectiveSpace _
      (twist d (fibre t ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))))
  let : Algebra k (T.residueField t) :=
    (Spec.preimage (T.fromSpecResidueField t ≫ e.hom)).hom.toAlgebra
  have hspec : specMapAlgebraMap k (T.residueField t) = T.fromSpecResidueField t ≫ e.hom := by
    rw [specMapAlgebraMap, RingHom.algebraMap_toAlgebra]
    exact Spec.map_preimage _
  have hsq : IsPullback (fibreMap n t)
      (projectiveSpaceOverRing n (.of (T.residueField t)) ↘ Spec (.of (T.residueField t)))
      ((projectiveSpaceOver n T ↘ T) ≫ e.hom) (specMapAlgebraMap k (T.residueField t)) := by
    rw [hspec]
    have h2 : IsPullback (𝟙 (projectiveSpaceOver n T)) (projectiveSpaceOver n T ↘ T)
        ((projectiveSpaceOver n T ↘ T) ≫ e.hom) e.hom := IsPullback.of_horiz_isIso ⟨by simp⟩
    have h := (isPullback_projectiveSpaceOverMap n (T.fromSpecResidueField t)).paste_horiz h2
    simp only [Category.comp_id] at h
    exact h
  have hbc := eulerCharacteristic_baseChange_field k (T.residueField t) (fibreMap n t)
    (projectiveSpaceOverRing n (.of (T.residueField t)) ↘ Spec (.of (T.residueField t)))
    ((projectiveSpaceOver n T ↘ T) ≫ e.hom) hsq
    (twist d ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)))
  have eL : (Scheme.Modules.pullback i).obj (twistingSheaf n T d) ≅
      @Scheme.Modules.tensorPowerModules Z ((Scheme.Modules.pullback i).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n T)) hinvL d :=
    (Scheme.Modules.pullback i).mapIso
        (tensorPowModuleProjectiveTwistIso n T d).symm ≪≫
      Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso i
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n T) d ≪≫
      (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso Z
        ((Scheme.Modules.pullback i).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n T)) d).symm
  calc @fibreHilbert n T ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) hfpF t d
      = eulerCharacteristic (T.residueField t)
          (projectiveSpaceOverRing n (.of (T.residueField t)) ↘ Spec (.of (T.residueField t)))
          (projectiveTwist n (fibre t ((Scheme.Modules.pushforward i).obj
            (Stacks.Ample.unitModule Z))) d) := rfl
    _ = eulerCharacteristic (T.residueField t)
          (projectiveSpaceOverRing n (.of (T.residueField t)) ↘ Spec (.of (T.residueField t)))
          ((Scheme.Modules.pullback (fibreMap n t)).obj
            (twist d ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)))) :=
        eulerCharacteristic_eq_of_iso _ _
          (twistPullbackIso (T.fromSpecResidueField t) d
            ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)))
    _ = eulerCharacteristic k ((projectiveSpaceOver n T ↘ T) ≫ e.hom)
          (twist d ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z))) := hbc.symm
    _ = @eulerCharacteristic k _ Z (i ≫ ((projectiveSpaceOver n T ↘ T) ≫ e.hom)) _
          ((Scheme.Modules.pullback i).obj (twistingSheaf n T d)) _ :=
        eulerCharacteristic_tensorSheaf_pushforward_unit_of_isClosedImmersion k i
          ((projectiveSpaceOver n T ↘ T) ≫ e.hom) (twistingSheaf n T d) hcohE hcohZ hcohF hcohpE
    _ = @eulerCharacteristic k _ Z (i ≫ ((projectiveSpaceOver n T ↘ T) ≫ e.hom)) _
          (@Scheme.Modules.tensorPowerModules Z _ hinvL d) hcohL :=
        eulerCharacteristic_eq_of_iso _ _ eL
    _ = @eulerCharacteristic k _ Z ((i ≫ (projectiveSpaceOver n T ↘ T)) ≫ e.hom) hproperZ
          (@Scheme.Modules.tensorPowerModules Z _ hinvL d) hcohL :=
        eulerCharacteristic_congr_structureMorphism k
          (Category.assoc i (projectiveSpaceOver n T ↘ T) e.hom).symm _ hproperZ _ hcohL

end ProjectiveQuot

variable (B : BigFppfSite.{u})

/-- A closed subscheme of `ℙⁿ_U` whose polarization has Hilbert polynomial `P` is a member of
`Quot^P_{𝒪/ℙⁿ/ℤ}(U)`. Let `U` be a scheme of the big fppf site, let `k` be a field with an
isomorphism `e` of `U` with `Spec k`, and let `i : Z ⟶ ℙⁿ_U` be a closed immersion whose
composite to `U` is flat and of finite presentation. If the Hilbert function of the polarized
family `(Z, 𝒪(1)|_Z)` of `AlgebraicGeometry.hilbertPolarizedFamily` takes the values of `P`, then
`i` cuts out a member `K` of `Quot^P_{𝒪/ℙⁿ/ℤ}(U)` whose quotient is `i_* 𝒪_Z`. -/
theorem hilbertFamilies_of_polarizedHilbertFunction
    {n : ℕ} (U : B.Schemes) (k : Type u) [Field k] (e : B.inclusion.obj U ≅ Spec (.of k))
    {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOver n (B.inclusion.obj U)) [IsClosedImmersion i]
    (hfl : Flat (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U)))
    (hfp : FinitePresentation
      (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U)))
    (P : Polynomial ℚ)
    (hP : ∀ d : ℤ, (polarizedHilbertFunction (hilbertPolarizedFamily n U i hfl hfp) k e d : ℚ)
      = P.eval (d : ℚ)) :
    ∃ K : Subobject (ProjectiveQuot.freeModule n 1 (B.inclusion.obj U)),
      K ∈ ProjectiveQuot.hilbertFamilies n 1 P (B.inclusion.obj U) ∧
        Nonempty ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z) ≅
          ProjectiveQuot.quotient K) := by
  have hln : IsLocallyNoetherian (projectiveSpaceOver n (B.inclusion.obj U)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      ((projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U) ≫ e.hom)
  have := hfl
  have hlnZ : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  have hcohF : ((Scheme.Modules.pushforward i).obj
      (Stacks.Ample.unitModule Z)).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion i _
  have hfpF : ((Scheme.Modules.pushforward i).obj
      (Stacks.Ample.unitModule Z)).IsFinitePresentation :=
    _root_.isFinitePresentation_of_isCoherent _
  refine ⟨ProjectiveQuot.familyOfClosedImmersion i,
    ⟨ProjectiveQuotOverSpace.isFlatFamily_of_iso
      (ProjectiveQuot.quotientFamilyOfClosedImmersionIso i).symm
      ⟨hfpF, Stacks.Chow.isFlatOver_pushforwardStructureSheaf i _⟩, ?_⟩,
    ⟨(ProjectiveQuot.quotientFamilyOfClosedImmersionIso i).symm⟩⟩
  have hfpQ : (ProjectiveQuot.quotient
      (ProjectiveQuot.familyOfClosedImmersion i)).IsFinitePresentation :=
    SheafOfModules.IsFinitePresentation.of_iso hfpF
      (ProjectiveQuot.quotientFamilyOfClosedImmersionIso i).symm
  have hpx : IsProper (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U)) :=
    (hilbertPolarizedFamily n U i hfl hfp).proper
  have hpZ : IsProper
      ((i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U)) ≫ e.hom) :=
    inferInstance
  have hinvL : AlgebraicGeometry.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (structureSheafRing Z.toRingedSpace).property ((Scheme.Modules.pullback i).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (B.inclusion.obj U))) :=
    (hilbertPolarizedFamily n U i hfl hfp).invertible
  have hcohL : ∀ d : ℤ, (@Scheme.Modules.tensorPowerModules Z _ hinvL d).IsCoherent := fun d =>
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Z _
  rw [ProjectiveQuot.hasFibreHilbertPolynomial_iff]
  intro t d
  rw [ProjectiveQuot.fibreHilbert_eq_of_iso
      (ProjectiveQuot.quotientFamilyOfClosedImmersionIso i) t,
    ProjectiveQuot.fibreHilbert_pushforward_unitModule k e i hfpF t d hpZ hinvL (hcohL d)]
  exact hP d

end AlgebraicGeometry

end
