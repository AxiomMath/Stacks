/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.FibreHilbert
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.BaseFieldInvariance
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialPolynomial
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation

/-!
# The fibrewise Hilbert function of a closed subscheme of `ℙⁿ` over a field

Let `T` be a scheme isomorphic to the spectrum of a field `k` and let `i : Z ⟶ ℙⁿ_T` be a
closed immersion. The fibrewise Hilbert function of `i_*𝒪_Z` on `ℙⁿ_T`
(`AlgebraicGeometry.ProjectiveQuot.fibreHilbert`) at the point of `T` is
`d ↦ χ(Z, (i^*𝒪(1))^{⊗ d})`: the fibre over the residue field is the extension of scalars along
`k ⟶ κ(t)`, which does not change Euler characteristics (Stacks 08AB); the twist is moved inside
the direct image by the projection formula and the cohomology of a direct image along the affine
`i` is that of the module (Stacks 01E8, 089W); and `i^*𝒪(d) = (i^*𝒪(1))^{⊗ d}`.

This is the computation of the Hilbert polynomial of a point of `Hilb_{ℙⁿ_U/U}` over a field in
the proof of Stacks 0DSQ.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.fibreHilbert_pushforward_unitModule_eq_eulerSum`.

## References

* [Stacks Project, Tag 08AB](https://stacks.math.columbia.edu/tag/08AB)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
  (isInvertibleModule_twistOver tensorPowModuleProjectiveTwistIso)

namespace AlgebraicGeometry

universe u

namespace ProjectiveQuot

variable {n : ℕ} {T : Scheme.{u}}

open Stacks.Ample in
/-- **The fibrewise Hilbert function of `i_*𝒪_Z` is `d ↦ χ(Z, (i^*𝒪(1))^{⊗ d})`**, for a closed
immersion `i : Z ⟶ ℙⁿ_T` over a base `T` isomorphic to the spectrum of a field `k`. -/
theorem fibreHilbert_pushforward_unitModule_eq_eulerSum (k : Type u) [Field k]
    (e : T ≅ Spec (.of k)) {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOver n T) [IsClosedImmersion i]
    [hfpF : ((Scheme.Modules.pushforward i).obj (unitModule Z)).IsFinitePresentation]
    [hinvL : IsInvertibleModule Z ((Scheme.Modules.pullback i).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n T))]
    (t : T) (d : ℤ) :
    fibreHilbert ((Scheme.Modules.pushforward i).obj (unitModule Z)) t d =
      ProperFlatFibreEulerCharacteristic.eulerSum k ((i ≫ (projectiveSpaceOver n T ↘ T)) ≫ e.hom)
        (tensorPowModule Z ((Scheme.Modules.pullback i).obj
          (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n T)) d) := by
  have hπ : IsProper (projectiveSpaceOver n T ↘ T) := isProper_projectiveSpaceOver n T
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
  have hcohL : (tensorPowModule Z ((Scheme.Modules.pullback i).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n T)) d).IsCoherent :=
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
  have hcohfib'' : (twist d (fibre t ((Scheme.Modules.pushforward i).obj
      (Stacks.Ample.unitModule Z)))).IsCoherent := hcohfib'
  have hproperZ : IsProper ((i ≫ (projectiveSpaceOver n T ↘ T)) ≫ e.hom) := inferInstance
  -- the fibre square over the residue field of `t`
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
  -- `i^*𝒪(d)` is the `d`-th power of `i^*𝒪(1)`
  have eL : (Scheme.Modules.pullback i).obj (twistingSheaf n T d) ≅
      tensorPowModule Z ((Scheme.Modules.pullback i).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n T)) d :=
    (Scheme.Modules.pullback i).mapIso (tensorPowModuleProjectiveTwistIso n T d).symm ≪≫
      Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTensorPowModuleIntIso i
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n T) d
  calc fibreHilbert ((Scheme.Modules.pushforward i).obj (Stacks.Ample.unitModule Z)) t d
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
          (tensorPowModule Z ((Scheme.Modules.pullback i).obj
            (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n T)) d) hcohL :=
        eulerCharacteristic_eq_of_iso _ _ eL
    _ = @eulerCharacteristic k _ Z ((i ≫ (projectiveSpaceOver n T ↘ T)) ≫ e.hom) hproperZ
          (tensorPowModule Z ((Scheme.Modules.pullback i).obj
            (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n T)) d) hcohL :=
        eulerCharacteristic_congr_structureMorphism k
          (Category.assoc i (projectiveSpaceOver n T ↘ T) e.hom).symm _ hproperZ _ hcohL
    _ = _ := rfl

end ProjectiveQuot

end AlgebraicGeometry

end
