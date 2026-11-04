module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CompactPerfectTag
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.PerfectDirectImageLocallySmall
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Comparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.CategoryTheory.Monoidal.ReseatExactPairing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedModelComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-!
# Compact objects of `D_QCoh(𝒪_X)` are dualizable

Let `X` be a quasi-compact quasi-separated scheme. A compact object `K` of `D_QCoh(𝒪_X)` has a
right dual for the monoidal structure `Stacks.Duality.quasiCoherentDerivedMonoidal X` of
[Stacks, Tag 0FPT] and [Stacks, Tag 08DX]: `K` is perfect ([Stacks, Tag 09M1]), the derived dual
`K^∨ = RSheafHom(K, 𝒪_X)` of a perfect object is perfect ([Stacks, Tag 08DQ]), hence lies in
`D_QCoh`, and `(K, K^∨)` is an exact pairing ([Stacks, Tag 0FPC]).

[Stacks, Tag 0FPC] is proved at the model `HasDerivedCategory.standard`, whereas `D_QCoh(𝒪_X)`
and its monoidal structure live at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. The pairing is moved between the two by the
comparison equivalence of the models, which is monoidal for the derived tensor products
(`Stacks.SheafOfModules.DerivedMonoidal.modelEquivMonoidal`).

## Main results

* `Stacks.Duality.isPerfect_modelEquiv_functor_obj_iff` — perfectness is invariant under the
  comparison of two models.
* `Stacks.Duality.nonempty_hasRightDual_of_isCompactObject` — a compact object of `D_QCoh(𝒪_X)`
  has a right dual.

## References

* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory StacksDraft.DerivedModel

universe w w' u

namespace Stacks.Duality

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

/-- **Perfectness does not depend on the model of the derived category.** For two models `h₁`,
`h₂` of `D(𝒪_X)` and `E` in the first, the comparison equivalence carries `E` to a perfect object
iff `E` is perfect. -/
theorem isPerfect_modelEquiv_functor_obj_iff (X : RingedSpace.{u, u})
    (h₁ : HasDerivedCategory.{w} (StrictlyPerfect.OXMod.{u, u} X))
    (h₂ : HasDerivedCategory.{w'} (StrictlyPerfect.OXMod.{u, u} X))
    (E : @DerivedCategory _ _ _ h₁) :
    @Stacks.Cohomology.PerfectComplexes.IsPerfect X h₂ ((modelEquiv h₁ h₂).functor.obj E) ↔
      @Stacks.Cohomology.PerfectComplexes.IsPerfect X h₁ E := by
  let K := (@DerivedCategory.Q _ _ _ h₁).objPreimage E
  let eK : (@DerivedCategory.Q _ _ _ h₁).obj K ≅ E :=
    (@DerivedCategory.Q _ _ _ h₁).objObjPreimageIso E
  let e₂ : (modelEquiv h₁ h₂).functor.obj E ≅ (@DerivedCategory.Q _ _ _ h₂).obj K :=
    (modelEquiv h₁ h₂).functor.mapIso eK.symm ≪≫ (modelCompQIso h₁ h₂).app K
  exact ⟨fun h => @Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso X h₁ _ _ eK
      (Stacks.Cohomology.PerfectComplexes.isPerfect_Q_transfer h₂ h₁ K
        (@Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso X h₂ _ _ e₂ h)),
    fun h => @Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso X h₂ _ _ e₂.symm
      (Stacks.Cohomology.PerfectComplexes.isPerfect_Q_transfer h₁ h₂ K
        (@Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso X h₁ _ _ eK.symm h))⟩

section Standard

attribute [local instance 10000] HasDerivedCategory.standard

/-- **[Stacks, Tag 0FPC] and [Stacks, Tag 08DQ], read for the base structure, at the standard
model.** A perfect object `K` of `D(𝒪_X)` has a perfect left dual — `K^∨ = RSheafHom(K, 𝒪_X)` —
for the monoidal structure `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` of
[Stacks, Tag 0FPT], of which `Stacks.SheafOfModules.derivedMonoidalStructure` is a re-seating. -/
theorem exists_isPerfect_exactPairing_derivedMonoidal (X : RingedSpace.{u, u})
    (K : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf))
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) K) :
    ∃ D : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) D ∧
        Nonempty (@ExactPairing _ _
          (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf) K D) :=
  ⟨Stacks.SheafOfModules.derivedDual X.sheaf K,
    Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace X K hK,
    ⟨@MonoidalCategory.exactPairingOfReseat _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf) _ _
      (Stacks.SheafOfModules.derivedTensorMonoidalIso X.sheaf)
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.sheaf) K _
      (Stacks.SheafOfModules.exactPairingDerivedDual X.sheaf K
        (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X K hK))⟩⟩

end Standard

/-- **A compact object of `D_QCoh(𝒪_Y)` is dualizable.** Let `Y` be a quasi-compact
quasi-separated scheme and `K` a compact object of `D_QCoh(𝒪_Y)`. Then `K` has a right dual for
the monoidal structure `Stacks.Duality.quasiCoherentDerivedMonoidal Y` of `D_QCoh(𝒪_Y)`.

`K` is perfect ([Stacks, Tag 09M1]); at the standard model its derived dual
`K^∨ = RSheafHom(K, 𝒪_Y)` is a left dual ([Stacks, Tag 0FPC]) and is perfect
([Stacks, Tag 08DQ]); the comparison of models is monoidal, so the pairing moves to the locally
small model, where `K^∨`, being perfect, has quasi-coherent cohomology ([Stacks, Tag 08E5]) and the
pairing restricts to the full monoidal subcategory `D_QCoh(𝒪_Y)`. -/
theorem nonempty_hasRightDual_of_isCompactObject (Y : Scheme.{u}) [CompactSpace Y]
    [QuasiSeparatedSpace Y] (K : quasiCoherentDerivedCategory Y) (hK : IsCompactObject.{u} K) :
    Nonempty (@HasRightDual _ _ (quasiCoherentDerivedMonoidal Y) K) := by
  let hstd := HasDerivedCategory.standard Y.Modules
  let hls := Scheme.Modules.hasDerivedCategory Y
  let M := modelEquiv hstd hls
  -- `K`, read at the standard model, is perfect.
  let Kstd : @DerivedCategory Y.Modules _ _ hstd := M.inverse.obj K.obj
  have hKstd : @Stacks.Cohomology.PerfectComplexes.IsPerfect Y.toRingedSpace hstd Kstd :=
    (isPerfect_modelEquiv_functor_obj_iff Y.toRingedSpace hstd hls Kstd).1
      (@Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso Y.toRingedSpace hls _ _
        (M.counitIso.app K.obj).symm (isPerfect_of_isCompactObject K hK))
  -- [Stacks, Tag 0FPC] at the standard model
  obtain ⟨Dstd, hDstd, ⟨pstd⟩⟩ :=
    exists_isPerfect_exactPairing_derivedMonoidal Y.toRingedSpace Kstd hKstd
  -- moved to the locally small model along the monoidal comparison
  let pmap := @ExactPairing.map (@DerivedCategory Y.Modules _ _ hstd)
    (@DerivedCategory Y.Modules _ _ hls) _ _
    (@Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal _ _ _ Y.sheaf _ _ hstd)
    (Scheme.Modules.derivedMonoidal Y) M.functor
    (Stacks.SheafOfModules.DerivedMonoidal.modelEquivMonoidal Y.sheaf hstd hls) Kstd Dstd pstd
  let pls := @MonoidalCategory.exactPairingReseat _ _ (Scheme.Modules.derivedMonoidal Y) _ _
    (@Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso _ _ _ Y.sheaf _ _ hls)
    (@Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso _ _ _ Y.sheaf _ _ hls)
    (M.functor.obj Kstd) (M.functor.obj Dstd) pmap
  let pK := @exactPairingCongrLeft _ _ (Scheme.Modules.canonicalDerivedMonoidal Y) _ _ _ pls
    (M.counitIso.app K.obj).symm
  -- the dual lies in `D_QCoh(𝒪_Y)`
  have hDperf : @Stacks.Cohomology.PerfectComplexes.IsPerfect Y.toRingedSpace hls
      (M.functor.obj Dstd) :=
    (isPerfect_modelEquiv_functor_obj_iff Y.toRingedSpace hstd hls Dstd).2 hDstd
  have hDqc : DerivedCategoryB.derivedCategoryB (A := Y.Modules)
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf) (M.functor.obj Dstd) :=
    isQuasicoherentDerived_of_isPseudoCoherent Y _
      ((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace _).1 hDperf).isPseudoCoherent
  let Kd : quasiCoherentDerivedCategory Y := ⟨M.functor.obj Dstd, hDqc⟩
  let psub := @ExactPairing.ofFullyFaithful _ _ _ _
    (@ObjectProperty.fullMonoidalSubcategory _ _ (Scheme.Modules.canonicalDerivedMonoidal Y) _
      (quasiCoherent_isMonoidal Y))
    (Scheme.Modules.canonicalDerivedMonoidal Y) (ObjectProperty.ι _)
    (@ObjectProperty.monoidalι _ _ (Scheme.Modules.canonicalDerivedMonoidal Y) _
      (quasiCoherent_isMonoidal Y)) _ _ K Kd pK
  exact ⟨@HasRightDual.mk _ _ (quasiCoherentDerivedMonoidal Y) K Kd
    (@MonoidalCategory.exactPairingReseat _ _
      (@ObjectProperty.fullMonoidalSubcategory _ _ (Scheme.Modules.canonicalDerivedMonoidal Y) _
        (quasiCoherent_isMonoidal Y))
      _ _ (quasiCoherentCurriedTensorIso Y) (Iso.refl _) K Kd psub)⟩

end Stacks.Duality

end
