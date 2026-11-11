module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatUntensoredBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMapTransport
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for the derived pushforward along a proper morphism, at the canonical map

Let `f : X ⟶ S` be a proper morphism of finite presentation and consider a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

[Stacks, Tag 0B91] says that in each of its two clauses `Rf_*` of the given object is perfect and
that its formation commutes with arbitrary base change. This file proves the **base-change half
of both clauses at the canonical map**, with nothing granted:

1. for `f` flat and `E ∈ D(𝒪_X)` perfect, the derived base-change map of [Stacks, Tag 08HY]
   `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` is an isomorphism;
2. for an `𝒪_X`-module `𝒢` of finite presentation, flat over `S`, the map
   `Lg^*Rf_*𝒢 ⟶ Rf'_*L(g')^*𝒢 ⟶ Rf'_*(g')^*𝒢`, the map of [Stacks, Tag 08HY] followed by the
   derived-to-ordinary comparison, is an isomorphism.

It also proves the tensor forms of the two base-change halves, at the canonical map
`AlgebraicGeometry.tensorFlatBaseChangeMap` of [Stacks, Tag 0A1D].

The perfection half of clause (1) — `Rf_*E` perfect for `E` perfect and `f` flat — is
`AlgebraicGeometry.isPerfect_derivedPushforward_of_flat_of_isProper`; the perfection half of
clause (2) is `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.perfectDerivedPushforward`.
Both clauses in full, the statement registered as [Stacks, Tag 0B91], are
`ProperFlatBaseChange.isPerfect_derivedPushforward_and_isIso_baseChange_of_isProper`.

## Main results

* `AlgebraicGeometry.ProperFlatBaseChange.isIso_derivedBaseChangeMap_of_flat`: the map of
  [Stacks, Tag 08HY] is invertible for `f` flat, quasi-compact and quasi-separated, at every `E`
  such that `E` and `L(g')^*E` have quasi-coherent cohomology.
* `AlgebraicGeometry.ProperFlatBaseChange.isIso_derivedBaseChangeMap_of_isPerfect`:
  **[Stacks, Tag 0B91], clause (1), the base-change half.**
* `…ProperFlatBaseChange.isIso_derivedBaseChangeComp_singleDegree_of_isFinitePresentation`:
  **[Stacks, Tag 0B91], clause (2), the base-change half.**
* `AlgebraicGeometry.ProperFlatBaseChange.isIso_tensorFlatBaseChangeMap_structure_of_isPerfect`:
  the tensor form of the base-change half of clause (1), with nothing granted.
* `…ProperFlatBaseChange.isIso_tensorFlatBaseChangeMap_module_of_isFinitePresentation`: the
  tensor form of the base-change half of clause (2), at the clause's `E = 𝒪_X`, with nothing
  granted.

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0A1D](https://stacks.math.columbia.edu/tag/0A1D)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.Cohomology.DerivedBaseChangeComparison (baseChangeTensorComparison)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.ProperFlatBaseChange

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- `𝒪_X` placed in degree zero, as the complex `singleDegreeComplex 𝒪_X` that
`AlgebraicGeometry.tensorFlatBaseChangeMap` is evaluated at in clause (1) of [Stacks, Tag 0B91]. -/
abbrev structureDegreeComplex (X : Scheme.{u}) : CochainComplex X.Modules ℤ :=
  singleDegreeComplex (StrictlyPerfect.structureModule X.toRingedSpace : X.Modules)

/-- A module placed in degree zero is a bounded-above complex. -/
theorem minus_singleDegreeComplex (M : X.Modules) :
    CochainComplex.minus X.Modules (singleDegreeComplex M) :=
  ⟨0, inferInstance⟩

/-- A perfect object of `D(𝒪_X)` has quasi-coherent cohomology: it is pseudo-coherent, and
[Stacks, Tag 08E5] applies. -/
theorem isQuasicoherent_homology_of_isPerfect (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) (n : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent :=
  isQuasicoherentDerived_of_isPseudoCoherent X E
    (RingedSpace.IsPerfect.isPseudoCoherent (X := X.toRingedSpace) hE) n

/-- The unit constraint `E ⊗^L_{𝒪_X} 𝒪_X ≅ E` of [Stacks, Tag 0FPT], with `𝒪_X` written as the
complex `singleDegreeComplex 𝒪_X`. -/
def tensorStructureDegreeComplexIso (E : DerivedCategory X.Modules) :
    ((derivedTensorProductFunctor X.sheaf).obj E).obj
      (DerivedCategory.Q.obj (structureDegreeComplex X)) ≅ E :=
  ((derivedTensorProductFunctor X.sheaf).obj E).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _).symm ≪≫
    Stacks.RingedSpace.derivedTensorRightUnitIso X.toRingedSpace E

/-- The comparison `L(g')^*(E ⊗^L 𝒪_X) ⟶ L(g')^*E ⊗^L (g')^*𝒪_X` of [Stacks, Tag 0DJA], taken at
the derived-to-ordinary comparison for `𝒪_X[0]`, is an isomorphism: the first factor is the
monoidality isomorphism of [Stacks, Tag 079U], and the second is invertible because `𝒪_X[0]` is
K-flat. -/
theorem isIso_baseChangeTensorComparison_structure (h : X' ⟶ X) (E : DerivedCategory X.Modules) :
    IsIso (baseChangeTensorComparison h.toLRSHom.toShHom E
      (DerivedCategory.Q.obj (structureDegreeComplex X))
      (DerivedCategory.Q.obj ((pullbackComplex h.toLRSHom.toShHom).obj (structureDegreeComplex X)))
      ((derivedPullbackNatTrans h.toLRSHom.toShHom).app (structureDegreeComplex X))) := by
  have hφ : IsIso ((derivedPullbackNatTrans h.toLRSHom.toShHom).app (structureDegreeComplex X)) :=
    Stacks.Cohomology.DerivedPullbackTensor.isIso_derivedPullbackNatTrans_app
      h.toLRSHom.toShHom _ (Stacks.SheafOfModules.isKFlat_single_unit _)
  refine IsIso.comp_isIso' ?_ ?_
  · exact ((Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
      h.toLRSHom.toShHom).app _).isIso_hom
  · exact (((derivedTensorProductFunctor X'.sheaf).obj
      ((derivedPullback h.toLRSHom.toShHom).obj E)).mapIso (@asIso _ _ _ _ _ hφ)).isIso_hom

/-- **The derived base-change map of [Stacks, Tag 08HY] is invertible along a flat morphism.**
For a cartesian square with `f` flat, quasi-compact and quasi-separated, and an object `E` of
`D(𝒪_X)` such that `E` and `L(g')^*E` have quasi-coherent cohomology, the canonical map
`Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` is an isomorphism. -/
theorem isIso_derivedBaseChangeMap_of_flat (hsq : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiSeparated f] [Flat f] (E : DerivedCategory X.Modules)
    (hE : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj E).IsQuasicoherent)
    (hE' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj
      ((derivedPullback g'.toLRSHom.toShHom).obj E)).IsQuasicoherent) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom (comp_toShHom_of_comm hsq.w) E) := by
  rw [← derivedBaseChangeComp_id]
  refine isIso_derivedBaseChangeComp_of_pointwiseBaseChange hsq E _ (𝟙 _) hE hE' ?_
  have h₀ : PointwiseBaseChangeIsIso f g f' g' hsq.w
      (DerivedCategory.Q.obj (structureDegreeComplex X))
      (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj (structureDegreeComplex X)))
      ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (structureDegreeComplex X)) :=
    fun x' n => isIso_baseChangeCohomologyMap_derivedPullbackNatTrans_of_isFlatOver hsq hsq.w
      _ (minus_singleDegreeComplex _) (isFlatOver_singleDegreeComplex f _
        (Stacks.Cohomology.PerfectPushforward.isFlatOver_structureModule f)) x' n
  have h₁ := pointwiseBaseChangeTensor f g f' g' hsq hsq.w E _ _ _ h₀
  let ρ := tensorStructureDegreeComplexIso E
  let e := (derivedPullback g'.toLRSHom.toShHom).mapIso ρ.symm ≪≫
    @asIso _ _ _ _ _ (isIso_baseChangeTensorComparison_structure g' E)
  intro x' n
  have h₂ := (isIso_baseChangeCohomologyMap_iff_of_isIso_source f g f' g' hsq.w E _ _ ρ.inv
    (Iso.isIso_inv ρ) _ x' n).2 (h₁ x' n)
  have h₃ := (isIso_baseChangeCohomologyMap_iff_of_isIso_target f g f' g' hsq.w E _ _ e.hom e.inv
    e.isIso_inv x' n).2 h₂
  exact cast (congrArg (fun φ => IsIso (baseChangeCohomologyMap f g f' g' hsq.w E _ φ x' n))
    e.hom_inv_id) h₃

/-- Let `f : X ⟶ S` be flat, proper and of finite presentation and let `E` be a perfect object
of `D(𝒪_X)`. For every cartesian square, the formation of `Rf_*E` commutes with base change: the
canonical map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of [Stacks, Tag 08HY] is an isomorphism.

Only quasi-compactness and quasi-separatedness of `f` are used, besides flatness, so the
statement is made under those; a proper morphism of finite presentation has both. That `Rf_*E`
is perfect is `AlgebraicGeometry.isPerfect_derivedPushforward_of_flat_of_isProper`; the whole of
[Stacks, Tag 0B91] is `isPerfect_derivedPushforward_and_isIso_baseChange_of_isProper`. -/
theorem isIso_derivedBaseChangeMap_of_isPerfect (hsq : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiSeparated f] [Flat f] (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom (comp_toShHom_of_comm hsq.w) E) :=
  isIso_derivedBaseChangeMap_of_flat hsq E (isQuasicoherent_homology_of_isPerfect E hE)
    (isQuasicoherent_homology_of_isPerfect _
      (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback g'.toLRSHom.toShHom E hE))

/-- Let `f : X ⟶ S` be proper of finite presentation and let `𝒢` be an `𝒪_X`-module of finite
presentation, flat over `S`. For every cartesian square, the formation of `Rf_*𝒢` commutes with
base change: the canonical map `Lg^*Rf_*𝒢 ⟶ Rf'_*L(g')^*𝒢 ⟶ Rf'_*(g')^*𝒢` — the map of
[Stacks, Tag 08HY] followed by `Rf'_*` of the derived-to-ordinary comparison,
`derivedBaseChangeComp` — is an isomorphism.

Only quasi-compactness and quasi-separatedness of `f` are used, so the statement is made under
those. That `Rf_*𝒢` is perfect is
`AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.perfectDerivedPushforward`. -/
theorem isIso_derivedBaseChangeComp_singleDegree_of_isFinitePresentation
    (hsq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f] (G : X.Modules)
    [G.IsFinitePresentation] (hGflat : IsFlatOver f.toLRSHom.toShHom G) :
    IsIso (derivedBaseChangeComp f g f' g' hsq.w (DerivedCategory.Q.obj (singleDegreeComplex G))
      (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj (singleDegreeComplex G)))
      ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (singleDegreeComplex G))) :=
  ProperFlatFibreEulerCharacteristic.isIso_derivedBaseChangeComp_singleDegree hsq G
    (isQuasicoherent_of_isFinitePresentation G) (isQuasicoherent_of_isFinitePresentation _) hGflat

/-- **The tensor form of the base-change half of [Stacks, Tag 0B91] (1), with nothing granted.**
For a cartesian square with `f` flat, quasi-compact and quasi-separated and a perfect `E`, the
map `Lg^*Rf_*(E ⊗^L 𝒪_X) ⟶ Rf'_*(L(g')^*E ⊗^L (g')^*𝒪_X)` of
`AlgebraicGeometry.tensorFlatBaseChangeMap` is an isomorphism. -/
theorem isIso_tensorFlatBaseChangeMap_structure_of_isPerfect (hsq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [Flat f] (E : DerivedCategory X.Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E) :
    IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E
      (structureDegreeComplex X)) := by
  have hE' := RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback g'.toLRSHom.toShHom E hE
  refine isIso_tensorFlatBaseChangeMap_of_isPullback_of_tensorQuasicoherent f g f' g' hsq
    inferInstance inferInstance _ E
    _ (minus_singleDegreeComplex _) (isFlatOver_singleDegreeComplex f _
      (Stacks.Cohomology.PerfectPushforward.isFlatOver_structureModule f)) (fun n => ?_)
    (fun n => ?_)
  · exact ProperFlatFibreEulerCharacteristic.isQuasicoherent_homology_of_iso
      (tensorStructureDegreeComplexIso E) (isQuasicoherent_homology_of_isPerfect E hE) n
  · exact ProperFlatFibreEulerCharacteristic.isQuasicoherent_homology_of_iso
      ((derivedPullback g'.toLRSHom.toShHom).mapIso (tensorStructureDegreeComplexIso E).symm ≪≫
        @asIso _ _ _ _ _ (isIso_baseChangeTensorComparison_structure g' E)).symm
      (isQuasicoherent_homology_of_isPerfect _ hE') n

/-- **The tensor form of the base-change half of [Stacks, Tag 0B91] (2), at the clause's own
`E = 𝒪_X`, with nothing granted.** For a cartesian square with `f` quasi-compact and
quasi-separated and an `𝒪_X`-module `𝒢` of finite presentation, flat over `S`, the map
`Lg^*Rf_*(𝒪_X ⊗^L 𝒢) ⟶ Rf'_*(L(g')^*𝒪_X ⊗^L (g')^*𝒢)` of
`AlgebraicGeometry.tensorFlatBaseChangeMap` is an isomorphism. -/
theorem isIso_tensorFlatBaseChangeMap_module_of_isFinitePresentation
    (hsq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f] (G : X.Modules)
    [G.IsFinitePresentation] (hGflat : IsFlatOver f.toLRSHom.toShHom G) :
    IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w)
      (DerivedCategory.Q.obj (structureDegreeComplex X)) (singleDegreeComplex G)) := by
  have hG := ProperFlatFibreEulerCharacteristic.isQuasicoherent_homology_of_iso
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app G).symm
    (ProperFlatFibreEulerCharacteristic.isQuasicoherent_homology_singleFunctor G
      (isQuasicoherent_of_isFinitePresentation G))
  have hG' := ProperFlatFibreEulerCharacteristic.isQuasicoherent_homology_of_iso
    (ProperFlatFibreEulerCharacteristic.pullbackComplexSingleIso g' G)
    (ProperFlatFibreEulerCharacteristic.isQuasicoherent_homology_singleFunctor _
      (isQuasicoherent_of_isFinitePresentation _))
  refine isIso_tensorFlatBaseChangeMap_of_isPullback_of_tensorQuasicoherent f g f' g' hsq
    inferInstance inferInstance _ _
    _ (minus_singleDegreeComplex G) (isFlatOver_singleDegreeComplex f G hGflat) (fun n => ?_)
    (fun n => ?_)
  · exact ProperFlatFibreEulerCharacteristic.isQuasicoherent_homology_of_iso
      (((derivedTensorProductFunctor X.sheaf).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _).symm).app _ ≪≫
        Stacks.RingedSpace.derivedTensorLeftUnitIso X.toRingedSpace _) hG n
  · exact ProperFlatFibreEulerCharacteristic.isQuasicoherent_homology_of_iso
      (((derivedTensorProductFunctor X'.sheaf).mapIso
          ((derivedPullback g'.toLRSHom.toShHom).mapIso
            ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _).symm ≪≫
            Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso
              g'.toLRSHom.toShHom)).app _ ≪≫
        Stacks.RingedSpace.derivedTensorLeftUnitIso X'.toRingedSpace _) hG' n

end AlgebraicGeometry.ProperFlatBaseChange

end
