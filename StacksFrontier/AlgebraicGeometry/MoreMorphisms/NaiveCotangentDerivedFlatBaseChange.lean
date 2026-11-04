module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentFlatBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionOnComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Unconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DoubleComplexFlat
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackTwoStep
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentFlatDegreeZero

/-!
# The derived base change of the naive cotangent complex along a flat morphism

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a cartesian square of schemes with `f : X ⟶ Y` flat.  The undecorated comparison
`(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` is a quasi-isomorphism — the first clause of Stacks 0FK0, proved
in `StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentFlatBaseChange`.  This file proves
the second clause: if moreover `NL_{X/Y}` has Tor amplitude in `[-1, 0]`, then the *derived*
comparison `L(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` is an isomorphism in `D(𝒪_{X'})`.

## Main definitions

* `Stacks.NaiveCotangentDerivedFlatBaseChange.pulledComplexIso`: the identification of Mathlib's
  termwise pullback of `NL_{X/Y}` along `g'` with the inverse-image-then-extend-scalars model
  `Stacks.NaiveCotangentFlatBaseChange.pulledComplex` that the first clause is stated over.  It
  is `RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep` taken termwise, its naturality
  giving the compatibility with the differential.
* `Stacks.NaiveCotangentDerivedFlatBaseChange.derivedBaseChangeMapOfComparison`: the canonical
  derived base change map `L(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}`, the composite of the canonical
  comparison `L(g')^* ⟶ (g')^*` of Stacks 06YJ with the base change map of complexes of the
  first clause.

## Main results

* `Stacks.NaiveCotangentDerivedFlatBaseChange.kFlat_naiveCotangentComplex_of_hasTorAmplitude`:
  if `NL_{X/Y}` has Tor amplitude in `[-1, 0]` then it is K-flat.  Its degree `0` term is flat
  (Stacks 08TW, `Stacks.SheafOfModules.isFlat_naiveCotangentComplex_X_zero`), so its degree `-1`
  term is flat by the ringed-space form of Stacks 0653, and a bounded-above complex of flat
  modules is K-flat by Stacks 06YQ.
* `Stacks.NaiveCotangentDerivedFlatBaseChange.isIso_derivedBaseChangeMapOfComparison_of_flat`:
  **the second clause of Stacks 0FK0.**

## Implementation notes

The derived pullback is Stacks 06YJ's
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`, the total left derived
functor of termwise pullback, and the comparison at a complex is
`Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex`.  It is stated over
Mathlib's abstract left adjoint `RingedSpaceModuleAdjunction.modulePullback`, while the first
clause is stated over the two-step model; `pulledComplexIso` bridges the two, using the
identification of the two models proved in
`StacksFrontier.Topology.Sheaves.Functors.Module.PullbackTwoStep`.

The Tor-amplitude hypothesis is the ringed-space notion of Stacks 08CG,
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, taken for the image of `NL_{X/Y}` in
`D(𝒪_X)`.  Flatness of `f` enters only through the first clause.

## References

* [Stacks Project, Tag 0FK0](https://stacks.math.columbia.edu/tag/0FK0)
* [Stacks Project, Tag 0653](https://stacks.math.columbia.edu/tag/0653)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules (inverseImageBaseRing inverseImageFirstRingMap ringedSpaceStructureMap)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap)
open Stacks.NaiveCotangentFlatBaseChange (pulledComplex baseChangeMapOfComparison
  quasiIso_baseChangeMapOfComparison_of_flat_algebra)
open RingedSpaceModuleAdjunction (modulePullback twoStepPullback modulePullbackIsoTwoStep)
open Stacks.DerivedPullback.Composition (derivedPullbackComparisonOnComplex)

universe u

noncomputable section

namespace Stacks.NaiveCotangentDerivedFlatBaseChange

attribute [local instance] HasDerivedCategory.standard

variable {X Y X' Y' : Scheme.{u}}

/-! ### The two models of the pullback of the naive cotangent complex -/

/-- **The two models of `(g')^*NL_{X/Y}` agree.**  Mathlib's termwise pullback of `NL_{X/Y}`
along `g'` is isomorphic to `Stacks.NaiveCotangentFlatBaseChange.pulledComplex`, the
inverse-image-then-extend-scalars model that Stacks 08TM and the first clause of Stacks 0FK0 are
stated over.  It is `RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep` applied termwise. -/
def pulledComplexIso (f : X ⟶ Y) (g' : X' ⟶ X) :
    ((modulePullback g'.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (Scheme.naiveCotangentComplex f) ≅ pulledComplex f g' :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (modulePullbackIsoTwoStep g'.toLRSHom.toShHom).app
      ((Scheme.naiveCotangentComplex f).X i))
    (fun i j _ =>
      ((modulePullbackIsoTwoStep g'.toLRSHom.toShHom).hom.naturality
        ((Scheme.naiveCotangentComplex f).d i j)).symm)

/-! ### K-flatness of the naive cotangent complex -/

/-- **A naive cotangent complex of Tor amplitude in `[-1, 0]` is K-flat.**  Its degree `0` term
is flat because its stalks are the free cotangent spaces of the canonical presentations of the
stalk maps, so the ringed-space form of Stacks 0653 makes the degree `-1` term flat too; a
bounded-above complex of flat `𝒪_X`-modules is K-flat by Stacks 06YQ. -/
theorem kFlat_naiveCotangentComplex_of_hasTorAmplitude (f : X ⟶ Y)
    (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace
      (Scheme.naiveCotangentComplex f) := by
  refine Stacks.Cohomology.TorAmplitude.DoubleFlat.kFlat_of_hasTorAmplitude
    (X := X.toRingedSpace) (Scheme.naiveCotangentComplex f) ?_ ?_ ?_
  · exact Scheme.naiveCotangentComplex_isZero_X f
  · exact Stacks.SheafOfModules.isFlat_ringedSpace_naiveCotangentComplex_X_zero
      f.toLRSHom.toShHom
  · exact htor

/-! ### The derived base change map -/

/-- **The canonical derived base change map `L(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}`** of a commutative
square of schemes, attached to a comparison `bc : (g')^{-1}f^{-1}𝒪_Y ⟶ (f')^{-1}𝒪_{Y'}`.

It is the canonical comparison `L(g')^*NL_{X/Y} ⟶ (g')^*NL_{X/Y}` of Stacks 06YJ, followed by
the identification `pulledComplexIso` of the two models of the pullback, followed by the
canonical base change map of complexes
`Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison`. -/
def derivedBaseChangeMapOfComparison (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (bc : inverseImageBaseRing g'.toLRSHom.toShHom f.toLRSHom.toShHom ⟶
      inverseImageSheaf f'.toLRSHom.toShHom)
    (hbc : inverseImageFirstRingMap g'.toLRSHom.toShHom f.toLRSHom.toShHom ≫
        ringedSpaceStructureMap g'.toLRSHom.toShHom =
      bc ≫ ringedSpaceStructureMap f'.toLRSHom.toShHom) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        g'.toLRSHom.toShHom).obj (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ⟶
      DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f') :=
  derivedPullbackComparisonOnComplex g'.toLRSHom.toShHom (Scheme.naiveCotangentComplex f) ≫
    DerivedCategory.Q.map (pulledComplexIso f g').hom ≫
      DerivedCategory.Q.map (baseChangeMapOfComparison f f' g' bc hbc)

/-- The comparison `L(g')^*K ⟶ (g')^*K` at a complex is invertible when `K` is K-flat: it is
the comparison of Stacks 06YJ at the homotopy class of `K`, which
`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat` inverts,
conjugated by three isomorphisms of localization comparisons. -/
theorem isIso_derivedPullbackComparisonOnComplex_of_kFlat {S T : RingedSpace.{u, u}} (h : S ⟶ T)
    (P : CochainComplex (RingedSpaceModuleAdjunction.ModuleSheaves T) ℤ)
    (hP : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex T P) :
    IsIso (derivedPullbackComparisonOnComplex h P) := by
  have := Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat
    h P hP
  unfold Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex
  infer_instance

/-- **Stacks 0FK0, the derived clause.**  For a cartesian square of schemes whose right vertical
morphism `f : X ⟶ Y` is flat and whose naive cotangent complex `NL_{X/Y}` has Tor amplitude in
`[-1, 0]`, the canonical derived comparison `L(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` is an isomorphism in
`D(𝒪_{X'})`.

The Tor amplitude makes `NL_{X/Y}` K-flat, so the comparison `L(g')^*NL_{X/Y} ⟶ (g')^*NL_{X/Y}`
is invertible by Stacks 06YJ; the remaining factor is the base change map of complexes, which is
a quasi-isomorphism by the first clause. -/
@[stacks 0FK0 "the SECOND clause -- the DERIVED comparison `L(g')^* NL_{X/Y} -> NL_{X'/Y'}` is \
a quasi-isomorphism when `NL_{X/Y}` has tor-amplitude in [-1,0] -- with no hypotheses beyond a \
CARTESIAN square (`hsq : IsPullback g' f' f g`), `[Flat f]` and that tor-amplitude.  The first \
clause is \
`Stacks.NaiveCotangentFlatBaseChange.quasiIso_baseChangeMapOfComparison_of_flat_algebra`.  The \
DERIVED PULLBACK is not assumed: it is \
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`, the total left derived \
functor of termwise pullback of [Stacks, Tag 06YJ], which exists for every morphism of ringed \
spaces, and the comparison `L(g')^* K -> (g')^* K` at a complex is \
`Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex`.  TOR AMPLITUDE is the \
ringed-space notion of [Stacks, Tag 08CG], \
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, tested against EVERY `O_X`-module.  The map \
is CONSTRUCTED, not assumed: `derivedBaseChangeMapOfComparison` is the Tag 06YJ comparison, \
then the identification `pulledComplexIso` of Mathlib's termwise pullback with the \
inverse-image-then-extend-scalars model, then the first clause's map of complexes \
`Stacks.NaiveCotangentFlatBaseChange.baseChangeMapOfComparison`, taken against the CANONICAL \
base-ring comparison `AlgebraicGeometry.BaseChangeStalk.baseRingComparison` of the square.  \
PROVED HERE: that `NL_{X/Y}` is K-flat under the tor-amplitude hypothesis \
(`kFlat_naiveCotangentComplex_of_hasTorAmplitude`), which is the whole content of the clause \
beyond the first -- its degree 0 term is flat because each stalk is the free cotangent space of \
the canonical presentation of the stalk map \
(`Stacks.SheafOfModules.isFlat_naiveCotangentComplex_X_zero`, [Stacks, Tag 05NE] plus \
`Algebra.Generators.cotangentSpaceBasis`), so its degree -1 term is flat by the ringed-space \
form of [Stacks, Tag 0653] \
(`Stacks.Cohomology.TorAmplitude.DoubleFlat.isFlat_X_negOne_of_hasTorAmplitude`, the stupid \
filtration of a two-term complex fed to [Stacks, Tag 08CJ] (1)), and a bounded-above complex of \
flat modules is K-flat by [Stacks, Tag 06YQ]; and that a K-flat complex inverts the Tag 06YJ \
comparison (`isIso_derivedPullbackComparisonOnComplex_of_kFlat`).  The two models of `(g')^*` \
are identified by `RingedSpaceModuleAdjunction.modulePullbackIsoTwoStep`, proved here from \
uniqueness of left adjoints, which closes the input that \
`StacksFrontier/AlgebraicGeometry/EtaleAlgebra/FlatBaseChange/StructureSheaf.lean` had recorded as \
open.  SCOPE: the undecorated first clause is on \
`Stacks.NaiveCotangentFlatBaseChange.quasiIso_baseChangeMapOfComparison_of_flat_algebra`; the \
two declarations together are the whole tag"]
theorem isIso_derivedBaseChangeMapOfComparison_of_flat (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
    (g' : X' ⟶ X) (hsq : IsPullback g' f' f g) [AlgebraicGeometry.Flat f]
    (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :
    IsIso (derivedBaseChangeMapOfComparison f f' g'
      (AlgebraicGeometry.BaseChangeStalk.baseRingComparison f f' g' g hsq.w)
      (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp f f' g' g hsq.w)) := by
  have h1 := isIso_derivedPullbackComparisonOnComplex_of_kFlat g'.toLRSHom.toShHom
    (Scheme.naiveCotangentComplex f) (kFlat_naiveCotangentComplex_of_hasTorAmplitude f htor)
  have h2 := (DerivedCategory.Q.mapIso (pulledComplexIso f g')).isIso_hom
  have h3 : IsIso (DerivedCategory.Q.map
      (baseChangeMapOfComparison f f' g'
        (AlgebraicGeometry.BaseChangeStalk.baseRingComparison f f' g' g hsq.w)
        (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp f f' g' g hsq.w))) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact quasiIso_baseChangeMapOfComparison_of_flat_algebra f g f' g' hsq
  unfold derivedBaseChangeMapOfComparison
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (@IsIso.comp_isIso _ _ _ _ _ _ _ h2 h3)

end Stacks.NaiveCotangentDerivedFlatBaseChange

end

end
