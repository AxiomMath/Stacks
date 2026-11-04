module

public import StacksFrontier.AlgebraicGeometry.BaseChange.SheafHomFinitelyPresentedPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibreHomVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHomFunctorial

/-!
# Perfectness of the derived pushforward of a derived internal hom into a finitely presented
complex

Let `f : X ⟶ S` be a morphism of schemes of finite presentation, let `E` be a perfect object of
`D(𝒪_X)` and let `𝒢^•` be a bounded complex of finitely presented `𝒪_X`-modules, flat over `S`,
with support proper over `S`. Then `K = Rf_*R𝓗om_{𝒪_X}(E, 𝒢^•)` is a perfect object of
`D(𝒪_S)`. This is the perfectness half of [Stacks, Tag 0A1J].

## Main definitions

* `AlgebraicGeometry.sheafHomIsoDerivedDualTensor`: for a perfect `E` and any `M` in `D(𝒪_X)`,
  `R𝓗om_{𝒪_X}(E, M) ≅ E^∨ ⊗^L_{𝒪_X} M`, with the derived tensor product of
  [Stacks, Tag 0A1H].

## Main results

* `AlgebraicGeometry.isPerfect_derivedDual_scheme`: the dual of a perfect object of `D(𝒪_X)` is
  perfect.
* `AlgebraicGeometry.isPerfect_derivedPushforward_derivedSheafHom_of_finitePresentation`: the
  perfectness half of [Stacks, Tag 0A1J].

## Implementation notes

The source reduces to the Noetherian case [Stacks, Tag 0DJR] by Noetherian approximation, and
[Stacks, Tag 0DJR] itself is [Stacks, Tag 0DJQ] after the identification
`R𝓗om(E, 𝒢^•) = E^∨ ⊗^L 𝒢^•` of [Stacks, Tag 08DQ]. The same identification, made first,
reduces [Stacks, Tag 0A1J] to [Stacks, Tag 0A1H] at the perfect object `E^∨`, and the
Noetherian approximation is then the one already carried out in the proof of
[Stacks, Tag 0A1H]. That is the route taken here.

The identification is assembled from three isomorphisms: the third assertion of [Stacks, Tag 08DQ]
as a natural isomorphism (`Stacks.SheafOfModules.derivedTensorDualNatIsoOfIsPerfectSpace`), which
puts `E^∨` in the right slot of `Stacks.SheafOfModules.derivedTensor`; the symmetry of the derived
monoidal structure, which moves it to the left slot; and
`AlgebraicGeometry.derivedTensorSpellingIso`, which passes from
`Stacks.SheafOfModules.derivedTensor` to the derived tensor product
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` that [Stacks, Tag 0A1H] is stated
with.

## References

* [Stacks Project, Tag 0A1J](https://stacks.math.columbia.edu/tag/0A1J)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 0DJR](https://stacks.math.columbia.edu/tag/0DJR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.SheafOfModules (derivedSheafHom derivedDual)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

section DualTensor

variable {X : Scheme.{u}}

/-- `R𝓗om_{𝒪_X}(E, M) ≅ M ⊗^L_{𝒪_X} E^∨` for a perfect `E`: the third assertion of
[Stacks, Tag 08DQ] at the scheme `X`, with `E^∨` in the right slot of
`Stacks.SheafOfModules.derivedTensor`. -/
def sheafHomIsoTensorDerivedDual
    (E : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (M : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf)) :
    ((derivedSheafHom X.sheaf).obj (op E)).obj M ≅
      ((Stacks.SheafOfModules.derivedTensor X.sheaf).obj M).obj (derivedDual X.sheaf E) :=
  ((Stacks.SheafOfModules.derivedTensorDualNatIsoOfIsPerfectSpace X.toRingedSpace E hE).app
      M).symm

/-- The symmetry `M ⊗^L A ≅ A ⊗^L M` of `Stacks.SheafOfModules.derivedTensor` on a scheme. -/
def derivedTensorSwapIso
    (A M : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf)) :
    ((Stacks.SheafOfModules.derivedTensor X.sheaf).obj M).obj A ≅
      ((Stacks.SheafOfModules.derivedTensor X.sheaf).obj A).obj M :=
  @BraidedCategory.braiding
    (DerivedCategory (Stacks.SheafOfModules.StructureSheafModules X.sheaf)) _
    (Stacks.SheafOfModules.derivedMonoidalStructure X.sheaf)
    (Stacks.SheafOfModules.derivedSymmetricStructure X.sheaf).toBraidedCategory M A

/-- **`R𝓗om_{𝒪_X}(E, M) ≅ E^∨ ⊗^L_{𝒪_X} M` for a perfect `E`** ([Stacks, Tag 08DQ]), with the
derived tensor product `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` that
[Stacks, Tag 0A1H] is stated with, and with perfectness read as in that tag. -/
def sheafHomIsoDerivedDualTensor (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (M : DerivedCategory X.Modules) :
    ((derivedSheafHom X.sheaf).obj (op E)).obj M ≅
      ((derivedTensorProductFunctor X.sheaf).obj (derivedDual X.sheaf E)).obj M :=
  sheafHomIsoTensorDerivedDual E hE M ≪≫ derivedTensorSwapIso _ M ≪≫
    (((derivedTensorSpellingIso X).app _).app M).symm

/-- **The dual of a perfect object of `D(𝒪_X)` is perfect** ([Stacks, Tag 08DQ], first
assertion), with perfectness read as in [Stacks, Tag 0A1H]. -/
theorem isPerfect_derivedDual_scheme (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) :
    RingedSpace.IsPerfect (X := X.toRingedSpace) (derivedDual X.sheaf E) :=
  Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace X.toRingedSpace E hE

end DualTensor

/-- **The perfectness half of [Stacks, Tag 0A1J].** Let `f : X ⟶ S` be a morphism of schemes of
finite presentation, let `E` be a perfect object of `D(𝒪_X)` and let `𝒢^•` be a bounded complex
of finitely presented `𝒪_X`-modules, flat over `S`, with support proper over `S`. Then
`Rf_*R𝓗om_{𝒪_X}(E, 𝒢^•)` is a perfect object of `D(𝒪_S)`.

By [Stacks, Tag 08DQ], `R𝓗om(E, 𝒢^•) ≅ E^∨ ⊗^L 𝒢^•` with `E^∨` perfect, and
`Rf_*(E^∨ ⊗^L 𝒢^•)` is perfect by [Stacks, Tag 0A1H]. -/
theorem isPerfect_derivedPushforward_derivedSheafHom_of_finitePresentation {X S : Scheme.{u}}
    (f : X ⟶ S) (hf : FinitePresentation f) (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (G : CochainComplex X.Modules ℤ)
    (hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      FlatProperSupportFinitelyPresented f G) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        (((derivedSheafHom X.sheaf).obj (op E)).obj (DerivedCategory.Q.obj G))) :=
  isPerfect_of_iso_scheme
    ((derivedPushforward f.toLRSHom.toShHom).mapIso
      (sheafHomIsoDerivedDualTensor E hE (DerivedCategory.Q.obj G))).symm
    (isPerfect_derivedPushforward_tensor f hf _ (isPerfect_derivedDual_scheme E hE) G hG)

end AlgebraicGeometry

end
