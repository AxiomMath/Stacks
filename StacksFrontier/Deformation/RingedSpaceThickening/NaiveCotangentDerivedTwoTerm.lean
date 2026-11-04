module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentDerivedFlatBaseChange
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedComparison
public import StacksFrontier.Deformation.RingedSpaceThickening.PulledNaiveCotangentTwoTerm

/-!
# A two-term structure on the derived pullback `Lf^*𝖭𝖫_{S/S'}`

For composable morphisms `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` of ringed
spaces, `AlgebraicGeometry.RingedSpaceThickening.pulledNaiveCotangentTwoTerm` equips the
*degreewise* pullback `f^*𝖭𝖫_{S/S'}` with the two-term structure that the obstruction theory of
[Stacks Project, Tag 08U8] consumes. This file transports that structure onto the *derived*
pullback `Lf^*𝖭𝖫_{S/S'}`, under the one hypothesis that makes the two agree: K-flatness of
`𝖭𝖫_{S/S'}`.

The underlying object of the structure built here is `derivedPullbackNaiveCotangent f t` by
`rfl` (`derivedPullbackNaiveCotangentTwoTerm_obj`), so the obstruction class
`NaiveCotangentTwoTerm.conormalExtClass` of a conormal homomorphism is an element of the group
`extOnePulledNaiveCotangent f t G`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.derivedPullbackNaiveCotangentIso`: the identification
  `Lf^*𝖭𝖫_{S/S'} ≅ f^*𝖭𝖫_{S/S'}` in `D(𝒪_X)` for `𝖭𝖫_{S/S'}` K-flat.
* `AlgebraicGeometry.RingedSpaceThickening.derivedPullbackNaiveCotangentTwoTerm`: the resulting
  two-term structure whose underlying object is `Lf^*𝖭𝖫_{S/S'}`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.derivedPullbackNaiveCotangentTwoTerm_obj`: its
  underlying object is `derivedPullbackNaiveCotangent f t` definitionally.
* `AlgebraicGeometry.RingedSpaceThickening.kFlatComplex_naiveCotangentComplex_of_hasTorAmplitude`:
  for morphisms of *schemes*, the K-flatness hypothesis follows from Tor amplitude in `[-1, 0]`,
  which is the form [Stacks Project, Tag 0FK0] states it in.

## Implementation notes

The identification is the first factor of
`AlgebraicGeometry.RingedSpaceThickening.derivedPullbackNaiveCotangentComparison`, the
comparison `q` of [Stacks Project, Tag 06YJ] between the derived and the degreewise pullback,
followed by `pulledNaiveCotangentComplexIso`, the change of spelling of the degreewise pullback.
`Stacks.NaiveCotangentDerivedFlatBaseChange.isIso_derivedPullbackComparisonOnComplex_of_kFlat`
inverts the first factor on a K-flat complex and the second is an isomorphism outright, so the
composite is one; `NaiveCotangentTwoTerm.ofIso` then moves the structure across it, leaving the
two terms and the differential of `pulledNaiveCotangentTwoTerm` unchanged.

K-flatness is a hypothesis and not a theorem. For a morphism of schemes it follows from Tor
amplitude in `[-1, 0]`, by
`Stacks.NaiveCotangentDerivedFlatBaseChange.kFlat_naiveCotangentComplex_of_hasTorAmplitude`,
and that is how `kFlatComplex_naiveCotangentComplex_of_hasTorAmplitude` below reads it — the
scheme-level and ringed-space-level naive cotangent complexes of a morphism of schemes are the
same complex, so no comparison is needed. Tor amplitude in `[-1, 0]` is a genuine restriction on
the morphism.

The two spellings of the category of `𝒪_X`-modules,
`RingedSpaceModuleAdjunction.structureSheafRing` and
`Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf`, agree here with no mediation: the underlying
object of `pulledNaiveCotangentTwoTerm` is
`DerivedCategory.Q.obj (pulledNaiveCotangentComplex f t)` by `rfl` in either spelling, so the
structure built here lives in the same category as `extOnePulledNaiveCotangent`.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8), the obstruction class of
  a conormal homomorphism, which consumes a two-term structure.
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ), the derived pullback and
  its comparison with the degreewise one.
* [Stacks Project, Tag 0FK0](https://stacks.math.columbia.edu/tag/0FK0), where Tor amplitude in
  `[-1, 0]` is the hypothesis that makes the derived comparison invertible.
* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition (derivedPullbackComparisonOnComplex)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}} (f : X ⟶ S) (t : S ⟶ S')

/-- **`Lf^*𝖭𝖫_{S/S'} ≅ f^*𝖭𝖫_{S/S'}` for `𝖭𝖫_{S/S'}` K-flat.** The comparison of
[Stacks Project, Tag 06YJ] between the derived and the degreewise pullback, at the complex
`𝖭𝖫_{S/S'}`, followed by the change of spelling `pulledNaiveCotangentComplexIso`: the first
factor is invertible because the complex is K-flat, and the second is an isomorphism. -/
def derivedPullbackNaiveCotangentIso
    (hkf : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex S
      (RingedSpace.naiveCotangentComplex t)) :
    derivedPullbackNaiveCotangent f t ≅ (pulledNaiveCotangentTwoTerm f t).obj :=
  letI :=
    Stacks.NaiveCotangentDerivedFlatBaseChange.isIso_derivedPullbackComparisonOnComplex_of_kFlat
      f (RingedSpace.naiveCotangentComplex t) hkf
  (asIso (derivedPullbackComparisonOnComplex f (RingedSpace.naiveCotangentComplex t))).trans
    (DerivedCategory.Q.mapIso (pulledNaiveCotangentComplexIso f t))

/-- **The two-term structure of `Lf^*𝖭𝖫_{S/S'}`**, for `𝖭𝖫_{S/S'}` K-flat: the two-term
structure of the degreewise pullback, transported along
`derivedPullbackNaiveCotangentIso`. Its conormal term is `f^*(𝒥/𝒥²)`, its degree `0` term is
`f^*Ω` and its differential is `pulledConormalMap f t`, all unchanged from
`pulledNaiveCotangentTwoTerm`. -/
def derivedPullbackNaiveCotangentTwoTerm
    (hkf : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex S
      (RingedSpace.naiveCotangentComplex t)) :
    NaiveCotangentTwoTerm (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X)) 0) :=
  (pulledNaiveCotangentTwoTerm f t).ofIso (derivedPullbackNaiveCotangentIso f t hkf)

variable (hkf : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex S
  (RingedSpace.naiveCotangentComplex t))

/-- The underlying object of the two-term structure is `Lf^*𝖭𝖫_{S/S'}` definitionally. -/
@[simp]
theorem derivedPullbackNaiveCotangentTwoTerm_obj :
    (derivedPullbackNaiveCotangentTwoTerm f t hkf).obj = derivedPullbackNaiveCotangent f t :=
  rfl

/-- The differential is `pulledConormalMap f t`, the transport having changed neither of the
two terms nor the differential. -/
@[simp]
theorem derivedPullbackNaiveCotangentTwoTerm_d :
    (derivedPullbackNaiveCotangentTwoTerm f t hkf).d = pulledConormalMap f t :=
  rfl

/-- **For a morphism of schemes, Tor amplitude in `[-1, 0]` supplies the K-flatness
hypothesis.** The naive cotangent complex of a morphism of schemes is the naive cotangent
complex of the underlying morphism of ringed spaces, so
`Stacks.NaiveCotangentDerivedFlatBaseChange.kFlat_naiveCotangentComplex_of_hasTorAmplitude`
applies with no comparison. -/
theorem kFlatComplex_naiveCotangentComplex_of_hasTorAmplitude {V W : Scheme.{u}} (g : V ⟶ W)
    (htor : Stacks.Cohomology.TorAmplitude.HasTorAmplitude V.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex g)) (-1) 0) :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex V.toRingedSpace
      (RingedSpace.naiveCotangentComplex g.toLRSHom.toShHom) :=
  Stacks.NaiveCotangentDerivedFlatBaseChange.kFlat_naiveCotangentComplex_of_hasTorAmplitude g htor

end AlgebraicGeometry.RingedSpaceThickening

end
