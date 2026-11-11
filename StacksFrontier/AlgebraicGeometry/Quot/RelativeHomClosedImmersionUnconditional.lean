module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso

/-!
# The relative Hom functor and a closed immersion: Stacks 08K5

Stacks 08K5: for a closed immersion `i : X' ⟶ X` of algebraic spaces over an algebraic space
`Y`, a quasi-coherent `𝒪_X`-module `F` and a quasi-coherent `𝒪_{X'}`-module `G'`,

`Hom(F, i_*G') = Hom(i^*F, G')`

as functors on the test schemes over `Y`.

`AlgebraicGeometry.Space.homFunctorClosedImmersion` gives this from four inputs, each of which
holds here:

* the pseudofunctoriality of the direct images of Stacks 03LU is the term
  `AlgebraicGeometry.Space.modulePushforwardCoherence`;
* quasi-coherence of `i_*G'` is Stacks 03M9 along a closed immersion,
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion`;
* quasi-coherence of `i^*F` is Stacks 03GA,
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isClosedImmersion`;
* the base-change clause of Stacks 07U8 for the affine morphism `i` (a closed immersion is
  affine, Stacks 07U2) is
  `AlgebraicGeometry.Space.nonempty_modulePullbackModulePushforwardIso_of_isAffineHom`, applied
  to the cartesian squares `AlgebraicGeometry.Space.isPullback_baseChangeSourceMap`; this is
  `AlgebraicGeometry.Space.testSchemePushforwardBaseChange_of_isAffineHom` below.

## Main results

* `AlgebraicGeometry.Space.testSchemePushforwardBaseChange_of_isAffineHom`: the base-change
  clause of Stacks 07U8 in the form `AlgebraicGeometry.Space.TestSchemePushforwardBaseChange`,
  for an affine morphism and a quasi-coherent module.
* `AlgebraicGeometry.Space.homFunctorClosedImmersionIso_of_isQuasicoherentOnSite`:
  `Hom(F, i_*G') = Hom(i^*F, G')` for a closed immersion `i` and quasi-coherent `F` and `G'`.

## References

* [Stacks Project, Tag 08K5](https://stacks.math.columbia.edu/tag/08K5)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 07U2](https://stacks.math.columbia.edu/tag/07U2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y : AlgebraicSpaces B S hS}

/-- **The base-change clause of Stacks 07U8 along the test schemes.**  For an affine morphism
`i : X' ⟶ X` over `Y` and a quasi-coherent `𝒪_{X'}`-module `G'`, the pullback of `i_*G'` to
every base change `X_T` is the direct image along `X'_T ⟶ X_T` of the pullback of `G'`.

The square formed by `X'_T ⟶ X_T`, `i` and the two projections is cartesian, and affine base
change applies to it. -/
theorem testSchemePushforwardBaseChange_of_isAffineHom (p : X ⟶ Y) (i : X' ⟶ X)
    (hi : IsAffineHom B S hS i.hom) (G' : Modules.{u, u} B S hS X'.1 X'.2)
    (hG' : G'.IsQuasicoherentOnSite) :
    TestSchemePushforwardBaseChange p i G' := fun T ↦
  nonempty_modulePullbackModulePushforwardIso_of_isAffineHom
    (isPullback_baseChangeSourceMap p i T).flip hi G' hG'

/-- **Stacks 08K5.**  Let `i : X' ⟶ X` be a closed immersion of algebraic spaces over an
algebraic space `Y` over `S`, let `F` be a quasi-coherent `𝒪_X`-module and let `G'` be a
quasi-coherent `𝒪_{X'}`-module.  Then

`Hom(F, i_*G') = Hom(i^*F, G')`

as functors on the test schemes over `Y`: the relative Hom functor of Stacks 08JT of the
situation `(X ⟶ Y, F, i_*G')` is isomorphic to the one of the situation `(X' ⟶ Y, i^*F, G')`,
both formed with the pseudofunctoriality `AlgebraicGeometry.Space.modulePushforwardCoherence`
of Stacks 03LU.

The two situations are formed with the quasi-coherence of `i_*G'` (Stacks 03M9) and of `i^*F`
(Stacks 03GA), and the comparison is bijective by the base-change clause of Stacks 07U8 for
the affine morphism `i`. -/
@[stacks 08K5 "The whole statement, under exactly the source's hypotheses."]
def homFunctorClosedImmersionIso_of_isQuasicoherentOnSite (p : X ⟶ Y) (i : X' ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (G' : Modules.{u, u} B S hS X'.1 X'.2) (hF : F.IsQuasicoherentOnSite)
    (hG' : G'.IsQuasicoherentOnSite) :
    (pushforwardHomSituation p i F G' hF
        (isQuasicoherentOnSite_modulePushforward_of_isClosedImmersion B S hS i hi G'
          hG')).homFunctor (modulePushforwardCoherence B S hS) ≅
      (pullbackHomSituation p i F G'
        (isQuasicoherentOnSite_modulePullback_of_isClosedImmersion B S hS i hi F hF)
        hG').homFunctor (modulePushforwardCoherence B S hS) :=
  homFunctorClosedImmersion (modulePushforwardCoherence B S hS) p i hi F G' hF _ _ hG'
    (testSchemePushforwardBaseChange_of_isAffineHom p i
      (isAffineHom_of_isClosedImmersion B S hS i.hom hi) G' hG')

end AlgebraicGeometry.Space

end
