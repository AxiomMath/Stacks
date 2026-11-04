module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalTensorPowerProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedTensorPowersPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackOfIso

/-!
# The numerical invariants of Stacks 0DNE along base change of the standing data

Let `f₀ : X₀ ⟶ B₀` be a separated morphism of algebraic spaces of finite presentation, let
`E_{1,0}, …, E_{r,0}` be perfect objects of `D(𝒪_{X₀})`, let `g : B ⟶ B₀` be a morphism of
algebraic spaces, and let `f : X = X₀ ×_{B₀} B ⟶ B` be the base change, with projection
`p : X ⟶ X₀` and perfect objects `E_j = Lp^*E_{j,0}`.  For an object `(T, 𝓕)` of `Coh_{X/B}`,
with image `(T, 𝓕₀)` in `Coh_{X₀/B₀}` under the top row of the 2-cartesian square of
Stacks 08LP, and for every `n ∈ ℤ^{⊕ r}`, the objects

`K_n = Rf_{T,*}((E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r})_T ⊗^𝐋 𝓕)` and
`K_{n,0} = Rf_{0,T,*}((E_{1,0}^{⊗ n_1} ⊗ ⋯ ⊗ E_{r,0}^{⊗ n_r})_T ⊗^𝐋 𝓕₀)`

of `D(𝒪_T)` are isomorphic.  Hence the numerical invariants agree, and `Coh^P_{X/B}` is the
inverse image of `Coh^P_{X₀/B₀}` along `Coh_{X/B} ⟶ Coh_{X₀/B₀}`: this is the cartesian square
through which the proof of Stacks 0DNE reduces to a Noetherian base.  In particular, if
`Coh^P_{X₀/B₀} ⊆ Coh_{X₀/B₀}` is open and closed, so is `Coh^P_{X/B} ⊆ Coh_{X/B}`.

## Main definitions

* `AlgebraicGeometry.Space.NumericalSituation.numericalDirectImageBaseChangeIso`: `K_n ≅ K_{n,0}`.

## Main results

* `AlgebraicGeometry.Space.NumericalSituation.numericalEuler_baseChange`: the numerical
  invariants of `(T, 𝓕)` and of its image agree.
* `AlgebraicGeometry.Space.NumericalSituation.hasNumericalInvariants_baseChange_iff`: `(T, 𝓕)`
  lies in `Coh^P_{X/B}` exactly when its image lies in `Coh^P_{X₀/B₀}`.
* `AlgebraicGeometry.Space.NumericalSituation.isOpenAndClosedCondition_baseChange`: if
  `Coh^P_{X₀/B₀}` is an open and closed substack of `Coh_{X₀/B₀}`, then `Coh^P_{X/B}` is an open
  and closed substack of `Coh_{X/B}`.

## Implementation notes

The base change `X_T` of `X` to `T` and the base change `X_{0,T}` of `X₀` to `T` are identified
by the comparison `ι : X_T ≅ X_{0,T}` of
`AlgebraicGeometry.Space.CoherentSituation.baseChangeSpaceIso`,
and the module of the image object is `(ι⁻¹)^*𝓕`.  The isomorphism `K_n ≅ K_{n,0}` is assembled
from: the compatibility of the products of integer tensor powers with derived pullback
(`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackDerivedTensorPowerProductIso`), the
composition law of derived pullback, the compatibility of derived pullback with the derived
tensor product (Stacks 07A4), and the computation of derived pullback and derived pushforward
along the isomorphism `ι`.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 08LP](https://stacks.math.columbia.edu/tag/08LP)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D₀ : CoherentSituation B S hS)
  {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ D₀.Y)

namespace CoherentSituation

/-- The projection `X₀ ×_{B₀} B ⟶ X₀` of the base-changed standing data. -/
abbrev baseChangeSourceProjection : (D₀.baseChange g).X ⟶ D₀.X :=
  ObjectProperty.homMk (pullback.fst D₀.f.hom g.hom)

end CoherentSituation

namespace NumericalSituation

variable (hf₀ : IsSeparated B S hS D₀.f.hom) (hf : IsSeparated B S hS (D₀.baseChange g).f.hom)
  {r : ℕ} (E₀ : Fin r → DerivedCategory (Modules.{u, u} B S hS D₀.X.1 D₀.X.2))
  (hE₀ : ∀ j, (smallEtaleRingedSite B S hS D₀.X.1 D₀.X.2).IsPerfect (E₀ j))
  (P : (Fin r → ℤ) → ℤ)

/-- The perfect objects `E_j = Lp^*E_{j,0}` on the base-changed source. -/
abbrev baseChangeObjects : Fin r → DerivedCategory (Modules.{u, u} B S hS (D₀.baseChange g).X.1
    (D₀.baseChange g).X.2) :=
  fun j => (smallEtaleDerivedModulePullback B S hS (D₀.baseChangeSourceProjection g)).obj (E₀ j)

omit hf₀ hf in
include hE₀ in
/-- The objects `E_j = Lp^*E_{j,0}` are perfect (Stacks 08H6). -/
theorem isPerfect_baseChangeObjects (j : Fin r) :
    (smallEtaleRingedSite B S hS (D₀.baseChange g).X.1 (D₀.baseChange g).X.2).IsPerfect
      (baseChangeObjects D₀ g E₀ j) :=
  isPerfect_smallEtaleDerivedModulePullback _ _ (hE₀ j)

/-- **The objects `(E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r})_T ⊗^𝐋 𝓕` along the comparison `ι`**: the
object on `X_T` is the derived pullback along `ι : X_T ≅ X_{0,T}` of the corresponding object on
`X_{0,T}` for the image of `(T, 𝓕)` in `Coh_{X₀/B₀}`. -/
def numericalTensorBaseChangeIso (A : CoherentObject (D₀.baseChange g)) (n : Fin r → ℤ) :
    (ofDerivedTensorPowerProducts hf (baseChangeObjects D₀ g E₀)
        (isPerfect_baseChangeObjects D₀ g E₀ hE₀) P).numericalTensor A n ≅
      (smallEtaleDerivedModulePullback B S hS (D₀.baseChangeSpaceIso g A.T).hom).obj
        ((ofDerivedTensorPowerProducts hf₀ E₀ hE₀ P).numericalTensor
          (D₀.baseChangeObject' (modulePullbackStabilityOfFinitePresentation B S hS) g A) n) :=
  let ι := D₀.baseChangeSpaceIso g A.T
  let eE : (smallEtaleDerivedModulePullback B S hS
        (baseChangeProjection (D₀.baseChange g).f A.T)).obj
        (derivedTensorPowerProduct B S hS _ _ (baseChangeObjects D₀ g E₀) n) ≅
      (smallEtaleDerivedModulePullback B S hS ι.hom).obj
        ((smallEtaleDerivedModulePullback B S hS
          (baseChangeProjection D₀.f ((D₀.overBase g).obj A.T))).obj
            (derivedTensorPowerProduct B S hS _ _ E₀ n)) :=
    (smallEtaleDerivedModulePullback B S hS
        (baseChangeProjection (D₀.baseChange g).f A.T)).mapIso
        (smallEtaleDerivedModulePullbackDerivedTensorPowerProductIso
          (D₀.baseChangeSourceProjection g) E₀ hE₀ n).symm ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS _ _).app _ ≪≫
      (smallEtaleDerivedModulePullbackCongr B S hS
        (D₀.baseChangeSpaceIso_hom_projection g A.T).symm).app _ ≪≫
      ((smallEtaleDerivedModulePullbackCompIso B S hS _ _).app _).symm
  ((smallEtaleDerivedTensor B S hS (baseChangeSpace (D₀.baseChange g).f A.T)).mapIso eE).app _ ≪≫
    ((smallEtaleDerivedTensor B S hS (baseChangeSpace (D₀.baseChange g).f A.T)).obj _).mapIso
      (smallEtaleDerivedModulePullbackSingleInvIsoOfIso ι A.F).symm ≪≫
    ((smallEtaleDerivedPullbackTensorIso ι.hom).app (_, _)).symm

/-- **`K_n ≅ K_{n,0}`**: for an object `(T, 𝓕)` of `Coh_{X/B}` and its image in `Coh_{X₀/B₀}`,
the objects `Rf_{T,*}((E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r})_T ⊗^𝐋 𝓕)` and
`Rf_{0,T,*}((E_{1,0}^{⊗ n_1} ⊗ ⋯ ⊗ E_{r,0}^{⊗ n_r})_T ⊗^𝐋 𝓕₀)` of `D(𝒪_T)` are isomorphic. -/
def numericalDirectImageBaseChangeIso (A : CoherentObject (D₀.baseChange g)) (n : Fin r → ℤ) :
    (ofDerivedTensorPowerProducts hf (baseChangeObjects D₀ g E₀)
        (isPerfect_baseChangeObjects D₀ g E₀ hE₀) P).numericalDirectImage A n ≅
      (ofDerivedTensorPowerProducts hf₀ E₀ hE₀ P).numericalDirectImage
        (D₀.baseChangeObject' (modulePullbackStabilityOfFinitePresentation B S hS) g A) n :=
  (Stacks.DerivedFunctor.totalRightDerived
      (modulePushforward B S hS ((D₀.baseChange g).projection A.T))).mapIso
      (numericalTensorBaseChangeIso D₀ g hf₀ hf E₀ hE₀ P A n) ≪≫
    (eqToIso (congrArg (fun k => (Stacks.DerivedFunctor.totalRightDerived
      (modulePushforward B S hS k) : DerivedCategory (Modules.{u, u} B S hS
        (baseChangeSpace (D₀.baseChange g).f A.T).1 (baseChangeSpace (D₀.baseChange g).f A.T).2) ⥤
          DerivedCategory (Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj A.T.left).1
            ((schemeSpaceFunctor B S hS).obj A.T.left).2)))
      (D₀.baseChangeSpaceIso_hom_inclusion g A.T).symm)).app _ ≪≫
    derivedModulePushforwardCompPullbackIsoOfIso (D₀.baseChangeSpaceIso g A.T)
      (D₀.projection ((D₀.overBase g).obj A.T)) _

/-- **The numerical invariants agree along the base change of the standing data**: for an
object `(T, 𝓕)` of `Coh_{X/B}`, `n ∈ ℤ^{⊕ r}` and a point `t` of `T`, the invariant
`χ_n(t)` of `(T, 𝓕)` for the perfect objects `Lp^*E_{j,0}` is the invariant `χ_n(t)` of its image
in `Coh_{X₀/B₀}` for the perfect objects `E_{j,0}`. -/
theorem numericalEuler_baseChange (A : CoherentObject (D₀.baseChange g)) (n : Fin r → ℤ) :
    (ofDerivedTensorPowerProducts hf (baseChangeObjects D₀ g E₀)
        (isPerfect_baseChangeObjects D₀ g E₀ hE₀) P).numericalEuler A n =
      (ofDerivedTensorPowerProducts hf₀ E₀ hE₀ P).numericalEuler
        (D₀.baseChangeObject' (modulePullbackStabilityOfFinitePresentation B S hS) g A) n :=
  derivedFibreEuler_congr _ (numericalDirectImageBaseChangeIso D₀ g hf₀ hf E₀ hE₀ P A n)

/-- **`Coh^P_{X/B}` is the inverse image of `Coh^P_{X₀/B₀}`**: an object of `Coh_{X/B}` has the
numerical invariants `P` for the perfect objects `Lp^*E_{j,0}` exactly when its image in
`Coh_{X₀/B₀}` has them for the perfect objects `E_{j,0}`. -/
theorem hasNumericalInvariants_baseChange_iff (A : CoherentObject (D₀.baseChange g)) :
    (ofDerivedTensorPowerProducts hf (baseChangeObjects D₀ g E₀)
        (isPerfect_baseChangeObjects D₀ g E₀ hE₀) P).HasNumericalInvariants A ↔
      (ofDerivedTensorPowerProducts hf₀ E₀ hE₀ P).HasNumericalInvariants
        (D₀.baseChangeObject' (modulePullbackStabilityOfFinitePresentation B S hS) g A) := by
  refine forall_congr' fun n => forall_congr' fun t => ?_
  rw [numericalEuler_baseChange D₀ g hf₀ hf E₀ hE₀ P A n]
  rfl

/-- **The cartesian square of the proof of Stacks 0DNE**: if
`Coh^P_{X₀/B₀} ⊆ Coh_{X₀/B₀}` is an open and closed substack for the perfect objects `E_{j,0}`,
then `Coh^P_{X/B} ⊆ Coh_{X/B}` is an open and closed substack for the perfect objects
`Lp^*E_{j,0}`, where `X = X₀ ×_{B₀} B`. -/
theorem isOpenAndClosedCondition_baseChange
    (h₀ : CoherentSituation.IsOpenAndClosedCondition D₀
      (ofDerivedTensorPowerProducts hf₀ E₀ hE₀ P).HasNumericalInvariants) :
    CoherentSituation.IsOpenAndClosedCondition (D₀.baseChange g)
      (ofDerivedTensorPowerProducts hf (baseChangeObjects D₀ g E₀)
        (isPerfect_baseChangeObjects D₀ g E₀ hE₀) P).HasNumericalInvariants :=
  h₀.of_baseChange g (hasNumericalInvariants_baseChange_iff D₀ g hf₀ hf E₀ hE₀ P)

end NumericalSituation

end AlgebraicGeometry.Space

end
