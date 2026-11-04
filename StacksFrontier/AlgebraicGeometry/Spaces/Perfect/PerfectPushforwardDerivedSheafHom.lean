module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectPushforwardTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom

/-!
# The direct image of `RSheafHom(E, 𝒢)` for `E` perfect and `𝒢` flat with proper support, for
the derived internal Hom of `D(𝒪_X)` transported from the equi-universe model

Let `Y` be a Noetherian algebraic space and `f : X ⟶ Y` a morphism of algebraic spaces which is
locally of finite type and quasi-separated.  Let `E` be a perfect object of `D(𝒪_X)` and `𝒢^•` a
bounded complex of coherent `𝒪_X`-modules, flat over `Y`, with support proper over `Y`.  Then
`K = Rf_* RSheafHom(E, 𝒢^•)` is a perfect object of `D(𝒪_Y)`.  This is the statement of
Stacks 0DKK for the derived internal Hom `AlgebraicGeometry.Space.smallEtaleDerivedSheafHom`.

## Main results

* `AlgebraicGeometry.Space.derivedSheafHomPushforwardIsoTensorDual`: the identification
  `Rf_* RSheafHom(E, 𝒢^•) ≅ Rf_*(E^∨ ⊗^L 𝒢^•)` of the proof of Stacks 0DKK.
* `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_smallEtaleDerivedSheafHom`: `K` is
  perfect.

## The proof

The source's proof of Stacks 0DKK.  The dual `E^∨ = RSheafHom(E, 𝒪_X)` of the perfect object `E`
is perfect and `RSheafHom(E, 𝒢^•) ≅ E^∨ ⊗^L 𝒢^•` (Stacks 08JJ, on the small étale site of an
algebraic space: `AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedDual` and
`AlgebraicGeometry.Space.smallEtaleDerivedSheafHomIsoTensorDual`), so `K ≅ Rf_*(E^∨ ⊗^L 𝒢^•)`,
which is perfect by Stacks 0DKJ
(`AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_derivedTensor`) applied to `E^∨`.

## Implementation notes

The same assertion for the derived internal Hom
`AlgebraicGeometry.RingedSite.derivedSheafHomSmallBifunctor`, built directly on the small étale
ringed site, is `AlgebraicGeometry.Space.isPerfect_derivedModulePushforward_derivedSheafHom`.
The statement here is for the derived internal Hom
`AlgebraicGeometry.Space.smallEtaleDerivedSheafHom`, the derived internal Hom of the equi-universe
model read through the derived equivalence with the model, which is the one carrying the duality
theory (Stacks 08J8, 08JJ) on an algebraic space; it is the perfectness of the object `K` of
Stacks 08JN as stated in `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDirectImage`.

`⊗^L` is the derived tensor product `AlgebraicGeometry.Space.smallEtaleDerivedTensor` of the small
étale ringed site, through which Stacks 08JJ is stated there.  The direct image `Rf_*` is the total
right derived functor of the pushforward of modules, as in Stacks 0DKJ.

## References

* [Stacks Project, Tag 0DKK](https://stacks.math.columbia.edu/tag/0DKK)
* [Stacks Project, Tag 0DKJ](https://stacks.math.columbia.edu/tag/0DKJ)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] smallEtaleRingedSite_essentiallySmall
  Stacks.hasSheafCompose_forget₂_commRingCat pointTopology isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- **`Rf_* RSheafHom(E, 𝒢^•) ≅ Rf_*(E^∨ ⊗^L 𝒢^•)` for a perfect `E`**: the direct image of the
identification `RSheafHom(E, 𝒢^•) ≅ E^∨ ⊗^L 𝒢^•` of Stacks 08JJ. -/
def derivedSheafHomPushforwardIsoTensorDual (f : X ⟶ Y)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj G) ≅
      (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X E)).obj G) :=
  (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).mapIso
    (smallEtaleDerivedSheafHomIsoTensorDual B S hS X E G hE)

/-- **Stacks 0DKK for the derived internal Hom of `D(𝒪_X)` transported from the model.**
Let `Y` be a Noetherian algebraic space and `f : X ⟶ Y` a morphism locally of finite type and
quasi-separated.  Let `E` be a perfect object of `D(𝒪_X)` and `𝒢^•` a bounded
complex of coherent `𝒪_X`-modules, flat over `Y`, with support proper over `Y`.  Then
`K = Rf_* RSheafHom(E, 𝒢^•)` is a perfect object of `D(𝒪_Y)`. -/
theorem isPerfect_derivedModulePushforward_smallEtaleDerivedSheafHom
    (hTop : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hG : FlatProperSupportComplex B S hS f hf G) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj (DerivedCategory.Q.obj G))) :=
  RingedSite.IsPerfect.of_iso _
    (isPerfect_derivedModulePushforward_derivedTensor B S hS hTop f hf hfqs hY
      (smallEtaleDerivedTensorProduct B S hS X) (smallEtaleDerivedDual B S hS X E)
      (isPerfect_smallEtaleDerivedDual B S hS X E hE) G hG)
    (derivedSheafHomPushforwardIsoTensorDual B S hS f E hE (DerivedCategory.Q.obj G)).symm

end AlgebraicGeometry.Space

end
