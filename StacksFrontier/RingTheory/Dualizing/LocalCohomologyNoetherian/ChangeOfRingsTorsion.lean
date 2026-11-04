module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.LocalCohomologyNoetherian.ChangeOfRings
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.ExtendedCech

/-!
# The `I`-power-torsion form of the change-of-rings isomorphism for local cohomology

Let `A → B` be a homomorphism of Noetherian rings and `I ⊆ A` an ideal, with `Z = V(I)` and
`Y = V(IB)`. [Stacks, Tag 0957] asserts a chain of four equal objects of `D(B)`:

$$ R\Gamma_I(A) \otimes_A^{\mathbf L} B \;=\; R\Gamma_Z(A) \otimes_A^{\mathbf L} B \;=\;
   R\Gamma_Y(B) \;=\; R\Gamma_{IB}(B). $$

`StacksFrontier.RingTheory.Dualizing.LocalCohomologyNoetherian.ChangeOfRings` proves the middle
equality, between the two local-cohomology terms. This file adds the two outer terms — derived
`I`-power torsion `RΓ_I(A)` and derived `IB`-power torsion `RΓ_{IB}(B)` — and identifies them
with `RΓ_Z(A)` and `RΓ_Y(B)`, so that the whole chain is available as a single isomorphism.

The identification of the two torsion functors is part (3) of [Stacks, Tag 0955]
(`Dualizing.TorsionCounit.isIso_compareTorsionFunctors_app`): over a Noetherian ring the
canonical comparison `RΓ_I ⟶ RΓ_Z` of [Stacks, Tag 0A6U] is invertible at every object of
`D(A)`. This is the only place Noetherianity is used, and it is used twice, once over `A` and
once over `B` — which is exactly why the source assumes both rings Noetherian.

## Main definitions

* `Dualizing.derivedPowerTorsionOfRing` — `RΓ_I(A)`, derived `I`-power torsion of the regular
  module, viewed in the ambient derived category.
* `Dualizing.derivedPowerTorsionOfRingLifted` — the same after transporting the regular module
  into a larger module universe.

## Main results

* `Dualizing.derivedPowerTorsionObjIsoLocalCohomologyObj` — over a Noetherian ring,
  `RΓ_I(M) ≅ RΓ_Z(M)`; this is part (3) of [Stacks, Tag 0955] packaged as an isomorphism, and it
  is the input, not part of Tag 0957.
* `Dualizing.derivedPowerTorsionOfRingBaseChangeIsoLocalCohomology` — the first equality of the
  source: `RΓ_I(A) ⊗ᴸ_A B ≅ RΓ_Z(A) ⊗ᴸ_A B`.
* `Dualizing.localCohomologyOfRingIsoDerivedPowerTorsionOfRing` — the last equality of the
  source: `RΓ_Y(B) ≅ RΓ_{IB}(B)`.
* `Dualizing.derivedPowerTorsionOfRingBaseChangeIso` — the whole chain, composed:
  `RΓ_I(A) ⊗ᴸ_A B ≅ RΓ_{IB}(B)`.
* `Dualizing.derivedPowerTorsionOfRingLiftedBaseChangeIso` — the same for rings in independent
  universes, after transporting both regular modules into a common module universe.

## Implementation notes

The source's closed subsets `Z = V(I)` and `Y = V(IB)` are encoded by the ideal arguments of
`Dualizing.localCohomologyFunctor` and of `Dualizing.derivedPowerTorsion`, and `IB` is
`Ideal.map f I`. So the four terms of the source give three isomorphisms with content, expressed
in `D(B)` rather than as equalities; derived tensor product with `B` is represented by derived
extension of scalars, as in `ChangeOfRings`.

Noetherianity of `A` and of `B` is assumed because the two torsion terms need it: over a general
ring the comparison `RΓ_I ⟶ RΓ_Z` is not invertible, which is [Stacks, Tag 0A6P]. The
local-cohomology terms alone would need only finite generation of `I`, which is what
`ChangeOfRings` assumes.

`hI : I.FG` is kept as an explicit argument even though `IsNoetherianRing A` supplies it. It is
not a decorative hypothesis: `hI` occurs in the *types* of all four objects, because it is an
argument of `Dualizing.localCohomologyFunctor` and of `Dualizing.derivedPowerTorsion`. Taking it
universally quantified is therefore strictly stronger than specializing it to
`Ideal.fg_of_isNoetherianRing I`, and since `I` ranges over every ideal of the Noetherian ring
`A`, the source's hypothesis on `I` is covered in full.

## References

* [Stacks Project, Tag 0957](https://stacks.math.columbia.edu/tag/0957)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
* [Stacks Project, Tag 0A6P](https://stacks.math.columbia.edu/tag/0A6P)
* [Stacks Project, Tag 0A6U](https://stacks.math.columbia.edu/tag/0A6U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u uA uB v

namespace Dualizing

/-! ### The two torsion models agree over a Noetherian ring -/

/-- **Over a Noetherian ring the two models of local cohomology agree, at a module.** The
canonical comparison `RΓ_I ⟶ RΓ_Z` of [Stacks, Tag 0A6U] is invertible — part (3) of
[Stacks, Tag 0955] — so derived `I`-power torsion of `M` and local cohomology of `M` are
isomorphic in `D(A)`. This is the input to the outer two equalities of [Stacks, Tag 0957] and
carries no `@[stacks 0957]` attribute of its own. -/
def derivedPowerTorsionObjIsoLocalCohomologyObj (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.FG) (M : ModuleCat.{max u v} A) :
    Stacks.LocalCohomology.derivedPowerTorsionObj.{u, v} A I hI M ≅
      (derivedPowerTorsionProperty A I hI).ι.obj
        ((localCohomologyFunctor.{u, max u v} A I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)) :=
  haveI := TorsionCounit.isIso_compareTorsionFunctors_app.{u, v} A I hI
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)
  (derivedPowerTorsionProperty A I hI).ι.mapIso
    (asIso ((compareTorsionFunctors.{u, v} A I hI).app
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)))

/-! ### `RΓ_I` of the regular module -/

/-- `RΓ_I(A)`: derived `I`-power torsion of a ring along a finitely generated ideal, viewed in
the ambient derived category of `A`-modules. This is the first term of the chain of
[Stacks, Tag 0957]. -/
abbrev derivedPowerTorsionOfRing (A : Type uA) [CommRing A] (I : Ideal A) (hI : I.FG) :
    DerivedCategory (ModuleCat.{uA} A) :=
  Stacks.LocalCohomology.derivedPowerTorsionObj.{uA, uA} A I hI (ModuleCat.of A A)

/-- `RΓ_I(A)` taken after transporting the regular module into the module universe
`max uA v`. -/
abbrev derivedPowerTorsionOfRingLifted (A : Type uA) [CommRing A] (I : Ideal A) (hI : I.FG) :
    DerivedCategory (ModuleCat.{max uA v} A) :=
  Stacks.LocalCohomology.derivedPowerTorsionObj.{uA, v} A I hI
    ((ModuleCat.uliftFunctor.{v, uA} A).obj (ModuleCat.of A A))

/-- `RΓ_I(A) ≅ RΓ_Z(A)` over a Noetherian ring, at the regular module: the case `M = A` of
`Dualizing.derivedPowerTorsionObjIsoLocalCohomologyObj`. -/
def derivedPowerTorsionOfRingIsoLocalCohomologyOfRing (A : Type uA) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (hI : I.FG) :
    derivedPowerTorsionOfRing A I hI ≅ localCohomologyOfRing A I hI :=
  derivedPowerTorsionObjIsoLocalCohomologyObj.{uA, uA} A I hI (ModuleCat.of A A)

/-- `RΓ_I(A) ≅ RΓ_Z(A)` over a Noetherian ring, at the regular module transported into the
module universe `max uA v`. -/
def derivedPowerTorsionOfRingLiftedIsoLocalCohomologyOfRingLifted (A : Type uA) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (hI : I.FG) :
    derivedPowerTorsionOfRingLifted.{uA, v} A I hI ≅ localCohomologyOfRingLifted.{uA, v} A I hI :=
  derivedPowerTorsionObjIsoLocalCohomologyObj.{uA, v} A I hI
    ((ModuleCat.uliftFunctor.{v, uA} A).obj (ModuleCat.of A A))

/-! ### The outer two equalities of Stacks 0957 -/

/-- **Stacks 0957, the first equality.** `RΓ_I(A) ⊗ᴸ_A B ≅ RΓ_Z(A) ⊗ᴸ_A B`: derived extension of
scalars applied to the identification of the two torsion models over the Noetherian ring `A`. -/
@[stacks 0957 "first equality: RΓ_I(A) ⊗ᴸ B = RΓ_Z(A) ⊗ᴸ B"]
def derivedPowerTorsionOfRingBaseChangeIsoLocalCohomology (A B : Type uA) [CommRing A]
    [CommRing B] [IsNoetherianRing A] (f : A →+* B) (I : Ideal A) (hI : I.FG) :
    (derivedExtensionScalarsGeneral.{uA, 0, uA} f).functor.obj
        (derivedPowerTorsionOfRing A I hI) ≅
      (derivedExtensionScalarsGeneral.{uA, 0, uA} f).functor.obj
        (localCohomologyOfRing A I hI) :=
  (derivedExtensionScalarsGeneral.{uA, 0, uA} f).functor.mapIso
    (derivedPowerTorsionOfRingIsoLocalCohomologyOfRing A I hI)

/-- **Stacks 0957, the last equality.** `RΓ_Y(B) ≅ RΓ_{IB}(B)` for `Y = V(IB)`: the
identification of the two torsion models over the Noetherian ring `B`, read backwards at the
ideal `IB = Ideal.map f I`. -/
@[stacks 0957 "last equality: RΓ_Y(B) = RΓ_{IB}(B)"]
def localCohomologyOfRingIsoDerivedPowerTorsionOfRing (A B : Type uA) [CommRing A] [CommRing B]
    [IsNoetherianRing B] (f : A →+* B) (I : Ideal A) (hI : I.FG) :
    localCohomologyOfRing B (I.map f) (hI.map f) ≅
      derivedPowerTorsionOfRing B (I.map f) (hI.map f) :=
  (derivedPowerTorsionOfRingIsoLocalCohomologyOfRing B (I.map f) (hI.map f)).symm

/-! ### The whole chain of Stacks 0957 -/

/-- **Stacks 0957, the whole chain.** For a homomorphism `f : A → B` of Noetherian rings and a
finitely generated ideal `I ⊆ A`, there is an isomorphism
`RΓ_I(A) ⊗ᴸ_A B ≅ RΓ_{IB}(B)` in `D(B)`, obtained by composing the three isomorphisms of the
source: the first equality, the change-of-rings isomorphism
`Dualizing.localCohomologyOfRingBaseChangeIso`, and the last equality. -/
@[stacks 0957 "the four-term chain, composed, for two rings in one universe"]
def derivedPowerTorsionOfRingBaseChangeIso (A B : Type uA) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) (I : Ideal A) (hI : I.FG) :
    (derivedExtensionScalarsGeneral.{uA, 0, uA} f).functor.obj
        (derivedPowerTorsionOfRing A I hI) ≅
      derivedPowerTorsionOfRing B (I.map f) (hI.map f) :=
  derivedPowerTorsionOfRingBaseChangeIsoLocalCohomology A B f I hI ≪≫
    localCohomologyOfRingBaseChangeIso A B f I hI ≪≫
      localCohomologyOfRingIsoDerivedPowerTorsionOfRing A B f I hI

/-- **Stacks 0957, the whole chain, for two rings in independent universes**, after transporting
both regular modules into a common module universe. -/
@[stacks 0957 "the four-term chain, composed, across universes"]
def derivedPowerTorsionOfRingLiftedBaseChangeIso (A : Type uA) (B : Type uB) [CommRing A]
    [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) (I : Ideal A)
    (hI : I.FG) :
    (derivedExtensionScalarsGeneral.{uA, max uA uB, uB} f).functor.obj
        (derivedPowerTorsionOfRingLifted.{uA, max uA uB} A I hI) ≅
      derivedPowerTorsionOfRingLifted.{uB, max uA uB} B (I.map f) (hI.map f) :=
  (derivedExtensionScalarsGeneral.{uA, max uA uB, uB} f).functor.mapIso
      (derivedPowerTorsionOfRingLiftedIsoLocalCohomologyOfRingLifted.{uA, max uA uB} A I hI) ≪≫
    localCohomologyOfRingLiftedBaseChangeIso A B f I hI ≪≫
      (derivedPowerTorsionOfRingLiftedIsoLocalCohomologyOfRingLifted.{uB, max uA uB} B
        (I.map f) (hI.map f)).symm

end Dualizing

end
