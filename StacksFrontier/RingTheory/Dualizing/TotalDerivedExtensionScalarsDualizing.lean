module

public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.AdicCompletion
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange

/-!
# Dualizing complexes under the total derived functor of extension of scalars

[Stacks, Tag 0A7G] (`Dualizing.isDualizingComplex_localization`) and [Stacks, Tag 0DWD]
(`Dualizing.isDualizingComplex_adicCompletion`) are stated for
`StacksDraft.PseudoCoherence.derivedExtensionScalars` and for
`(ModuleCat.extendScalars _).mapDerivedCategory` respectively. Neither is the functor that the
base change of an `Ext` system along a localization or a completion produces: that one is
`(CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars _).functor`, the second
factor of `derivedExtensionScalars` on its own, which is the spelling appearing in
`Stacks.Algebraization.dualizingExtSystemLocalizationNatIso` and in
`Stacks.Algebraization.dualizingExtSystemAdicCompletionNatIso`.

This file states both tags at that functor. Nothing new is proved: when extension of scalars is
exact the comparison of the total derived functor is invertible, which is
`Dualizing.totalDerivedExtensionScalarsIsoExtendScalars`, and transporting along it is
`Dualizing.isDualizingComplex_of_iso`.

## Main results

* `Dualizing.isDualizingComplex_totalDerivedExtensionScalars_isLocalization` —
  [Stacks, Tag 0A7G] at `(totalDerivedExtensionScalars (algebraMap A B)).functor` for `B` a
  localization of `A`.
* `Dualizing.isDualizingComplex_totalDerivedExtensionScalars_adicCompletion` —
  [Stacks, Tag 0DWD] at `(totalDerivedExtensionScalars (algebraMap A A^∧)).functor`.

## Implementation notes

Exactness of extension of scalars is not taken as a hypothesis: it is available from flatness in
both cases, by `IsLocalization.flat` and by `AdicCompletion.flat_of_isNoetherian`, through
`extendScalars_preservesFiniteLimits_of_flat'`. Since
`CategoryTheory.Functor.mapDerivedCategory` takes that exactness as an instance argument, the
two tags are applied inside the proofs, where the instance has been introduced.

No `@[stacks]` attribute appears below: 0A7G and 0DWD are both already attributed, at
`StacksFrontier/RingTheory/Dualizing/Complex.lean:1061` and
`StacksFrontier/RingTheory/Dualizing/UbiquityDualizingComplexes/AdicCompletion.lean:92`; what is
new here is a change of functor, which carries no tag of its own.

## References

* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0DWD](https://stacks.math.columbia.edu/tag/0DWD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **Stacks Project, Tag 0A7G**, read at the total derived functor of degreewise extension of
scalars: the derived extension of a dualizing complex to a localization is a dualizing complex
over the localized ring. -/
theorem isDualizingComplex_totalDerivedExtensionScalars_isLocalization {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A] (S : Submonoid A)
    [IsLocalization S B] (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsDualizingComplex K) :
    letI : IsNoetherianRing B := IsLocalization.isNoetherianRing S B inferInstance
    IsDualizingComplex
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)).functor.obj K) :=
  let : IsNoetherianRing B := IsLocalization.isNoetherianRing S B inferInstance
  let : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap A B)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B S))
  isDualizingComplex_of_iso
    ((totalDerivedExtensionScalarsIsoExtendScalars (algebraMap A B)).app K).symm
    (isDualizingComplex_extendScalars_of_isLocalization S K hK)

/-- **Stacks Project, Tag 0DWD**, read at the total derived functor of degreewise extension of
scalars: the derived base change of a dualizing complex to the completion of a Noetherian ring
along any ideal is a dualizing complex. -/
theorem isDualizingComplex_totalDerivedExtensionScalars_adicCompletion {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsDualizingComplex K) :
    IsDualizingComplex
      ((totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A (AdicCompletion I A))).functor.obj K) :=
  let : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion I A))) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, u} _
      (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian I))
  isDualizingComplex_of_iso
    ((totalDerivedExtensionScalarsIsoExtendScalars
      (algebraMap A (AdicCompletion I A))).app K).symm
    (isDualizingComplex_adicCompletion I K hK)

end Dualizing

end
