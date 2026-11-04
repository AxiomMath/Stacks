module

public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.LocalizationCriterion
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange
import all StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible

/-!
# Dualizing complexes and derived localization away from an element

[Stacks, Tag 0A7G] (`Dualizing.isDualizingComplex_localization`) says that the derived extension
of a dualizing complex along a localization is dualizing, and it is stated for
`StacksDraft.PseudoCoherence.derivedExtensionScalars`. [Stacks, Tag 0A7H]
(`Dualizing.isDualizingComplex_of_localizations`) is the converse gluing statement, and its
hypothesis is stated for `StacksDraft.PseudoCoherence.localizationAwayFunctorAux`. The two
functors are canonically isomorphic at a localization away from one element, but nothing stated
that, so 0A7G could not be used to feed 0A7H.

This file supplies the comparison and the resulting statement in the shape 0A7H consumes:
`Dualizing.isDualizingComplex_localizationAway`, and the two directions together as
`Dualizing.isDualizingComplex_iff_localizationAway`.

## Main definitions

* `Dualizing.uliftDerivedSelfIso` — the module-universe lift `ModuleCat.uliftFunctor.{u, u}`
  induces the identity on `D(R)`. This is a general fact about `Functor.mapDerivedCategory`; it
  is stated here because this is the first place in the library that needs it.
* `Dualizing.derivedExtensionScalarsIsoLocalizationAway` — the comparison
  `derivedExtensionScalars (algebraMap A A_g) ≅ localizationAwayFunctorAux g`.

## Main results

* `Dualizing.isDualizingComplex_localizationAway` — [Stacks, Tag 0A7G] read at the functor
  `localizationAwayFunctorAux` of [Stacks, Tag 0A7H]'s hypothesis.
* `Dualizing.isDualizingComplex_iff_localizationAway` — a complex over a Noetherian ring is
  dualizing exactly when its derived localization at every member of a family generating the unit
  ideal is dualizing. The `←` direction is [Stacks, Tag 0A7H]; the `→` direction needs no
  hypothesis on the family at all.

## Implementation notes

`derivedExtensionScalars` is `(ModuleCat.uliftFunctor _).mapDerivedCategory` composed with the
total derived functor of degreewise extension of scalars, the lift being there so that the three
universes (source ring, target ring, module carrier) may be independent. At a localization away
from one element all three coincide, so the lift is removable, which is the whole content of the
comparison: `Dualizing.uliftDerivedSelfIso` cancels it and the identification of the total
derived functor with `localizationAwayFunctorAux` — both are left derived functors of the same
exact functor — is already in the library.

Both identifications used by the comparison are `private` where they are proved, and are reached
by `import all` rather than re-proved: `Dualizing.isDualizingComplex_of_iso` of
`StacksFrontier/RingTheory/Dualizing/DualizingComplexes/PolynomialBaseChange.lean` (which
`StacksFrontier/RingTheory/Dualizing/NormalizedShift.lean` already reaches the same way) and
`DerivedCategory.Invertible.localizationAwayIso` of
`StacksFrontier/Homology/DerivedCategory/Monoidal/Invertible.lean`. A private name reached that way
may appear in a proof but not in an exposed `def` body, which is why
`Dualizing.derivedExtensionScalarsIsoLocalizationAway` carries `@[no_expose]`.

No `@[stacks]` attribute appears below. 0A7G and 0A7H are both already attributed, at
`StacksFrontier/RingTheory/Dualizing/Complex.lean:1043` and
`StacksFrontier/RingTheory/Dualizing/LocalizationCriterion.lean:616`; what is new here is the
comparison between the two functors they are stated for, which carries no tag of its own.

## References

* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0A7H](https://stacks.math.columbia.edu/tag/0A7H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.PseudoCoherence (derivedExtensionScalars localizationAwayFunctorAux)

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Dualizing

/-- The module-universe lift at one universe induces the identity on the derived category: on
cochain complexes it is degreewise `ULift.moduleEquiv`, and `Functor.mapDerivedCategory` is
determined by its factorisation through `DerivedCategory.Q`. -/
noncomputable def uliftDerivedSelfIso (R : Type u) [CommRing R] :
    (ModuleCat.uliftFunctor.{u, u} R).mapDerivedCategory ≅
      𝟭 (DerivedCategory (ModuleCat.{u} R)) := by
  let U := ModuleCat.uliftFunctor.{u, u} R
  let Uc := U.mapHomologicalComplex (ComplexShape.up ℤ)
  let ηc : Uc ≅ 𝟭 (CochainComplex (ModuleCat.{u} R) ℤ) :=
    NatIso.ofComponents (fun K =>
      HomologicalComplex.Hom.isoOfComponents
        (fun _ => ULift.moduleEquiv.toModuleIso)
        (by intro i j hij; rfl)) (by
      intro K L f
      ext i x
      rfl)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ U.mapDerivedCategory) (DerivedCategory.Q ⋙ 𝟭 _)
    U.mapDerivedCategory (𝟭 _)
    (U.mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight ηc DerivedCategory.Q ≪≫ Functor.leftUnitor _)

/-- Derived extension of scalars along `A → A_g` is the derived localization away from `g`: the
universe lift inside `derivedExtensionScalars` is the identity here, since the two rings and the
module carrier live in the same universe, and what remains is the total derived functor of
degreewise extension of scalars, which is `localizationAwayFunctorAux g`. -/
@[no_expose] noncomputable def derivedExtensionScalarsIsoLocalizationAway
    (A : Type u) [CommRing A] (g : A) :
    derivedExtensionScalars.{u, u, u} (algebraMap A (Localization.Away g)) ≅
      localizationAwayFunctorAux.{u, u} g := by
  unfold derivedExtensionScalars
  exact Functor.isoWhiskerRight (uliftDerivedSelfIso A) _ ≪≫ Functor.leftUnitor _ ≪≫
    DerivedCategory.Invertible.localizationAwayIso.{u, u} g

/-- **Stacks Project, Tag 0A7G**, read at the functor of [Stacks, Tag 0A7H]'s hypothesis: the
derived localization of a dualizing complex away from an element is a dualizing complex over the
localized ring. -/
theorem isDualizingComplex_localizationAway {A : Type u} [CommRing A] [IsNoetherianRing A]
    (g : A) (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsDualizingComplex K) :
    IsDualizingComplex ((localizationAwayFunctorAux.{u, u} g).obj K) :=
  isDualizingComplex_of_iso ((derivedExtensionScalarsIsoLocalizationAway A g).app K)
    (isDualizingComplex_localization (B := Localization.Away g) (Submonoid.powers g) K hK)

/-- A complex over a Noetherian ring is dualizing exactly when its derived localization at every
member of a family generating the unit ideal is dualizing.

The `←` direction is [Stacks, Tag 0A7H] (`isDualizingComplex_of_localizations`). The `→`
direction is [Stacks, Tag 0A7G] and uses neither `hspan` nor the family: each localization of a
dualizing complex is dualizing. -/
theorem isDualizingComplex_iff_localizationAway {A : Type u} [CommRing A] [IsNoetherianRing A]
    {ι : Type w} (f : ι → A) (hspan : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsDualizingComplex K ↔
      ∀ i, IsDualizingComplex ((localizationAwayFunctorAux.{u, u} (f i)).obj K) :=
  ⟨fun hK i => isDualizingComplex_localizationAway (f i) K hK,
    isDualizingComplex_of_localizations f K hspan⟩

end Dualizing

end
