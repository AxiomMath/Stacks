module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkLocalizationCriterion
public import StacksFrontier.Homology.ExtendScalars.Localization

/-!
# Extension of scalars to the localizations detects isomorphisms of modules

A map of modules over a commutative ring is an isomorphism exactly when all of its localizations
at primes are. This module states that criterion for extension of scalars rather than for
`LocalizedModule.map`, which is the form in which a base-change argument meets it: a comparison
map of modules is base changed along `R → R_p`, and what one knows is that the base change is
invertible at every `p`.

## Main results

* `Stacks.StalkLocalization.isIso_extendScalars_map_iff_bijective_localizedMap`: extension of
  scalars to `Localization S` of a map of modules is invertible exactly when the localization of
  that map at `S` is bijective.
* `Stacks.StalkLocalization.isIso_iff_forall_isIso_extendScalars_atPrime`: a map of modules is
  invertible exactly when its extension of scalars to `Localization.AtPrime p` is invertible for
  every prime `p`.

## Implementation notes

The two functors `ModuleCat R ⥤ ModuleCat (Localization S)` — extension of scalars along
`R → Localization S` and the localized-module functor — are identified by
`extendScalars_iso_localizedModuleFunctor`, which also carries out the identification of the
tensor carrier that extension of scalars builds over the restriction of `Localization S` to an
`R`-module. Invertibility is then transported by `CategoryTheory.NatIso.isIso_map_iff`, and the
remaining step compares the two spellings of the localized map, which is
`Stacks.StalkLocalization.bijective_localizedModule_map_iff`.

No tag attribute is placed here. The local criterion itself is [Stacks, Tag 00HN] (6) and is
already carried, unregistered, as
`Stacks.StalkLocalization.bijective_iff_forall_bijective_localizedMap`; nothing below states more
than a restatement of it.

## References

* [Stacks Project, Tag 00HN](https://stacks.math.columbia.edu/tag/00HN)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped ChangeOfRings

universe u

namespace Stacks.StalkLocalization

variable {R : Type u} [CommRing R]

/-- **Extension of scalars to a localization is invertible exactly when the localized map is
bijective.** The two functors to modules over `Localization S` agree, so invertibility of the
base change of `F` is invertibility of the localized-module map, which is bijectivity of
`LocalizedModule.map`. -/
public theorem isIso_extendScalars_map_iff_bijective_localizedMap (S : Submonoid R)
    {M N : ModuleCat.{u} R} (F : M ⟶ N) :
    IsIso ((ModuleCat.extendScalars.{u, u, u} (algebraMap R (Localization S))).map F) ↔
      Function.Bijective (LocalizedModule.map S F.hom) := by
  have h1 : IsIso ((ModuleCat.extendScalars.{u, u, u} (algebraMap R (Localization S))).map F) ↔
      IsIso ((ModuleCat.localizedModuleFunctor.{u} S).map F) :=
    NatIso.isIso_map_iff (extendScalars_iso_localizedModuleFunctor.{u, u} S) F
  have h2 : IsIso ((ModuleCat.localizedModuleFunctor.{u} S).map F) ↔
      Function.Bijective (ModuleCat.localizedModuleMap S F).hom := by
    rw [show (ModuleCat.localizedModuleFunctor.{u} S).map F = ModuleCat.localizedModuleMap S F
      from rfl]
    exact ConcreteCategory.isIso_iff_bijective _
  have h3 : Function.Bijective (ModuleCat.localizedModuleMap S F).hom ↔
      Function.Bijective (IsLocalizedModule.map S (M.localizedModuleMkLinearMap S)
        (N.localizedModuleMkLinearMap S) F.hom) :=
    Iff.of_eq (congrArg Function.Bijective (funext fun _ => rfl))
  exact h1.trans (h2.trans (h3.trans (bijective_localizedModule_map_iff S F.hom
    (M.localizedModuleMkLinearMap S) (N.localizedModuleMkLinearMap S)).symm))

/-- **A map of modules is invertible exactly when all of its base changes to the localizations at
primes are.** This is [Stacks, Tag 00HN] (6) read through extension of scalars. -/
public theorem isIso_iff_forall_isIso_extendScalars_atPrime {M N : ModuleCat.{u} R}
    (F : M ⟶ N) :
    IsIso F ↔ ∀ (p : Ideal R) (_ : p.IsPrime),
      IsIso ((ModuleCat.extendScalars.{u, u, u}
        (algebraMap R (Localization.AtPrime p))).map F) := by
  rw [ConcreteCategory.isIso_iff_bijective, bijective_iff_forall_bijective_localizedMap F.hom]
  refine ⟨fun h p hp => ?_, fun h p hp => ?_⟩
  · exact (isIso_extendScalars_map_iff_bijective_localizedMap p.primeCompl F).mpr (@h p hp)
  · exact (isIso_extendScalars_map_iff_bijective_localizedMap p.primeCompl F).mp (h p hp)

end Stacks.StalkLocalization

end
