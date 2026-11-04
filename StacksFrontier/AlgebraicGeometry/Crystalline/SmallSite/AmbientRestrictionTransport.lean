module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionTransport
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientRestrictionConservative

/-!
# The ambient restrictions on a localised small crystalline site compute `F_T`

This is the small-site counterpart of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionTransport`.
[Stacks, Tag 07IT] is stated for `𝒞 = CRIS(X/S)` and for `𝒞 = Cris(X/S)` alike, and a sheaf of
modules on `Cris(X/S)` is in general not the restriction of one on `CRIS(X/S)`, so the
identification and its consequence are repeated here.

## Main results

* `SmallSite.CrystallineThickening.pushforward_ambientOverStructureHom_obj_unit`
  — restriction along an ambient restriction carries the universe lift of the structure sheaf of
  the localised small crystalline site to the universe lift of the structure sheaf of the Zariski
  site of the ambient scheme.
* `SmallSite.CrystallineThickening.pushforward_ambientOverStructureHom_obj_ulift`
  — restriction along an ambient restriction carries the universe lift of a module on the
  localised small crystalline site to the universe lift of its restriction `F_T`.
* `SmallSite.hasGlobalPresentation_pushforward_ambientOverStructureHom`
  — **for a locally quasi-coherent crystal on `Cris(X/S)` and an object with affine ambient
  scheme, every ambient restriction of the module on the localised site has a global
  presentation**, read at the module universe `u + 1`.

## Implementation notes

As on the big site both identifications hold by `rfl`: the comparison of structure sheaves along
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.ambientOverFunctor` is the
identity, and the restriction of a module to the opens of the ambient scheme of an object of
`Cris(X/S)` is its restriction along
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.restrictOpenFunctor`, which
is the composite of that functor with the forgetful functor of the slice.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace SmallSite

namespace CrystallineThickening

variable (B : CrystallineThickening S)

/-- **Restriction along an ambient restriction carries the universe lift of the structure sheaf
of the localised small crystalline site to the universe lift of the structure sheaf of the Zariski
site of the ambient scheme.** -/
theorem pushforward_ambientOverStructureHom_obj_unit (X : Over B) :
    (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
          (SheafOfModules.unit ((structureSheaf S).over B))) =
      SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
        (SheafOfModules.unit
          ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤)) :=
  rfl

/-- **Restriction along an ambient restriction carries the universe lift of a sheaf of
`𝒪_{X/S}`-modules on the localised small crystalline site to the universe lift of its restriction
`F_T`.** -/
theorem pushforward_ambientOverStructureHom_obj_ulift
    (M : SheafOfModules.{u} (structureSheaf S)) (X : Over B) :
    (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B)) =
      SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
        ((CohomologyRestriction.moduleRestrictionSheaf M X.left).over ⊤) :=
  rfl

end CrystallineThickening

/-- **For a locally quasi-coherent crystal in `𝒪_{X/S}`-modules on `Cris(X/S)` and an object with
affine ambient scheme, every ambient restriction of the module on the localised site has a global
presentation**, at the module universe `u + 1` at which a global presentation on that localised
site is read. -/
theorem hasGlobalPresentation_pushforward_ambientOverStructureHom
    {M : SheafOfModules.{u} (structureSheaf S)} (hlqc : IsLocallyQuasiCoherent M)
    (hcrys : IsSheafCrystal M) (B : CrystallineThickening S)
    [IsAffine B.obj.thickening.target.scheme] (X : Over B) :
    ((SheafOfModules.pushforward.{u + 1}
      (CrystallineThickening.ambientOverStructureHom B X)).obj
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (M.over B))).HasGlobalPresentation := by
  rw [CrystallineThickening.pushforward_ambientOverStructureHom_obj_ulift]
  exact SheafOfModules.hasGlobalPresentation_uliftForPresentation'.{u, u, u, u, u + 1}
    (Stacks.SheafOfModules.hasGlobalPresentation_over.{u, u, u, u}
      (CohomologyRestriction.moduleRestrictionSheaf M X.left) ⊤
      (hasGlobalPresentation_moduleRestrictionSheaf_of_isSheafCrystal_isAffine hlqc hcrys X.hom))

end SmallSite

end Crystalline.GlobalCrystallineSituation

end
