module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionConservative
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.CrystalPresentationPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits

/-!
# The ambient restrictions of a module on a localised crystalline site are its ambient restrictions

The functors of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionConservative` were
built so that restriction of sheaves of modules along them *computes* the restrictions `F_T` of
[Stacks, Tag 07IQ].  This file records that identification, which holds on the nose, and draws the
consequence that the direction (2) ⇒ (1) of [Stacks, Tag 07IT] needs: for a locally quasi-coherent
crystal in `𝒪_{X/S}`-modules and an object `(U', T', δ')` with affine ambient scheme, *every*
ambient restriction of the module on the localised site `CRIS(X/S)/(U', T', δ')` has a global
presentation, at the module universe `u + 1` in which a global presentation on that localised site
is read.

## Main results

* `GlobalCrystallineSituation.Thickening.pushforward_ambientOverStructureHom_obj_unit`
  — restriction along the ambient restrictions carries the universe lift of the structure sheaf of
  the localised site to the universe lift of the structure sheaf of the Zariski site of the
  ambient scheme.
* `GlobalCrystallineSituation.Thickening.pushforward_ambientOverStructureHom_obj_ulift`
  — restriction along the ambient restrictions carries the universe lift of a module on the
  localised site to the universe lift of its restriction `F_T`.
* `GlobalCrystallineSituation.hasGlobalPresentation_pushforward_ambientOverStructureHom`
  — **for a locally quasi-coherent crystal and an object with affine ambient scheme, every ambient
  restriction of the module on the localised site has a global presentation**, read at the module
  universe `u + 1`.

## Implementation notes

Both identifications hold by `rfl`.  The restriction of `𝒪_{X/S}` to the opens of the ambient
scheme of an object is by definition its restriction along
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenFunctor`, the comparison of
structure sheaves along
`Crystalline.GlobalCrystallineSituation.Thickening.ambientOverFunctor` is the identity, and the
universe lift of a module changes the sections but not the site; so both sides of each equation
are the same presheaf of modules on the same site.  That is the point of building the family out
of `CategoryTheory.Over.post` and `CategoryTheory.Over.map`: the composite with the forgetful
functor of the slice is the restriction functor itself, not merely isomorphic to it.

The global presentation is assembled from three inputs.  The restriction `F_T` over an
object of the localised site has a global presentation by
`hasGlobalPresentation_moduleRestrictionSheaf_of_isSheafCrystal_isAffine`: the presentation of
`F_{T'}` on the affine ambient scheme of the base object is carried along the invertible
comparison map of the structure morphism of the object.  That presentation is carried
to the slice of the Zariski site at the greatest open by
`Stacks.SheafOfModules.hasGlobalPresentation_over`, and raised to the module universe `u + 1` by
`SheafOfModules.hasGlobalPresentation_uliftForPresentation'`.  The universes only force the last
step: a global presentation on the localised crystalline site is indexed by `Type (u + 1)` and
read at the module universe `u + 1`, while the presentations of the `F_T` are indexed by `Type u`
on the Zariski sites.

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

namespace Thickening

variable (B : Thickening S)

/-- **Restriction along an ambient restriction carries the universe lift of the structure sheaf
of the localised crystalline site to the universe lift of the structure sheaf of the Zariski site
of the ambient scheme.** -/
theorem pushforward_ambientOverStructureHom_obj_unit (X : Over B) :
    (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
          (SheafOfModules.unit ((crystallineStructureSheaf S).over B))) =
      SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
        (SheafOfModules.unit ((X.left.ringRestrictionSheaf).over ⊤)) :=
  rfl

/-- **Restriction along an ambient restriction carries the universe lift of a sheaf of
`𝒪_{X/S}`-modules on the localised crystalline site to the universe lift of its restriction
`F_T`.**  Over an open `W` of the ambient scheme of the object `X` both sides are the sections of
`F` over the restriction of `X` to `W`, lifted to the universe `u + 1`. -/
theorem pushforward_ambientOverStructureHom_obj_ulift
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (X : Over B) :
    (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B)) =
      SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
        ((moduleRestrictionSheaf M X.left).over ⊤) :=
  rfl

end Thickening

/-- **For a locally quasi-coherent crystal in `𝒪_{X/S}`-modules and an object `(U', T', δ')` with
affine ambient scheme, every ambient restriction of the module on the localised site
`CRIS(X/S)/(U', T', δ')` has a global presentation**, at the module universe `u + 1` at which a
global presentation on that localised site is read. -/
theorem hasGlobalPresentation_pushforward_ambientOverStructureHom
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hlqc : IsLocallyQuasiCoherent M)
    (hcrys : IsSheafCrystal M) (B : Thickening S) [IsAffine B.thickening.target.scheme]
    (X : Over B) :
    ((SheafOfModules.pushforward.{u + 1} (Thickening.ambientOverStructureHom B X)).obj
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (M.over B))).HasGlobalPresentation := by
  rw [Thickening.pushforward_ambientOverStructureHom_obj_ulift]
  exact SheafOfModules.hasGlobalPresentation_uliftForPresentation'.{u, u, u, u, u + 1}
    (Stacks.SheafOfModules.hasGlobalPresentation_over.{u, u, u, u}
      (Thickening.moduleRestrictionSheaf M X.left) ⊤
      (hasGlobalPresentation_moduleRestrictionSheaf_of_isSheafCrystal_isAffine hlqc hcrys X.hom))

end Crystalline.GlobalCrystallineSituation

end
