module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionLift
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientRestrictionTransport

/-!
# Global sections on a localised small crystalline site are global sections on the ambient scheme

This is the small-site counterpart of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionLift`.
[Stacks, Tag 07IT] is stated for `𝒞 = CRIS(X/S)` and for `𝒞 = Cris(X/S)` alike, and a sheaf of
modules on `Cris(X/S)` is in general not the restriction of one on `CRIS(X/S)`, so the bijection
is repeated here.

## Main results

* `SmallSite.CrystallineThickening.isTerminal_ambientOverFunctorObjTop`: the image of the
  terminal object of the localised Zariski site under the ambient restriction at the identity of
  `B` is terminal in `Cris(X/S)/B`.
* `SmallSite.CrystallineThickening.uliftUnitHomEquiv_pushforward_map`: the two readings of a
  global section agree on the nose.
* `SmallSite.CrystallineThickening.bijective_pushforward_map_uliftUnit`: restriction along the
  ambient restriction at the identity of `B` is bijective on morphisms out of the universe lift of
  the structure sheaf.

## Implementation notes

The proof is the big site's: both sides of the bijection are instances of
`SheafOfModules.uliftUnitHomEquiv` for two terminal objects of `Cris(X/S)/B`, the terminal object
`CategoryTheory.Over.mkIdTerminal` and the image of the terminal object of the localised Zariski
site, and the triangle relating them commutes by `rfl`.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
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

/-- **The ambient restriction at the identity of `B` carries the terminal object of the localised
Zariski site to a terminal object of the localised small crystalline site.** -/
noncomputable def isTerminal_ambientOverFunctorObjTop :
    IsTerminal ((ambientOverFunctor B (Over.mk (𝟙 B))).obj
      (Over.mk (𝟙 (⊤ : (Over.mk (𝟙 B) : Over B).left.obj.thickening.target.scheme.Opens)))) :=
  IsTerminal.ofIso (Over.mkIdTerminal (X := B))
    (ambientOverFunctorObjTopIso B (Over.mk (𝟙 B))).symm

/-- **The global section attached to the ambient restriction of a morphism out of the universe
lift of the structure sheaf is the global section attached to the morphism itself**, read over the
image of the terminal object of the localised Zariski site. -/
theorem uliftUnitHomEquiv_pushforward_map
    (Z : SheafOfModules.{u + 1} ((structureSheaf S).over B))
    (φ : SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
      (SheafOfModules.unit ((structureSheaf S).over B)) ⟶ Z) :
    SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1}
        (Over.mkIdTerminal
          (X := (⊤ : (Over.mk (𝟙 B) : Over B).left.obj.thickening.target.scheme.Opens)))
        ((SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj Z)
        ((SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map φ) =
      SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
        (isTerminal_ambientOverFunctorObjTop B) Z φ :=
  rfl

/-- **Restriction along the ambient restriction at the identity of `B` is bijective on morphisms
out of the universe lift of the structure sheaf of the localised small crystalline site.** This is
the statement with which a presentation chosen on the affine ambient scheme is lifted to the
localised site. -/
theorem bijective_pushforward_map_uliftUnit
    (Z : SheafOfModules.{u + 1} ((structureSheaf S).over B)) :
    Function.Bijective
      (fun φ : SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
          (SheafOfModules.unit ((structureSheaf S).over B)) ⟶ Z ↦
        (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map φ) := by
  have hcomp : (fun φ : SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (SheafOfModules.unit ((structureSheaf S).over B)) ⟶ Z ↦
      SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1}
        (Over.mkIdTerminal
          (X := (⊤ : (Over.mk (𝟙 B) : Over B).left.obj.thickening.target.scheme.Opens)))
        ((SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj Z)
        ((SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map φ)) =
      fun φ ↦ SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
        (isTerminal_ambientOverFunctorObjTop B) Z φ :=
    funext fun φ ↦ uliftUnitHomEquiv_pushforward_map B Z φ
  have hright : Function.Bijective
      (fun ψ : SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
            (SheafOfModules.unit
              ((Thickening.ringRestrictionSheaf
                (Over.mk (𝟙 B) : Over B).left.obj).over ⊤)) ⟶
          (SheafOfModules.pushforward.{u + 1}
            (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj Z ↦
        SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1}
          (Over.mkIdTerminal
            (X := (⊤ : (Over.mk (𝟙 B) : Over B).left.obj.thickening.target.scheme.Opens)))
          ((SheafOfModules.pushforward.{u + 1}
            (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj Z) ψ) :=
    (SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1} _ _).bijective
  have hleft : Function.Bijective
      (fun φ : SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
          (SheafOfModules.unit ((structureSheaf S).over B)) ⟶ Z ↦
        SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
          (isTerminal_ambientOverFunctorObjTop B) Z φ) :=
    (SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
      (isTerminal_ambientOverFunctorObjTop B) Z).bijective
  rw [← hcomp] at hleft
  exact (hright.of_comp_iff' _).1 hleft

end CrystallineThickening

end SmallSite

end Crystalline.GlobalCrystallineSituation

end
