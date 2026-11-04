module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.PresentationLifting

/-!
# Global sections on a localised crystalline site are global sections on the ambient scheme

Let `B` be an object of the big crystalline site of a global crystalline situation and let
`CRIS(X/S)/B` be the localisation of the site at it.  The ambient restriction attached to the
*identity* of `B` — the functor of
`Crystalline.GlobalCrystallineSituation.Thickening.ambientOverFunctor` at the terminal object of
`CRIS(X/S)/B` — carries the terminal object of the Zariski site of the ambient scheme of `B`,
localised at its greatest open, to an object isomorphic to the terminal object of `CRIS(X/S)/B`.

Consequently restriction along it is a *bijection* on morphisms out of the universe lift of the
structure sheaf: a global section of a sheaf of modules on `CRIS(X/S)/B` is the same thing as a
global section of its restriction to the ambient scheme of `B`.

That bijection is what the direction (2) ⇒ (1) of [Stacks, Tag 07IT] needs in order to *lift* the
generators and the relations of a presentation of `F_{T'}` on the affine ambient scheme `T'` to
morphisms on the localised crystalline site, where the presentation of `F` has to be assembled.
Without it one would have to compute the global sections of a coproduct of copies of the structure
sheaf on the crystalline site, which is the step the earlier implementation notes of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.CrystalPresentationPullback` could not
take.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.isTerminal_ambientOverFunctorObjTop` — the
  image of the terminal object of the localised Zariski site under the ambient restriction at the
  identity of `B` is terminal in `CRIS(X/S)/B`.
* `Crystalline.GlobalCrystallineSituation.Thickening.uliftUnitHomEquiv_pushforward_map` — the
  global section attached to the restriction of a morphism out of the universe lift of the
  structure sheaf is the global section attached to the morphism itself, read at the image of the
  terminal object.  This holds by `rfl`.
* `Crystalline.GlobalCrystallineSituation.Thickening.bijective_pushforward_map_uliftUnit` —
  **restriction along the ambient restriction at the identity of `B` is bijective on morphisms out
  of the universe lift of the structure sheaf.**

## Implementation notes

`SheafOfModules.uliftUnitHomEquiv` of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.PresentationLifting` reads a
morphism out of `SheafOfModules.uliftForPresentation` of the structure sheaf as its value at
`SheafOfModules.uliftUnitGen` over a terminal object.  Both sides of the bijection below are
instances of it, for two different terminal objects of the *same* category: the terminal object
`CategoryTheory.Over.mkIdTerminal` of `CRIS(X/S)/B`, and the image of the terminal object of the
localised Zariski site, which is terminal by
`CategoryTheory.Limits.IsTerminal.ofIso` and
`Crystalline.GlobalCrystallineSituation.Thickening.ambientOverFunctorObjTopIso`.  The two
evaluations agree on the nose, restriction along a functor of sites being evaluation at the image
of the object and the comparison of structure sheaves being the identity, so the triangle
commutes by `rfl` and bijectivity follows from that of the two equivalences.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace Thickening

variable (B : Thickening S)

/-- **The ambient restriction at the identity of `B` carries the terminal object of the localised
Zariski site to a terminal object of the localised crystalline site.**  Its image is the
restriction of `B` to the whole of its ambient scheme, which is isomorphic to `B` itself by
`Crystalline.GlobalCrystallineSituation.Thickening.ambientOverFunctorObjTopIso`, and `B` with its
identity is terminal in `CRIS(X/S)/B`. -/
noncomputable def isTerminal_ambientOverFunctorObjTop :
    IsTerminal ((ambientOverFunctor B (Over.mk (𝟙 B))).obj
      (Over.mk (𝟙 (⊤ : (Over.mk (𝟙 B) : Over B).left.thickening.target.scheme.Opens)))) :=
  IsTerminal.ofIso (Over.mkIdTerminal (X := B))
    (ambientOverFunctorObjTopIso B (Over.mk (𝟙 B))).symm

/-- **The global section attached to the ambient restriction of a morphism out of the universe
lift of the structure sheaf is the global section attached to the morphism itself**, read over the
image of the terminal object of the localised Zariski site.  Restriction along a functor of sites
is evaluation at the image of the object, the comparison of structure sheaves is the identity, and
the generating section matches, so the two readings agree on the nose. -/
theorem uliftUnitHomEquiv_pushforward_map
    (Z : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B))
    (φ : SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
      (SheafOfModules.unit ((crystallineStructureSheaf S).over B)) ⟶ Z) :
    SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1}
        (Over.mkIdTerminal
          (X := (⊤ : (Over.mk (𝟙 B) : Over B).left.thickening.target.scheme.Opens)))
        ((SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj Z)
        ((SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map φ) =
      SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
        (isTerminal_ambientOverFunctorObjTop B) Z φ :=
  rfl

/-- **Restriction along the ambient restriction at the identity of `B` is bijective on morphisms
out of the universe lift of the structure sheaf of the localised crystalline site.**

A morphism out of that lift is its value at the generating section over a terminal object, and the
ambient restriction at the identity of `B` hits a terminal object; so the two readings are two
bijections with the same composite, and restriction is the comparison between them.

This is the statement with which a presentation chosen on the affine ambient scheme is lifted to
the localised crystalline site: each generator and each relation is a morphism out of the lift of
the structure sheaf there, and has a unique preimage here. -/
theorem bijective_pushforward_map_uliftUnit
    (Z : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)) :
    Function.Bijective
      (fun φ : SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
          (SheafOfModules.unit ((crystallineStructureSheaf S).over B)) ⟶ Z ↦
        (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map φ) := by
  have hcomp : (fun φ : SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
        (SheafOfModules.unit ((crystallineStructureSheaf S).over B)) ⟶ Z ↦
      SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1}
        (Over.mkIdTerminal
          (X := (⊤ : (Over.mk (𝟙 B) : Over B).left.thickening.target.scheme.Opens)))
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
              (((Over.mk (𝟙 B) : Over B).left.ringRestrictionSheaf).over ⊤)) ⟶
          (SheafOfModules.pushforward.{u + 1}
            (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj Z ↦
        SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1}
          (Over.mkIdTerminal
            (X := (⊤ : (Over.mk (𝟙 B) : Over B).left.thickening.target.scheme.Opens)))
          ((SheafOfModules.pushforward.{u + 1}
            (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj Z) ψ) :=
    (SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1} _ _).bijective
  have hleft : Function.Bijective
      (fun φ : SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
          (SheafOfModules.unit ((crystallineStructureSheaf S).over B)) ⟶ Z ↦
        SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
          (isTerminal_ambientOverFunctorObjTop B) Z φ) :=
    (SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
      (isTerminal_ambientOverFunctorObjTop B) Z).bijective
  rw [← hcomp] at hleft
  exact (hright.of_comp_iff' _).1 hleft

end Thickening

end Crystalline.GlobalCrystallineSituation

end
