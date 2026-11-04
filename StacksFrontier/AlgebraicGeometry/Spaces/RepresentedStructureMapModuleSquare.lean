module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange

/-!
# The square of small étale ringed sites of a representable morphism, on structure modules

Let `B` be a big fppf site containing a scheme `S` and let `g : T' ⟶ T` be a morphism of the big
fppf category over `S`.  `AlgebraicGeometry.Space.representedStructureMapRing_square` says that
the two routes round the square of small étale ringed sites
```
  (yoneda.obj T')_étale ⟶ (yoneda.obj T)_étale
        |                        |
  (T'-scheme)_étale  ⟶     (T-scheme)_étale
```
carry the structure sheaf of **rings** of `T` to the structure sheaf of rings of `T'` by the same
map.  This file reads that square on the structure sheaves as **modules**: the two routes carry
`𝒪_T`, regarded as a module over itself, to `𝒪_{T'}`, regarded as a module over itself, by the
same morphism of sheaves of modules.

## Main results

* `AlgebraicGeometry.Space.unitToPushforwardObjUnit_representedStructureMapRing_square`: **the
  module-level counterpart of `AlgebraicGeometry.Space.representedStructureMapRing_square`**,
  with each of the two routes written as the composite of the morphisms of modules attached to
  its two legs.

## Implementation notes

The reading is by `SheafOfModules.unitToPushforwardObjUnit`, which sends a
comparison `φ : R ⟶ F_*R'` of sheaves of rings to the morphism `𝒪 ⟶ F_*𝒪'` of sheaves of modules
whose component over an object of the site is the component of `φ` with its ring structure
forgotten.  Both routes round the square are composites of two legs, so the two general lemmas of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModulePullbackUnit.lean` reduce the
statement to the ring-level square itself: the composite comparison of a route is read leg by leg
by `SheafOfModules.unitToPushforwardObjUnit_comparisonComp_eq_comp`, and the comparison of
the two direct images attached to the identification of the two base changes carries one reading
to the other by
`SheafOfModules.unitToPushforwardObjUnit_comp_pushforwardCongr₂_hom_app`.

The proof is written as a term rather than by `rw`.  The two composite comparisons of the square
mix the two spellings of the structure sheaf of rings of an algebraic space described in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackBaseChange.lean` —
`AlgebraicGeometry.Space.smallEtaleRingSheaf` on the base-change leg and
`AlgebraicGeometry.Space.ringStructureSheaf` on the identification leg — which agree at default
transparency but not at the transparency at which `rw` matches, so the goal is reported as not
type-correct and no rewrite fires.  `CategoryTheory.congrArg` and `Eq.trans` elaborate at default
transparency and are unaffected.

The left-hand route's direct image is `SheafOfModules.pushforward` of the
structure comparison of the identification of the two sites, which is
`AlgebraicGeometry.Space.representedModulePushforward` — the functor of
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` — by `rfl`; it is written in the
`pushforward` form so that both routes are visibly composites of the same shape.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] isContinuous_smallBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- **The two routes round the square of small étale ringed sites carry the structure sheaf of
`T`, read as a module over itself, to the structure sheaf of `T'`, read as a module over itself,
by the same morphism.**  This is
`AlgebraicGeometry.Space.representedStructureMapRing_square` read on modules: each route is the
composite of the morphisms of modules attached to its two legs — the identification of the small
étale site of a representable algebraic space with the small étale site of the underlying scheme,
and base change along the morphism in question — and the comparison of the two direct images
attached to the identification of the two base changes matches them. -/
theorem unitToPushforwardObjUnit_representedStructureMapRing_square :
    (SheafOfModules.unitToPushforwardObjUnit (representedEquivSharp B S hS T) ≫
          (SheafOfModules.pushforward.{u} (representedEquivSharp B S hS T)).map
            (SheafOfModules.unitToPushforwardObjUnit
              (representedSchemeStructureMapRing B S hS g))) ≫
        (SheafOfModules.pushforwardCongr₂.{u} _
          (representedSmallEtaleBaseChangeIso B S hS g hg)
          (representedStructureMapRing_square B S hS g hg)).hom.app
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')) =
      SheafOfModules.unitToPushforwardObjUnit
            (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg) ≫
        (SheafOfModules.pushforward.{u}
          (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)).map
          (SheafOfModules.unitToPushforwardObjUnit (representedEquivSharp B S hS T')) :=
  (congrArg (fun z ↦ z ≫ (SheafOfModules.pushforwardCongr₂.{u} _
        (representedSmallEtaleBaseChangeIso B S hS g hg)
        (representedStructureMapRing_square B S hS g hg)).hom.app
        (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T')))
      (SheafOfModules.unitToPushforwardObjUnit_comparisonComp_eq_comp
        (representedEquivSharp B S hS T)
        (representedSchemeStructureMapRing B S hS g))).symm.trans
    ((SheafOfModules.unitToPushforwardObjUnit_comp_pushforwardCongr₂_hom_app _ _ _).trans
      (SheafOfModules.unitToPushforwardObjUnit_comparisonComp_eq_comp _ _))

end AlgebraicGeometry.Space

end
