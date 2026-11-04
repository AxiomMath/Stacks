module

public import StacksFrontier.AlgebraicGeometry.Spaces.AssociatedModulePullbackUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModulePullbackNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleObjPullbackUnit
public import StacksFrontier.CategoryTheory.CompositeGluing

/-!
# The transport of the inverse image at an associated module, read at the unit module

`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` carries the inverse image of
`𝒪`-modules along a represented morphism of algebraic spaces, applied to the associated module
of a Zariski module, onto the associated module of the Zariski pullback. This file reads that
comparison at the **unit** module — the structure sheaf — and shows that it carries the
canonical map `φ^*𝒪 ⟶ 𝒪` of the represented morphism to the associated module of the Zariski
map `r^*𝒪 ⟶ 𝒪` of the underlying morphism of schemes.

That is the compatibility the agreement of the canonical maps of conormal sheaves of
[Stacks Project, Tag 04G2] part (2) rests on: both canonical maps are, after the square
comparison, the inverse image of a single map of ideal sheaves, and a map of ideal sheaves is
determined by its composite with the inclusion into the structure sheaf followed by exactly this
canonical map.

## The composition that is carried out here

The comparison is the composite of two factors, and the unit-module compatibility of each is
already available:

* the first factor `AlgebraicGeometry.Space.representedModuleObjPullbackIso` carries `φ^*𝒪 ⟶ 𝒪`
  to the canonical map of the morphism of small étale ringed sites of
  [Stacks Project, Tag 070R] (2) — that is
  `AlgebraicGeometry.Space.structureModulePullbackMap_representedModuleObjPullbackIso`;
* the second factor `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso` of
  [Stacks Project, Tag 03LC] (1) carries that canonical map to the associated module of the
  Zariski one — that is
  `AlgebraicGeometry.SmallEtale.pullbackObjUnitToUnit_associatedModuleBaseChangeIso`.

What makes the composition more than a concatenation is that the first statement is at the
structure sheaf of the small étale site, while the comparison's first factor is applied to the
*associated module of the Zariski structure sheaf*. The two are compared by the canonical map
`SheafOfModules.pullbackObjUnitToUnit` of the structure comparison of
[Stacks Project, Tag 03DU] (4), and moving the first statement along it is exactly the
naturality of the comparison in the module —
`AlgebraicGeometry.Space.representedModuleObjPullbackIso_naturality`.

## Main results

* `AlgebraicGeometry.Space.pullback_pullbackObjUnitToUnit_comp`:
  [Stacks Project, Tag 03LC] (1) at the unit module, rearranged so that the base-change
  comparison appears on the other side.
* `AlgebraicGeometry.Space.structureModulePullbackMap_representedAssociatedModulePullbackIso`:
  **the transport at an associated module carries `φ^*𝒪 ⟶ 𝒪` to the associated module of the
  Zariski `r^*𝒪 ⟶ 𝒪`.**

## Implementation notes

The whole file turns on the single delta separating
`AlgebraicGeometry.SmallEtale.associatedModule` from the pullback along the structure comparison
that it is defined to be. The source of `SheafOfModules.pullbackObjUnitToUnit` of the structure
comparison is written at the *pullback* spelling, while the transport is applied to the
*associated module*, so that delta has to be crossed somewhere, and
`AlgebraicGeometry.Space.representedModuleObjPullbackIso` is an expensive place to cross it.

Crossing it by `exact`, letting the module arguments be solved by
unification, is a `whnf` timeout at 200000 heartbeats — in the final assembly, in a restatement
of the naturality on its own, and in an equation of isomorphisms presenting the transport at the
unit module with the pullback spelling, all three. Crossing it with the two module arguments of
the naturality given **explicitly**, which is what
`AlgebraicGeometry.Space.representedModuleObjPullbackIso_naturality_associatedModule` does, is
9 s for the file. The delta then has to be decided only where the given module is checked
against the given morphism's type, and not underneath the comparison.

Every step is applied as a generic lemma — `Stacks.CategoryTheory.comp_eq_comp_of_glue` and
`Stacks.CategoryTheory.map_square` — with no `rw` on a geometric term anywhere: the Zariski
structure sheaf of a scheme is a `TopCat.Sheaf`, which is not type-correct at `implicit`
transparency where sheaves on the topology of its opens are expected, so a `rw` whose motive
mentions it fails outright.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- The transport at an associated module, read on `hom` as the composite of its two factors.
Obtained from the equation of isomorphisms, which is where it is cheap. -/
theorem representedAssociatedModulePullbackIso_hom
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    (representedAssociatedModulePullbackIso B S hS g hg 𝓕).hom =
      (representedModuleObjPullbackIso B S hS g hg
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj 𝓕)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
            (associatedBigEtaleSite B) g.left 𝓕).inv :=
  congrArg Iso.hom (representedAssociatedModulePullbackIso_eq B S hS g hg 𝓕)

/-- **[Stacks Project, Tag 03LC] (1) at the unit module, with the base-change comparison moved
to the other side.**  Pulling the canonical map `𝒪^a ⟶ 𝒪` of the small étale site of the target
back along the morphism of small étale ringed sites, and then applying the canonical map of that
morphism, is the inverse base-change comparison followed by the associated module of the Zariski
canonical map and the canonical map of the source's own small étale site. -/
theorem pullback_pullbackObjUnitToUnit_comp :
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).map
          (SheafOfModules.pullbackObjUnitToUnit
            (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property)) ≫
        SheafOfModules.pullbackObjUnitToUnit (representedSchemeStructureMapRing B S hS g) =
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
            (associatedBigEtaleSite B) g.left
            (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)).inv ≫
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
              (SheafOfModules.pullbackObjUnitToUnit
                (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
                  g.left).toRingCatSheafHom) ≫
            SheafOfModules.pullbackObjUnitToUnit
              (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)) :=
  (Iso.eq_inv_comp _).mpr
    (_root_.AlgebraicGeometry.SmallEtale.pullbackObjUnitToUnit_associatedModuleBaseChangeIso
      (associatedBigEtaleSite B) g.left).symm

/-- The naturality of the object form at the canonical map of [Stacks Project, Tag 03DU] (4),
with the source module spelled through the **associated-module functor** rather than through
pullback along the structure comparison.

The two spellings differ by a single delta, and this restatement is the only place that delta is
crossed; it has to be crossed somewhere, and inside the assembly below it is a `whnf`
timeout. -/
theorem representedModuleObjPullbackIso_naturality_associatedModule :
    (modulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedSmallEtaleModuleEquivalence B S hS T).functor.map
            (SheafOfModules.pullbackObjUnitToUnit
              (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T) T.left.property))) ≫
        (representedModuleObjPullbackIso B S hS g hg
          (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T))).hom =
      (representedModuleObjPullbackIso B S hS g hg
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj
              (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf))).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).map
            (SheafOfModules.pullbackObjUnitToUnit
              (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T) T.left.property))) :=
  @representedModuleObjPullbackIso_naturality B S hS T' T g hg
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj
      (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf))
    (SheafOfModules.unit (representedSchemeStructureSheaf B S hS T))
    (SheafOfModules.pullbackObjUnitToUnit
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property))

/-- **The transport of the inverse image at an associated module carries the canonical map
`φ^*𝒪 ⟶ 𝒪` of the represented morphism to the associated module of the Zariski canonical map
`r^*𝒪 ⟶ 𝒪` of the underlying morphism of schemes.**

Both sides are read at the Zariski structure sheaf, so on the left the canonical map of
[Stacks Project, Tag 03DU] (4) comparing its associated module with the structure sheaf of the
small étale site appears, pulled back along `φ`; on the right the same map appears for the
source, after the associated module of the Zariski canonical map.

The proof is the two unit-module compatibilities of the two factors joined by the naturality in
the module of the first — see the module documentation. -/
theorem structureModulePullbackMap_representedAssociatedModulePullbackIso :
    (modulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedSmallEtaleModuleEquivalence B S hS T).functor.map
            (SheafOfModules.pullbackObjUnitToUnit
              (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T) T.left.property))) ≫
        structureModulePullbackMap B S hS (representedSpaceMap B S hS g) =
      (representedAssociatedModulePullbackIso B S hS g hg
            (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
                (SheafOfModules.pullbackObjUnitToUnit
                  (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
                    g.left).toRingCatSheafHom) ≫
              SheafOfModules.pullbackObjUnitToUnit
                (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
                  ((BigFppfOver.toScheme B S hS).obj T') T'.left.property)) :=
  Stacks.CategoryTheory.comp_eq_comp_of_glue
    (structureModulePullbackMap_representedModuleObjPullbackIso B S hS g hg)
    (representedModuleObjPullbackIso_naturality_associatedModule B S hS g hg)
    (Stacks.CategoryTheory.map_square
      (representedSmallEtaleModuleEquivalence B S hS T').functor
      (pullback_pullbackObjUnitToUnit_comp B S hS g))
    (representedAssociatedModulePullbackIso_hom B S hS g hg
      (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf))

end AlgebraicGeometry.Space

end
