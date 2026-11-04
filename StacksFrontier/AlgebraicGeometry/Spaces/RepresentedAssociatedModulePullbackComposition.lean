module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModulePullbackNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModulePullbackUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChangeComposition
public import StacksFrontier.CategoryTheory.FactoredTransportComposition

/-!
# The transport of the inverse image at an associated module, and composition

`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` carries the inverse image of
`𝒪`-modules of [Stacks Project, Tag 03LU] along a represented morphism of algebraic spaces, read
at the associated module of a Zariski module, onto the associated module of the Zariski pullback.
This file reduces the compatibility of that transport with **composition** of represented
morphisms — its compatibility with `AlgebraicGeometry.Space.modulePullbackCompIso` on the one
side and with `AlgebraicGeometry.Scheme.Modules.pullbackComp` on the other — to the same
compatibility for the transport before the associated module is taken,
`AlgebraicGeometry.Space.representedModuleObjPullbackIso`.

The two transports differ by the base-change comparison of [Stacks Project, Tag 03LC] (1), whose
composition law carries `AlgebraicGeometry.Scheme.Modules.pullbackComp` to the composition law
`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` of the pullbacks along the morphisms of
small étale ringed sites of [Stacks Project, Tag 070R] (2).

No `stacks` tag is registered. This is a step of part (2) of [Stacks Project, Tag 04G2], not an
assertion of 03LU, 03LC or 03DU.

## Main results

All names are in the namespace `AlgebraicGeometry.Space`.

* `associatedModuleObjBaseChangeIso_inv_comp`: the composition law of part (1) of [Stacks Project,
  Tag 03LC], solved for the inverse comparisons.
* `representedAssociatedModulePullbackIso_comp_of_objComp`: the composition law for the transport
  at an associated module follows from the composition law for `representedModuleObjPullbackIso`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local irreducible] representedModuleObjPullbackIso modulePullback
  _root_.AlgebraicGeometry.SmallEtale.associatedModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Factor

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hg : yoneda.relativelyRepresentable (yoneda.map g))


end Factor

section Composition

variable {T₁ T₂ T₃ : BigFppfOver B S hS} (p : T₁ ⟶ T₂) (q : T₂ ⟶ T₃)
    (hp : yoneda.relativelyRepresentable (yoneda.map p))
    (hq : yoneda.relativelyRepresentable (yoneda.map q))
    (hpq : yoneda.relativelyRepresentable (yoneda.map (p ≫ q)))

/-- **The composition law of [Stacks Project, Tag 03LC] (1), solved for the inverse
comparisons.**  Pulling the comparison below `q` back along `ε_p`, following it by the inverse of
the comparison below `p` and then by the associated module of the Zariski composition law, is the
composition law `AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` of the pullbacks along
the morphisms of small étale ringed sites followed by the inverse of the comparison below the
composite. -/
theorem associatedModuleObjBaseChangeIso_inv_comp
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T₃).Modules) :
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS p)).map
          (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
            (associatedBigEtaleSite B) q.left 𝓕).inv ≫
        (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
            (associatedBigEtaleSite B) p.left
            ((Scheme.Modules.pullback (B.inclusion.map q.left)).obj 𝓕)).inv ≫
          (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T₁) T₁.left.property).map
            ((Scheme.Modules.pullbackComp (B.inclusion.map p.left)
              (B.inclusion.map q.left)).hom.app 𝓕) =
      (_root_.AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso
            (associatedBigEtaleSite B) p.left q.left).hom.app
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T₃) T₃.left.property).obj 𝓕) ≫
        (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
          (associatedBigEtaleSite B) (p ≫ q).left 𝓕).inv :=
  Stacks.CategoryTheory.inv_comp_inv_comp_eq_of_comp_eq
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
      (associatedBigEtaleSite B) p.left
      ((Scheme.Modules.pullback (B.inclusion.map q.left)).obj 𝓕))
    ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS p)).mapIso
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
        (associatedBigEtaleSite B) q.left 𝓕))
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
      (associatedBigEtaleSite B) (p ≫ q).left 𝓕)
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_comp
      (associatedBigEtaleSite B) p.left q.left 𝓕)

/-- **The composition law for the transport at an associated module, from the composition law for
the transport itself.**

Assume that the transport `AlgebraicGeometry.Space.representedModuleObjPullbackIso` of the
inverse image along a represented morphism carries the composition comparison
`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` of pullbacks along the morphisms of
small étale ringed sites of [Stacks Project, Tag 070R] (2) to the composition comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of [Stacks Project, Tag 03LU], at the associated
module of `𝓕`.  Then `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` carries
`AlgebraicGeometry.Scheme.Modules.pullbackComp` to that same composition comparison. -/
theorem representedAssociatedModulePullbackIso_comp_of_objComp
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T₃).Modules)
    (hobj :
      (modulePullback B S hS (representedSpaceMap B S hS p)).map
            (representedModuleObjPullbackIso B S hS q hq
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T₃) T₃.left.property).obj 𝓕)).hom ≫
          (representedModuleObjPullbackIso B S hS p hp
            ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS q)).obj
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T₃) T₃.left.property).obj 𝓕))).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS T₁).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso
                (associatedBigEtaleSite B) p.left q.left).hom.app
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T₃) T₃.left.property).obj 𝓕)) =
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS p)
              (representedSpaceMap B S hS q)).hom.app
            ((representedSmallEtaleModuleEquivalence B S hS T₃).functor.obj
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T₃) T₃.left.property).obj 𝓕)) ≫
          (representedModuleObjPullbackIso B S hS (p ≫ q) hpq
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T₃) T₃.left.property).obj 𝓕)).hom) :
    (modulePullback B S hS (representedSpaceMap B S hS p)).map
          (representedAssociatedModulePullbackIso B S hS q hq 𝓕).hom ≫
        (representedAssociatedModulePullbackIso B S hS p hp
          ((Scheme.Modules.pullback (B.inclusion.map q.left)).obj 𝓕)).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS T₁).functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T₁) T₁.left.property).map
            ((Scheme.Modules.pullbackComp (B.inclusion.map p.left)
              (B.inclusion.map q.left)).hom.app 𝓕)) =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS p)
            (representedSpaceMap B S hS q)).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS T₃).functor.obj
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T₃) T₃.left.property).obj 𝓕)) ≫
        (representedAssociatedModulePullbackIso B S hS (p ≫ q) hpq 𝓕).hom :=
  Stacks.CategoryTheory.comp_transport_of_factored
    (modulePullback B S hS (representedSpaceMap B S hS p))
    (representedSmallEtaleModuleEquivalence B S hS T₁).functor
    (representedAssociatedModulePullbackIso_hom B S hS q hq 𝓕)
    (representedAssociatedModulePullbackIso_hom B S hS p hp _)
    (representedModuleObjPullbackIso_naturality B S hS p hp
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
        (associatedBigEtaleSite B) q.left 𝓕).inv)
    (associatedModuleObjBaseChangeIso_inv_comp B S hS p q 𝓕)
    (representedAssociatedModulePullbackIso_hom B S hS (p ≫ q) hpq 𝓕) hobj

end Composition

end AlgebraicGeometry.Space

end
