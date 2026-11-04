module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.CategoryTheory.CommutingSquares
public import StacksFrontier.CategoryTheory.Equivalence.ConjugateObjIsoNaturality

/-!
# Naturality in the module of the transport of the inverse image along a represented morphism

`AlgebraicGeometry.Space.representedModuleObjPullbackIso` carries the inverse image of
`𝒪`-modules along a represented morphism of algebraic spaces to pullback of sheaves of modules
along the morphism of small étale ringed sites of [Stacks Project, Tag 070R] (2) of the
underlying morphism of schemes, at one module; and
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` does the same for the
associated module of a Zariski module, landing on the Zariski pullback.

Both are built objectwise: the functor-level comparison they rest on,
`AlgebraicGeometry.Space.representedModulePullbackIso`, compares the inverse image followed by
the *quasi-inverse* of the comparison equivalence with the quasi-inverse followed by pullback,
and the object form is that comparison read at the image of the module under the equivalence and
corrected by the unit and the counit. So nothing about either is natural in the module by
construction.

The naturality is formal, and is proved generically in
`StacksFrontier.CategoryTheory.Equivalence.ConjugateObjIsoNaturality`: a family of isomorphisms
given by that formula is natural, the three steps being the naturality of the comparison, of the
unit and of the counit. Here that generic statement is instantiated, the formula being
discharged by `rfl` as an equation of isomorphisms, and then composed with the naturality of
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`, which is a comparison of functors
and whose naturality is therefore its own.

## Main results

* `AlgebraicGeometry.Space.representedModuleObjPullbackIso_naturality`: **the object form of the
  transport of the inverse image is natural in the module.**
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_naturality`: **the transport
  at an associated module is natural in the Zariski module.**

## Implementation notes

The generic lemma takes the family of isomorphisms and the formula for it as hypotheses rather
than naming a conjugate, so that the instantiation supplies the formula by `rfl` at the level of
isomorphisms. The same equation between the `hom` components of the two sides is measurably
more expensive here, projecting `hom` out of a three-fold composite driving the elaborator into
the construction of the inverse image.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- **The object form of the transport of the inverse image along a represented morphism is
natural in the module.**

This is `Stacks.Equivalence.conjugateObjIso_naturality` at the two comparison equivalences of
the small étale sites, the inverse image along the represented morphism and pullback along the
morphism of small étale ringed sites of the underlying morphism of schemes, with the formula
discharged by `rfl`. -/
theorem representedModuleObjPullbackIso_naturality
    {M N : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T)} (ψ : M ⟶ N) :
    (modulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedSmallEtaleModuleEquivalence B S hS T).functor.map ψ) ≫
        (representedModuleObjPullbackIso B S hS g hg N).hom =
      (representedModuleObjPullbackIso B S hS g hg M).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).map ψ) :=
  Stacks.Equivalence.conjugateObjIso_naturality
    (representedSmallEtaleModuleEquivalence B S hS T)
    (representedSmallEtaleModuleEquivalence B S hS T')
    (modulePullback B S hS (representedSpaceMap B S hS g))
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g))
    (representedModulePullbackIso B S hS g hg)
    (representedModuleObjPullbackIso B S hS g hg) (fun _ ↦ rfl) ψ

/-- The base-change comparison of [Stacks Project, Tag 03LC] (1) is natural in the module, read
backwards: it is a comparison of *functors*, so this is the naturality of its inverse. -/
theorem associatedModuleBaseChangeIso_inv_naturality
    {𝓕 𝓖 : ((BigFppfOver.toScheme B S hS).obj T).Modules} (ψ : 𝓕 ⟶ 𝓖) :
    (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map ψ) ≫
        (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
          (associatedBigEtaleSite B) g.left 𝓖).inv =
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
            (associatedBigEtaleSite B) g.left 𝓕).inv ≫
        (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
          ((Scheme.Modules.pullback (B.inclusion.map g.left)).map ψ) :=
  (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
    (associatedBigEtaleSite B) g.left).inv.naturality ψ

/-- The transport at an associated module, as the composite of its two factors.

The equation is at the level of *isomorphisms*, which is the only level at which it is cheap:
the same equation between the `hom` components exhausts the `whnf` budget, projecting `hom` out
of the composite driving the elaborator into the construction of the inverse image. -/
theorem representedAssociatedModulePullbackIso_eq
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T).Modules) :
    representedAssociatedModulePullbackIso B S hS g hg 𝓕 =
      representedModuleObjPullbackIso B S hS g hg
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj 𝓕) ≪≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.mapIso
          (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
            (associatedBigEtaleSite B) g.left 𝓕).symm :=
  rfl

/-- The base-change comparison's naturality, read under the functor of the comparison
equivalence and at the spelling the second factor of the transport is built at. -/
theorem functor_mapIso_associatedModuleObjBaseChangeIso_symm_naturality
    {𝓕 𝓖 : ((BigFppfOver.toScheme B S hS).obj T).Modules} (ψ : 𝓕 ⟶ 𝓖) :
    (representedSmallEtaleModuleEquivalence B S hS T').functor.map
            ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS g)).map
              ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map ψ)) ≫
          ((representedSmallEtaleModuleEquivalence B S hS T').functor.mapIso
            (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
              (associatedBigEtaleSite B) g.left 𝓖).symm).hom =
        ((representedSmallEtaleModuleEquivalence B S hS T').functor.mapIso
              (_root_.AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso
                (associatedBigEtaleSite B) g.left 𝓕).symm).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS T').functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
                ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
              ((Scheme.Modules.pullback (B.inclusion.map g.left)).map ψ)) := by
  simp only [Functor.mapIso_hom, Iso.symm_hom]
  rw [← Functor.map_comp, ← Functor.map_comp, associatedModuleBaseChangeIso_inv_naturality]

/-- **The transport of the inverse image at an associated module is natural in the Zariski
module.**

`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` is the object form of the
transport read at the associated module, followed by the base-change comparison of
[Stacks Project, Tag 03LC] (1); its naturality is the naturality of the first at the associated
module of the given map glued to that of the second at the map itself. -/
theorem representedAssociatedModulePullbackIso_naturality
    {𝓕 𝓖 : ((BigFppfOver.toScheme B S hS).obj T).Modules} (ψ : 𝓕 ⟶ 𝓖) :
    (modulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedSmallEtaleModuleEquivalence B S hS T).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map ψ)) ≫
        (representedAssociatedModulePullbackIso B S hS g hg 𝓖).hom =
      (representedAssociatedModulePullbackIso B S hS g hg 𝓕).hom ≫
        (representedSmallEtaleModuleEquivalence B S hS T').functor.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
            ((Scheme.Modules.pullback (B.inclusion.map g.left)).map ψ)) :=
  Stacks.Equivalence.trans_naturality
    (representedAssociatedModulePullbackIso_eq B S hS g hg 𝓕)
    (representedAssociatedModulePullbackIso_eq B S hS g hg 𝓖)
    (representedModuleObjPullbackIso_naturality B S hS g hg
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map ψ))
    (functor_mapIso_associatedModuleObjBaseChangeIso_symm_naturality B S hS g ψ)

end AlgebraicGeometry.Space

end
