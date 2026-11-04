module

public import StacksFrontier.CategoryTheory.Adjunction.MateTransportCocycle
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModulePullbackComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePushforwardSquareCompositionLaw

/-!
# The transport of the inverse image along a represented morphism is compatible with composition

For a morphism `g : T' ⟶ T` of the big fppf category over `S` whose represented morphism of
algebraic spaces is representable,
`AlgebraicGeometry.Space.representedModuleObjPullbackIso` identifies the inverse image of
`𝒪`-modules of [Stacks Project, Tag 03LU] along the represented morphism, read at the `𝒪`-module
which a sheaf of modules on the small étale site of the underlying scheme becomes, with the
`𝒪`-module of the pullback of that sheaf along the morphism of small étale ringed sites of
[Stacks Project, Tag 070R] (2).  This file proves that **those identifications are compatible
with composition**: the composition comparison
`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` on the schemes side is carried to the
composition comparison `AlgebraicGeometry.Space.modulePullbackCompIso` of [Stacks Project,
Tag 03LU] on the spaces side.

That is the statement the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleImmersionFunctorial.lean` record as the
residue of part (2) of [Stacks Project, Tag 04G2], and the one that
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_of_objComp` takes as its
hypothesis `hobj`.  The corresponding statement for the transport at an associated module follows
at once, and is proved here too.

## Main results

* `AlgebraicGeometry.Space.conjugateEquiv_smallEtalePullbackCompIso_representedScheme`: the
  conjugate of the schemes-side composition comparison of pullbacks is the composition comparison
  of direct images in the factored form that the composition law of the square uses.
* `AlgebraicGeometry.Space.representedModuleObjPullbackIso_comp`: **the composition law for the
  transport.**
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp`: **the composition law
  for the transport at an associated module**, which is what part (2) of [Stacks Project,
  Tag 04G2] consumes.

## Implementation notes

The whole proof is one application of
`Stacks.CategoryTheory.transportedComparison_cocycle`, the generic cocycle for a system of
comparisons of left adjoints conjugated by equivalences, and **no argument of that application is
a restatement**: the comparison of the two routes round the square of direct images is
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, its composition law is
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso_factoredComp` read at an
object by the generic `Stacks.CategoryTheory.cocycle_app_of_iso`, and the two identifications of
the composition comparisons of the left adjoints as conjugates are
`AlgebraicGeometry.Space.conjugateEquiv_modulePullbackCompIso_hom` and the one statement this
file has to supply.

That one statement is the schemes-side half.
`AlgebraicGeometry.SmallEtale.conjugateEquiv_smallEtalePullbackCompIso_inv` computes the
conjugate of the *inverse* of the composition comparison of pullbacks, and an isomorphism is
determined by its inverse, so `CategoryTheory.Iso.inv_eq_inv` turns that into the forward
statement; the two composites then agree because
`AlgebraicGeometry.Space.representedSchemeModulePushforwardFactoredCompIso` is by construction
`AlgebraicGeometry.SmallEtale.smallEtalePushforwardCompIso` followed by the inverse of
`CategoryTheory.SheafOfModules.pushforwardComp`, and
`AlgebraicGeometry.Space.representedSchemeBaseChange_factoredCompIso` is a reducible
abbreviation for the comparison of base changes of étale scheme charts that the former is built
from.

The composite is presented as the literal `p ≫ q` with the factorisation `rfl`, at which
`AlgebraicGeometry.Space.modulePushforwardFactoredCompIso_rfl` makes the factored composition
comparison of direct images the unfactored one, so the conjugate statement applies with no
conversion.

## What remains between this law and part (2) of [Stacks Project, Tag 04G2]

The note of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleRepresentedNaturality.lean` headed *What the
naturality assumes, and what that assumption is* says that the reduction of its hypothesis `hΞ`
has for its own residue a statement about
`AlgebraicGeometry.Space.representedModuleObjPullbackIso`.  That residue is what this file
proves, so that half of the note is now discharged; **what the note does not say is that `hΞ` is
the law for a commutative *square* rather than for a composite**, and three further steps carry
the one to the other.  They are listed here, with the reduction worked out, because none of them
is done:

* the square comparison `AlgebraicGeometry.Space.squarePullbackCompIso` is by construction two
  instances of `AlgebraicGeometry.Space.modulePullbackCompIso` with an `eqToIso` of the square
  between them, and `Stacks.ClosedImmersion.pullbackCompIso` is two instances of
  `RingedSpaceModuleAdjunction.modulePullbackComp` with a
  `RingedSpaceModuleAdjunction.modulePullbackCongr` between them, so `hΞ` follows from this file's
  law applied to the two composites `b ≫ j'` and `j ≫ a` once the three residual factors are
  matched;
* the first residual factor is the transport of the law's right-hand side along the square: the
  inverse of the transport at `b ≫ j'`, the component of that `eqToIso`, and the transport at
  `j ≫ a`.  It is an identity obtainable by `subst` on the square at plain variables, before any
  geometric term appears;
* the second is the identification of `Stacks.ClosedImmersion.pullbackCompIso` with the two
  instances of `AlgebraicGeometry.Scheme.Modules.pullbackComp` that this file's law produces,
  together with the schemes-level transport along the square.  The composition comparison
  `modulePullbackCompUniq`, a comparison *of left adjoints by uniqueness*, is not known to agree
  with these, but that question does **not** arise for this pair: `RingedSpaceModuleAdjunction.modulePullbackComp` is
  `CategoryTheory.SheafOfModules.pullbackComp` of the two structure-sheaf maps (read backwards)
  and `AlgebraicGeometry.Scheme.Modules.pullbackComp` is `CategoryTheory.SheafOfModules.
  pullbackComp` as well, so the two are the same Mathlib construction at two presentations of the
  same morphisms.  **This is read off the two definitions**, and the cost of the
  identification at the geometric instantiation is unknown.

Beyond `hΞ`, part (2) is stated by the source for an **immersion**, while
`AlgebraicGeometry.Space.conormalSheafMap_representedConormalKernelIdealZPowIso` is for a square
of *closed* immersions of schemes of the site; so the tag's registration needs the immersion
generality as well, and is not claimed anywhere by this file.

No `stacks` tag is registered.  This is a step of part (2) of [Stacks Project, Tag 04G2], not an
assertion of 03LU, 070R or 04G2 itself.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T₁ T₂ T₃ : BigFppfOver B S hS} (p : T₁ ⟶ T₂) (q : T₂ ⟶ T₃)

/-- **The conjugate of the schemes-side composition comparison of pullbacks of sheaves of
modules is the composition comparison of the direct images**, in the factored form in which the
composition law of the square of small étale ringed sites of a representable morphism states it.

`AlgebraicGeometry.SmallEtale.conjugateEquiv_smallEtalePullbackCompIso_inv` is this statement for
the inverse of the composition comparison, and an isomorphism is determined by its inverse. -/
theorem conjugateEquiv_smallEtalePullbackCompIso_representedScheme :
    conjugateEquiv
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (representedSchemeStructureMapRing B S hS (p ≫ q)))
        ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (representedSchemeStructureMapRing B S hS q)).comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (representedSchemeStructureMapRing B S hS p)))
        (_root_.AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso
          (associatedBigEtaleSite B) p.left q.left).hom =
      (representedSchemeModulePushforwardFactoredCompIso B S hS p q (p ≫ q) rfl).hom := by
  refine (Iso.inv_eq_inv
    (conjugateIsoEquiv
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (representedSchemeStructureMapRing B S hS (p ≫ q)))
      ((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (representedSchemeStructureMapRing B S hS q)).comp
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (representedSchemeStructureMapRing B S hS p)))
      (_root_.AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso
        (associatedBigEtaleSite B) p.left q.left))
    (representedSchemeModulePushforwardFactoredCompIso B S hS p q (p ≫ q) rfl)).mp ?_
  have key := _root_.AlgebraicGeometry.SmallEtale.conjugateEquiv_smallEtalePullbackCompIso_inv
    (associatedBigEtaleSite B) p.left q.left
  exact key.trans rfl

/-- `AlgebraicGeometry.Space.conjugateEquiv_modulePullbackCompIso_hom` for the represented
morphisms, with the composite spelled as the morphism represented by `p ≫ q` and the composition
comparison of direct images in its factored form.

The same statement: the two spellings of the composite morphism of algebraic spaces are
definitionally equal, and at the factorisation `rfl` the factored comparison is the unfactored
one.  It is restated here so that the composition law below meets only one spelling, and so that
the conversion between the two is paid once, in a declaration of its own. -/
theorem conjugateEquiv_modulePullbackCompIso_representedSpaceMap :
    conjugateEquiv (modulePullbackAdjunction B S hS (representedSpaceMap B S hS (p ≫ q)))
        ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS q)).comp
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS p)))
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS p)
          (representedSpaceMap B S hS q)).hom =
      (modulePushforwardFactoredCompIso B S hS (representedSpaceMap B S hS p)
        (representedSpaceMap B S hS q) (representedSpaceMap B S hS (p ≫ q))
        (representedSpaceMap_comp_eq B S hS p q (p ≫ q) rfl)).inv :=
  conjugateEquiv_modulePullbackCompIso_hom (representedSpaceMap B S hS p)
    (representedSpaceMap B S hS q)

section Law

-- Without these, both the identification below and the single application of the
-- generic cocycle are deterministic 200 000-heartbeat `whnf` timeouts.  None of them has to be
-- unfolded here: the transport is read through its own definition, and all of these enter only
-- symbolically.
attribute [local irreducible] modulePullback modulePullbackCompIso modulePushforward
  modulePushforwardCompIso modulePushforwardFactoredCompIso representedSmallEtaleEquivalence
  smallBaseChange structureSheaf structureSheaf' structurePresheaf
  representedModulePushforwardSquareIso

/-- **The transport of the inverse image along a represented morphism is the comparison of the
two left adjoints of the direct image round the square, corrected by the two identifications of
the small étale sites** — that is, it is
`Stacks.CategoryTheory.transportedComparisonApp` of the comparison
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso` of the two direct images.

This holds by construction; it is recorded as a declaration of its own so that the composition
law below is an application of the generic cocycle with no unfolding of the transport inside its
elaboration. -/
theorem transportedComparisonApp_representedModulePushforwardSquareIso {T' T : BigFppfOver B S hS}
    (g : T' ⟶ T) (hg : yoneda.relativelyRepresentable (yoneda.map g))
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T)) :
    Stacks.CategoryTheory.transportedComparisonApp
        (representedSmallEtaleModuleEquivalence B S hS T)
        (representedSmallEtaleModuleEquivalence B S hS T')
        (modulePullbackAdjunction B S hS (representedSpaceMap B S hS g))
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (representedSchemeStructureMapRing B S hS g))
        (representedModulePushforwardSquareIso B S hS g hg) M =
      (representedModuleObjPullbackIso B S hS g hg M).hom :=
  rfl

variable (hp : yoneda.relativelyRepresentable (yoneda.map p))
  (hq : yoneda.relativelyRepresentable (yoneda.map q))
  (hpq : yoneda.relativelyRepresentable (yoneda.map (p ≫ q)))

include hp hq hpq in
/-- **The transport of the inverse image along a represented morphism is compatible with
composition.**  Pulling a sheaf of modules on the small étale site of the scheme underlying `T₃`
back along the morphism of small étale ringed sites of `q` and then along that of `p`, and
reading the result on the small étale site of `yoneda.obj T₁`, is reading it there along the
composite: the transport carries the composition comparison
`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` to the composition comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of [Stacks Project, Tag 03LU].

The transport is the comparison of the two left adjoints of the direct image round the square,
conjugated by the identifications of the small étale sites; so it is the mate of
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`, and mates compose. -/
theorem representedModuleObjPullbackIso_comp
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS T₃)) :
    (modulePullback B S hS (representedSpaceMap B S hS p)).map
          (representedModuleObjPullbackIso B S hS q hq M).hom ≫
        (representedModuleObjPullbackIso B S hS p hp
            ((SheafOfModules.pullback.{u}
              (representedSchemeStructureMapRing B S hS q)).obj M)).hom ≫
          (representedSmallEtaleModuleEquivalence B S hS T₁).functor.map
            ((_root_.AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso
              (associatedBigEtaleSite B) p.left q.left).hom.app M) =
      (modulePullbackCompIso B S hS (representedSpaceMap B S hS p)
            (representedSpaceMap B S hS q)).hom.app
          ((representedSmallEtaleModuleEquivalence B S hS T₃).functor.obj M) ≫
        (representedModuleObjPullbackIso B S hS (p ≫ q) hpq M).hom := by
  rw [← transportedComparisonApp_representedModulePushforwardSquareIso B S hS q hq M,
    ← transportedComparisonApp_representedModulePushforwardSquareIso B S hS p hp
      ((SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS q)).obj M),
    ← transportedComparisonApp_representedModulePushforwardSquareIso B S hS (p ≫ q) hpq M]
  exact Stacks.CategoryTheory.transportedComparison_cocycle
    (representedSmallEtaleModuleEquivalence B S hS T₁)
    (representedSmallEtaleModuleEquivalence B S hS T₂)
    (representedSmallEtaleModuleEquivalence B S hS T₃)
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS p))
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS q))
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS (p ≫ q)))
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS p))
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS q))
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS (p ≫ q)))
    (representedModulePushforwardSquareIso B S hS p hp)
    (representedModulePushforwardSquareIso B S hS q hq)
    (representedModulePushforwardSquareIso B S hS (p ≫ q) hpq)
    (modulePushforwardFactoredCompIso B S hS (representedSpaceMap B S hS p)
      (representedSpaceMap B S hS q) (representedSpaceMap B S hS (p ≫ q))
      (representedSpaceMap_comp_eq B S hS p q (p ≫ q) rfl))
    (representedSchemeModulePushforwardFactoredCompIso B S hS p q (p ≫ q) rfl)
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS p)
      (representedSpaceMap B S hS q))
    (_root_.AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso
      (associatedBigEtaleSite B) p.left q.left)
    (conjugateEquiv_modulePullbackCompIso_representedSpaceMap B S hS p q)
    (conjugateEquiv_smallEtalePullbackCompIso_representedScheme B S hS p q)
    (fun Z ↦ Stacks.CategoryTheory.cocycle_app_of_iso
      (representedModulePushforwardSquareIso_factoredComp B S hS p q (p ≫ q) rfl hp hq hpq) Z) M

include hp hq hpq in
/-- **The composition law for the transport of the inverse image at an associated module.**

This is `AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_comp_of_objComp` with its
hypothesis discharged by `AlgebraicGeometry.Space.representedModuleObjPullbackIso_comp`. -/
theorem representedAssociatedModulePullbackIso_comp
    (𝓕 : ((BigFppfOver.toScheme B S hS).obj T₃).Modules) :
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
  representedAssociatedModulePullbackIso_comp_of_objComp B S hS p q hp hq hpq 𝓕
    (representedModuleObjPullbackIso_comp B S hS p q hp hq hpq _)

end Law

end AlgebraicGeometry.Space

end
