module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlueDatumClosure

/-!
# Stacks 03DV, functorial in the object, and composition in the big fppf site

`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` is the comparison that
Stacks 03DV leaves implicit, in the spelling its consumers use: for `T` an object of the big
fppf category over `S` with structure morphism `f : X ⟶ S`,

    `(f^*𝓕)^a ≅ (𝓕^a)|_{(Sch/X)_fppf}`,

naturally in the `𝒪_S`-module `𝓕`.  Nothing so far said how that family of isomorphisms behaves
under *composition* in the big fppf site, and that is one of the two halves of the residue of
`CategoryTheory.Pseudofunctor.DescentData.pullHom_hom` recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ComparisonCoherence.lean`.  The other
half is `AlgebraicGeometry.BigFppfOver.objRestrictComp_cocycle`, proved unconditionally in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/GlueDatumClosure.lean`.

This file states that first half and reduces it to the opposite side of an adjunction.  The
comparison is built entirely out of isomorphisms that `CategoryTheory.Adjunction.leftAdjointUniq`
and `CategoryTheory.Adjunction.leftAdjointCompIso` produce, so it cannot be computed by
unfolding; the one handle on such an isomorphism is that it is determined by its mate.  Both
functors it compares are left adjoints: the source is a composite of two pullbacks, and the
target is the associated-module functor followed by restriction to an object, which is a left
adjoint by `AlgebraicGeometry.BigFppfOver.objRestrictAdjunction` — restriction to the big fppf
site of the scheme of `T` is restriction to the localization at `T`, a left adjoint by
`SheafOfModules.overPushforwardOverAdj`, followed by the reindexing along the equivalence of
Stacks 06WI, which is an equivalence.  So the comparison is determined by its mate, and the
coherence of Stacks 03DV with composition of objects is equivalent to the corresponding identity
between mates, which is an identity between isomorphisms of *pushforwards*.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.objRestrictAdjunction` and
  `AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction`: **restriction to the big
  fppf site of the scheme of `T` is a left adjoint**, in two ways — the right adjoint is the
  pushforward along `SheafOfModules.pushforwardOver` of `T` preceded by the inverse of the
  reindexing equivalence of Stacks 06WI, and it is `SheafOfModules.overPullback` along the
  structure morphism of `T`.

## Main results

* `AlgebraicGeometry.BigFppfOver.objHom_comp`: the structure morphism of `T'` factors through
  the structure morphism of `T` for `g : T' ⟶ T`, as the equality of morphisms of schemes that
  pins the composite the coherence is about.
* `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_ext`: **a comparison of the
  shape of Stacks 03DV is determined by its mate**, both of the functors it compares being left
  adjoints.  This is the only handle there is on `associatedModuleObjRestrictNatIso`, which no
  amount of unfolding computes.
* `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_comp_of_conjugate`: **the
  comparison of Stacks 03DV is compatible with composition of objects of the big fppf site**,
  granted the corresponding identity between the mates.  Restricting an `𝒪_S`-module to the
  scheme of `T` and then to the scheme of `T'` over it, comparing in two steps and contracting by
  `AlgebraicGeometry.BigFppfOver.objRestrictComp`, is comparing in one step at `T'`.

## Implementation notes

Nothing here carries a `stacks` attribute: the comparison this file is about is a step
Stacks 03DV leaves implicit and carries no tag of its own.

`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_comp_of_conjugate` is stated
with its hypothesis on the side of the right adjoints *on purpose*, and the hypothesis is not yet
discharged.  The two sides of the conclusion are isomorphisms between left adjoints assembled
from `CategoryTheory.Adjunction.leftAdjointUniq`; the mate of such an isomorphism is a
composite of comparisons of pushforwards of sheaves of modules, and those are the identity on
sections — which is the form in which
`AlgebraicGeometry.BigFppfOver.objRestrictComp_cocycle`, the other half of the residue, was
proved.  What is missing is the computation of the mate of
`associatedModuleObjRestrictNatIso` itself: no such computation exists, because
`AlgebraicGeometry.BigFppfOver.associatedModuleObjIso` goes through
`SheafOfModules.pullbackSquareIso` and
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso` through
`CategoryTheory.Adjunction.leftAdjointUniq` of a reindexing equivalence, and the mate of neither
is recorded.  Supplying those two computations, together with
`CategoryTheory.conjugateEquiv_whiskerLeft`, `CategoryTheory.conjugateEquiv_whiskerRight`,
`CategoryTheory.conjugateEquiv_associator_hom` and
`SheafOfModules.conjugateEquiv_pullbackComp_inv` for the structural factors, is what would turn
the hypothesis into a theorem.  The mate of `AlgebraicGeometry.BigFppfOver.objRestrictComp` is
owed as well, and that one is best taken with respect to
`AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction`, where it is the comparison of
`SheafOfModules.overPullback`s induced by `CategoryTheory.Over.pullbackComp` — a statement at an
arbitrary site, which is why both statements here are parametrised by an arbitrary adjunction for
restriction to an object rather than by one of the two constructed above.

The composite of structure morphisms is pinned by `AlgebraicGeometry.BigFppfOver.objHom_comp`
rather than left as a composite, so that the source of the two-step route is literally the
source of the one-step comparison at `T'`; this is the same device by which the composites in
`AlgebraicGeometry.BigFppfOver.objRestrictComp_cocycle` are pinned by `CategoryTheory.Over.w`.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The composite of structure morphisms -/

/-- **The structure morphism of `T'` is the structure morphism of `T` precomposed with `g`.**
For `g : T' ⟶ T` a morphism of the big fppf category over `S`, the scheme of `T'` is an object
over the scheme `X` of `T` through `g`, and its structure morphism over `S` is that morphism
followed by `f : X ⟶ S`.  This is `AlgebraicGeometry.BigFppfOver.hom_hom_comp` read through
`AlgebraicGeometry.BigFppfOver.objHom`; it is the equality of morphisms of schemes that pins the
composite in the coherence of Stacks 03DV below. -/
public theorem objHom_comp {T T' : BigFppfOver B S hS} (g : T' ⟶ T) :
    objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left) ≫
        objHom B S hS T =
      objHom B S hS T' :=
  (hom_hom_comp B S hS g).symm

/-! ### Restriction to an object is a left adjoint -/

/-- **Restriction to the big fppf site of the scheme of `T` is a left adjoint.**  It is
restriction to the localization of the big fppf site of `S` at `T`, which is left adjoint to the
pushforward along `SheafOfModules.pushforwardOver` of `T` by
`SheafOfModules.overPushforwardOverAdj`, followed by the reindexing along the equivalence of
Stacks 06WI, which is one half of an equivalence of categories of sheaves of modules.

Restriction to an object is a *pushforward*, so this is not the adjunction it is built from:
it is the one on the other side, and it is what makes the comparison of Stacks 03DV an
isomorphism between two left adjoints, hence determined by its mate. -/
public noncomputable def objRestrictAdjunction (T : BigFppfOver B S hS) :
    objRestrict B S hS T ⊣
      (Stacks.SheafOfModules.reindexEquivalence
          (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
          (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse ⋙
        SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver T) :=
  (SheafOfModules.overPushforwardOverAdj.{u} (R := structureSheaf B S hS) T).comp
    (Stacks.SheafOfModules.reindexEquivalence
      (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
      (objEquiv B S hS T) ((structureSheaf B S hS).over T)).toAdjunction

/-- **Restriction to the big fppf site of the scheme of `T` is a left adjoint, the second
way.**  By `AlgebraicGeometry.BigFppfOver.objRestrict_eq_overMap` it *is* restriction along the
structure morphism of `T` in the big fppf category over `S`, and that category has pullbacks, so
`SheafOfModules.overMapPushforwardAdj` applies: the right adjoint is `SheafOfModules.overPullback`
along the same morphism.

This adjunction and `AlgebraicGeometry.BigFppfOver.objRestrictAdjunction` are adjunctions for one
and the same functor but are not the same adjunction, and mates are taken with respect to one of
them, so the two give different — equally valid — reductions.  This one is the useful one for
`AlgebraicGeometry.BigFppfOver.objRestrictComp`, whose mate with respect to it is a comparison of
`SheafOfModules.overPullback`s at an arbitrary site, where
`Stacks.SheafOfModules.overMapCompIso` is computable. -/
public noncomputable def objRestrictOverPullbackAdjunction (T : BigFppfOver B S hS) :
    objRestrict B S hS T ⊣ SheafOfModules.overPullback.{u} B.structureSheaf T.hom := by
  rw [objRestrict_eq_overMap]
  exact SheafOfModules.overMapPushforwardAdj.{u} B.structureSheaf T.hom

/-! ### The comparison of Stacks 03DV is determined by its mate -/

/-- **A comparison of the shape of Stacks 03DV is determined by its mate.**  Two isomorphisms

    `f^*(-)^a ≅ (-)^a|_{(Sch/X)_fppf}`

with the same source and target agree as soon as their mates do.  Both functors are left
adjoints — the source is a composite of two pullbacks, the target is the associated-module
functor followed by restriction to an object, which is a left adjoint by either of
`AlgebraicGeometry.BigFppfOver.objRestrictAdjunction` and
`AlgebraicGeometry.BigFppfOver.objRestrictOverPullbackAdjunction`, and the adjunction is taken as
an argument because the mate depends on which — and `CategoryTheory.conjugateIsoEquiv` is a
bijection between isomorphisms of left adjoints and isomorphisms of the corresponding right
adjoints.

This is the only handle on `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`
there is: that isomorphism is assembled from `CategoryTheory.Adjunction.leftAdjointUniq`, whose
value no unfolding computes, and whose mate is the identity by construction. -/
public theorem associatedModuleObjRestrictNatIso_ext {T : BigFppfOver B S hS}
    {G : SheafOfModules.{u}
        (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)) ⥤
      SheafOfModules.{u} (structureSheaf B S hS)} (adj : objRestrict B S hS T ⊣ G)
    {α β : Scheme.Modules.pullback (objHom B S hS T) ⋙
        associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T) ≅
      associatedModule B S hS ⋙ objRestrict B S hS T}
    (h : conjugateIsoEquiv ((associatedModuleAdjunction B S hS).comp adj)
          ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).comp
            (associatedModuleAdjunction B (objScheme B S hS T)
              (contains_objScheme B S hS T))) α =
        conjugateIsoEquiv ((associatedModuleAdjunction B S hS).comp adj)
          ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).comp
            (associatedModuleAdjunction B (objScheme B S hS T)
              (contains_objScheme B S hS T))) β) :
    α = β :=
  (conjugateIsoEquiv _ _).injective h

/-! ### Stacks 03DV and composition of objects -/

/-- **The comparison of Stacks 03DV is compatible with composition of objects of the big fppf
site**, granted the corresponding identity between the mates.

Let `g : T' ⟶ T` be a morphism of the big fppf category over `S`, let `f : X ⟶ S` be the
structure morphism of `T` and `g.left : X' ⟶ X` that of `T'` read over `X`.  An `𝒪_S`-module
`𝓕` can be compared with the restriction of `𝓕^a` to the big fppf site of `X'` in two ways: in
one step, by `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` at `T'`, or in
two, by that comparison at `T` and then at `Over.mk g.left`, the iterated pullback of modules on
schemes being contracted by `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.BigFppfOver.objHom_comp` on the one side and the iterated restriction by
`AlgebraicGeometry.BigFppfOver.objRestrictComp` on the other.  The two agree.

Together with `AlgebraicGeometry.BigFppfOver.objRestrictComp_cocycle` this is the residue of
`CategoryTheory.Pseudofunctor.DescentData.pullHom_hom` for the transition isomorphisms of
Stacks 03DX (1), described in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/ComparisonCoherence.lean`; granting it,
`AlgebraicGeometry.BigFppfOver.pullHom_transitionIso_of_comparison_comp` closes that field.

The hypothesis is the same identity read through
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_ext`, that is, on the side of
the right adjoints, where every factor is a comparison of pushforwards of sheaves of modules and
so is the identity on sections.  It is *not* discharged here; the implementation notes name
exactly the mates that are still to be computed. -/
public theorem associatedModuleObjRestrictNatIso_comp_of_conjugate
    {T T' : BigFppfOver B S hS} (g : T' ⟶ T)
    {G : SheafOfModules.{u}
        (structureSheaf B (objScheme B S hS T') (contains_objScheme B S hS T')) ⥤
      SheafOfModules.{u} (structureSheaf B S hS)} (adj : objRestrict B S hS T' ⊣ G)
    (h : conjugateIsoEquiv ((associatedModuleAdjunction B S hS).comp adj)
          ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T')).comp
            (associatedModuleAdjunction B (objScheme B S hS T')
              (contains_objScheme B S hS T')))
          ((Functor.isoWhiskerRight
                (Scheme.Modules.pullbackComp
                    (objHom B (objScheme B S hS T) (contains_objScheme B S hS T)
                      (Over.mk g.left))
                    (objHom B S hS T) ≪≫
                  Scheme.Modules.pullbackCongr (objHom_comp B S hS g))
                (associatedModule B (objScheme B S hS T')
                  (contains_objScheme B S hS T'))).symm ≪≫
            Functor.associator _ _ _ ≪≫
              Functor.isoWhiskerLeft _
                  (associatedModuleObjRestrictNatIso B (objScheme B S hS T)
                    (contains_objScheme B S hS T) (Over.mk g.left)) ≪≫
                (Functor.associator _ _ _).symm ≪≫
                  Functor.isoWhiskerRight (associatedModuleObjRestrictNatIso B S hS T) _ ≪≫
                    Functor.associator _ _ _ ≪≫
                      Functor.isoWhiskerLeft _ (objRestrictComp B S hS g)) =
        conjugateIsoEquiv ((associatedModuleAdjunction B S hS).comp adj)
          ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T')).comp
            (associatedModuleAdjunction B (objScheme B S hS T')
              (contains_objScheme B S hS T')))
          (associatedModuleObjRestrictNatIso B S hS T')) :
    (Functor.isoWhiskerRight
          (Scheme.Modules.pullbackComp
              (objHom B (objScheme B S hS T) (contains_objScheme B S hS T) (Over.mk g.left))
              (objHom B S hS T) ≪≫
            Scheme.Modules.pullbackCongr (objHom_comp B S hS g))
          (associatedModule B (objScheme B S hS T') (contains_objScheme B S hS T'))).symm ≪≫
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft _
              (associatedModuleObjRestrictNatIso B (objScheme B S hS T)
                (contains_objScheme B S hS T) (Over.mk g.left)) ≪≫
            (Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight (associatedModuleObjRestrictNatIso B S hS T) _ ≪≫
                Functor.associator _ _ _ ≪≫
                  Functor.isoWhiskerLeft _ (objRestrictComp B S hS g) =
      associatedModuleObjRestrictNatIso B S hS T' :=
  associatedModuleObjRestrictNatIso_ext B S hS adj h

end AlgebraicGeometry.BigFppfOver

end
