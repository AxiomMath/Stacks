module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjRestrictIsoFactors
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RightAdjointComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackCompMate

/-!
# The mate of the comparison of Stacks 03DV

For `T` an object of the big fppf category over `S` with structure morphism `f : X ⟶ S`,
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` is the comparison

    `(f^*𝓕)^a ≅ (𝓕^a)|_{(Sch/X)_fppf}`

that Stacks 03DV leaves implicit.  It is assembled entirely out of isomorphisms produced by
`CategoryTheory.Adjunction.leftAdjointUniq`, so no unfolding computes it; the one handle on such
an isomorphism is its mate, and
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_ext` says the mate determines
it.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/NatIsoCoherence.lean` record that mate as
the computation that was missing.  This file supplies it.

Both factors of the comparison are treated.  The factor
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso` between the two spellings of one
and the same ringed site — the localization of the big fppf site of `S` at `T`, and the big fppf
site of `X` — is the composite of five isomorphisms made explicit by
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso_eq`, and its mate is computed
factor by factor: the two pullback transports contribute
`SheafOfModules.pushforwardCongr` and `SheafOfModules.pushforwardComp`, the comparison of two
left adjoints of one and the same pushforward contributes nothing, the counit of the reindexing
equivalence of Stacks 06WI contributes the unit of the inverse equivalence, and the right unitor
contributes the left unitor of the right adjoint.  The other factor,
`AlgebraicGeometry.BigFppfOver.associatedModuleObjIso`, has its mate from
`AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_associatedModuleObjIso`, and the two are joined
by the mates of the structural associators and whiskerings.

Every isomorphism on the right-hand side of both results is a comparison of *pushforwards* of
sheaves of modules, hence the identity on sections.

## Main results

* `AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_associatedModuleObjRestrictIso`: **the mate of
  the comparison of Stacks 03DV between the two spellings of the site**, with respect to the
  associated-module adjunction of the scheme of `T` on one side and the composite of the
  localized pullback–pushforward adjunction with the reindexing equivalence of Stacks 06WI on the
  other.  It is the unit of the inverse reindexing equivalence followed by the contraction of the
  iterated pushforward and the transport along
  `AlgebraicGeometry.BigFppfOver.objSliceStructureMap_eq`.
* `AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_associatedModuleObjRestrictNatIso`: **the mate
  of the comparison of Stacks 03DV**, with respect to
  `AlgebraicGeometry.BigFppfOver.objRestrictAdjunction` for restriction to an object.  This is
  the computation that `associatedModuleObjRestrictNatIso_ext` and
  `associatedModuleObjRestrictNatIso_comp_of_conjugate` were waiting for.

## Implementation notes

Nothing here carries a `stacks` attribute: the comparison this file is about is a step
Stacks 03DV leaves implicit and carries no tag of its own.

Nothing here unfolds `AlgebraicGeometry.BigFppfOver.objRestrict`, a reducible abbreviation whose
body is the structure sheaf of the big fppf site, and nothing evaluates a functor between
categories of sheaves of modules at an object; both statements are whiskered identities of
natural transformations.  Both proofs are chains of `Eq.trans` and `congrArg` rather than
rewrites: `rw` fails on these goals because the two readings of a category of sheaves of modules
over a scheme — `S.Modules` and `SheafOfModules S.ringCatSheaf` — are definitionally but not
syntactically equal, so the rewritten target is reported as not type-correct under the
`implicit` transparency level.  For the same reason the intermediate adjunctions of
`Stacks.Mates.conjugateIsoEquiv_trans` are left to unification, which runs at default
transparency, instead of being supplied to `rw`, which does not.

**What is still owed for the three-way coherence.**  These two results discharge three of the
four entries of the pentagon of
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_comp_of_pentagon`: taking
`AlgebraicGeometry.BigFppfOver.objRestrictAdjunction` for restriction to an object, the mates of
the comparison of Stacks 03DV at the three objects involved are given by
`conjugateIsoEquiv_associatedModuleObjRestrictNatIso`, and the mate of the contraction of the
iterated pullback by
`AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_pullbackComp_objHom`.  None of those four
isomorphisms mentions
`AlgebraicGeometry.BigFppfOver.objRestrictRightAdjointIso`.  The remaining entry is the mate of
`AlgebraicGeometry.BigFppfOver.objRestrictComp`, and the only computation of it with respect to
`objRestrictAdjunction` is
`AlgebraicGeometry.BigFppfOver.conjugateIsoEquiv_objRestrictComp_objRestrictAdjunction`, which
expresses it through *three* occurrences of `objRestrictRightAdjointIso` — at `T`, at `T'` and at
the object of the big fppf category over the scheme of `T` — and `SheafOfModules.overPullback`.
Those three occurrences have nothing to cancel against, and the count does not depend on which
adjunctions are chosen for restriction to an object, the pentagon being equivalent to the same
identity for every choice.  So the pentagon is equivalent to a computation of the mate of
`objRestrictComp` that does *not* go through `objRestrictRightAdjointIso` — equivalently, to the
compatibility of `objRestrictRightAdjointIso` with the two composition isomorphisms — and that
identity is not a consequence of the four entries.  It is a statement about the big fppf
category: the product with `T'` is the product with `T` followed by the product with `T'` over
the scheme of `T`, as functors of sites, together with the compatibility of the three structure
sheaves.  `AlgebraicGeometry.BigFppfOver.objStarIso` is the corresponding statement on the small
Zariski site of `S` only.

## References

* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- **The mate of the comparison of Stacks 03DV between the two spellings of the site.**
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso` identifies the pullback along the
comparison of ringed sites of the localization at `T`, followed by the reindexing of
Stacks 06WI, with the associated-module functor of the scheme `X` of `T`.  Both are left
adjoints, and the mate of the comparison — with respect to
`AlgebraicGeometry.BigFppfOver.associatedModuleAdjunction` of `X` on one side and the composite
of the localized pullback–pushforward adjunction with the reindexing equivalence on the other —
is the isomorphism

    `𝓖 ↦ 𝓖|_{X_Zar}  ≅  𝓖 ↦ (𝓖 reindexed back)|_{X_Zar}`

of restrictions along the small Zariski site of `X`: the unit of the inverse reindexing
equivalence, followed by the contraction of the iterated pushforward along the structure map of
`X` and the (identity) comparison of the reindexing, followed by the transport along
`AlgebraicGeometry.BigFppfOver.objSliceStructureMap_eq`.

The computation is factor by factor on
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso_eq`.  The third factor there,
`CategoryTheory.Adjunction.leftAdjointUniq` of two left adjoints of one and the same pushforward,
contributes the identity by `Stacks.Mates.conjugateIsoEquiv_leftAdjointUniq`, which is why no
trace of it survives on the right. -/
public theorem conjugateIsoEquiv_associatedModuleObjRestrictIso :
    conjugateIsoEquiv
        (associatedModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T))
        ((SheafOfModules.pullbackPushforwardAdjunction.{u} (objSliceStructureMap B S hS T)).comp
          (Stacks.SheafOfModules.reindexEquivalence
            (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
            (objEquiv B S hS T) ((structureSheaf B S hS).over T)).toAdjunction)
        (associatedModuleObjRestrictIso B S hS T) =
      (Functor.leftUnitor (restrictModule B (objScheme B S hS T)
            (contains_objScheme B S hS T))).symm ≪≫
        Functor.isoWhiskerRight
            (Stacks.SheafOfModules.reindexEquivalence
              (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
              (objEquiv B S hS T) ((structureSheaf B S hS).over T)).symm.unitIso
            (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)) ≪≫
          Functor.associator
              (Stacks.SheafOfModules.reindexEquivalence
                (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
                (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse
              (SheafOfModules.pushforward.{u} (objReindexSharp B S hS T))
              (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)) ≪≫
            Functor.isoWhiskerLeft
              (Stacks.SheafOfModules.reindexEquivalence
                (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
                (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse
              (SheafOfModules.pushforwardComp.{u}
                  (structureMap B (objScheme B S hS T) (contains_objScheme B S hS T))
                  (objReindexSharp B S hS T) ≪≫
                SheafOfModules.pushforwardCongr.{u}
                  (objSliceStructureMap_eq B S hS T).symm) := by
  rw [associatedModuleObjRestrictIso_eq]
  have h4 : conjugateIsoEquiv
        (associatedModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T))
        ((associatedModuleAdjunction B (objScheme B S hS T)
          (contains_objScheme B S hS T)).comp Adjunction.id)
        (Functor.rightUnitor
          (associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T))) =
      (Functor.leftUnitor
        (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T))).symm :=
    Iso.ext (conjugateEquiv_rightUnitor_hom
      (associatedModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)))
  have h2 : conjugateIsoEquiv
        ((associatedModuleAdjunction B (objScheme B S hS T)
            (contains_objScheme B S hS T)).comp
          ((SheafOfModules.pullbackPushforwardAdjunction.{u} (objReindexSharp B S hS T)).comp
            (Stacks.SheafOfModules.reindexEquivalence
              (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
              (objEquiv B S hS T) ((structureSheaf B S hS).over T)).toAdjunction))
        (((associatedModuleAdjunction B (objScheme B S hS T)
            (contains_objScheme B S hS T)).comp
          (SheafOfModules.pullbackPushforwardAdjunction.{u} (objReindexSharp B S hS T))).comp
          (Stacks.SheafOfModules.reindexEquivalence
            (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
            (objEquiv B S hS T) ((structureSheaf B S hS).over T)).toAdjunction)
        (Functor.associator
          (associatedModule B (objScheme B S hS T) (contains_objScheme B S hS T))
          (SheafOfModules.pullback.{u} (objReindexSharp B S hS T))
          (objRestrictFunctor B S hS T)) =
      Functor.associator _ _ _ :=
    Iso.ext (conjugateEquiv_associator_hom
      (associatedModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T))
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (objReindexSharp B S hS T))
      (Stacks.SheafOfModules.reindexEquivalence
        (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
        (objEquiv B S hS T) ((structureSheaf B S hS).over T)).toAdjunction)
  refine Eq.trans (Eq.trans (Stacks.Mates.conjugateIsoEquiv_trans _ _ _ _ _)
    (congrArg₂ (fun a b => a ≪≫ b)
      (Eq.trans (Stacks.Mates.conjugateIsoEquiv_trans _ _ _ _ _)
        (congrArg₂ (fun a b => a ≪≫ b)
          (Eq.trans (Stacks.Mates.conjugateIsoEquiv_trans _ _ _ _ _)
            (congrArg₂ (fun a b => a ≪≫ b) h4
              (Eq.trans (Stacks.Mates.conjugateIsoEquiv_isoWhiskerLeft _ _ _ _)
                (congrArg (fun x => Functor.isoWhiskerRight x
                    (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)))
                  (Eq.trans (Stacks.Mates.conjugateIsoEquiv_trans _ _ _ _ _)
                    (Eq.trans
                      (congrArg₂ (fun a b => a ≪≫ b)
                        (Stacks.Mates.conjugateIsoEquiv_equivalenceCounitIso
                          (Stacks.SheafOfModules.reindexEquivalence
                            (J' := topology B (objScheme B S hS T)
                              (contains_objScheme B S hS T))
                            (objEquiv B S hS T) ((structureSheaf B S hS).over T)))
                        (Eq.trans (Stacks.Mates.conjugateIsoEquiv_isoWhiskerRight _ _ _ _)
                          (Eq.trans
                            (congrArg (fun x => Functor.isoWhiskerLeft
                                (Stacks.SheafOfModules.reindexEquivalence
                                  (J' := topology B (objScheme B S hS T)
                                    (contains_objScheme B S hS T))
                                  (objEquiv B S hS T)
                                  ((structureSheaf B S hS).over T)).inverse x)
                              (Stacks.Mates.conjugateIsoEquiv_leftAdjointUniq
                                (SheafOfModules.pullbackPushforwardAdjunction.{u}
                                  (objReindexSharp B S hS T))
                                (Stacks.SheafOfModules.reindexEquivalence
                                  (J' := topology B (objScheme B S hS T)
                                    (contains_objScheme B S hS T))
                                  (objEquiv B S hS T)
                                  ((structureSheaf B S hS).over T)).symm.toAdjunction))
                            (Functor.isoWhiskerLeft_refl _ _))))
                      (Iso.trans_refl _)))))))
          h2))
      (Eq.trans (Stacks.Mates.conjugateIsoEquiv_isoWhiskerRight _ _ _ _)
        (congrArg (fun x => Functor.isoWhiskerLeft
            (Stacks.SheafOfModules.reindexEquivalence
              (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
              (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse x)
          (Eq.trans (Stacks.Mates.conjugateIsoEquiv_trans _ _ _ _ _)
            (congrArg₂ (fun a b => a ≪≫ b)
              (Stacks.SheafOfModules.conjugateIsoEquiv_pullbackComp_symm _ _)
              (@Stacks.SheafOfModules.conjugateIsoEquiv_pullbackCongr _ _ _ _ _ _ _ _ _ _ _ _
                (sheafPushforward_objSliceStructureMap_isRightAdjoint B S hS T)
                (isRightAdjoint_pushforward_objSliceStructureMapFactored B S hS T)
                (objSliceStructureMap_eq B S hS T)))))))) ?_
  exact Eq.trans (Iso.trans_assoc _ _ _) (Iso.trans_assoc _ _ _)

/-- **The mate of the comparison of Stacks 03DV.**  For `f : X ⟶ S` the structure morphism of an
object `T` of the big fppf category over `S`, the comparison

    `(f^*𝓕)^a ≅ (𝓕^a)|_{(Sch/X)_fppf}`

of `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` is an isomorphism between
two left adjoints — the source by the composite of the pullback of modules on schemes with the
associated-module functor of `X`, the target by
`AlgebraicGeometry.BigFppfOver.associatedModuleAdjunction` composed with
`AlgebraicGeometry.BigFppfOver.objRestrictAdjunction` — and this is its mate: the composite of
the comparison of pushforwards that the square of ringed sites of
`AlgebraicGeometry.BigFppfOver.comparisonComp_objStarIso` supplies with the mate of
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictIso`, joined by the structural
associators.  Every factor is a comparison of pushforwards of sheaves of modules, hence the
identity on sections.

This is the computation named as missing in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/NatIsoCoherence.lean`; with it,
`AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso_ext` becomes usable, because
both sides of any identity between comparisons of this shape can now be computed. -/
public theorem conjugateIsoEquiv_associatedModuleObjRestrictNatIso :
    conjugateIsoEquiv ((associatedModuleAdjunction B S hS).comp (objRestrictAdjunction B S hS T))
        ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).comp
          (associatedModuleAdjunction B (objScheme B S hS T) (contains_objScheme B S hS T)))
        (associatedModuleObjRestrictNatIso B S hS T) =
      Functor.associator (Stacks.SheafOfModules.reindexEquivalence
          (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
          (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse
            (SheafOfModules.pushforward.{u} (SheafOfModules.pushforwardOver T))
            (restrictModule B S hS) ≪≫
        Functor.isoWhiskerLeft (Stacks.SheafOfModules.reindexEquivalence
          (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
          (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse
            (SheafOfModules.pushforwardComp.{u} (structureMap B S hS)
                (SheafOfModules.pushforwardOver T) ≪≫
              SheafOfModules.pushforwardCongr₂.{u} _ (objStarIso B S hS T)
                  (comparisonComp_objStarIso B S hS T) ≪≫
                (SheafOfModules.pushforwardComp.{u} (objHom B S hS T).toRingCatSheafHom
                  (objSliceStructureMap B S hS T)).symm) ≪≫
          (Functor.associator (Stacks.SheafOfModules.reindexEquivalence
          (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
          (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse
                (SheafOfModules.pushforward.{u} (objSliceStructureMap B S hS T))
                (Scheme.Modules.pushforward (objHom B S hS T))).symm ≪≫
            (Functor.isoWhiskerRight
              ((Functor.leftUnitor
                      (restrictModule B (objScheme B S hS T)
                        (contains_objScheme B S hS T))).symm ≪≫
              Functor.isoWhiskerRight (Stacks.SheafOfModules.reindexEquivalence
          (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
          (objEquiv B S hS T) ((structureSheaf B S hS).over T)).symm.unitIso
                  (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)) ≪≫
                Functor.associator (Stacks.SheafOfModules.reindexEquivalence
          (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
          (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse
                    (SheafOfModules.pushforward.{u} (objReindexSharp B S hS T))
                    (restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)) ≪≫
                  Functor.isoWhiskerLeft (Stacks.SheafOfModules.reindexEquivalence
          (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
          (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse
                    (SheafOfModules.pushforwardComp.{u}
                        (structureMap B (objScheme B S hS T) (contains_objScheme B S hS T))
                        (objReindexSharp B S hS T) ≪≫
                      SheafOfModules.pushforwardCongr.{u}
                        (objSliceStructureMap_eq B S hS T).symm))
              (Scheme.Modules.pushforward (objHom B S hS T))).symm := by
  have hD : conjugateIsoEquiv
        ((associatedModuleAdjunction B S hS).comp (objRestrictAdjunction B S hS T))
        (((associatedModuleAdjunction B S hS).comp
            (SheafOfModules.overPushforwardOverAdj.{u} (R := structureSheaf B S hS) T)).comp
          (Stacks.SheafOfModules.reindexEquivalence
          (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
          (objEquiv B S hS T) ((structureSheaf B S hS).over T)).toAdjunction)
        (Functor.associator (associatedModule B S hS)
          (SheafOfModules.overFunctor.{u} (structureSheaf B S hS) T)
          (objRestrictFunctor B S hS T)) =
      Functor.associator _ _ _ :=
    Iso.ext (conjugateEquiv_associator_hom (associatedModuleAdjunction B S hS)
      (SheafOfModules.overPushforwardOverAdj.{u} (R := structureSheaf B S hS) T)
      (Stacks.SheafOfModules.reindexEquivalence
          (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
          (objEquiv B S hS T) ((structureSheaf B S hS).over T)).toAdjunction)
  have hB : conjugateIsoEquiv
        ((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).comp
          ((SheafOfModules.pullbackPushforwardAdjunction.{u}
              (objSliceStructureMap B S hS T)).comp (Stacks.SheafOfModules.reindexEquivalence
          (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
          (objEquiv B S hS T) ((structureSheaf B S hS).over T)).toAdjunction))
        (((Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T)).comp
            (SheafOfModules.pullbackPushforwardAdjunction.{u}
              (objSliceStructureMap B S hS T))).comp (Stacks.SheafOfModules.reindexEquivalence
          (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
          (objEquiv B S hS T) ((structureSheaf B S hS).over T)).toAdjunction)
        (Functor.associator (Scheme.Modules.pullback (objHom B S hS T))
          (SheafOfModules.pullback.{u} (objSliceStructureMap B S hS T))
          (objRestrictFunctor B S hS T)) =
      Functor.associator _ _ _ :=
    Iso.ext (conjugateEquiv_associator_hom
      (Scheme.Modules.pullbackPushforwardAdjunction (objHom B S hS T))
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (objSliceStructureMap B S hS T))
      (Stacks.SheafOfModules.reindexEquivalence
          (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
          (objEquiv B S hS T) ((structureSheaf B S hS).over T)).toAdjunction)
  refine Eq.trans (Eq.trans (Stacks.Mates.conjugateIsoEquiv_trans _ _ _ _ _)
    (congrArg₂ (fun a b => a ≪≫ b)
      (Eq.trans (Stacks.Mates.conjugateIsoEquiv_trans _ _ _ _ _)
        (congrArg₂ (fun a b => a ≪≫ b)
          (Eq.trans (Stacks.Mates.conjugateIsoEquiv_trans _ _ _ _ _)
            (congrArg₂ (fun a b => a ≪≫ b) hD
              (Eq.trans (Stacks.Mates.conjugateIsoEquiv_isoWhiskerRight _ _ _ _)
                (congrArg (fun x => Functor.isoWhiskerLeft
                    (Stacks.SheafOfModules.reindexEquivalence
                      (J' := topology B (objScheme B S hS T)
                        (contains_objScheme B S hS T))
                      (objEquiv B S hS T) ((structureSheaf B S hS).over T)).inverse x)
                  (conjugateIsoEquiv_associatedModuleObjIso B S hS T)))))
          (Eq.trans (Stacks.Mates.conjugateIsoEquiv_iso_symm _ _ _)
            (congrArg Iso.symm hB))))
      (Eq.trans (Stacks.Mates.conjugateIsoEquiv_iso_symm _ _ _)
        (congrArg Iso.symm
          (Eq.trans (Stacks.Mates.conjugateIsoEquiv_isoWhiskerLeft _ _ _ _)
            (congrArg
              (fun x => Functor.isoWhiskerRight x
                (Scheme.Modules.pushforward (objHom B S hS T)))
              (conjugateIsoEquiv_associatedModuleObjRestrictIso B S hS T))))))) ?_
  exact Eq.trans (Iso.trans_assoc _ _ _) (Iso.trans_assoc _ _ _)

end AlgebraicGeometry.BigFppfOver

end
