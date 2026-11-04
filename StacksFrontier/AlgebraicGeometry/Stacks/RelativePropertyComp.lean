module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangeComposite

/-!
# A relative property stable under composition is stable under composition (Stacks 045B)

Let `S` be a scheme contained in a big fppf site `B` and let `P` be a property of morphisms of
algebraic spaces over `S` which is stable under base change, local on the target for the fppf
precoverage, and stable under composition. Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of
categories fibred in groupoids over the big fppf site of `S`, both representable by algebraic
spaces and both having `P` relatively in the sense of Stacks 03YK. Stacks 045B says that `f ≫ g`
again has `P`.

The proof is the one in the source. Fix a scheme `U` over `S` and a scheme-valued point `z` of
`𝒵`, and let `F` be an algebraic space over `U` representing the base change of `f ≫ g` along
`z`. Representability of `g` gives an algebraic space `G` over `U` representing the base change
of `g` along `z`, and the structural morphism `G → U` has `P` by `hPg`. The two base changes are
related by `CategoryTheory.PresheafOfCategories.baseChangeNatTrans`, a morphism `F → G` *over*
`U`, so it suffices to see that `F → G` has `P`, and `P` is then inherited by the composite.

That `F → G` has `P` is locality on the target. Take a scheme atlas `A → G` of `G` *itself*
(`AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`), so that nothing has to be relocalized: by
`AlgebraicGeometry.Space.prop_iff_pullbackSnd_atlas` it suffices that the base change of
`F → G` to `A` has `P`, and
`CategoryTheory.PresheafOfCategories.exists_isPullback_baseChangeNatTrans` identifies that base
change with the lower-shriek extension of an algebraic space over `A` representing the base
change of `f` alone along a scheme-valued point of `𝒴`. That is an instance of `hPf`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_relocalizePresheaf`: the lower-shriek extension of an
  algebraic space over a scheme of the site is an algebraic space over the base.
* `AlgebraicGeometry.Space.prop_relocalizeToYoneda_iff`: the morphism of algebraic spaces that
  the relative-property statements of Stacks 03YK are about may equally be read as
  `CategoryTheory.OverShriek.relocalizeToYoneda`.
* `AlgebraicGeometry.Stack.prop_comp_of_atlasDescent`: **Stacks 045B** with the condition of
  Stacks 04XB written out longhand and locality on the target weakened to descent along a
  surjective étale scheme chart of the target, which is the form the separation axioms of
  Stacks 04YW need.
* `AlgebraicGeometry.Stack.hasRelativeProperty_comp`: **Stacks 045B**.

## Implementation notes

The representability witness of the composite is the one Stacks 0301
(`AlgebraicGeometry.isRepresentableByAlgebraicSpaces_comp`) builds from the witnesses for the two
factors, so representability of the composite is a conclusion and not a hypothesis. The witness
argument of `AlgebraicGeometry.Stack.HasRelativeProperty` is inert —
`HasRelativeProperty B S hS P f h₁` and `HasRelativeProperty B S hS P f h₂` are the same
proposition by `rfl` — so the statement may equally be read at any other witness.

`AlgebraicGeometry.Space.Topology.fppf.precoverage` has an index universe independent of the
universe of the site, so the `CategoryTheory.MorphismProperty.IsLocalAtTarget` hypothesis carries
a second universe argument, which is the one
`AlgebraicGeometry.Space.prop_iff_pullbackSnd_atlas` is instantiated at.

The square of presheaves produced by
`CategoryTheory.PresheafOfCategories.exists_isPullback_baseChangeNatTrans` is cartesian in the
category of algebraic spaces because the inclusion of that full subcategory reflects fibre
products — that is
`AlgebraicGeometry.Space.algebraicSpaceProperty_isClosedUnderLimitsOfShape_walkingCospan` —
and the comparison with the *chosen* fibre product that
`AlgebraicGeometry.Space.prop_iff_pullbackSnd_atlas` speaks about is
`CategoryTheory.IsPullback.isoPullback`, absorbed by `RespectsIso`.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.OverShriek
open CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry

universe u v w t

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03I5 part (2), read through Stacks 04SG.** The lower-shriek extension along the
structural morphism of `U` of an algebraic space over `U` is an algebraic space over `S`: it is
the image of the forward functor of Stacks 04SG, after forgetting the morphism to the
representable algebraic space of `U`. -/
theorem isAlgebraicSpace_relocalizePresheaf (U : BigFppfOver B S hS)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F) :
    IsAlgebraicSpace B S hS ((relocalizePresheafFunctor U.hom).obj F) :=
  AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS
    ((spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).app
      ⟨F, hF⟩).symm
    ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).property

/-- **Stacks 04SG.** The morphism of algebraic spaces over `S` that the relative-property
statements of Stacks 03YK and Stacks 026O are about — the structural morphism of the image of `F`
under the forward functor of Stacks 04SG — has a property respecting isomorphisms exactly when
the relocalization's own structural morphism `CategoryTheory.OverShriek.relocalizeToYoneda`
does. -/
theorem prop_relocalizeToYoneda_iff (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.RespectsIso] (U : BigFppfOver B S hS)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F) :
    P (ObjectProperty.homMk (relocalizeToYoneda U.hom F) :
        (⟨(relocalizePresheafFunctor U.hom).obj F,
            isAlgebraicSpace_relocalizePresheaf B S hS U F hF⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩) ↔
      P (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  have hiso : IsIso (ObjectProperty.homMk
        ((spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).inv.app
          ⟨F, hF⟩) :
      (⟨(relocalizePresheafFunctor U.hom).obj F,
          isAlgebraicSpace_relocalizePresheaf B S hS U F hF⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).obj.left,
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
            ⟨F, hF⟩).property⟩) :=
    ⟨⟨ObjectProperty.homMk
        ((spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).hom.app
          ⟨F, hF⟩),
      ObjectProperty.hom_ext _ (by simp), ObjectProperty.hom_ext _ (by simp)⟩⟩
  have hfac : (ObjectProperty.homMk
        ((spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).inv.app
          ⟨F, hF⟩) :
      (⟨(relocalizePresheafFunctor U.hom).obj F,
          isAlgebraicSpace_relocalizePresheaf B S hS U F hF⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).obj.left,
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
            ⟨F, hF⟩).property⟩) ≫
        algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩) =
      ObjectProperty.homMk (relocalizeToYoneda U.hom F) :=
    ObjectProperty.hom_ext _
      (relocalizeToYoneda_eq B U.left.1 S U.left.2 hS U.hom ⟨F, hF⟩)
  have key := P.cancel_left_of_respectsIso (ObjectProperty.homMk
        ((spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).inv.app
          ⟨F, hF⟩) :
      (⟨(relocalizePresheafFunctor U.hom).obj F,
          isAlgebraicSpace_relocalizePresheaf B S hS U F hF⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).obj.left,
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
            ⟨F, hF⟩).property⟩)
    (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))
  rw [hfac] at key
  exact key

end Space

namespace Stack

/-- **Stacks 045B with locality on the target replaced by descent along a scheme atlas.** Let `P`
be a property of morphisms of algebraic spaces over `S` which respects isomorphisms, is stable
under composition, and may be tested on the base change of a morphism to a surjective étale
scheme chart of its target. If two composable 1-morphisms of categories fibred in groupoids over
the big fppf site of `S` are representable by algebraic spaces and satisfy the condition of
Stacks 04XB for `P`, then so does their composite.

This is the form of Stacks 045B that applies to the separation axioms of Stacks 04YW. The reason
it is needed is the one recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties`:
`AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**) carries
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange` and
`CategoryTheory.MorphismProperty.IsLocalAtTarget` as instance arguments, and for quasi-compactness,
quasi-separatedness, unramifiedness, properness and local quasi-finiteness of morphisms of
algebraic spaces over `S` the locality instance is not in the library, so a *statement* about
`HasRelativeProperty` cannot even be elaborated at those properties. The condition of Stacks 04XB
is therefore written out longhand, and locality on the target is weakened to the single
consequence of it that the proof uses, namely the one
`AlgebraicGeometry.Space.prop_iff_pullbackSnd_atlas` draws from it.
`AlgebraicGeometry.Stack.hasRelativeProperty_comp` is the specialisation back to the instance
form. -/
theorem prop_comp_of_atlasDescent
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.RespectsIso] [P.IsStableUnderComposition]
    (hatlas : ∀ {X Y : AlgebraicSpaces B S hS} (k : X ⟶ Y) {T : BigFppfOver B S hS}
      {a : yoneda.obj T ⟶ Y.obj},
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a →
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a →
      P (Limits.pullback.snd k (ObjectProperty.homMk a :
        (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y)) → P k)
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hPf : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)))
    (hPg : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒵.val.obj)
      (_hz : z ⋙ 𝒵.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒴.val.p 𝒵.val.p z
            (CatFiberedInGroupoids.homFunctor g))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒵.val.obj)
      (_hz : z ⋙ 𝒵.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒵.val.p z
            (CatFiberedInGroupoids.homFunctor (f ≫ g)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  intro U zz hz Fp hFp hE
  obtain ⟨E⟩ := hE
  obtain ⟨Gq, hGq, ⟨EG⟩⟩ := hg U zz hz
  have hΛFp := Space.isAlgebraicSpace_relocalizePresheaf B S hS U Fp hFp
  have hΛGq := Space.isAlgebraicSpace_relocalizePresheaf B S hS U Gq hGq
  -- The structural morphism of the representing space of `U ×_𝒵 𝒴` has `P`, by `hPg`.
  have hPG : P (ObjectProperty.homMk (relocalizeToYoneda U.hom Gq) :
      (⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩) :=
    (Space.prop_relocalizeToYoneda_iff B S hS P U Gq hGq).2 (hPg U zz hz Gq hGq ⟨EG⟩)
  -- The comparison morphism of the two representing spaces has `P`, by locality over a scheme
  -- atlas of the representing space of `U ×_𝒵 𝒴`.
  have hPm : P (ObjectProperty.homMk (baseChangeNatTrans U.hom zz f.hom.w E EG) :
      (⟨(relocalizePresheafFunctor U.hom).obj Fp, hΛFp⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩) := by
    obtain ⟨T, aa, hsurj, hetale⟩ := hΛGq.exists_atlas
    refine hatlas _ hsurj hetale ?_
    obtain ⟨fib, c, y, hc, hy, ⟨Efib⟩⟩ :=
      exists_isPullback_baseChangeNatTrans U.hom zz f.hom.w E EG g.hom.w hz
        𝒳.property 𝒴.property 𝒵.property T.left T.hom aa
    obtain ⟨F', hF', ⟨E'⟩⟩ := hf (Over.mk T.hom) y hy
    have hfib : IsAlgebraicSpace B T.left.1 T.left.2 fib :=
      isAlgebraicSpace_of_iso B T.left.1 T.left.2 (isoOfEquivalenceOver Efib E') hF'
    have hΛfib := Space.isAlgebraicSpace_relocalizePresheaf B S hS (Over.mk T.hom) fib hfib
    have hPfib : P (ObjectProperty.homMk (relocalizeToYoneda T.hom fib) :
        (⟨(relocalizePresheafFunctor T.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj (Over.mk T.hom), isAlgebraicSpace_yoneda B S hS (Over.mk T.hom)⟩) :=
      (Space.prop_relocalizeToYoneda_iff B S hS P (Over.mk T.hom) fib hfib).2
        (hPf (Over.mk T.hom) y hy fib hfib ⟨Efib⟩)
    have hsq : IsPullback
        (ObjectProperty.homMk c :
          (⟨(relocalizePresheafFunctor T.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨(relocalizePresheafFunctor U.hom).obj Fp, hΛFp⟩)
        (ObjectProperty.homMk (relocalizeToYoneda T.hom fib) :
          (⟨(relocalizePresheafFunctor T.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩)
        (ObjectProperty.homMk (baseChangeNatTrans U.hom zz f.hom.w E EG) :
          (⟨(relocalizePresheafFunctor U.hom).obj Fp, hΛFp⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩)
        (ObjectProperty.homMk aa :
          (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩) :=
      IsPullback.of_map_of_faithful (ObjectProperty.ι _) hc
    rw [← P.cancel_left_of_respectsIso hsq.isoPullback.hom, hsq.isoPullback_hom_snd]
    exact hPfib
  -- `P` is stable under composition, and the comparison is a morphism over `U`.
  refine (Space.prop_relocalizeToYoneda_iff B S hS P U Fp hFp).1 ?_
  have hcomp : (ObjectProperty.homMk (baseChangeNatTrans U.hom zz f.hom.w E EG) :
        (⟨(relocalizePresheafFunctor U.hom).obj Fp, hΛFp⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩) ≫
        (ObjectProperty.homMk (relocalizeToYoneda U.hom Gq) :
          (⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩) =
      ObjectProperty.homMk (relocalizeToYoneda U.hom Fp) :=
    ObjectProperty.hom_ext _
      (baseChangeNatTrans_comp_relocalizeToYoneda U.hom zz f.hom.w E EG)
  have key := P.comp_mem _ _ hPm hPG
  rw [hcomp] at key
  exact key


/-- **Stacks 045B.** Let `P` be a property of morphisms of algebraic spaces over `S` which is
stable under base change, local on the target for the fppf precoverage, and stable under
composition. If two composable 1-morphisms of categories fibred in groupoids over the big fppf
site of `S` are representable by algebraic spaces and have the relative property `P` of Stacks
03YK, then so does their composite. -/
@[stacks 045B]
theorem hasRelativeProperty_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, t} B S hS)]
    [P.IsStableUnderComposition]
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hPf : HasRelativeProperty B S hS P f hf)
    (hPg : HasRelativeProperty B S hS P g hg) :
    HasRelativeProperty B S hS P (f ≫ g)
      (isRepresentableByAlgebraicSpaces_comp B S hS f g hf hg) :=
  prop_comp_of_atlasDescent B S hS P
    (fun {_X _Y} k {_T} {_a} hsurj hetale h =>
      (Space.prop_iff_pullbackSnd_atlas.{u, t} B S hS P k hsurj hetale).2 h)
    f g hf hg hPf hPg
end Stack

end AlgebraicGeometry

end
