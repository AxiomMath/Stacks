module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityPostcomp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangePoint
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCompositeBaseChangeRepresentable

/-!
# Étaleness and representability are cancelled by an étale second factor (Stacks 05XK)

Let `𝒳 ⟶ 𝒴 ⟶ 𝒵` be 1-morphisms of categories fibred in groupoids over the big fppf site of a
scheme `S`. Stacks 05XK says that if `𝒳 ⟶ 𝒵` and `𝒴 ⟶ 𝒵` are representable by algebraic spaces
and étale, then so is `𝒳 ⟶ 𝒴`. The two conclusions are independent of each other and are proved
separately here.

Representability is cancellation of a representable postcomposition, since `𝒳 ⟶ 𝒴` is a
1-morphism in the categories over `𝒵` from `𝒳 ⟶ 𝒵` to `𝒴 ⟶ 𝒵`.

Étaleness is the corresponding cancellation for the relative property of Stacks 03YK. Fix a
scheme-valued point `y` of `𝒴` over a scheme `U` over `S` and an algebraic space `F` over `U`
representing `(Sch/U)_{fppf} ×_{y, 𝒴, f} 𝒳`. Let `G`, respectively `H`, be an algebraic space
over `U` representing the base change of `f ≫ g`, respectively of `g`, along the induced point
`y ≫ g` of `𝒵`. Then

* the structural morphisms of `G` and of `H` are étale, by the two hypotheses;
* the comparison morphism `G ⟶ H` of Stacks 045B
  (`CategoryTheory.PresheafOfCategories.baseChangeNatTrans`) is a morphism over `U`, so it is
  étale by Stacks 03FV, cancellation of an étale postcomposition for morphisms of algebraic
  spaces;
* the structural morphism of `F` is a base change of that comparison morphism, by
  `CategoryTheory.PresheafOfCategories.exists_section_isPullback_baseChangeNatTrans_of_point`
  applied to
  the canonical point of the intermediate 2-fibre product attached to `y`, so it is étale by
  Stacks 03FU.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_comp`: **Stacks 05XK**,
  representability of the intervening 1-morphism.
* `AlgebraicGeometry.Stack.isEtale_algebraicSpaceMap_of_comp`: **Stacks 05XK**, étaleness of the
  intervening 1-morphism.
* `AlgebraicGeometry.Stack.isRelativelyEtale_of_comp`: the two together, in the vocabulary of
  `AlgebraicGeometry.Stack.IsRelativelyEtale`.

## Implementation notes

Étaleness of a representable 1-morphism is written out as the universally quantified statement
of Stacks 03YK rather than through `AlgebraicGeometry.Stack.HasRelativeProperty`, for the reason
recorded in `StacksFrontier.AlgebraicGeometry.Stacks.EtaleSmoothLocalMorphism`: that definition
takes locality at the target for the fppf precoverage as an instance argument, and that instance
is not available for `AlgebraicGeometry.Space.etaleMorphisms`. Its body uses neither instance, so
the longhand is the same proposition with no hypothesis on the property; it is the body of
`AlgebraicGeometry.Stack.IsRelativelyEtale`, which cannot be used directly because that
abbreviation is pinned at `CatFiberedInGroupoids.{u, u, u + 1, u + 1}` while the statement below
holds at free universes. Note that the proof genuinely needs no locality hypothesis either —
unlike Stacks 045B, which obtains the comparison morphism's property from a covering of the
intermediate space, cancellation gets it from Stacks 03FV outright.

The point of the intermediate 2-fibre product `(Sch/U)_{fppf} ×_{y ≫ g, 𝒵, g} 𝒴` attached to `y`
is `CategoryTheory.TwoFibreProductOver.baseChangeSection`, whose second projection is `y` itself.
That is why the prescribed-point form of the fibre-product identification is needed: the
algebraic space the statement quantifies over represents the base change along `y` on the nose,
and a point only 2-isomorphic to `y` would not do.

## References

* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 05XK](https://stacks.math.columbia.edu/tag/05XK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.OverShriek
open CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u v w

/-- **Stacks 05XK.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of categories fibred in
groupoids over the big fppf site of `S`. If `f ≫ g` and `g` are representable by algebraic
spaces, then so is `f`.

This is cancellation of a representable postcomposition,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_postcomp`, applied to the triangle
formed by `f`, `g` and `f ≫ g`, whose comparison 2-cell is the identity. -/
@[stacks 05XK "representability"]
theorem isRepresentableByAlgebraicSpaces_of_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsRepresentableByAlgebraicSpaces B S hS (f ≫ g).hom)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom :=
  isRepresentableByAlgebraicSpaces_of_postcomp B S hS g.hom (f ≫ g).hom f.hom
    (Iso.refl _) hg hfg

/-- **Stacks 05XK.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of categories fibred in
groupoids over the big fppf site of `S`, with `f ≫ g` and `g` representable by algebraic spaces.
If every algebraic space representing a base change of `f ≫ g`, respectively of `g`, along a
scheme-valued point of `𝒵` has étale structural morphism, then so does every algebraic space
representing a base change of `f` along a scheme-valued point of `𝒴`.

Together with `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_comp` this is the
statement that an intervening 1-morphism of a factorization through an étale representable
1-morphism is itself representable and étale, in the sense of Stacks 04XB at
`AlgebraicGeometry.Space.IsEtale`. -/
@[stacks 05XK "étaleness"]
theorem isEtale_algebraicSpaceMap_of_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsRepresentableByAlgebraicSpaces B S hS (f ≫ g).hom)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hEfg : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒵.val.obj)
      (_hz : z ⋙ 𝒵.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒵.val.p z
          (CatFiberedInGroupoids.homFunctor (f ≫ g)))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsEtale B S hS (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom)
    (hEg : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒵.val.obj)
      (_hz : z ⋙ 𝒵.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒴.val.p 𝒵.val.p z
          (CatFiberedInGroupoids.homFunctor g))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsEtale B S hS (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsEtale B S hS (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  classical
  intro U y hy Fk hFk hEK
  obtain ⟨EK⟩ := hEK
  set P := Space.etaleMorphisms B S hS with hP
  have hff : CatFiberedInGroupoids.homFunctor f ⋙ 𝒴.val.p = 𝒳.val.p :=
    CatFiberedInGroupoids.homFunctor_comp_p f
  have hgg : CatFiberedInGroupoids.homFunctor g ⋙ 𝒵.val.p = 𝒴.val.p :=
    CatFiberedInGroupoids.homFunctor_comp_p g
  have hz : (y ⋙ CatFiberedInGroupoids.homFunctor g) ⋙ 𝒵.val.p = Over.map U.hom := by
    rw [Functor.assoc, hgg, hy]
  obtain ⟨Fp, hFp, ⟨E⟩⟩ := hfg U (y ⋙ CatFiberedInGroupoids.homFunctor g) hz
  obtain ⟨Gq, hGq, ⟨EG⟩⟩ := hg U (y ⋙ CatFiberedInGroupoids.homFunctor g) hz
  have hΛFp := Space.isAlgebraicSpace_relocalizePresheaf B S hS U Fp hFp
  have hΛGq := Space.isAlgebraicSpace_relocalizePresheaf B S hS U Gq hGq
  have hΛFk := Space.isAlgebraicSpace_relocalizePresheaf B S hS U Fk hFk
  -- The structural morphisms of the two representing spaces over `𝒵` are étale.
  have hPG := (Space.prop_relocalizeToYoneda_iff B S hS P U Gq hGq).2
    (hEg U (y ⋙ CatFiberedInGroupoids.homFunctor g) hz Gq hGq ⟨EG⟩)
  have hPF := (Space.prop_relocalizeToYoneda_iff B S hS P U Fp hFp).2
    (hEfg U (y ⋙ CatFiberedInGroupoids.homFunctor g) hz Fp hFp ⟨E⟩)
  -- The comparison morphism of the two is étale, by Stacks 03FV.
  have hcomp : (ObjectProperty.homMk (baseChangeNatTrans U.hom
          (y ⋙ CatFiberedInGroupoids.homFunctor g) hff E EG) :
        (⟨(relocalizePresheafFunctor U.hom).obj Fp, hΛFp⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩) ≫
        (ObjectProperty.homMk (relocalizeToYoneda U.hom Gq) :
          (⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩) =
      ObjectProperty.homMk (relocalizeToYoneda U.hom Fp) :=
    ObjectProperty.hom_ext _ (baseChangeNatTrans_comp_relocalizeToYoneda U.hom
      (y ⋙ CatFiberedInGroupoids.homFunctor g) hff E EG)
  have hPα : P (ObjectProperty.homMk (baseChangeNatTrans U.hom
      (y ⋙ CatFiberedInGroupoids.homFunctor g) hff E EG) :
      (⟨(relocalizePresheafFunctor U.hom).obj Fp, hΛFp⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩) := by
    refine MorphismProperty.of_postcomp P (W' := P) _ _ hPG ?_
    rw [hcomp]
    exact hPF
  -- The canonical point of the intermediate 2-fibre product attached to `y`.
  have hw : TwoFibreProductOver.baseChangeSection (pT := Over.map U.hom) (pZ := 𝒵.val.p) y
        (CatFiberedInGroupoids.homFunctor g) hy hgg ⋙
      TwoFibreProductOver.structureFunctor (Over.map U.hom) 𝒴.val.p 𝒵.val.p
        (y ⋙ CatFiberedInGroupoids.homFunctor g) (CatFiberedInGroupoids.homFunctor g) =
      Over.map U.hom := by
    rw [← TwoFibreProductOver.fst_comp_eq, ← Functor.assoc,
      TwoFibreProductOver.baseChangeSection_comp_fst, Functor.id_comp]
  obtain ⟨fib, c, β, hc, ⟨Efib⟩⟩ := exists_section_isPullback_baseChangeNatTrans_of_point U.hom
    (y ⋙ CatFiberedInGroupoids.homFunctor g) hff E EG hgg hz
    𝒳.property 𝒴.property 𝒵.property U.hom _ hw
  -- That presheaf represents the base change along `y` itself, so it is `Fk` up to isomorphism.
  have hfibAlg : IsAlgebraicSpace B U.left.1 U.left.2 fib :=
    isAlgebraicSpace_of_iso B U.left.1 U.left.2 (isoOfEquivalenceOver Efib EK) hFk
  have hΛfib := Space.isAlgebraicSpace_relocalizePresheaf B S hS U fib hfibAlg
  have hsq : IsPullback
      (ObjectProperty.homMk c :
        (⟨(relocalizePresheafFunctor U.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨(relocalizePresheafFunctor U.hom).obj Fp, hΛFp⟩)
      (ObjectProperty.homMk (relocalizeToYoneda U.hom fib) :
        (⟨(relocalizePresheafFunctor U.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩)
      (ObjectProperty.homMk (baseChangeNatTrans U.hom
          (y ⋙ CatFiberedInGroupoids.homFunctor g) hff E EG) :
        (⟨(relocalizePresheafFunctor U.hom).obj Fp, hΛFp⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩)
      (ObjectProperty.homMk β :
        (⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩ :
            AlgebraicSpaces B S hS) ⟶
          ⟨(relocalizePresheafFunctor U.hom).obj Gq, hΛGq⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hc
  have hPfib : P (ObjectProperty.homMk (relocalizeToYoneda U.hom fib) :
      (⟨(relocalizePresheafFunctor U.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq hPα
  -- Transport along the isomorphism of representing presheaves, which is over `U`.
  refine (Space.prop_relocalizeToYoneda_iff B S hS P U Fk hFk).1 ?_
  have hiso : IsIso (ObjectProperty.homMk
        ((relocalizePresheafFunctor U.hom).map (isoOfEquivalenceOver Efib EK).hom) :
      (⟨(relocalizePresheafFunctor U.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨(relocalizePresheafFunctor U.hom).obj Fk, hΛFk⟩) :=
    ⟨⟨ObjectProperty.homMk
        ((relocalizePresheafFunctor U.hom).map (isoOfEquivalenceOver Efib EK).inv),
      ObjectProperty.hom_ext _ (by simp), ObjectProperty.hom_ext _ (by simp)⟩⟩
  have hfac : (ObjectProperty.homMk
        ((relocalizePresheafFunctor U.hom).map (isoOfEquivalenceOver Efib EK).hom) :
      (⟨(relocalizePresheafFunctor U.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨(relocalizePresheafFunctor U.hom).obj Fk, hΛFk⟩) ≫
        (ObjectProperty.homMk (relocalizeToYoneda U.hom Fk) :
          (⟨(relocalizePresheafFunctor U.hom).obj Fk, hΛFk⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩) =
      ObjectProperty.homMk (relocalizeToYoneda U.hom fib) :=
    ObjectProperty.hom_ext _
      (relocalizePresheafFunctor_map_comp_relocalizeToYoneda U.hom
        (isoOfEquivalenceOver Efib EK).hom)
  have key := P.cancel_left_of_respectsIso (ObjectProperty.homMk
        ((relocalizePresheafFunctor U.hom).map (isoOfEquivalenceOver Efib EK).hom) :
      (⟨(relocalizePresheafFunctor U.hom).obj fib, hΛfib⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨(relocalizePresheafFunctor U.hom).obj Fk, hΛFk⟩)
    (ObjectProperty.homMk (relocalizeToYoneda U.hom Fk) :
      (⟨(relocalizePresheafFunctor U.hom).obj Fk, hΛFk⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj (Over.mk U.hom), isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)⟩)
  rw [hfac] at key
  exact key.mp hPfib

/-- Étale permanence in the vocabulary of `AlgebraicGeometry.Stack.IsRelativelyEtale`: if `f ≫ g`
and `g` are étale in the sense of Stacks 04XB at `AlgebraicGeometry.Space.IsEtale`, then so
is `f`.

This carries no `@[stacks]` attribute, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth`: it is
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_comp` and
`AlgebraicGeometry.Stack.isEtale_algebraicSpaceMap_of_comp`, which together already carry the
tag, read at the saturated universes that `AlgebraicGeometry.Stack.IsRelativelyEtale` is pinned
at. -/
theorem isRelativelyEtale_of_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hfg : IsRelativelyEtale B S hS (f ≫ g)) (hg : IsRelativelyEtale B S hS g) :
    IsRelativelyEtale B S hS f := by
  obtain ⟨hfgr, hEfg⟩ := hfg
  obtain ⟨hgr, hEg⟩ := hg
  exact ⟨isRepresentableByAlgebraicSpaces_of_comp B S hS f g hfgr hgr,
    isEtale_algebraicSpaceMap_of_comp B S hS f g hfgr hgr hEfg hEg⟩

end AlgebraicGeometry.Stack

end
