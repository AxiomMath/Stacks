module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.EtaleLocalProperties
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.EtaleLocalPropertiesPointTest
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.SpacesImmersions
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Unramified
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.UnramifiedPointTest
public import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.HigherDiagonalMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSourceOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSeparationConverse
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Quasi-DM and DM conditions in a morphism of thickenings of algebraic stacks

Let `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` be a morphism of thickenings of algebraic stacks over `S`.
Then `f` is quasi-DM, Deligne–Mumford, or representable by algebraic spaces exactly when `f'` is.
For a thickening `𝒳 ⊂ 𝒳'` of algebraic stacks over `S`, the stack `𝒳` is DM, quasi-DM, or an
algebraic space exactly when `𝒳'` is.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_outer_of_inner_of_pointTest`: a property of
  morphisms of algebraic spaces that transfers across cartesian squares of thickenings of
  algebraic spaces with horizontal morphisms locally of finite type passes from the base change of
  a 1-morphism along a thickening of its target to the 1-morphism itself.
* `AlgebraicGeometry.Stack.hasRelativeProperty_relativeDiagonal_outer_of_inner_of_pointTest`: such
  a property passes from the relative diagonal of `f` to that of `f'`.
* `AlgebraicGeometry.Stack.hasRelativeProperty_relativeDiagonal_iff_of_pointTest`: such a property
  holds for the relative diagonal of `f` if and only if it holds for that of `f'`.
* `AlgebraicGeometry.Stack.isQuasiDM_inner_iff_outer`: `f` is quasi-DM if and only if `f'` is.
* `AlgebraicGeometry.Stack.isDM_inner_iff_outer`: `f` is DM if and only if `f'` is.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_relativeDiagonal_inner_iff_outer`: the
  relative diagonal of `f` is a monomorphism if and only if that of `f'` is.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_inner_iff_outer`: `f` is representable
  by algebraic spaces if and only if `f'` is.
* `AlgebraicGeometry.Stack.isDMOver_iff_isThickening` and
  `AlgebraicGeometry.Stack.isQuasiDMOver_iff_isThickening`: `𝒳` is DM, respectively quasi-DM,
  over `S` if and only if `𝒳'` is.
* `AlgebraicGeometry.Stack.isDMAbs_iff_isThickening` and
  `AlgebraicGeometry.Stack.isQuasiDMAbs_iff_isThickening`: `𝒳` is DM, respectively quasi-DM, if
  and only if `𝒳'` is.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_iff_isThickening`: `𝒳` is an algebraic
  space if and only if `𝒳'` is.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 042D](https://stacks.math.columbia.edu/tag/042D)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 04ZW](https://stacks.math.columbia.edu/tag/04ZW)
* [Stacks Project, Tag 04X6](https://stacks.math.columbia.edu/tag/04X6)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 0AHJ](https://stacks.math.columbia.edu/tag/0AHJ)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
* [Stacks Project, Tag 0BPU](https://stacks.math.columbia.edu/tag/0BPU)
* [Stacks Project, Tag 0BPV](https://stacks.math.columbia.edu/tag/0BPV)
* [Stacks Project, Tag 0BPW](https://stacks.math.columbia.edu/tag/0BPW)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
* [Stacks Project, Tag 0CJC](https://stacks.math.columbia.edu/tag/0CJC)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section PointTest

variable {𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

/-- Let `k : 𝒴 ⟶ 𝒴'` be a thickening of algebraic stacks over `S`, let `f' : 𝒳' ⟶ 𝒴'` be a
1-morphism and let `sq` be a 2-cartesian square over the cospan `(k, f')`, with `sq.fst` and `f'`
representable by algebraic spaces and locally of finite type. Let `P` be a property of morphisms
of algebraic spaces over `S`, stable under base change and fppf local on the target, such that
`P` passes from `p` to `p'` in every cartesian square of thickenings of algebraic spaces over `S`
whose horizontal morphisms `p` and `p'` are locally of finite type. If `sq.fst` has `P`, then so
does `f'`. -/
theorem hasRelativeProperty_outer_of_inner_of_pointTest
    {k : 𝒴 ⟶ 𝒴'} {f' : 𝒳' ⟶ 𝒴'}
    (sq : Bicategory.TwoCommSq k f') (hsq : Bicategory.IsTwoFibreProduct sq)
    (hk : IsThickening k)
    (hrepInner : IsRepresentableByAlgebraicSpaces B S hS sq.fst.hom.hom)
    (hrepOuter : IsRepresentableByAlgebraicSpaces B S hS f'.hom.hom)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hpointTest : ∀ {A A' C C' : AlgebraicSpaces B S hS} {a : A ⟶ A'} {b : C ⟶ C'}
      {p : A ⟶ C} {p' : A' ⟶ C'}, Space.IsThickeningHom B S hS a →
      Space.IsThickeningHom B S hS b → IsPullback p a b p' →
      Space.locallyOfFiniteTypeProperty B S hS p →
      Space.locallyOfFiniteTypeProperty B S hS p' → P p → P p')
    (hftInner :
      letI : (Space.locallyOfFiniteTypeProperty B S hS).IsLocalAtTarget
          (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
        (Space.locallyOfFiniteType_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
          (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
      HasRelativeProperty.{u, u, u + 1, u} B S hS
        (Space.locallyOfFiniteTypeProperty B S hS) sq.fst.hom hrepInner)
    (hftOuter :
      letI : (Space.locallyOfFiniteTypeProperty B S hS).IsLocalAtTarget
          (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
        (Space.locallyOfFiniteType_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
          (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
      HasRelativeProperty.{u, u, u + 1, u} B S hS
        (Space.locallyOfFiniteTypeProperty B S hS) f'.hom hrepOuter)
    (h : HasRelativeProperty.{u, u, u + 1, u} B S hS P sq.fst.hom hrepInner) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P f'.hom hrepOuter := by
  let : (Space.locallyOfFiniteTypeProperty B S hS).IsStableUnderBaseChange :=
    Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS
  let : (Space.locallyOfFiniteTypeProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    (Space.locallyOfFiniteType_isLocalAtTarget_fpqc.{u, u} B S hS).of_le
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have hft : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.locallyOfFiniteTypeProperty B S hS) sq.fst.hom hrepInner := hftInner
  have hft' : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.locallyOfFiniteTypeProperty B S hS) f'.hom hrepOuter := hftOuter
  have hD : Bicategory.IsTwoFibreProduct
      (AlgebraicStacks.toCatFiberedInGroupoids B S hS sq) :=
    AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS _ hsq
  have hK : IsRelativeThickening B S hS k.hom :=
    isRelativeThickening_of_isThickening B S hS hk
  rw [hasRelativeProperty_iff_forall_space_baseChange B S hS P f'.hom hrepOuter]
  rw [hasRelativeProperty_iff_forall_space_baseChange B S hS P sq.fst.hom hrepInner] at h
  rw [hasRelativeProperty_iff_forall_space_baseChange B S hS
    (Space.locallyOfFiniteTypeProperty B S hS) sq.fst.hom hrepInner] at hft
  rw [hasRelativeProperty_iff_forall_space_baseChange B S hS
    (Space.locallyOfFiniteTypeProperty B S hS) f'.hom hrepOuter] at hft'
  intro 𝒵 h𝒵 g Q hQ F G hF hG eF eG
  set R := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g
    k.hom with hRdef
  have hR : Bicategory.IsTwoFibreProduct R :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  have hRthick : IsRelativeThickening B S hS R.fst :=
    isRelativeThickening_baseChange B S hS _ g hK R hR
  have hRrep : IsRepresentableByAlgebraicSpace B S hS R.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u} B S hS _ _ _
      k.hom g R hR hK.1 h𝒵
  obtain ⟨Gv, hGv, ⟨eGv⟩⟩ := hRrep
  have hRrep : IsRepresentableByAlgebraicSpace B S hS R.pt := ⟨Gv, hGv, ⟨eGv⟩⟩
  have hciRel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.closedImmersionProperty B S hS) R.fst hRthick.1 :=
    (isClosedImmersion_iff_hasRelativeProperty.{u, u} B S hS R.fst hRthick.1).1 hRthick.2.1
  have hgvCI := prop_representingMap_of_hasRelativeProperty B S hS
    (Space.closedImmersionProperty B S hS) R.fst hRthick.1 hciRel 𝒵 (𝟙 𝒵)
    (Bicategory.TwoCommSq.idCospan R.fst) (Bicategory.isTwoFibreProduct_idCospan R.fst)
    Gv G hGv hG eGv eG
  have hgvSurj := prop_representingMap_of_hasRelativeProperty B S hS
    (Space.surjectiveMorphismProperty B S hS) R.fst hRthick.1 (hRthick.2.2 hRthick.1) 𝒵 (𝟙 𝒵)
    (Bicategory.TwoCommSq.idCospan R.fst) (Bicategory.isTwoFibreProduct_idCospan R.fst)
    Gv G hGv hG eGv eG
  have hgvThick : Space.IsThickeningHom B S hS
      (ObjectProperty.homMk (representingMap B S hS R.pt 𝒵 Gv G eGv eG R.fst) :
        (⟨Gv, hGv⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) :=
    (Space.isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS _).2 ⟨hgvCI, hgvSurj⟩
  set V := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} R.snd
    sq.fst.hom with hVdef
  have hV : Bicategory.IsTwoFibreProduct V :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  have hVrep : IsRepresentableByAlgebraicSpace B S hS V.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u} B S hS _ _ _
      sq.fst.hom R.snd V hV hrepInner hRrep
  obtain ⟨Fv, hFv, ⟨eFv⟩⟩ := hVrep
  have hPin := h R.pt hRrep R.snd V hV Fv Gv hFv hGv eFv eGv
  have hQfst : IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _
      f'.hom g Q hQ hrepOuter
  set W := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} R.fst Q.fst
    with hWdef
  have hW : Bicategory.IsTwoFibreProduct W :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _
  have hWrep : IsRepresentableByAlgebraicSpace B S hS W.pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u} B S hS _ _ _
      Q.fst R.fst W hW hQfst hRrep
  obtain ⟨Fw, hFw, ⟨eFw⟩⟩ := hWrep
  have hpb : IsPullback
      (representingMap B S hS W.pt R.pt Fw Gv eFw eGv W.fst)
      (representingMap B S hS W.pt Q.pt Fw F eFw eF W.snd)
      (representingMap B S hS R.pt 𝒵 Gv G eGv eG R.fst)
      (representingMap B S hS Q.pt 𝒵 F G eF eG Q.fst) :=
    isPullback_representingMap_of_isTwoFibreProduct B S hS hW Gv F G Fw Fw
      eGv eF eG eFw eFw
  have hWthick : IsRelativeThickening B S hS W.snd :=
    isRelativeThickening_baseChange B S hS R.fst Q.fst hRthick W.swap
      (Bicategory.isTwoFibreProduct_swap hW)
  have hiwCI := prop_representingMap_of_hasRelativeProperty B S hS
    (Space.closedImmersionProperty B S hS) W.snd hWthick.1
    ((isClosedImmersion_iff_hasRelativeProperty.{u, u} B S hS W.snd hWthick.1).1 hWthick.2.1)
    Q.pt (𝟙 Q.pt) (Bicategory.TwoCommSq.idCospan W.snd)
    (Bicategory.isTwoFibreProduct_idCospan W.snd) Fw F hFw hF eFw eF
  have hiwSurj := prop_representingMap_of_hasRelativeProperty B S hS
    (Space.surjectiveMorphismProperty B S hS) W.snd hWthick.1 (hWthick.2.2 hWthick.1)
    Q.pt (𝟙 Q.pt) (Bicategory.TwoCommSq.idCospan W.snd)
    (Bicategory.isTwoFibreProduct_idCospan W.snd) Fw F hFw hF eFw eF
  have hiwThick : Space.IsThickeningHom B S hS
      (ObjectProperty.homMk (representingMap B S hS W.pt Q.pt Fw F eFw eF W.snd) :
        (⟨Fw, hFw⟩ : AlgebraicSpaces B S hS) ⟶ (⟨F, hF⟩ : AlgebraicSpaces B S hS)) :=
    (Space.isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS _).2 ⟨hiwCI, hiwSurj⟩
  have hRbig : Bicategory.IsTwoFibreProduct
      (((AlgebraicStacks.toCatFiberedInGroupoids B S hS
        sq).pasteFst V).reindexFst R.iso.symm) :=
    Bicategory.isTwoFibreProduct_reindexFst R.iso.symm
      (Bicategory.isTwoFibreProduct_pasteFst _ hD V hV)
  have hWbig : Bicategory.IsTwoFibreProduct (Q.pasteFst W) :=
    Bicategory.isTwoFibreProduct_pasteFst Q hQ W hW
  set A := Bicategory.twoFibreProductPreHom hWbig
    (((AlgebraicStacks.toCatFiberedInGroupoids B S hS
      sq).pasteFst V).reindexFst R.iso.symm) with hAdef
  set A' := Bicategory.twoFibreProductPreHom hRbig (Q.pasteFst W) with hA'def
  obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProductPreHom_rel hRbig (A.comp A')
    (Bicategory.TwoCommSq.PreHom.id _)
  obtain ⟨θ', -, -⟩ := Bicategory.twoFibreProductPreHom_rel hWbig (A'.comp A)
    (Bicategory.TwoCommSq.PreHom.id _)
  have hinv1 : representingMap B S hS V.pt W.pt Fv Fw eFv eFw A.hom ≫
      representingMap B S hS W.pt V.pt Fw Fv eFw eFv A'.hom = 𝟙 Fv :=
    (representingMap_comp B S hS Fv Fw Fv eFv eFw eFv A.hom A'.hom).symm.trans
      ((representingMap_congr_twoIso B S hS Fv Fv eFv eFv θ).trans
        (representingMap_id B S hS _ Fv eFv))
  have hinv2 : representingMap B S hS W.pt V.pt Fw Fv eFw eFv A'.hom ≫
      representingMap B S hS V.pt W.pt Fv Fw eFv eFw A.hom = 𝟙 Fw :=
    (representingMap_comp B S hS Fw Fv Fw eFw eFv eFw A'.hom A.hom).symm.trans
      ((representingMap_congr_twoIso B S hS Fw Fw eFw eFw θ').trans
        (representingMap_id B S hS _ Fw eFw))
  have hfst := (representingMap_congr_twoIso B S hS Fv Gv eFv eGv A.isoFst).trans
    (representingMap_comp B S hS Fv Fw Gv eFv eFw eGv A.hom (Q.pasteFst W).fst)
  have hiso : IsIso (ObjectProperty.homMk
      (representingMap B S hS V.pt W.pt Fv Fw eFv eFw A.hom) :
        (⟨Fv, hFv⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Fw, hFw⟩ : AlgebraicSpaces B S hS)) :=
    ⟨ObjectProperty.homMk (representingMap B S hS W.pt V.pt Fw Fv eFw eFv A'.hom),
      ObjectProperty.hom_ext _ hinv1, ObjectProperty.hom_ext _ hinv2⟩
  have hfst' : (ObjectProperty.homMk (representingMap B S hS V.pt R.pt Fv Gv eFv eGv V.fst) :
        (⟨Fv, hFv⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Gv, hGv⟩ : AlgebraicSpaces B S hS)) =
      (ObjectProperty.homMk (representingMap B S hS V.pt W.pt Fv Fw eFv eFw A.hom) :
          (⟨Fv, hFv⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Fw, hFw⟩ : AlgebraicSpaces B S hS)) ≫
        (ObjectProperty.homMk (representingMap B S hS W.pt R.pt Fw Gv eFw eGv W.fst) :
          (⟨Fw, hFw⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Gv, hGv⟩ : AlgebraicSpaces B S hS)) :=
    ObjectProperty.hom_ext _ hfst
  have hri : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso (P := P)
  have hriLft : (Space.locallyOfFiniteTypeProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := Space.locallyOfFiniteTypeProperty B S hS)
  have hLftIn := hft R.pt hRrep R.snd V hV Fv Gv hFv hGv eFv eGv
  rw [hfst'] at hPin hLftIn
  have hPfw := (P.cancel_left_of_respectsIso _ _).mp hPin
  have hLftFw := ((Space.locallyOfFiniteTypeProperty B S hS).cancel_left_of_respectsIso
    _ _).mp hLftIn
  have hLftFo := hft' 𝒵 h𝒵 g Q hQ F G hF hG eF eG
  have hpb' : IsPullback
      (ObjectProperty.homMk (representingMap B S hS W.pt R.pt Fw Gv eFw eGv W.fst) :
        (⟨Fw, hFw⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Gv, hGv⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (representingMap B S hS W.pt Q.pt Fw F eFw eF W.snd) :
        (⟨Fw, hFw⟩ : AlgebraicSpaces B S hS) ⟶ (⟨F, hF⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (representingMap B S hS R.pt 𝒵 Gv G eGv eG R.fst) :
        (⟨Gv, hGv⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS))
      (ObjectProperty.homMk (representingMap B S hS Q.pt 𝒵 F G eF eG Q.fst) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι
        (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u ↦ IsAlgebraicSpace B S hS F)) hpb
  exact hpointTest hiwThick hgvThick hpb' hLftFw hLftFo hPfw

end PointTest

section Diagonal

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}
  (m : ThickeningMorphism i j hi hj)

/-- Let `m` be a morphism of thickenings of algebraic stacks over `S` and let `P` be a property of
morphisms of algebraic spaces over `S`, stable under base change and fppf local on the target,
such that `P` passes from `f` to `f'` in every cartesian square of thickenings of algebraic spaces
over `S` whose horizontal morphisms `f` and `f'` are locally of finite type. If the relative
diagonal of `m.inner` has `P`, then so does the relative diagonal of `m.outer`. -/
theorem hasRelativeProperty_relativeDiagonal_outer_of_inner_of_pointTest
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hpointTest : ∀ {A A' C C' : AlgebraicSpaces B S hS} {a : A ⟶ A'} {b : C ⟶ C'}
      {f : A ⟶ C} {f' : A' ⟶ C'}, Space.IsThickeningHom B S hS a →
      Space.IsThickeningHom B S hS b → IsPullback f a b f' →
      Space.locallyOfFiniteTypeProperty B S hS f →
      Space.locallyOfFiniteTypeProperty B S hS f' → P f → P f')
    (h : HasRelativeProperty.{u, u, u + 1, u} B S hS P
      (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner)) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P
      (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer) :=
  hasRelativeProperty_outer_of_inner_of_pointTest B S hS
    (selfProductDiagonalSquare B S hS m) (isTwoFibreProduct_selfProductDiagonalSquare B S hS m)
    (isThickening_selfProductDiagonalMap B S hS m)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer)
    P hpointTest
    (isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack B S hS m.inner).choose_spec
    (isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack B S hS m.outer).choose_spec h

/-- Let `m` be a morphism of thickenings of algebraic stacks over `S` and let `P` be a property of
morphisms of algebraic spaces over `S`, stable under base change and fppf local on the target,
such that `P` passes from `f` to `f'` in every cartesian square of thickenings of algebraic spaces
over `S` whose horizontal morphisms `f` and `f'` are locally of finite type. Then the relative
diagonal of `m.inner` has `P` if and only if the relative diagonal of `m.outer` has `P`. -/
theorem hasRelativeProperty_relativeDiagonal_iff_of_pointTest
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hpointTest : ∀ {A A' C C' : AlgebraicSpaces B S hS} {a : A ⟶ A'} {b : C ⟶ C'}
      {f : A ⟶ C} {f' : A' ⟶ C'}, Space.IsThickeningHom B S hS a →
      Space.IsThickeningHom B S hS b → IsPullback f a b f' →
      Space.locallyOfFiniteTypeProperty B S hS f →
      Space.locallyOfFiniteTypeProperty B S hS f' → P f → P f') :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P
        (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.inner) ↔
      HasRelativeProperty.{u, u, u + 1, u} B S hS P
        (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom
        (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS m.outer) :=
  ⟨hasRelativeProperty_relativeDiagonal_outer_of_inner_of_pointTest B S hS m P hpointTest,
    hasRelativeProperty_relativeDiagonal_inner_of_outer B S hS m P⟩

/-! ### Quasi-DM and DM morphisms -/

/-- In a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`,
the 1-morphism `f` is quasi-DM if and only if `f'` is quasi-DM. -/
@[stacks 0CJ9 "item (8): quasi-DM"]
theorem isQuasiDM_inner_iff_outer :
    AlgebraicStacks.IsQuasiDM B S hS m.inner ↔ AlgebraicStacks.IsQuasiDM B S hS m.outer := by
  let : (Space.locallyQuasiFiniteProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isLocallyQuasiFinite_isLocalAtTarget_fppf.{u, u} B S hS
  exact hasRelativeProperty_relativeDiagonal_iff_of_pointTest B S hS m
    (Space.locallyQuasiFiniteProperty B S hS)
    fun ha hb hsq hlft hlft' ↦
      (Space.locallyQuasiFiniteProperty_iff_of_cartesianSquareOfThickeningHoms
        B S hS ha hb hsq hlft hlft').1

/-- In a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`,
the 1-morphism `f` is Deligne–Mumford if and only if `f'` is Deligne–Mumford. -/
@[stacks 0CJ9 "item (9): DM"]
theorem isDM_inner_iff_outer : IsDM B S hS m.inner ↔ IsDM B S hS m.outer := by
  let : (Space.unramifiedMorphismProperty B S hS).IsStableUnderBaseChange :=
    Space.isUnramified_isStableUnderBaseChange B S hS
  let : (Space.unramifiedMorphismProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le
      (L := Space.Topology.fpqc.precoverage.{u, u} B S hS)
      (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have key := hasRelativeProperty_relativeDiagonal_iff_of_pointTest B S hS m
    (Space.unramifiedMorphismProperty B S hS)
    fun ha hb hsq hlft hlft' ↦
      (Space.unramifiedMorphismProperty_iff_of_cartesianSquareOfThickeningHoms
        B S hS ha hb hsq hlft hlft').1
  exact ⟨fun hin ↦ ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS
      m.outer, key.1 hin.choose_spec⟩,
    fun hout ↦ ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS
      m.inner, key.2 hout.choose_spec⟩⟩

/-! ### Representability by algebraic spaces -/

/-- In a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`,
the relative diagonal of `f` is a monomorphism if and only if the relative diagonal of `f'` is a
monomorphism. -/
theorem AlgebraicStacks.isMonomorphism_relativeDiagonal_inner_iff_outer :
    AlgebraicStacks.IsMonomorphism B S hS
        (relativeDiagonalAlgebraicStacks B S hS m.inner) ↔
      AlgebraicStacks.IsMonomorphism B S hS
        (relativeDiagonalAlgebraicStacks B S hS m.outer) := by
  have key := hasRelativeProperty_relativeDiagonal_iff_of_pointTest B S hS m
    (MorphismProperty.monomorphisms (AlgebraicSpaces B S hS))
    fun ha hb hsq hlft hlft' hmono ↦
      (Space.mono_iff_of_cartesianSquareOfThickeningHoms B S hS ha hb hsq hlft hlft').1 hmono
  exact ⟨fun hin ↦ ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS
      m.outer, key.1 hin.2⟩,
    fun hout ↦ ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS
      m.inner, key.2 hout.2⟩⟩

/-- In a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`,
the 1-morphism `f` is representable by algebraic spaces if and only if `f'` is. -/
@[stacks 0CJ9 "item (12): representable by algebraic spaces"]
theorem isRepresentableByAlgebraicSpaces_inner_iff_outer :
    IsRepresentableByAlgebraicSpaces B S hS m.inner.hom.hom ↔
      IsRepresentableByAlgebraicSpaces B S hS m.outer.hom.hom :=
  (AlgebraicStacks.isRepresentableByAlgebraicSpaces_iff_isMonomorphism_relativeDiagonal
      B S hS m.inner).trans
    ((AlgebraicStacks.isMonomorphism_relativeDiagonal_inner_iff_outer B S hS m).trans
      (AlgebraicStacks.isRepresentableByAlgebraicSpaces_iff_isMonomorphism_relativeDiagonal
        B S hS m.outer).symm)

end Diagonal

/-! ### Thickenings of algebraic stacks -/

section Thickening

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks over `S`, then `𝒳` is DM over `S` if and only
if `𝒳'` is DM over `S`. -/
@[stacks 0BPW "clause (3): DM over the base"]
theorem isDMOver_iff_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    IsDMOver B S hS 𝒳 ↔ IsDMOver B S hS 𝒳' :=
  isDM_inner_iff_outer B S hS (structureThickeningMorphism B S hS i hi)

/-- If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks over `S`, then `𝒳` is quasi-DM over `S` if
and only if `𝒳'` is quasi-DM over `S`. -/
@[stacks 0BPW "clause (4): quasi-DM over the base"]
theorem isQuasiDMOver_iff_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    IsQuasiDMOver B S hS 𝒳 ↔ IsQuasiDMOver B S hS 𝒳' :=
  isQuasiDM_inner_iff_outer B S hS (structureThickeningMorphism B S hS i hi)

universe w'

/-- If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks over `S`, then `𝒳` is Deligne–Mumford if and
only if `𝒳'` is Deligne–Mumford, in the absolute sense of `AlgebraicGeometry.Stack.IsDMAbs`. -/
@[stacks 0BPW "clause (3): DM, the absolute axiom of Stacks 050D part (5)"]
theorem isDMAbs_iff_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    IsDMAbs.{u, w, w'} B S hS 𝒳 ↔ IsDMAbs.{u, w, w'} B S hS 𝒳' :=
  (isDMAbs_iff_isDMOver.{u, w, w'} B S hS 𝒳).trans
    ((isDMOver_iff_isThickening B S hS i hi).trans
      (isDMAbs_iff_isDMOver.{u, w, w'} B S hS 𝒳').symm)

/-- If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks over `S`, then `𝒳` is quasi-DM if and only
if `𝒳'` is quasi-DM, in the absolute sense of `AlgebraicGeometry.Stack.IsQuasiDMAbs`. -/
@[stacks 0BPW "clause (4): quasi-DM, the absolute axiom of Stacks 050D part (6)"]
theorem isQuasiDMAbs_iff_isThickening (i : 𝒳 ⟶ 𝒳') (hi : IsThickening i) :
    IsQuasiDMAbs.{u, w, w'} B S hS 𝒳 ↔ IsQuasiDMAbs.{u, w, w'} B S hS 𝒳' :=
  (isQuasiDMAbs_iff_isQuasiDMOver.{u, w, w'} B S hS 𝒳).trans
    ((isQuasiDMOver_iff_isThickening B S hS i hi).trans
      (isQuasiDMAbs_iff_isQuasiDMOver.{u, w, w'} B S hS 𝒳').symm)

/-- If `𝒳 ⊂ 𝒳'` is a thickening of algebraic stacks over `S`, then `𝒳` is an algebraic space if
and only if `𝒳'` is an algebraic space. -/
@[stacks 0BPW "clause (1): algebraic space, the whole equivalence"]
theorem isRepresentableByAlgebraicSpace_iff_isThickening (i : 𝒳 ⟶ 𝒳')
    (hi : IsThickening i) :
    IsRepresentableByAlgebraicSpace B S hS 𝒳.val ↔
      IsRepresentableByAlgebraicSpace B S hS 𝒳'.val := by
  refine ⟨fun h ↦ ?_, isRepresentableByAlgebraicSpace_of_isThickening B S hS i hi⟩
  have hinner : IsRepresentableByAlgebraicSpaces B S hS
      (structureThickeningMorphism B S hS i hi).inner.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS
      (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))) h
      (structureThickeningMorphism B S hS i hi).inner.hom
  have houter := (isRepresentableByAlgebraicSpaces_inner_iff_outer B S hS
    (structureThickeningMorphism B S hS i hi)).1 hinner
  exact isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u} B S hS
    𝒳'.val (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
    (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
    (structureMorphism B S hS 𝒳').hom (𝟙 _)
    (Bicategory.TwoCommSq.idCospan (structureMorphism B S hS 𝒳').hom)
    (Bicategory.isTwoFibreProduct_idCospan _) houter
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS _)

end Thickening

end AlgebraicGeometry.Stack

end
