module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartComparisonAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSliceFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeHomRepresentableAffineTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictionOfScalarsSectionSpaceBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceChartSurjectiveEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsFiniteLocallyFree

/-!
# Stacks 05XR for the fibre data of Stacks 05YD and 05Y5

Let `S` be a scheme contained in a big fppf site, let `z : Z ⟶ Q` be a finite locally free
morphism of algebraic spaces over `S` and let `g : X' ⟶ X` be an étale morphism of algebraic
spaces over `S`. The proofs of Stacks 05YD and Stacks 05Y5 compute the fibre of the morphism they
are about, at a scheme-valued point of its target, as a restriction of scalars
`Res_{Z_U/U}(W) ⟶ U` for fibre data

```text
  W = Z_U ×_{b, X} X'  ⟶  Z_U = U ×_{a, Q} Z  ⟶  U
```

over an object `U` of the site. That this restriction of scalars is an algebraic space étale over
`U` is the assertion of Stacks 05XR, recorded as
`AlgebraicGeometry.Space.IsFibreSectionsAlgebraicEtale`, and this file proves it.

## The two recognitions

Stacks 05XR is proved, with no separatedness, as
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isEtale` and
`AlgebraicGeometry.Space.isEtale_sectionSpace_of_isEtale`, for a space of sections formed on the
big fppf site of a *base scheme*; and
`AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_relocalize` and
`AlgebraicGeometry.Space.isEtale_projection_restrictionOfScalars_relocalize` carry that over to a
restriction of scalars, but only for fibre data of the special shape produced by the lower-shriek
relocalization `Λ` along the structural morphism of `U`. What this file supplies is that arbitrary
fibre data has that shape.

* `Z_U` **is represented by an object of the site over `U`.** Affineness of `z`, the first
  conjunct of Stacks 03ZV, makes `z` relatively representable
  (`AlgebraicGeometry.Space.relativelyRepresentable_of_isAffineHom`), so the base change of `z`
  along `a` is `h_{Z'}` for an object `Z'` of the site with a structural morphism to `U`; the
  underlying morphism of schemes is finite by Stacks 03ZU, through
  `AlgebraicGeometry.Space.isFinite_of_isPullback_of_isFiniteLocallyFree`. Reading that structural
  morphism as an object `Z₀` of the site over the scheme underlying `U` is
  `AlgebraicGeometry.relocalizeBaseHom`.
* `W` **is `Λ` of a presheaf on the site over the scheme underlying `U`.** A presheaf over `h_U`
  is `Λ` of the fibre of its own structural morphism over the tautological section, which is the
  essential surjectivity half of the presheaf level form of Stacks 00Y1; the statement used is
  `AlgebraicGeometry.Space.relocalizeToYoneda_fibreOfSection_eq`, a cartesian square of
  `CategoryTheory.OverShriek.isPullback_relocalizeFibreOfSectionMap` whose right-hand leg is an
  identity.

The morphism `W ⟶ h_{Z_U}` of the recognized data is `Λ` of a morphism
`w₀ : W₀ ⟶ h_{Z₀}` over the scheme underlying `U`
(`AlgebraicGeometry.Space.relocalizedFibreTotalHom`): a section of `W₀` over `V` is a section of
`W` over `Λ V` lying over the tautological morphism `V ⟶ U`, and its image in `Z_U = h_{Z'}` is
then a morphism of the site over `U`, not merely over `S`. Étaleness of `w₀` is étaleness of
`Λ w₀` by `AlgebraicGeometry.presheaf_relocalizeChart_iff`
(`AlgebraicGeometry.Space.isEtale_of_isEtale_relocalizePresheafFunctor_map`), and algebraicity of
`W₀` is algebraicity of `Λ W₀` by Stacks 04SG
(`AlgebraicGeometry.isAlgebraicSpace_viewOver_iff`).

Transporting a restriction of scalars across an isomorphism of its data is
`AlgebraicGeometry.Space.restrictionOfScalars_iso_of_iso_data`: it is Stacks 05YC, the base change
of a restriction of scalars, read at the identity of the base.

## Main results

* `AlgebraicGeometry.Space.isFibreSectionsAlgebraicEtale`: **Stacks 05XR for the fibre data.**
* `isRepresentableByAlgebraicSpaces_restrictionOfScalarsMap_of_isFiniteLocallyFree`
  and `AlgebraicGeometry.Space.hasProperty_isEtale_restrictionOfScalarsMap_of_isFiniteLocallyFree`:
  **Stacks 05YD**, first and second conclusions, at the hypotheses of the source.
* `isRepresentableByAlgebraicSpaces_relativeHomPostcompose_of_isFiniteLocallyFree`
  and
  `AlgebraicGeometry.Space.hasProperty_isEtale_relativeHomPostcompose_of_isFiniteLocallyFree`:
  **Stacks 05Y5**, first and second conclusions, at the hypotheses of the source.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree_of_representable`
  and
  `isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree_of_representable`:
  **Stacks 05Y7** and **Stacks 05YF** with the input from Stacks 05XR gone, so that the only
  hypothesis besides the source's is the case of a target representable by an object of the site.

## References

* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03ZU](https://stacks.math.columbia.edu/tag/03ZU)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05Y5](https://stacks.math.columbia.edu/tag/05Y5)
* [Stacks Project, Tag 05Y7](https://stacks.math.columbia.edu/tag/05Y7)
* [Stacks Project, Tag 05YC](https://stacks.math.columbia.edu/tag/05YC)
* [Stacks Project, Tag 05YD](https://stacks.math.columbia.edu/tag/05YD)
* [Stacks Project, Tag 05YF](https://stacks.math.columbia.edu/tag/05YF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] etale_scheme_respectsIso

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Étaleness descends along the lower-shriek extension -/

/-- **Étaleness of a morphism of presheaves is reflected by the lower-shriek extension.** If
`Λ_h k` is étale then so is `k`. -/
theorem isEtale_of_isEtale_relocalizePresheafFunctor_map (V : Scheme.{u}) (hV : B.Contains V)
    (h : B.obj hV ⟶ B.obj hS) {F G : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u} (k : F ⟶ G)
    (hk : IsEtale B S hS ((OverShriek.relocalizePresheafFunctor h).map k)) :
    IsEtale B V hV k := by
  intro T φ hφ
  refine (presheaf_relocalizeChart_iff B V S hV hS h
    (@_root_.AlgebraicGeometry.Etale.{u}) (φ ≫ k)).1 ?_
  rw [← relocalizeChart_comp B V S hV hS h φ k]
  exact hk _ _ ((presheaf_relocalizeChart_iff B V S hV hS h
    (@_root_.AlgebraicGeometry.Etale.{u}) φ).2 hφ)

/-! ### Transporting a restriction of scalars across an isomorphism of its data -/

variable {B S hS}

/-- **A restriction of scalars only depends on its data up to isomorphism.** If `z' : Z' ⟶ Q` and
`x' : X' ⟶ Z'` are carried to `z : Z ⟶ Q` and `x : X ⟶ Z` by isomorphisms `Z' ≅ Z` and `X' ≅ X`
over `Q`, then `Res_{Z'/Q}(X')` and `Res_{Z/Q}(X)` are isomorphic over `Q`. -/
theorem restrictionOfScalars_iso_of_iso_data {X X' Z Z' Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} {x' : X' ⟶ Z'} {z' : Z' ⟶ Q} (eZ : Z'.obj ≅ Z.obj) (eX : X'.obj ≅ X.obj)
    (hz : z'.hom = eZ.hom ≫ z.hom) (hx : x'.hom ≫ eZ.hom = eX.hom ≫ x.hom)
    (r : RestrictionOfScalarsConstruction B S hS x z)
    (r' : RestrictionOfScalarsConstruction B S hS x' z') :
    ∃ i : r'.presheaf ≅ r.presheaf, i.hom ≫ r.projection = r'.projection := by
  have : IsIso ((ObjectProperty.homMk eZ.hom : Z' ⟶ Z).hom) := inferInstanceAs (IsIso eZ.hom)
  have : IsIso ((ObjectProperty.homMk eX.hom : X' ⟶ X).hom) := inferInstanceAs (IsIso eX.hom)
  have : IsIso ((ObjectProperty.homMk (𝟙 Q.obj) : Q ⟶ Q).hom) :=
    inferInstanceAs (IsIso (𝟙 Q.obj))
  have hZ : IsPullback z'.hom (ObjectProperty.homMk eZ.hom : Z' ⟶ Z).hom
      (ObjectProperty.homMk (𝟙 Q.obj) : Q ⟶ Q).hom z.hom :=
    IsPullback.of_vert_isIso ⟨by
      show z'.hom ≫ 𝟙 Q.obj = eZ.hom ≫ z.hom
      rw [Category.comp_id, hz]⟩
  have hX : IsPullback x'.hom (ObjectProperty.homMk eX.hom : X' ⟶ X).hom
      (ObjectProperty.homMk eZ.hom : Z' ⟶ Z).hom x.hom :=
    IsPullback.of_vert_isIso ⟨hx⟩
  obtain ⟨i, hi, -⟩ := restrictionOfScalars_baseChange hZ hX r r'
  have hid : IsPullback r.projection (𝟙 r.presheaf)
      (ObjectProperty.homMk (𝟙 Q.obj) : Q ⟶ Q).hom r.projection :=
    IsPullback.of_id_snd
  refine ⟨i ≪≫ hid.isoPullback.symm, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hid.isoPullback_inv_fst, hi]

/-! ### Recognizing arbitrary fibre data as relocalized data -/

/-- **The morphism `W₀ ⟶ h_{Z₀}` of the recognized data.** A section of `W₀` over an object `V`
of the site of the scheme underlying `U` is a section `s` of `W` over `Λ V` whose image in `h_U`
is the tautological morphism `Λ V ⟶ U`; its image in `Z_U`, read through the identification of
`Z_U` with `h_{Λ Z₀}`, is therefore a morphism `Λ V ⟶ Λ Z₀` over `U`, that is a morphism
`V ⟶ Z₀` of the site of the scheme underlying `U`. -/
def relocalizedFibreTotalHom {U : BigFppfOver B S hS} (Z₀ : BigFppfOver B U.left.1 U.left.2)
    {FW FZ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (wh : FW ⟶ FZ) (ζh : FZ ⟶ yoneda.obj U)
    (eZ : FZ ≅ yoneda.obj (relocalizedBase B S hS U Z₀))
    (heZ : eZ.hom ≫ yoneda.map (relocalizedBaseHom B S hS U Z₀) = ζh) :
    OverShriek.fibreOfSection U.hom (wh ≫ ζh) (𝟙 (yoneda.obj U)) ⟶ yoneda.obj Z₀ where
  app V := ↾fun s =>
    Over.homMk (eZ.hom.app (op ((Over.map U.hom).obj V.unop)) (wh.app _ s.1)).left (by
      have h1 := types_congr_hom (NatTrans.congr_app heZ
        (op ((Over.map U.hom).obj V.unop))) (wh.app (op ((Over.map U.hom).obj V.unop)) s.1)
      have h2 : eZ.hom.app (op ((Over.map U.hom).obj V.unop)) (wh.app _ s.1) ≫
          relocalizedBaseHom B S hS U Z₀ =
            (wh ≫ ζh).app (op ((Over.map U.hom).obj V.unop)) s.1 := h1
      have h3 := congrArg Over.Hom.left h2
      rw [Over.comp_left, relocalizedBaseHom_left] at h3
      refine h3.trans ?_
      rw [s.2]
      rfl)
  naturality V V' g := by
    ext s
    refine Over.OverMorphism.ext ?_
    have hn := NatTrans.naturality_apply (wh ≫ eZ.hom)
      ((Over.map U.hom).map g.unop).op s.1
    have hn' : eZ.hom.app (op ((Over.map U.hom).obj V'.unop))
          (wh.app _ (FW.map ((Over.map U.hom).map g.unop).op s.1)) =
        (Over.map U.hom).map g.unop ≫
          eZ.hom.app (op ((Over.map U.hom).obj V.unop)) (wh.app _ s.1) := hn
    change (eZ.hom.app (op ((Over.map U.hom).obj V'.unop))
        (wh.app _ (FW.map ((Over.map U.hom).map g.unop).op s.1))).left = _
    rw [hn']
    rfl

/-- **The recognized morphism is the relocalization of `relocalizedFibreTotalHom`.** The
comparison `Λ (fibreOfSection …) ⟶ W` identifying the total space, followed by
`W ⟶ Z_U ≅ h_{Λ Z₀}`, is `Λ` of `AlgebraicGeometry.Space.relocalizedFibreTotalHom` read through
Stacks 03I4 part (2), that is `AlgebraicGeometry.Space.relocalizedTotalHom`. -/
theorem relocalizeFibreOfSectionMap_comp_eq_relocalizedTotalHom {U : BigFppfOver B S hS}
    (Z₀ : BigFppfOver B U.left.1 U.left.2) {FW FZ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (wh : FW ⟶ FZ) (ζh : FZ ⟶ yoneda.obj U)
    (eZ : FZ ≅ yoneda.obj (relocalizedBase B S hS U Z₀))
    (heZ : eZ.hom ≫ yoneda.map (relocalizedBaseHom B S hS U Z₀) = ζh) :
    OverShriek.relocalizeFibreOfSectionMap U.hom (wh ≫ ζh) (𝟙 (yoneda.obj U)) ≫ wh ≫ eZ.hom =
      relocalizedTotalHom B S hS U Z₀
        (OverShriek.fibreOfSection U.hom (wh ≫ ζh) (𝟙 (yoneda.obj U)))
        (relocalizedFibreTotalHom Z₀ wh ζh eZ heZ) := by
  refine NatTrans.ext (funext fun T => ConcreteCategory.hom_ext _ _ fun x => ?_)
  refine Over.OverMorphism.ext ?_
  have hx : x.1.1 ≫ U.hom = T.unop.hom := x.2
  have hmap : (OverShriek.relocalizeFibreOfSectionMap U.hom (wh ≫ ζh)
        (𝟙 (yoneda.obj U))).app T x = FW.map (OverShriek.overMapMkIso U.hom hx).hom.op x.1.2.1 :=
    OverShriek.relocalizeFibreOfSectionMap_app_apply U.hom (wh ≫ ζh) (𝟙 (yoneda.obj U)) x
  have hn := NatTrans.naturality_apply (wh ≫ eZ.hom)
    (OverShriek.overMapMkIso U.hom hx).hom.op x.1.2.1
  have hn' : eZ.hom.app T (wh.app T (FW.map (OverShriek.overMapMkIso U.hom hx).hom.op x.1.2.1)) =
      (OverShriek.overMapMkIso U.hom hx).hom ≫
        eZ.hom.app (op ((Over.map U.hom).obj (Over.mk x.1.1))) (wh.app _ x.1.2.1) := hn
  show (eZ.hom.app T (wh.app T ((OverShriek.relocalizeFibreOfSectionMap U.hom (wh ≫ ζh)
      (𝟙 (yoneda.obj U))).app T x))).left =
    ((relocalizedFibreTotalHom Z₀ wh ζh eZ heZ).app (op (Over.mk x.1.1)) x.1.2).left
  rw [hmap, hn', Over.comp_left, OverShriek.overMapMkIso_hom_left, Category.id_comp]
  rfl

/-- For fibre data whose base is identified with the relocalization of an object `Z₀` of the
site of the scheme underlying `U`, with a finite structural morphism of schemes, the restriction
of scalars is an algebraic space étale over `U`. -/
theorem isAlgebraicSpace_isEtale_restrictionOfScalars_of_relocalizedBase
    (U : BigFppfOver B S hS) (Z₀ : BigFppfOver B U.left.1 U.left.2)
    {ZU W : AlgebraicSpaces B S hS}
    (ζ : ZU ⟶ (schemeSpace U : AlgebraicSpaces B S hS))
    (w : W ⟶ ZU) (eZ : ZU.obj ≅ yoneda.obj (relocalizedBase B S hS U Z₀))
    (heZ : eZ.hom ≫ yoneda.map (relocalizedBaseHom B S hS U Z₀) = ζ.hom)
    (hw : IsEtale B S hS w.hom)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z₀.hom)) :
    IsAlgebraicSpace B S hS (restrictionOfScalars B S hS w ζ).presheaf ∧
      IsEtale B S hS (restrictionOfScalars B S hS w ζ).projection := by
  let W₀ := OverShriek.fibreOfSection U.hom (w.hom ≫ ζ.hom) (𝟙 (yoneda.obj U))
  let w₀ : W₀ ⟶ yoneda.obj Z₀ := relocalizedFibreTotalHom Z₀ w.hom ζ.hom eZ heZ
  have hpb := OverShriek.isPullback_relocalizeFibreOfSectionMap U.hom (w.hom ≫ ζ.hom)
    (𝟙 (yoneda.obj U))
  let eW : (OverShriek.relocalizePresheafFunctor U.hom).obj W₀ ≅ W.obj :=
    hpb.isoIsPullback _ _ IsPullback.of_id_fst
  have heWhom : eW.hom =
      OverShriek.relocalizeFibreOfSectionMap U.hom (w.hom ≫ ζ.hom) (𝟙 (yoneda.obj U)) := by
    simpa using hpb.isoIsPullback_hom_fst _ _ IsPullback.of_id_fst
  have htotal : eW.hom ≫ w.hom ≫ eZ.hom = relocalizedTotalHom B S hS U Z₀ W₀ w₀ := by
    rw [heWhom]
    exact relocalizeFibreOfSectionMap_comp_eq_relocalizedTotalHom Z₀ w.hom ζ.hom eZ heZ
  have hW₀ : IsAlgebraicSpace B U.left.1 U.left.2 W₀ :=
    (isAlgebraicSpace_viewOver_iff B U.left.1 S U.left.2 hS U.hom W₀).1
      (isAlgebraicSpace_of_iso B S hS eW.symm W.property)
  have hΛw₀ : IsEtale B S hS ((OverShriek.relocalizePresheafFunctor U.hom).map w₀) := by
    have h1 : IsEtale B S hS (relocalizedTotalHom B S hS U Z₀ W₀ w₀) := by
      rw [← htotal]
      exact isEtale_comp B S hS (isEtale_of_isIso B S hS eW.hom)
        (isEtale_comp B S hS hw (isEtale_of_isIso B S hS eZ.hom))
    have h2 : (OverShriek.relocalizePresheafFunctor U.hom).map w₀ =
        relocalizedTotalHom B S hS U Z₀ W₀ w₀ ≫
          ((OverShriek.relocalizeYonedaIso U.hom).app Z₀).inv := by
      rw [relocalizedTotalHom, Category.assoc]
      show _ = _ ≫ (OverShriek.relocalizeYonedaIso U.hom).hom.app Z₀ ≫
        ((OverShriek.relocalizeYonedaIso U.hom).app Z₀).inv
      rw [show (OverShriek.relocalizeYonedaIso U.hom).hom.app Z₀ =
        ((OverShriek.relocalizeYonedaIso U.hom).app Z₀).hom from rfl,
        Iso.hom_inv_id, Category.comp_id]
    rw [h2]
    exact isEtale_comp B S hS h1
      (isEtale_of_isIso B S hS ((OverShriek.relocalizeYonedaIso U.hom).app Z₀).inv)
  have hw₀ : IsEtale B U.left.1 U.left.2 w₀ :=
    isEtale_of_isEtale_relocalizePresheafFunctor_map B S hS U.left.1 U.left.2 U.hom w₀ hΛw₀
  have hss : IsAlgebraicSpace B U.left.1 U.left.2
      (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀) :=
    isAlgebraicSpace_sectionSpace_of_isEtale hW₀ hw₀ hZfin
  have hsset : IsEtale B U.left.1 U.left.2
      (terminal.from (sectionSpace B U.left.1 U.left.2 Z₀ W₀ w₀)) :=
    isEtale_sectionSpace_of_isEtale hW₀ hw₀ hZfin
  have hA := isAlgebraicSpace_restrictionOfScalars_relocalize B S hS U Z₀ W₀ w₀ hW₀ hss
  have hE := isEtale_projection_restrictionOfScalars_relocalize B S hS U Z₀ W₀ w₀ hW₀ hss hsset
  obtain ⟨i, hi⟩ := restrictionOfScalars_iso_of_iso_data (x := relocalizedTotalSpaceHom
      B S hS U Z₀ W₀ w₀ hW₀) (z := relocalizedBaseSpaceHom B S hS U Z₀) (x' := w) (z' := ζ)
    eZ (eW.symm) heZ.symm (by
      rw [Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc]
      exact htotal)
    (restrictionOfScalars B S hS (relocalizedTotalSpaceHom B S hS U Z₀ W₀ w₀ hW₀)
      (relocalizedBaseSpaceHom B S hS U Z₀))
    (restrictionOfScalars B S hS w ζ)
  refine ⟨isAlgebraicSpace_of_iso B S hS i.symm hA, ?_⟩
  rw [← hi]
  exact isEtale_comp B S hS (isEtale_of_isIso B S hS i.hom) hE

/-! ### Stacks 05XR for arbitrary fibre data -/

variable (B S hS)

/-- **Stacks 05XR for the fibre data of Stacks 05YD and Stacks 05Y5.** Let `z : Z ⟶ Q` be a
finite locally free morphism of algebraic spaces over `S`, let `U` be an object of the big fppf
category over `S`, let `Z_U` be an algebraic space exhibited as a base change `U ×_{a, Q} Z` of
`z` and let `w : W ⟶ Z_U` be an étale morphism of algebraic spaces over `S`. Then the restriction
of scalars `Res_{Z_U/U}(W)` is an algebraic space over `S` and its projection to `U` is étale. -/
@[stacks 05XR "the restriction of scalars of a base change of a finite locally free morphism \
along an étale morphism is an algebraic space étale over the base"]
theorem isAlgebraicSpace_isEtale_restrictionOfScalars_of_isPullback
    {Z Q : AlgebraicSpaces B S hS} (z : Z ⟶ Q) (hz : IsFiniteLocallyFree B S hS z)
    (U : BigFppfOver B S hS) (ZU W : AlgebraicSpaces B S hS)
    (ζ : ZU ⟶ (schemeSpace U : AlgebraicSpaces B S hS))
    (w : W ⟶ ZU) (a : yoneda.obj U ⟶ Q.obj) (ι : ZU.obj ⟶ Z.obj)
    (sq : IsPullback ζ.hom ι a z.hom) (hw : IsEtale B S hS w.hom) :
    IsAlgebraicSpace B S hS (restrictionOfScalars B S hS w ζ).presheaf ∧
      IsEtale B S hS (restrictionOfScalars B S hS w ζ).projection := by
  have hrep : yoneda.relativelyRepresentable z.hom :=
    relativelyRepresentable_of_isAffineHom B S hS z hz.1
  have hfin : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (hrep.snd a)) :=
    isFinite_of_isPullback_of_isFiniteLocallyFree B S hS z hrep hz a (hrep.fst a) (hrep.snd a)
      (hrep.isPullback a)
  let e : ZU.obj ≅ yoneda.obj (hrep.pullback a) := sq.isoIsPullback _ _ (hrep.isPullback a).flip
  have he : e.hom ≫ yoneda.map (hrep.snd a) = ζ.hom :=
    sq.isoIsPullback_hom_fst _ _ (hrep.isPullback a).flip
  let iZ := asIso (relocalizeBaseHom B U.left.1 S U.left.2 hS U.hom (Over.w (hrep.snd a)))
  refine isAlgebraicSpace_isEtale_restrictionOfScalars_of_relocalizedBase U
    (Over.mk (hrep.snd a).left) ζ w (e ≪≫ yoneda.mapIso iZ) ?_ hw hfin
  rw [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, ← yoneda.map_comp,
    show iZ.hom ≫ relocalizedBaseHom B S hS U (Over.mk (hrep.snd a).left) = hrep.snd a from
      Over.OverMorphism.ext (by
        show (relocalizeBaseHom B U.left.1 S U.left.2 hS U.hom
          (Over.w (hrep.snd a))).left ≫ (hrep.snd a).left = (hrep.snd a).left
        rw [relocalizeBaseHom_left, Category.id_comp])]
  exact he

/-- **Stacks 05XR for the fibre data of Stacks 05YD and Stacks 05Y5.** For `g : X' ⟶ X` étale
and `z : Z ⟶ Q` finite locally free, the restriction of scalars `Res_{Z_U/U}(W)` is an algebraic
space étale over `U` for every base change `Z_U = U ×_{a, Q} Z` of `z` over an object of the site
and every fibre product `W = Z_U ×_{b, X} X'` of `g`. -/
theorem isFibreSectionsAlgebraicEtale {X' X Z Q : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (z : Z ⟶ Q) : IsFibreSectionsAlgebraicEtale B S hS g z := by
  intro hg_etale hz U ZU W ζ w a ι b κ sq sq'
  have sqSpace : IsPullback (ObjectProperty.homMk κ : W ⟶ X') w g
      (ObjectProperty.homMk b : ZU ⟶ X) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) sq'.flip
  exact isAlgebraicSpace_isEtale_restrictionOfScalars_of_isPullback B S hS z hz U ZU W ζ w a ι sq
    (isEtale_of_isPullback B S hS _ w g _ sqSpace hg_etale)

/-! ### Stacks 05YD and Stacks 05Y5 at the hypotheses of the source -/

/-- **Stacks 05YD, first conclusion, at the hypotheses of the source.** Let `X' → X → Z → Q` be
morphisms of algebraic spaces over `S` with `X' → X` étale and `Z → Q` finite locally free. Then
`Res_{Z/Q}(X') → Res_{Z/Q}(X)` is representable by algebraic spaces. -/
@[stacks 05YD "representable by algebraic spaces: at the hypotheses of the source, with nothing
carried"]
theorem isRepresentableByAlgebraicSpaces_restrictionOfScalarsMap_of_isFiniteLocallyFree
    {X' X Z Q : AlgebraicSpaces B S hS} {x' : X' ⟶ Z} {x : X ⟶ Z} (g : X' ⟶ X)
    (hg : g ≫ x = x') (z : Z ⟶ Q) (hg_etale : IsEtale B S hS g.hom)
    (hz : IsFiniteLocallyFree B S hS z) :
    IsRepresentableByAlgebraicSpaces B S hS (restrictionOfScalarsMap g hg z).1 :=
  isRepresentableByAlgebraicSpaces_restrictionOfScalarsMap g hg z hg_etale hz
    (isFibreSectionsAlgebraicEtale B S hS g z)

/-- **Stacks 05YD, second conclusion, at the hypotheses of the source.** In the situation of
`isRepresentableByAlgebraicSpaces_restrictionOfScalarsMap_of_isFiniteLocallyFree`,
the morphism `Res_{Z/Q}(X') → Res_{Z/Q}(X)` is étale. -/
@[stacks 05YD "étale: at the hypotheses of the source, with nothing carried"]
theorem hasProperty_isEtale_restrictionOfScalarsMap_of_isFiniteLocallyFree
    {X' X Z Q : AlgebraicSpaces B S hS} {x' : X' ⟶ Z} {x : X ⟶ Z} (g : X' ⟶ X)
    (hg : g ≫ x = x') (z : Z ⟶ Q) (hg_etale : IsEtale B S hS g.hom)
    (hz : IsFiniteLocallyFree B S hS z) :
    HasProperty B S hS (fun _ _ f => IsEtale B S hS f.hom) (restrictionOfScalarsMap g hg z).1
      (isRepresentableByAlgebraicSpaces_restrictionOfScalarsMap_of_isFiniteLocallyFree B S hS g hg
        z hg_etale hz) :=
  hasProperty_isEtale_restrictionOfScalarsMap g hg z hg_etale hz
    (isFibreSectionsAlgebraicEtale B S hS g z)

/-- **Stacks 05Y5, first conclusion, at the hypotheses of the source.** Let `Z → Q` and
`X' → X → Q` be morphisms of algebraic spaces over `S` with `X' → X` étale and `Z → Q` finite
locally free. Then `Mor_Q(Z, X') → Mor_Q(Z, X)` is representable by algebraic spaces. -/
@[stacks 05Y5 "representable by algebraic spaces: at the hypotheses of the source, with nothing
carried"]
theorem isRepresentableByAlgebraicSpaces_relativeHomPostcompose_of_isFiniteLocallyFree
    {X' X Z Q : AlgebraicSpaces B S hS} {x' : X' ⟶ Q} {x : X ⟶ Q} {z : Z ⟶ Q}
    (HX' : RelativeHomConstruction B S hS Z.obj X'.obj Q.obj z.hom x'.hom)
    (HX : RelativeHomConstruction B S hS Z.obj X.obj Q.obj z.hom x.hom)
    (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom) (hg_etale : IsEtale B S hS g.hom)
    (hz : IsFiniteLocallyFree B S hS z) :
    IsRepresentableByAlgebraicSpaces B S hS (relativeHomPostcompose HX' HX g.hom hg) :=
  isRepresentableByAlgebraicSpaces_relativeHomPostcompose HX' HX g hg hg_etale hz
    (isFibreSectionsAlgebraicEtale B S hS g z)

/-- **Stacks 05Y5, second conclusion, at the hypotheses of the source.** In the situation of
`isRepresentableByAlgebraicSpaces_relativeHomPostcompose_of_isFiniteLocallyFree`,
the morphism `Mor_Q(Z, X') → Mor_Q(Z, X)` is étale. -/
@[stacks 05Y5 "étale: at the hypotheses of the source, with nothing carried"]
theorem hasProperty_isEtale_relativeHomPostcompose_of_isFiniteLocallyFree
    {X' X Z Q : AlgebraicSpaces B S hS} {x' : X' ⟶ Q} {x : X ⟶ Q} {z : Z ⟶ Q}
    (HX' : RelativeHomConstruction B S hS Z.obj X'.obj Q.obj z.hom x'.hom)
    (HX : RelativeHomConstruction B S hS Z.obj X.obj Q.obj z.hom x.hom)
    (g : X' ⟶ X) (hg : g.hom ≫ x.hom = x'.hom) (hg_etale : IsEtale B S hS g.hom)
    (hz : IsFiniteLocallyFree B S hS z) :
    HasProperty B S hS (fun _ _ f => IsEtale B S hS f.hom)
      (relativeHomPostcompose HX' HX g.hom hg)
      (isRepresentableByAlgebraicSpaces_relativeHomPostcompose_of_isFiniteLocallyFree B S hS HX'
        HX g hg hg_etale hz) :=
  hasProperty_isEtale_relativeHomPostcompose HX' HX g hg hg_etale hz
    (isFibreSectionsAlgebraicEtale B S hS g z)

/-! ### Stacks 05Y7 and Stacks 05YF, with the input from Stacks 05XR gone -/

/-- **Stacks 05Y7**, with the input from Stacks 05XR discharged. Let `z : Z ⟶ Q` and `x : X ⟶ Q`
be morphisms of algebraic spaces over `S` with `z` finite locally free. Then the relative
morphism functor `Mor_Q(Z, X)` of Stacks 05Y2 is an algebraic space over `S`, provided it is one
whenever the target is representable by an object of the site. -/
theorem isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree_of_representable
    (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)
    (hz : IsFiniteLocallyFree B S hS
      (ObjectProperty.homMk z :
        (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Q, hQ⟩ : AlgebraicSpaces B S hS)))
    (hrepresentable : ∀ (U : BigFppfOver B S hS) (u : yoneda.obj U ⟶ Q),
      IsAlgebraicSpace B S hS
        (relativeHom B S hS Z (yoneda.obj U) Q z u hZ (isAlgebraicSpace_yoneda B S hS U) hQ)) :
    IsAlgebraicSpace B S hS (relativeHom B S hS Z X Q z x hZ hX hQ) :=
  isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree B S hS Z X Q z x hZ hX hQ hz
    (fun _ _ => isFibreSectionsAlgebraicEtale B S hS _ _) hrepresentable

/-- **Stacks 05YF**, with the input from Stacks 05XR discharged. Let `x : X ⟶ Z` and `z : Z ⟶ Q`
be morphisms of algebraic spaces over `S` with `z` finite locally free. Then the restriction of
scalars `Res_{Z/Q}(X)` of Stacks 05YA is an algebraic space over `S`, provided the relative
morphism functor is one whenever its target is representable by an object of the site. -/
theorem isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree_of_representable
    {X Z Q : AlgebraicSpaces B S hS} (x : X ⟶ Z) (z : Z ⟶ Q)
    (hz : IsFiniteLocallyFree B S hS z)
    (hrepresentable : ∀ (U : BigFppfOver B S hS) (u : yoneda.obj U ⟶ Q.obj),
      IsAlgebraicSpace B S hS
        (relativeHom B S hS Z.obj (yoneda.obj U) Q.obj z.hom u Z.property
          (isAlgebraicSpace_yoneda B S hS U) Q.property)) :
    IsAlgebraicSpace B S hS (restrictionOfScalars B S hS x z).presheaf :=
  isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree B S hS x z hz
    (fun _ _ => isFibreSectionsAlgebraicEtale B S hS _ _)
    (fun _ _ => isFibreSectionsAlgebraicEtale B S hS _ _) hrepresentable

/-! ### Stacks 05Y7 and Stacks 05YF, with nothing carried -/

/-- **Relative morphism functors into a representable target.** Let `z : Z ⟶ Q` be a finite
locally free morphism of algebraic spaces over `S`. For every object `U` of the site and every
morphism `u : h_U ⟶ Q`, the relative morphism functor `Mor_Q(Z, h_U)` is an algebraic space over
`S`. -/
theorem isAlgebraicSpace_relativeHom_yoneda_of_isFiniteLocallyFree
    (Z Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hQ : IsAlgebraicSpace B S hS Q)
    (hz : IsFiniteLocallyFree B S hS
      (ObjectProperty.homMk z :
        (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Q, hQ⟩ : AlgebraicSpaces B S hS)))
    (U : BigFppfOver B S hS) (u : yoneda.obj U ⟶ Q) :
    IsAlgebraicSpace B S hS
      (relativeHom B S hS Z (yoneda.obj U) Q z u hZ (isAlgebraicSpace_yoneda B S hS U) hQ) :=
  isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree_of_fibreSections B S hS Z (yoneda.obj U) Q
    z u hZ (isAlgebraicSpace_yoneda B S hS U) hQ hz
    fun _ _ _ _ g z' => isFibreSectionsAlgebraicEtale B S hS g z'

/-- **Stacks 05Y7, at the hypotheses of the source.** Let `S` be a scheme contained in a big fppf
site, and let `z : Z ⟶ Q` and `x : X ⟶ Q` be morphisms of algebraic spaces over `S`. If `z` is
finite locally free then the relative morphism functor `Mor_Q(Z, X)` of Stacks 05Y2 is an
algebraic space over `S`. -/
@[stacks 05Y7 "at the hypotheses of the source, with nothing carried"]
theorem isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree_source
    (Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)
    (hz : IsFiniteLocallyFree B S hS
      (ObjectProperty.homMk z :
        (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Q, hQ⟩ : AlgebraicSpaces B S hS))) :
    IsAlgebraicSpace B S hS (relativeHom B S hS Z X Q z x hZ hX hQ) :=
  isAlgebraicSpace_relativeHom_of_isFiniteLocallyFree_of_representable B S hS Z X Q z x hZ hX hQ hz
    (isAlgebraicSpace_relativeHom_yoneda_of_isFiniteLocallyFree B S hS Z Q z hZ hQ hz)

/-- **Stacks 05YF, at the hypotheses of the source.** Let `x : X ⟶ Z` and `z : Z ⟶ Q` be
morphisms of algebraic spaces over `S` with `z` finite locally free. Then the restriction of
scalars `Res_{Z/Q}(X)` of Stacks 05YA is an algebraic space over `S`. -/
@[stacks 05YF "at the hypotheses of the source, with nothing carried"]
theorem isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree_source
    {X Z Q : AlgebraicSpaces B S hS} (x : X ⟶ Z) (z : Z ⟶ Q)
    (hz : IsFiniteLocallyFree B S hS z) :
    IsAlgebraicSpace B S hS (restrictionOfScalars B S hS x z).presheaf :=
  isAlgebraicSpace_restrictionOfScalars_of_isFiniteLocallyFree_of_representable B S hS x z hz
    (isAlgebraicSpace_relativeHom_yoneda_of_isFiniteLocallyFree B S hS Z.obj Q.obj z.hom
      Z.property Q.property hz)

end Space

end AlgebraicGeometry

end
