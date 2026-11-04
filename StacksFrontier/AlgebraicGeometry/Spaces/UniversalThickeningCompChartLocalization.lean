module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UniversalExistence
public import StacksFrontier.CategoryTheory.SubfunctorFactor
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningCompEtaleLocalization

/-!
# The compatible étale localization of a composite square, produced from a chart

Let `Z ⟶ Y ⟶ X` be morphisms of algebraic spaces over a scheme `S`, presented as in Stacks 06BF
by universal first-order thickenings `Z ⊂ Z'` over `X` and `Y ⊂ Y'` over `X` together with
`i : Z ⟶ Y` and the factorization `hfac`.  `AlgebraicGeometry.Space` of
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningCompEtaleLocalization.lean` localizes
that square along a *given* compatible localization datum — the two étale extensions `gZ`, `gY`,
the localized first morphism and its factorization.  This file **produces** that datum from an
étale chart, so that the data are no longer hypotheses of the localization.

The input is the topological invariance of the spaces-étale site, Stacks 05ZH, at the inclusion
of a first-order thickening: an algebraic space étale over the closed subspace of a first-order
thickening is the base change of an algebraic space étale over the ambient space.  That is
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isFirstOrderThickening`, read through
`Stacks.Spaces.UniversalThickening.etaleExtendsAlongFirstOrderThickening`.

## Main definitions

* `AlgebraicGeometry.Space.CompatibleEtaleLocalization`: the datum of a compatible étale
  localization of the composite square over an étale `φ : U ⟶ X` — the two étale extensions with
  their structure morphisms to `U`, the localized first morphism, and the two compatibilities.
  This is exactly the list of hypotheses the localization statements of
  `UniversalThickeningCompEtaleLocalization.lean` take.

## Main results

* `AlgebraicGeometry.Space.exists_etaleExtension_of_chart`: **the étale extension of a chart
  across a first-order thickening, with its structure morphism to the base.**  An algebraic space
  `V` étale over the closed subspace `W` of a first-order thickening `W ⊂ W'`, with a morphism
  `V ⟶ U` over an étale `φ : U ⟶ X`, extends to an étale `g : W'_U ⟶ W'` whose inverse image
  `g⁻¹(W)` is identified with `V` over `W`, carrying a morphism `r : W'_U ⟶ U` with
  `r ≫ φ = g ≫ p` restricting on `g⁻¹(W)` to the given `V ⟶ U`.  The extension is Stacks 05ZH;
  the morphism `r` is the unique lift of Stacks 0611 across the thickening `g⁻¹(W) ⊂ W'_U` along
  the formally étale `φ`, so it is *determined* by the chart and the extension.
* `AlgebraicGeometry.Space.exists_compatibleEtaleLocalization_of_charts`: **a compatible pair of
  charts produces a compatible étale localization of the pair**, with the two inverse images
  identified with the two charts and the localized first morphism *equal* to the given morphism
  of charts read through those identifications.  So neither the localized first morphism nor its
  two compatibilities is data beyond the chart: the morphism is forced by the identifications and
  the compatibilities are proved.
* `AlgebraicGeometry.Space.isIso_fromPreimage_universalThickeningCompFibre`: the projection from
  the copy of `Z` inside the fibre product `Y ×_{Y'} Z'` to `Z` is an **isomorphism** — the copy
  of `Z` is `Z`.  This is what makes a chart of the space the conormal sequence of the
  composition is read on into a chart of `Z`.
* `AlgebraicGeometry.Space.exists_compatibleEtaleLocalization_of_fibreChart`: **a chart of the
  copy of `Z` inside the fibre product alone produces a compatible étale localization**, over the
  identity of `X`.
* `AlgebraicGeometry.Space.CompatibleEtaleLocalization.isUniversalFirstOrderThickening_preimage_gZ`
  and `…_gY`, `…CompatibleEtaleLocalization.universalThickeningCompMap_comm`,
  `…CompatibleEtaleLocalization.universalThickeningCompFibreSubspace_eq`,
  `…CompatibleEtaleLocalization.isPullback_projection`,
  `…CompatibleEtaleLocalization.isEtale_projection` and
  `…CompatibleEtaleLocalization.universalThickeningCompSub_eq`: the localization statements of
  `UniversalThickeningCompEtaleLocalization.lean`, read at a localization datum.

## Implementation notes

**What the chart determines, and what it determines only up to an isomorphism.**  Stacks 05ZH is
an equivalence of sites, so the étale extension `g : W'_U ⟶ W'` of a chart `V ⟶ W` exists and is
unique up to a unique isomorphism over `W'` compatible with the identification of `g⁻¹(W)` with
`V`; what the essential-surjectivity statement returns is one such extension, with the cartesian
square exhibiting `V` as `W ×_{W'} W'_U`.  Accordingly the extension is produced here as an
existential and the identification `e : g⁻¹(W) ≅ V` is carried: it is the comparison of two
cartesian squares on one cospan, `CategoryTheory.IsPullback.isoIsPullback`, hence itself unique.
Given the extension, nothing further is a choice — the structure morphism `r : W'_U ⟶ U` is the
*unique* lift of Stacks 0611, and in the pair statement the localized first morphism is *defined*
as the given morphism of charts conjugated by the two identifications, so the two
compatibilities `iloc_comp` and `fac` that `UniversalThickeningCompEtaleLocalization.lean` carries
as data are theorems here.  That is the one correction to the shape the previous revision of that
file described: those two were data only because no étale extension was available to pin the
localized morphism down.

**Nothing here touches a module**, exactly as in
`UniversalThickeningCompEtaleLocalization.lean`: every statement is an equation of morphisms of
presheaves, of subfunctors or of algebraic spaces, or a cartesian square of them.

**The chart data are presheaf morphisms.**  A chart is given by its underlying morphism of
presheaves rather than by a morphism of the category of algebraic spaces, since that is the form
`AlgebraicGeometry.Space.IsEtale` is stated at and the form
`Stacks.Spaces.UniversalThickening.etaleExtendsAlongFirstOrderThickening` consumes; the
structure morphisms of the two localized thickenings, which have to be morphisms of algebraic
spaces because the universal property of Stacks 0602 is stated at them, are produced here.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH), the topological
  invariance of the spaces-étale site, which produces the étale extensions.
* [Stacks Project, Tag 060D](https://stacks.math.columbia.edu/tag/060D), the localization of one
  thickening.
* [Stacks Project, Tag 06BF](https://stacks.math.columbia.edu/tag/06BF), the composite square.
* [Stacks Project, Tag 0611](https://stacks.math.columbia.edu/tag/0611), the unique lift across a
  first-order thickening along a formally étale morphism, which produces the structure morphisms
  of the localized thickenings.
* [Stacks Project, Tag 0616](https://stacks.math.columbia.edu/tag/0616), an étale morphism is
  formally étale.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The étale extension of a chart across a first-order thickening -/

/-- **The étale extension of a chart across a first-order thickening, with its structure
morphism.**  Let `W ⊂ W'` be a first-order thickening with `p : W' ⟶ X`, let `φ : U ⟶ X` be
étale, let `v : V ⟶ W` be étale and let `ρ : V ⟶ U` lie over `φ`, that is `ρ ≫ φ = v ≫ W.ι ≫ p`.
Then there are an étale `g : W'_U ⟶ W'` and a morphism `r : W'_U ⟶ U` with `r ≫ φ = g ≫ p`,
together with an isomorphism `e : g⁻¹(W) ≅ V` over `W`, such that `r` restricts on `g⁻¹(W)` to
`ρ` read through `e`.

The extension is the essential surjectivity of Stacks 05ZH at the inclusion of a first-order
thickening, in the form
`Stacks.Spaces.UniversalThickening.etaleExtendsAlongFirstOrderThickening`; the isomorphism `e` is
the comparison of the cartesian square that statement returns with the cartesian square of
`CategoryTheory.Subfunctor.isPullback_preimage`.  The morphism `r` is the unique lift of
Stacks 0611 for the formally étale `φ` across the first-order thickening `g⁻¹(W) ⊂ W'_U`, which
is one by Stacks 09ZX because `g` is étale; so `r` is determined by `g`, `e` and `ρ`. -/
theorem exists_etaleExtension_of_chart {X U W' V : AlgebraicSpaces B S hS}
    (W : Subfunctor W'.obj) (p : W' ⟶ X) (hW : IsFirstOrderThickening B S hS W' W)
    (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (v : V.obj ⟶ W.toFunctor) (hv : IsEtale B S hS v)
    (ρ : V.obj ⟶ U.obj) (hρ : ρ ≫ φ.hom = v ≫ W.ι ≫ p.hom) :
    ∃ (W'U : AlgebraicSpaces B S hS) (g : W'U ⟶ W') (r : W'U ⟶ U)
      (e : (W.preimage g.hom).toFunctor ≅ V.obj),
      IsEtale B S hS g.hom ∧ r ≫ φ = g ≫ p ∧ e.hom ≫ v = W.fromPreimage g.hom ∧
        (W.preimage g.hom).ι ≫ r.hom = e.hom ≫ ρ := by
  obtain ⟨W'U, g, j, hg, hsq⟩ :=
    Stacks.Spaces.UniversalThickening.etaleExtendsAlongFirstOrderThickening B S hS W hW v hv
  obtain ⟨e, he⟩ : ∃ e : (W.preimage g.hom).toFunctor ≅ V.obj,
      e.hom ≫ v = W.fromPreimage g.hom :=
    ⟨(Subfunctor.isPullback_preimage g.hom W).isoIsPullback _ _ hsq,
      IsPullback.isoIsPullback_hom_fst _ _ _ _⟩
  have hφFE : FormallyEtale φ.hom :=
    ((isEtale_iff_isLocallyOfFinitePresentation_and_formallyEtale B S hS
      U.property X.property φ.hom).mp hφ).2
  have hpre : IsFirstOrderThickening B S hS W'U (W.preimage g.hom) :=
    isFirstOrderThickening_preimage_of_isEtale B S hS W g hg hW
  have hsolid : (e.hom ≫ ρ) ≫ φ.hom = (W.preimage g.hom).ι ≫ g.hom ≫ p.hom := by
    rw [Category.assoc, hρ, reassoc_of% he, reassoc_of% (Subfunctor.fromPreimage_ι W g.hom)]
  obtain ⟨rh, hr, -⟩ := FormallyEtale.existsUnique_lift_of_firstOrderThickening B S hS φ hφFE
    (W.preimage g.hom) hpre (e.hom ≫ ρ) (g.hom ≫ p.hom) hsolid
  exact ⟨W'U, g, ObjectProperty.homMk rh, e, hg, ObjectProperty.hom_ext _ hr.2, he, hr.1⟩

/-! ### The datum of a compatible étale localization of the pair -/

/-- **A compatible étale localization of the composite square of Stacks 06BF.**  For universal
first-order thickenings `Z ⊂ Z'` over `X` with `pZ : Z' ⟶ X` and `Y ⊂ Y'` over `X` with
`pY : Y' ⟶ X`, a morphism `i : Z ⟶ Y`, and an étale `φ : U ⟶ X`, this is the datum the
localization statements of
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningCompEtaleLocalization.lean` take: étale
extensions of the two ambient spaces with structure morphisms to `U`, the localized first
morphism between the two inverse images, and its two compatibilities. -/
structure CompatibleEtaleLocalization {X Y' Z' U : AlgebraicSpaces B S hS}
    (Y : Subfunctor Y'.obj) (Z : Subfunctor Z'.obj) (pY : Y' ⟶ X) (pZ : Z' ⟶ X)
    (i : Z.toFunctor ⟶ Y.toFunctor) (φ : U ⟶ X) where
  /-- The localized ambient space of the thickening of `Z`. -/
  ambientZ : AlgebraicSpaces B S hS
  /-- The localized ambient space of the thickening of `Y`. -/
  ambientY : AlgebraicSpaces B S hS
  /-- The étale extension of the ambient space of the thickening of `Z`. -/
  gZ : ambientZ ⟶ Z'
  /-- The structure morphism of the localized thickening of `Z`. -/
  rZ : ambientZ ⟶ U
  /-- The étale extension of the ambient space of the thickening of `Y`. -/
  gY : ambientY ⟶ Y'
  /-- The structure morphism of the localized thickening of `Y`. -/
  rY : ambientY ⟶ U
  /-- The extension on the `Z` side is étale. -/
  isEtale_gZ : IsEtale B S hS gZ.hom
  /-- The extension on the `Y` side is étale. -/
  isEtale_gY : IsEtale B S hS gY.hom
  /-- The `Z` side of the localization lies over `φ`. -/
  over_gZ : rZ ≫ φ = gZ ≫ pZ
  /-- The `Y` side of the localization lies over `φ`. -/
  over_gY : rY ≫ φ = gY ≫ pY
  /-- The localized first morphism, from the inverse image of `Z` to the inverse image of `Y`. -/
  iloc : (Z.preimage gZ.hom).toFunctor ⟶ (Y.preimage gY.hom).toFunctor
  /-- The localized first morphism lies over `i`. -/
  iloc_comp : iloc ≫ Y.fromPreimage gY.hom = Z.fromPreimage gZ.hom ≫ i
  /-- The localized factorization of the structure morphism of the smaller space. -/
  fac : (Z.preimage gZ.hom).ι ≫ rZ.hom = iloc ≫ (Y.preimage gY.hom).ι ≫ rY.hom

namespace CompatibleEtaleLocalization

variable {X Y' Z' U : AlgebraicSpaces B S hS} {Y : Subfunctor Y'.obj} {Z : Subfunctor Z'.obj}
    {pY : Y' ⟶ X} {pZ : Z' ⟶ X} {i : Z.toFunctor ⟶ Y.toFunctor} {φ : U ⟶ X}
    (L : CompatibleEtaleLocalization B S hS Y Z pY pZ i φ)
    (hZ : IsUniversalFirstOrderThickening B S hS Z pZ)
    (hY : IsUniversalFirstOrderThickening B S hS Y pY)
    (hfac : Z.ι ≫ pZ.hom = i ≫ Y.ι ≫ pY.hom)
    (hφ : IsEtale B S hS φ.hom)

include hZ hφ in
/-- **Clause (2) of Stacks 060D on the `Z` side.**  The inverse image of `Z` is a universal
first-order thickening over `U`, with structure morphism `rZ`. -/
theorem isUniversalFirstOrderThickening_preimage_gZ :
    IsUniversalFirstOrderThickening B S hS (Z.preimage L.gZ.hom) L.rZ :=
  IsUniversalFirstOrderThickening.etaleLocalizationPreimage B S hS Z pZ hZ φ hφ L.gZ
    L.isEtale_gZ L.rZ L.over_gZ

include hY hφ in
/-- **Clause (2) of Stacks 060D on the `Y` side.**  The inverse image of `Y` is a universal
first-order thickening over `U`, with structure morphism `rY`. -/
theorem isUniversalFirstOrderThickening_preimage_gY :
    IsUniversalFirstOrderThickening B S hS (Y.preimage L.gY.hom) L.rY :=
  IsUniversalFirstOrderThickening.etaleLocalizationPreimage B S hS Y pY hY φ hφ L.gY
    L.isEtale_gY L.rY L.over_gY

/-- **The morphism `h : Z' ⟶ Y'` of clause (1) of Stacks 06BF commutes with the localization.**
`AlgebraicGeometry.Space.universalThickeningCompMap_etaleLocalization` at a localization
datum. -/
theorem universalThickeningCompMap_comm :
    universalThickeningCompMap B S hS L.iloc
          (isUniversalFirstOrderThickening_preimage_gZ B S hS L hZ hφ)
          (isUniversalFirstOrderThickening_preimage_gY B S hS L hY hφ) L.fac ≫ L.gY =
      L.gZ ≫ universalThickeningCompMap B S hS i hZ hY hfac :=
  universalThickeningCompMap_etaleLocalization B S hS i hZ hY hfac φ L.gZ L.rZ L.over_gZ L.gY
    L.rY L.over_gY (isUniversalFirstOrderThickening_preimage_gZ B S hS L hZ hφ)
    (isUniversalFirstOrderThickening_preimage_gY B S hS L hY hφ) L.iloc L.iloc_comp L.fac

/-- **The localized fibre product is the inverse image of the original one.**
`AlgebraicGeometry.Space.universalThickeningCompFibreSubspace_etaleLocalization` at a
localization datum. -/
theorem universalThickeningCompFibreSubspace_eq :
    universalThickeningCompFibreSubspace B S hS L.iloc
          (isUniversalFirstOrderThickening_preimage_gZ B S hS L hZ hφ)
          (isUniversalFirstOrderThickening_preimage_gY B S hS L hY hφ) L.fac =
      preimageSubspace B S hS L.gZ
        (universalThickeningCompFibreSubspace B S hS i hZ hY hfac) :=
  universalThickeningCompFibreSubspace_etaleLocalization B S hS i hZ hY hfac φ L.gZ L.rZ
    L.over_gZ L.gY L.rY L.over_gY (isUniversalFirstOrderThickening_preimage_gZ B S hS L hZ hφ)
    (isUniversalFirstOrderThickening_preimage_gY B S hS L hY hφ) L.iloc L.iloc_comp L.fac

/-- **The localized fibre product sits in a cartesian square over `gZ`.**
`AlgebraicGeometry.Space.isPullback_universalThickeningCompFibreLocalizationProjection` at a
localization datum. -/
theorem isPullback_projection :
    IsPullback (universalThickeningCompFibreLocalizationProjection B S hS i hZ hY hfac φ L.gZ
        L.rZ L.over_gZ L.gY L.rY L.over_gY
        (isUniversalFirstOrderThickening_preimage_gZ B S hS L hZ hφ)
        (isUniversalFirstOrderThickening_preimage_gY B S hS L hY hφ) L.iloc L.iloc_comp L.fac)
      (universalThickeningCompFibreSubspace B S hS L.iloc
        (isUniversalFirstOrderThickening_preimage_gZ B S hS L hZ hφ)
        (isUniversalFirstOrderThickening_preimage_gY B S hS L hY hφ) L.fac).1.ι
      (universalThickeningCompFibreSubspace B S hS i hZ hY hfac).1.ι L.gZ.hom :=
  isPullback_universalThickeningCompFibreLocalizationProjection B S hS i hZ hY hfac φ L.gZ L.rZ
    L.over_gZ L.gY L.rY L.over_gY (isUniversalFirstOrderThickening_preimage_gZ B S hS L hZ hφ)
    (isUniversalFirstOrderThickening_preimage_gY B S hS L hY hφ) L.iloc L.iloc_comp L.fac

/-- **The projection of the localized fibre product onto the original one is étale.**
`AlgebraicGeometry.Space.isEtale_universalThickeningCompFibreLocalizationProjection` at a
localization datum. -/
theorem isEtale_projection :
    IsEtale B S hS (universalThickeningCompFibreLocalizationProjection B S hS i hZ hY hfac φ
      L.gZ L.rZ L.over_gZ L.gY L.rY L.over_gY
      (isUniversalFirstOrderThickening_preimage_gZ B S hS L hZ hφ)
      (isUniversalFirstOrderThickening_preimage_gY B S hS L hY hφ) L.iloc L.iloc_comp L.fac) :=
  isEtale_universalThickeningCompFibreLocalizationProjection B S hS i hZ hY hfac φ L.gZ L.rZ
    L.over_gZ L.gY L.rY L.over_gY (isUniversalFirstOrderThickening_preimage_gZ B S hS L hZ hφ)
    (isUniversalFirstOrderThickening_preimage_gY B S hS L hY hφ) L.iloc L.iloc_comp L.fac
    L.isEtale_gZ

/-- **The copy of `Z` inside the localized fibre product is the inverse image of the copy of `Z`
inside the original one.**  `AlgebraicGeometry.Space.universalThickeningCompSub_etaleLocalization`
at a localization datum: the space the conormal sequence of the composition is read on localizes
over the chart. -/
theorem universalThickeningCompSub_eq :
    universalThickeningCompSub B S hS L.iloc
          (isUniversalFirstOrderThickening_preimage_gZ B S hS L hZ hφ)
          (isUniversalFirstOrderThickening_preimage_gY B S hS L hY hφ) L.fac =
      (universalThickeningCompSub B S hS i hZ hY hfac).preimage
        (universalThickeningCompFibreLocalizationProjection B S hS i hZ hY hfac φ L.gZ L.rZ
          L.over_gZ L.gY L.rY L.over_gY
          (isUniversalFirstOrderThickening_preimage_gZ B S hS L hZ hφ)
          (isUniversalFirstOrderThickening_preimage_gY B S hS L hY hφ) L.iloc L.iloc_comp L.fac) :=
  universalThickeningCompSub_etaleLocalization B S hS i hZ hY hfac φ L.gZ L.rZ L.over_gZ L.gY
    L.rY L.over_gY (isUniversalFirstOrderThickening_preimage_gZ B S hS L hZ hφ)
    (isUniversalFirstOrderThickening_preimage_gY B S hS L hY hφ) L.iloc L.iloc_comp L.fac

end CompatibleEtaleLocalization

/-! ### A compatible pair of charts produces a compatible localization -/

/-- **A compatible pair of charts produces a compatible étale localization of the pair.**  Let
`φ : U ⟶ X` be étale, let `v : V ⟶ Z` and `w : W ⟶ Y` be étale, let `c : V ⟶ W` lie over `i` and
let `ρ : W ⟶ U` lie over `φ`.  Then there is a compatible étale localization of the composite
square over `φ` whose two inverse images are identified with `V` and `W` over `Z` and `Y`, and
whose localized first morphism is `c` read through those two identifications.

Both halves are `AlgebraicGeometry.Space.exists_etaleExtension_of_chart`, the `Z` half applied to
the chart `v` with structure morphism `c ≫ ρ` — which lies over `φ` because `c` lies over `i` and
`ρ` over `φ`, by the factorization `hfac` of the composite square.  The localized first morphism
is then forced, and its two compatibilities are proved rather than assumed: `iloc_comp` is `hc`
conjugated by the two identifications, and `fac` is the restriction identity of the two
structure morphisms, again conjugated. -/
theorem exists_compatibleEtaleLocalization_of_charts
    {X Y' Z' U V W : AlgebraicSpaces B S hS} {Y : Subfunctor Y'.obj} {Z : Subfunctor Z'.obj}
    {pY : Y' ⟶ X} {pZ : Z' ⟶ X} (i : Z.toFunctor ⟶ Y.toFunctor)
    (hZ : IsFirstOrderThickening B S hS Z' Z) (hY : IsFirstOrderThickening B S hS Y' Y)
    (hfac : Z.ι ≫ pZ.hom = i ≫ Y.ι ≫ pY.hom)
    (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (v : V.obj ⟶ Z.toFunctor) (hv : IsEtale B S hS v)
    (w : W.obj ⟶ Y.toFunctor) (hw : IsEtale B S hS w)
    (c : V.obj ⟶ W.obj) (hc : c ≫ w = v ≫ i)
    (ρ : W.obj ⟶ U.obj) (hρ : ρ ≫ φ.hom = w ≫ Y.ι ≫ pY.hom) :
    ∃ (L : CompatibleEtaleLocalization B S hS Y Z pY pZ i φ)
      (eZ : (Z.preimage L.gZ.hom).toFunctor ≅ V.obj)
      (eY : (Y.preimage L.gY.hom).toFunctor ≅ W.obj),
      eZ.hom ≫ v = Z.fromPreimage L.gZ.hom ∧ eY.hom ≫ w = Y.fromPreimage L.gY.hom ∧
        L.iloc = eZ.hom ≫ c ≫ eY.inv := by
  obtain ⟨Y'U, gY, rY, eY, hgY, hoverY, heY, hrY⟩ :=
    exists_etaleExtension_of_chart B S hS Y pY hY φ hφ w hw ρ hρ
  have hρV : (c ≫ ρ) ≫ φ.hom = v ≫ Z.ι ≫ pZ.hom := by
    rw [Category.assoc, hρ, reassoc_of% hc, hfac]
  obtain ⟨Z'U, gZ, rZ, eZ, hgZ, hoverZ, heZ, hrZ⟩ :=
    exists_etaleExtension_of_chart B S hS Z pZ hZ φ hφ v hv (c ≫ ρ) hρV
  have hilocComp : (eZ.hom ≫ c ≫ eY.inv) ≫ Y.fromPreimage gY.hom =
      Z.fromPreimage gZ.hom ≫ i := by
    simp only [Category.assoc, ← heY, ← heZ, Iso.inv_hom_id_assoc, hc]
  have hfacU : (Z.preimage gZ.hom).ι ≫ rZ.hom =
      (eZ.hom ≫ c ≫ eY.inv) ≫ (Y.preimage gY.hom).ι ≫ rY.hom := by
    simp only [Category.assoc, hrZ, hrY, Iso.inv_hom_id_assoc]
  exact ⟨⟨Z'U, Y'U, gZ, rZ, gY, rY, hgZ, hgY, hoverZ, hoverY, eZ.hom ≫ c ≫ eY.inv, hilocComp,
    hfacU⟩, eZ, eY, heZ, heY, rfl⟩

/-! ### The copy of `Z` inside the fibre product is `Z` -/

variable {X Y' Z' : AlgebraicSpaces B S hS} {Y : Subfunctor Y'.obj} {Z : Subfunctor Z'.obj}
    {pY : Y' ⟶ X} {pZ : Z' ⟶ X} (i : Z.toFunctor ⟶ Y.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z pZ)
    (hY : IsUniversalFirstOrderThickening B S hS Y pY)
    (hfac : Z.ι ≫ pZ.hom = i ≫ Y.ι ≫ pY.hom)

/-- `Z` is contained in the fibre product `Y ×_{Y'} Z'`, read as a closed subspace of `Z'`: the
morphism `h : Z' ⟶ Y'` of clause (1) of Stacks 06BF carries `Z` into `Y`, which is
`AlgebraicGeometry.Space.universalThickeningCompMap_restrict`. -/
theorem le_universalThickeningCompFibreSubspace :
    Z ≤ (universalThickeningCompFibreSubspace B S hS i hZ hY hfac).1 :=
  have P := Subfunctor.isPullback_preimage (universalThickeningCompMap B S hS i hZ hY hfac).hom Y
  Subfunctor.le_of_comp_eq_ι
    (P.lift i Z.ι (universalThickeningCompMap_restrict B S hS i hZ hY hfac).symm)
    (P.lift_snd _ _ _)

/-- **The copy of `Z` inside the fibre product `Y ×_{Y'} Z'` is `Z`.**  The projection
`AlgebraicGeometry.Space.universalThickeningCompSub` ⟶ `Z` — the canonical projection of the
inverse image of `Z ⊆ Z'` along the inclusion of the fibre product — is an isomorphism, because
`Z` is already contained in the fibre product.

This is what turns an étale chart of the space the conormal sequence of the composition is read
on into an étale chart of `Z`. -/
theorem isIso_fromPreimage_universalThickeningCompFibre :
    IsIso (Z.fromPreimage (universalThickeningCompFibreSubspace B S hS i hZ hY hfac).1.ι) := by
  set F := (universalThickeningCompFibreSubspace B S hS i hZ hY hfac).1
  have hle : Z ≤ F := le_universalThickeningCompFibreSubspace B S hS i hZ hY hfac
  have hk : Subfunctor.homOfLe hle ≫ F.ι = Z.ι := Subfunctor.homOfLe_ι hle
  obtain ⟨n, hn⟩ : ∃ n : Z.toFunctor ⟶ (Z.preimage F.ι).toFunctor,
      n ≫ (Z.preimage F.ι).ι = Subfunctor.homOfLe hle :=
    ⟨Subfunctor.lift (Subfunctor.homOfLe hle) (by
      rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp, hk, Subfunctor.range_ι]), rfl⟩
  have hm : Z.fromPreimage F.ι ≫ Z.ι = (Z.preimage F.ι).ι ≫ F.ι :=
    Subfunctor.fromPreimage_ι Z F.ι
  refine ⟨n, ?_, ?_⟩
  · refine (cancel_mono (Z.preimage F.ι).ι).1 ((cancel_mono F.ι).1 ?_)
    simp only [Category.assoc, reassoc_of% hn, hk, hm, Category.id_comp]
  · refine (cancel_mono Z.ι).1 ?_
    simp only [Category.assoc, hm, reassoc_of% hn, hk, Category.id_comp]

/-- **A chart of the copy of `Z` inside the fibre product produces a compatible étale
localization of the pair**, over the identity of `X`.

The chart is an étale chart of `Z` by
`AlgebraicGeometry.Space.isIso_fromPreimage_universalThickeningCompFibre`, and the chart taken on
the `Y` side is the identity of `Y`; its étale extension is an algebraic space étale over `Y'`
whose inverse image of `Y` is identified with `Y`, so it is isomorphic to `Y'` over `Y'` but is
not `Y'` on the nose — it is whatever
`AlgebraicGeometry.Space.exists_etaleExtension_of_chart` returns.  The resulting localization
datum restricts the thickening of `Z` to the chart and leaves the thickening of `Y` where it is
up to that isomorphism.  So a
chart of the space the conormal sequence of the composition is read on does by itself produce the
whole localization datum — what it does not produce is a chart of `Y` to read the left-hand term
of that sequence on, which is why
`AlgebraicGeometry.Space.exists_compatibleEtaleLocalization_of_charts` takes a compatible *pair*
of charts. -/
theorem exists_compatibleEtaleLocalization_of_fibreChart {V : AlgebraicSpaces B S hS}
    (a : V.obj ⟶ (universalThickeningCompSub B S hS i hZ hY hfac).toFunctor)
    (ha : IsEtale B S hS a) :
    ∃ (L : CompatibleEtaleLocalization B S hS Y Z pY pZ i (𝟙 X))
      (eZ : (Z.preimage L.gZ.hom).toFunctor ≅ V.obj),
      eZ.hom ≫ a ≫ Z.fromPreimage
          (universalThickeningCompFibreSubspace B S hS i hZ hY hfac).1.ι =
        Z.fromPreimage L.gZ.hom := by
  have hiso := isIso_fromPreimage_universalThickeningCompFibre B S hS i hZ hY hfac
  set f := a ≫ Z.fromPreimage (universalThickeningCompFibreSubspace B S hS i hZ hY hfac).1.ι
  have hv : IsEtale B S hS f := isEtale_comp B S hS ha (isEtale_of_isIso B S hS _)
  have hφ : IsEtale B S hS (𝟙 X : X ⟶ X).hom := isEtale_of_isIso B S hS (𝟙 X.obj)
  have hw : IsEtale B S hS (𝟙 Y.toFunctor) := isEtale_of_isIso B S hS (𝟙 Y.toFunctor)
  obtain ⟨L, eZ, eY, heZ, heY, hilocEq⟩ := exists_compatibleEtaleLocalization_of_charts B S hS i
    hZ.firstOrder hY.firstOrder hfac (𝟙 X) hφ f hv
    (W := (⟨Y.toFunctor, hY.firstOrder.1.1.1⟩ : AlgebraicSpaces B S hS))
    (𝟙 Y.toFunctor) hw (f ≫ i) (Category.comp_id _) (Y.ι ≫ pY.hom) (by simp)
  exact ⟨L, eZ, heZ⟩

end AlgebraicGeometry.Space

end
