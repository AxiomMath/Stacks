module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningEtaleLocalization

/-!
# Étale localization of the composite square of two universal first-order thickenings

Let `Z ⟶ Y ⟶ X` be morphisms of algebraic spaces over a scheme `S`, presented as in Stacks 06BF
by universal first-order thickenings `Z ⊂ Z'` over `X` with structure morphism `pZ : Z' ⟶ X` and
`Y ⊂ Y'` over `X` with structure morphism `pY : Y' ⟶ X`, together with `i : Z ⟶ Y` and the
factorization `hfac` of the structure morphism of `Z` through `Y`.  Stacks 060D localizes **one**
such thickening along an étale morphism; this file localizes the whole **composite square**.

A compatible étale localization of the pair over an étale `φ : U ⟶ X` consists of

* étale extensions `gZ : Z'_U ⟶ Z'` and `gY : Y'_U ⟶ Y'` with structure morphisms
  `rZ : Z'_U ⟶ U` and `rY : Y'_U ⟶ U` satisfying `rZ ≫ φ = gZ ≫ pZ` and `rY ≫ φ = gY ≫ pY`;
* the localized first morphism `iU : gZ⁻¹(Z) ⟶ gY⁻¹(Y)`, lying over `i`, with the localized
  factorization.

The two localized thickenings are then `gZ⁻¹(Z) ⊂ Z'_U` over `U` and `gY⁻¹(Y) ⊂ Y'_U` over `U`,
by clause (2) of Stacks 060D, and this file proves that the rest of the Stacks 06BF
configuration localizes with them: the morphism `h : Z' ⟶ Y'` of clause (1), the fibre product
`Y ×_{Y'} Z'` and the copy of `Z` inside it — the space the conormal sequence of the composition
is read on.

## Main definitions

* `AlgebraicGeometry.Space.universalThickeningCompFibreLocalizationProjection`: the projection
  `Y_U ×_{Y'_U} Z'_U ⟶ Y ×_{Y'} Z'` of the localized fibre product onto the original one.

## Main results

* `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.etaleLocalizationPreimage`: clause (2)
  of Stacks 060D at the canonical inverse image — the étale extension `g : W'_U ⟶ W'` of a
  universal first-order thickening `W ⊂ W'` over `X` presents `g⁻¹(W) ⊂ W'_U` as a universal
  first-order thickening over an étale `U ⟶ X`.  The cartesian square clause (2) asks for is the
  one of `CategoryTheory.Subfunctor.isPullback_preimage`, so nothing has to be supplied for it;
  this is the form in which both halves of the pair are localized below.
* `AlgebraicGeometry.Space.universalThickeningCompMap_etaleLocalization`: **the morphism
  `h : Z' ⟶ Y'` of clause (1) of Stacks 06BF commutes with the localization**, that is
  `h_U ≫ gY = gZ ≫ h`.  This is the heart of the file.  No étaleness is used: the two
  morphisms `Z'_U ⟶ Y'` agree because both restrict to `Z.fromPreimage gZ ≫ i` on `gZ⁻¹(Z)` and
  both lie over `gZ ≫ pZ`, so they coincide by the uniqueness clause of the universal property of
  `Y ⊂ Y'` applied to the first-order thickening `gZ⁻¹(Z) ⊂ Z'_U`.
* `AlgebraicGeometry.Space.universalThickeningCompFibreSubspace_etaleLocalization`: **the
  localized fibre product is the inverse image of the original one** along `gZ`, as closed
  subspaces of `Z'_U`.
* `AlgebraicGeometry.Space.isPullback_universalThickeningCompFibreLocalizationProjection` and
  `AlgebraicGeometry.Space.isEtale_universalThickeningCompFibreLocalizationProjection`: that
  projection sits in a cartesian square over `gZ` and is therefore étale.
* `AlgebraicGeometry.Space.universalThickeningCompSub_etaleLocalization`: **the copy of `Z` inside
  the localized fibre product is the inverse image of the copy of `Z` inside the original one**
  along that projection.  This is the statement that the base of the conormal sequence of the
  composition localizes over the chart; the corresponding statement for
  `AlgebraicGeometry.Space.universalThickeningCompConormalBase` of the module
  `…/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/ConormalShortExact.lean` is this
  equality read through `Subtype.ext`, that closed subspace being this subfunctor with a proof
  attached.

## Implementation notes

**The localized universal properties are arguments, not hypotheses of the file.**  The statements
below take the two localized universal properties `hZU` and `hYU` as arguments rather than
building them, so that they hold for any witnesses; the witnesses are produced by
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.etaleLocalizationPreimage` in this file,
which is clause (2) of Stacks 060D and is where the étaleness of `φ`, `gZ` and `gY` is consumed.
The compatibility of `h` itself needs none of them.

**Nothing in this file touches a module.**  Every statement is an equation of morphisms of
presheaves, of subfunctors or of algebraic spaces.  That is deliberate: the identifications of
the conormal *modules* of the two localized thickenings are clause (3) of Stacks 060D,
`AlgebraicGeometry.Space.conormalModuleEtaleLocalizationIso`, applied once with `gZ` and once
with `gY` at the cartesian squares of `CategoryTheory.Subfunctor.isPullback_preimage`, and once
more with the projection above at the cartesian square proved here; no new statement is needed
for them and none is added.

## Where the localization data come from

**They are produced from a chart**, in
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalThickeningCompChartLocalization.lean`.  Extending
an étale morphism over `Z` across the closed immersion `Z ⊂ Z'` is the topological invariance of
the spaces-étale site, Stacks 05ZH, and **that is proved** —
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isFirstOrderThickening` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/SpacesEtaleEssSurj.lean`, read through
`Stacks.Spaces.UniversalThickening.etaleExtendsAlongFirstOrderThickening`.  The data remain arguments of the statements below, so that they hold
for any witnesses, and `AlgebraicGeometry.Space.exists_compatibleEtaleLocalization_of_charts`
supplies witnesses from a compatible pair of charts;
`AlgebraicGeometry.Space.exists_compatibleEtaleLocalization_of_fibreChart` supplies them from a
chart of the space the conormal sequence is read on alone, over the identity of `X`.  What is
produced there is also sharper than the shape of this file in one respect: `hiU` and `hfacU` are
*proved* for the localized morphism the chart determines, rather than being further data.

## What is not proved

* **The *arrows* of the conormal sequence are not identified across the localization**, and
  nothing here claims they are.  Carrying the left-hand arrow
  `π^*𝒞_{Y/X} ⟶ π^*𝒞_{Z/X}` of Stacks 06BD across the localization needs the map of Stacks 04CP
  at the localization square to be the isomorphism of Stacks 04CO, which the *What is not proved*
  section of `StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleEtaleRestriction.lean` records as
  absent: the two available descriptions of
  `AlgebraicGeometry.Space.idealSheafMap` and of the Stacks 03LW comparison are not brought to a
  common form anywhere in this development.  So this file carries the *geometry* of the
  localization and not the comparison of the two sequences of modules.

## References

* [Stacks Project, Tag 060D](https://stacks.math.columbia.edu/tag/060D), the localization of one
  thickening.
* [Stacks Project, Tag 06BF](https://stacks.math.columbia.edu/tag/06BF), the composite square.
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602), the universal property
  whose uniqueness clause identifies the two morphisms `Z'_U ⟶ Y'`.
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q), the inverse image of a
  closed subspace is a closed subspace.
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH), the input the
  étale extensions are produced from.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

/-! ### Two identities for inverse images of subfunctors -/

/-- Taking inverse images of a subfunctor composes. -/
private theorem preimage_preimage_eq {C : Type v} [Category.{w} C] {F F' F'' : C ⥤ Type u}
    (G : Subfunctor F) (p : F' ⟶ F) (q : F'' ⟶ F') :
    (G.preimage p).preimage q = G.preimage (q ≫ p) :=
  Subfunctor.ext (funext fun n => (Set.preimage_comp (f := q.app n) (g := p.app n)).symm)

/-- Inverse images of a subfunctor along two factorizations of the same composite agree. -/
private theorem preimage_preimage_eq_of_comp_eq {C : Type v} [Category.{w} C]
    {F F₁ F₂ F' : C ⥤ Type u} (G : Subfunctor F) (p₁ : F₁ ⟶ F) (q₁ : F' ⟶ F₁) (p₂ : F₂ ⟶ F)
    (q₂ : F' ⟶ F₂) (h : q₁ ≫ p₁ = q₂ ≫ p₂) :
    (G.preimage p₁).preimage q₁ = (G.preimage p₂).preimage q₂ := by
  rw [preimage_preimage_eq, preimage_preimage_eq, h]

/-- A subfunctor which *is* the inverse image of `G` along `p`, with any morphism to `G` over
`p`, sits in the cartesian square of the inverse image: the morphism is forced to be the
canonical projection because the inclusion of a subfunctor is a monomorphism. -/
private theorem isPullback_of_preimage_eq {C : Type v} [Category.{w} C] {F F' : C ⥤ Type u}
    (G : Subfunctor F) (p : F' ⟶ F) (H : Subfunctor F') (hH : H = G.preimage p)
    (c : H.toFunctor ⟶ G.toFunctor) (hc : c ≫ G.ι = H.ι ≫ p) :
    IsPullback c H.ι G.ι p := by
  subst hH
  obtain rfl : c = G.fromPreimage p := (cancel_mono G.ι).1 (by rwa [Subfunctor.fromPreimage_ι])
  exact Subfunctor.isPullback_preimage p G

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Clause (2) of Stacks 060D at the canonical inverse image -/

/-- **Clause (2) of Stacks 060D at the canonical inverse image.**  Let `W ⊂ W'` be a universal
first-order thickening of `W` over `X` with structure morphism `p : W' ⟶ X`, let `φ : U ⟶ X` be
étale and let `g : W'_U ⟶ W'` be étale with a morphism `r : W'_U ⟶ U` satisfying
`r ≫ φ = g ≫ p`.  Then the inverse image `g⁻¹(W) ⊂ W'_U` is a universal first-order thickening
of `g⁻¹(W)` over `U`, with structure morphism `r`.

This is `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.etaleLocalization` with the
smaller space taken to be the inverse image and the cartesian square taken to be the one of
`CategoryTheory.Subfunctor.isPullback_preimage`, so that neither has to be supplied.  It is the
form in which the two halves of a composite square are localized below. -/
theorem IsUniversalFirstOrderThickening.etaleLocalizationPreimage
    {X U W' W'U : AlgebraicSpaces B S hS} (W : Subfunctor W'.obj) (p : W' ⟶ X)
    (hW : IsUniversalFirstOrderThickening B S hS W p)
    (φ : U ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (g : W'U ⟶ W') (hg : IsEtale B S hS g.hom) (r : W'U ⟶ U) (hr : r ≫ φ = g ≫ p) :
    IsUniversalFirstOrderThickening B S hS (W.preimage g.hom) r :=
  IsUniversalFirstOrderThickening.etaleLocalization B S hS W p hW φ hφ g hg r hr
    (W.preimage g.hom) (W.fromPreimage g.hom) (Subfunctor.isPullback_preimage g.hom W)

/-! ### The composite square and its compatible localization -/

variable {X Y' Z' U Y'U Z'U : AlgebraicSpaces B S hS} {Y : Subfunctor Y'.obj}
    {Z : Subfunctor Z'.obj} {pY : Y' ⟶ X} {pZ : Z' ⟶ X} (i : Z.toFunctor ⟶ Y.toFunctor)
    (hZ : IsUniversalFirstOrderThickening B S hS Z pZ)
    (hY : IsUniversalFirstOrderThickening B S hS Y pY)
    (hfac : Z.ι ≫ pZ.hom = i ≫ Y.ι ≫ pY.hom)
    (φ : U ⟶ X)
    (gZ : Z'U ⟶ Z') (rZ : Z'U ⟶ U) (hrZ : rZ ≫ φ = gZ ≫ pZ)
    (gY : Y'U ⟶ Y') (rY : Y'U ⟶ U) (hrY : rY ≫ φ = gY ≫ pY)
    (hZU : IsUniversalFirstOrderThickening B S hS (Z.preimage gZ.hom) rZ)
    (hYU : IsUniversalFirstOrderThickening B S hS (Y.preimage gY.hom) rY)
    (iU : (Z.preimage gZ.hom).toFunctor ⟶ (Y.preimage gY.hom).toFunctor)
    (hiU : iU ≫ Y.fromPreimage gY.hom = Z.fromPreimage gZ.hom ≫ i)
    (hfacU : (Z.preimage gZ.hom).ι ≫ rZ.hom = iU ≫ (Y.preimage gY.hom).ι ≫ rY.hom)

include hrZ hrY hiU in
/-- **The morphism `h : Z' ⟶ Y'` of clause (1) of Stacks 06BF commutes with a compatible étale
localization of the pair**, on underlying presheaves: `h_U ≫ gY = gZ ≫ h`.

Both sides are morphisms `Z'_U ⟶ Y'`, and both are lifts of one solid diagram for the universal
property of `Y ⊂ Y'` over `X` at the first-order thickening `gZ⁻¹(Z) ⊂ Z'_U`: each restricts to
`Z.fromPreimage gZ ≫ i` on `gZ⁻¹(Z)` and each composes with `pY` to `gZ ≫ pZ`.  For `h_U ≫ gY`
the restriction is `universalThickeningCompMap_restrict` for the localized datum followed by
`hiU`, and the composite with `pY` is `universalThickeningCompMap_over_hom` for the localized
datum read through `hrY` and `hrZ`; for `gZ ≫ h` both are the corresponding statements for the
original datum.  So they agree by the uniqueness clause of the universal property.

No étaleness is used here; see the implementation notes of this file. -/
theorem universalThickeningCompMap_etaleLocalization_hom :
    (universalThickeningCompMap B S hS iU hZU hYU hfacU).hom ≫ gY.hom =
      gZ.hom ≫ (universalThickeningCompMap B S hS i hZ hY hfac).hom := by
  have hrZhom : rZ.hom ≫ φ.hom = gZ.hom ≫ pZ.hom :=
    congrArg (fun k : Z'U ⟶ X => k.hom) hrZ
  have hrYhom : rY.hom ≫ φ.hom = gY.hom ≫ pY.hom :=
    congrArg (fun k : Y'U ⟶ X => k.hom) hrY
  refine hY.eq_of_lifts (Z.preimage gZ.hom) hZU.firstOrder (Z.fromPreimage gZ.hom ≫ i)
    (gZ.hom ≫ pZ.hom) _ _ ?_ ?_ ?_ ?_
  · rw [reassoc_of% (universalThickeningCompMap_restrict B S hS iU hZU hYU hfacU),
      ← Subfunctor.fromPreimage_ι, reassoc_of% hiU, Category.assoc]
  · rw [Category.assoc, ← hrYhom,
      reassoc_of% (universalThickeningCompMap_over_hom B S hS iU hZU hYU hfacU), hrZhom]
  · rw [← Category.assoc, ← Subfunctor.fromPreimage_ι, Category.assoc,
      universalThickeningCompMap_restrict, Category.assoc]
  · rw [Category.assoc, universalThickeningCompMap_over_hom]

include hrZ hrY hiU in
/-- **The morphism `h : Z' ⟶ Y'` of clause (1) of Stacks 06BF commutes with a compatible étale
localization of the pair.**  The morphism of algebraic spaces form of
`AlgebraicGeometry.Space.universalThickeningCompMap_etaleLocalization_hom`. -/
theorem universalThickeningCompMap_etaleLocalization :
    universalThickeningCompMap B S hS iU hZU hYU hfacU ≫ gY =
      gZ ≫ universalThickeningCompMap B S hS i hZ hY hfac :=
  ObjectProperty.hom_ext _
    (universalThickeningCompMap_etaleLocalization_hom B S hS i hZ hY hfac φ gZ rZ hrZ gY rY hrY
      hZU hYU iU hiU hfacU)

include hrZ hrY hiU in
/-- **The localized fibre product is the inverse image of the original one.**  The fibre product
`Y_U ×_{Y'_U} Z'_U` of the localized datum is, as a closed subspace of `Z'_U`, the inverse image
along `gZ` of the fibre product `Y ×_{Y'} Z'` of the original datum.

Both are inverse images of `Y`: the left-hand one along `h_U` then `gY`, the right-hand one along
`gZ` then `h`, and the two composites agree by
`AlgebraicGeometry.Space.universalThickeningCompMap_etaleLocalization_hom`. -/
theorem universalThickeningCompFibreSubspace_etaleLocalization :
    universalThickeningCompFibreSubspace B S hS iU hZU hYU hfacU =
      preimageSubspace B S hS gZ (universalThickeningCompFibreSubspace B S hS i hZ hY hfac) := by
  refine Subtype.ext (preimage_preimage_eq_of_comp_eq Y gY.hom _ _ _ ?_)
  exact universalThickeningCompMap_etaleLocalization_hom B S hS i hZ hY hfac φ gZ rZ hrZ gY rY
    hrY hZU hYU iU hiU hfacU

include hrZ hrY hiU in
/-- **The projection of the localized fibre product onto the original one.**  A morphism
`Y_U ×_{Y'_U} Z'_U ⟶ Y ×_{Y'} Z'` over `gZ`, obtained from the mapping property of the fibre
product `Y ×_{Y'} Z'` applied to the structure morphism of the localized fibre product followed
by the projection `gY⁻¹(Y) ⟶ Y`, and to the inclusion of the localized fibre product followed by
`gZ`.  That the two agree over `Y'` is
`AlgebraicGeometry.Space.universalThickeningCompMap_etaleLocalization_hom`. -/
noncomputable def universalThickeningCompFibreLocalizationProjection :
    (universalThickeningCompFibre B S hS iU hZU hYU hfacU).obj ⟶
      (universalThickeningCompFibre B S hS i hZ hY hfac).obj :=
  (Subfunctor.isPullback_preimage (universalThickeningCompMap B S hS i hZ hY hfac).hom Y).lift
    ((Y.preimage gY.hom).fromPreimage (universalThickeningCompMap B S hS iU hZU hYU hfacU).hom ≫
      Y.fromPreimage gY.hom)
    ((universalThickeningCompFibreSubspace B S hS iU hZU hYU hfacU).1.ι ≫ gZ.hom)
    (by
      calc ((Y.preimage gY.hom).fromPreimage
                (universalThickeningCompMap B S hS iU hZU hYU hfacU).hom ≫
              Y.fromPreimage gY.hom) ≫ Y.ι
          = (Y.preimage gY.hom).fromPreimage
                (universalThickeningCompMap B S hS iU hZU hYU hfacU).hom ≫
              Y.fromPreimage gY.hom ≫ Y.ι := Category.assoc _ _ _
        _ = (Y.preimage gY.hom).fromPreimage
                (universalThickeningCompMap B S hS iU hZU hYU hfacU).hom ≫
              (Y.preimage gY.hom).ι ≫ gY.hom := by rw [Subfunctor.fromPreimage_ι]
        _ = ((Y.preimage gY.hom).fromPreimage
                (universalThickeningCompMap B S hS iU hZU hYU hfacU).hom ≫
              (Y.preimage gY.hom).ι) ≫ gY.hom := (Category.assoc _ _ _).symm
        _ = ((universalThickeningCompFibreSubspace B S hS iU hZU hYU hfacU).1.ι ≫
              (universalThickeningCompMap B S hS iU hZU hYU hfacU).hom) ≫ gY.hom := by
            rw [Subfunctor.fromPreimage_ι]
        _ = (universalThickeningCompFibreSubspace B S hS iU hZU hYU hfacU).1.ι ≫
              (universalThickeningCompMap B S hS iU hZU hYU hfacU).hom ≫ gY.hom :=
            Category.assoc _ _ _
        _ = (universalThickeningCompFibreSubspace B S hS iU hZU hYU hfacU).1.ι ≫
              gZ.hom ≫ (universalThickeningCompMap B S hS i hZ hY hfac).hom := by
            rw [universalThickeningCompMap_etaleLocalization_hom B S hS i hZ hY hfac φ gZ rZ hrZ
              gY rY hrY hZU hYU iU hiU hfacU]
        _ = ((universalThickeningCompFibreSubspace B S hS iU hZU hYU hfacU).1.ι ≫ gZ.hom) ≫
              (universalThickeningCompMap B S hS i hZ hY hfac).hom :=
            (Category.assoc _ _ _).symm)

include hrZ hrY hiU in
/-- The projection of the localized fibre product onto the original one lies over `gZ`. -/
theorem universalThickeningCompFibreLocalizationProjection_ι :
    universalThickeningCompFibreLocalizationProjection B S hS i hZ hY hfac φ gZ rZ hrZ gY rY hrY
          hZU hYU iU hiU hfacU ≫
        (universalThickeningCompFibreSubspace B S hS i hZ hY hfac).1.ι =
      (universalThickeningCompFibreSubspace B S hS iU hZU hYU hfacU).1.ι ≫ gZ.hom :=
  (Subfunctor.isPullback_preimage (universalThickeningCompMap B S hS i hZ hY hfac).hom
    Y).lift_snd _ _ _

include hrZ hrY hiU in
/-- The projection of the localized fibre product onto the original one is compatible with the
two structure morphisms of Stacks 06BF, clause (1): it carries the structure morphism of the
localized fibre product to `Y` over the projection `gY⁻¹(Y) ⟶ Y`. -/
theorem universalThickeningCompFibreLocalizationProjection_structure :
    universalThickeningCompFibreLocalizationProjection B S hS i hZ hY hfac φ gZ rZ hrZ gY rY hrY
          hZU hYU iU hiU hfacU ≫
        (universalThickeningCompStructure B S hS i hZ hY hfac).hom =
      (universalThickeningCompStructure B S hS iU hZU hYU hfacU).hom ≫
        Y.fromPreimage gY.hom :=
  (Subfunctor.isPullback_preimage (universalThickeningCompMap B S hS i hZ hY hfac).hom
    Y).lift_fst _ _ _

include hrZ hrY hiU in
/-- **The localized fibre product sits in a cartesian square over `gZ`.**  The projection onto
the original fibre product, the two inclusions and `gZ` form a fibre product square: the
localized fibre product is the inverse image of the original one by
`AlgebraicGeometry.Space.universalThickeningCompFibreSubspace_etaleLocalization`, and the
projection is then forced to be the canonical one, the inclusion of a subfunctor being a
monomorphism. -/
theorem isPullback_universalThickeningCompFibreLocalizationProjection :
    IsPullback (universalThickeningCompFibreLocalizationProjection B S hS i hZ hY hfac φ gZ rZ
        hrZ gY rY hrY hZU hYU iU hiU hfacU)
      (universalThickeningCompFibreSubspace B S hS iU hZU hYU hfacU).1.ι
      (universalThickeningCompFibreSubspace B S hS i hZ hY hfac).1.ι gZ.hom :=
  isPullback_of_preimage_eq (universalThickeningCompFibreSubspace B S hS i hZ hY hfac).1 gZ.hom
    (universalThickeningCompFibreSubspace B S hS iU hZU hYU hfacU).1
    (congrArg Subtype.val (universalThickeningCompFibreSubspace_etaleLocalization B S hS i hZ hY
      hfac φ gZ rZ hrZ gY rY hrY hZU hYU iU hiU hfacU))
    _
    (universalThickeningCompFibreLocalizationProjection_ι B S hS i hZ hY hfac φ gZ rZ hrZ gY rY
      hrY hZU hYU iU hiU hfacU)

include hrZ hrY hiU in
/-- **The projection of the localized fibre product onto the original one is étale**, being a
base change of the étale `gZ` along the inclusion of the original fibre product into `Z'`. -/
theorem isEtale_universalThickeningCompFibreLocalizationProjection
    (hgZ : IsEtale B S hS gZ.hom) :
    IsEtale B S hS (universalThickeningCompFibreLocalizationProjection B S hS i hZ hY hfac φ gZ
      rZ hrZ gY rY hrY hZU hYU iU hiU hfacU) := by
  have hsqS : IsPullback
      (ObjectProperty.homMk (universalThickeningCompFibreLocalizationProjection B S hS i hZ hY
          hfac φ gZ rZ hrZ gY rY hrY hZU hYU iU hiU hfacU) :
        universalThickeningCompFibre B S hS iU hZU hYU hfacU ⟶
          universalThickeningCompFibre B S hS i hZ hY hfac)
      (universalThickeningCompFibreInclusion B S hS iU hZU hYU hfacU)
      (universalThickeningCompFibreInclusion B S hS i hZ hY hfac) gZ :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι (IsAlgebraicSpace B S hS))
      (isPullback_universalThickeningCompFibreLocalizationProjection B S hS i hZ hY hfac φ gZ rZ
        hrZ gY rY hrY hZU hYU iU hiU hfacU)
  exact isEtale_of_isPullback B S hS _ _ gZ _ hsqS.flip hgZ

include hrZ hrY hiU in
/-- **The copy of `Z` inside the localized fibre product is the inverse image of the copy of `Z`
inside the original one**, along the projection of the two fibre products.

Both are inverse images of `Z`: the left-hand one along the inclusion of the localized fibre
product then `gZ`, the right-hand one along the projection then the inclusion of the original
fibre product, and the two composites agree by
`AlgebraicGeometry.Space.universalThickeningCompFibreLocalizationProjection_ι`.

This is the statement that the space the conormal sequence of the composition is read on
localizes over the chart. -/
theorem universalThickeningCompSub_etaleLocalization :
    universalThickeningCompSub B S hS iU hZU hYU hfacU =
      (universalThickeningCompSub B S hS i hZ hY hfac).preimage
        (universalThickeningCompFibreLocalizationProjection B S hS i hZ hY hfac φ gZ rZ hrZ gY rY
          hrY hZU hYU iU hiU hfacU) := by
  exact preimage_preimage_eq_of_comp_eq Z gZ.hom _ _ _
    (universalThickeningCompFibreLocalizationProjection_ι B S hS i hZ hY hfac φ gZ rZ hrZ gY rY
      hrY hZU hYU iU hiU hfacU).symm

end AlgebraicGeometry.Space

end
