module

public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeGluingPairUniqueness
public import StacksFrontier.AlgebraicGeometry.Descent.RelativeGluingOverBasis

/-!
# Functoriality of relative gluing for quasi-coherent sheaves

Fix a locally directed open cover `𝒰` of a scheme `S` and two relative gluing data `dX` and `dY`
over it, with local schemes `Xᵢ` and `Yᵢ`, glued schemes `X` and `Y`, and chart morphisms
`ιᵢ : Xᵢ ⟶ X` and `ι'ᵢ : Yᵢ ⟶ Y`. Let each datum carry a compatible family of quasi-coherent
modules — `ℱᵢ` on `Xᵢ` with transition isomorphisms `θ`, and `𝒢ᵢ` on `Yᵢ` with transition
isomorphisms `η` — realized by modules `ℱ` on `X` and `𝒢` on `Y`.

A family of morphisms `hᵢ : Xᵢ ⟶ Yᵢ` commuting with the restriction maps is a natural
transformation `dX.functor ⟶ dY.functor`, and it induces the morphism `h : X ⟶ Y` of glued
schemes, which is `CategoryTheory.Limits.colimMap`. This file glues the **sheaf** half of that
functoriality: a family of morphisms `τᵢ : hᵢ⁎𝒢ᵢ ⟶ ℱᵢ` compatible with `θ` and `η` comes from a
single morphism `h⁎𝒢 ⟶ ℱ` on the glued scheme, whose inverse image on the `i`-th chart is `τᵢ`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeSheafGluing.chartComparison`: the canonical identification
  `ιᵢ⁎(h⁎𝒢) ≅ hᵢ⁎(ι'ᵢ⁎𝒢)`, the two inverse images along the two factorizations of the composite
  `Xᵢ ⟶ Y`.
* `Stacks.AlgebraicGeometry.RelativeSheafGluing.squareComparison`: the canonical identification
  `(ρᵢⱼ)⁎(hⱼ⁎ -) ≅ hᵢ⁎((σᵢⱼ)⁎ -)` across the naturality square of the family `hᵢ`.
* `Stacks.AlgebraicGeometry.RelativeSheafGluing.pullbackChartHom`: the chart datum built from
  `τᵢ`, a morphism `ιᵢ⁎(h⁎𝒢) ⟶ ιᵢ⁎ℱ`.
* `Stacks.AlgebraicGeometry.RelativeSheafGluing.IsTransitionCompatible`: compatibility of the
  family `τᵢ` with the transition isomorphisms `θ` and `η`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeSheafGluing.exists_pullbackHom_of_transitionCompatible`:
  the sheaf half of the functoriality on the canonical glued schemes. A compatible family `τᵢ`
  gives a morphism `h⁎𝒢 ⟶ ℱ` restricting back to the `τᵢ`.
* `Stacks.AlgebraicGeometry.RelativeSheafGluing.existsUnique_hom_of_chartHomOn`: morphisms of
  modules glue, uniquely, along the charts of an arbitrary gluing.
* `Stacks.AlgebraicGeometry.RelativeSheafGluing.existsUnique_glueHom_and_pullbackHom`:
  **Tag 01LK, both paragraphs**, for arbitrary pairs `(X, ℱ)` and `(Y, 𝒢)` obtained from the
  data of Tag 01LI over a locally directed open cover: the induced morphism `h : X ⟶ Y` restricts
  back to the `hᵢ`, lies over `S` and is unique as such, and there is a unique morphism
  `h⁎𝒢 ⟶ ℱ` restricting back to the `τᵢ`.
* `Stacks.AlgebraicGeometry.RelativeSheafGluing.existsUnique_glueHom_and_pullbackHom_basis`: the
  same for data indexed by a basis of the topology of `S`, as in the source.

## Implementation notes

The scheme half of the same functoriality is
`AlgebraicGeometry.CompatibleRelativeGluingData.colimMap_localHom_toBase` together with
`CategoryTheory.Limits.colimMap` and `CategoryTheory.Limits.ι_colimMap`: the induced morphism of
glued schemes, the fact that it restricts to the given `hᵢ`, and the fact that it lies over the
base. Nothing here repeats that; the morphism of modules is glued over the same `h`.

The gluing step itself is
`Stacks.AlgebraicGeometry.RelativeSheafGluing.RelativeSheafGluingData.exists_hom_of_chartHom`,
which is stated for an arbitrary pair of modules on the glued scheme precisely so that it can be
used here with the pair `h⁎𝒢` and `ℱ`. What this file supplies is its hypothesis: that the chart
data built from `τᵢ` agree along the transition maps.

**Where the work is.** Deriving that hypothesis from the compatibility of `τ` with `θ` and `η`
needs, besides the two `Realization.compatible` squares, one identity between canonical
comparisons alone: the two ways of comparing `(ρᵢⱼ)⁎(ιⱼ⁎(h⁎𝒢))` with `hᵢ⁎(ι'ᵢ⁎𝒢)` agree, one
going through `ιᵢ⁎(h⁎𝒢)` and the other through `hᵢ⁎((σᵢⱼ)⁎(ι'ⱼ⁎𝒢))`. Both are comparisons of
iterated inverse images along chains of morphisms whose composites agree, so the identity is
pseudofunctoriality, and it is assembled from three instances of
`Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp` — the cocycle condition for a chain of three
morphisms. Writing every comparison as
`Stacks.AlgebraicGeometry.ModuleLimits.canHom`, which bundles
`AlgebraicGeometry.Scheme.Modules.pullbackComp` with the congruence along the equality of
composites, is what makes that assembly a sequence of rewrites: the comparison occurring in
`RelativeSheafGluingData.IsChartCompatible` and in `Realization.compatible` is literally `canHom`
at the colimit cocone equation.

The hypothesis that each `hᵢ` is a morphism over the `i`-th member of the cover is not needed for
the morphism of modules and is therefore not assumed.

## References

* [Stacks Project, Tag 01LI](https://stacks.math.columbia.edu/tag/01LI)
* [Stacks Project, Tag 01LK](https://stacks.math.columbia.edu/tag/01LK)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits

namespace Stacks.AlgebraicGeometry.RelativeSheafGluing

variable {S : Scheme.{u}} {𝒰 : S.OpenCover} [Category 𝒰.I₀] [𝒰.LocallyDirected]
  [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
  {dX dY : Scheme.Cover.RelativeGluingData 𝒰}

/-! ### The two factorizations of a chart into the glued target -/

/-- The composite `Xᵢ ⟶ X ⟶ Y` of the `i`-th chart of the source with the induced morphism of
glued schemes. -/
abbrev chartToTarget (hom : dX.functor ⟶ dY.functor) (i : 𝒰.I₀) :
    dX.functor.obj i ⟶ dY.glued :=
  colimit.ι dX.functor i ≫ colimMap hom

/-- The other factorization of `Xᵢ ⟶ Y`: first the local morphism `hᵢ`, then the `i`-th chart of
the target. -/
lemma chartToTarget_eq (hom : dX.functor ⟶ dY.functor) (i : 𝒰.I₀) :
    hom.app i ≫ colimit.ι dY.functor i = chartToTarget hom i :=
  (ι_colimMap hom i).symm

/-- The diagonal `Xᵢ ⟶ Yⱼ` of the naturality square of the family `hᵢ`, taken through `Xⱼ`. -/
abbrev squareComposite (hom : dX.functor ⟶ dY.functor) {i j : 𝒰.I₀} (hij : i ⟶ j) :
    dX.functor.obj i ⟶ dY.functor.obj j :=
  dX.functor.map hij ≫ hom.app j

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- The other factorization of the diagonal `Xᵢ ⟶ Yⱼ`, taken through `Yᵢ`. -/
lemma squareComposite_eq (hom : dX.functor ⟶ dY.functor) {i j : 𝒰.I₀} (hij : i ⟶ j) :
    hom.app i ≫ dY.functor.map hij = squareComposite hom hij :=
  (hom.naturality hij).symm

/-- The diagonal followed by the `j`-th chart of the target is the composite `Xᵢ ⟶ Y`. -/
private lemma squareComposite_comp_ι (hom : dX.functor ⟶ dY.functor) {i j : 𝒰.I₀}
    (hij : i ⟶ j) :
    squareComposite hom hij ≫ colimit.ι dY.functor j = chartToTarget hom i := by
  rw [← squareComposite_eq, Category.assoc, colimit.w, chartToTarget_eq]

/-- The transition morphism of the source followed by the composite `Xⱼ ⟶ Y` is the composite
`Xᵢ ⟶ Y`. -/
private lemma map_comp_chartToTarget (hom : dX.functor ⟶ dY.functor) {i j : 𝒰.I₀}
    (hij : i ⟶ j) :
    dX.functor.map hij ≫ chartToTarget hom j = chartToTarget hom i := by
  rw [chartToTarget, ← Category.assoc, colimit.w]

/-! ### The comparison isomorphisms and the chart datum -/

variable {DX : RelativeSheafGluingData dX} {DY : RelativeSheafGluingData dY}

/-- The canonical identification of the inverse image of `h⁎𝒢` on the `i`-th chart of the source
with the inverse image along `hᵢ` of the inverse image of `𝒢` on the `i`-th chart of the target.
Both are inverse images along the composite `Xᵢ ⟶ Y`, read through its two factorizations. -/
def chartComparison (hom : dX.functor ⟶ dY.functor) (B : DY.Realization) (i : 𝒰.I₀) :
    (Scheme.Modules.pullback (colimit.ι dX.functor i)).obj
        ((Scheme.Modules.pullback (colimMap hom)).obj B.sheaf) ≅
      (Scheme.Modules.pullback (hom.app i)).obj
        ((Scheme.Modules.pullback (colimit.ι dY.functor i)).obj B.sheaf) :=
  canIso (colimit.ι dX.functor i) (colimMap hom) (chartToTarget hom i) rfl B.sheaf ≪≫
    (canIso (hom.app i) (colimit.ι dY.functor i) (chartToTarget hom i)
      (chartToTarget_eq hom i) B.sheaf).symm

/-- The canonical identification across the naturality square of the family `hᵢ`: the inverse
image along the transition morphism of the source of the inverse image along `hⱼ`, compared with
the inverse image along `hᵢ` of the inverse image along the transition morphism of the target.
Both are inverse images along the diagonal `Xᵢ ⟶ Yⱼ`. -/
def squareComparison (hom : dX.functor ⟶ dY.functor) {i j : 𝒰.I₀} (hij : i ⟶ j)
    (P : (dY.functor.obj j).Modules) :
    (Scheme.Modules.pullback (dX.functor.map hij)).obj
        ((Scheme.Modules.pullback (hom.app j)).obj P) ≅
      (Scheme.Modules.pullback (hom.app i)).obj
        ((Scheme.Modules.pullback (dY.functor.map hij)).obj P) :=
  canIso (dX.functor.map hij) (hom.app j) (squareComposite hom hij) rfl P ≪≫
    (canIso (hom.app i) (dY.functor.map hij) (squareComposite hom hij)
      (squareComposite_eq hom hij) P).symm

/-- The chart datum attached to a family `τᵢ : hᵢ⁎𝒢ᵢ ⟶ ℱᵢ`: the morphism
`ιᵢ⁎(h⁎𝒢) ⟶ ιᵢ⁎ℱ` obtained by identifying the source with `hᵢ⁎(ι'ᵢ⁎𝒢)`, then with `hᵢ⁎𝒢ᵢ`
through the local identification of `𝒢`, applying `τᵢ`, and identifying `ℱᵢ` with `ιᵢ⁎ℱ`. -/
def pullbackChartHom (hom : dX.functor ⟶ dY.functor) (A : DX.Realization) (B : DY.Realization)
    (τ : ∀ i, (Scheme.Modules.pullback (hom.app i)).obj (DY.obj i) ⟶ DX.obj i) (i : 𝒰.I₀) :
    (Scheme.Modules.pullback (colimit.ι dX.functor i)).obj
        ((Scheme.Modules.pullback (colimMap hom)).obj B.sheaf) ⟶
      (Scheme.Modules.pullback (colimit.ι dX.functor i)).obj A.sheaf :=
  (chartComparison hom B i).hom ≫
    (Scheme.Modules.pullback (hom.app i)).map (B.localIso i).inv ≫ τ i ≫ (A.localIso i).hom

/-- **Compatibility of a family `τᵢ : hᵢ⁎𝒢ᵢ ⟶ ℱᵢ` with the transition isomorphisms.** Along an
arrow `i ⟶ j` of the cover, pulling `τⱼ` back along the transition morphism of the source and
following it with the transition isomorphism of `ℱ` agrees with passing across the naturality
square of `hᵢ`, applying the transition isomorphism of `𝒢`, and then `τᵢ`. -/
def IsTransitionCompatible (hom : dX.functor ⟶ dY.functor) (DX : RelativeSheafGluingData dX)
    (DY : RelativeSheafGluingData dY)
    (τ : ∀ i, (Scheme.Modules.pullback (hom.app i)).obj (DY.obj i) ⟶ DX.obj i) : Prop :=
  ∀ {i j : 𝒰.I₀} (hij : i ⟶ j),
    (Scheme.Modules.pullback (dX.functor.map hij)).map (τ j) ≫ (DX.transitionIso hij).hom =
      (squareComparison hom hij (DY.obj j)).hom ≫
        (Scheme.Modules.pullback (hom.app i)).map (DY.transitionIso hij).hom ≫ τ i

/-! ### Formal properties of the comparisons -/

/-- The inverse of the canonical comparison of an iterated inverse image is natural in the
module. -/
private lemma canIso_inv_naturality {W Z X : Scheme.{u}} (q : W ⟶ Z) (g : Z ⟶ X) (pi : W ⟶ X)
    (hpi : q ≫ g = pi) {M M' : X.Modules} (ψ : M ⟶ M') :
    (canIso q g pi hpi M).inv ≫
        (Scheme.Modules.pullback q).map ((Scheme.Modules.pullback g).map ψ) =
      (Scheme.Modules.pullback pi).map ψ ≫ (canIso q g pi hpi M').inv := by
  rw [Iso.inv_comp_eq, canIso_hom, ← Category.assoc, ← canHom_naturality, Category.assoc,
    ← canIso_hom, Iso.hom_inv_id, Category.comp_id]

/-- The chart comparison, followed by the canonical comparison on the target side, is the
canonical comparison on the source side. -/
@[reassoc]
private lemma chartComparison_hom_comp (hom : dX.functor ⟶ dY.functor) (B : DY.Realization)
    (i : 𝒰.I₀) :
    (chartComparison hom B i).hom ≫
        canHom (hom.app i) (colimit.ι dY.functor i) (chartToTarget hom i)
          (chartToTarget_eq hom i) B.sheaf =
      canHom (colimit.ι dX.functor i) (colimMap hom) (chartToTarget hom i) rfl B.sheaf := by
  rw [chartComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc, ← canIso_hom,
    Iso.inv_hom_id, Category.comp_id, canIso_hom]

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- The square comparison, followed by the canonical comparison on the target side, is the
canonical comparison on the source side. -/
@[reassoc]
private lemma squareComparison_hom_comp (hom : dX.functor ⟶ dY.functor) {i j : 𝒰.I₀}
    (hij : i ⟶ j) (P : (dY.functor.obj j).Modules) :
    (squareComparison hom hij P).hom ≫
        canHom (hom.app i) (dY.functor.map hij) (squareComposite hom hij)
          (squareComposite_eq hom hij) P =
      canHom (dX.functor.map hij) (hom.app j) (squareComposite hom hij) rfl P := by
  rw [squareComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc, ← canIso_hom,
    Iso.inv_hom_id, Category.comp_id, canIso_hom]

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- The square comparison is natural in the module. -/
@[reassoc]
private lemma squareComparison_hom_naturality (hom : dX.functor ⟶ dY.functor) {i j : 𝒰.I₀}
    (hij : i ⟶ j) {P Q : (dY.functor.obj j).Modules} (u : P ⟶ Q) :
    (squareComparison hom hij P).hom ≫
        (Scheme.Modules.pullback (hom.app i)).map
          ((Scheme.Modules.pullback (dY.functor.map hij)).map u) =
      (Scheme.Modules.pullback (dX.functor.map hij)).map
          ((Scheme.Modules.pullback (hom.app j)).map u) ≫
        (squareComparison hom hij Q).hom := by
  rw [squareComparison, squareComparison, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    Iso.symm_hom, Category.assoc, canIso_inv_naturality, canIso_hom, canIso_hom,
    ← Category.assoc, ← Category.assoc, canHom_naturality]

/-- The local identifications of a realization, read against the canonical comparison: the
transition isomorphism of the datum is what the local identification of the glued module becomes
on passing from the `j`-th to the `i`-th chart. -/
private lemma canHom_comp_localIso_inv (B : DY.Realization) {i j : 𝒰.I₀} (hij : i ⟶ j) :
    canHom (dY.functor.map hij) (colimit.ι dY.functor j) (colimit.ι dY.functor i)
        (colimit.w dY.functor hij) B.sheaf ≫ (B.localIso i).inv =
      (Scheme.Modules.pullback (dY.functor.map hij)).map (B.localIso j).inv ≫
        (DY.transitionIso hij).hom := by
  rw [Iso.comp_inv_eq, Category.assoc, B.compatible hij, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rfl

/-- **The coherence the gluing rests on.** The two ways of comparing the inverse image of `h⁎𝒢`
along the transition morphism of the source composed with the `j`-th chart, with the inverse image
along `hᵢ` of the inverse image of `𝒢` on the `i`-th chart of the target, agree: one route passes
through the `i`-th chart of the source, the other across the naturality square of `hᵢ` and then
along the transition morphism of the target. Both sides are comparisons of iterated inverse images
along chains whose composites agree, and the identity is three instances of the cocycle condition
`Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp`. -/
@[reassoc]
private lemma chartComparison_compat (hom : dX.functor ⟶ dY.functor) (B : DY.Realization)
    {i j : 𝒰.I₀} (hij : i ⟶ j) :
    canHom (dX.functor.map hij) (colimit.ι dX.functor j) (colimit.ι dX.functor i)
        (colimit.w dX.functor hij)
        ((Scheme.Modules.pullback (colimMap hom)).obj B.sheaf) ≫
        (chartComparison hom B i).hom =
      (Scheme.Modules.pullback (dX.functor.map hij)).map (chartComparison hom B j).hom ≫
        (squareComparison hom hij
            ((Scheme.Modules.pullback (colimit.ι dY.functor j)).obj B.sheaf)).hom ≫
          (Scheme.Modules.pullback (hom.app i)).map
            (canHom (dY.functor.map hij) (colimit.ι dY.functor j) (colimit.ι dY.functor i)
              (colimit.w dY.functor hij) B.sheaf) := by
  have h1 := canHom_comp (dX.functor.map hij) (colimit.ι dX.functor j) (colimMap hom)
    (colimit.ι dX.functor i) (chartToTarget hom j) (chartToTarget hom i)
    (colimit.w dX.functor hij) rfl rfl (map_comp_chartToTarget hom hij) B.sheaf
  have h2 := canHom_comp (dX.functor.map hij) (hom.app j) (colimit.ι dY.functor j)
    (squareComposite hom hij) (chartToTarget hom j) (chartToTarget hom i) rfl
    (chartToTarget_eq hom j) (squareComposite_comp_ι hom hij)
    (map_comp_chartToTarget hom hij) B.sheaf
  have h3 := canHom_comp (hom.app i) (dY.functor.map hij) (colimit.ι dY.functor j)
    (squareComposite hom hij) (colimit.ι dY.functor i) (chartToTarget hom i)
    (squareComposite_eq hom hij) (colimit.w dY.functor hij)
    (squareComposite_comp_ι hom hij) (chartToTarget_eq hom i) B.sheaf
  rw [← cancel_mono (canHom (hom.app i) (colimit.ι dY.functor i) (chartToTarget hom i)
    (chartToTarget_eq hom i) B.sheaf)]
  simp only [Category.assoc]
  rw [chartComparison_hom_comp, ← h1, h3, squareComparison_hom_comp_assoc, ← h2,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, chartComparison_hom_comp]

/-- `canHom_comp_localIso_inv` after applying the inverse image along `hᵢ`. -/
@[reassoc]
private lemma map_canHom_comp_map_localIso_inv (hom : dX.functor ⟶ dY.functor)
    (B : DY.Realization) {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (Scheme.Modules.pullback (hom.app i)).map
          (canHom (dY.functor.map hij) (colimit.ι dY.functor j) (colimit.ι dY.functor i)
            (colimit.w dY.functor hij) B.sheaf) ≫
        (Scheme.Modules.pullback (hom.app i)).map (B.localIso i).inv =
      (Scheme.Modules.pullback (hom.app i)).map
          ((Scheme.Modules.pullback (dY.functor.map hij)).map (B.localIso j).inv) ≫
        (Scheme.Modules.pullback (hom.app i)).map (DY.transitionIso hij).hom := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    canHom_comp_localIso_inv]

/-- The compatibility square of a realization, with its comparison written as `canHom`. -/
private lemma realization_compatible_canHom (A : DX.Realization) {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (DX.transitionIso hij).hom ≫ (A.localIso i).hom =
      (Scheme.Modules.pullback (dX.functor.map hij)).map (A.localIso j).hom ≫
        canHom (dX.functor.map hij) (colimit.ι dX.functor j) (colimit.ι dX.functor i)
          (colimit.w dX.functor hij) A.sheaf :=
  A.compatible hij

/-! ### The glued morphism -/

/-- **The chart data built from a compatible family `τ` agree along the transition maps.** This
is the hypothesis of
`Stacks.AlgebraicGeometry.RelativeSheafGluing.RelativeSheafGluingData.exists_hom_of_chartHom` for
the pair `h⁎𝒢`, `ℱ`. -/
private lemma isChartCompatible_pullbackChartHom (hom : dX.functor ⟶ dY.functor)
    (A : DX.Realization) (B : DY.Realization)
    (τ : ∀ i, (Scheme.Modules.pullback (hom.app i)).obj (DY.obj i) ⟶ DX.obj i)
    (hτ : IsTransitionCompatible hom DX DY τ) :
    RelativeSheafGluingData.IsChartCompatible (pullbackChartHom hom A B τ) := by
  intro i j hij
  have hT : (Scheme.Modules.pullback (dX.functor.map hij)).map (τ j) ≫
        (DX.transitionIso hij).hom ≫ (A.localIso i).hom =
      (squareComparison hom hij (DY.obj j)).hom ≫
        (Scheme.Modules.pullback (hom.app i)).map (DY.transitionIso hij).hom ≫ τ i ≫
          (A.localIso i).hom := by
    rw [← Category.assoc, hτ hij]
    simp only [Category.assoc]
  change canHom (dX.functor.map hij) (colimit.ι dX.functor j) (colimit.ι dX.functor i)
        (colimit.w dX.functor hij)
        ((Scheme.Modules.pullback (colimMap hom)).obj B.sheaf) ≫
      pullbackChartHom hom A B τ i =
    (Scheme.Modules.pullback (dX.functor.map hij)).map (pullbackChartHom hom A B τ j) ≫
      canHom (dX.functor.map hij) (colimit.ι dX.functor j) (colimit.ι dX.functor i)
        (colimit.w dX.functor hij) A.sheaf
  simp only [pullbackChartHom, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [chartComparison_compat_assoc, map_canHom_comp_map_localIso_inv_assoc,
    squareComparison_hom_naturality_assoc, ← realization_compatible_canHom, ← hT]

/-- *Functoriality of relative gluing for quasi-coherent sheaves, on the canonical glued schemes.*
Let `𝒰` be a locally directed open cover of a scheme `S` and let `dX`, `dY` be relative gluing
data over it, carrying compatible families of quasi-coherent modules realized by `ℱ` on the glued
scheme `X` and `𝒢` on the glued scheme `Y`. Given a family of morphisms `hᵢ : Xᵢ ⟶ Yᵢ` commuting
with the restriction maps — hence the morphism `h = colimMap` of glued schemes — and morphisms
`τᵢ : hᵢ⁎𝒢ᵢ ⟶ ℱᵢ` compatible with the transition isomorphisms of the two families, there is a
morphism `h⁎𝒢 ⟶ ℱ` whose inverse image on the `i`-th chart is `τᵢ`, read through the canonical
identifications.

The whole remark, for both paragraphs, on arbitrary pairs obtained from the data and with
uniqueness of both induced morphisms, is
`Stacks.AlgebraicGeometry.RelativeSheafGluing.existsUnique_glueHom_and_pullbackHom`. -/
theorem exists_pullbackHom_of_transitionCompatible (hom : dX.functor ⟶ dY.functor)
    (A : DX.Realization) (B : DY.Realization)
    (τ : ∀ i, (Scheme.Modules.pullback (hom.app i)).obj (DY.obj i) ⟶ DX.obj i)
    (hτ : IsTransitionCompatible hom DX DY τ) :
    ∃ ψ : (Scheme.Modules.pullback (colimMap hom)).obj B.sheaf ⟶ A.sheaf, ∀ i,
      (Scheme.Modules.pullback (colimit.ι dX.functor i)).map ψ =
        pullbackChartHom hom A B τ i :=
  RelativeSheafGluingData.exists_hom_of_chartHom _
    (isChartCompatible_pullbackChartHom hom A B τ hτ)

/-! ### Gluing morphisms of modules on an arbitrary gluing -/

section Gluing

open AlgebraicGeometry.Scheme.Cover.RelativeGluingData

variable {d : Scheme.Cover.RelativeGluingData 𝒰} (G : Gluing d)

/-- A family of morphisms of the inverse images of two modules on the total space of a gluing `G`,
one over each chart of `G`, compatible with the canonical comparisons along the transition maps.
On the canonical gluing this is `RelativeSheafGluingData.IsChartCompatible`. -/
def IsChartCompatibleOn {M N : G.pt.Modules}
    (c : ∀ i, (Scheme.Modules.pullback (G.chart i)).obj M ⟶
      (Scheme.Modules.pullback (G.chart i)).obj N) : Prop :=
  ∀ {i j : 𝒰.I₀} (hij : i ⟶ j),
    canHom (d.functor.map hij) (G.chart j) (G.chart i) (G.chart_trans hij) M ≫ c i =
      (Scheme.Modules.pullback (d.functor.map hij)).map (c j) ≫
        canHom (d.functor.map hij) (G.chart j) (G.chart i) (G.chart_trans hij) N

/-- The inverse image along a comparison `e` of the canonical gluing with `G`, read on a chart. -/
private lemma map_glue_eq (e : d.glued ≅ G.pt) (he : ∀ i, colimit.ι d.functor i ≫ e.hom = G.chart i)
    {M N : G.pt.Modules} (φ : M ⟶ N) (i : 𝒰.I₀) :
    (Scheme.Modules.pullback (colimit.ι d.functor i)).map
        ((Scheme.Modules.pullback e.hom).map φ) =
      canHom (colimit.ι d.functor i) e.hom (G.chart i) (he i) M ≫
        (Scheme.Modules.pullback (G.chart i)).map φ ≫
          inv (canHom (colimit.ι d.functor i) e.hom (G.chart i) (he i) N) := by
  rw [← Category.assoc, ← canHom_naturality, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- **Morphisms of modules glue along the charts of an arbitrary gluing.** A family of morphisms
of the inverse images of two modules on the total space of a gluing `G`, compatible along the
transition maps, is the family of inverse images of exactly one morphism of the modules.

The existence half is `RelativeSheafGluingData.exists_hom_of_chartHom` moved off the canonical
total space along the comparison of `G` with the canonical gluing; the uniqueness half is
`RelativeSheafGluingData.hom_ext_of_chart_pullbacks` moved the same way. -/
theorem existsUnique_hom_of_chartHomOn {M N : G.pt.Modules}
    (c : ∀ i, (Scheme.Modules.pullback (G.chart i)).obj M ⟶
      (Scheme.Modules.pullback (G.chart i)).obj N)
    (hc : IsChartCompatibleOn G c) :
    ∃! ψ : M ⟶ N, ∀ i, (Scheme.Modules.pullback (G.chart i)).map ψ = c i := by
  obtain ⟨e, he, -⟩ := RelativeSheafGluingData.exists_glued_iso G
  have hff := pullbackFullyFaithful e
  let c' : ∀ i, (Scheme.Modules.pullback (colimit.ι d.functor i)).obj
      ((Scheme.Modules.pullback e.hom).obj M) ⟶
        (Scheme.Modules.pullback (colimit.ι d.functor i)).obj
          ((Scheme.Modules.pullback e.hom).obj N) := fun i =>
    canHom (colimit.ι d.functor i) e.hom (G.chart i) (he i) M ≫ c i ≫
      inv (canHom (colimit.ι d.functor i) e.hom (G.chart i) (he i) N)
  have hc'i : ∀ i, c' i = canHom (colimit.ι d.functor i) e.hom (G.chart i) (he i) M ≫ c i ≫
      inv (canHom (colimit.ι d.functor i) e.hom (G.chart i) (he i) N) := fun _ => rfl
  have hc' : RelativeSheafGluingData.IsChartCompatible c' := by
    intro i j hij
    have hN := canHom_comp (d.functor.map hij) (colimit.ι d.functor j) e.hom
      (colimit.ι d.functor i) (G.chart j) (G.chart i) (colimit.w d.functor hij) (he j) (he i)
      (G.chart_trans hij) N
    have hN' : canHom (d.functor.map hij) (G.chart j) (G.chart i) (G.chart_trans hij) N ≫
          inv (canHom (colimit.ι d.functor i) e.hom (G.chart i) (he i) N) =
        inv ((Scheme.Modules.pullback (d.functor.map hij)).map
            (canHom (colimit.ι d.functor j) e.hom (G.chart j) (he j) N)) ≫
          canHom (d.functor.map hij) (colimit.ι d.functor j) (colimit.ι d.functor i)
            (colimit.w d.functor hij) ((Scheme.Modules.pullback e.hom).obj N) := by
      rw [IsIso.comp_inv_eq, Category.assoc, ← hN, IsIso.inv_hom_id_assoc]
    change canHom (d.functor.map hij) (colimit.ι d.functor j) (colimit.ι d.functor i)
        (colimit.w d.functor hij) ((Scheme.Modules.pullback e.hom).obj M) ≫ c' i =
      (Scheme.Modules.pullback (d.functor.map hij)).map (c' j) ≫
        canHom (d.functor.map hij) (colimit.ι d.functor j) (colimit.ι d.functor i)
          (colimit.w d.functor hij) ((Scheme.Modules.pullback e.hom).obj N)
    rw [hc'i, hc'i]
    simp only [Functor.map_comp, Functor.map_inv, Category.assoc]
    rw [← canHom_comp_assoc (d.functor.map hij) (colimit.ι d.functor j) e.hom
      (colimit.ι d.functor i) (G.chart j) (G.chart i) (colimit.w d.functor hij) (he j) (he i)
      (G.chart_trans hij) M, reassoc_of% (hc hij), hN']
  obtain ⟨ψ', hψ'⟩ := RelativeSheafGluingData.exists_hom_of_chartHom c' hc'
  have hmap : (Scheme.Modules.pullback e.hom).map (hff.preimage ψ') = ψ' := hff.map_preimage ψ'
  refine ⟨hff.preimage ψ', fun i => ?_, fun φ hφ => ?_⟩
  · have h := map_glue_eq G e he (hff.preimage ψ') i
    rw [hmap, hψ' i, hc'i i] at h
    exact ((cancel_mono _).1 ((cancel_epi _).1 h)).symm
  · refine hff.map_injective ?_
    rw [hmap]
    refine RelativeSheafGluingData.hom_ext_of_chart_pullbacks _ _ fun i => ?_
    change (Scheme.Modules.pullback (colimit.ι d.functor i)).map
        ((Scheme.Modules.pullback e.hom).map φ) =
      (Scheme.Modules.pullback (colimit.ι d.functor i)).map ψ'
    rw [map_glue_eq G e he φ i, hφ i, hψ' i, hc'i i]

end Gluing

/-! ### The morphism of glued pairs -/

section Pair

open AlgebraicGeometry.Scheme.Cover.RelativeGluingData

variable (hom : dX.functor ⟶ dY.functor) (G : Gluing dX) (G' : Gluing dY)

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- The composites of the local morphisms with the charts of `G'` are compatible with the
transition morphisms of `dX`. -/
lemma glueHom_w {i j : 𝒰.I₀} (hij : i ⟶ j) :
    dX.functor.map hij ≫ hom.app j ≫ G'.chart j = hom.app i ≫ G'.chart i := by
  rw [← Category.assoc, hom.naturality, Category.assoc, G'.chart_trans]

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- **The morphism of total spaces induced by a compatible family of local morphisms.** For
gluings `G` of `dX` and `G'` of `dY` and a family `hᵢ : Xᵢ ⟶ Yᵢ` commuting with the restriction
maps, the morphism `G.pt ⟶ G'.pt` glued from the composites of the `hᵢ` with the charts of
`G'`. -/
def glueHom : G.pt ⟶ G'.pt :=
  G.cover.glueMorphismsOfLocallyDirected (fun i => hom.app i ≫ G'.chart i) fun hij =>
    glueHom_w hom G' hij

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- The glued morphism restricts on the `i`-th chart to the `i`-th local morphism. -/
@[reassoc]
lemma chart_glueHom (i : 𝒰.I₀) : G.chart i ≫ glueHom hom G G' = hom.app i ≫ G'.chart i :=
  G.cover.map_glueMorphismsOfLocallyDirected _ _ i

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- The glued morphism is a morphism over the base when every local morphism is. -/
lemma glueHom_toBase (hover : hom ≫ dY.natTrans = dX.natTrans) :
    glueHom hom G G' ≫ G'.toBase = G.toBase :=
  G.hom_ext _ _ fun i => by
    rw [chart_glueHom_assoc, ← (G'.isPullback_chart i).w, ← (G.isPullback_chart i).w, ← hover]
    exact (Category.assoc _ _ _).symm

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- The glued morphism is the only morphism restricting to the local morphisms. -/
lemma eq_glueHom {k : G.pt ⟶ G'.pt} (hk : ∀ i, G.chart i ≫ k = hom.app i ≫ G'.chart i) :
    k = glueHom hom G G' :=
  G.hom_ext _ _ fun i => by rw [hk i, chart_glueHom]

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- The composite `Xᵢ ⟶ G.pt ⟶ G'.pt` of the `i`-th chart with the glued morphism. -/
abbrev chartToTargetOn (i : 𝒰.I₀) : dX.functor.obj i ⟶ G'.pt :=
  G.chart i ≫ glueHom hom G G'

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- The other factorization of `Xᵢ ⟶ G'.pt`, through `hᵢ`. -/
lemma chartToTargetOn_eq (i : 𝒰.I₀) :
    hom.app i ≫ G'.chart i = chartToTargetOn hom G G' i :=
  (chart_glueHom hom G G' i).symm

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
private lemma squareComposite_comp_chart {i j : 𝒰.I₀} (hij : i ⟶ j) :
    squareComposite hom hij ≫ G'.chart j = chartToTargetOn hom G G' i := by
  rw [← squareComposite_eq, Category.assoc, G'.chart_trans, chartToTargetOn_eq]

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
private lemma map_comp_chartToTargetOn {i j : 𝒰.I₀} (hij : i ⟶ j) :
    dX.functor.map hij ≫ chartToTargetOn hom G G' j = chartToTargetOn hom G G' i := by
  rw [chartToTargetOn, ← Category.assoc, G.chart_trans]

variable {G G'}

/-- The canonical identification of the inverse image of `k⁎𝒢` on the `i`-th chart of `G` with
the inverse image along `hᵢ` of the inverse image of `𝒢` on the `i`-th chart of `G'`, where
`k = glueHom hom G G'`. -/
def chartComparisonOn (R' : DY.RealizationOn G') (i : 𝒰.I₀) :
    (Scheme.Modules.pullback (G.chart i)).obj
        ((Scheme.Modules.pullback (glueHom hom G G')).obj R'.sheaf) ≅
      (Scheme.Modules.pullback (hom.app i)).obj
        ((Scheme.Modules.pullback (G'.chart i)).obj R'.sheaf) :=
  canIso (G.chart i) (glueHom hom G G') (chartToTargetOn hom G G' i) rfl R'.sheaf ≪≫
    (canIso (hom.app i) (G'.chart i) (chartToTargetOn hom G G' i)
      (chartToTargetOn_eq hom G G' i) R'.sheaf).symm

/-- The chart datum attached to a family `τᵢ : hᵢ⁎𝒢ᵢ ⟶ ℱᵢ` on arbitrary gluings: the morphism
`(G.chart i)⁎(k⁎𝒢) ⟶ (G.chart i)⁎ℱ` obtained by identifying the source with
`hᵢ⁎((G'.chart i)⁎𝒢)`, then with `hᵢ⁎𝒢ᵢ` through the local identification of `𝒢`, applying
`τᵢ`, and identifying `ℱᵢ` with `(G.chart i)⁎ℱ`. -/
def pullbackChartHomOn (R : DX.RealizationOn G) (R' : DY.RealizationOn G')
    (τ : ∀ i, (Scheme.Modules.pullback (hom.app i)).obj (DY.obj i) ⟶ DX.obj i) (i : 𝒰.I₀) :
    (Scheme.Modules.pullback (G.chart i)).obj
        ((Scheme.Modules.pullback (glueHom hom G G')).obj R'.sheaf) ⟶
      (Scheme.Modules.pullback (G.chart i)).obj R.sheaf :=
  (chartComparisonOn hom R' i (G := G)).hom ≫
    (Scheme.Modules.pullback (hom.app i)).map (R'.localIso i).inv ≫ τ i ≫ (R.localIso i).hom

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
@[reassoc]
private lemma chartComparisonOn_hom_comp (R' : DY.RealizationOn G') (i : 𝒰.I₀) :
    (chartComparisonOn hom R' i (G := G)).hom ≫
        canHom (hom.app i) (G'.chart i) (chartToTargetOn hom G G' i)
          (chartToTargetOn_eq hom G G' i) R'.sheaf =
      canHom (G.chart i) (glueHom hom G G') (chartToTargetOn hom G G' i) rfl R'.sheaf := by
  rw [chartComparisonOn, Iso.trans_hom, Iso.symm_hom, Category.assoc, ← canIso_hom,
    Iso.inv_hom_id, Category.comp_id, canIso_hom]

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
private lemma canHom_comp_localIsoOn_inv (R' : DY.RealizationOn G') {i j : 𝒰.I₀} (hij : i ⟶ j) :
    canHom (dY.functor.map hij) (G'.chart j) (G'.chart i) (G'.chart_trans hij) R'.sheaf ≫
        (R'.localIso i).inv =
      (Scheme.Modules.pullback (dY.functor.map hij)).map (R'.localIso j).inv ≫
        (DY.transitionIso hij).hom := by
  rw [Iso.comp_inv_eq, Category.assoc, R'.compatible hij, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rfl

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
@[reassoc]
private lemma chartComparisonOn_compat (R' : DY.RealizationOn G') {i j : 𝒰.I₀} (hij : i ⟶ j) :
    canHom (dX.functor.map hij) (G.chart j) (G.chart i) (G.chart_trans hij)
        ((Scheme.Modules.pullback (glueHom hom G G')).obj R'.sheaf) ≫
        (chartComparisonOn hom R' i (G := G)).hom =
      (Scheme.Modules.pullback (dX.functor.map hij)).map
          (chartComparisonOn hom R' j (G := G)).hom ≫
        (squareComparison hom hij
            ((Scheme.Modules.pullback (G'.chart j)).obj R'.sheaf)).hom ≫
          (Scheme.Modules.pullback (hom.app i)).map
            (canHom (dY.functor.map hij) (G'.chart j) (G'.chart i) (G'.chart_trans hij)
              R'.sheaf) := by
  have h1 := canHom_comp (dX.functor.map hij) (G.chart j) (glueHom hom G G')
    (G.chart i) (chartToTargetOn hom G G' j) (chartToTargetOn hom G G' i)
    (G.chart_trans hij) rfl rfl (map_comp_chartToTargetOn hom G G' hij) R'.sheaf
  have h2 := canHom_comp (dX.functor.map hij) (hom.app j) (G'.chart j)
    (squareComposite hom hij) (chartToTargetOn hom G G' j) (chartToTargetOn hom G G' i) rfl
    (chartToTargetOn_eq hom G G' j) (squareComposite_comp_chart hom G G' hij)
    (map_comp_chartToTargetOn hom G G' hij) R'.sheaf
  have h3 := canHom_comp (hom.app i) (dY.functor.map hij) (G'.chart j)
    (squareComposite hom hij) (G'.chart i) (chartToTargetOn hom G G' i)
    (squareComposite_eq hom hij) (G'.chart_trans hij)
    (squareComposite_comp_chart hom G G' hij) (chartToTargetOn_eq hom G G' i) R'.sheaf
  rw [← cancel_mono (canHom (hom.app i) (G'.chart i) (chartToTargetOn hom G G' i)
    (chartToTargetOn_eq hom G G' i) R'.sheaf)]
  simp only [Category.assoc]
  rw [chartComparisonOn_hom_comp, ← h1, h3, squareComparison_hom_comp_assoc, ← h2,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, chartComparisonOn_hom_comp]

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
@[reassoc]
private lemma map_canHom_comp_map_localIsoOn_inv (R' : DY.RealizationOn G') {i j : 𝒰.I₀}
    (hij : i ⟶ j) :
    (Scheme.Modules.pullback (hom.app i)).map
          (canHom (dY.functor.map hij) (G'.chart j) (G'.chart i) (G'.chart_trans hij)
            R'.sheaf) ≫
        (Scheme.Modules.pullback (hom.app i)).map (R'.localIso i).inv =
      (Scheme.Modules.pullback (hom.app i)).map
          ((Scheme.Modules.pullback (dY.functor.map hij)).map (R'.localIso j).inv) ≫
        (Scheme.Modules.pullback (hom.app i)).map (DY.transitionIso hij).hom := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    canHom_comp_localIsoOn_inv]

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
private lemma realizationOn_compatible_canHom (R : DX.RealizationOn G) {i j : 𝒰.I₀}
    (hij : i ⟶ j) :
    (DX.transitionIso hij).hom ≫ (R.localIso i).hom =
      (Scheme.Modules.pullback (dX.functor.map hij)).map (R.localIso j).hom ≫
        canHom (dX.functor.map hij) (G.chart j) (G.chart i) (G.chart_trans hij) R.sheaf :=
  R.compatible hij

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- The chart data built from a compatible family `τ` on arbitrary gluings agree along the
transition maps. -/
private lemma isChartCompatibleOn_pullbackChartHomOn (R : DX.RealizationOn G)
    (R' : DY.RealizationOn G')
    (τ : ∀ i, (Scheme.Modules.pullback (hom.app i)).obj (DY.obj i) ⟶ DX.obj i)
    (hτ : IsTransitionCompatible hom DX DY τ) :
    IsChartCompatibleOn G (pullbackChartHomOn hom R R' τ) := by
  intro i j hij
  have hT : (Scheme.Modules.pullback (dX.functor.map hij)).map (τ j) ≫
        (DX.transitionIso hij).hom ≫ (R.localIso i).hom =
      (squareComparison hom hij (DY.obj j)).hom ≫
        (Scheme.Modules.pullback (hom.app i)).map (DY.transitionIso hij).hom ≫ τ i ≫
          (R.localIso i).hom := by
    rw [← Category.assoc, hτ hij]
    simp only [Category.assoc]
  simp only [pullbackChartHomOn, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [chartComparisonOn_compat_assoc, map_canHom_comp_map_localIsoOn_inv_assoc,
    squareComparison_hom_naturality_assoc, ← realizationOn_compatible_canHom, ← hT]

/-- **Stacks Project, Tag 01LK.** *Functoriality of relative gluing, for schemes and for
quasi-coherent sheaves.* Let `𝒰` be a locally directed open cover of a scheme `S` (for instance the
cover by the members of a basis of the topology of `S`, see
`Stacks.AlgebraicGeometry.RelativeSheafGluing.existsUnique_glueHom_and_pullbackHom_basis`), and
let `(dX, DX)` and `(dY, DY)` be two data as in Tag 01LI: relative gluing data `Xᵢ ⟶ 𝒰ᵢ`,
`Yᵢ ⟶ 𝒰ᵢ` with restriction morphisms `ρ`, `σ`, carrying compatible families of quasi-coherent
modules `ℱᵢ`, `𝒢ᵢ` with transition isomorphisms `θ`, `η`. Let `(G, R)` be a pair
`(f : X ⟶ S, ℱ)` obtained from the first datum and `(G', R')` a pair `(g : Y ⟶ S, 𝒢)` obtained
from the second. Suppose given morphisms `hᵢ : Xᵢ ⟶ Yᵢ` over `𝒰ᵢ` compatible with the
restrictions (the natural transformation `hom` with `hover`), and morphisms
`τᵢ : hᵢ⁎𝒢ᵢ ⟶ ℱᵢ` compatible with `θ` and `η`. Then:

* the morphism of schemes `h = glueHom hom G G' : X ⟶ Y` restricts back to the `hᵢ` on the
  charts, is a morphism over `S`, and is the only morphism restricting back to the `hᵢ`;
* there is exactly one morphism `h⁎𝒢 ⟶ ℱ` restricting back to the `τᵢ` on the charts, read
  through the canonical identifications. -/
@[stacks 01LK "both functoriality assertions of the remark: the induced morphism of glued
schemes over S restricting to the h_U (and unique as such), and the unique induced morphism
h^*G -> F restricting to the tau_U, for arbitrary pairs obtained from the data of Tag 01LI"]
theorem existsUnique_glueHom_and_pullbackHom (hover : hom ≫ dY.natTrans = dX.natTrans)
    (R : DX.RealizationOn G) (R' : DY.RealizationOn G')
    (τ : ∀ i, (Scheme.Modules.pullback (hom.app i)).obj (DY.obj i) ⟶ DX.obj i)
    (hτ : IsTransitionCompatible hom DX DY τ) :
    (∀ i, G.chart i ≫ glueHom hom G G' = hom.app i ≫ G'.chart i) ∧
      glueHom hom G G' ≫ G'.toBase = G.toBase ∧
      (∀ k : G.pt ⟶ G'.pt, (∀ i, G.chart i ≫ k = hom.app i ≫ G'.chart i) →
        k = glueHom hom G G') ∧
      ∃! ψ : (Scheme.Modules.pullback (glueHom hom G G')).obj R'.sheaf ⟶ R.sheaf, ∀ i,
        (Scheme.Modules.pullback (G.chart i)).map ψ = pullbackChartHomOn hom R R' τ i :=
  ⟨chart_glueHom hom G G', glueHom_toBase hom G G' hover, fun _ hk => eq_glueHom hom G G' hk,
    existsUnique_hom_of_chartHomOn G _ (isChartCompatibleOn_pullbackChartHomOn hom R R' τ hτ)⟩

end Pair

/-! ### Over a basis of the topology -/

section Basis

open AlgebraicGeometry.Scheme.Cover.RelativeGluingData
open TopologicalSpace

variable {B : Set S.Opens}

/-- A family of morphisms `h U : D.obj U ⟶ D'.obj U` between the pieces of two gluing data over a
basis, compatible with their restriction morphisms, read as a natural transformation between the
diagrams of pieces. -/
def basisNatTrans (hB : Opens.IsBasis B) (D D' : Scheme.BasisGluingData S B)
    (h : ∀ U : B, D.obj U ⟶ D'.obj U)
    (hcompat : ∀ {V U : B} (hVU : V.1 ≤ U.1), D.res hVU ≫ h U = h V ≫ D'.res hVU) :
    (D.relativeGluingData hB).functor ⟶ (D'.relativeGluingData hB).functor where
  app := h
  naturality _ _ f := hcompat (leOfHom f)

/-- The component of `basisNatTrans` at `U` is `h U`, so the `τ_U` of
`existsUnique_glueHom_and_pullbackHom_basis` are morphisms `h_U⁎𝒢_U ⟶ ℱ_U`. -/
@[simp]
lemma basisNatTrans_app (hB : Opens.IsBasis B) (D D' : Scheme.BasisGluingData S B)
    (h : ∀ U : B, D.obj U ⟶ D'.obj U)
    (hcompat : ∀ {V U : B} (hVU : V.1 ≤ U.1), D.res hVU ≫ h U = h V ≫ D'.res hVU) (U : B) :
    (basisNatTrans hB D D' h hcompat).app U = h U :=
  rfl

/-- **Stacks Project, Tag 01LK, over a basis of the topology.** Let `S` be a scheme and `B` a
basis for its topology. Let `D`, `D'` be gluing data over `B` as in Tag 01LH (local schemes
`f_U : X_U ⟶ U`, `g_U : Y_U ⟶ U` with restriction morphisms `ρ^U_V`, `σ^U_V`), and let `DX`, `DY`
be compatible families of quasi-coherent modules `ℱ_U`, `𝒢_U` on them with transition
isomorphisms `θ^U_V`, `η^U_V`, as in Tag 01LI. Let `(G, R)` be a pair `(f : X ⟶ S, ℱ)` obtained
from the first datum and `(G', R')` a pair `(g : Y ⟶ S, 𝒢)` obtained from the second. Suppose
given morphisms `h_U : X_U ⟶ Y_U` over `U` compatible with the restrictions `ρ^U_V` and
`σ^U_V`, and morphisms `τ_U : h_U⁎𝒢_U ⟶ ℱ_U` compatible with the maps `θ^U_V` and `η^U_V`.
Then the induced morphism of schemes `h : X ⟶ Y` restricts back to the `h_U`, is a morphism over
`S` and is the only morphism restricting back to the `h_U`, and there is exactly one morphism
`h⁎𝒢 ⟶ ℱ` restricting back to the `τ_U`.

This is `Stacks.AlgebraicGeometry.RelativeSheafGluing.existsUnique_glueHom_and_pullbackHom` for
the cover of `S` by the members of `B`. -/
@[stacks 01LK "both functoriality assertions of the remark, for data indexed by a basis of the
topology as in Tags 01LH and 01LI"]
theorem existsUnique_glueHom_and_pullbackHom_basis (hB : Opens.IsBasis B)
    {D D' : Scheme.BasisGluingData S B} {DX : RelativeSheafGluingData (D.relativeGluingData hB)}
    {DY : RelativeSheafGluingData (D'.relativeGluingData hB)}
    (G : Gluing (D.relativeGluingData hB)) (G' : Gluing (D'.relativeGluingData hB))
    (R : DX.RealizationOn G) (R' : DY.RealizationOn G')
    (h : ∀ U : B, D.obj U ⟶ D'.obj U) (hover : ∀ U : B, h U ≫ D'.proj U = D.proj U)
    (hcompat : ∀ {V U : B} (hVU : V.1 ≤ U.1), D.res hVU ≫ h U = h V ≫ D'.res hVU)
    (τ : ∀ U, (Scheme.Modules.pullback ((basisNatTrans hB D D' h hcompat).app U)).obj
      (DY.obj U) ⟶ DX.obj U)
    (hτ : IsTransitionCompatible (dX := D.relativeGluingData hB) (dY := D'.relativeGluingData hB)
      (basisNatTrans hB D D' h hcompat) DX DY τ) :
    (∀ U, G.chart U ≫ glueHom (basisNatTrans hB D D' h hcompat) G G' =
        (basisNatTrans hB D D' h hcompat).app U ≫ G'.chart U) ∧
      glueHom (basisNatTrans hB D D' h hcompat) G G' ≫ G'.toBase = G.toBase ∧
      (∀ k : G.pt ⟶ G'.pt,
        (∀ U, G.chart U ≫ k = (basisNatTrans hB D D' h hcompat).app U ≫ G'.chart U) →
          k = glueHom (basisNatTrans hB D D' h hcompat) G G') ∧
      ∃! ψ : (Scheme.Modules.pullback
          (glueHom (basisNatTrans hB D D' h hcompat) G G')).obj R'.sheaf ⟶ R.sheaf, ∀ U,
        (Scheme.Modules.pullback (G.chart U)).map ψ =
          pullbackChartHomOn (dX := D.relativeGluingData hB) (dY := D'.relativeGluingData hB)
            (basisNatTrans hB D D' h hcompat) R R' τ U :=
  existsUnique_glueHom_and_pullbackHom (dX := D.relativeGluingData hB)
    (dY := D'.relativeGluingData hB) (basisNatTrans hB D D' h hcompat)
    (by ext U; exact hover U) R R' τ hτ

end Basis

end Stacks.AlgebraicGeometry.RelativeSheafGluing

end
