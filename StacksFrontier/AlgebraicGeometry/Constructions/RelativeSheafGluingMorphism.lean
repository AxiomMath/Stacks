module

public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeSheafGluing

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
  **the sheaf half of the functoriality of relative gluing.** A compatible family `τᵢ` gives a
  morphism `h⁎𝒢 ⟶ ℱ` restricting back to the `τᵢ`.

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

/-- **Stacks Project, Tag 01LK.** *Functoriality of relative gluing for quasi-coherent sheaves.*
Let `𝒰` be a locally directed open cover of a scheme `S` and let `dX`, `dY` be relative gluing
data over it, carrying compatible families of quasi-coherent modules realized by `ℱ` on the glued
scheme `X` and `𝒢` on the glued scheme `Y`. Given a family of morphisms `hᵢ : Xᵢ ⟶ Yᵢ` commuting
with the restriction maps — hence the morphism `h = colimMap` of glued schemes — and morphisms
`τᵢ : hᵢ⁎𝒢ᵢ ⟶ ℱᵢ` compatible with the transition isomorphisms of the two families, there is a
morphism `h⁎𝒢 ⟶ ℱ` whose inverse image on the `i`-th chart is `τᵢ`, read through the canonical
identifications.

The companion half of the remark — that `h` is a morphism over `S` restricting to the given `hᵢ`
— is `CategoryTheory.Limits.ι_colimMap` together with
`AlgebraicGeometry.CompatibleRelativeGluingData.colimMap_localHom_toBase`. -/
@[stacks 01LK "sheaf_morphism"]
theorem exists_pullbackHom_of_transitionCompatible (hom : dX.functor ⟶ dY.functor)
    (A : DX.Realization) (B : DY.Realization)
    (τ : ∀ i, (Scheme.Modules.pullback (hom.app i)).obj (DY.obj i) ⟶ DX.obj i)
    (hτ : IsTransitionCompatible hom DX DY τ) :
    ∃ ψ : (Scheme.Modules.pullback (colimMap hom)).obj B.sheaf ⟶ A.sheaf, ∀ i,
      (Scheme.Modules.pullback (colimit.ι dX.functor i)).map ψ =
        pullbackChartHom hom A B τ i :=
  RelativeSheafGluingData.exists_hom_of_chartHom _
    (isChartCompatible_pullbackChartHom hom A B τ hτ)

end Stacks.AlgebraicGeometry.RelativeSheafGluing

end
