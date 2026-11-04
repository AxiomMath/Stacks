module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FieldSpectrumCoverSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent

/-!
# Quasi-compactness of a field-valued representative of a point (Stacks 0DTK)

A point of an algebraic stack `𝒳` over `S` is an equivalence class of field-valued points
(**Stacks 04XG**), and each field-valued point `p` determines a 1-morphism `Spec k ⟶ 𝒳` by the
2-Yoneda lemma. This file proves **Stacks 0DTK**: quasi-compactness of that 1-morphism depends
only on the class of `p`, so *some* field-valued representative of a point is quasi-compact
exactly when *every* one is.

Two field-valued points of the same point are joined by a third with arrows to both, and an
arrow `g : p.obj ⟶ q.obj` lies over a morphism `Spec k ⟶ Spec k'` of the site which exhibits
the 1-morphism of `p` as the composite of that morphism with the 1-morphism of `q`. The
morphism of the site is quasi-compact, so **Stacks 050W** carries quasi-compactness from `q` to
`p`; it is surjective, the spectrum of a field having one point, so **Stacks 050X** carries
quasi-compactness from `p` to `q`.

## Main definitions

* `AlgebraicGeometry.Stack.fieldValuedPointBaseMap`: the morphism of the big fppf category of
  `S` that an arrow between the objects of two field-valued points lies over.
* `AlgebraicGeometry.Stack.FieldValuedPoint.fieldSpectrum`: the field spectrum underlying a
  field-valued point.
* `AlgebraicGeometry.Stack.schemeStackMap`: the 1-morphism of algebraic stacks over `S` induced
  by a morphism of the big fppf category of `S`.
* `AlgebraicGeometry.Stack.fieldValuedPointMorphismBaseMapIso`: the factorisation of the
  1-morphism of `p` through the 1-morphism of `q` along that morphism of the site.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompact_schemeFibredCategoryMap_of_fieldValuedPointBase`: a
  morphism of the site out of the base of a field-valued point induces a quasi-compact
  1-morphism of represented categories fibred in groupoids, and
  `AlgebraicGeometry.Stack.isQuasiCompactMorphism_schemeStackMap_of_fieldValuedPointBase` the
  same read in the sense of Stacks 050U.
* `AlgebraicGeometry.Stack.isSurjective_of_fieldSpectrum`: every 1-morphism between the
  algebraic stacks of two field spectra is surjective.
* `AlgebraicGeometry.Stack.isQuasiCompactFieldValuedPoint_dom_of_hom` and
  `AlgebraicGeometry.Stack.isQuasiCompactFieldValuedPoint_cod_of_hom`: an arrow of field-valued
  points carries quasi-compactness in both directions.
* `AlgebraicGeometry.Stack.exists_isQuasiCompactFieldValuedPoint_iff_forall`: **Stacks 0DTK**.

## Implementation notes

The factorisation `AlgebraicGeometry.Stack.fieldValuedPointMorphismBaseMapIso` is
`AlgebraicGeometry.Stack.basedFactorIso` — functoriality of the 2-Yoneda 1-morphism of an
object, **Stacks 004B** — read at a field-valued point. That statement places the source of the
1-morphism over the spelling `𝒳.p.obj x` of the base, while a field-valued point records its
base separately together with an equality to that spelling, so the two are reconciled by
substituting the equality, after which the two base objects and the two base morphisms agree
syntactically and no transport along an equality of objects survives in the statement.

Quasi-compactness of the morphism of the site is the Stacks 04XB property of
`AlgebraicGeometry.Stack.schemeFibredCategoryMap`, obtained from
`AlgebraicGeometry.Stack.hasRelativeProperty_schemeFibredCategoryMap`; its locality hypothesis
is `AlgebraicGeometry.Space.isQuasiCompact_isLocalAtTarget_fppf`, supplied locally because it is
a theorem rather than an instance. The underlying morphism of schemes is quasi-compact because
the source is the spectrum of a field, whose space is finite.

The hypothesis that `𝒳` is an algebraic stack is used twice and is not removable: it gives the
representability of the 1-morphism of a field-valued point (**Stacks 045G**), without which
quasi-compactness in the sense of Stacks 04XB is not asserted of a morphism at all, and it puts
the two 1-morphisms in the 2-category of algebraic stacks, where the permanence properties
Stacks 050W and Stacks 050X are available.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 040W](https://stacks.math.columbia.edu/tag/040W)
* [Stacks Project, Tag 045F](https://stacks.math.columbia.edu/tag/045F)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XF](https://stacks.math.columbia.edu/tag/04XF)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 050W](https://stacks.math.columbia.edu/tag/050W)
* [Stacks Project, Tag 050X](https://stacks.math.columbia.edu/tag/050X)
* [Stacks Project, Tag 0DTK](https://stacks.math.columbia.edu/tag/0DTK)
* [Stacks Project, Tag 0GW1](https://stacks.math.columbia.edu/tag/0GW1)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v t w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism of the big fppf category of `S` that an arrow between the objects of two
field-valued points lies over, read on their recorded bases through the two identifications of
a recorded base with the base of the point's object. -/
def fieldValuedPointBaseMap {𝒴 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    {p q : FieldValuedPoint B S hS 𝒴} (g : p.obj ⟶ q.obj) : p.base ⟶ q.base :=
  eqToHom p.over.symm ≫ 𝒴.p.map g ≫ eqToHom q.over

/-- The spectrum of a field underlying a field-valued point: its recorded base, together with
the identification of the underlying scheme of that base with the spectrum of its field. -/
def FieldValuedPoint.fieldSpectrum {𝒴 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    (p : FieldValuedPoint B S hS 𝒴) : FieldSpectrum B S hS where
  carrier := p.carrier
  base := p.base
  isSpec := p.isSpec

/-- The 1-morphism of algebraic stacks over `S` induced by a morphism `g : U ⟶ V` of the big
fppf category of `S`, namely `AlgebraicGeometry.Stack.schemeFibredCategoryMap` read in the
2-category of algebraic stacks. -/
def schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V) :
    schemeStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS V :=
  Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS g)

/-- **Functoriality of the 2-Yoneda 1-morphism at a field-valued point (Stacks 004B).** An arrow
`g : p.obj ⟶ q.obj` between the objects of two field-valued points of a category fibred in
groupoids over the big fppf site of `S` exhibits the 1-morphism `Spec k ⟶ 𝒳` of `p` as the
composite of the morphism of the site that `g` lies over with the 1-morphism `Spec k' ⟶ 𝒳`
of `q`. -/
noncomputable def fieldValuedPointMorphismBaseMapIso
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    {p q : FieldValuedPoint B S hS 𝒳.val} (g : p.obj ⟶ q.obj) :
    (fieldValuedPointMorphism B S hS 𝒳 p).hom ≅
      BasedFunctor.comp (overMapBased B S hS (fieldValuedPointBaseMap B S hS g))
        (fieldValuedPointMorphism B S hS 𝒳 q).hom := by
  simp only [fieldValuedPointBaseMap]
  obtain ⟨_, _, _, _, _, _⟩ := p
  obtain ⟨_, _, _, _, _, _⟩ := q
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact basedFactorIso B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids g

/-- **A morphism of the site out of the base of a field-valued point induces a quasi-compact
1-morphism of represented categories fibred in groupoids.** The base is the spectrum of a field,
so the morphism is quasi-compact on underlying schemes, hence quasi-compact as a morphism of the
representable algebraic spaces (**Stacks 03KG**), and Stacks 03YK at a represented source and
target transports it to the induced 1-morphism. -/
theorem isQuasiCompact_schemeFibredCategoryMap_of_fieldValuedPointBase
    {𝒴 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)} (p : FieldValuedPoint B S hS 𝒴)
    {V : BigFppfOver B S hS} (k : p.base ⟶ V) :
    IsQuasiCompact B S hS (schemeFibredCategoryMap B S hS k) := by
  let _inst : (Space.quasiCompactProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    Space.isQuasiCompact_isLocalAtTarget_fppf B S hS
  exact hasRelativeProperty_schemeFibredCategoryMap.{u, u + 1} B S hS
    (Space.quasiCompactProperty B S hS) k
    (Space.isQuasiCompact_yoneda_map_of_quasiCompact B S hS k
      (quasiCompact_toScheme_map_of_fieldValuedPointBase B S hS p k))

/-- **A morphism of the site out of the base of a field-valued point induces a quasi-compact
1-morphism of algebraic stacks.** This is
`AlgebraicGeometry.Stack.isQuasiCompact_schemeFibredCategoryMap_of_fieldValuedPointBase` read
through **Stacks 050T**, the representability witness being the one of Stacks 02ZZ. -/
theorem isQuasiCompactMorphism_schemeStackMap_of_fieldValuedPointBase
    {𝒴 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)} (p : FieldValuedPoint B S hS 𝒴)
    {V : BigFppfOver B S hS} (k : p.base ⟶ V) :
    IsQuasiCompactMorphism.{u, w} B S hS (schemeStackMap.{u, w} B S hS k) :=
  (isQuasiCompact_iff_baseChange_quasiCompact.{u, w} B S hS (schemeStackMap.{u, w} B S hS k)
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS k)).1
    (isQuasiCompact_schemeFibredCategoryMap_of_fieldValuedPointBase B S hS p k)

/-- **Every 1-morphism between the algebraic stacks of two spectra of fields is surjective.**
The spectrum of a field has exactly one point, so the target has at most one point while the
source has at least one, and `AlgebraicGeometry.Stack.IsSurjective` (**Stacks 04ZS**) is
surjectivity of the map on points. -/
theorem isSurjective_of_fieldSpectrum (F F' : FieldSpectrum B S hS)
    (f : schemeStack.{u, w} B S hS F.base ⟶ schemeStack.{u, w} B S hS F'.base) :
    IsSurjective B S hS f := by
  have : Subsingleton (points B S hS (schemeStack.{u, w} B S hS F'.base).val.val
      (Classical.choose (schemeStack.{u, w} B S hS F'.base).property)) :=
    subsingleton_points_fieldSpectrumStack.{u, w} B S hS F'
  obtain ⟨z⟩ := nonempty_points_fieldSpectrumStack.{u, w} B S hS F
  exact fun _ => ⟨z, Subsingleton.elim _ _⟩

/-- **The domain of an arrow of field-valued points of an algebraic stack inherits
quasi-compactness from its codomain.** The 1-morphism of the domain is the composite of the
morphism of the site the arrow lies over with the 1-morphism of the codomain; the first factor
is quasi-compact because its source is the spectrum of a field, and **Stacks 050W** composes
the two. -/
theorem isQuasiCompactFieldValuedPoint_dom_of_hom (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {p q : FieldValuedPoint B S hS 𝒳.val.val} (g : p.obj ⟶ q.obj)
    (hq : IsQuasiCompactFieldValuedPoint B S hS 𝒳.val q) :
    IsQuasiCompactFieldValuedPoint B S hS 𝒳.val p := by
  have hrep := isRepresentableByAlgebraicSpaces_fieldValuedPointMorphism B S hS 𝒳 p
  have hiso := fieldValuedPointMorphismBaseMapIso B S hS 𝒳.val g
  have hcomp := isQuasiCompactMorphism_comp B S hS
    (schemeStackMap.{u, w} B S hS (fieldValuedPointBaseMap B S hS g))
    (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 q)
    (isQuasiCompactMorphism_schemeStackMap_of_fieldValuedPointBase.{u, w} B S hS p
      (fieldValuedPointBaseMap B S hS g))
    ((isQuasiCompactFieldValuedPoint_iff_isQuasiCompactMorphism B S hS 𝒳 q).1 hq)
  have hrepcomp := isRepresentableByAlgebraicSpaces_of_basedIso B S hS
    (fieldValuedPointMorphism B S hS 𝒳.val p)
    (schemeStackMap.{u, w} B S hS (fieldValuedPointBaseMap B S hS g) ≫
      fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 q).hom hiso hrep
  exact (isQuasiCompactFieldValuedPoint_iff_isQuasiCompact B S hS 𝒳.val p).2
    ⟨hrep, isQuasiCompact_congr_basedIso B S hS
      (schemeStackMap.{u, w} B S hS (fieldValuedPointBaseMap B S hS g) ≫
        fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 q).hom
      (fieldValuedPointMorphism B S hS 𝒳.val p) hiso.symm hrepcomp hrep
      ((isQuasiCompact_iff_baseChange_quasiCompact.{u, w} B S hS
        (schemeStackMap.{u, w} B S hS (fieldValuedPointBaseMap B S hS g) ≫
          fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 q) hrepcomp).2 hcomp)⟩

/-- **The codomain of an arrow of field-valued points of an algebraic stack inherits
quasi-compactness from its domain.** The arrow lies over a morphism of the site between two
spectra of fields, which is surjective on points, and the 1-morphism of the domain factors
through the 1-morphism of the codomain along it, so **Stacks 050X** transports
quasi-compactness. -/
theorem isQuasiCompactFieldValuedPoint_cod_of_hom (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {p q : FieldValuedPoint B S hS 𝒳.val.val} (g : p.obj ⟶ q.obj)
    (hp : IsQuasiCompactFieldValuedPoint B S hS 𝒳.val p) :
    IsQuasiCompactFieldValuedPoint B S hS 𝒳.val q :=
  (isQuasiCompactFieldValuedPoint_iff_isQuasiCompactMorphism B S hS 𝒳 q).2
    (isQuasiCompactMorphism_of_comp_of_isSurjective B S hS
      (schemeStackMap.{u, w} B S hS (fieldValuedPointBaseMap B S hS g))
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p)
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 q)
      (Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
        (fieldValuedPointMorphismBaseMapIso B S hS 𝒳.val g).symm))
      (isSurjective_of_fieldSpectrum.{u, w} B S hS
        (FieldValuedPoint.fieldSpectrum B S hS p) (FieldValuedPoint.fieldSpectrum B S hS q) _)
      ((isQuasiCompactFieldValuedPoint_iff_isQuasiCompactMorphism B S hS 𝒳 p).1 hp))

/-- **Stacks 0DTK.** Let `𝒳` be an algebraic stack over `S` and let `x` be a point of `𝒳`. Some
morphism `Spec k ⟶ 𝒳` in the equivalence class of `x` is quasi-compact if and only if every
morphism `Spec k ⟶ 𝒳` in the equivalence class of `x` is quasi-compact.

Two field-valued representatives of `x` admit a common refinement (**Stacks 04XF**), and the
arrow to each of them carries quasi-compactness from the refinement and to it. -/
@[stacks 0DTK]
theorem exists_isQuasiCompactFieldValuedPoint_iff_forall (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids) :
    (∃ p : FieldValuedPoint B S hS 𝒳.val.val,
        pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = x ∧
          IsQuasiCompactFieldValuedPoint B S hS 𝒳.val p) ↔
      ∀ p : FieldValuedPoint B S hS 𝒳.val.val,
        pointClass B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids p = x →
          IsQuasiCompactFieldValuedPoint B S hS 𝒳.val p := by
  refine ⟨fun ⟨p, hp, hpqc⟩ q hq => ?_, fun h => ?_⟩
  · obtain ⟨r, ⟨f⟩, ⟨g⟩⟩ := (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val
      𝒳.val.isFiberedInGroupoids p q).1 (hp.trans hq.symm)
    exact isQuasiCompactFieldValuedPoint_cod_of_hom.{u, w} B S hS 𝒳 g
      (isQuasiCompactFieldValuedPoint_dom_of_hom.{u, w} B S hS 𝒳 f hpqc)
  · obtain ⟨p, hp⟩ := Quotient.exists_rep x
    exact ⟨p, hp, h p hp⟩

end AlgebraicGeometry.Stack

end
