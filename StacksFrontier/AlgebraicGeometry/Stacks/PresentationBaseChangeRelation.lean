module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationBaseChangePresentation

/-!
# The arrow space of the base-changed presentation is the base change of the relation

Let `S` be a scheme of a big fppf site, let `g : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks over
`S` representable by algebraic spaces and let `P = ((U, R, s, t, c), [U/R] ≃ 𝒳)` be a presentation
of `𝒳`. `AlgebraicGeometry.Stack.GroupoidPresentation.baseChangedPresentation` builds the
presentation `[U'/R'] ⟶ 𝒳'` on the chosen representing spaces of `U' = U ×_𝒳 𝒳'` and of
`U' ×_{𝒳'} U'`. This module identifies the second of those with the base change of the relation:

    U' ×_{𝒳'} U' = U ×_𝒳 U ×_𝒳 𝒳' = (U ×_𝒳 U) ×_𝒳 𝒳',

where `R = U ×_𝒳 U` is the self-intersection of the atlas.

## Main results

* `AlgebraicGeometry.Stack.GroupoidPresentation.nonempty_equivalenceOver_baseChangedRelation`:
  `U' ×_{𝒳'} U'` and `(U ×_𝒳 U) ×_{s, U} U'` are equivalent over the site.
* `AlgebraicGeometry.Stack.GroupoidPresentation.isTwoFibreProduct_baseChangedRelationTriple`:
  the latter is a 2-fibre product of the cospan `(s ≫ a, g)`, i.e. it *is* `(U ×_𝒳 U) ×_𝒳 𝒳'`.
* `Stack.GroupoidPresentation.nonempty_equivalenceOver_arrows_baseChangedPresentation`:
  therefore the arrow space of the base-changed presentation represents `(U ×_𝒳 U) ×_𝒳 𝒳'`.
* `AlgebraicGeometry.Stack.GroupoidPresentation.exists_baseChangedPresentation`:
  there is a presentation of `𝒳'` whose groupoid is of the form `(U', R', s', t', c')` with
  `U' = U ×_𝒳 𝒳'` and `R' = R ×_𝒳 𝒳'`.

## Implementation notes

Two 2-fibre products of one cospan of categories fibred in groupoids have equivalent apexes by
`CategoryTheory.Bicategory.isEquivalence_of_isTwoFibreProduct`, and
`CategoryTheory.StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence` upgrades an
equivalence of underlying categories commuting with the structure functors to an equivalence over
the site.

The comparison 1-morphism is extracted with `Quotient.out`: a morphism of 2-commutative squares
(Stacks 003Q) is an equivalence class of pre-morphisms, and only the underlying 1-morphism of
apexes is used, which every representative has.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XC](https://stacks.math.columbia.edu/tag/02XC)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 04Y6](https://stacks.math.columbia.edu/tag/04Y6)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.GroupoidPresentation

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 𝒳' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
variable (P : GroupoidPresentation B S hS 𝒳.val) (g : 𝒳' ⟶ 𝒳)

/-- The canonical square presenting the self-intersection `R = U ×_𝒳 U` of the atlas. -/
noncomputable abbrev atlasRelationSquare : Bicategory.TwoCommSq (atlasMap P) (atlasMap P) :=
  CatFiberedInGroupoids.RepresentablePresentation.relationSquare (atlasMap P)

/-- The canonical square presenting `R ×_{s, U} U'`, the base change of the relation of the atlas
along the base-changed atlas. -/
noncomputable abbrev atlasRelationBaseChangeSquare :
    Bicategory.TwoCommSq (atlasRelationSquare P).snd (baseChangedAtlasSquare P g).fst :=
  CatFiberedInGroupoids.RepresentablePresentation.relationBaseChangeSquare (atlasMap P) g

/-- The canonical square presenting the self-intersection `U' ×_{𝒳'} U'` of the base-changed
atlas. -/
noncomputable abbrev baseChangedRelationSquare :
    Bicategory.TwoCommSq (baseChangedAtlas P g) (baseChangedAtlas P g) :=
  CatFiberedInGroupoids.RepresentablePresentation.baseChangedRelationSquare (atlasMap P) g

/-- `R ×_{s, U} U'` is a 2-fibre product of the cospan `(a, pr_U ≫ a)` naming the triple product
`U ×_𝒳 U ×_𝒳 𝒳'`. -/
noncomputable def isTwoFibreProduct_baseChangedRelationTriple :
    Bicategory.IsTwoFibreProduct
      ((atlasRelationSquare P).paste (atlasRelationBaseChangeSquare P g)) :=
  Bicategory.isTwoFibreProduct_relationBaseChangeTriple
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (atlasMap P) (atlasMap P))
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)

/-- `U' ×_{𝒳'} U'` is a 2-fibre product of the cospan `(a, pr_U ≫ a)` naming the triple product
`U ×_𝒳 U ×_𝒳 𝒳'`. -/
noncomputable def isTwoFibreProduct_baseChangedSelfIntersectionTriple :
    Bicategory.IsTwoFibreProduct
      ((baseChangedAtlasSquare P g).baseChangedSelfIntersection
        (baseChangedRelationSquare P g)) :=
  Bicategory.isTwoFibreProduct_baseChangedSelfIntersection
    (isTwoFibreProduct_baseChangedAtlasSquare P g)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)

/-- The comparison 1-morphism of the two apexes, read off from the terminality of the second
square in the category of 2-commutative squares over the triple product. -/
noncomputable def baseChangedRelationComparison :
    Bicategory.TwoCommSq.PreHom
      ((baseChangedAtlasSquare P g).baseChangedSelfIntersection (baseChangedRelationSquare P g))
      ((atlasRelationSquare P).paste (atlasRelationBaseChangeSquare P g)) :=
  _root_.Quotient.out ((isTwoFibreProduct_baseChangedRelationTriple P g).from _)

/-- `U' ×_{𝒳'} U' = U ×_𝒳 U ×_𝒳 𝒳' = (U ×_𝒳 U) ×_{s, U} U'`: the self-intersection of the
base-changed atlas is equivalent over the big fppf site of `S` to the base change of the relation
of the atlas. -/
theorem nonempty_equivalenceOver_baseChangedRelation :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (baseChangedAtlasSquare P g).pt 𝒳'
        (baseChangedAtlas P g).hom).val.p
      (atlasRelationBaseChangeSquare P g).pt.val.p) :=
  StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (baseChangedRelationSquare P g).pt.isFiberedInGroupoids
    (atlasRelationBaseChangeSquare P g).pt.isFiberedInGroupoids
    (baseChangedRelationComparison P g).hom.hom.toFunctor
    (baseChangedRelationComparison P g).hom.hom.w
    (Bicategory.isEquivalence_of_isTwoFibreProduct
      (isTwoFibreProduct_baseChangedSelfIntersectionTriple P g)
      (isTwoFibreProduct_baseChangedRelationTriple P g)
      (baseChangedRelationComparison P g))

section Arrows

variable {U' R' : AlgebraicSpaces B S hS}
variable (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
variable (h𝒳' : IsAlgebraicStack.{u, w} B S hS 𝒳'.val)
variable
  (eU' : StacksRepresentableCFG.EquivalenceOver
    (baseChangedAtlasSquare P g).pt.val.p (presheafOfCategories (U'.obj ⋙ typeToCat)).p)
  (eR' : StacksRepresentableCFG.EquivalenceOver
    (SelfIntersection.relation B S hS (baseChangedAtlasSquare P g).pt 𝒳'
      (baseChangedAtlas P g).hom).val.p
    (presheafOfCategories (R'.obj ⋙ typeToCat)).p)

/-- The arrow space of the base-changed presentation represents `R ×_𝒳 𝒳'`. -/
theorem nonempty_equivalenceOver_arrows_baseChangedPresentation :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (atlasRelationBaseChangeSquare P g).pt.val.p
      (presheafOfCategories
        ((baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid.arrows.obj ⋙ typeToCat)).p) :=
  (nonempty_equivalenceOver_baseChangedRelation P g).map (·.symm.trans eR')

/-- The object space of the base-changed presentation represents `U ×_𝒳 𝒳'`. -/
theorem nonempty_equivalenceOver_objects_baseChangedPresentation :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (baseChangedAtlasSquare P g).pt.val.p
      (presheafOfCategories
        ((baseChangedPresentation P g h𝒳 h𝒳' eU' eR').groupoid.objects.obj ⋙ typeToCat)).p) :=
  ⟨eU'⟩

end Arrows

/-- Let `g : 𝒳' ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S` representable by algebraic
spaces and let `[U/R] ⟶ 𝒳` be a presentation. Then there is a presentation `[U'/R'] ⟶ 𝒳'` whose
presenting groupoid is of the form `(U', R', s', t', c')`: its object space represents
`U' = U ×_𝒳 𝒳'` and its arrow space represents `R' = R ×_𝒳 𝒳'`, where `R` is the
self-intersection `U ×_𝒳 U` of the atlas. -/
@[stacks 04Y6 "assertions (1) and (2): a groupoid of the form (U', R', s', t', c') and a \
presentation [U'/R'] -> X'; the 2-commutative square of assertions (3) and (4) is not claimed"]
theorem exists_baseChangedPresentation
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒳' : IsAlgebraicStack.{u, w} B S hS 𝒳'.val)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom) :
    ∃ (P' : GroupoidPresentation B S hS 𝒳'.val),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (baseChangedAtlasSquare P g).pt.val.p
        (presheafOfCategories (P'.groupoid.objects.obj ⋙ typeToCat)).p) ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (atlasRelationBaseChangeSquare P g).pt.val.p
        (presheafOfCategories (P'.groupoid.arrows.obj ⋙ typeToCat)).p) := by
  obtain ⟨FU, hFU, ⟨eU'⟩⟩ := isRepresentableByAlgebraicSpace_baseChangedAtlas P g hg
  obtain ⟨FR, hFR, ⟨eR'⟩⟩ := isRepresentableByAlgebraicSpace_baseChangedRelation P g h𝒳' hg
  exact ⟨baseChangedPresentation (U' := ⟨FU, hFU⟩) (R' := ⟨FR, hFR⟩) P g h𝒳 h𝒳' eU' eR', ⟨eU'⟩,
    nonempty_equivalenceOver_arrows_baseChangedPresentation
      (U' := ⟨FU, hFU⟩) (R' := ⟨FR, hFR⟩) P g h𝒳 h𝒳' eU' eR'⟩

end AlgebraicGeometry.Stack.GroupoidPresentation

end
