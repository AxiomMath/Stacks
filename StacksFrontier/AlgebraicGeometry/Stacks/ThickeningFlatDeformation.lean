module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.Flatness
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAtAPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCompGeneral
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.UnderlyingTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.StrictTwoCommSq
import all StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact

/-!
# Flatness along a thickening of algebraic stacks

Consider a commutative diagram of thickenings of algebraic stacks over `S` over a thickening
`iB : ℬ ⟶ ℬ'` of bases, with `𝒴' ⟶ ℬ'` locally of finite type, `𝒳' ⟶ ℬ'` flat and locally of
finite presentation, the restricted 1-morphism `f : 𝒳 ⟶ 𝒴` flat, and `𝒳` and `𝒴` the base
changes of `𝒳'` and `𝒴'` along `iB`. Then the ambient 1-morphism `f' : 𝒳' ⟶ 𝒴'` is flat, and
`𝒴' ⟶ ℬ'` is flat at every point of `|𝒴'|` in the image of `|f'|`.

## Main definitions

* `AlgebraicGeometry.Stack.SmoothChartTower`: three compatible smooth charts of `ℬ'`, `𝒴'` and
  `𝒳'`, surjective on objects, with the two morphisms of charts and the three finiteness and
  flatness hypotheses read on them.
* `AlgebraicGeometry.Stack.IsRelativeThickening`: a 1-morphism of categories fibred in groupoids
  which is representable by algebraic spaces, a closed immersion in the sense of Stacks 04XB, and
  surjective on every algebraic-space base change.
* `AlgebraicGeometry.Stack.ThickenedChartTower`: such a tower together with the three iterated
  2-fibre products base-changing it along the thickening of the base.
* `AlgebraicGeometry.Stack.ThickenedChartTower.flatDeformationDiagram`: the flat deformation
  diagram of algebraic spaces it carries.
* `AlgebraicGeometry.Stack.restrictionPreHom`: the restricted 1-morphism of a commutative diagram
  of thickenings, read as a morphism of 2-commutative squares over the cospan `(pY', iB)`.

## Main results

* `AlgebraicGeometry.Stack.isFlat_ambient_of_flatDeformation`: the ambient 1-morphism `f'` is
  flat.
* `AlgebraicGeometry.Stack.isFlatAt_target_of_flatDeformation`: `𝒴' ⟶ ℬ'` is flat at every point
  of `|𝒴'|` in the image of `|f'|`.
* `AlgebraicGeometry.Stack.isFlat_fWV`: flatness of the morphism of charts of the restricted
  1-morphism.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_pasteInnerSq`: the inner square of a rectangle of
  2-fibre products is a 2-fibre product, the converse of
  `CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst`.
* `AlgebraicGeometry.Stack.isRelativelySmooth_preHom_diagramCone_of_chart`: the comparison
  1-morphisms of a diagram of Stacks 06FM whose left vertical 1-morphism factors through a smooth
  chart of a 2-fibre product are smooth.
* `AlgebraicGeometry.Stack.exists_smoothChartTower` and
  `AlgebraicGeometry.Stack.exists_thickenedChartTower`: both exist.
* `AlgebraicGeometry.Space.isThickening_range_of_isClosedImmersion_isSurjective`: the range of a
  surjective closed immersion of algebraic spaces is a thickening of its target.
* `AlgebraicGeometry.Stack.mono_and_isThickening_range_representingMap_fst`: a base change of a
  relative thickening, read on representing presheaves, is a monomorphism whose range is a
  thickening.
* `AlgebraicGeometry.Stack.ThickenedChartTower.isPullback_target`,
  `.isPullback_source` and `.isPullback_sourceBase`: the three base-change squares, read on
  representing presheaves, are pullback squares of algebraic spaces.

## References

* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 03MN](https://stacks.math.columbia.edu/tag/03MN)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04ZP](https://stacks.math.columbia.edu/tag/04ZP)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FP](https://stacks.math.columbia.edu/tag/06FP)
* [Stacks Project, Tag 06FQ](https://stacks.math.columbia.edu/tag/06FQ)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 0BPR](https://stacks.math.columbia.edu/tag/0BPR)
* [Stacks Project, Tag 0CGW](https://stacks.math.columbia.edu/tag/0CGW)
* [Stacks Project, Tag 0CIC](https://stacks.math.columbia.edu/tag/0CIC)
* [Stacks Project, Tag 0CID](https://stacks.math.columbia.edu/tag/0CID)
* [Stacks Project, Tag 0CJB](https://stacks.math.columbia.edu/tag/0CJB)
* [Stacks Project, Tag 0DFQ](https://stacks.math.columbia.edu/tag/0DFQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CatFiberedInGroupoids
open Stacks.Thickenings

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The range of a surjective closed immersion of algebraic spaces is a thickening of its target
in the sense of Stacks 05ZK. -/
theorem isThickening_range_of_isClosedImmersion_isSurjective
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hA : IsAlgebraicSpace B S hS A)
    (X : AlgebraicSpaces B S hS) (p : A ⟶ X.1)
    (hclosed : IsClosedImmersion B S hS p) (hsurj : IsSurjective B S hS p) :
    IsThickening B S hS X (Subfunctor.range p) := by
  let Q := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} :
    MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  have : Mono p := mono_of_isClosedImmersion B S hS p hclosed
  have : IsIso (Subfunctor.toRange p) := inferInstance
  have hfactor : inv (Subfunctor.toRange p) ≫ p = (Subfunctor.range p).ι :=
    (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι p).symm
  have hRangeAlg : IsAlgebraicSpace B S hS (Subfunctor.range p).toFunctor :=
    isAlgebraicSpace_of_iso B S hS (asIso (Subfunctor.toRange p)) hA
  have hRangeClosed : IsClosedImmersion B S hS (Subfunctor.range p).ι := by
    have hQ : Q.RespectsIso :=
      MorphismProperty.RespectsIso.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) (BigFppfOver.toScheme B S hS)
    have : Q.presheaf.RespectsIso := inferInstance
    have hpre := MorphismProperty.RespectsIso.precomp Q.presheaf
      (inv (Subfunctor.toRange p)) p hclosed
    rwa [hfactor] at hpre
  refine ⟨⟨hRangeAlg, hRangeClosed⟩, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨pointsMap B S hS A (Subfunctor.toRange p) x, ?_⟩
  calc pointsMap B S hS (Subfunctor.range p).toFunctor (Subfunctor.range p).ι
          (pointsMap B S hS A (Subfunctor.toRange p) x)
      = pointsMap B S hS A (Subfunctor.toRange p ≫ (Subfunctor.range p).ι) x := by
        rw [pointsMap_comp]; rfl
    _ = pointsMap B S hS A p x := by rw [Subfunctor.toRange_ι]
    _ = y := hx

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u w

/-- In a category, `Bh ≫ Ch = A ≫ Dh` with `A` and `Ch` isomorphisms implies
`Dh ≫ Ch⁻¹ = A⁻¹ ≫ Bh`. -/
private theorem comp_inv_eq_inv_comp {C : Type*} [Category C] {a b c d : C}
    (A : a ≅ b) (Bh : a ⟶ c) (Ch : c ≅ d) (Dh : b ⟶ d)
    (h : Bh ≫ Ch.hom = A.hom ≫ Dh) : Dh ≫ Ch.inv = A.inv ≫ Bh := by
  have h' : A.inv ≫ Bh ≫ Ch.hom = Dh := by rw [h, Iso.inv_hom_id_assoc]
  rw [← h', Category.assoc, Category.assoc, Ch.hom_inv_id, Category.comp_id]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- In a 2-fibre product square of categories fibred in groupoids over `S` over a cospan
`(g, f)` with `g` relatively smooth and surjective on objects, the second projection is relatively
smooth and surjective on objects. -/
theorem isRelativelySmooth_isSurjectiveOnObjects_snd
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P)
    (hgsm : IsRelativelySmooth B S hS g)
    (hgsu : IsSurjectiveOnObjects B S hS 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor g)) :
    IsRelativelySmooth B S hS P.snd ∧
      IsSurjectiveOnObjects B S hS P.pt.val.p 𝒳.val.p
        (CatFiberedInGroupoids.homFunctor P.snd) := by
  have hsm : IsRelativelySmooth B S hS P.snd :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS 𝒵 𝒴 𝒳 g f P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hgsm
  refine ⟨hsm, (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS
    P.snd hsm.1).2 ?_⟩
  exact hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
    (Space.surjectiveMorphismProperty B S hS) 𝒵 𝒴 𝒳 g f P.swap
    (Bicategory.isTwoFibreProduct_swap hP) hgsm.1
    ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS g hgsm.1).1 hgsu)

/-- In a 2-fibre product square over a cospan `(g, f)` with `g` relatively smooth and surjective on
objects, a relatively smooth 1-morphism `c` surjective on objects into the apex stays so after
composing with the second projection. -/
private theorem isRelativelySmooth_isSurjectiveOnObjects_comp_snd
    {𝒵 𝒳 𝒴 𝒯 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P) (hgsm : IsRelativelySmooth B S hS g)
    (hgsu : IsSurjectiveOnObjects B S hS 𝒵.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor g))
    (c : 𝒯 ⟶ P.pt) (hcsm : IsRelativelySmooth B S hS c)
    (hcsu : IsSurjectiveOnObjects B S hS 𝒯.val.p P.pt.val.p
      (CatFiberedInGroupoids.homFunctor c)) :
    IsRelativelySmooth B S hS (c ≫ P.snd) ∧
      IsSurjectiveOnObjects B S hS 𝒯.val.p 𝒳.val.p
        (CatFiberedInGroupoids.homFunctor (c ≫ P.snd)) := by
  obtain ⟨hsm, hsu⟩ := isRelativelySmooth_isSurjectiveOnObjects_snd B S hS g f P hP hgsm hgsu
  exact ⟨isRelativelySmooth_comp B S hS c P.snd hcsm hsm,
    isSurjectiveOnObjects_comp B S hS 𝒯.val.p P.pt.val.p 𝒳.val.p
      (CatFiberedInGroupoids.homFunctor c) (CatFiberedInGroupoids.homFunctor P.snd)
      (CatFiberedInGroupoids.homFunctor_comp_p P.snd) hcsu hsu⟩

/-- The 1-morphism attached to the morphism of representing presheaves of a 1-morphism `k`
between represented categories fibred in groupoids is 2-isomorphic to `k`. -/
theorem nonempty_twoIso_associatedMap_representingMap
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (k : fibredCategory B S hS F ⟶ fibredCategory B S hS G) :
    Nonempty ((associatedMap B S hS (representingMap B S hS (fibredCategory B S hS F)
      (fibredCategory B S hS G) F G (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) k)).1 ≅ k) := by
  set h := representingMap B S hS (fibredCategory B S hS F) (fibredCategory B S hS G) F G
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) k with hdef
  have hleft : representingMap B S hS (fibredCategory B S hS F) (fibredCategory B S hS G) F G
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (associatedMap B S hS h).1 = h :=
    representingMap_associatedMap B S hS F G h
  obtain ⟨e, hee, -⟩ := existsUnique_twoIso_of_representingMap_eq B S hS
    (fibredCategory B S hS F) (fibredCategory B S hS G) F G
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) hleft
  exact ⟨Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso e hee)⟩

/-! ### Thickenings on charts -/

/-- A 1-morphism of categories fibred in groupoids over `S` *is a relative thickening* when it is
representable by algebraic spaces, is a closed immersion in the sense of Stacks 04XB, and every
algebraic space representing one of its base changes has surjective structural morphism. -/
def IsRelativeThickening {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsRepresentableByAlgebraicSpaces B S hS f.hom ∧ IsClosedImmersion B S hS f ∧
    ∀ hf : IsRepresentableByAlgebraicSpaces B S hS f.hom,
      HasRelativeProperty.{u, u, u + 1, u} B S hS
        (Space.surjectiveMorphismProperty B S hS) f hf

/-- A thickening of algebraic stacks is a relative thickening of the underlying categories
fibred in groupoids. -/
theorem isRelativeThickening_of_isThickening {𝒵 𝒵' : AlgebraicStacks.{u, w} B S hS}
    {i : 𝒵 ⟶ 𝒵'} (hi : IsThickening i) : IsRelativeThickening B S hS i.hom :=
  ⟨hi.1.1, hi.1.2, fun _ =>
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS i hi.1.1).1 hi.2⟩

/-- The projection of a 2-fibre product square to the source of `g` over a cospan `(g, f)` with
`f` a relative thickening is a relative thickening. -/
theorem isRelativeThickening_baseChange
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴) (hf : IsRelativeThickening B S hS f)
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q) :
    IsRelativeThickening B S hS Q.fst :=
  ⟨isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒳 𝒴 𝒵 f g Q hQ hf.1,
    isClosedImmersion_baseChange.{u, u, u + 1} B S hS 𝒳 𝒴 𝒵 f g Q hQ hf.2.1,
    fun _ => hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) 𝒳 𝒴 𝒵 f g Q hQ hf.1 (hf.2.2 hf.1)⟩

/-- In a 2-fibre product square over a cospan `(g, f)` with `f` a relative thickening, whose apex
and the source of `g` are represented by algebraic spaces `F` and `G`, the morphism `F ⟶ G` of
representing presheaves induced by the projection to the source of `g` is a monomorphism whose
range is a thickening of `G` in the sense of Stacks 05ZK. -/
theorem mono_and_isThickening_range_representingMap_fst
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴) (hf : IsRelativeThickening B S hS f)
    (Q : Bicategory.TwoCommSq g f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver Q.pt.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒵.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p) :
    Mono (representingMap B S hS Q.pt 𝒵 F G eF eG Q.fst) ∧
      Space.IsThickening B S hS (⟨G, hG⟩ : AlgebraicSpaces B S hS)
        (Subfunctor.range (representingMap B S hS Q.pt 𝒵 F G eF eG Q.fst)) := by
  have hfpqc : (Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.precoverage.{u, u} .fpqc B S hS) :=
    Space.isClosedImmersion_isLocalAtTarget_fpqc B S hS
  have hfppf : (Space.closedImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage B S hS)
  have hcl : Space.IsClosedImmersion B S hS (representingMap B S hS Q.pt 𝒵 F G eF eG Q.fst) :=
    prop_representingMap_of_hasRelativeProperty B S hS
      (Space.closedImmersionProperty B S hS) f hf.1 hf.2.1 𝒵 g Q hQ F G hF hG eF eG
  have hsj : Space.IsSurjective B S hS (representingMap B S hS Q.pt 𝒵 F G eF eG Q.fst) :=
    prop_representingMap_of_hasRelativeProperty B S hS
      (Space.surjectiveMorphismProperty B S hS) f hf.1 (hf.2.2 hf.1) 𝒵 g Q hQ F G hF hG eF eG
  exact ⟨Space.mono_of_isClosedImmersion B S hS _ hcl,
    Space.isThickening_range_of_isClosedImmersion_isSurjective B S hS hF ⟨G, hG⟩ _ hcl hsj⟩

/-! ### The tower of ambient charts -/

/-- The apex of the canonical 2-fibre product over a cospan whose second leg is representable by
algebraic spaces and whose first leg has a source representable by an algebraic space is itself
representable by an algebraic space. -/
private theorem exists_space_canonical
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    IsRepresentableByAlgebraicSpace B S hS
      (twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt :=
  isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS 𝒵 𝒴 𝒳 g f
    (twoFibreProductSquare.{u, u, u + 1, u + 1} f g)
    (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f g) hg h𝒳

/-- A 2-fibre product square of a 1-morphism `k` between represented categories fibred in groupoids
and a 1-morphism `fY` representable by algebraic spaces, read on representing presheaves, is a
pullback square. -/
private theorem isPullback_representingMap_of_represented
    {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX' : IsAlgebraicSpace B S hS X')
    {𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {k : fibredCategory B S hS X' ⟶ fibredCategory B S hS Y'}
    {fY : 𝒲 ⟶ fibredCategory B S hS Y'} (hfY : IsRepresentableByAlgebraicSpaces B S hS fY.hom)
    {Q : Bicategory.TwoCommSq k fY} (hQ : Bicategory.IsTwoFibreProduct Q)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (eU : StacksRepresentableCFG.EquivalenceOver 𝒲.val.p (presheafOfCategories (U ⋙ typeToCat)).p)
    (eV : StacksRepresentableCFG.EquivalenceOver Q.pt.val.p
      (presheafOfCategories (V ⋙ typeToCat)).p) :
    IsPullback
      (representingMap B S hS Q.pt (fibredCategory B S hS X') V X' eV
        (StacksRepresentableCFG.EquivalenceOver.refl _) Q.fst)
      (representingMap B S hS Q.pt 𝒲 V U eV eU Q.snd)
      (representingMap B S hS (fibredCategory B S hS X') (fibredCategory B S hS Y') X' Y'
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) k)
      (representingMap B S hS 𝒲 (fibredCategory B S hS Y') U Y' eU
        (StacksRepresentableCFG.EquivalenceOver.refl _) fY) := by
  classical
  obtain ⟨K, -, ⟨eK⟩⟩ := exists_space_canonical B S hS k fY hfY
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS X' hX')
  exact isPullback_representingMap_of_isTwoFibreProduct B S hS hQ X' U Y' V K
    (StacksRepresentableCFG.EquivalenceOver.refl _) eU
    (StacksRepresentableCFG.EquivalenceOver.refl _) eV eK

/-- A cospan whose second leg is representable by algebraic spaces and whose first leg has a source
representable by an algebraic space has a 2-fibre product square with representable apex. -/
private theorem exists_isTwoFibreProduct_represented
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴) (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS 𝒳) :
    ∃ Q : Bicategory.TwoCommSq f g, Nonempty (Bicategory.IsTwoFibreProduct Q) ∧
      IsRepresentableByAlgebraicSpace B S hS Q.pt :=
  ⟨_, ⟨isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f g⟩,
    exists_space_canonical B S hS f g hg h𝒳⟩

/-- Let `P` be a
2-fibre product of a cospan `(g, f)` of categories fibred in groupoids over `S`, let `k` be a
1-morphism into the source of `g`, and let `Sq` be a 2-fibre product of the composed cospan
`(k ≫ g, f)` together with a pre-morphism `p` from the rectangle it defines over `(g, f)` to `P`.
Then the inner square cut out by `p` — the apex of `Sq` over `(k, P.fst)` — is a 2-fibre product.

This is the converse of `CategoryTheory.Bicategory.isTwoFibreProduct_pasteFst`. -/
noncomputable def isTwoFibreProduct_pasteInnerSq
    {𝒳 𝒴 𝒵 𝒯 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} (P : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P)
    {k : 𝒯 ⟶ 𝒵} {Sq : Bicategory.TwoCommSq (k ≫ g) f}
    (hSq : Bicategory.IsTwoFibreProduct Sq)
    (p : Bicategory.TwoCommSq.PreHom (Bicategory.pasteOuterSq k Sq) P) :
    Bicategory.IsTwoFibreProduct (Bicategory.pasteInnerSq P p) := by
  classical
  set Q₀ := twoFibreProductSquare.{u, u, u + 1, u + 1} k P.fst with hQ₀def
  have hQ₀ : Bicategory.IsTwoFibreProduct Q₀ :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} k P.fst
  set q := Bicategory.twoFibreProductPreHom hQ₀ (Bicategory.pasteInnerSq P p) with hqdef
  have hequiv : Functor.IsEquivalence
      (Bicategory.pasteFstPreHom P Q₀ p q).hom.hom.toFunctor :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hSq
      (Bicategory.isTwoFibreProduct_pasteFst P hP Q₀ hQ₀)
      (Bicategory.pasteFstPreHom P Q₀ p q)
  exact Bicategory.isTwoFibreProduct_of_isEquivalence_to hQ₀ q hequiv

/-- Let `Q₁` be a 2-fibre product of the cospan `(b, f)`, let `cc` be a smooth
1-morphism from a category of elements into its apex, and let the diagram of Stacks 06FM be
the one `cc` defines: its left vertical 1-morphism is `cc` followed by the projection to the
source of `f`, its top horizontal morphism of algebraic spaces is a morphism inducing `cc`
followed by the other projection, and its 2-cell is the filler of `Q₁` whiskered by `cc`. Then
every comparison 1-morphism from that diagram to every 2-fibre product of `(b, f)` is smooth. -/
theorem isRelativelySmooth_preHom_diagramCone_of_chart
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (b : fibredCategory B S hS V ⟶ 𝒴)
    (Q₁ : Bicategory.TwoCommSq b f) (hQ₁ : Bicategory.IsTwoFibreProduct Q₁)
    (cc : fibredCategory B S hS U ⟶ Q₁.pt) (hcc : IsRelativelySmooth B S hS cc)
    (h : U ⟶ V) (e : (associatedMap B S hS h).1 ≅ cc ≫ Q₁.fst)
    (Q : Bicategory.TwoCommSq b f) (hQ : Bicategory.IsTwoFibreProduct Q)
    (k : Bicategory.TwoCommSq.PreHom
      (diagramCone B S hS f (cc ≫ Q₁.snd) b h
        (Bicategory.whiskerRightIso e b ≪≫ Bicategory.whiskerLeftIso cc Q₁.iso)) Q) :
    IsRelativelySmooth B S hS k.hom := by
  refine isRelativelySmooth_preHom_of_isTwoFibreProduct B S hS hQ₁ hQ
    (preHomOfStrict.{u, u, u + 1, u + 1}
      (T := diagramCone B S hS f (cc ≫ Q₁.snd) b h
        (Bicategory.whiskerRightIso e b ≪≫ Bicategory.whiskerLeftIso cc Q₁.iso))
      (S := Q₁) cc e (Iso.refl _) ?_) k hcc
  simp only [Iso.refl_hom, Bicategory.id_whiskerRight, Category.comp_id]
  rfl

variable {ℬ ℬ' 𝒴' 𝒳' : AlgebraicStacks.{u, w} B S hS}

/-- A tower of smooth charts of 1-morphisms `f' : 𝒳' ⟶ 𝒴'` and `pY' : 𝒴' ⟶ ℬ'` of algebraic
stacks over `S`: algebraic spaces `U'`, `V'`, `W'` with smooth charts of `ℬ'`, `𝒴'`, `𝒳'`
surjective on objects, morphisms `g' : V' ⟶ U'` and `h' : W' ⟶ V'` making the two squares
2-commute with smooth comparison 1-morphisms, such that `g'` is locally of finite type and
`h' ≫ g'` is flat and locally of finite presentation. -/
structure SmoothChartTower (pY' : 𝒴' ⟶ ℬ') (f' : 𝒳' ⟶ 𝒴') where
  /-- the chart of the ambient base -/
  U' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- the chart of the ambient target -/
  V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- the chart of the ambient source -/
  W' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `U'` is an algebraic space over `S` -/
  algebraicU : IsAlgebraicSpace B S hS U'
  /-- `V'` is an algebraic space over `S` -/
  algebraicV : IsAlgebraicSpace B S hS V'
  /-- `W'` is an algebraic space over `S` -/
  algebraicW : IsAlgebraicSpace B S hS W'
  /-- the chart 1-morphism of the ambient base -/
  a' : fibredCategory B S hS U' ⟶ ℬ'.val
  /-- the chart 1-morphism of the ambient target -/
  b' : fibredCategory B S hS V' ⟶ 𝒴'.val
  /-- the chart 1-morphism of the ambient source -/
  c' : fibredCategory B S hS W' ⟶ 𝒳'.val
  /-- the morphism of charts of the structure 1-morphism of the ambient target -/
  g' : V' ⟶ U'
  /-- the morphism of charts of the ambient 1-morphism -/
  h' : W' ⟶ V'
  /-- the chart of the ambient base is smooth -/
  smoothA : IsRelativelySmooth B S hS a'
  /-- the chart of the ambient base is surjective on objects -/
  surjectiveA : IsSurjectiveOnObjects B S hS (fibredCategory B S hS U').val.p ℬ'.val.val.p
    (CatFiberedInGroupoids.homFunctor a')
  /-- the chart of the ambient target is smooth -/
  smoothB : IsRelativelySmooth B S hS b'
  /-- the chart of the ambient target is surjective on objects -/
  surjectiveB : IsSurjectiveOnObjects B S hS (fibredCategory B S hS V').val.p 𝒴'.val.val.p
    (CatFiberedInGroupoids.homFunctor b')
  /-- the chart of the ambient source is smooth -/
  smoothC : IsRelativelySmooth B S hS c'
  /-- the chart of the ambient source is surjective on objects -/
  surjectiveC : IsSurjectiveOnObjects B S hS (fibredCategory B S hS W').val.p 𝒳'.val.val.p
    (CatFiberedInGroupoids.homFunctor c')
  /-- the square of charts of the structure 1-morphism of the ambient target 2-commutes -/
  targetComm : (associatedMap B S hS g').1 ≫ a' ≅ b' ≫ pY'.hom
  /-- the square of charts of the ambient 1-morphism 2-commutes -/
  sourceComm : (associatedMap B S hS h').1 ≫ b' ≅ c' ≫ f'.hom
  /-- every comparison 1-morphism from the square of charts of the structure 1-morphism of the
  ambient target to a 2-fibre product of the cospan `(a', pY')` is smooth: the chart of the
  ambient target presents that 2-fibre product -/
  smoothTargetComparison : ∀ (Q : Bicategory.TwoCommSq a' pY'.hom)
    (_hQ : Bicategory.IsTwoFibreProduct Q)
    (k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS pY'.hom b' a' g' targetComm) Q),
      IsRelativelySmooth B S hS k.hom
  /-- every comparison 1-morphism from the square of charts of the ambient 1-morphism to a
  2-fibre product of the cospan `(b', f')` is smooth: the chart of the ambient source presents
  that 2-fibre product -/
  smoothSourceComparison : ∀ (Q : Bicategory.TwoCommSq b' f'.hom)
    (_hQ : Bicategory.IsTwoFibreProduct Q)
    (k : Bicategory.TwoCommSq.PreHom (diagramCone B S hS f'.hom c' b' h' sourceComm) Q),
      IsRelativelySmooth B S hS k.hom
  /-- the chart of the ambient target is locally of finite type over the chart of the base -/
  finiteType : Space.IsLocallyOfFiniteType B S hS g'
  /-- the chart of the ambient source is flat over the chart of the base -/
  flat : Space.IsFlat B S hS (h' ≫ g')
  /-- the chart of the ambient source is locally of finite presentation over the chart of the
  base -/
  finitePresentation : Space.IsLocallyOfFinitePresentation B S hS (h' ≫ g')

/-- For 1-morphisms `f' : 𝒳' ⟶ 𝒴'`, `pY' : 𝒴' ⟶ ℬ'` and `pX' ≅ f' ≫ pY'` of algebraic stacks
with `pY'` locally of finite type and `pX'` flat and locally of finite presentation, a tower of
smooth charts of `pY'` and `f'` exists. -/
theorem exists_smoothChartTower (pX' : 𝒳' ⟶ ℬ') (pY' : 𝒴' ⟶ ℬ') (f' : 𝒳' ⟶ 𝒴')
    (houter : f' ≫ pY' ≅ pX')
    (hYft : AlgebraicStacks.IsLocallyOfFiniteType B S hS pY')
    (hXflat : AlgebraicStacks.IsFlat B S hS pX')
    (hXfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS pX') :
    Nonempty (SmoothChartTower B S hS pY' f') := by
  classical
  obtain ⟨U', hU', a', hasm, hasu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS ℬ'.property
  set QY : Bicategory.TwoCommSq a' pY'.hom :=
    twoFibreProductSquare.{u, u, u + 1, u + 1} a' pY'.hom with hQYdef
  have hQY : Bicategory.IsTwoFibreProduct QY :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} a' pY'.hom
  have hQYalg : IsAlgebraicStack.{u, w} B S hS QY.pt.val :=
    isAlgebraicStack_twoFibreProduct B S hS (fibredCategory B S hS U').val 𝒴'.val.val ℬ'.val.val
      a'.hom pY'.hom.hom ℬ'.property.choose_spec.1 ℬ'.property.choose_spec.2.1
      (isAlgebraicStack_fibredCategory.{u, w} B S hS U' hU') 𝒴'.property
  obtain ⟨V', hV', ccV, hccVsm, hccVsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS hQYalg
  obtain ⟨hbsm, hbsu⟩ := isRelativelySmooth_isSurjectiveOnObjects_comp_snd B S hS a' pY'.hom QY
    hQY hasm hasu ccV hccVsm hccVsu
  set TX : Bicategory.TwoCommSq QY.snd f'.hom :=
    twoFibreProductSquare.{u, u, u + 1, u + 1} QY.snd f'.hom with hTXdef
  have hTX : Bicategory.IsTwoFibreProduct TX :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} QY.snd f'.hom
  set Qc : Bicategory.TwoCommSq ccV TX.fst :=
    twoFibreProductSquare.{u, u, u + 1, u + 1} ccV TX.fst with hQcdef
  have hQc : Bicategory.IsTwoFibreProduct Qc :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} ccV TX.fst
  have hSX : Bicategory.IsTwoFibreProduct (TX.pasteFst Qc) :=
    Bicategory.isTwoFibreProduct_pasteFst TX hTX Qc hQc
  have hTXalg : IsAlgebraicStack.{u, w} B S hS TX.pt.val :=
    isAlgebraicStack_twoFibreProduct B S hS QY.pt.val 𝒳'.val.val 𝒴'.val.val
      QY.snd.hom f'.hom.hom 𝒴'.property.choose_spec.1 𝒴'.property.choose_spec.2.1
      hQYalg 𝒳'.property
  have hQcalg : IsAlgebraicStack.{u, w} B S hS (TX.pasteFst Qc).pt.val :=
    isAlgebraicStack_twoFibreProduct B S hS (fibredCategory B S hS V').val TX.pt.val QY.pt.val
      ccV.hom TX.fst.hom hQYalg.choose_spec.1 hQYalg.choose_spec.2.1
      (isAlgebraicStack_fibredCategory.{u, w} B S hS V' hV') hTXalg
  obtain ⟨W', hW', ccW, hccWsm, hccWsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS hQcalg
  obtain ⟨hcsm, hcsu⟩ := isRelativelySmooth_isSurjectiveOnObjects_comp_snd B S hS (ccV ≫ QY.snd)
    f'.hom (TX.pasteFst Qc) hSX hbsm hbsu ccW hccWsm hccWsu
  obtain ⟨hQcsndsm, -⟩ := isRelativelySmooth_isSurjectiveOnObjects_snd B S hS
    ccV TX.fst Qc hQc hccVsm hccVsu
  obtain ⟨eG⟩ := nonempty_twoIso_associatedMap_representingMap B S hS V' U' (ccV ≫ QY.fst)
  obtain ⟨eH⟩ := nonempty_twoIso_associatedMap_representingMap B S hS W' V' (ccW ≫ Qc.fst)
  have hQXbig : Bicategory.IsTwoFibreProduct (QY.pasteSnd TX) :=
    Bicategory.isTwoFibreProduct_pasteSnd QY hQY TX hTX
  have hQX : Bicategory.IsTwoFibreProduct
      ((QY.pasteSnd TX).reindexSnd (algebraicStacksTwoIsoHom B S hS houter)) :=
    Bicategory.isTwoFibreProduct_reindexSnd _ hQXbig
  have hccsm : IsRelativelySmooth B S hS (ccW ≫ Qc.snd) :=
    isRelativelySmooth_comp B S hS ccW Qc.snd hccWsm hQcsndsm
  have hiso : (ccW ≫ Qc.snd) ≫ ((QY.pasteSnd TX).reindexSnd
      (algebraicStacksTwoIsoHom B S hS houter)).fst ≅
      (ccW ≫ Qc.fst) ≫ (ccV ≫ QY.fst) :=
    (Bicategory.whiskerLeftIso ccW (Bicategory.whiskerRightIso Qc.iso QY.fst)).symm
  have hflatEvery : HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ k => Space.IsFlat B S hS k) pX'.hom :=
    (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ k => Space.IsFlat B S hS k) (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
      𝒳'.property ℬ'.property pX'.hom).2
      ((AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS pX').1 hXflat)
  have hchart : ∀ P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      HasPropertyOnEverySmoothDiagram B S hS P pX'.hom →
      P (representingMap B S hS (fibredCategory B S hS W') (fibredCategory B S hS V') W' V'
            (StacksRepresentableCFG.EquivalenceOver.refl _)
            (StacksRepresentableCFG.EquivalenceOver.refl _) (ccW ≫ Qc.fst) ≫
          representingMap B S hS (fibredCategory B S hS V') (fibredCategory B S hS U') V' U'
            (StacksRepresentableCFG.EquivalenceOver.refl _)
            (StacksRepresentableCFG.EquivalenceOver.refl _) (ccV ≫ QY.fst)) := by
    intro P hP
    rw [← representingMap_comp B S hS W' V' U'
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) (ccW ≫ Qc.fst) (ccV ≫ QY.fst),
      representingMap_congr_twoIso B S hS W' U'
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) hiso.symm]
    exact prop_representingMap_fst_of_smooth_comparison B S hS P pX'.hom hP U' W' hU' hW'
      a' hasm _ hQX _ hccsm
  exact ⟨{
    U' := U'
    V' := V'
    W' := W'
    algebraicU := hU'
    algebraicV := hV'
    algebraicW := hW'
    a' := a'
    b' := ccV ≫ QY.snd
    c' := ccW ≫ (TX.pasteFst Qc).snd
    g' := representingMap B S hS (fibredCategory B S hS V') (fibredCategory B S hS U') V' U'
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (ccV ≫ QY.fst)
    h' := representingMap B S hS (fibredCategory B S hS W') (fibredCategory B S hS V') W' V'
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (ccW ≫ Qc.fst)
    smoothA := hasm
    surjectiveA := hasu
    smoothB := hbsm
    surjectiveB := hbsu
    smoothC := hcsm
    surjectiveC := hcsu
    targetComm := Bicategory.whiskerRightIso eG a' ≪≫ Bicategory.whiskerLeftIso ccV QY.iso
    sourceComm := Bicategory.whiskerRightIso eH (ccV ≫ QY.snd) ≪≫
      Bicategory.whiskerLeftIso ccW (TX.pasteFst Qc).iso
    smoothTargetComparison := isRelativelySmooth_preHom_diagramCone_of_chart B S hS
      pY'.hom a' QY hQY ccV hccVsm _ eG
    smoothSourceComparison := isRelativelySmooth_preHom_diagramCone_of_chart B S hS
      f'.hom (ccV ≫ QY.snd) (TX.pasteFst Qc) hSX ccW hccWsm _ eH
    finiteType := prop_representingMap_fst_of_smooth_comparison B S hS
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k) pY'.hom hYft U' V' hU' hV'
      a' hasm QY hQY ccV hccVsm
    flat := hchart _ hflatEvery
    finitePresentation := hchart _ hXfp }⟩


/-! ### Base change of the tower along the thickening of the base -/

/-- A tower of smooth charts together with its base change along a thickening `iB` of the ambient
base: three 2-fibre product squares base-changing the chart of the ambient base along `iB`, then
the chart of the ambient target along that, then the chart of the ambient source along *that*,
with algebraic spaces `U`, `V`, `W` representing their apexes. -/
structure ThickenedChartTower (iB : ℬ ⟶ ℬ') (pY' : 𝒴' ⟶ ℬ') (f' : 𝒳' ⟶ 𝒴') where
  /-- the tower of charts of the ambient stacks -/
  tower : SmoothChartTower B S hS pY' f'
  /-- the base change of the chart of the ambient base along the base thickening -/
  AU : Bicategory.TwoCommSq tower.a' iB.hom
  /-- that square is a 2-fibre product -/
  cartAU : Bicategory.IsTwoFibreProduct AU
  /-- the base change of the chart of the ambient target -/
  Qv : Bicategory.TwoCommSq (associatedMap B S hS tower.g').1 AU.fst
  /-- that square is a 2-fibre product -/
  cartQv : Bicategory.IsTwoFibreProduct Qv
  /-- the base change of the chart of the ambient source -/
  Qw : Bicategory.TwoCommSq (associatedMap B S hS tower.h').1 Qv.fst
  /-- that square is a 2-fibre product -/
  cartQw : Bicategory.IsTwoFibreProduct Qw
  /-- the chart of the base of the thickening -/
  U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- the chart of the target of the thickening -/
  V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- the chart of the source of the thickening -/
  W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `U` is an algebraic space over `S` -/
  algU : IsAlgebraicSpace B S hS U
  /-- `V` is an algebraic space over `S` -/
  algV : IsAlgebraicSpace B S hS V
  /-- `W` is an algebraic space over `S` -/
  algW : IsAlgebraicSpace B S hS W
  /-- `U` represents the apex of the first square -/
  eU : StacksRepresentableCFG.EquivalenceOver AU.pt.val.p
    (presheafOfCategories (U ⋙ typeToCat)).p
  /-- `V` represents the apex of the second square -/
  eV : StacksRepresentableCFG.EquivalenceOver Qv.pt.val.p
    (presheafOfCategories (V ⋙ typeToCat)).p
  /-- `W` represents the apex of the third square -/
  eW : StacksRepresentableCFG.EquivalenceOver Qw.pt.val.p
    (presheafOfCategories (W ⋙ typeToCat)).p

namespace ThickenedChartTower

variable {B S hS} {iB : ℬ ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'} {f' : 𝒳' ⟶ 𝒴'}
variable (C : ThickenedChartTower B S hS iB pY' f')

/-- The thickening of the chart of the ambient base. -/
noncomputable def iU : C.U ⟶ C.tower.U' :=
  representingMap B S hS C.AU.pt (fibredCategory B S hS C.tower.U') C.U C.tower.U' C.eU
    (StacksRepresentableCFG.EquivalenceOver.refl _) C.AU.fst

/-- The thickening of the chart of the ambient target. -/
noncomputable def iV : C.V ⟶ C.tower.V' :=
  representingMap B S hS C.Qv.pt (fibredCategory B S hS C.tower.V') C.V C.tower.V' C.eV
    (StacksRepresentableCFG.EquivalenceOver.refl _) C.Qv.fst

/-- The thickening of the chart of the ambient source. -/
noncomputable def iW : C.W ⟶ C.tower.W' :=
  representingMap B S hS C.Qw.pt (fibredCategory B S hS C.tower.W') C.W C.tower.W' C.eW
    (StacksRepresentableCFG.EquivalenceOver.refl _) C.Qw.fst

/-- The structure morphism of the chart of the target over the chart of the base. -/
noncomputable def gVU : C.V ⟶ C.U :=
  representingMap B S hS C.Qv.pt C.AU.pt C.V C.U C.eV C.eU C.Qv.snd

/-- The morphism of charts of the restricted 1-morphism. -/
noncomputable def fWV : C.W ⟶ C.V :=
  representingMap B S hS C.Qw.pt C.Qv.pt C.W C.V C.eW C.eV C.Qw.snd

/-- The base change of the base thickening to the chart of the ambient base is a relative
thickening. -/
theorem isRelativeThickening_AU (hiB : IsThickening iB) :
    IsRelativeThickening B S hS C.AU.fst :=
  isRelativeThickening_baseChange B S hS iB.hom C.tower.a'
    (isRelativeThickening_of_isThickening B S hS hiB) C.AU C.cartAU

/-- The base change of the base thickening to the chart of the ambient target is a relative
thickening. -/
theorem isRelativeThickening_Qv (hiB : IsThickening iB) :
    IsRelativeThickening B S hS C.Qv.fst :=
  isRelativeThickening_baseChange B S hS C.AU.fst _ (C.isRelativeThickening_AU hiB)
    C.Qv C.cartQv

/-- The base change of the base thickening to the chart of the ambient source is a relative
thickening. -/
theorem isRelativeThickening_Qw (hiB : IsThickening iB) :
    IsRelativeThickening B S hS C.Qw.fst :=
  isRelativeThickening_baseChange B S hS C.Qv.fst _ (C.isRelativeThickening_Qv hiB)
    C.Qw C.cartQw

end ThickenedChartTower


namespace ThickenedChartTower

variable {B S hS} {iB : ℬ ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'} {f' : 𝒳' ⟶ 𝒴'}
variable (C : ThickenedChartTower B S hS iB pY' f')

/-- The chart of the target is the base change of the chart of the ambient target. -/
theorem isPullback_target (hiB : IsThickening iB) :
    IsPullback C.iV C.gVU C.tower.g' C.iU := by
  have h := isPullback_representingMap_of_represented B S hS C.tower.algebraicV
    (C.isRelativeThickening_AU hiB).1 C.cartQv C.eU C.eV
  rwa [representingMap_associatedMap] at h

/-- The chart of the source is the base change of the chart of the ambient source. -/
theorem isPullback_source (hiB : IsThickening iB) :
    IsPullback C.iW C.fWV C.tower.h' C.iV := by
  have h := isPullback_representingMap_of_represented B S hS C.tower.algebraicW
    (C.isRelativeThickening_Qv hiB).1 C.cartQw C.eV C.eW
  rwa [representingMap_associatedMap] at h

/-- The chart of the source is the base change of the chart of the ambient source over the chart
of the ambient base. -/
theorem isPullback_sourceBase (hiB : IsThickening iB) :
    IsPullback C.iW (C.fWV ≫ C.gVU) (C.tower.h' ≫ C.tower.g') C.iU := by
  have h := isPullback_representingMap_of_represented B S hS C.tower.algebraicW
    (C.isRelativeThickening_AU hiB).1
    (Bicategory.isTwoFibreProduct_pasteFst C.Qv C.cartQv C.Qw C.cartQw) C.eU C.eW
  have h2 : IsPullback C.iW
      (representingMap B S hS C.Qw.pt C.AU.pt C.W C.U C.eW C.eU (C.Qw.snd ≫ C.Qv.snd))
      (representingMap B S hS (fibredCategory B S hS C.tower.W')
        (fibredCategory B S hS C.tower.U') C.tower.W' C.tower.U'
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        ((associatedMap B S hS C.tower.h').1 ≫ (associatedMap B S hS C.tower.g').1))
      C.iU := h
  rw [representingMap_comp B S hS C.W C.V C.U C.eW C.eV C.eU C.Qw.snd C.Qv.snd,
    representingMap_comp B S hS C.tower.W' C.tower.V' C.tower.U'
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (associatedMap B S hS C.tower.h').1 (associatedMap B S hS C.tower.g').1,
    representingMap_associatedMap, representingMap_associatedMap] at h2
  exact h2

/-- The thickening of the chart of the ambient base is a monomorphism whose range is a
thickening. -/
theorem mono_and_isThickening_iU (hiB : IsThickening iB) : Mono C.iU ∧
    Space.IsThickening B S hS (⟨C.tower.U', C.tower.algebraicU⟩ : AlgebraicSpaces B S hS)
      (Subfunctor.range C.iU) :=
  mono_and_isThickening_range_representingMap_fst B S hS iB.hom C.tower.a'
    (isRelativeThickening_of_isThickening B S hS hiB) C.AU C.cartAU C.U C.tower.U'
    C.algU C.tower.algebraicU C.eU (StacksRepresentableCFG.EquivalenceOver.refl _)

/-- The thickening of the chart of the ambient target is a monomorphism whose range is a
thickening. -/
theorem mono_and_isThickening_iV (hiB : IsThickening iB) : Mono C.iV ∧
    Space.IsThickening B S hS (⟨C.tower.V', C.tower.algebraicV⟩ : AlgebraicSpaces B S hS)
      (Subfunctor.range C.iV) :=
  mono_and_isThickening_range_representingMap_fst B S hS C.AU.fst _
    (C.isRelativeThickening_AU hiB) C.Qv C.cartQv C.V C.tower.V'
    C.algV C.tower.algebraicV C.eV (StacksRepresentableCFG.EquivalenceOver.refl _)

/-- The thickening of the chart of the ambient source is a monomorphism whose range is a
thickening. -/
theorem mono_and_isThickening_iW (hiB : IsThickening iB) : Mono C.iW ∧
    Space.IsThickening B S hS (⟨C.tower.W', C.tower.algebraicW⟩ : AlgebraicSpaces B S hS)
      (Subfunctor.range C.iW) :=
  mono_and_isThickening_range_representingMap_fst B S hS C.Qv.fst _
    (C.isRelativeThickening_Qv hiB) C.Qw C.cartQw C.W C.tower.W'
    C.algW C.tower.algebraicW C.eW (StacksRepresentableCFG.EquivalenceOver.refl _)


/-- The flat deformation diagram of algebraic spaces carried by a thickened chart tower: its
ambient row is the tower of charts of the ambient stacks and its restricted row is their base
change along the thickening of the base. -/
noncomputable def flatDeformationDiagram (hiB : IsThickening iB) :
    Space.FlatDeformationDiagram B S hS where
  X := ⟨C.W, C.algW⟩
  X' := ⟨C.tower.W', C.tower.algebraicW⟩
  Y := ⟨C.V, C.algV⟩
  Y' := ⟨C.tower.V', C.tower.algebraicV⟩
  B := ⟨C.U, C.algU⟩
  B' := ⟨C.tower.U', C.tower.algebraicU⟩
  iX := ObjectProperty.homMk C.iW
  iY := ObjectProperty.homMk C.iV
  iB := ObjectProperty.homMk C.iU
  f := ObjectProperty.homMk C.fWV
  f' := ObjectProperty.homMk C.tower.h'
  g := ObjectProperty.homMk C.gVU
  g' := ObjectProperty.homMk C.tower.g'
  iX_mono := (C.mono_and_isThickening_iW hiB).1
  iY_mono := (C.mono_and_isThickening_iV hiB).1
  iB_mono := (C.mono_and_isThickening_iU hiB).1
  iX_thickening := (C.mono_and_isThickening_iW hiB).2
  iY_thickening := (C.mono_and_isThickening_iV hiB).2
  iB_thickening := (C.mono_and_isThickening_iU hiB).2
  comm_f := ObjectProperty.hom_ext _ (C.isPullback_source hiB).w
  comm_g := ObjectProperty.hom_ext _ (C.isPullback_target hiB).w
  isPullback_X :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) (C.isPullback_sourceBase hiB)
  isPullback_Y := IsPullback.of_map_of_faithful (ObjectProperty.ι _) (C.isPullback_target hiB)
  finiteType_Y' := C.tower.finiteType
  flat_X' := C.tower.flat
  finitePresentation_X' := C.tower.finitePresentation

end ThickenedChartTower

/-- A tower of smooth charts can be base-changed along a thickening of the ambient base. -/
theorem exists_thickenedChartTower {iB : ℬ ⟶ ℬ'} (hiB : IsThickening iB)
    {pY' : 𝒴' ⟶ ℬ'} {f' : 𝒳' ⟶ 𝒴'} (T : SmoothChartTower B S hS pY' f') :
    Nonempty (ThickenedChartTower B S hS iB pY' f') := by
  classical
  obtain ⟨AU, ⟨cartAU⟩, U, hU, ⟨eU⟩⟩ := exists_isTwoFibreProduct_represented B S hS T.a' iB.hom
    hiB.1.1 (isRepresentableByAlgebraicSpace_fibredCategory B S hS T.U' T.algebraicU)
  have hAUfst : IsRelativeThickening B S hS AU.fst :=
    isRelativeThickening_baseChange B S hS iB.hom T.a'
      (isRelativeThickening_of_isThickening B S hS hiB) AU cartAU
  obtain ⟨Qv, ⟨cartQv⟩, V, hV, ⟨eV⟩⟩ := exists_isTwoFibreProduct_represented B S hS
    (associatedMap B S hS T.g').1 AU.fst hAUfst.1
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS T.V' T.algebraicV)
  have hQvfst : IsRelativeThickening B S hS Qv.fst :=
    isRelativeThickening_baseChange B S hS AU.fst _ hAUfst Qv cartQv
  obtain ⟨Qw, ⟨cartQw⟩, W, hW, ⟨eW⟩⟩ := exists_isTwoFibreProduct_represented B S hS
    (associatedMap B S hS T.h').1 Qv.fst hQvfst.1
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS T.W' T.algebraicW)
  exact ⟨{ tower := T, AU := AU, cartAU := cartAU, Qv := Qv, cartQv := cartQv, Qw := Qw
           cartQw := cartQw, U := U, V := V, W := W, algU := hU, algV := hV, algW := hW
           eU := eU, eV := eV, eW := eW }⟩

/-! ### Flatness along a thickening of algebraic stacks -/

/-- Let `PX` and `PY` be 2-commutative squares over the cospans `(pX', iB)` and `(pY', iB)` —
their apexes are the restricted source and target, and their first projections the two
thickenings — and let `f` be a 1-morphism between their apexes together with two 2-cells: one
identifying `f` followed by the thickening of the target with the thickening of the source
followed by `f'`, the other identifying `f` followed by the structure 1-morphism of the restricted
target with that of the restricted source. If the cube commutes (`hcoh`), these data are a
pre-morphism from the square of the restricted source, read over the cospan `(pY', iB)` by
composing its first projection with `f'`, to the square of the restricted target. -/
noncomputable def restrictionPreHom
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    (PX : Bicategory.TwoCommSq pX' iB) (PY : Bicategory.TwoCommSq pY' iB)
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom) :
    Bicategory.TwoCommSq.PreHom
      (Bicategory.pasteOuterSq f'.hom
        (PX.underlying.reindexFst (algebraicStacksTwoIsoHom B S hS houter).symm))
      PY.underlying :=
  preHomOfStrict.{u, u, u + 1, u + 1} f.hom
    (algebraicStacksTwoIsoHom B S hS hrestrict).symm
    (algebraicStacksTwoIsoHom B S hS hinner).symm (by
      have hcohH : Bicategory.whiskerLeft f.hom PY.underlying.iso.hom ≫
          (Bicategory.whiskerRightIso
            (algebraicStacksTwoIsoHom B S hS hinner) iB.hom).hom =
          (Bicategory.whiskerRightIso
              (algebraicStacksTwoIsoHom B S hS hrestrict) pY'.hom).hom ≫
            (Bicategory.whiskerLeft PX.underlying.fst
              (algebraicStacksTwoIsoHom B S hS houter).hom ≫ PX.underlying.iso.hom) :=
        congrArg Bicategory.InducedBicategory.Hom₂.hom hcoh
      change (𝟙 ((PX.underlying.fst ≫ f'.hom) ≫ pY'.hom) ≫
          (Bicategory.whiskerLeft PX.underlying.fst
              (algebraicStacksTwoIsoHom B S hS houter).hom ≫ PX.underlying.iso.hom)) ≫
          (Bicategory.whiskerRightIso
            (algebraicStacksTwoIsoHom B S hS hinner) iB.hom).inv
        = (Bicategory.whiskerRightIso
            (algebraicStacksTwoIsoHom B S hS hrestrict) pY'.hom).inv ≫
          Bicategory.whiskerLeft f.hom PY.underlying.iso.hom
      rw [Category.id_comp]
      exact comp_inv_eq_inv_comp _ _ _ _ hcohH)

/-- Let `PX` and `PY` be 2-fibre products of `(pX', iB)` and `(pY', iB)`, and let the restricted
1-morphism `f` be flat, with 2-cells forming a commuting cube (`hcoh`). Then the morphism of
algebraic spaces `W ⟶ V` that a thickened chart tower carries is flat. -/
theorem isFlat_fWV
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (hfflat : AlgebraicStacks.IsFlat B S hS f)
    (C : ThickenedChartTower B S hS iB pY' f') :
    Space.IsFlat B S hS C.fWV := by
  classical
  set Pflat : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    (fun _ _ k => Space.IsFlat B S hS k) with hPflat
  have _inst : (spaceProperty B S hS Pflat).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have hflatloc : Space.IsSmoothLocalOnSourceAndTarget B S hS Pflat :=
    Space.isSmoothLocalOnSourceAndTarget_flat B S hS
  have hfflat' : HasPropertyOnSomeSmoothDiagram B S hS Pflat f.hom :=
    (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).1 hfflat
  have hPYu : Bicategory.IsTwoFibreProduct PY.underlying :=
    isTwoFibreProduct_underlying_algebraicStacks B S hS PY hcartY
  have hPXu : Bicategory.IsTwoFibreProduct PX.underlying :=
    isTwoFibreProduct_underlying_algebraicStacks B S hS PX hcartX
  have hSx : Bicategory.IsTwoFibreProduct
      (PX.underlying.reindexFst (algebraicStacksTwoIsoHom B S hS houter).symm) :=
    Bicategory.isTwoFibreProduct_reindexFst _ hPXu
  set XX := Bicategory.pasteInnerSq PY.underlying
    (restrictionPreHom B S hS PX PY houter hrestrict hinner hcoh) with hXXdef
  have hXX : Bicategory.IsTwoFibreProduct XX :=
    isTwoFibreProduct_pasteInnerSq B S hS PY.underlying hPYu hSx _
  have hGV : Bicategory.IsTwoFibreProduct
      ((C.AU.pasteFst C.Qv).reindexFst C.tower.targetComm) :=
    Bicategory.isTwoFibreProduct_reindexFst _
      (Bicategory.isTwoFibreProduct_pasteFst C.AU C.cartAU C.Qv C.cartQv)
  set cV := Bicategory.twoFibreProductPreHom hPYu
    (Bicategory.pasteOuterSq C.tower.b' ((C.AU.pasteFst C.Qv).reindexFst C.tower.targetComm))
    with hcVdef
  have hMV : Bicategory.IsTwoFibreProduct (Bicategory.pasteInnerSq PY.underlying cV) :=
    isTwoFibreProduct_pasteInnerSq B S hS PY.underlying hPYu hGV cV
  have hcVsm : IsRelativelySmooth B S hS cV.hom :=
    (isRelativelySmooth_isSurjectiveOnObjects_snd B S hS C.tower.b' PY.underlying.fst
      (Bicategory.pasteInnerSq PY.underlying cV) hMV C.tower.smoothB C.tower.surjectiveB).1
  set Dsq := twoFibreProductSquare.{u, u, u + 1, u + 1} C.tower.b' f'.hom with hDsqdef
  have hDsq : Bicategory.IsTwoFibreProduct Dsq :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} C.tower.b' f'.hom
  set cc := Bicategory.twoFibreProductPreHom hDsq
    (diagramCone B S hS f'.hom C.tower.c' C.tower.b' C.tower.h' C.tower.sourceComm) with hccdef
  have hccsm : IsRelativelySmooth B S hS cc.hom :=
    C.tower.smoothSourceComparison Dsq hDsq cc
  set Ev := twoFibreProductSquare.{u, u, u + 1, u + 1} C.Qv.fst Dsq.fst with hEvdef
  have hEv : Bicategory.IsTwoFibreProduct Ev :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} C.Qv.fst Dsq.fst
  set Pc := twoFibreProductSquare.{u, u, u + 1, u + 1} Ev.snd cc.hom with hPcdef
  have hPc : Bicategory.IsTwoFibreProduct Pc :=
    isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} Ev.snd cc.hom
  have hPcfst : IsRelativelySmooth B S hS Pc.fst :=
    isRelativelySmooth_baseChange.{u, u, u + 1} B S hS
      (fibredCategory B S hS C.tower.W') Dsq.pt Ev.pt cc.hom Ev.snd Pc hPc hccsm
  have hRc : Bicategory.IsTwoFibreProduct (Ev.swap.pasteFst Pc.swap) :=
    Bicategory.isTwoFibreProduct_pasteFst Ev.swap (Bicategory.isTwoFibreProduct_swap hEv)
      Pc.swap (Bicategory.isTwoFibreProduct_swap hPc)
  have hQwr : Bicategory.IsTwoFibreProduct (C.Qw.reindexFst cc.isoFst) :=
    Bicategory.isTwoFibreProduct_reindexFst _ C.cartQw
  set e₀ := Bicategory.twoFibreProductPreHom hRc (C.Qw.reindexFst cc.isoFst) with he₀def
  have he₀eq : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e₀.hom) :=
    Bicategory.isEquivalence_of_isTwoFibreProduct hQwr hRc e₀
  have hcompsm : IsRelativelySmooth B S hS (e₀.hom ≫ Pc.fst) :=
    isRelativelySmooth_of_isEquivalence_comp B S hS e₀.hom Pc.fst he₀eq hPcfst
  have hGv : Bicategory.IsTwoFibreProduct ((Dsq.pasteFst Ev).reindexFst cV.isoFst) :=
    Bicategory.isTwoFibreProduct_reindexFst _
      (Bicategory.isTwoFibreProduct_pasteFst Dsq hDsq Ev hEv)
  set pv := Bicategory.twoFibreProductPreHom (Bicategory.isTwoFibreProduct_swap hXX)
    (Bicategory.pasteOuterSq cV.hom ((Dsq.pasteFst Ev).reindexFst cV.isoFst)) with hpvdef
  have hNV : Bicategory.IsTwoFibreProduct (Bicategory.pasteInnerSq XX.swap pv) :=
    isTwoFibreProduct_pasteInnerSq B S hS XX.swap (Bicategory.isTwoFibreProduct_swap hXX) hGv pv
  have hbc : HasPropertyOnSomeSmoothDiagram B S hS Pflat
      (twoFibreProductSquare.{u, u, u + 1, u + 1} cV.hom f.hom).fst :=
    hasPropertyOnSomeSmoothDiagram_baseChange_of_isRepresentableByAlgebraicSpace B S hS Pflat
      f.hom cV.hom ⟨C.V, C.algV, ⟨C.eV⟩⟩ hfflat'
  have hEvfst : HasPropertyOnSomeSmoothDiagram B S hS Pflat Ev.fst :=
    hasPropertyOnSomeSmoothDiagram_fst_of_isTwoFibreProduct B S hS Pflat
      (twoFibreProductSquare.{u, u, u + 1, u + 1} cV.hom f.hom)
      (Bicategory.pasteInnerSq XX.swap pv)
      (isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} cV.hom f.hom) hNV hbc
  have hsmoothflat : HasPropertyOnSomeSmoothDiagram B S hS Pflat (e₀.hom ≫ Pc.fst) :=
    hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS Pflat (e₀.hom ≫ Pc.fst)
      C.W C.algW C.eW hcompsm (Space.isFlat_id B S hS C.algW)
  have hchain : HasPropertyOnSomeSmoothDiagram B S hS Pflat ((e₀.hom ≫ Pc.fst) ≫ Ev.fst) :=
    hasPropertyOnSomeSmoothDiagram_comp_of_precomp B S hS Pflat
      (fun hX hY hZ p q hp hq => hflatloc.precomp hX hY hZ p q hp hq)
      (fun hX hY hZ p q hp hq => Space.isFlat_comp B S hS hX hY hZ p q hp hq)
      (e₀.hom ≫ Pc.fst) Ev.fst hsmoothflat hEvfst
  have hQwsnd : HasPropertyOnSomeSmoothDiagram B S hS Pflat C.Qw.snd :=
    hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS Pflat e₀.isoSnd.symm hchain
  exact prop_representingMap_of_hasPropertyOnSomeSmoothDiagram B S hS Pflat hflatloc
    C.W C.V C.algW C.algV C.eW C.eV C.Qw.snd hQwsnd

/-- For a commutative diagram of algebraic stacks over `S` over a thickening `iB : ℬ ⟶ ℬ'` of
bases, whose cube commutes (`hcoh`), with `𝒴' ⟶ ℬ'` locally of finite type, `𝒳' ⟶ ℬ'` flat and
locally of finite presentation, the restricted 1-morphism `f` flat, and the two restricted stacks
the base changes of the ambient ones along `iB`, the ambient 1-morphism `f'` is flat. -/
@[stacks 0CJB "flatness of the ambient morphism"]
theorem isFlat_ambient_of_flatDeformation
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (hYft : AlgebraicStacks.IsLocallyOfFiniteType B S hS pY')
    (hXflat : AlgebraicStacks.IsFlat B S hS pX')
    (hXfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS pX')
    (hfflat : AlgebraicStacks.IsFlat B S hS f) :
    AlgebraicStacks.IsFlat B S hS f' := by
  classical
  obtain ⟨T⟩ := exists_smoothChartTower B S hS pX' pY' f' houter hYft hXflat hXfp
  obtain ⟨C⟩ := exists_thickenedChartTower B S hS hiB T
  have hflat : Space.IsFlat B S hS C.tower.h' :=
    Space.isFlat_of_flatDeformationDiagram B S hS (C.flatDeformationDiagram hiB)
      (isFlat_fWV B S hS hcartX hcartY houter hrestrict hinner hcoh hfflat C)
  exact (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f').2
    ⟨C.tower.W', C.tower.V', C.tower.algebraicW, C.tower.algebraicV, C.tower.c', C.tower.b',
      C.tower.h', ⟨C.tower.sourceComm⟩, C.tower.smoothC, C.tower.surjectiveC, C.tower.smoothB,
      hflat⟩

/-- Under the hypotheses of `AlgebraicGeometry.Stack.isFlat_ambient_of_flatDeformation`, the
structure 1-morphism `𝒴' ⟶ ℬ'` is flat, in the sense of Stacks 0CID, at every point of `|𝒴'|` in
the image of `|f'|`. -/
@[stacks 0CJB "flatness of the target over the base at image points"]
theorem isFlatAt_target_of_flatDeformation
    {iB : ℬ ⟶ ℬ'} {pX' : 𝒳' ⟶ ℬ'} {pY' : 𝒴' ⟶ ℬ'}
    {PX : Bicategory.TwoCommSq pX' iB} {PY : Bicategory.TwoCommSq pY' iB}
    {f : PX.pt ⟶ PY.pt} {f' : 𝒳' ⟶ 𝒴'}
    (hiB : IsThickening iB)
    (hcartX : Bicategory.IsTwoFibreProduct PX) (hcartY : Bicategory.IsTwoFibreProduct PY)
    (houter : f' ≫ pY' ≅ pX')
    (hrestrict : f ≫ PY.fst ≅ PX.fst ≫ f')
    (hinner : f ≫ PY.snd ≅ PX.snd)
    (hcoh : Bicategory.whiskerLeft f PY.iso.hom ≫ Bicategory.whiskerRight hinner.hom iB =
      Bicategory.whiskerRight hrestrict.hom pY' ≫
        Bicategory.whiskerLeft PX.fst houter.hom ≫ PX.iso.hom)
    (hYft : AlgebraicStacks.IsLocallyOfFiniteType B S hS pY')
    (hXflat : AlgebraicStacks.IsFlat B S hS pX')
    (hXfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS pX')
    (hfflat : AlgebraicStacks.IsFlat B S hS f)
    (x' : AlgebraicStacks.points B S hS 𝒳') :
    AlgebraicStacks.IsFlatAt B S hS pY' (AlgebraicStacks.pointsMap B S hS f' x') := by
  classical
  obtain ⟨T⟩ := exists_smoothChartTower B S hS pX' pY' f' houter hYft hXflat hXfp
  obtain ⟨C⟩ := exists_thickenedChartTower B S hS hiB T
  have hfWV := isFlat_fWV B S hS hcartX hcartY houter hrestrict hinner hcoh hfflat C
  have hsurj : Function.Surjective (spacePointMap B S hS C.tower.W' 𝒳'.val C.tower.c'.hom) := by
    rw [spacePointMap_surjective_iff_pointsMap_surjective]
    exact pointsMap_surjective_of_isSurjectiveOnObjects B S hS
      (𝒳 := algebraicSpaceStack.{u, w} B S hS C.tower.W' C.tower.algebraicW) (𝒴 := 𝒳')
      (Bicategory.InducedBicategory.mkHom C.tower.c') C.tower.surjectiveC
  obtain ⟨w, hw⟩ := hsurj x'
  have hat : Space.IsFlatAt B S hS C.tower.g'
      (Space.pointsMap B S hS C.tower.W' C.tower.h' w) :=
    Space.isFlatAt_target_of_flatDeformationDiagram B S hS (C.flatDeformationDiagram hiB)
      hfWV w
  refine ⟨{ U := C.tower.V', V := C.tower.U'
            algebraicU := C.tower.algebraicV, algebraicV := C.tower.algebraicU
            a := C.tower.b', b := C.tower.a', h := C.tower.g', iso := C.tower.targetComm
            u := Space.pointsMap B S hS C.tower.W' C.tower.h' w
            liesOver := ?_
            flatB := hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _
              C.tower.a' C.tower.U' C.tower.algebraicU
              (StacksRepresentableCFG.EquivalenceOver.refl _) C.tower.smoothA
              (Space.isFlat_id B S hS C.tower.algebraicU)
            flatComparison := fun Q hQ k =>
              hasPropertyOnSomeSmoothDiagram_of_isRelativelySmooth B S hS _ k.hom
                C.tower.V' C.tower.algebraicV
                (StacksRepresentableCFG.EquivalenceOver.refl _)
                (C.tower.smoothTargetComparison Q hQ k)
                (Space.isFlat_id B S hS C.tower.algebraicV) }, hat⟩
  have h2 : spacePointMap B S hS C.tower.W' 𝒴'.val
        (((associatedMap B S hS C.tower.h').1.hom).comp C.tower.b'.hom)
      = spacePointMap B S hS C.tower.W' 𝒴'.val (C.tower.c'.hom.comp f'.hom.hom) :=
    (spacePointMap_eq_pointsMap_comp B S hS C.tower.W' 𝒴'.val _).trans
      (((congrArg (fun m => m ∘ spacePointMap B S hS C.tower.W'
            (fibredCategory B S hS C.tower.W')
            (BasedFunctor.id (fibredCategory B S hS C.tower.W').val))
          (pointsMap_eq_of_basedNatTrans B S hS (fibredCategory B S hS C.tower.W').val
            (fibredCategory B S hS C.tower.W').property 𝒴'.val.property
            C.tower.sourceComm.hom.hom)).trans
        (spacePointMap_eq_pointsMap_comp B S hS C.tower.W' 𝒴'.val _).symm))
  calc spacePointMap B S hS C.tower.V' 𝒴'.val C.tower.b'.hom
          (Space.pointsMap B S hS C.tower.W' C.tower.h' w)
      = spacePointMap B S hS C.tower.W' 𝒴'.val
          (((associatedMap B S hS C.tower.h').1.hom).comp C.tower.b'.hom) w :=
        congrFun (spacePointMap_associatedMap_comp B S hS C.tower.h' 𝒴'.val
          C.tower.b'.hom).symm w
    _ = spacePointMap B S hS C.tower.W' 𝒴'.val (C.tower.c'.hom.comp f'.hom.hom) w := by
        rw [h2]
    _ = AlgebraicStacks.pointsMap B S hS f'
          (spacePointMap B S hS C.tower.W' 𝒳'.val C.tower.c'.hom w) :=
        congrFun (spacePointMap_comp B S hS C.tower.W' 𝒳'.val 𝒴'.val C.tower.c'.hom
          f'.hom.hom) w
    _ = AlgebraicStacks.pointsMap B S hS f' x' := by rw [hw]

end AlgebraicGeometry.Stack

end
