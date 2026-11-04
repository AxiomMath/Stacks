module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityQuotientStackTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenRelationEtaleQuotientEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenSubgroupoidQuotientStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Unconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackProjectionRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Sheafification
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The quotient stack of an open subgroupoid is étale over the quotient stack

Let `φ : (U, P, s|_P, t|_P, c|_P) ⟶ (U, R, s, t, c)` be the inclusion of an open subgroupoid of a
groupoid in algebraic spaces over an algebraic space `B`, encoded as a morphism of groupoids whose
map on objects is an isomorphism and whose map on arrows is an open immersion, and assume `s` is
flat and locally of finite presentation. This file proves the étaleness clause of **Stacks 0DU2**:
the 1-morphism `[φ] : [U/P] ⟶ [U/R]` of Stacks 046Q, once representable by algebraic spaces, is
étale in the sense of Stacks 03YK.

## The argument

It is the source's. Étaleness of morphisms of algebraic spaces is stable under base change
(Stacks 03FU) and local on the target for the fppf topology (Stacks 042B), so by Stacks 045D it
may be checked after base change along the projection `π : S_U ⟶ [U/R]` of Stacks 044R, which is
locally essentially surjective with no hypothesis on the groupoid. By **Stacks 04Y4** that base
change is the quotient stack `[U''/R'']` of the auxiliary groupoid of Section 78.21, with its
descended morphism to `U`; the pre-relation of the auxiliary groupoid over `U` is an open
immersion, so by **Stacks 0DU1** `[U''/R'']` is the algebraic space `U''/R''` and the leg is the
étale structure morphism `U''/R'' ⟶ U`.

## Main definitions

* `AlgebraicGeometry.Stack.auxQuotientSquareFibred`: the square of Stacks 04Y4, read in the
  2-category of categories fibred in groupoids over the big fppf site.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_auxQuotientComparison`: the comparison 1-morphism of
  Stacks 04Y4 is an equivalence of the underlying categories.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_auxQuotientSquareFibred`: **Stacks 04Y4** in the
  2-category of categories fibred in groupoids, which is where Stacks 045D needs it.
* `AlgebraicGeometry.Stack.hasRelativeProperty_etale_quotientStackMap`: the 1-morphism
  `[U/P] ⟶ [U/R]` is étale in the sense of Stacks 03YK.

## Implementation notes

Stacks 04Y4 is proved in the library as a 2-fibre product of *stacks* in groupoids, a weaker
universal property than a 2-fibre product of categories fibred in groupoids. The proof is re-run
here against the canonical 2-fibre product of categories fibred in groupoids, exactly as
`AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquareFibred` does for Stacks 04ZN: the
mediating pre-morphism into it has underlying functor the comparison of Stacks 04Y4 on the nose.

The auxiliary groupoid enters twice, over `B`
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxGroupoid`, the form Stacks 04Y4 uses) and over `U`
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxGroupoidOverTargetObjects`, the form Stacks 0DU1
applies to). The two have the same objects, arrows, source, target, composition and pointwise
groupoids, so they have the same quotient stack definitionally, and the 0DU1 comparison of the
second is a 1-morphism out of the quotient stack of the first.

## References

* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 042B](https://stacks.math.columbia.edu/tag/042B)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 04Y4](https://stacks.math.columbia.edu/tag/04Y4)
* [Stacks Project, Tag 0DU1](https://stacks.math.columbia.edu/tag/0DU1)
* [Stacks Project, Tag 0DU2](https://stacks.math.columbia.edu/tag/0DU2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-- **The square of Stacks 04Y4, read in the 2-category of categories fibred in groupoids.**
Apex, legs and filler are those of `AlgebraicGeometry.Stack.auxQuotientSquare`; only the ambient
2-category differs. -/
noncomputable def auxQuotientSquareFibred (φ : Hom G G') :
    Bicategory.TwoCommSq
      (Bicategory.InducedBicategory.mkHom (quotientStackMap φ) :
        quotientStackCFG C S hS G ⟶ quotientStackCFG C S hS G')
      (Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection G') :
        liftedSpaceStack G'.objects ⟶ quotientStackCFG C S hS G') where
  pt := quotientStackCFG C S hS (auxGroupoid φ)
  fst := Bicategory.InducedBicategory.mkHom (auxQuotientToSource φ)
  snd := Bicategory.InducedBicategory.mkHom (auxLiftedQuotientStackToObjects φ)
  iso := Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso (auxSquareCell φ) (auxSquareCell_isHomLift φ))

/-- **The comparison 1-morphism of Stacks 04Y4 is an equivalence of categories**: it is an
equivalence over the site by `AlgebraicGeometry.Stack.isEquivalenceOver_auxQuotientComparison`. -/
theorem isEquivalence_auxQuotientComparison (φ : Hom G G') :
    (auxQuotientComparison φ).IsEquivalence := by
  obtain ⟨hequiv⟩ := isEquivalenceOver_auxQuotientComparison φ
  exact (CategoryTheory.Equivalence.mk (auxQuotientComparison φ) hequiv.inv
    hequiv.unitIso.symm hequiv.counitIso).isEquivalence_functor

/-- **Stacks 04Y4 in the 2-category of categories fibred in groupoids.** The square
`AlgebraicGeometry.Stack.auxQuotientSquareFibred` is a 2-fibre product (Stacks 003Q) of
categories fibred in groupoids over the big fppf site: the pre-morphism of Stacks 003O into the
canonical 2-fibre product has underlying functor the comparison of Stacks 04Y4, which is an
equivalence, and terminality transports along it. -/
noncomputable def isTwoFibreProduct_auxQuotientSquareFibred (φ : Hom G G') :
    Bicategory.IsTwoFibreProduct (auxQuotientSquareFibred φ) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _)
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _
      (auxQuotientSquareFibred φ))
    (isEquivalence_auxQuotientComparison φ)

/-- The square of Stacks 04Y4 over the cospan `(π, [φ])`, in the orientation Stacks 045D
consumes: its first leg is the descended morphism `[U''/R''] ⟶ S_{U'}`. -/
noncomputable abbrev auxQuotientSquareFibredSwap (φ : Hom G G') :
    Bicategory.TwoCommSq (quotientStackProjectionHom G') (quotientStackMapCFGHom φ) :=
  (auxQuotientSquareFibred φ).swap

/-- The swapped square of Stacks 04Y4 is a 2-fibre product of categories fibred in groupoids. -/
noncomputable def isTwoFibreProduct_auxQuotientSquareFibredSwap (φ : Hom G G') :
    Bicategory.IsTwoFibreProduct (auxQuotientSquareFibredSwap φ) :=
  Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_auxQuotientSquareFibred φ)

/-- **The 0DU1 comparison of the auxiliary groupoid, against the first leg of the square.** The
comparison `[U''/R''] ⟶ U''/R''` followed by the structure morphism `U''/R'' ⟶ U'` is the
descended morphism `[U''/R''] ⟶ S_{U'}` followed by the comparison of morphism universes. -/
theorem quotientStackToQuotientSheaf_comp_auxToTargetObjects (φ : Hom G G')
    (hflat : Space.IsFlat C S hS (auxGroupoidOverTargetObjects φ).objectsToBase.hom)
    (hlfp : Space.IsLocallyOfFinitePresentation C S hS
      (auxGroupoidOverTargetObjects φ).objectsToBase.hom)
    (hopen : Space.IsOpenImmersion C S hS
      (Space.groupoidPreRelation (auxGroupoidOverTargetObjects φ)).left) :
    BasedFunctor.comp
        (quotientStackToQuotientSheaf (auxGroupoidOverTargetObjects φ) hflat hlfp hopen)
        (associatedMap C S hS
          (quotientSheafToBaseSpace (auxGroupoidOverTargetObjects φ) hflat hlfp hopen).hom).1.hom =
      BasedFunctor.comp (auxLiftedQuotientStackToObjects φ)
        (liftedFibredCategoryDown G'.objects) :=
  quotientStackToQuotientSheaf_comp_toBase (auxGroupoidOverTargetObjects φ) hflat hlfp hopen

/-- **Stacks 0DU2, étaleness.** Let `φ : G ⟶ H` be a morphism of groupoids in algebraic spaces
over `B` whose map on objects is an isomorphism and whose map on arrows is an open immersion —
the inclusion of an open subgroupoid `(U, P, s|_P, t|_P, c|_P)` of `(U, R, s, t, c)` — and let the
source map of `H` be flat and locally of finite presentation. If the 1-morphism
`[φ] : [U/P] ⟶ [U/R]` of Stacks 046Q is representable by algebraic spaces, it is étale in the
sense of Stacks 03YK.

By Stacks 045D it suffices that the base change of `[φ]` along `π : S_U ⟶ [U/R]` be étale; by
Stacks 04Y4 that base change is `[U''/R''] ⟶ S_U`, which by Stacks 0DU1 is the étale structure
morphism `U''/R'' ⟶ U` of the quotient of the auxiliary groupoid. The representability
hypothesis is what Stacks 03YK presupposes in order to speak of the relative property; it is
discharged in the full statement of Stacks 0DU2. -/
theorem hasRelativeProperty_etale_quotientStackMap {H : GroupoidInAlgebraicSpaces C S hS B}
    (φ : Hom G H) (hobj : IsIso φ.toGroupoidHom.mapObjects)
    (hopen : Space.IsOpenImmersion C S hS φ.toGroupoidHom.mapArrows)
    (hsflat : Space.IsFlat C S hS H.source.hom)
    (hslfp : Space.IsLocallyOfFinitePresentation C S hS H.source.hom)
    (hrep : IsRepresentableByAlgebraicSpaces C S hS (quotientStackMap φ)) :
    HasRelativeProperty.{u, u + 1, u + 1, u} C S hS (Space.etaleMorphisms C S hS)
      (quotientStackMapCFGHom φ) hrep := by
  let G'' := auxGroupoidOverTargetObjects φ
  have hflat := isFlat_auxToTargetObjects φ hobj hsflat
  have hlfp := isLocallyOfFinitePresentation_auxToTargetObjects φ hobj hslfp
  have hopen'' := isOpenImmersion_auxGroupoidPreRelation φ hobj hopen
  let X : AlgebraicSpaces C S hS := quotientSheafSpace G'' hflat hlfp hopen''
  let Q := auxQuotientSquareFibredSwap φ
  have hQ : Bicategory.IsTwoFibreProduct Q := isTwoFibreProduct_auxQuotientSquareFibredSwap φ
  have hQfst : IsRepresentableByAlgebraicSpaces C S hS Q.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u + 1, u + 1} C S hS _ _ _
      (quotientStackMapCFGHom φ) (quotientStackProjectionHom H) Q hQ hrep
  let p : Q.pt.val ⥤ᵇ (fibredCategory C S hS X.obj).val :=
    quotientStackToQuotientSheaf G'' hflat hlfp hopen''
  have : p.toFunctor.IsEquivalence :=
    isEquivalence_quotientStackToQuotientSheaf G'' hflat hlfp hopen''
  let q : (liftedObjectSpace H).val ⥤ᵇ (fibredCategory C S hS H.objects.obj).val :=
    liftedFibredCategoryDown H.objects
  have : q.toFunctor.IsEquivalence := isEquivalence_liftedFibredCategoryDown H.objects
  let a := (associatedMap C S hS (quotientSheafToBaseSpace G'' hflat hlfp hopen'').hom).1
  have α : BasedFunctor.comp p a.hom ≅ BasedFunctor.comp Q.fst.hom q :=
    eqToIso (quotientStackToQuotientSheaf_comp_auxToTargetObjects φ hflat hlfp hopen'')
  have hprop : Space.etaleMorphisms C S hS
      (ObjectProperty.homMk (representingMap C S hS (fibredCategory C S hS X.obj)
        (fibredCategory C S hS H.objects.obj) X.obj H.objects.obj
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (StacksRepresentableCFG.EquivalenceOver.refl _) a) :
        (⟨X.obj, X.property⟩ : AlgebraicSpaces C S hS) ⟶ ⟨H.objects.obj, H.objects.property⟩) := by
    show Space.IsEtale C S hS (representingMap C S hS _ _ _ _ _ _ a)
    rw [representingMap_associatedMap]
    exact isEtale_auxQuotientSheafToBase φ hobj hopen hsflat hslfp
  exact hasRelativeProperty_of_baseChange.{u, u + 1, u + 1, u} C S hS _ _ _
    (Space.etaleMorphisms C S hS) (quotientStackMapCFGHom φ) (quotientStackProjectionHom H)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _)
    hrep (localEssSurj_quotientStackProjectionHom H)
    (hasRelativeProperty_fst_of_isTwoFibreProduct_representingMap C S hS
      (Space.etaleMorphisms C S hS)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _)
      hQ _ hQfst a (isRepresentableByAlgebraicSpaces_associatedMap _) p q α X.obj H.objects.obj
      X.property H.objects.property (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) hprop)

end AlgebraicGeometry.Stack

end
