module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfToSmallEtale
public import StacksFrontier.CategoryTheory.Adjunction.CategoricalPullbackFullyFaithful

/-!
# Triples of a small étale sheaf, a big fppf sheaf and a comparison

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site of
algebraic spaces over the same big fppf site of schemes, and `f : X ⟶ Y` a morphism of `T`.
Write `a_X` for the morphism from the big fppf topos of `X` to its small étale topos (Stacks
0DGI), `f_small` for the morphism of small étale topoi and `f_{big,fppf}` for that of big fppf
topoi. This file sets up the category of triples `(G, H, α)` with `G ∈ Sh(X_étale)`,
`H ∈ Sh((Spaces/Y)_fppf)` and `α : a_X⁻¹G ≅ f_{big,fppf}⁻¹H`, and the canonical functor
`F ↦ (f_small⁻¹F, a_Y⁻¹F, can)` into it.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.fppfSmallEtaleInverseImageCommIso`: the canonical
  isomorphism `can : f_small⁻¹ ⋙ a_X⁻¹ ≅ a_Y⁻¹ ⋙ f_{big,fppf}⁻¹`, conjugate to the big
  fppf–small étale square of Stacks 0DGI.
* `AlgebraicGeometry.BigFppfSpaceSite.fppfSmallEtaleTripleFunctor`: the canonical functor into
  the two-fibre product `a_X⁻¹ ⊡ f_{big,fppf}⁻¹`, whose objects are exactly the triples.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isEquivalence_fppfSmallEtaleTripleFunctor_of_essImage`:
  the canonical functor is an equivalence as soon as `a_X⁻¹` and `a_Y⁻¹` are fully faithful and
  a big fppf sheaf `H` on `Y` lies in the essential image of `a_Y⁻¹` whenever
  `f_{big,fppf}⁻¹H` lies in that of `a_X⁻¹`. This is the first paragraph of the proof of
  Stacks 0DGL.

## References

* [Stacks Project, Tag 0DGI](https://stacks.math.columbia.edu/tag/0DGI)
* [Stacks Project, Tag 0DGL](https://stacks.math.columbia.edu/tag/0DGL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite) {X Y : T.Spaces} (f : X ⟶ Y)

/-- **The canonical isomorphism `can : f_small⁻¹ ⋙ a_X⁻¹ ≅ a_Y⁻¹ ⋙ f_{big,fppf}⁻¹`** of the
square of topoi of Stacks 0DGI: the conjugate of the identification
`AlgebraicGeometry.BigFppfSpaceSite.bigFppfSmallEtale_pushforwardCommIso` of the composite
direct images. -/
def fppfSmallEtaleInverseImageCommIso :
    (E.smallEtaleMorphism (etaleMap T E h f)).inverseImage ⋙
        (fppfToSmallEtaleMorphism T E h X).inverseImage ≅
      (fppfToSmallEtaleMorphism T E h Y).inverseImage ⋙ (bigFppfMorphism T f).inverseImage :=
  ((conjugateIsoEquiv
      ((E.smallEtaleMorphism (etaleMap T E h f)).comp (fppfToSmallEtaleMorphism T E h X)).adj
      ((fppfToSmallEtaleMorphism T E h Y).comp (bigFppfMorphism T f)).adj).symm
    (bigFppfSmallEtale_pushforwardCommIso T E h f)).symm

/-- **The canonical functor of Stacks 0DGL.** It sends a small étale sheaf `F` on `Y` to the
triple `(f_small⁻¹F, a_Y⁻¹F, can)` of the two-fibre product `a_X⁻¹ ⊡ f_{big,fppf}⁻¹`, whose
objects are the triples `(G, H, α)` with `G` a small étale sheaf on `X`, `H` a big fppf sheaf
on `Y` and `α : a_X⁻¹G ≅ f_{big,fppf}⁻¹H` an isomorphism. -/
abbrev fppfSmallEtaleTripleFunctor :
    Sheaf (Space.SpacesEtale.topology E.fppfSite S E.fppf_mem (etaleSpace T E h Y))
        (Type (u + 1)) ⥤
      CategoricalPullback (fppfToSmallEtaleMorphism T E h X).inverseImage
        (bigFppfMorphism T f).inverseImage :=
  Stacks.CategoryTheory.modificationGluingFunctor (fppfSmallEtaleInverseImageCommIso T E h f)

/-- **The first paragraph of the proof of Stacks 0DGL.** If `a_X⁻¹` and `a_Y⁻¹` are fully
faithful, the canonical functor into the triples is fully faithful, and it is an equivalence as
soon as every big fppf sheaf `H` on `Y` with `f_{big,fppf}⁻¹H` in the essential image of `a_X⁻¹`
is itself in the essential image of `a_Y⁻¹`. -/
theorem isEquivalence_fppfSmallEtaleTripleFunctor_of_essImage
    [(fppfToSmallEtaleMorphism T E h X).inverseImage.Full]
    [(fppfToSmallEtaleMorphism T E h X).inverseImage.Faithful]
    [(fppfToSmallEtaleMorphism T E h Y).inverseImage.Full]
    [(fppfToSmallEtaleMorphism T E h Y).inverseImage.Faithful]
    (hdesc : ∀ H : Sheaf (BigFppfSpaceOver.topology T Y) (Type (u + 1)),
      (fppfToSmallEtaleMorphism T E h X).inverseImage.essImage
          ((bigFppfMorphism T f).inverseImage.obj H) →
        (fppfToSmallEtaleMorphism T E h Y).inverseImage.essImage H) :
    (fppfSmallEtaleTripleFunctor T E h f).IsEquivalence :=
  Stacks.CategoryTheory.modificationGluingFunctor_isEquivalence_of_snd _
    fun Z => hdesc Z.snd ⟨Z.fst, ⟨Z.iso⟩⟩

end AlgebraicGeometry.BigFppfSpaceSite

end
