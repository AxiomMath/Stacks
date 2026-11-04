module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.InverseImageExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackPreservesFlatness

/-!
# The pullback of a K-flat complex along a morphism of ringed topoi

Let `f : (Sh(C), O_X) ⟶ (Sh(D), O_Y)` be a morphism of ringed topoi presented by a continuous
functor `f.u` of the underlying sites which is a morphism of sites, and let `f^*` be the abstract
module pullback `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`.  This file states the two
assertions of Stacks 0G7E — that the degreewise pullback of a K-flat complex with flat terms has
flat terms and is again K-flat — **with no hypothesis left over**.

## How the hypotheses are discharged

Every statement here is one application of a conditional result of the library:

* `Stacks.Sheaves.DerivedPullback.KFlatPullback.isFlat_pullbackComplex_X` and
  `Stacks.Sheaves.InverseImageExactness.kFlat_pullbackComplex` carry Stacks 05VD as a parameter,
  in the pointwise form `Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesIsFlat`
  and in the universally quantified form
  `Stacks.Sheaves.InverseImageExactness.PullbackPreservesIsFlatUniv` respectively.  The
  universally quantified form is the one the reduction of Stacks 0G6R consumes, because the
  source applies Stacks 05VD not to `f` but to the geometric half of its factorization.
* Both forms are theorems:
  `AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlat` and
  `AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlatUniv`.

## Main results

* `AlgebraicGeometry.RingedToposSiteHom.isFlat_pullbackComplex_X`: **the flat-terms assertion of
  Stacks 0G7E**, unconditional — every term of the degreewise pullback of a complex with flat
  terms is flat.
* `AlgebraicGeometry.RingedToposSiteHom.kFlat_pullbackComplex`: **the K-flatness assertion of
  Stacks 0G7E**, unconditional — the degreewise pullback of a K-flat complex with flat terms is
  K-flat.

## Implementation notes

*Why the names are reused in a second namespace.*  The conditional forms
`Stacks.Sheaves.DerivedPullback.KFlatPullback.isFlat_pullbackComplex_X` and
`Stacks.Sheaves.InverseImageExactness.kFlat_pullbackComplex` keep their names in their own
namespaces; the statements below are the same conclusions with the Stacks 05VD hypothesis
removed, and they live in `AlgebraicGeometry.RingedToposSiteHom` beside the morphism they are
about, so no name is shadowed.

*No tag is placed in this file, and that is a judgement rather than an omission.*  Stacks 0G6R is
already carried by `Stacks.Sheaves.RingedToposModules.shortExact_map_pullbackModules` for the
pullback that Stacks 03D6 part (2) constructs, and the two Stacks 0G7E consequences below are
stated under instance hypotheses on `Stacks.SheafOfModules.Tensor.sheafTensor` that the source
does not carry.  So none of them is a new assertion of the source.

*Universes.*  Everything is at `AlgebraicGeometry.RingedTopos.{u, u, u}`.  The narrowing is
inherited from the results applied, not chosen here; its four independent forcings on this chain
are recorded in the implementation notes of
`Stacks.Sheaves.DerivedPullback.FlatExtendScalars.pullbackPreservesIsFlat_of_auxHomG`'s module
and of `Stacks.Sheaves.InverseImageExactness.pullbackPreservesShortExact`'s module.

## References

* [The Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [The Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [The Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedToposSiteHom

noncomputable section

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y)

variable [HasSheafify Y.J AddCommGrpCat.{u}]

/-- **The flat-terms assertion of Stacks Tag 0G7E**, unconditional: every term of the degreewise
pullback of a complex with flat terms is flat.

The term of the degreewise pullback in degree `i` is `f^*(K^i)` on the nose, so this is Stacks
05VD once per degree; `AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlat` supplies
it. -/
theorem isFlat_pullbackComplex_X (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (K.X i)) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      (((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K).X i) :=
  Stacks.Sheaves.DerivedPullback.KFlatPullback.isFlat_pullbackComplex_X f hmos
    (pullbackPreservesIsFlat f) K hflatK i

section Consumer

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **The K-flatness assertion of Stacks Tag 0G7E**, unconditional: the degreewise pullback of a
K-flat complex with flat terms is K-flat.

`Stacks.Sheaves.InverseImageExactness.kFlat_pullbackComplex` takes universally quantified
Stacks 05VD as its only hypothesis, and
`AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlatUniv` supplies it. -/
theorem kFlat_pullbackComplex (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat.KFlat Y.O K)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (K.X i)) :
    Stacks.SheafOfModules.KFlat.KFlat X.O
      ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K) :=
  Stacks.Sheaves.InverseImageExactness.kFlat_pullbackComplex f hmos
    pullbackPreservesIsFlatUniv.{u} K hK hflatK

end Consumer

end

end AlgebraicGeometry.RingedToposSiteHom

end
