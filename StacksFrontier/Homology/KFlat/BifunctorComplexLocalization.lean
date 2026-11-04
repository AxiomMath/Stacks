module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SubcategoryLocalization
public import StacksFrontier.Homology.KFlat.BifunctorLocalization

/-!
# The derived category is the localization of the K-flat complexes

For an additive bifunctor `F : A ⥤ B ⥤ D` between abelian categories,
`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization` exhibits the derived category `D(B)` as
the localization of the K-flat *objects of the homotopy category* `K(B)` at the
quasi-isomorphisms between them.  This file takes the same localization one step earlier, on
the K-flat *complexes*: the full subcategory of `Comp(B)` spanned by the complexes whose class
in `K(B)` is K-flat for `F` localizes onto `D(B)` at the quasi-isomorphisms between those
complexes.

Two bifunctors on `D(B)` are therefore isomorphic as soon as each is a descent of one and the
same bifunctor on the K-flat complexes: `CategoryTheory.Localization.lift₂NatIso` applies to
the pair of localization functors recorded here.  That is what the comparisons of the derived
tensor product with its K-flat descent are built from, both over a ring and on a ringed site.

## Main definitions

* `CochainComplex.KFlatBifunctor.kFlatComplexQuasiIso`: the quasi-isomorphisms between K-flat
  complexes, as a morphism property of the full subcategory
  `CochainComplex.KFlatBifunctor.kFlatComplexes F` of K-flat complexes.

## Main results

* `CochainComplex.KFlatBifunctor.kFlatComplexQ_isLocalization`: `D(B)` is the localization of
  the K-flat complexes at the quasi-isomorphisms between them.  So a bifunctor on K-flat
  complexes inverting those quasi-isomorphisms descends to `D(B)`, and a pair of such descents
  of one bifunctor are isomorphic.

## Implementation notes

The localization is taken at the level of complexes rather than of objects of `K(B)` because
that is the level at which the K-flat comparison of a derived tensor product is stated: such a
comparison is an isomorphism at `DerivedCategory.Q.obj K` for a *complex* `K`, so along
`CochainComplex.KFlatBifunctor.kFlatComplexQ` it is a lifting datum verbatim, whereas a lifting
datum along `CochainComplex.KFlatBifunctor.kFlatQ` — whose source is the K-flat objects of the
*homotopy* category — would first have to be transported across
`DerivedCategory.quotientCompQhIso` in each variable.

No new property of complexes is introduced: the property
`CochainComplex.KFlatBifunctor.kFlatComplexes F` of
`StacksFrontier.Homology.KFlat.BifunctorLocalization` is already the one
`CategoryTheory.ObjectProperty.ι_comp_Q_isLocalization` consumes, being
`CategoryTheory.ObjectProperty.complexSubcategory (kFlatObjects F)` by `rfl`, and
`CochainComplex.KFlatBifunctor.kFlatComplexQ F` is already its inclusion followed by
`DerivedCategory.Q`.

Closure of the K-flat objects of `K(B)` under isomorphisms is carried as an instance binder,
exactly as `CategoryTheory.ObjectProperty.ι_comp_Q_isLocalization` carries it.  For a bifunctor
coming from a monoidal structure it is discharged by
`CochainComplex.KFlatMonoidal.kFlatObjects_isClosedUnderIsomorphisms`; carrying it keeps this
file independent of that monoidal specialization.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- The quasi-isomorphisms between K-flat complexes of objects of `B`. -/
abbrev kFlatComplexQuasiIso : MorphismProperty (kFlatComplexes F).FullSubcategory :=
  (HomologicalComplex.quasiIso B (ComplexShape.up ℤ)).inverseImage (kFlatComplexes F).ι

variable [(kFlatObjects F).IsClosedUnderIsomorphisms] [HasDerivedCategory B]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- **`D(B)` is the localization of the K-flat complexes at the quasi-isomorphisms between
them.**  So a bifunctor on K-flat complexes inverting those quasi-isomorphisms descends to
`D(B)`, and a pair of such descents of one bifunctor are isomorphic.

This is `CategoryTheory.ObjectProperty.ι_comp_Q_isLocalization` at the K-flat objects of
`K(B)`, whose own hypothesis — that `D(B)` is the localization of those objects — is
`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization`. -/
instance kFlatComplexQ_isLocalization :
    (kFlatComplexQ F).IsLocalization (kFlatComplexQuasiIso F) :=
  ObjectProperty.ι_comp_Q_isLocalization (kFlatObjects F)

end CochainComplex.KFlatBifunctor

end
