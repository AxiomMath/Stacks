module

public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor

/-!
# A bifunctor against two factors concentrated in degree zero

Let `F : A ⥤ B ⥤ D` be a bifunctor, additive in each variable, between abelian categories, and
let `M`, `N` be objects of `A` and `B`.  Applying `F` to `M` and `N`, each placed in degree `0`,
gives a double complex concentrated in the single spot `(0, 0)`, so its total complex is
`F(M, N)` placed in degree `0`:

`Tot(F(M[0], N[0])) ≅ F(M, N)[0]`.

This is the identification that carries a statement about sheaves of modules into a statement
about complexes of them, and from there — through the K-flat comparison of the derived monoidal
structure — into the derived category.

## Main definitions

* `CochainComplex.KFlatBifunctor.mapBifunctorSingleBothIso`: `Tot(F(M[0], N[0])) ≅ F(M, N)[0]`.

## Main results

* `CochainComplex.KFlatBifunctor.rowComplex_eq_mapHomologicalComplex`: the termwise complex
  `p ↦ F(G^p, N)` is `F(-, N)` applied degreewise to `G`.  The two sides are the same complex;
  the identification is recorded in a single declaration so that no proof has to reconcile the
  spelling `CochainComplex.KFlatBifunctor.rowComplex` — which the single-row comparison of Tag
  06YQ produces — with the `Functor.mapHomologicalComplex` spelling that Mathlib's
  `HomologicalComplex.singleMapHomologicalComplex` consumes.

## Implementation notes

The isomorphism is a composite of three identifications, none of them built by hand:
`CochainComplex.KFlatBifunctor.totalSingleIso` for the second factor, the spelling equality
above, and Mathlib's `HomologicalComplex.singleMapHomologicalComplex` for the additive functor
`F(-, N)`.  In particular no comparison of a term of a total complex with a value of the
bifunctor is written out, and the Koszul signs never appear: the only spot of the double complex
that survives is `(0, 0)`, where the sign is `1`.

The additivity of `F(-, N)` — that is, of `F.flip.obj N` — is carried as an instance binder
rather than derived from `F.Additive`, because the two are not the same statement for a
bifunctor and because a consumer at a concrete bifunctor has it from its own monoidal
preadditivity.

Companion to `CochainComplex.KFlatBifunctor.rowComplex_flip_eq` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.CyclesOfAnAcyclicKFlatComplex`, which records
the same identification for the transposed bifunctor, i.e. for a first factor concentrated in
degree zero.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive]

omit [Abelian B] in
/-- The termwise complex `p ↦ F(G^p, N)` is `F(-, N)` applied degreewise to `G`.  The two sides
are the same complex; this records the identification in a single declaration so that the two
spellings never have to be reconciled inside a proof. -/
public theorem rowComplex_eq_mapHomologicalComplex (G : CochainComplex A ℤ) (N : B)
    [(F.flip.obj N).Additive] :
    rowComplex F G N = ((F.flip.obj N).mapHomologicalComplex (ComplexShape.up ℤ)).obj G :=
  rfl

variable [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

/-- **Two factors concentrated in degree zero make the total complex their image in degree
zero**: `Tot(F(M[0], N[0])) ≅ F(M, N)[0]`.

The double complex is concentrated in the spot `(0, 0)`.  Rather than compare its total complex
with that spot by hand, the second factor is handled by `totalSingleIso`, which gives
the termwise complex `p ↦ F(M[0]^p, N)`, and the first factor by Mathlib's
`HomologicalComplex.singleMapHomologicalComplex` for the additive functor `F(-, N)`, the two
spellings of the termwise complex being identified by
`rowComplex_eq_mapHomologicalComplex`. -/
public def mapBifunctorSingleBothIso (M : A) (N : B) [(F.flip.obj N).Additive] :
    HomologicalComplex.mapBifunctor ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M)
        ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj N) F (ComplexShape.up ℤ) ≅
      (HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj ((F.obj M).obj N) :=
  totalSingleIso F ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M) N ≪≫
    eqToIso (rowComplex_eq_mapHomologicalComplex F _ N) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex (F.flip.obj N)
      (ComplexShape.up ℤ) 0).app M

end CochainComplex.KFlatBifunctor

end
