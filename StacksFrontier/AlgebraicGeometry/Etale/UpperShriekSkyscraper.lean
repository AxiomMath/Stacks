module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalkFunctorDecomposition
public import StacksFrontier.AlgebraicGeometry.Etale.GeometricSkyscraper
public import StacksFrontier.AlgebraicGeometry.Etale.UpperShriekQuasiFinite

/-!
# The upper shriek of a skyscraper sheaf at a geometric point

Let `f : X ⟶ Y` be a locally quasi-finite separated morphism of a big étale site, let `ȳ` be a
geometric point of `Y` and let `A` be an abelian group. Then `f^!(ȳ_* A)` is the product of the
skyscrapers `x̄_* A` over the geometric points `x̄` of `X` lying over `ȳ`, naturally in `A`. This
is Stacks 0F59, part (2).

## Main definitions

* `AlgebraicGeometry.SmallEtale.fUpperShriekSkyscraperIso` — the isomorphism of functors
  `ȳ_* ⋙ f^! ≅ ∏_{f(x̄) = ȳ} x̄_*`.
* `AlgebraicGeometry.SmallEtale.fUpperShriekSkyscraperObjIso` — its value
  `f^!(ȳ_* A) ≅ ∏_{f(x̄) = ȳ} x̄_* A` at an abelian group `A`.

## Implementation notes

The proof is the uniqueness of right adjoints, and no computation with sections or germs occurs.
The functor `ȳ_* ⋙ f^!` is right adjoint to `f_! ⋙ (−)_ȳ`, being a composite of right adjoints;
the stalk decomposition of Stacks 0F5F, in the functorial form
`AlgebraicGeometry.SmallEtale.fShriekStalkFunctorIso`, identifies `f_! ⋙ (−)_ȳ` with the
coproduct of the stalk functors `(−)_x̄` over the geometric fibre; and the coproduct of a family
of left adjoints is left adjoint to the product of the right adjoints, which is
`CategoryTheory.Adjunction.sigmaFamilyAdjunction`. So `ȳ_* ⋙ f^!` and `∏_{x̄} x̄_*` are both
right adjoint to the same functor.

## References

* [Stacks Project, Tag 0F59](https://stacks.math.columbia.edu/tag/0F59)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 04FM](https://stacks.math.columbia.edu/tag/04FM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (s : GeometricPoint Y.obj)

/-- **Stacks 0F59, part (2).** For a locally quasi-finite morphism `f : X ⟶ Y` and a geometric
point `ȳ` of `Y`, the upper shriek of the skyscraper at `ȳ` is the product of the skyscrapers
over the geometric points of `X` lying over `ȳ`: `f^!(ȳ_* A) ≅ ∏_{f(x̄) = ȳ} x̄_* A`, naturally
in the abelian group `A`. -/
@[stacks 0F59 "part (2), f^!(ȳ_* A) ≅ ∏_{f(x̄) = ȳ} x̄_* A, naturally in A"]
public def fUpperShriekSkyscraperIso :
    etaleSkyscraperFunctor B Y.obj Y.property s AddCommGrpCat.{max (u + 1) v} ⋙
        fUpperShriekFunctor.{u, v} B f ≅
      Adjunction.piFamily (fun x : GeometricFiberPoint B f s =>
        etaleSkyscraperFunctor B X.obj X.property (x.toGeometricPoint B f s)
          AddCommGrpCat.{max (u + 1) v}) :=
  Adjunction.rightAdjointIsoPiFamily _ _
    (fun x : GeometricFiberPoint B f s =>
      etaleStalkSkyscraperAdjunction B X.obj X.property (x.toGeometricPoint B f s)
        AddCommGrpCat.{max (u + 1) v})
    ((fShriekAdjunction.{u, v} B f).comp
      (etaleStalkSkyscraperAdjunction B Y.obj Y.property s AddCommGrpCat.{max (u + 1) v}))
    (fShriekStalkFunctorIso.{u, v} B f s)

/-- **Stacks 0F59, part (2).** The value of the isomorphism at an abelian group `A`:
`f^!(ȳ_* A) ≅ ∏_{f(x̄) = ȳ} x̄_* A`. -/
@[stacks 0F59 "part (2), the formula at a given abelian group A"]
public def fUpperShriekSkyscraperObjIso (M : AddCommGrpCat.{max (u + 1) v}) :
    (fUpperShriekFunctor.{u, v} B f).obj
        (etaleSkyscraper B Y.obj Y.property s AddCommGrpCat.{max (u + 1) v} M) ≅
      ∏ᶜ fun x : GeometricFiberPoint B f s =>
        etaleSkyscraper B X.obj X.property (x.toGeometricPoint B f s)
          AddCommGrpCat.{max (u + 1) v} M :=
  (fUpperShriekSkyscraperIso.{u, v} B f s).app M

end AlgebraicGeometry.SmallEtale

end
