module

public import StacksFrontier.Algebra.Category.Grp.DirectSumCoproduct
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalkDecomposition
public import StacksFrontier.CategoryTheory.Adjunction.FamilyCoproductProduct

/-!
# The stalk decomposition of the direct image with compact support, as functors

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site and let `ȳ` be a geometric
point of `Y`. The stalk decomposition `(f_!F)_ȳ ≅ ⊕_{f(x̄) = ȳ} F_x̄` of Stacks 0F5F is an
isomorphism of functors: the composite of `f_!` with the stalk at `ȳ` is the coproduct, over the
geometric points of `X` lying over `ȳ`, of the stalk functors of `X` at those points.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fShriekStalkFunctorIso` — the stalk decomposition of `f_!` as an
  isomorphism of functors on abelian étale sheaves.

## Implementation notes

The objectwise decomposition `AlgebraicGeometry.SmallEtale.fShriekStalkIso` lands in the external
direct sum of the stalks, so it is composed with
`AddCommGrpCat.directSumCoproductIso`, which identifies that direct sum with the categorical
coproduct; the coproduct is the form in which the decomposition can be fed to
`CategoryTheory.Adjunction.sigmaFamily`. Naturality is the naturality of the two factors, which
is `AlgebraicGeometry.SmallEtale.fShriekStalkIso_natural` and
`AddCommGrpCat.directSumCoproductIso_natural`.

## References

* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 0F6P](https://stacks.math.columbia.edu/tag/0F6P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **Stacks 0F5F, part (1), as an isomorphism of functors.** The composite of the direct image
with compact support `f_!` with the stalk functor at a geometric point `ȳ` of `Y` is the
coproduct of the stalk functors of `X` at the geometric points lying over `ȳ`. -/
@[stacks 0F5F "part (1), stalk decomposition as an isomorphism of functors"]
public def fShriekStalkFunctorIso (s : GeometricPoint Y.obj) :
    fShriekFunctor.{u, v} B f ⋙ (geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v}) ≅
      Adjunction.sigmaFamily (fun x : GeometricFiberPoint B f s =>
        (geometricPointSitePoint B X.obj X.property (x.toGeometricPoint B f s)).sheafFiber
          (A := AddCommGrpCat.{max (u + 1) v})) :=
  NatIso.ofComponents
    (fun F => fShriekStalkIso.{u, v} B f s F ≪≫
      AddCommGrpCat.directSumCoproductIso.{u, max (u + 1) v}
        (fun x : GeometricFiberPoint B f s =>
          AddCommGrpCat.of ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) F.obj)))
    (fun {F G} φ => by
      have hn := fShriekStalkIso_natural.{u, v} B f s φ
      have hs := AddCommGrpCat.directSumCoproductIso_natural.{u, max (u + 1) v}
        (fun x : GeometricFiberPoint B f s =>
          AddCommGrpCat.of ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) F.obj))
        (fun x : GeometricFiberPoint B f s =>
          AddCommGrpCat.of ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) G.obj))
        (fun x => ((geometricPointSitePoint B X.obj X.property
          (x.toGeometricPoint B f s)).sheafFiber
            (A := AddCommGrpCat.{max (u + 1) v})).map φ)
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (AddCommGrpCat.directSumCoproductIso.{u, max (u + 1) v}
            (fun x : GeometricFiberPoint B f s => AddCommGrpCat.of
              ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) G.obj))).hom) hn).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun z => (fShriekStalkIso.{u, v} B f s F).hom ≫ z) hs).trans
              (Category.assoc _ _ _).symm))))

end AlgebraicGeometry.SmallEtale

end
