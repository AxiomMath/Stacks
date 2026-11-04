module

public import StacksFrontier.AlgebraicGeometry.FlagTower.Grassmannian
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Grassmannian

/-!
# `X × G(l, n)_k` is the Grassmannian of `X`

For a smooth projective scheme `X` over a field `k`, the product `X × G(l, n)` of Section 45.14
is the fibre product `X ×_{Spec k} G(l, n)_k` of `X` with the object
`Stacks.WeilCohomology.SmoothProjectiveScheme.grassmannian k l n`. Since
`G(l, n)_k = Spec k ×_{Spec ℤ} G(l, n)`, pasting the two cartesian squares identifies it with
`G(l, n)_X = X ×_{Spec ℤ} G(l, n)` (`AlgebraicGeometry.Grassmannian.schemeOver l n X`), compatibly
with the projections to `X`. This is the base over which tower A of
`StacksFrontier.AlgebraicGeometry.FlagTower.Grassmannian` is built, so that file applies to
`X × G(l, n)` through `Stacks.FlagTower.productGrassmannianIso`.

## Main definitions

* `Stacks.FlagTower.productGrassmannianIso`: `X ×_k G(l, n)_k ≅ G(l, n)_X`.

## References

* [Stacks Project, Tag 0FIQ](https://stacks.math.columbia.edu/tag/0FIQ)
* [Stacks Project, Tag 089U](https://stacks.math.columbia.edu/tag/089U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.WeilCohomology

universe u

namespace Stacks.FlagTower

variable (k : Type u) [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory) (l n : ℕ)

/-- **The product `X × G(l, n)` over `k` is the Grassmannian of `X`**: the fibre product
`X ×_{Spec k} G(l, n)_k` is `G(l, n)_X = X ×_{Spec ℤ} G(l, n)`. -/
def productGrassmannianIso :
    pullback X.obj.hom (SmoothProjectiveScheme.grassmannian k l n).obj.hom ≅
      Grassmannian.schemeOver.{u} l n ((SmoothProjectiveScheme.toScheme k).obj X) :=
  pullbackRightPullbackFstIso (terminal.from (Spec (.of k)))
      (terminal.from (Grassmannian.scheme.{u} l n)) X.obj.hom ≪≫
    pullback.congrHom (terminal.hom_ext _ _) rfl

/-- **The identification is over `X`.** -/
@[reassoc (attr := simp)]
theorem productGrassmannianIso_hom_fst :
    (productGrassmannianIso k X l n).hom ≫ pullback.fst _ _ = pullback.fst _ _ := by
  have h1 := pullbackRightPullbackFstIso_hom_fst (terminal.from (Spec (.of k)))
    (terminal.from (Grassmannian.scheme.{u} l n)) X.obj.hom
  have h2 : (pullback.congrHom (terminal.hom_ext (X.obj.hom ≫ terminal.from (Spec (.of k)))
      (terminal.from X.obj.left)) (rfl : terminal.from (Grassmannian.scheme.{u} l n) = _)).hom ≫
        pullback.fst (terminal.from X.obj.left) (terminal.from (Grassmannian.scheme.{u} l n)) =
      pullback.fst _ _ := by
    simp [pullback.congrHom]
  exact (Category.assoc _ _ _).trans ((congrArg (fun t =>
    (pullbackRightPullbackFstIso (terminal.from (Spec (.of k)))
      (terminal.from (Grassmannian.scheme.{u} l n)) X.obj.hom).hom ≫ t) h2).trans h1)

end Stacks.FlagTower

end
