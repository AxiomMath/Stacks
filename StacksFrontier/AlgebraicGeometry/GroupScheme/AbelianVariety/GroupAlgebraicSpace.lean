module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ConstantAbelianScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackTrivialActionClass

/-!
# A commutative group scheme as a commutative group algebraic space

Let `S` be a scheme of a big fppf site and let `G` be a group scheme over `S` lying in the site.
By Stacks 043I (`AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite`), `G` is a
group algebraic space over `S`. When `G` is commutative, so is this group algebraic space, in
the sense of `AlgebraicGeometry.Space.GroupAlgebraicSpace.IsCommutative`: its group of points
over every object over `S` is commutative. An abelian variety over a field `k` is commutative
(Stacks 03RP), so the group algebraic space over `Spec k` attached to it is commutative.

## Main definitions

* `AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupScheme`: the group algebraic space over
  `S` attached to a group scheme over `S` lying in the site (Stacks 043I).

## Main results

* `AlgebraicGeometry.Space.GroupAlgebraicSpace.isCommutative_ofGroupScheme`: it is commutative
  when the group scheme is.
* `AlgebraicGeometry.Space.GroupAlgebraicSpace.isCommutative_ofGroupScheme_of_isAbelianVariety`:
  the group algebraic space of an abelian variety is commutative.

## References

* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space.GroupAlgebraicSpace

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}

/-- **The group algebraic space over `S` of a group scheme over `S`** lying in the big fppf
site (Stacks 043I): `AlgebraicGeometry.Space.GroupAlgebraicSpace.ofGroupSchemeInSite` over the
terminal algebraic space, at the group scheme read as an object of the site. -/
abbrev ofGroupScheme (G : Over S) [GrpObj G] (hG : 𝒞.Contains G.left) :
    GroupAlgebraicSpace 𝒞 S hS (baseS 𝒞 S hS) (isAlgebraicSpace_baseS 𝒞 S hS) :=
  ofGroupSchemeInSite 𝒞 S hS _ _ (groupSchemeObj 𝒞 S hS G hG) (inferInstanceAs (GrpObj G))

/-- **The group algebraic space of a commutative group scheme is commutative**: a point over an
object `Z` over `S` is a morphism from `Z` to the presheaf of points of `G`, and these are
multiplied pointwise in the commutative groups of points of `G`. -/
instance isCommutative_ofGroupScheme (G : Over S) [GrpObj G] [IsCommMonObj G]
    (hG : 𝒞.Contains G.left) : (ofGroupScheme (hS := hS) G hG).IsCommutative where
  mul_comm Z x y := by
    let P := pointsOnSite 𝒞 S hS (groupSchemeObj 𝒞 S hS G hG) (inferInstanceAs (GrpObj G)) ⋙
      forget GrpCat
    let e : (Z ⟶ (ofGroupScheme (hS := hS) G hG).obj.X) ≃* (Z.left ⟶ P) :=
      overProdFstHomMulEquiv _ _ Z
    apply e.injective
    rw [map_mul, map_mul, Hom.mul_def, Hom.mul_def]
    ext T z
    change (MonObj.mul (X := P)).app T ((CartesianMonoidalCategory.lift (e x) (e y)).app T z) =
      (MonObj.mul (X := P)).app T ((CartesianMonoidalCategory.lift (e y) (e x)).app T z)
    rw [lift_app_apply, lift_app_apply]
    exact mul_comm (G := (toSchemeOver 𝒞 S hS).obj T.unop ⟶ G) _ _

/-- **The group algebraic space of an abelian variety over `k` is commutative**, since an
abelian variety is a commutative group scheme (Stacks 03RP,
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`). -/
instance isCommutative_ofGroupScheme_of_isAbelianVariety {k : Type u} [Field k]
    {hk : 𝒞.Contains (Spec (.of k))} (A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety k A]
    (hA : 𝒞.Contains A.left) : (ofGroupScheme (hS := hk) A hA).IsCommutative :=
  have : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A
  isCommutative_ofGroupScheme A hA

end AlgebraicGeometry.Space.GroupAlgebraicSpace

end
