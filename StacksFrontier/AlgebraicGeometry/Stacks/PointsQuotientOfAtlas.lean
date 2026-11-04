module

public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# The points of an algebraic stack as a quotient of the points of an atlas

Let `p : 𝒰 ⟶ 𝒳` be a 1-morphism of algebraic stacks over `S` and let `R` be a 2-fibre product
of `p` with itself, playing the role of `𝒰 ×_𝒳 𝒰`. Then:

* the image of `|R| ⟶ |𝒰| × |𝒰|` is exactly the set of pairs of points of `𝒰` with the same
  image in `|𝒳|` — that is, the graph of `Setoid.ker |p|`, so in particular an equivalence
  relation; and
* if `p` is surjective then `|𝒳|` is the quotient of `|𝒰|` by that equivalence relation.

## Main results

* `AlgebraicGeometry.Stack.pointsMap_fst_comp_eq_pointsMap_snd_comp`: the two legs of a
  2-commutative square over a cospan with equal legs agree after composing with `p` on points.
* `AlgebraicGeometry.Stack.range_pointsMap_prod_eq`: the image of `|R| ⟶ |𝒰| × |𝒰|` is the
  graph of `Setoid.ker |p|`.
* `AlgebraicGeometry.Stack.pointsQuotientEquiv`: `|𝒰| / Setoid.ker |p| ≃ |𝒳|`.
* `AlgebraicGeometry.Stack.pointsQuotientEquivOfRelativelySurjective`: the same, taking
  surjectivity in the relative-property form of Stacks 03YK.

## References

* [Stacks Project, Tag 04XJ](https://stacks.math.columbia.edu/tag/04XJ)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
-/

@[expose] public section

open CategoryTheory

universe u w t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The two legs of a 2-commutative square over the cospan `p, p` induce maps on points which
agree after composing with the map on points of `p`. -/
theorem pointsMap_fst_comp_eq_pointsMap_snd_comp
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (p : 𝒰 ⟶ 𝒳)
    (P : Bicategory.TwoCommSq p p)
    (r : points B S hS P.pt.val.val (Classical.choose P.pt.property)) :
    pointsMap B S hS 𝒰.val.val (Classical.choose 𝒰.property)
        (Classical.choose 𝒳.property) p.hom.hom
        (pointsMap B S hS P.pt.val.val (Classical.choose P.pt.property)
          (Classical.choose 𝒰.property) P.fst.hom.hom r) =
      pointsMap B S hS 𝒰.val.val (Classical.choose 𝒰.property)
        (Classical.choose 𝒳.property) p.hom.hom
        (pointsMap B S hS P.pt.val.val (Classical.choose P.pt.property)
          (Classical.choose 𝒰.property) P.snd.hom.hom r) := by
  rw [pointsMap_comp, pointsMap_comp]
  exact congrFun (pointsMap_eq_of_basedNatTrans B S hS P.pt.val.val
    (Classical.choose P.pt.property) (Classical.choose 𝒳.property) P.iso.hom.hom.hom) r

/-- For a 2-fibre product `R` of a 1-morphism `p : 𝒰 ⟶ 𝒳` of algebraic stacks with itself, the
image of `|R| ⟶ |𝒰| × |𝒰|` is exactly the set of pairs of points of `𝒰` with the same image in
`|𝒳|`; that is, the graph of `Setoid.ker` of the map on points of `p`. In particular that image
is an equivalence relation. -/
theorem range_pointsMap_prod_eq
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (p : 𝒰 ⟶ 𝒳)
    (P : Bicategory.TwoCommSq p p) (hP : Bicategory.IsTwoFibreProduct P) :
    Set.range (fun r : points B S hS P.pt.val.val (Classical.choose P.pt.property) =>
        (pointsMap B S hS P.pt.val.val (Classical.choose P.pt.property)
            (Classical.choose 𝒰.property) P.fst.hom.hom r,
          pointsMap B S hS P.pt.val.val (Classical.choose P.pt.property)
            (Classical.choose 𝒰.property) P.snd.hom.hom r)) =
      {q : points B S hS 𝒰.val.val (Classical.choose 𝒰.property) ×
          points B S hS 𝒰.val.val (Classical.choose 𝒰.property) |
        pointsMap B S hS 𝒰.val.val (Classical.choose 𝒰.property)
            (Classical.choose 𝒳.property) p.hom.hom q.1 =
          pointsMap B S hS 𝒰.val.val (Classical.choose 𝒰.property)
            (Classical.choose 𝒳.property) p.hom.hom q.2} := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨r, rfl⟩
    exact pointsMap_fst_comp_eq_pointsMap_snd_comp B S hS p P r
  · rintro ⟨u₁, u₂⟩ h
    obtain ⟨r, hr₁, hr₂⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS P hP u₁ u₂ h
    exact ⟨r, Prod.ext hr₁ hr₂⟩

/-- The points of `𝒳` are the quotient of the points of `𝒰` by the equivalence relation of
`AlgebraicGeometry.Stack.range_pointsMap_prod_eq`, for a surjective 1-morphism
`p : 𝒰 ⟶ 𝒳` of algebraic stacks. -/
noncomputable def pointsQuotientEquiv
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (p : 𝒰 ⟶ 𝒳)
    (hsurj : IsSurjective B S hS p) :
    Quotient (Setoid.ker (pointsMap B S hS 𝒰.val.val (Classical.choose 𝒰.property)
        (Classical.choose 𝒳.property) p.hom.hom)) ≃
      points B S hS 𝒳.val.val (Classical.choose 𝒳.property) :=
  Setoid.quotientKerEquivOfSurjective _ hsurj

/-- `AlgebraicGeometry.Stack.pointsQuotientEquiv` with surjectivity given in the
relative-property form of Stacks 03YK. -/
noncomputable def pointsQuotientEquivOfRelativelySurjective
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (p : 𝒰 ⟶ 𝒳)
    (hp : IsRepresentableByAlgebraicSpaces B S hS p.hom.hom)
    (hsurj : HasRelativeProperty.{u, u, u + 1, t} B S hS
      (Space.surjectiveMorphismProperty B S hS) p.hom hp) :
    Quotient (Setoid.ker (pointsMap B S hS 𝒰.val.val (Classical.choose 𝒰.property)
        (Classical.choose 𝒳.property) p.hom.hom)) ≃
      points B S hS 𝒳.val.val (Classical.choose 𝒳.property) :=
  pointsQuotientEquiv B S hS p
    ((pointsMap_surjective_iff_isRelativelySurjective.{u, w, t} B S hS p hp).mpr hsurj)

end AlgebraicGeometry.Stack

end
