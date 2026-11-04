module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsQuotientOfAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology

/-!
# The points of an algebraic stack with a surjective atlas by an algebraic space

Let `𝒳` be an algebraic stack over `S`, let `U` be an algebraic space over `S` and let
`f : U ⟶ 𝒳` be a surjective 1-morphism out of the algebraic stack `U` defines. Let `R` be a
2-fibre product of `f` with itself, playing the role of `U ×_𝒳 U`. Then the image of
`|R| ⟶ |U| × |U|` is an equivalence relation on `|U|` — namely the kernel of `|f|` — and `|𝒳|`
is the quotient of `|U|` by it.

## Main definitions

* `AlgebraicGeometry.Stack.spacePointsEquiv`: the points of an algebraic space are the points
  of the algebraic stack it defines.
* `AlgebraicGeometry.Stack.pointsMapToSpace`: the map on points of a 1-morphism into the
  algebraic stack of an algebraic space, valued in the points of that space.

## Main results

* `AlgebraicGeometry.Stack.range_prod_pointsMapToSpace_eq`: the image of `|R| ⟶ |U| × |U|` is
  the graph of the kernel of `|f|`.
* `AlgebraicGeometry.Stack.equivalence_mem_range_prod_pointsMapToSpace`: that image is an
  equivalence relation.
* `AlgebraicGeometry.Stack.spacePointsQuotientEquiv`: `|U|` modulo that relation is `|𝒳|`.

## Implementation notes

The points of `U` are identified with the points of its category of elements by
`AlgebraicGeometry.Stack.spacePointMap_id_bijective`, so the two legs `|R| ⟶ |U|` are the maps
on points of the two projections read through that bijection. The relation is presented as
`Setoid.ker` of the canonical map `|U| ⟶ |𝒳|` of Stacks 04XL. The quotient is a quotient of sets
of points, not the quotient stack `[U/R]`.

## References

* [Stacks Project, Tag 04XK](https://stacks.math.columbia.edu/tag/04XK)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The points of an algebraic space over `S` are the points of the algebraic stack it defines:
the canonical map of the tautological chart is bijective. -/
noncomputable def spacePointsEquiv (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Space.points B S hS F ≃
      points B S hS (fibredCategory B S hS F).val (fibredCategory B S hS F).property :=
  Equiv.ofBijective _ (spacePointMap_id_bijective B S hS F)

/-- The map on points of a 1-morphism of algebraic stacks whose target is the algebraic stack
of an algebraic space `F`, read as a map to the points of `F` itself. -/
noncomputable def pointsMapToSpace {𝒬 : AlgebraicStacks.{u, w} B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (q : 𝒬 ⟶ algebraicSpaceStack.{u, w} B S hS F hF) :
    AlgebraicStacks.points B S hS 𝒬 → Space.points B S hS F :=
  (spacePointsEquiv B S hS F).symm ∘ AlgebraicStacks.pointsMap B S hS q

/-- The canonical map of Stacks 04XL out of an algebraic space is the map on points of the
chart, read through `AlgebraicGeometry.Stack.spacePointsEquiv`. -/
theorem spacePointMap_eq_pointsMap_comp_spacePointsEquiv
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (p : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳) :
    spacePointMap B S hS F 𝒳.val p.hom.hom =
      AlgebraicStacks.pointsMap B S hS p ∘ spacePointsEquiv B S hS F :=
  spacePointMap_comp B S hS F (fibredCategory B S hS F) 𝒳.val
    (BasedFunctor.id (fibredCategory B S hS F).val) p.hom.hom

/-- **The image of the relation on points.** For a 2-fibre product `R` of a chart
`f : U ⟶ 𝒳` by an algebraic space with itself, the image of `|R| ⟶ |U| × |U|` is exactly the
set of pairs of points of `U` with the same image in `|𝒳|`. -/
@[stacks 04XK "image of the relation on points"]
theorem range_prod_pointsMapToSpace_eq
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {p : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳}
    (P : Bicategory.TwoCommSq p p) (hP : Bicategory.IsTwoFibreProduct P) :
    Set.range (fun r : AlgebraicStacks.points B S hS P.pt =>
        (pointsMapToSpace B S hS hF P.fst r, pointsMapToSpace B S hS hF P.snd r)) =
      {q : Space.points B S hS F × Space.points B S hS F |
        spacePointMap B S hS F 𝒳.val p.hom.hom q.1 =
          spacePointMap B S hS F 𝒳.val p.hom.hom q.2} := by
  have hkey := range_pointsMap_prod_eq B S hS p P hP
  have hcomp := spacePointMap_eq_pointsMap_comp_spacePointsEquiv B S hS hF p
  ext ⟨x, y⟩
  have hmem : ((spacePointsEquiv B S hS F x, spacePointsEquiv B S hS F y) ∈
      Set.range (fun r : AlgebraicStacks.points B S hS P.pt =>
        (AlgebraicStacks.pointsMap B S hS P.fst r,
          AlgebraicStacks.pointsMap B S hS P.snd r))) ↔
      AlgebraicStacks.pointsMap B S hS p (spacePointsEquiv B S hS F x) =
        AlgebraicStacks.pointsMap B S hS p (spacePointsEquiv B S hS F y) := by
    rw [hkey]
    exact Iff.rfl
  simp only [Set.mem_ofPred_eq, hcomp, Function.comp_apply]
  rw [← hmem]
  simp only [pointsMapToSpace, Function.comp_apply, Set.mem_range, Prod.mk.injEq,
    Equiv.symm_apply_eq]

/-- **The relation on points is an equivalence relation.** The image of
`|R| ⟶ |U| × |U|` is the kernel of `|f|`. -/
@[stacks 04XK "equivalence relation on points"]
theorem equivalence_mem_range_prod_pointsMapToSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {p : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳}
    (P : Bicategory.TwoCommSq p p) (hP : Bicategory.IsTwoFibreProduct P) :
    Equivalence (fun x y : Space.points B S hS F =>
      (x, y) ∈ Set.range (fun r : AlgebraicStacks.points B S hS P.pt =>
        (pointsMapToSpace B S hS hF P.fst r, pointsMapToSpace B S hS hF P.snd r))) := by
  rw [range_prod_pointsMapToSpace_eq B S hS hF P hP]
  exact (Setoid.ker (spacePointMap B S hS F 𝒳.val p.hom.hom)).iseqv

/-- **The points of the stack as a quotient.** For a surjective chart
`f : U ⟶ 𝒳` by an algebraic space, `|𝒳|` is the quotient of `|U|` by the kernel of `|f|`,
which is the image of `|R| ⟶ |U| × |U|` by
`AlgebraicGeometry.Stack.range_prod_pointsMapToSpace_eq`. -/
@[stacks 04XK "the points of the stack as a quotient"]
noncomputable def spacePointsQuotientEquiv
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (p : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳) (hsurj : IsSurjective B S hS p) :
    Quotient (Setoid.ker (spacePointMap B S hS F 𝒳.val p.hom.hom)) ≃
      AlgebraicStacks.points B S hS 𝒳 :=
  Setoid.quotientKerEquivOfSurjective _ (by
    rw [spacePointMap_eq_pointsMap_comp_spacePointsEquiv B S hS hF p]
    exact hsurj.comp (spacePointsEquiv B S hS F).surjective)

/-- `AlgebraicGeometry.Stack.spacePointsQuotientEquiv` sends the class of a point of `U` to its
image in `|𝒳|`. -/
theorem spacePointsQuotientEquiv_mk
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (p : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳) (hsurj : IsSurjective B S hS p)
    (x : Space.points B S hS F) :
    spacePointsQuotientEquiv B S hS hF p hsurj (Quotient.mk _ x) =
      spacePointMap B S hS F 𝒳.val p.hom.hom x :=
  rfl

end AlgebraicGeometry.Stack

end
