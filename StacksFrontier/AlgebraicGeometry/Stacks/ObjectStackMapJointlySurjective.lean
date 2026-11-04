module

public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectMorphismFactor
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack

/-!
# Families of objects over a surjective object whose 1-morphisms jointly cover the stack

Let `x₀` be an object of an algebraic stack `𝒳` whose 1-morphism `x₀ : (Sch/U₀) → 𝒳`
(Stacks 004B) is surjective, and let `{φ_i : y_i → x₀}` be arrows of `𝒳` whose images
`U_i → U₀` are jointly surjective on underlying schemes. Then the 1-morphisms
`y_i : (Sch/U_i) → 𝒳` are jointly surjective on points (Stacks 04XE): `y_i` is 2-isomorphic to the
composite `U_i → U₀ → 𝒳`. This is the joint surjectivity with which a covering of an atlas object
enters the locality statements Stacks 075Y, 07AN and 07AQ.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.iUnion_range_pointsMap_objectStackMap`.

## References

* [Stacks Project, Tag 04XE](https://stacks.math.columbia.edu/tag/04XE)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Objects over a surjective object, lying over a jointly surjective family of schemes, give
1-morphisms jointly surjective on points.** If `x₀ : (Sch/U₀) → 𝒳` is surjective and the
images `U_i → U₀` of arrows `φ_i : y_i → x₀` are jointly surjective, then every point of `𝒳` is
in the image of some `y_i : (Sch/U_i) → 𝒳`, which is 2-isomorphic to `U_i → U₀ → 𝒳`
(`AlgebraicGeometry.Stack.objectMorphismFactorIso`). -/
theorem iUnion_range_pointsMap_objectStackMap (x₀ : 𝒳.val.val.obj)
    (hx₀ : IsSurjective B S hS (objectStackMap B S hS 𝒳 x₀)) {ι : Type*}
    (y : ι → 𝒳.val.val.obj) (φ : ∀ i, y i ⟶ x₀)
    (hcov : ∀ t, ∃ i s, (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (φ i)) s = t) :
    Set.univ = ⋃ i, Set.range (pointsMap B S hS (objectStackMap B S hS 𝒳 (y i))) := by
  let := pointTopology B S hS (schemeFibredCategory B S hS (𝒳.val.val.p.obj x₀))
  let := fun i => pointTopology B S hS (schemeFibredCategory B S hS (𝒳.val.val.p.obj (y i)))
  refine (Set.eq_univ_of_forall fun ξ => ?_).symm
  obtain ⟨t', rfl⟩ := hx₀ ξ
  obtain ⟨i, s, hs⟩ := hcov (pointsHomeomorphScheme B S hS (𝒳.val.val.p.obj x₀) t')
  refine Set.mem_iUnion.2 ⟨i, (pointsHomeomorphScheme B S hS (𝒳.val.val.p.obj (y i))).symm s, ?_⟩
  have h₂ : pointsMap B S hS (objectStackMap B S hS 𝒳 (y i)) =
      pointsMap B S hS (schemeStackMap.{u, w} B S hS (𝒳.val.val.p.map (φ i)) ≫
        objectStackMap B S hS 𝒳 x₀) :=
    pointsMap_eq_of_hom₂ B S hS
      (Bicategory.InducedBicategory.mkHom₂ (objectMorphismFactorIso B S hS 𝒳.val (φ i)).hom)
  rw [h₂, pointsMap_comp]
  refine congrArg (pointsMap B S hS (objectStackMap B S hS 𝒳 x₀)) ?_
  apply (pointsHomeomorphScheme B S hS (𝒳.val.val.p.obj x₀)).injective
  rwa [pointsHomeomorphScheme_pointsMap, siteMap_schemeStackMap, Homeomorph.apply_symm_apply]

end AlgebraicGeometry.Stack.AlgebraicStacks
