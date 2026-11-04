module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitInjectivity
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreserving

/-!
# Limit preservation of Artin's contraction functor

In the situation of Stacks 0GH8, let `F` be the contraction functor of Stacks 0GHA. For a
cofiltered limit `V = lim V_i` of affine locally Noetherian schemes over `S`, the map
`colim F(V_i) ⟶ F(V)` is injective
(`AlgebraicGeometry.Artin.ContractionSituation.exists_mapTriple_eq_of_isLimit`). Hence `F` is limit
preserving as soon as this map is also surjective (Stacks 0GI5).

## Main results

In the namespace `AlgebraicGeometry.Artin.ContractionSituation`:

* `limitPreserving_contractionFunctor_of_exists_stage`: `F` is limit preserving as soon as every
  element of `F(lim V_i)` comes from some `F(V_i)`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The contraction functor is limit preserving once every element over a limit comes from a
stage**: if for every cofiltered limit `κ` of affine objects every element of `F(κ.pt)` is the
image of an element of some `F(D.obj i)`, then the contraction functor of `c` is limit
preserving. -/
theorem limitPreserving_contractionFunctor_of_exists_stage (c : ContractionSituation B S hS)
    (hsurj : ∀ (I : Type u) [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ LocallyNoetherianOver B S hS) (κ : Cone D),
      IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ) →
      (∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i))) →
      IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt) →
      ∀ ξ : Triple c κ.pt.obj, ∃ (i : I) (y : Triple c (D.obj i).obj),
        mapTriple c (κ.π.app i).hom y = ξ) :
    LimitPreserving.{u, u + 1, u, u, u + 1, u} (LocallyNoetherianOver.toScheme B S hS)
      (contractionFunctor c) := by
  intro I _ _ D κ hκ hD hpt
  exact nonempty_isColimit_mapCocone_of_exists_of_eventually_eq (contractionFunctor c) D κ
    (hsurj I D κ hκ hD hpt) (exists_mapTriple_eq_of_isLimit c hκ hD hpt)

end AlgebraicGeometry.Artin.ContractionSituation

end
