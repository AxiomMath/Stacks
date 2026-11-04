module

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.InfiniteProductQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The point space of the algebraic space of the infinite product example

Let `K` be a field, `S = Spec K`, `U = Spec (∏_{n ∈ ℕ} K)` and let `X = U/R` be the algebraic
space of
`StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.InfiniteProductQuotient`. Stacks
02Z8 observes that the map `|U| → |X|` is continuous and surjective, that the coordinate
points `u_n` of `|U|` all map to one point `x₀` of `|X|`, and that — the `u_n` being dense in
`|U|` — the closure of `x₀` is all of `|X|`, so that `|X|` is irreducible with generic point
`x₀`, even though `x₀` is the image of a section `S ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.InfiniteProduct.basePoint`: the point of the point space of `S`.

## Main results

* `AlgebraicGeometry.Space.InfiniteProduct.surjective_pointsMap_quotientMap`: the map
  `|U| → |X|` is surjective, and
  `AlgebraicGeometry.Space.InfiniteProduct.continuous_pointsMap_quotientMap`: it is
  continuous.
* `AlgebraicGeometry.Space.InfiniteProduct.pointsMap_quotientMap_coordinatePoint`: the point
  of `|U|` of the `n`-th coordinate maps to the point of `x₀`.
* `AlgebraicGeometry.Space.InfiniteProduct.dense_range_pointsMap_coordinatePoint`: the image
  of the section `S ⟶ X` is dense in `|X|`, that is `|X|` is irreducible with generic point
  `x₀`.

## Implementation notes

The point space of a represented presheaf on the site is identified with the representing
scheme by `AlgebraicGeometry.Space.schemePointsHomeomorph`, which is Stacks 03BX, clause (1),
and the map on points of a morphism of the site is the underlying map of schemes conjugated
by those homeomorphisms, which is
`AlgebraicGeometry.Space.pointsMap_yoneda_eq_conj`. Density is therefore transported from
`AlgebraicGeometry.Space.InfiniteProduct.dense_coordinatePoints`, proved for the scheme `U`,
and no separate computation of the points of `X` is needed: the image of a dense set under a
continuous surjection is dense, and it is contained in the image of the section.

Surjectivity of `|U| → |X|` comes from surjectivity of the quotient map after every
representable base change, which is Stacks 02WW, through Stacks 03MD in the form
`AlgebraicGeometry.Space.isSurjective_of_presheafSurjective`.

## References

* [Stacks Project, Tag 02Z8](https://stacks.math.columbia.edu/tag/02Z8)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.InfiniteProduct

attribute [local instance] AlgebraicGeometry.Space.pointTopology

variable (K : Type u) [Field K] (B : BigFppfSite.{u}) (hS : B.Contains (base K))
  (hU : B.Contains (space K)) (hR : B.Contains (relation K))

/-- The underlying morphism of schemes of the charted `n`-th coordinate morphism is the `n`-th
coordinate morphism. -/
theorem toScheme_map_chartCoordinate (n : ℕ) :
    (BigFppfOver.toScheme B (base K) hS).map (chartCoordinate K B hS hU n) =
      coordinate K n :=
  congrArg Over.Hom.left (post_chartCoordinate K B hS hU n)

/-- The point of the point space of `S`. -/
noncomputable def basePoint : points B (base K) hS (yoneda.obj (baseChart K B hS)) :=
  (schemePointsHomeomorph B (base K) hS (baseChart K B hS)).symm (default : base K)

/-- The point of `|S|` of `AlgebraicGeometry.Space.InfiniteProduct.basePoint` is the point of
the scheme `S`. -/
theorem schemePointsHomeomorph_basePoint :
    schemePointsHomeomorph B (base K) hS (baseChart K B hS) (basePoint K B hS) =
      (default : base K) :=
  (schemePointsHomeomorph B (base K) hS (baseChart K B hS)).apply_symm_apply _

/-- The point of `|U|` of the `n`-th coordinate is the image of the point of `|S|` under the
`n`-th coordinate morphism. -/
theorem pointsMap_chartCoordinate_basePoint (n : ℕ) :
    pointsMap B (base K) hS (yoneda.obj (baseChart K B hS))
        (yoneda.map (chartCoordinate K B hS hU n)) (basePoint K B hS) =
      (schemePointsHomeomorph B (base K) hS (spaceChart K B hS hU)).symm
        ((coordinate K n).base (default : base K)) := by
  rw [pointsMap_yoneda_eq_conj]
  simp only [Function.comp_apply, schemePointsHomeomorph_basePoint,
    toScheme_map_chartCoordinate]
  rfl

section Quotient

variable [HasSheafify (BigFppfOver.topology B (base K) hS) (Type u)]

/-- **Stacks 02Z8.** The map `|U| → |X|` is surjective. -/
@[stacks 02Z8 "the map |U| → |X| is surjective"]
theorem surjective_pointsMap_quotientMap :
    Function.Surjective (pointsMap B (base K) hS (yoneda.obj (spaceChart K B hS hU))
      (Space.quotientMap B (base K) hS (chartSource K B hS hU hR)
        (chartTarget K B hS hU hR))) :=
  isSurjective_of_presheafSurjective B (base K) hS _ (quotientMap_surjective K B hS hU hR)

/-- **Stacks 02Z8.** The map `|U| → |X|` is continuous. -/
@[stacks 02Z8 "the map |U| → |X| is continuous"]
theorem continuous_pointsMap_quotientMap :
    Continuous (pointsMap B (base K) hS (yoneda.obj (spaceChart K B hS hU))
      (Space.quotientMap B (base K) hS (chartSource K B hS hU hR)
        (chartTarget K B hS hU hR))) :=
  continuous_pointsMap B (base K) hS _

/-- **Stacks 02Z8.** The point of `|U|` of the `n`-th coordinate maps to the point `x₀` of
`|X|`, for every `n`: all the coordinate points of `|U|` are identified in `|X|`. -/
@[stacks 02Z8 "the coordinate points of |U| all map to x₀"]
theorem pointsMap_quotientMap_coordinatePoint (n : ℕ) :
    pointsMap B (base K) hS (yoneda.obj (spaceChart K B hS hU))
        (Space.quotientMap B (base K) hS (chartSource K B hS hU hR)
          (chartTarget K B hS hU hR))
        ((schemePointsHomeomorph B (base K) hS (spaceChart K B hS hU)).symm
          ((coordinate K n).base (default : base K))) =
      pointsMap B (base K) hS (yoneda.obj (baseChart K B hS))
        (coordinatePoint K B hS hU hR) (basePoint K B hS) := by
  rw [← pointsMap_chartCoordinate_basePoint K B hS hU n,
    ← Function.comp_apply (f := pointsMap B (base K) hS (yoneda.obj (spaceChart K B hS hU)) _),
    ← pointsMap_comp, quotientMap_comp_chartCoordinate K B hS hU hR n]

/-- **Stacks 02Z8.** The image of the section `S ⟶ X` is dense in `|X|`: the point `x₀` has
closure all of `|X|`, so `|X|` is irreducible with generic point `x₀`.

The coordinate points are dense in `|U|` by
`AlgebraicGeometry.Space.InfiniteProduct.dense_coordinatePoints`, the map `|U| → |X|` is
continuous and surjective, and it carries every coordinate point to `x₀`. -/
@[stacks 02Z8 "the closure of x₀ is all of |X|"]
theorem dense_range_pointsMap_coordinatePoint :
    Dense (Set.range (pointsMap B (base K) hS (yoneda.obj (baseChart K B hS))
      (coordinatePoint K B hS hU hR))) := by
  set e := schemePointsHomeomorph B (base K) hS (spaceChart K B hS hU) with he
  set D : Set (points B (base K) hS (yoneda.obj (spaceChart K B hS hU))) :=
    e.symm '' Set.range (fun n : ℕ ↦ (coordinate K n).base (default : base K)) with hD
  have hDdense : Dense D :=
    e.symm.surjective.denseRange.dense_image e.symm.continuous (dense_coordinatePoints K)
  have himage : pointsMap B (base K) hS (yoneda.obj (spaceChart K B hS hU))
      (Space.quotientMap B (base K) hS (chartSource K B hS hU hR)
        (chartTarget K B hS hU hR)) '' D ⊆
      Set.range (pointsMap B (base K) hS (yoneda.obj (baseChart K B hS))
        (coordinatePoint K B hS hU hR)) := by
    rintro _ ⟨w, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
    exact ⟨basePoint K B hS, (pointsMap_quotientMap_coordinatePoint K B hS hU hR n).symm⟩
  refine Dense.mono himage ?_
  exact (surjective_pointsMap_quotientMap K B hS hU hR).denseRange.dense_image
    (continuous_pointsMap_quotientMap K B hS hU hR) hDdense

end Quotient

end AlgebraicGeometry.Space.InfiniteProduct

end
