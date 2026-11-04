module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.SubgroupoidDivisionDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SitePullbackContainment
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.DescentSizeBound
import all StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient

/-!
# The quotient groupoid of a division lives in the big fppf site

Let `(U, R, s, t, c)` be a groupoid scheme over `S` and let `D` be a division of it by a finite
locally free subgroupoid in the sense of **Stacks 04S4**, with quotient `Ū = U/P` and descended
groupoid `(Ū, R̄, s̄, t̄, c̄)`.  A big fppf site over `S` which contains the object scheme `U` and
the arrow scheme `R` contains `Ū`, `R̄` and the scheme of composable pairs of the descended
groupoid as well.

The reason is uniform: both `U ⟶ Ū` and `R ⟶ R̄` are surjective and flat, and the size cutoff of
a big fppf site is a strong prelimit cardinal, so the target of a surjective flat morphism whose
source the site contains is contained too
(`AlgebraicGeometry.BigFppfSite.contains_of_flat_surjective`).  For `U ⟶ Ū` this is the
`projection_finiteLocallyFree` and `projection_surjective` fields of
`AlgebraicGeometry.GroupoidScheme.Division`.  For `R ⟶ R̄` it is the cartesian square
exhibiting `(U, R)` as the restriction of `(Ū, R̄)`: the `descend_fullyFaithful` field makes the
square of `AlgebraicGeometry.Bootstrap04S6.isPullback_of_fullyFaithful_groupoid` cartesian, and
`AlgebraicGeometry.Bootstrap04S6.property_arrows_of_fullyFaithful_groupoid` then carries
surjectivity and flatness from the map on objects to the map on arrows.  The scheme of composable
pairs is then a fibre product of two copies of `R̄`, and a big fppf site contains the fibre
products of the schemes it contains by
`AlgebraicGeometry.BigFppfSite.contains_pullback_left`.

These are exactly the three containment hypotheses `hU`, `hR` and `hP` of
`Stacks.Groupoids.GroupoidScheme.realization`, so the descended groupoid of a division can be
realized as a groupoid in algebraic spaces whenever the original one can.

## Main results

* `AlgebraicGeometry.GroupoidScheme.Division.isPullback_descend_arrows`: the division exhibits
  `(U, R)` as the restriction of `(Ū, R̄)` — the source–target square of the descent morphism is
  cartesian.
* `AlgebraicGeometry.GroupoidScheme.Division.surjective_descend_mapArrows` and
  `…flat_descend_mapArrows`: the map `R ⟶ R̄` is surjective and flat.
* `AlgebraicGeometry.GroupoidScheme.Division.contains_quotient`,
  `…contains_descended_objects`, `…contains_descended_arrows` and
  `…contains_descended_composablePairs`: the four containments.

## References

* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 0231](https://stacks.math.columbia.edu/tag/0231)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Groupoids.GroupoidScheme

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {G H : Stacks.Groupoids.GroupoidScheme S}
  {i : Stacks.Groupoids.GroupoidScheme.Hom H G} {hobj : H.objects = G.objects}

/-- **A division exhibits the divided groupoid as the restriction of the descended one.** The
square formed by the map on arrows of the descent morphism and the two source–target maps is
cartesian, because the descent morphism is fully faithful on generalized points. -/
theorem Division.isPullback_descend_arrows (D : Division G H i hobj) :
    IsPullback (prod.lift G.target G.source) D.descend.mapArrows
      (prod.map D.descend.mapObjects D.descend.mapObjects)
      (prod.lift D.descended.target D.descended.source) :=
  Bootstrap04S6.isPullback_of_fullyFaithful_groupoid D.descend D.descend_fullyFaithful

/-- The map on arrows of the descent morphism of a division is surjective: it inherits
surjectivity of the quotient morphism through the cartesian square of
`AlgebraicGeometry.GroupoidScheme.Division.isPullback_descend_arrows`. -/
theorem Division.surjective_descend_mapArrows (D : Division G H i hobj) :
    Surjective D.descend.mapArrows.left := by
  let : MorphismProperty.IsStableUnderComposition (@Surjective.{u}) :=
    ⟨fun _ _ hf hg => by
      let := hf
      let := hg
      infer_instance⟩
  exact Bootstrap04S6.property_arrows_of_fullyFaithful_groupoid (@Surjective) D.descend
    D.descend_fullyFaithful D.surjective_descend_mapObjects

/-- The map on arrows of the descent morphism of a division is flat: it inherits flatness of the
quotient morphism, which is finite locally free, through the same cartesian square. -/
theorem Division.flat_descend_mapArrows (D : Division G H i hobj) :
    Flat D.descend.mapArrows.left :=
  Bootstrap04S6.property_arrows_of_fullyFaithful_groupoid (@Flat) D.descend D.descend_fullyFaithful
    D.flat_descend_mapObjects

/-- **A big fppf site containing the object scheme of a groupoid contains the quotient of a
division of it.** The quotient morphism is finite locally free and surjective, hence flat and
surjective. -/
theorem Division.contains_quotient (D : Division G H i hobj) (B : BigFppfSite.{u})
    (hU : B.Contains G.objects.left) : B.Contains D.quotient.left := by
  let : Flat D.projection.left :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      D.projection.left).mp D.projection_finiteLocallyFree).2.1
  let : Surjective D.projection.left := D.projection_surjective
  exact B.contains_of_flat_surjective D.projection.left hU

/-- The site contains the object scheme of the descended groupoid, which is the quotient. -/
theorem Division.contains_descended_objects (D : Division G H i hobj) (B : BigFppfSite.{u})
    (hU : B.Contains G.objects.left) : B.Contains D.descended.objects.left := by
  rw [D.descended_objects]
  exact D.contains_quotient B hU

/-- **A big fppf site containing the arrow scheme of a groupoid contains the arrow scheme of the
descended groupoid of a division of it.** The map on arrows is flat and surjective. -/
theorem Division.contains_descended_arrows (D : Division G H i hobj) (B : BigFppfSite.{u})
    (hR : B.Contains G.arrows.left) : B.Contains D.descended.arrows.left := by
  let := D.flat_descend_mapArrows
  let := D.surjective_descend_mapArrows
  exact B.contains_of_flat_surjective D.descend.mapArrows.left hR

/-- The site contains the scheme of composable pairs of the descended groupoid, a fibre product
of two copies of its arrow scheme. -/
theorem Division.contains_descended_composablePairs (D : Division G H i hobj)
    (B : BigFppfSite.{u}) (hR : B.Contains G.arrows.left) :
    B.Contains (pullback D.descended.source D.descended.target).left :=
  B.contains_pullback_left D.descended.source D.descended.target
    (D.contains_descended_arrows B hR) (D.contains_descended_arrows B hR)

end AlgebraicGeometry.GroupoidScheme

end
