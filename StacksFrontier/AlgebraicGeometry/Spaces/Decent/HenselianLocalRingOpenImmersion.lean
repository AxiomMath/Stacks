module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodCofiltered
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.RingTheory.Henselian.HenselizationCompletion

/-!
# The henselian local ring at a point of an open subspace, along an open immersion

For an open immersion `j : U ⟶ X` of decent algebraic spaces over `S` and a point `x` of `U`,
the henselian local ring of `U` at `x` and the henselian local ring of `X` at the image of `x`
are isomorphic. The two rings are not merely abstractly the same size: an elementary étale
neighborhood of `x` in `U`, composed with `j`, is again an elementary étale neighborhood, now of
the image point in `X`, with the *same* underlying pointed scheme, so the comparison needs no
argument beyond uniqueness of the henselization of that single common stalk.

## Main definitions

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.ofOpenImmersion` transports an
  elementary étale neighborhood of a point of `U` to an elementary étale neighborhood of its
  image in `X` along an open immersion `j : U ⟶ X`, keeping the same underlying pointed scheme.
* `AlgebraicGeometry.Space.henselianLocalRingRingEquivOfIsOpenImmersion`: the henselian local
  rings of `U` at `x` and of `X` at the image of `x` are isomorphic.

## Implementation notes

`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood` carries no reference to the ambient
presheaf beyond the chart morphism `toSpace` and the point condition `map_point`, so
transporting a neighborhood of `U` to a neighborhood of `X` along `j` keeps `scheme`, `point`,
`residueField_contained` and `mono_residueField` literally unchanged, resetting only
`toSpace := N.toSpace ≫ j` (still étale, since an open immersion is étale and étale morphisms
compose) and `map_point` (through naturality of `pointsMap` in composition).

Given one such neighborhood `N` of `x` in `U` and its transport `ΦN` in `X`, Stacks 0EMY
(`AlgebraicGeometry.Space.henselianLocalRing_isHenselization`) exhibits the henselian local ring
of `U` at `x` and the henselian local ring of `X` at the image of `x` as henselizations of the
*same* stalk ring, `N.scheme.left.1.presheaf.stalk N.point`, and
`StacksDraft.exists_ringEquiv_of_isHenselization` identifies any two henselizations of one local
ring. No comparison of the categories of elementary étale neighborhoods of `x` in `U` and of its
image in `X` is needed: a single common neighborhood suffices. Existence of `N` is Stacks 0BBP,
`AlgebraicGeometry.Space.exists_affine_elementaryEtaleNeighborhood'`; cofilteredness of each
category of neighborhoods, which Stacks 0EMY and the locality of the henselian local ring need,
is Stacks 0BGV and is supplied by `AlgebraicGeometry.Space.henselianLocalRing_isHenselization`
and `AlgebraicGeometry.Space.henselianLocalRing_isLocalRing` from decency, so it is not a
hypothesis here.

## References

* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The elementary étale neighborhood of the image of `x` in `X` obtained from an elementary étale
neighborhood `N` of `x` in `U` along an open immersion `j : U ⟶ X`: its underlying pointed scheme
is that of `N`, and its chart morphism is the composite of the chart morphism of `N` with `j`. -/
def ElementaryEtaleNeighborhood.ofOpenImmersion
    (hU : IsAlgebraicSpace B S hS U) (hX : IsAlgebraicSpace B S hS X)
    {x : points B S hS U} {j : U ⟶ X} (hj : IsOpenImmersion B S hS j)
    (N : ElementaryEtaleNeighborhood B S hS U hU x) :
    ElementaryEtaleNeighborhood B S hS X hX (pointsMap B S hS U j x) where
  scheme := N.scheme
  point := N.point
  residueField_contained := N.residueField_contained
  toSpace := N.toSpace ≫ j
  etale_toSpace := isEtale_comp B S hS N.etale_toSpace
    (isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS hj))
  map_point := by
    rw [pointsMap_comp]
    exact congrArg (pointsMap B S hS U j) N.map_point
  mono_residueField := by
    have : Mono (yoneda.map
        (residueFieldMap B S hS N.scheme N.point N.residueField_contained) ≫ N.toSpace) :=
      N.mono_residueField
    have : Mono j := mono_of_isOpenImmersion B S hS j hj
    rw [← Category.assoc]
    infer_instance

/-- The scheme of `ElementaryEtaleNeighborhood.ofOpenImmersion` applied to `N` is the scheme
of `N`. -/
@[simp]
theorem ElementaryEtaleNeighborhood.scheme_ofOpenImmersion
    (hU : IsAlgebraicSpace B S hS U) (hX : IsAlgebraicSpace B S hS X)
    {x : points B S hS U} {j : U ⟶ X} (hj : IsOpenImmersion B S hS j)
    (N : ElementaryEtaleNeighborhood B S hS U hU x) :
    (ElementaryEtaleNeighborhood.ofOpenImmersion B S hS hU hX hj N).scheme = N.scheme := rfl

/-- The point of `ElementaryEtaleNeighborhood.ofOpenImmersion` applied to `N` is the point
of `N`. -/
@[simp]
theorem ElementaryEtaleNeighborhood.point_ofOpenImmersion
    (hU : IsAlgebraicSpace B S hS U) (hX : IsAlgebraicSpace B S hS X)
    {x : points B S hS U} {j : U ⟶ X} (hj : IsOpenImmersion B S hS j)
    (N : ElementaryEtaleNeighborhood B S hS U hU x) :
    (ElementaryEtaleNeighborhood.ofOpenImmersion B S hS hU hX hj N).point = N.point := rfl

/-- **The henselian local ring is compatible with open immersions.** The henselian local rings
of `U` at a point `x` and of `X` at the image of `x` along an open immersion `j : U ⟶ X` are
isomorphic. -/
noncomputable def henselianLocalRingRingEquivOfIsOpenImmersion
    (hX : IsAlgebraicSpace B S hS X) (hU : IsAlgebraicSpace B S hS U)
    (hXdec : IsDecentSpace B S hS X) (hUdec : IsDecentSpace B S hS U)
    {j : U ⟶ X} (hj : IsOpenImmersion B S hS j) (x : points B S hS U) :
    (↥(henselianLocalRing B S hS U hU x hUdec) : Type (u + 1)) ≃+*
      (↥(henselianLocalRing B S hS X hX (pointsMap B S hS U j x) hXdec) : Type (u + 1)) := by
  let N := (exists_affine_elementaryEtaleNeighborhood' B S hS hU hUdec x).choose
  let ΦN := ElementaryEtaleNeighborhood.ofOpenImmersion B S hS hU hX hj N
  letI hIsLocalU : IsLocalRing (↥(henselianLocalRing B S hS U hU x hUdec) : Type (u + 1)) :=
    henselianLocalRing_isLocalRing B S hS U hU x hUdec
  letI hIsLocalX : IsLocalRing
      (↥(henselianLocalRing B S hS X hX (pointsMap B S hS U j x) hXdec) : Type (u + 1)) :=
    henselianLocalRing_isLocalRing B S hS X hX _ hXdec
  letI hAlgU : Algebra (N.scheme.left.1.presheaf.stalk N.point)
      (↥(henselianLocalRing B S hS U hU x hUdec) : Type (u + 1)) :=
    stalkAlgebra B S hS U hU x hUdec N
  letI hAlgX : Algebra (N.scheme.left.1.presheaf.stalk N.point)
      (↥(henselianLocalRing B S hS X hX (pointsMap B S hS U j x) hXdec) : Type (u + 1)) :=
    stalkAlgebra B S hS X hX _ hXdec ΦN
  letI hHenselU : IsLocalRing.IsHenselization (N.scheme.left.1.presheaf.stalk N.point)
      (IsLocalRing.ResidueField (N.scheme.left.1.presheaf.stalk N.point))
      (↥(henselianLocalRing B S hS U hU x hUdec) : Type (u + 1)) :=
    henselianLocalRing_isHenselization B S hS U hU x hUdec N
  letI hHenselX : IsLocalRing.IsHenselization (N.scheme.left.1.presheaf.stalk N.point)
      (IsLocalRing.ResidueField (N.scheme.left.1.presheaf.stalk N.point))
      (↥(henselianLocalRing B S hS X hX (pointsMap B S hS U j x) hXdec) : Type (u + 1)) :=
    henselianLocalRing_isHenselization B S hS X hX _ hXdec ΦN
  exact (StacksDraft.exists_ringEquiv_of_isHenselization
    (R := N.scheme.left.1.presheaf.stalk N.point)
    (H := (↥(henselianLocalRing B S hS U hU x hUdec) : Type (u + 1)))
    (H' :=
      (↥(henselianLocalRing B S hS X hX (pointsMap B S hS U j x) hXdec) : Type (u + 1)))).choose

end AlgebraicGeometry.Space

end
