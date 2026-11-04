module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# Charts factoring through an étale morphism, and the covering of an elementary square

Let `g : Z ⟶ W` be an étale morphism of algebraic spaces and `T` an étale chart of `W`.  A point
of the scheme of `T` whose image in `W` lies in the image of `g` is hit by a chart `T' ⟶ T` of
`W` admitting a morphism to the postcomposition of a chart of `Z`: take a surjective étale chart
`c` of `Z`, and for `T'` the representable fibre product of `T` with `c` over `W`.

For an elementary distinguished square `(U ⊆ W, f : V ⟶ W)` every point of `W` lies on `U` or in
the image of `f` (a point outside `U` lies on the reduced closed complement, over which `f` is an
isomorphism), so the pointwise criterion
`AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range` makes the sieve of the
charts factoring through `U` or through `V` covering.

## Main results

* `AlgebraicGeometry.Space.exists_hom_smallEtalePostcomp_of_mem_range`: the chart through an
  étale morphism hitting a given point.
* `AlgebraicGeometry.Space.mem_range_or_mem_range_of_isElementaryDistinguishedSquare`: the
  points of the ambient space of a square lie on the open subspace or in the image of the étale
  member.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A chart through an étale morphism hitting a point.**  For an étale `g : Z ⟶ W` of
algebraic spaces, an étale chart `T` of `W` and a point `x` of the scheme of `T` whose image in
`W` is in the image of `g`, some chart `T' ⟶ T` hitting `x` admits a morphism to the
postcomposition of a chart of `Z`. -/
theorem exists_hom_smallEtalePostcomp_of_mem_range {W Z : AlgebraicSpaces B S hS} (g : Z ⟶ W)
    (hg : IsEtale B S hS g.hom) (T : SmallEtale B S hS W.1)
    (x : (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS W.1).obj T))
    (hx : pointsMap B S hS _ T.1.hom ((pointsEquivScheme B S hS T.1.left).symm x) ∈
      Set.range (pointsMap B S hS Z.1 g.hom)) :
    ∃ (T' : SmallEtale B S hS W.1) (k : T' ⟶ T) (T'' : SmallEtale B S hS Z.1),
      Nonempty (T' ⟶ (smallEtalePostcomp B S hS g hg).obj T'') ∧
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS W.1).map k)) := by
  set c := sumAtlasChart B S hS Z
  have hc : IsSurjective B S hS c.1.hom := sumAtlasChart_isSurjective B S hS Z
  set P := (smallEtalePostcomp B S hS g hg).obj c
  have hrep : yoneda.relativelyRepresentable P.1.hom := P.property.rep
  set q : hrep.pullback T.1.hom ⟶ T.1.left := hrep.snd T.1.hom
  set p : hrep.pullback T.1.hom ⟶ P.1.left := hrep.fst' T.1.hom with hp
  have hw : yoneda.map p ≫ P.1.hom = yoneda.map q ≫ T.1.hom := by
    rw [hp, Functor.relativelyRepresentable.map_fst']
    exact hrep.w T.1.hom
  have hqEtale : Etale ((BigFppfOver.toScheme B S hS).map q) :=
    P.property.property T.1.hom (hrep.fst T.1.hom) (hrep.snd T.1.hom) (hrep.isPullback T.1.hom)
  let Vc : SmallEtale B S hS W.1 :=
    ⟨CostructuredArrow.mk (yoneda.map q ≫ T.1.hom),
      etale_comp_of_scheme B S hS q T.1.hom hqEtale T.property⟩
  refine ⟨Vc, ObjectProperty.homMk (CostructuredArrow.homMk q rfl), c,
    ⟨ObjectProperty.homMk (CostructuredArrow.homMk p hw)⟩, ?_⟩
  set t := (pointsEquivScheme B S hS T.1.left).symm x
  obtain ⟨z, hz⟩ := hx
  obtain ⟨a, ha⟩ := hc z
  have hat : pointsMap B S hS _ P.1.hom a = pointsMap B S hS _ T.1.hom t := by
    show pointsMap B S hS _ (c.1.hom ≫ g.hom) a = _
    rw [pointsMap_comp_apply, ha, hz]
  obtain ⟨w, -, hw2⟩ := exists_points_of_isPullback B S hS (hrep.isPullback T.1.hom) a t hat
  refine ⟨pointsToScheme B S hS _ w, ?_⟩
  have h1 := pointsToScheme_pointsMap_yoneda B S hS q w
  rw [hw2] at h1
  show (BigFppfOver.toScheme B S hS).map q (pointsToScheme B S hS _ w) = x
  rw [← h1]
  exact (pointsEquivScheme B S hS T.1.left).apply_symm_apply x

/-- **The points of an elementary distinguished square.**  Every point of the ambient space
lies on the open subspace or in the image of the étale member: a point outside the open
subspace lies on the reduced closed complement, over which the étale member is an
isomorphism. -/
theorem mem_range_or_mem_range_of_isElementaryDistinguishedSquare
    {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : IsAlgebraicSpace B S hS W) (U : Subfunctor W) (f : V ⟶ W)
    (h : IsElementaryDistinguishedSquare B S hS hW U f) (x : points B S hS W) :
    x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) ∨
      x ∈ Set.range (pointsMap B S hS V f) := by
  classical
  by_cases hx : x ∈ Set.range (pointsMap B S hS U.toFunctor U.ι)
  · exact Or.inl hx
  · right
    set D := reducedClosedSubspace B S hS W hW
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ h.isClosedComplement
    have hxD : x ∈ Set.range (pointsMap B S hS D.toFunctor D.ι) := by
      rwa [range_pointsMap_ι_reducedClosedSubspace]
    obtain ⟨z, rfl⟩ := hxD
    have : IsIso (D.fromPreimage f) := h.isIsoOverComplement
    obtain ⟨p, hp⟩ := pointsMap_surjective_of_isIso B S hS (D.fromPreimage f) z
    refine ⟨pointsMap B S hS (D.preimage f).toFunctor (D.preimage f).ι p, ?_⟩
    rw [← pointsMap_comp_apply, ← Subfunctor.fromPreimage_ι, pointsMap_comp_apply, hp]

end AlgebraicGeometry.Space

end
