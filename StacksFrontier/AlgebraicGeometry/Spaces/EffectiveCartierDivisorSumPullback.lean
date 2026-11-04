module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# The inverse image of a sum of effective Cartier divisors

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B` and let `D₁, D₂ ⊆ X` be closed subspaces.  Following Stacks 0840 the inverse image of
the sum `D₁ + D₂` of Stacks 083U is the sum of the inverse images,

`f⁻¹(D₁ + D₂) = f⁻¹(D₁) + f⁻¹(D₂)`,

and consequently the pullback of `D₁ + D₂` is defined as soon as the pullbacks of `D₁` and `D₂`
are: those pullbacks are then effective Cartier divisors on `Y`, and so is their sum by
Stacks 083V.

## Main results

* `AlgebraicGeometry.Space.preimage_sumClosedSubspaces` is the second assertion of
  **Stacks 0840**, `f^*(D₁ + D₂) = f^*D₁ + f^*D₂`, for arbitrary closed subspaces.
* `AlgebraicGeometry.Space.isPullbackDefined_sumClosedSubspaces` is the first assertion of
  **Stacks 0840**: the pullback of `D₁ + D₂` is defined when those of `D₁` and `D₂` are.
* `AlgebraicGeometry.Space.chartKer_preimage`: on an étale scheme chart of the source lying over
  a chart of the target, the chart ideal sheaf of an inverse image is the inverse image of the
  chart ideal sheaf.
* `AlgebraicGeometry.Space.chartKer_sumClosedSubspaces`: on the chart carrying the sum, the
  chart ideal sheaf of `D₁ + D₂` is the product of those of `D₁` and `D₂`.
* `AlgebraicGeometry.Space.sumChartOver`: a surjective étale scheme chart of `Y` lying over the
  chart of `Y` carrying the sum and, along `f`, over the chart of `X` carrying the sum.

## Implementation notes

Neither assertion needs `D₁` and `D₂` to be effective Cartier divisors on `X`: the inverse image
commutes with the sum for arbitrary closed subspaces, and the definedness of the pullback of the
sum uses only that the two inverse images are effective Cartier divisors on `Y`, which is what
`AlgebraicGeometry.Space.IsPullbackDefined` asserts.  This is the same widening as in
Stacks 083U, where the sum itself is formed for arbitrary closed subspaces.

The whole argument is the computation of both sides on one surjective étale scheme chart of `Y`.
The sum of Stacks 083U is formed on the chart `AlgebraicGeometry.Space.sumAtlasChart`, and what
is known about it on a chart `A` is the formula
`AlgebraicGeometry.Space.definingIdealAt_sumClosedSubspaces_of_isAffine`, which needs `A` to lie
over that chart; the inverse image, on the other hand, is computed on a chart `A` of `Y` lying
over a chart of `X` by `AlgebraicGeometry.Space.schemeKer_snd_preimage` together with
`AlgebraicGeometry.Space.schemeKer_snd_comp`.  So the chart used is
`AlgebraicGeometry.Space.sumChartOver`, the base change to `Y` of the chart of `X` carrying the
sum taken over the chart of `Y` carrying the sum, which lies over both; it is surjective because
both of its factors are, and étale by part (1) of Stacks 03EC.

On that chart the identity is the multiplicativity of the inverse image of ideal sheaves of
schemes, `Stacks.IdealSheaf.comap_mul`: the chart ideal sheaf of `D₁ + D₂` on the chart of `X`
is the product of those of `D₁` and `D₂`, and taking inverse images along the chart morphism
turns that product into the product of the chart ideal sheaves of the two inverse images.
Passing between chart ideal sheaves and the defining ideals of Stacks 083B is
`AlgebraicGeometry.Space.ker_rep_snd_eq_ofIdealTop_definingIdealAt` on the affine charts, so the
two closed subspaces have the same defining ideal sheaf and hence agree.

## References

* [Stacks Project, Tag 0840](https://stacks.math.columbia.edu/tag/0840)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
* [Stacks Project, Tag 083V](https://stacks.math.columbia.edu/tag/083V)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 083B](https://stacks.math.columbia.edu/tag/083B)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The chart ideal sheaf of a sum -/

/-- **On the chart carrying the sum, the chart ideal sheaf of `D₁ + D₂` is the product of those
of `D₁` and `D₂`.** -/
theorem chartKer_sumClosedSubspaces (X : AlgebraicSpaces B S hS)
    (D₁ D₂ : ClosedSubspaces B S hS X.1) :
    chartKer B S hS X (sumClosedSubspaces B S hS X D₁ D₂) (atlasHom B S hS X) =
      chartKer B S hS X D₁ (atlasHom B S hS X) * chartKer B S hS X D₂ (atlasHom B S hS X) := by
  have hinv := isInvariantSubscheme_mul_chartKer B S hS X (atlasHom_surjective B S hS X) D₁ D₂
  set J := chartKer B S hS X D₁ (atlasHom B S hS X) *
    chartKer B S hS X D₂ (atlasHom B S hS X)
  set Zs := sumClosedSubspaces B S hS X D₁ D₂
  have hZ1 : Zs.1 = invariantSubspace B S hS (atlasHom B S hS X)
      (Subobject.mk J.subschemeι) := rfl
  have himm1 : AlgebraicGeometry.IsImmersion (Subobject.mk ((BigFppfOver.toScheme B S hS).map
      (Zs.2.2.rep.snd (atlasHom B S hS X)))).arrow := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    infer_instance
  have himm2 : AlgebraicGeometry.IsImmersion (Subobject.mk J.subschemeι).arrow := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    infer_instance
  have hpres : (Subobject.underlyingIso ((BigFppfOver.toScheme B S hS).map
        (Zs.2.2.rep.snd (atlasHom B S hS X)))).symm.hom ≫
      (Subobject.mk ((BigFppfOver.toScheme B S hS).map
        (Zs.2.2.rep.snd (atlasHom B S hS X)))).arrow =
      (BigFppfOver.toScheme B S hS).map (Zs.2.2.rep.snd (atlasHom B S hS X)) :=
    Subobject.underlyingIso_arrow _
  have hsp : subschemePoints B S hS (Subobject.mk ((BigFppfOver.toScheme B S hS).map
        (Zs.2.2.rep.snd (atlasHom B S hS X)))) =
      subschemePoints B S hS (Subobject.mk J.subschemeι) := by
    rw [subschemePoints_eq_range B S hS _ _ hpres,
      range_yoneda_snd_eq_preimage B S hS (atlasHom B S hS X) Zs.2.2.rep, hZ1,
      preimage_invariantSubspace B S hS (atlasHom_surjective B S hS X) _ hinv]
  refine Scheme.IdealSheafData.subobject_mk_subschemeι_inj.1 ?_
  rw [subobject_mk_chartKer B S hS X Zs (atlasHom B S hS X)]
  exact subschemePoints_injective B S hS himm1 himm2 hsp

/-! ### The chart ideal sheaf of an inverse image -/

variable {X Y : AlgebraicSpaces B S hS}

/-- **The chart ideal sheaf of an inverse image is the inverse image of the chart ideal
sheaf.** Let `f : Y ⟶ X` be a morphism of algebraic spaces, `Z ⊆ X` a closed subspace, `A` an
étale scheme chart of `Y` and `r : A ⟶ W` a morphism of the site to a chart `p : W ⟶ X` lying
over `f`.  Then the chart ideal sheaf of `f⁻¹(Z)` at `A` is the inverse image along `r` of the
chart ideal sheaf of `Z` at `W`. -/
theorem chartKer_preimage (f : Y ⟶ X) (Z : ClosedSubspaces B S hS X.1)
    (A : SmallEtale B S hS Y.1) {W : BigFppfOver B S hS} (p : yoneda.obj W ⟶ X.1)
    (r : A.1.left ⟶ W) (hr : yoneda.map r ≫ p = A.1.hom ≫ f.hom) :
    chartKer B S hS Y ⟨Z.1.preimage f.hom,
        isClosedSubspace_preimage B S hS f.hom Z.1 X.2 Y.2 Z.2⟩ A.1.hom =
      (chartKer B S hS X Z p).comap ((BigFppfOver.toScheme B S hS).map r) := by
  rw [chartKer_eq, chartKer_eq, schemeKer_snd_preimage B S hS f Z A, ← hr,
    schemeKer_snd_comp B S hS Z p r]

/-- **The defining ideal of a closed subspace is read off its chart ideal sheaf.** On an affine
étale chart, the defining ideal of Stacks 083B is the ideal of global functions killed by the
closed subscheme that the chart ideal sheaf cuts out. -/
theorem definingIdealAt_eq_ker_appTop_of_chartKer_eq (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) (A : SmallEtale B S hS X.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left)]
    (I : ((BigFppfOver.toScheme B S hS).obj A.1.left).IdealSheafData)
    (h : chartKer B S hS X Z A.1.hom = I) :
    definingIdealAt B S hS X Z (op A) = RingHom.ker (I.subschemeι.appTop).hom :=
  (@Scheme.IdealSheafData.ker_appTop_subschemeι_ofIdealTop
      ((BigFppfOver.toScheme B S hS).obj A.1.left) inferInstance
      (definingIdealAt B S hS X Z (op A))).symm.trans
    (congrArg (fun J => RingHom.ker (J.subschemeι.appTop).hom)
      ((ker_rep_snd_eq_ofIdealTop_definingIdealAt B S hS X Z A).symm.trans h))

/-! ### A chart of the source lying over both charts carrying the sums -/

/-- The base change to `Y` of the chart of `X` carrying the sum, formed over the chart of `Y`
carrying the sum: a scheme chart of `Y` which lies over the latter and, along `f`, over the
former. -/
noncomputable def sumChartOver (f : Y ⟶ X) : SmallEtale B S hS Y.1 :=
  ⟨CostructuredArrow.mk (yoneda.map ((sumAtlasChart B S hS X).2.rep.snd
        ((sumAtlasChart B S hS Y).1.hom ≫ f.hom)) ≫ (sumAtlasChart B S hS Y).1.hom),
    etale_comp_of_scheme B S hS _ (sumAtlasChart B S hS Y).1.hom
      ((sumAtlasChart B S hS X).2.property_snd _) (sumAtlasChart B S hS Y).2⟩

/-- The projection of `AlgebraicGeometry.Space.sumChartOver` to the chart of `Y` carrying the
sum. -/
noncomputable def sumChartOverToTarget (f : Y ⟶ X) :
    sumChartOver B S hS f ⟶ sumAtlasChart B S hS Y :=
  ObjectProperty.homMk (CostructuredArrow.homMk ((sumAtlasChart B S hS X).2.rep.snd
    ((sumAtlasChart B S hS Y).1.hom ≫ f.hom)) rfl)

/-- The projection of `AlgebraicGeometry.Space.sumChartOver` to the chart of `X` carrying the
sum. -/
noncomputable def sumChartOverToSource (f : Y ⟶ X) :
    (sumChartOver B S hS f).1.left ⟶ (sumAtlasChart B S hS X).1.left :=
  (sumAtlasChart B S hS X).2.rep.fst' ((sumAtlasChart B S hS Y).1.hom ≫ f.hom)

/-- The projection of `AlgebraicGeometry.Space.sumChartOver` to the chart of `X` lies over
`f`. -/
theorem sumChartOverToSource_w (f : Y ⟶ X) :
    yoneda.map (sumChartOverToSource B S hS f) ≫ atlasHom B S hS X =
      (sumChartOver B S hS f).1.hom ≫ f.hom := by
  show yoneda.map ((sumAtlasChart B S hS X).2.rep.fst'
      ((sumAtlasChart B S hS Y).1.hom ≫ f.hom)) ≫ (sumAtlasChart B S hS X).1.hom =
    (sumChartOver B S hS f).1.hom ≫ f.hom
  rw [(sumAtlasChart B S hS X).2.rep.map_fst' ((sumAtlasChart B S hS Y).1.hom ≫ f.hom),
    (sumAtlasChart B S hS X).2.rep.w ((sumAtlasChart B S hS Y).1.hom ≫ f.hom),
    ← Category.assoc]
  rfl

/-- The chart `AlgebraicGeometry.Space.sumChartOver` is surjective on points. -/
theorem sumChartOver_isSurjective (f : Y ⟶ X) :
    IsSurjective B S hS (sumChartOver B S hS f).1.hom :=
  isSurjective_comp B S hS
    (isSurjective_of_presheafSurjective B S hS _
      (presheaf_yoneda_map_of_inverseImage B S hS inferInstance _
        ((atlasHom_surjective B S hS X).property_snd
          ((sumAtlasChart B S hS Y).1.hom ≫ f.hom))))
    (sumAtlasChart_isSurjective B S hS Y)

/-! ### Stacks 0840 -/

/-- **Stacks 0840.** The inverse image of a sum of closed subspaces is the sum of the inverse
images: `f^*(D₁ + D₂) = f^*D₁ + f^*D₂` for the sum of Stacks 083U. -/
@[stacks 0840 "the inverse image commutes with the sum"]
theorem preimage_sumClosedSubspaces (f : Y ⟶ X) (D₁ D₂ : ClosedSubspaces B S hS X.1) :
    (⟨(sumClosedSubspaces B S hS X D₁ D₂).1.preimage f.hom,
        isClosedSubspace_preimage B S hS f.hom (sumClosedSubspaces B S hS X D₁ D₂).1 X.2 Y.2
          (sumClosedSubspaces B S hS X D₁ D₂).2⟩ : ClosedSubspaces B S hS Y.1) =
      sumClosedSubspaces B S hS Y
        ⟨D₁.1.preimage f.hom, isClosedSubspace_preimage B S hS f.hom D₁.1 X.2 Y.2 D₁.2⟩
        ⟨D₂.1.preimage f.hom, isClosedSubspace_preimage B S hS f.hom D₂.1 X.2 Y.2 D₂.2⟩ := by
  refine definingIdealSheaf_injective B S hS Y ?_
  refine structureSubmodule_ext_of_forall_isAffine_hom B S hS Y (sumChartOver B S hS f)
    (sumChartOver_isSurjective B S hS f) _ _ fun A hA m => ?_
  have hAff : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
  have hw : yoneda.map ((SmallEtale.toOver B S hS Y.1).map m) ≫
      (sumChartOver B S hS f).1.hom = A.1.hom := CostructuredArrow.w m.1
  have hr : yoneda.map ((SmallEtale.toOver B S hS Y.1).map m ≫
      sumChartOverToSource B S hS f) ≫ atlasHom B S hS X =
      A.1.hom ≫ f.hom := by
    rw [Functor.map_comp, Category.assoc, sumChartOverToSource_w B S hS f, ← Category.assoc, hw]
  have hprod : chartKer B S hS Y ⟨(sumClosedSubspaces B S hS X D₁ D₂).1.preimage f.hom,
        isClosedSubspace_preimage B S hS f.hom (sumClosedSubspaces B S hS X D₁ D₂).1 X.2 Y.2
          (sumClosedSubspaces B S hS X D₁ D₂).2⟩ A.1.hom =
      chartKer B S hS Y ⟨D₁.1.preimage f.hom,
          isClosedSubspace_preimage B S hS f.hom D₁.1 X.2 Y.2 D₁.2⟩ A.1.hom *
        chartKer B S hS Y ⟨D₂.1.preimage f.hom,
          isClosedSubspace_preimage B S hS f.hom D₂.1 X.2 Y.2 D₂.2⟩ A.1.hom := by
    rw [chartKer_preimage B S hS f _ A (atlasHom B S hS X) _ hr,
      chartKer_preimage B S hS f D₁ A (atlasHom B S hS X) _ hr,
      chartKer_preimage B S hS f D₂ A (atlasHom B S hS X) _ hr,
      chartKer_sumClosedSubspaces B S hS X D₁ D₂, Stacks.IdealSheaf.comap_mul]
  have e : ∀ D : ClosedSubspaces B S hS X.1, chartKer B S hS Y ⟨D.1.preimage f.hom,
        isClosedSubspace_preimage B S hS f.hom D.1 X.2 Y.2 D.2⟩ A.1.hom =
      Scheme.IdealSheafData.ofIdealTop (definingIdealAt B S hS Y
        ⟨D.1.preimage f.hom, isClosedSubspace_preimage B S hS f.hom D.1 X.2 Y.2 D.2⟩ (op A)) :=
    fun D => ker_rep_snd_eq_ofIdealTop_definingIdealAt B S hS Y _ A
  refine Eq.trans ?_ (definingIdealAt_sumClosedSubspaces_of_isAffine B S hS Y _ _ A
    (m ≫ sumChartOverToTarget B S hS f)).symm
  exact (definingIdealAt_eq_ker_appTop_of_chartKer_eq B S hS Y _ A _
    (hprod.trans (by rw [e D₁, e D₂]; exact Scheme.IdealSheafData.ofIdealTop_mul _ _))).trans
    (Scheme.IdealSheafData.ker_appTop_subschemeι_ofIdealTop _)

/-- **Stacks 0840.** If the pullbacks of two closed subspaces along `f : Y ⟶ X` are defined,
then so is the pullback of their sum. -/
@[stacks 0840 "the pullback of the sum is defined"]
theorem isPullbackDefined_sumClosedSubspaces (f : Y ⟶ X) (D₁ D₂ : ClosedSubspaces B S hS X.1)
    (h₁ : IsPullbackDefined B S hS f D₁) (h₂ : IsPullbackDefined B S hS f D₂) :
    IsPullbackDefined B S hS f (sumClosedSubspaces B S hS X D₁ D₂) := by
  rw [show IsPullbackDefined B S hS f (sumClosedSubspaces B S hS X D₁ D₂) =
      IsEffectiveCartierDivisor B S hS Y
        ⟨(sumClosedSubspaces B S hS X D₁ D₂).1.preimage f.hom,
          isClosedSubspace_preimage B S hS f.hom (sumClosedSubspaces B S hS X D₁ D₂).1 X.2 Y.2
            (sumClosedSubspaces B S hS X D₁ D₂).2⟩ from rfl,
    preimage_sumClosedSubspaces B S hS f D₁ D₂]
  exact isEffectiveCartierDivisor_sumClosedSubspaces B S hS Y _ _ h₁ h₂

end AlgebraicGeometry.Space

end
