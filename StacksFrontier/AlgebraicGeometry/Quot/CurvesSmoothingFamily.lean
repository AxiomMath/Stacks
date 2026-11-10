module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UpperSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Size.PowerSeries
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingProperCurve

/-!
# The smoothing of a curve over `k⟦t⟧` as a family of curves

Stacks 0E7Y produces, for a proper scheme `X` over a field `k` of dimension at most one which is a
local complete intersection smooth away from finitely many points, a flat projective morphism
`g : Y ⟶ Spec k⟦t⟧` with smooth generic fibre and special fibre `X`. In the proof of Stacks 0E86
this `g` is a family of curves over `Spec k⟦t⟧`, whose classifying morphism links the point of `X`
of the stack of curves with a point of the smooth locus.

The total space `Y` has dimension two, so the relative-dimension condition of a family of curves
(Stacks 0D4Z) is not the bound on the dimension of the source used by
`AlgebraicGeometry.curveFamilyOfSchemeMorphism`; it is the bound on the fibres. The fibre over the
closed point is `X`, of dimension at most one, and by the upper semicontinuity of the dimension
of the fibres of a proper morphism (Stacks 0D4I) the bound spreads to every point of
`Spec k⟦t⟧`, each of which specializes to the closed point.

## Main definitions

* `AlgebraicGeometry.curveFamilyOfFiberDimensionLE`: a flat, proper morphism of finite
  presentation of the site whose fibres have local dimension at most one, as a family of curves.

## Main results

* `AlgebraicGeometry.Scheme.Hom.fiberDimension_le_of_specializes`: for a universally closed
  morphism locally of finite type, a bound on the dimension of the fibre over a point holds over
  each of its generizations.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_le_one_of_specialFibre`: a morphism to
  `Spec k⟦t⟧` as above whose special fibre is a scheme of dimension at most one has all its
  fibres of local dimension at most one.

## References

* [Stacks Project, Tag 0D4I](https://stacks.math.columbia.edu/tag/0D4I)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
* [Stacks Project, Tag 0E86](https://stacks.math.columbia.edu/tag/0E86)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The fibre dimension bound spreads to generizations.** For a universally closed morphism
locally of finite type, the set of points of the target over which the fibre has dimension at
most `n` is open (Stacks 0D4I), so it contains every generization of each of its points. -/
theorem Scheme.Hom.fiberDimension_le_of_specializes {Y T : Scheme.{u}} (g : Y ⟶ T)
    [UniversallyClosed g] [LocallyOfFiniteType g] (n : ℕ) {t t₀ : T} (h : t ⤳ t₀)
    (h₀ : g.fiberDimension t₀ ≤ ((n : ℕ∞) : WithBot ℕ∞)) :
    g.fiberDimension t ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
  have hlt : g.fiberDimension t₀ < (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) :=
    h₀.trans_lt (WithBot.coe_lt_coe.mpr (by exact_mod_cast Nat.lt_succ_self n))
  have hev := upperSemicontinuous_fiberDimension g t₀ _ hlt
  have ht : g.fiberDimension t < (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) :=
    (hev.filter_mono (specializes_iff_nhds.mp h)).self_of_nhds
  generalize g.fiberDimension t = d at ht ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe c =>
    rw [WithBot.coe_lt_coe] at ht
    rw [WithBot.coe_le_coe]
    exact (ENat.lt_add_one_iff (ENat.natCast_ne_top n)).mp (by exact_mod_cast ht)

/-- **The fibres of a smoothing over `k⟦t⟧` have dimension at most one.** Let `g : Y ⟶ Spec k⟦t⟧`
be universally closed and locally of finite type, with special fibre (the base change along the
constant coefficient `Spec k ⟶ Spec k⟦t⟧`) isomorphic over `Spec k` to a scheme `X` of dimension
at most one. Then every fibre of `g` has dimension at most one: the fibre over the closed point is
`X`, and every point of `Spec k⟦t⟧` specializes to the closed point. -/
theorem fiberDimension_le_one_of_specialFibre {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (hdim : topologicalKrullDim X ≤ 1)
    (g : Y ⟶ Spec (.of (PowerSeries k))) [UniversallyClosed g] [LocallyOfFiniteType g]
    (e : X ≅ pullback g (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))))
    (he : e.hom ≫ pullback.snd g
      (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = f)
    (t : Spec (.of (PowerSeries k))) : g.fiberDimension t ≤ ((1 : ℕ∞) : WithBot ℕ∞) := by
  have h1 := Scheme.Hom.fiberDimension_eq_of_over_iso (Over.isoMk e he : Over.mk f ≅ Over.mk
    (pullback.snd g (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k))))))
  let pt : Spec (.of k) := IsLocalRing.closedPoint k
  have hf : f.fiberDimension pt ≤ ((1 : ℕ∞) : WithBot ℕ∞) :=
    ((Topology.IsInducing.topologicalKrullDim_le (f.fiberι pt).isEmbedding.isInducing).trans
      hdim).trans (by simp)
  have h2 := congrFun (Scheme.Hom.fiberDimension_pullback_snd g
    (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k))))) pt
  have hc : g.fiberDimension
      (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k))) pt) ≤
        ((1 : ℕ∞) : WithBot ℕ∞) := by
    have h1pt : f.fiberDimension pt = (pullback.snd g
        (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k))))).fiberDimension pt :=
      congrFun h1 pt
    rwa [h1pt, h2] at hf
  have : IsLocalHom (PowerSeries.constantCoeff (R := k)) :=
    ⟨fun _ ha => PowerSeries.isUnit_iff_constantCoeff.mpr ha⟩
  have hsp : t ⤳ Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k))) pt := by
    have hcpt : Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k))) pt =
        IsLocalRing.closedPoint (PowerSeries k) :=
      IsLocalRing.comap_closedPoint (PowerSeries.constantCoeff (R := k))
    rw [hcpt]
    exact IsLocalRing.specializes_closedPoint _
  exact Scheme.Hom.fiberDimension_le_of_specializes g 1 hsp (by simpa using hc)

/-- **The fibres of a smoothing over `k⟦t⟧` have local dimension at most one** at every point
of the total space (`AlgebraicGeometry.fiberDimension_le_one_of_specialFibre`). -/
theorem topologicalKrullDimAt_fiber_le_one_of_specialFibre {k : Type u} [Field k]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (hdim : topologicalKrullDim X ≤ 1)
    (g : Y ⟶ Spec (.of (PowerSeries k))) [UniversallyClosed g] [LocallyOfFiniteType g]
    (e : X ≅ pullback g (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))))
    (he : e.hom ≫ pullback.snd g
      (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) = f)
    (y : Y) : topologicalKrullDimAt (g.fiber (g y)) (g.asFiber y) ≤ 1 := by
  simpa using (Scheme.Hom.topologicalKrullDimAt_fiber_le_fiberDimension g rfl).trans
    (fiberDimension_le_one_of_specialFibre f hdim g e he (g y))

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **A flat proper morphism with fibres of dimension at most one as a family of curves.** A
morphism of the big fppf site of the integers which is flat, proper and locally of finite
presentation, and whose fibre through every point of the source has local dimension at most
one, is a family of curves (Stacks 0D4Z): the relative-dimension condition of a family of curves
is exactly that bound, read in every étale chart (Stacks 04NC, 04NL). The space-level
quasi-compactness, separatedness and quasi-separatedness are those of the morphism of schemes. -/
def curveFamilyOfFiberDimensionLE {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hfib : ∀ x, topologicalKrullDimAt
      (((BigFppfOver.toScheme B integerBase hZ).map g).fiber
        (((BigFppfOver.toScheme B integerBase hZ).map g) x))
      (((BigFppfOver.toScheme B integerBase hZ).map g).asFiber x) ≤ 1) :
    CurveFamily B hZ where
  base := U
  total := schemeSpace T
  toBase := schemeSpaceMap g
  flat := (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
    Flat.isEtaleLocalOnSourceAndTarget g).2 hflat
  proper := by
    refine ⟨(Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance,
      ⟨?_, Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ g inferInstance⟩,
      ?_⟩
    · exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
        LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget g).2 inferInstance
    · have hrep : yoneda.relativelyRepresentable (yoneda.map g) :=
        Functor.relativelyRepresentable.map _ _
      exact (Space.presheaf_universallyClosed_iff B integerBase hZ
          (isAlgebraicSpace_yoneda B integerBase hZ T)
          (isAlgebraicSpace_yoneda B integerBase hZ U) hrep).1
        (Space.presheaf_yoneda_map_of_inverseImage B integerBase hZ
          (P := @UniversallyClosed.{u}) inferInstance g inferInstance)
  finitePresentation :=
    ⟨(Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
        LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget g).2 hlfp,
      Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ g inferInstance,
      (Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance⟩
  relativeDimensionLE x := by
    set φ := (BigFppfOver.toScheme B integerBase hZ).map g
    set y := Space.pointsToScheme B integerBase hZ T x
    have hle := hfib y
    have h0 := topologicalKrullDimAt_nonneg (φ.asFiber y)
    generalize hd : topologicalKrullDimAt (φ.fiber (φ y)) (φ.asFiber y) = d at hle h0
    induction d using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe c =>
      have hc1 : c ≤ 1 := by exact_mod_cast hle
      have hct : c ≠ ⊤ := ne_top_of_le_ne_top ENat.one_ne_top hc1
      obtain ⟨e, rfl⟩ := ENat.ne_top_iff_exists.mp hct
      refine ⟨e, by exact_mod_cast hc1, ?_⟩
      exact (Space.holdsOnEveryEtaleChartAtPoint_yoneda_map_iff B integerBase hZ
        (@HasFiberDimensionAt.{u} (e : ℕ∞))
        (fiberDimensionAt_isEtaleLocalOnSourceAndTarget (e : ℕ∞)) g x).2
        ((hasFiberDimensionAt_ofSchemeHom_iff φ y (e : ℕ∞)).2 hd)

end AlgebraicGeometry

end
