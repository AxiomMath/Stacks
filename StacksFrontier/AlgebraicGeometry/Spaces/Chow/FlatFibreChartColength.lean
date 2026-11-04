module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkLength
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackAssociatedCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicityAtPoint

/-!
# The colength of the fibre of a morphism, read on an étale chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `x̄` be a geometric
point of `X` with image `ȳ = f(x̄)` in `Y`, and let

`u ∈ U ⟶ V ∋ v`

be a commuting square of étale scheme charts over `f` carrying a lift of `x̄`, with `u` the
point of `U` under that lift and `v` its image in `V`.  This file proves

`length_{𝒪_{X, x̄}}(𝒪_{X, x̄} / 𝔪_{ȳ} 𝒪_{X, x̄}) = length_{𝒪_{U, u}}(𝒪_{U, u} / 𝔪_{v} 𝒪_{U, u})`,

the two readings of the colength of the extended maximal ideal: on the left over the étale
local ring at a geometric point, on the right over the Zariski stalk of a chart.  Nothing is
assumed of `f`, and no hypothesis is placed on the chart square beyond its commuting and
carrying the lift of `x̄`.

## Main results

* `AlgebraicGeometry.Space.length_quotient_map_maximalIdeal_etaleLocalRingMap_eq_chartLocalRing`:
  the identity, for a small étale neighbourhood of `x̄` and a chart of `Y` under it.
* `AlgebraicGeometry.Space.length_quotient_map_maximalIdeal_etaleLocalRingMap_eq_chartStalk`:
  the same for an étale scheme chart `U` of `X` and a point `u` of it over the image of `x̄`.
* `length_quotient_map_maximalIdeal_etaleLocalRingMap_eq_chartStalk_of_isAlgebraicSpace`: the
  same for an unbundled morphism of presheaves.
* `AlgebraicGeometry.Space.flatPullbackMult_eq_toNat_length_chartStalk`: the coefficient of the
  flat pullback of a prime cycle of Stacks 0EP8, as a colength on an étale chart.

## Implementation notes

`AlgebraicGeometry.Space.isLocalRing_etaleLocalRing` (Stacks 08AH) is a theorem and not an
instance in this development, so the maximal ideal of `𝒪_{Y, ȳ}` is named through a `letI` in
the statements, as `AlgebraicGeometry.Space.flatPullbackMult_eq_toNat_length` and
`AlgebraicGeometry.Space.map_maximalIdeal_chartLocalRingToEtaleLocalRing` do.

The square of local rings of Stacks 05VU is stated for a morphism of the category of algebraic
spaces, so the first statement is too; the second takes the two charts and the vertical
morphism as unbundled data, which is what makes it applicable at an arbitrary point of an
arbitrary chart.

## References

* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The colength of the extended maximal ideal is the same on the chart and at the geometric
point.**  In a commuting square of étale scheme charts over `f : X ⟶ Y` carrying a lift of a
geometric point `x̄` of `X`, the length of `𝒪_{U, u} / 𝔪_v 𝒪_{U, u}` over `𝒪_{U, u}` is the
length of `𝒪_{X, x̄} / 𝔪_{f(x̄)} 𝒪_{X, x̄}` over `𝒪_{X, x̄}`. -/
theorem length_quotient_map_maximalIdeal_etaleLocalRingMap_eq_chartLocalRing
    {Xs Ys : AlgebraicSpaces B S hS} (f : Xs ⟶ Ys)
    (xbar : GeometricPoint B S hS Xs.1) (N : SmallEtaleNeighborhood xbar)
    (Wc : SmallEtale B S hS Ys.1) (g : N.chart.obj.left ⟶ Wc.obj.left)
    (hcomm : N.chart.obj.hom ≫ f.hom = yoneda.map g ≫ Wc.obj.hom) :
    letI : IsLocalRing ↥(etaleLocalRing B S hS Ys.1 (geometricPointMap f.hom xbar)) :=
      isLocalRing_etaleLocalRing B S hS Ys.1 Ys.2 _
    Module.length ↥(chartLocalRing B S hS Xs.1 N)
        (↥(chartLocalRing B S hS Xs.1 N) ⧸
          Ideal.map (((BigFppfOver.toScheme B S hS).map g).stalkMap
              (chartPoint B S hS Xs.1 N)).hom
            (maximalIdeal ((chartScheme Wc).presheaf.stalk
              (((BigFppfOver.toScheme B S hS).map g).base
                (chartPoint B S hS Xs.1 N))))) =
      Module.length ↥(etaleLocalRing B S hS Xs.1 xbar)
        (↥(etaleLocalRing B S hS Xs.1 xbar) ⧸
          Ideal.map (etaleLocalRingMap Xs.2 f.hom xbar)
            (maximalIdeal ↥(etaleLocalRing B S hS Ys.1
              (geometricPointMap f.hom xbar)))) := by
  have : IsLocalRing ↥(etaleLocalRing B S hS Ys.1 (geometricPointMap f.hom xbar)) :=
    isLocalRing_etaleLocalRing B S hS Ys.1 Ys.2 _
  have : IsLocalRing ↥(etaleLocalRing B S hS Xs.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS Xs.1 Xs.2 xbar
  let : Algebra ↥(chartLocalRing B S hS Xs.1 N) ↥(etaleLocalRing B S hS Xs.1 xbar) :=
    (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N).toAlgebra
  have : Module.Flat ↥(chartLocalRing B S hS Xs.1 N) ↥(etaleLocalRing B S hS Xs.1 xbar) :=
    flat_chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N
  have : IsLocalHom (algebraMap ↥(chartLocalRing B S hS Xs.1 N)
      ↥(etaleLocalRing B S hS Xs.1 xbar)) :=
    isLocalHom_chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N
  have hid := (Ideal.map_map
      (((BigFppfOver.toScheme B S hS).map g).stalkMap (chartPoint B S hS Xs.1 N)).hom
      (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N)
      (I := maximalIdeal ((chartScheme Wc).presheaf.stalk
        (((BigFppfOver.toScheme B S hS).map g).base (chartPoint B S hS Xs.1 N))))).trans
    ((congrArg (fun φ => Ideal.map φ (maximalIdeal ((chartScheme Wc).presheaf.stalk
        (((BigFppfOver.toScheme B S hS).map g).base (chartPoint B S hS Xs.1 N)))))
      (etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing B S hS f xbar N Wc g hcomm)).trans
      (Ideal.map_map
        (chartLocalRingToEtaleLocalRing B S hS Ys.1 Ys.2 (targetNeighborhood B S hS N Wc g hcomm))
        (etaleLocalRingMap Xs.2 f.hom xbar)).symm)
  rw [length_baseChange_eq_of_map_maximalIdeal _ _
      (map_maximalIdeal_chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N) _,
    length_baseChange_quotient_eq (chartLocalRingToEtaleLocalRing B S hS Xs.1 Xs.2 N) _]
  exact congrArg (fun J : Ideal ↥(etaleLocalRing B S hS Xs.1 xbar) =>
      Module.length ↥(etaleLocalRing B S hS Xs.1 xbar)
        (↥(etaleLocalRing B S hS Xs.1 xbar) ⧸ J))
    (hid.trans (congrArg (Ideal.map (etaleLocalRingMap Xs.2 f.hom xbar))
      (map_maximalIdeal_chartLocalRingToEtaleLocalRing B S hS Ys.1 Ys.2
        (targetNeighborhood B S hS N Wc g hcomm))))

/-- **The colength of the extended maximal ideal at a point of an arbitrary étale chart.**  Let
`f : X ⟶ Y` be a morphism of algebraic spaces, let `U` and `V` be étale scheme charts of `X`
and of `Y` and `g : U ⟶ V` a morphism of schemes making the square over `f` commute, let `u` be
a point of `U` and `x̄` a geometric point of `X` with the same image in `|X|`, and write `v` for
the image of `u` in `V`.  Then

`length_{𝒪_{U, u}}(𝒪_{U, u} / 𝔪_v 𝒪_{U, u}) = length_{𝒪_{X, x̄}}(𝒪_{X, x̄} / 𝔪_{f(x̄)} 𝒪_{X, x̄})`.
-/
theorem length_quotient_map_maximalIdeal_etaleLocalRingMap_eq_chartStalk
    (X : AlgebraicSpaces B S hS) (Y : AlgebraicSpaces B S hS) (f : X ⟶ Y)
    (xbar : GeometricPoint B S hS X.1)
    (U : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (g : U.obj.left ⟶ V.obj.left)
    (hcomm : U.obj.hom ≫ f.hom = yoneda.map g ≫ V.obj.hom)
    (u : chartScheme U) (hu : chartSchemeToPoints B S hS X.1 U u = xbar.image) :
    letI : IsLocalRing ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar)) :=
      isLocalRing_etaleLocalRing B S hS Y.1 Y.2 _
    Module.length ((chartScheme U).presheaf.stalk u)
        ((chartScheme U).presheaf.stalk u ⧸
          Ideal.map (((BigFppfOver.toScheme B S hS).map g).stalkMap u).hom
            (maximalIdeal ((chartScheme V).presheaf.stalk
              (((BigFppfOver.toScheme B S hS).map g).base u)))) =
      Module.length ↥(etaleLocalRing B S hS X.1 xbar)
        (↥(etaleLocalRing B S hS X.1 xbar) ⧸
          Ideal.map (etaleLocalRingMap X.2 f.hom xbar)
            (maximalIdeal ↥(etaleLocalRing B S hS Y.1
              (geometricPointMap f.hom xbar)))) := by
  obtain ⟨N, rfl, rfl⟩ := exists_smallEtaleNeighborhood_chart_eq B S hS X xbar U u hu
  exact length_quotient_map_maximalIdeal_etaleLocalRingMap_eq_chartLocalRing B S hS f xbar N
    V g hcomm

/-- `AlgebraicGeometry.Space.length_quotient_map_maximalIdeal_etaleLocalRingMap_eq_chartStalk`
for a morphism of presheaves between two algebraic spaces, rather than for a morphism of the
category of algebraic spaces. -/
theorem length_quotient_map_maximalIdeal_etaleLocalRingMap_eq_chartStalk_of_isAlgebraicSpace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (xbar : GeometricPoint B S hS X)
    (U : SmallEtale B S hS X) (V : SmallEtale B S hS Y)
    (g : U.obj.left ⟶ V.obj.left)
    (hcomm : U.obj.hom ≫ f = yoneda.map g ≫ V.obj.hom)
    (u : chartScheme U) (hu : chartSchemeToPoints B S hS X U u = xbar.image) :
    letI : IsLocalRing ↥(etaleLocalRing B S hS Y (geometricPointMap f xbar)) :=
      isLocalRing_etaleLocalRing B S hS Y hY _
    Module.length ((chartScheme U).presheaf.stalk u)
        ((chartScheme U).presheaf.stalk u ⧸
          Ideal.map (((BigFppfOver.toScheme B S hS).map g).stalkMap u).hom
            (maximalIdeal ((chartScheme V).presheaf.stalk
              (((BigFppfOver.toScheme B S hS).map g).base u)))) =
      Module.length ↥(etaleLocalRing B S hS X xbar)
        (↥(etaleLocalRing B S hS X xbar) ⧸
          Ideal.map (etaleLocalRingMap hX f xbar)
            (maximalIdeal ↥(etaleLocalRing B S hS Y (geometricPointMap f xbar)))) :=
  length_quotient_map_maximalIdeal_etaleLocalRingMap_eq_chartStalk B S hS ⟨X, hX⟩ ⟨Y, hY⟩
    (ObjectProperty.homMk f) xbar U V g hcomm u hu

/-! ### The coefficient of a flat pullback of cycles as a colength on a chart -/

section FlatPullback

attribute [local instance] pointTopology

/-- **The coefficient of `W'` in `f^*[W]` is a colength on an étale chart.**  In the situation
of `AlgebraicGeometry.Space.flatPullbackMult_eq_toNat_length` — `W ⊆ Y` an integral closed
subspace, `V ⊆ f^{-1}(W)` an integral closed subspace of δ-dimension `dim_δ(W) + r` whose
generic point maps to the generic point of `W`, and `z̄` a geometric point of `f^{-1}(W)` over
the generic point of `V` — the coefficient of the image `W'` of `V` in `f^*[W]` is the colength

`length_{𝒪_{U, u}}(𝒪_{U, u} / 𝔪_{v} 𝒪_{U, u})`

of the extended maximal ideal along any commuting square of étale scheme charts `U ⟶ V_c` over
`f` with `u ∈ U` over the image of `z̄` in `|X|` and `v` the image of `u`. -/
theorem flatPullbackMult_eq_toNat_length_chartStalk (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (Vs : IntegralClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f).toFunctor)
    (hV : deltaDimension D sX (closedSubspaceComponentImage D sX hX (W.subspace.preimage f)
      (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W) Vs) =
        deltaDimension D sY W + (r : ℤ))
    (z : GeometricPoint D.site D.base D.base_mem (W.subspace.preimage f).toFunctor)
    (hz : z.image = Vs.ambientGenericPoint D.site D.base D.base_mem)
    (hgen : pointsMap D.site D.base D.base_mem X f
        (pointsMap D.site D.base D.base_mem _ (W.subspace.preimage f).ι
          (Vs.ambientGenericPoint D.site D.base D.base_mem)) =
      W.ambientGenericPoint D.site D.base D.base_mem)
    (U : SmallEtale D.site D.base D.base_mem X) (Vc : SmallEtale D.site D.base D.base_mem Y)
    (g : U.obj.left ⟶ Vc.obj.left)
    (hcomm : U.obj.hom ≫ f = yoneda.map g ≫ Vc.obj.hom)
    (u : chartScheme U)
    (hu : chartSchemeToPoints D.site D.base D.base_mem X U u =
      (geometricPointMap (W.subspace.preimage f).ι z).image) :
    flatPullbackMult D sX hX sY hY f hbase r hflat hr W
        (closedSubspaceComponentImage D sX hX (W.subspace.preimage f)
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W) Vs) =
      ((Module.length ((chartScheme U).presheaf.stalk u)
          ((chartScheme U).presheaf.stalk u ⧸
            Ideal.map (((BigFppfOver.toScheme D.site D.base D.base_mem).map g).stalkMap u).hom
              (maximalIdeal ((chartScheme Vc).presheaf.stalk
                (((BigFppfOver.toScheme D.site D.base D.base_mem).map g).base u))))).toNat :
        ℤ) := by
  refine Eq.trans (flatPullbackMult_eq_toNat_length D sX hX sY hY f hbase r hflat hr W Vs hV z hz
    hgen) ?_
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
    (length_quotient_map_maximalIdeal_etaleLocalRingMap_eq_chartStalk_of_isAlgebraicSpace
      D.site D.base D.base_mem hX.1 hY.1 f
      (geometricPointMap (W.subspace.preimage f).ι z) U Vc g hcomm u hu).symm

end FlatPullback

end AlgebraicGeometry.Space

end
