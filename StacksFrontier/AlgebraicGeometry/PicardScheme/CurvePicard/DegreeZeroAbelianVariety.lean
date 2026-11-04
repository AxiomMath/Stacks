module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.RationalPoints
public import
  StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyEquivalentDefinitions
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityJacobian
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement

/-!
# `Pic⁰` of a curve as an abelian variety

Let `X` be a smooth projective geometrically irreducible curve over a field `k` with a rational
point, whose Picard functor is representable. `Stacks.PicardFunctor.picardDegreeZeroSubgroup`
exhibits `Pic⁰_{X/k}` as an open subgroup scheme of the Picard group scheme; its underlying
scheme over `k` is the degree-zero component `Pic⁰_{X/k}`
(`Stacks.PicardFunctor.picardDegreeZeroSubgroup_carrier_X_hom`). Once that component is known to
be a smooth proper variety over `k` (clause (1) of [Stacks, Tag 0BA0], carried here as the
hypotheses `hproper`, `hsmooth` and `hint`), the group scheme `Pic⁰_{X/k}` is connected,
geometrically connected when `k` is separably closed, and an abelian variety by Remark 0H2U
(`Stacks.PicardFunctor.isAbelianVariety_picardDegreeZero`). Its group of `k`-points is `Pic⁰(X)`
(`Stacks.PicardFunctor.picardDegreeZeroPointsMulEquiv`).

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Remark 0H2U](https://stacks.math.columbia.edu/tag/0H2U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  [IsCurve k (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable]

/-- The structure morphism of the group scheme `Pic⁰_{X/k}` is that of the degree-zero
component. -/
theorem picardDegreeZeroSubgroup_carrier_X_hom :
    (picardDegreeZeroSubgroup B hX hk f σ hσ).carrier.X.hom =
      B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom :=
  rfl

/-- The underlying scheme of the group scheme `Pic⁰_{X/k}` is the degree-zero component. -/
theorem picardDegreeZeroSubgroup_carrier_X_left :
    (picardDegreeZeroSubgroup B hX hk f σ hσ).carrier.X.left =
      B.inclusion.obj (picardSchemeDegreeComponent B hX hk f σ hσ 0).left :=
  rfl

/-- **`Pic⁰_{X/k}` is proper** as soon as the degree-zero component is. -/
theorem isProper_picardDegreeZeroSubgroup_carrier
    (hproper : IsProper (B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom)) :
    IsProper (picardDegreeZeroSubgroup B hX hk f σ hσ).carrier.X.hom :=
  hproper

/-- **`Pic⁰_{X/k}` is smooth** as soon as the degree-zero component is. -/
theorem smooth_picardDegreeZeroSubgroup_carrier
    (hsmooth : Smooth (B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom)) :
    Smooth (picardDegreeZeroSubgroup B hX hk f σ hσ).carrier.X.hom :=
  hsmooth

/-- **`Pic⁰_{X/k}` is connected** as soon as the degree-zero component is integral. -/
theorem connectedSpace_picardDegreeZeroSubgroup_carrier
    (hint : IsIntegral (B.inclusion.obj (picardSchemeDegreeComponent B hX hk f σ hσ 0).left)) :
    ConnectedSpace (picardDegreeZeroSubgroup B hX hk f σ hσ).carrier.X.left :=
  have := hint
  (inferInstance :
    ConnectedSpace (B.inclusion.obj (picardSchemeDegreeComponent B hX hk f σ hσ 0).left))

/-- **`Pic⁰_{X/k}` is geometrically connected** over a separably closed field as soon as the
degree-zero component is integral. -/
theorem geometricallyConnected_picardDegreeZeroSubgroup_carrier [IsSepClosed k]
    (hint : IsIntegral (B.inclusion.obj (picardSchemeDegreeComponent B hX hk f σ hσ 0).left)) :
    GeometricallyConnected (B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom) :=
  have := connectedSpace_picardDegreeZeroSubgroup_carrier B hX hk f σ hσ hint
  (geometricallyConnected_iff_connectedSpace k
    (B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom)).2 ‹_›

/-- **`Pic⁰_{X/k}` is an abelian variety** (Remark 0H2U) as soon as the degree-zero component is
a smooth proper integral scheme over `k`, which is clause (1) of [Stacks, Tag 0BA0]. -/
theorem isAbelianVariety_picardDegreeZero
    (hproper : IsProper (B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom))
    (hsmooth : Smooth (B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom))
    (hint : IsIntegral (B.inclusion.obj (picardSchemeDegreeComponent B hX hk f σ hσ 0).left)) :
    IsAbelianVariety k (picardDegreeZeroSubgroup B hX hk f σ hσ).carrier.X :=
  isAbelianVariety_of_choices k (picardDegreeZeroSubgroup B hX hk f σ hσ).carrier.X
    (Or.inr hproper)
    (Or.inr (Or.inr (Or.inr (connectedSpace_picardDegreeZeroSubgroup_carrier B hX hk f σ hσ hint))))
    (Or.inl hsmooth)

/-- **`Pic⁰(X)` is `n`-divisible** for `n` invertible in an algebraically closed field `k`, as
soon as the degree-zero component of the Picard scheme is a smooth proper integral scheme over
`k` (clause (1) of [Stacks, Tag 0BA0]): `Pic⁰_{X/k}` is an abelian variety whose `k`-points are
`Pic⁰(X)`, and clause (4) of [Stacks, Tag 03RP] applies. This is the hypothesis `hdvd` of the
consumers of [Stacks, Tag 03RQ] and [Stacks, Tag 03RR]. -/
theorem exists_nsmul_eq_of_mem_picardDegreeZero [IsAlgClosed k]
    (hproper : IsProper (B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom))
    (hsmooth : Smooth (B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ 0).hom))
    (hint : IsIntegral (B.inclusion.obj (picardSchemeDegreeComponent B hX hk f σ hσ 0).left))
    (n : ℕ) (hn : IsUnit (n : k)) (x : schemePicard X)
    (hx : x ∈ picardDegreeZero k (B.inclusion.map f)
      (topologicalKrullDim_le_one_of_isCurve B hX hk f)) :
    ∃ y, n • y = x :=
  have hconn := connectedSpace_picardDegreeZeroSubgroup_carrier B hX hk f σ hσ hint
  exists_nsmul_eq_curvePicardDegreeZero_of_jacobian k X (B.inclusion.map f) n
    (picardDegreeZeroSubgroup B hX hk f σ hσ) hproper hsmooth hconn
    ((picardDegreeZeroSubgroup B hX hk f σ hσ).flat_zpow_carrier_of_isUnit
      hproper hsmooth hconn n hn)
    (picardDegreeZeroPoints B hX hk f σ hσ) (picardDegreeZeroPoints_mul B hX hk f σ hσ)
    (bijective_picardDegreeZeroPoints B hX hk f σ hσ).2 x hx

end Stacks.PicardFunctor
