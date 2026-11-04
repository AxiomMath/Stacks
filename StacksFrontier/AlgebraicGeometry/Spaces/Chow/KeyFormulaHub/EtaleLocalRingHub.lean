module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleLocalRingStrictHenselization
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.NormalIntegralElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericStalkSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishing
public import StacksFrontier.RingTheory.Depth.FlatLocalDimension
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksFrontier.RingTheory.OrderOfVanishing.Henselization

/-!
# The étale local ring at a geometric point over the generic point of a prime divisor

Let `X` be a decent algebraic space, let `Z ⊂ X` be a prime divisor with generic point `ξ` and
let `x̄` be a geometric point of `X` lying over `ξ`. The proof of the key formula of Stacks 0EQU
compares, inside the étale local ring `R = 𝒪_{X, x̄}`, two rings it receives:

* the henselian local ring `𝒪^h_{X, ξ}`, in which the orders of vanishing along `Z` are read, and
* the local ring `𝒪_{V, q}` of an étale scheme chart `V` of `X` at a point `q` over `ξ`, on which
  invertible modules are trivialized.

This file is that hub. Both maps into `R` are produced, not assumed, and both are flat, local
and extend the maximal ideal of the source to the maximal ideal of `R`; `R` and `𝒪_{V, q}` are
Noetherian of Krull dimension one when `X` is locally Noetherian.

## Main definitions

* `AlgebraicGeometry.Space.chartStalkToEtaleLocalRing`: the canonical map of Stacks 05VP from the
  local ring of a chart at any spelling `p` of the chart point.
* `AlgebraicGeometry.Space.chartGeometricPointAt` and
  `AlgebraicGeometry.Space.chartNeighborhoodAt`: for an étale chart `V` of `X` and a point `q` of
  its scheme, a geometric point of `X` over `q` and the small étale neighbourhood of it with chart
  `V` and chart point `q`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericChartNeighborhood`: the small étale neighbourhood
  of `x̄` given by the chosen elementary étale neighbourhood of `ξ`.
* `AlgebraicGeometry.Space.PrimeDivisor.henselianToEtaleLocalRing`: the map
  `𝒪^h_{X, ξ} → 𝒪_{X, x̄}` of Stacks 0EMZ.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.henselianToEtaleLocalRing_stalkToHenselianLocalRing`: on
  the local ring of the chosen elementary étale neighbourhood of `ξ` the map of Stacks 0EMZ is
  the canonical map of Stacks 05VP, and
  `AlgebraicGeometry.Space.PrimeDivisor.eq_henselianToEtaleLocalRing`: it is the only local map
  with this property.
* `AlgebraicGeometry.Space.PrimeDivisor.isHenselization_henselianToEtaleLocalRing`: `𝒪_{X, x̄}` is
  a strict henselization of `𝒪^h_{X, ξ}` along it, whence
  `flat_henselianToEtaleLocalRing`, `isLocalHom_henselianToEtaleLocalRing` and
  `map_maximalIdeal_henselianToEtaleLocalRing`; for the chart leg the same three facts are
  `flat_chartStalkToEtaleLocalRing`, `isLocalHom_chartStalkToEtaleLocalRing` and
  `map_maximalIdeal_chartStalkToEtaleLocalRing`.
* `AlgebraicGeometry.Space.PrimeDivisor.ringKrullDim_etaleLocalRing_eq_one`,
  `AlgebraicGeometry.Space.PrimeDivisor.ringKrullDim_chartLocalRing_eq_one` and
  `AlgebraicGeometry.Space.PrimeDivisor.ringKrullDim_chartStalk_eq_one`: the étale local ring and
  the local ring of every chart at a point over `ξ` have dimension one.

## Implementation notes

The map of Stacks 0EMZ is the map of the universal property of the henselization (Stacks 04GS):
`𝒪^h_{X, ξ}` is a henselization of the local ring `A` of the chosen elementary étale
neighbourhood `(U, u)` of `ξ`, and `𝒪_{X, x̄}` is a henselian local `A`-algebra along the
canonical map of Stacks 05VP for the small étale neighbourhood of `x̄` that `(U, u)` determines.
Stacks 04GS makes the local `A`-algebra map unique, which is what pins it.

The chart point of a small étale neighbourhood is the image of the closed point under the chosen
lift; it equals a prescribed point `p` of the chart scheme only propositionally. The chart leg is
therefore stated on the stalk at `p`, transported along `TopCat.Presheaf.stalkCongr`, so that a
consumer holding a chart `V` and a point `q` reads it on `𝒪_{V, q}` itself.

## References

* [Stacks Project, Tag 04GS](https://stacks.math.columbia.edu/tag/04GS)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 0EMZ](https://stacks.math.columbia.edu/tag/0EMZ)
* [Stacks Project, Tag 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Opposite

universe u

namespace AlgebraicGeometry.Space

/-- A ring map making the target a henselization is flat, local and extends the maximal ideal. -/
private theorem flat_isLocalHom_map_maximalIdeal_of_isHenselization {R S L : Type*} [CommRing R]
    [IsLocalRing R] [Field L] [Algebra (ResidueField R) L] [CommRing S] [IsLocalRing S]
    (f : R →+* S) (h : @IsHenselization R _ _ L _ _ S _ _ f.toAlgebra) :
    f.Flat ∧ IsLocalHom f ∧ (maximalIdeal R).map f = maximalIdeal S :=
  let := f.toAlgebra
  ⟨IsHenselization.flat (L := L), IsHenselization.isLocalHom (L := L),
    IsHenselization.map_maximalIdeal (L := L)⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

include hX

/-! ### The chart leg at an arbitrary spelling of the chart point -/

/-- The canonical map of Stacks 05VP read on the stalk of the chart at a point `p` equal to the
chart point: the identification of the two stalks followed by
`AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing`. -/
def chartStalkToEtaleLocalRing {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x)
    {p : chartScheme V.chart} (hp : chartPoint B S hS X V = p) :
    (chartScheme V.chart).presheaf.stalk p →+* (etaleLocalRing B S hS X x : Type (u + 1)) :=
  (chartLocalRingToEtaleLocalRing B S hS X hX V).comp
    ((chartScheme V.chart).presheaf.stalkCongr (Inseparable.of_eq hp.symm)).hom.hom

/-- At the chart point itself the map of `AlgebraicGeometry.Space.chartStalkToEtaleLocalRing` is
the canonical map of Stacks 05VP. -/
theorem chartStalkToEtaleLocalRing_rfl {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) :
    chartStalkToEtaleLocalRing B S hS hX V (rfl : chartPoint B S hS X V = _) =
      chartLocalRingToEtaleLocalRing B S hS X hX V := by
  refine RingHom.ext fun r ↦ ?_
  simp [chartStalkToEtaleLocalRing, TopCat.Presheaf.stalkCongr]

/-- The map `AlgebraicGeometry.Space.chartStalkToEtaleLocalRing` sends the germ at `p` of a
regular function on the chart to its germ at the geometric point. -/
theorem chartStalkToEtaleLocalRing_germ {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) {p : chartScheme V.chart} (hp : chartPoint B S hS X V = p)
    (a : Γ(chartScheme V.chart, ⊤)) :
    chartStalkToEtaleLocalRing B S hS hX V hp
        ((chartScheme V.chart).presheaf.germ ⊤ p trivial a) =
      etaleLocalRingGerm B S hS X x (op V) a := by
  subst hp
  rw [chartStalkToEtaleLocalRing_rfl]
  exact chartLocalRingToEtaleLocalRing_germ B S hS X hX V a

/-- **Stacks 04KF at an arbitrary spelling of the chart point.** The étale local ring is a strict
henselization of the stalk of the chart at `p` along
`AlgebraicGeometry.Space.chartStalkToEtaleLocalRing`, for the absolute separable closure of the
residue field. -/
theorem isHenselization_chartStalkToEtaleLocalRing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) {p : chartScheme V.chart} (hp : chartPoint B S hS X V = p) :
    @IsHenselization ((chartScheme V.chart).presheaf.stalk p) _ _
      (SeparableClosure (ResidueField ((chartScheme V.chart).presheaf.stalk p))) _ _
      (etaleLocalRing B S hS X x : Type (u + 1)) _ (isLocalRing_etaleLocalRing B S hS X hX x)
      (chartStalkToEtaleLocalRing B S hS hX V hp).toAlgebra := by
  subst hp
  rw [chartStalkToEtaleLocalRing_rfl]
  let : IsLocalRing (etaleLocalRing B S hS X x : Type (u + 1)) :=
    isLocalRing_etaleLocalRing B S hS X hX x
  let : Algebra ↥(chartLocalRing B S hS X V) (etaleLocalRing B S hS X x : Type (u + 1)) :=
    (chartLocalRingToEtaleLocalRing B S hS X hX V).toAlgebra
  let : IsHenselization ↥(chartLocalRing B S hS X V)
      (separableClosure (ResidueField ↥(chartLocalRing B S hS X V))
        (chartGeometricPoint V).residueField)
      (etaleLocalRing B S hS X x : Type (u + 1)) :=
    isHenselization_chartLocalRingToEtaleLocalRing B S hS X hX V
  exact IsHenselization.of_algEquiv
    (IsSepClosure.equiv (ResidueField ↥(chartLocalRing B S hS X V))
      (SeparableClosure (ResidueField ↥(chartLocalRing B S hS X V)))
      (separableClosure (ResidueField ↥(chartLocalRing B S hS X V))
        (chartGeometricPoint V).residueField))

/-- The chart leg is flat. -/
theorem flat_chartStalkToEtaleLocalRing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) {p : chartScheme V.chart} (hp : chartPoint B S hS X V = p) :
    (chartStalkToEtaleLocalRing B S hS hX V hp).Flat :=
  let := isLocalRing_etaleLocalRing B S hS X hX x
  (flat_isLocalHom_map_maximalIdeal_of_isHenselization _
    (isHenselization_chartStalkToEtaleLocalRing B S hS hX V hp)).1

/-- The chart leg is a local homomorphism. -/
theorem isLocalHom_chartStalkToEtaleLocalRing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) {p : chartScheme V.chart} (hp : chartPoint B S hS X V = p) :
    IsLocalHom (chartStalkToEtaleLocalRing B S hS hX V hp) :=
  let := isLocalRing_etaleLocalRing B S hS X hX x
  (flat_isLocalHom_map_maximalIdeal_of_isHenselization _
    (isHenselization_chartStalkToEtaleLocalRing B S hS hX V hp)).2.1

/-- The chart leg extends the maximal ideal of the stalk to the maximal ideal of the étale local
ring. -/
theorem map_maximalIdeal_chartStalkToEtaleLocalRing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) {p : chartScheme V.chart} (hp : chartPoint B S hS X V = p) :
    letI := isLocalRing_etaleLocalRing B S hS X hX x
    (maximalIdeal ((chartScheme V.chart).presheaf.stalk p)).map
        (chartStalkToEtaleLocalRing B S hS hX V hp) =
      maximalIdeal (etaleLocalRing B S hS X x : Type (u + 1)) :=
  let := isLocalRing_etaleLocalRing B S hS X hX x
  (flat_isLocalHom_map_maximalIdeal_of_isHenselization _
    (isHenselization_chartStalkToEtaleLocalRing B S hS hX V hp)).2.2

/-! ### A geometric point over a point of a chart -/

/-- **Every point of an étale scheme chart is the chart point of a small étale neighbourhood of a
geometric point lying over its image in `|X|`.** -/
theorem exists_geometricPoint_chartLift_liesOver (V : SmallEtale B S hS X) (q : chartScheme V) :
    ∃ (xbar : GeometricPoint B S hS X) (ℓ : xbar.val.siteObject ⟶ V.obj.left)
      (_ : V.obj.hom.app (op xbar.val.siteObject) ℓ = xbar.val.value),
      xbar.LiesOver (chartSchemeToPoints B S hS X V q) ∧
        ((BigFppfOver.toScheme B S hS).map ℓ) (closedPoint xbar.val.carrier) = q := by
  obtain ⟨z, hz⟩ := surjective_pointsToScheme B S hS V.obj.left q
  obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B S hS X
    (pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom z)
  have hcp : ChartPoint B S hS V.obj.left V.obj.hom q xbar.image := by
    rw [hxbar, ← hz]
    exact chartPoint_pointsToScheme B S hS V.obj.left V.obj.hom z
  obtain ⟨ℓ, hℓ, hℓq⟩ := exists_chartLift_of_chartPoint B S hS hX xbar V q hcp
  refine ⟨xbar, ℓ, hℓ, ?_, hℓq⟩
  have hzq : (pointsEquivScheme B S hS V.obj.left).symm q = z :=
    (Equiv.symm_apply_eq _).2 hz.symm
  show xbar.image = _
  rw [chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm, hxbar]
  exact congrArg _ hzq.symm

/-- A geometric point of `X` over a point `q` of an étale chart `V`, chosen through
`AlgebraicGeometry.Space.exists_geometricPoint_chartLift_liesOver`. -/
def chartGeometricPointAt (V : SmallEtale B S hS X) (q : chartScheme V) :
    GeometricPoint B S hS X :=
  (exists_geometricPoint_chartLift_liesOver B S hS hX V q).choose

/-- The small étale neighbourhood of `AlgebraicGeometry.Space.chartGeometricPointAt` with chart
`V`, its chart point being `q`. -/
def chartNeighborhoodAt (V : SmallEtale B S hS X) (q : chartScheme V) :
    SmallEtaleNeighborhood (chartGeometricPointAt B S hS hX V q) where
  chart := V
  point := (exists_geometricPoint_chartLift_liesOver B S hS hX V q).choose_spec.choose
  point_comp :=
    (exists_geometricPoint_chartLift_liesOver B S hS hX V q).choose_spec.choose_spec.choose

/-- The chart of `AlgebraicGeometry.Space.chartNeighborhoodAt` is `V`. -/
@[simp]
theorem chartNeighborhoodAt_chart (V : SmallEtale B S hS X) (q : chartScheme V) :
    (chartNeighborhoodAt B S hS hX V q).chart = V :=
  rfl

/-- The geometric point `AlgebraicGeometry.Space.chartGeometricPointAt` lies over the image of
`q` in `|X|`. -/
theorem chartGeometricPointAt_liesOver (V : SmallEtale B S hS X) (q : chartScheme V) :
    (chartGeometricPointAt B S hS hX V q).LiesOver (chartSchemeToPoints B S hS X V q) :=
  (exists_geometricPoint_chartLift_liesOver B S hS hX V q).choose_spec.choose_spec.choose_spec.1

/-- The chart point of `AlgebraicGeometry.Space.chartNeighborhoodAt` is `q`. -/
theorem chartPoint_chartNeighborhoodAt (V : SmallEtale B S hS X) (q : chartScheme V) :
    chartPoint B S hS X (chartNeighborhoodAt B S hS hX V q) = q :=
  (exists_geometricPoint_chartLift_liesOver B S hS hX V q).choose_spec.choose_spec.choose_spec.2

/-- The identification of the local ring of the chart of
`AlgebraicGeometry.Space.chartNeighborhoodAt` with the stalk `𝒪_{V, q}`. -/
def chartLocalRingAtEquiv (V : SmallEtale B S hS X) (q : chartScheme V) :
    (chartScheme V).presheaf.stalk q ≃+*
      ↥(chartLocalRing B S hS X (chartNeighborhoodAt B S hS hX V q)) :=
  ((chartScheme V).presheaf.stalkCongr
    (Inseparable.of_eq (chartPoint_chartNeighborhoodAt B S hS hX V
        q).symm)).commRingCatIsoToRingEquiv

/-- **The chart leg on `𝒪_{V, q}`.** The canonical map of Stacks 05VP from the stalk of an étale
chart `V` at `q` to the étale local ring at the geometric point
`AlgebraicGeometry.Space.chartGeometricPointAt`. -/
abbrev chartStalkAtToEtaleLocalRing (V : SmallEtale B S hS X) (q : chartScheme V) :
    (chartScheme V).presheaf.stalk q →+*
      (etaleLocalRing B S hS X (chartGeometricPointAt B S hS hX V q) : Type (u + 1)) :=
  chartStalkToEtaleLocalRing B S hS hX (chartNeighborhoodAt B S hS hX V q)
    (chartPoint_chartNeighborhoodAt B S hS hX V q)

/-- `AlgebraicGeometry.Space.chartStalkAtToEtaleLocalRing` is the canonical map of Stacks 05VP
after the identification `AlgebraicGeometry.Space.chartLocalRingAtEquiv`. -/
theorem chartStalkAtToEtaleLocalRing_eq (V : SmallEtale B S hS X) (q : chartScheme V) :
    chartStalkAtToEtaleLocalRing B S hS hX V q =
      (chartLocalRingToEtaleLocalRing B S hS X hX (chartNeighborhoodAt B S hS hX V q)).comp
        (chartLocalRingAtEquiv B S hS hX V q).toRingHom :=
  rfl

/-! ### The map of Stacks 0EMZ at the generic point of a prime divisor -/

variable (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
  {xbar : GeometricPoint B S hS X} (hxbar : xbar.LiesOver (Z.genericPoint B S hS X))

/-- The small étale neighbourhood of a geometric point over the generic point of a prime divisor
given by the chosen elementary étale neighbourhood of that generic point. -/
abbrev PrimeDivisor.genericChartNeighborhood : SmallEtaleNeighborhood xbar :=
  (Z.genericChart B S hS hX hdec).smallEtaleNeighborhood xbar hxbar

/-- The canonical map of Stacks 05VP from the local ring `𝒪_{U, u}` of the chosen elementary
étale neighbourhood of the generic point to the étale local ring at a geometric point over it. -/
abbrev PrimeDivisor.genericStalkToEtaleLocalRing :
    ↥(Z.genericStalkRing B S hS hX hdec) →+* (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
  chartStalkToEtaleLocalRing B S hS hX (Z.genericChartNeighborhood B S hS hX hdec hxbar)
    (chartPoint_smallEtaleNeighborhood B S hS X hX (Z.genericChart B S hS hX hdec) xbar hxbar)

/-- The étale local ring at a geometric point over the generic point is a strict henselization of
`𝒪_{U, u}` along `AlgebraicGeometry.Space.PrimeDivisor.genericStalkToEtaleLocalRing`. -/
theorem PrimeDivisor.isHenselization_genericStalkToEtaleLocalRing :
    @IsHenselization ↥(Z.genericStalkRing B S hS hX hdec) _ _
      (SeparableClosure (ResidueField ↥(Z.genericStalkRing B S hS hX hdec))) _ _
      (etaleLocalRing B S hS X xbar : Type (u + 1)) _
      (isLocalRing_etaleLocalRing B S hS X hX xbar)
      (Z.genericStalkToEtaleLocalRing B S hS hX hdec hxbar).toAlgebra :=
  isHenselization_chartStalkToEtaleLocalRing B S hS hX
    (Z.genericChartNeighborhood B S hS hX hdec hxbar) (p := (Z.genericChart B S hS hX hdec).point)
    (chartPoint_smallEtaleNeighborhood B S hS X hX (Z.genericChart B S hS hX hdec) xbar hxbar)

/-- The algebra structure of the henselian local ring at the generic point over `𝒪_{U, u}`, given
by the canonical map of Stacks 0EMY. -/
abbrev PrimeDivisor.genericStalkAlgebra :
    Algebra ↥(Z.genericStalkRing B S hS hX hdec) ↥(Z.genericHenselianLocalRing B S hS hX hdec) :=
  stalkAlgebra B S hS X hX (Z.genericPoint B S hS X) hdec (Z.genericChart B S hS hX hdec)

/-- The henselian local ring at the generic point is a henselization of `𝒪_{U, u}`. -/
theorem PrimeDivisor.isHenselization_genericHenselianLocalRing :
    @IsHenselization ↥(Z.genericStalkRing B S hS hX hdec) _ _
      (ResidueField ↥(Z.genericStalkRing B S hS hX hdec)) _ _
      ↥(Z.genericHenselianLocalRing B S hS hX hdec) _
      (henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec)
      (Z.genericStalkAlgebra B S hS hX hdec) :=
  henselianLocalRing_isHenselization B S hS X hX (Z.genericPoint B S hS X) hdec
    (Z.genericChart B S hS hX hdec)

/-- The structure map of the henselization `𝒪_{U, u} → 𝒪^h_{X, ξ}` is local. -/
theorem PrimeDivisor.isLocalHom_genericStalkAlgebra :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    letI := Z.genericStalkAlgebra B S hS hX hdec
    IsLocalHom (algebraMap ↥(Z.genericStalkRing B S hS hX hdec)
        ↥(Z.genericHenselianLocalRing B S hS hX hdec)) :=
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  let := Z.genericStalkAlgebra B S hS hX hdec
  let := Z.isHenselization_genericHenselianLocalRing B S hS hX hdec
  IsHenselization.isLocalHom (L := ResidueField ↥(Z.genericStalkRing B S hS hX hdec))

/-- The instances under which Stacks 04GS produces the map `𝒪^h_{X, ξ} → 𝒪_{X, x̄}`: the
structure map of the strict henselization `𝒪_{U, u} → 𝒪_{X, x̄}` is local, its target is
henselian, and `𝒪^h_{X, ξ}` is ind-étale over `𝒪_{U, u}` with the same residue field. -/
theorem PrimeDivisor.henselianToEtaleLocalRing_aux :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    letI := Z.genericStalkAlgebra B S hS hX hdec
    letI := isLocalRing_etaleLocalRing B S hS X hX xbar
    letI := (Z.genericStalkToEtaleLocalRing B S hS hX hdec hxbar).toAlgebra
    letI := Z.isLocalHom_genericStalkAlgebra B S hS hX hdec
    IsLocalHom (algebraMap ↥(Z.genericStalkRing B S hS hX hdec)
        (etaleLocalRing B S hS X xbar : Type (u + 1))) ∧
      HenselianLocalRing (etaleLocalRing B S hS X xbar : Type (u + 1)) ∧
      StacksDraft.IndEtale ↥(Z.genericStalkRing B S hS hX hdec)
        ↥(Z.genericHenselianLocalRing B S hS hX hdec) ∧
      Function.Surjective (ResidueField.map (algebraMap ↥(Z.genericStalkRing B S hS hX hdec)
        ↥(Z.genericHenselianLocalRing B S hS hX hdec))) := by
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  let := Z.genericStalkAlgebra B S hS hX hdec
  let := isLocalRing_etaleLocalRing B S hS X hX xbar
  let := (Z.genericStalkToEtaleLocalRing B S hS hX hdec hxbar).toAlgebra
  let := Z.isLocalHom_genericStalkAlgebra B S hS hX hdec
  let hH := Z.isHenselization_genericHenselianLocalRing B S hS hX hdec
  let hR := Z.isHenselization_genericStalkToEtaleLocalRing B S hS hX hdec hxbar
  exact ⟨IsHenselization.isLocalHom
      (L := SeparableClosure (ResidueField ↥(Z.genericStalkRing B S hS hX hdec))),
    IsHenselization.henselian
      (L := SeparableClosure (ResidueField ↥(Z.genericStalkRing B S hS hX hdec)))
      (R := ↥(Z.genericStalkRing B S hS hX hdec)),
    IsHenselization.ind_etale (L := ResidueField ↥(Z.genericStalkRing B S hS hX hdec))
      (R := ↥(Z.genericStalkRing B S hS hX hdec)),
    (IsHenselization.residueField_map_bijective (R := ↥(Z.genericStalkRing B S hS hX hdec))
      (Rh := ↥(Z.genericHenselianLocalRing B S hS hX hdec))).2⟩

/-- **The map `𝒪^h_{X, ξ} → 𝒪_{X, x̄}` of Stacks 0EMZ.** For a geometric point `x̄` over the
generic point `ξ` of a prime divisor, the local map of local rings from the henselian local ring
at `ξ` to the étale local ring at `x̄` lying over the local ring `𝒪_{U, u}` of the chosen
elementary étale neighbourhood of `ξ`, along the canonical map of Stacks 05VP into the étale local
ring. It is the map of the universal property of the henselization, Stacks 04GS. -/
def PrimeDivisor.henselianToEtaleLocalRing :
    ↥(Z.genericHenselianLocalRing B S hS hX hdec) →+*
      (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
  letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  letI := Z.genericStalkAlgebra B S hS hX hdec
  letI := isLocalRing_etaleLocalRing B S hS X hX xbar
  letI := (Z.genericStalkToEtaleLocalRing B S hS hX hdec hxbar).toAlgebra
  letI := Z.isLocalHom_genericStalkAlgebra B S hS hX hdec
  have h := Z.henselianToEtaleLocalRing_aux B S hS hX hdec hxbar
  letI := h.1
  letI := h.2.1
  (HenselianLocalRing.indEtaleAlgHom (R := ↥(Z.genericStalkRing B S hS hX hdec))
    (Rh := ↥(Z.genericHenselianLocalRing B S hS hX hdec))
    (Sh := (etaleLocalRing B S hS X xbar : Type (u + 1))) h.2.2.1 h.2.2.2).toRingHom

/-- **The map of Stacks 0EMZ lies over `𝒪_{U, u}`.** On the image of the local ring of the chosen
elementary étale neighbourhood of `ξ` it is the canonical map of Stacks 05VP into the étale local
ring. -/
theorem PrimeDivisor.henselianToEtaleLocalRing_stalkToHenselianLocalRing
    (r : ↥(Z.genericStalkRing B S hS hX hdec)) :
    Z.henselianToEtaleLocalRing B S hS hX hdec hxbar
        (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
          (Z.genericChart B S hS hX hdec) r) =
      Z.genericStalkToEtaleLocalRing B S hS hX hdec hxbar r :=
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  let := Z.genericStalkAlgebra B S hS hX hdec
  let := isLocalRing_etaleLocalRing B S hS X hX xbar
  let := (Z.genericStalkToEtaleLocalRing B S hS hX hdec hxbar).toAlgebra
  let := Z.isLocalHom_genericStalkAlgebra B S hS hX hdec
  have h := Z.henselianToEtaleLocalRing_aux B S hS hX hdec hxbar
  let := h.1
  let := h.2.1
  (HenselianLocalRing.indEtaleAlgHom (R := ↥(Z.genericStalkRing B S hS hX hdec))
    (Rh := ↥(Z.genericHenselianLocalRing B S hS hX hdec))
    (Sh := (etaleLocalRing B S hS X xbar : Type (u + 1))) h.2.2.1 h.2.2.2).commutes r

/-- The map of Stacks 0EMZ is a local homomorphism. -/
theorem PrimeDivisor.isLocalHom_henselianToEtaleLocalRing :
    IsLocalHom (Z.henselianToEtaleLocalRing B S hS hX hdec hxbar) :=
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  let := Z.genericStalkAlgebra B S hS hX hdec
  let := isLocalRing_etaleLocalRing B S hS X hX xbar
  let := (Z.genericStalkToEtaleLocalRing B S hS hX hdec hxbar).toAlgebra
  let := Z.isLocalHom_genericStalkAlgebra B S hS hX hdec
  have h := Z.henselianToEtaleLocalRing_aux B S hS hX hdec hxbar
  let := h.1
  let := h.2.1
  have h' := HenselianLocalRing.isLocalHom_indEtaleAlgHom (R := ↥(Z.genericStalkRing B S hS hX
      hdec))
    (Rh := ↥(Z.genericHenselianLocalRing B S hS hX hdec))
    (Sh := (etaleLocalRing B S hS X xbar : Type (u + 1))) h.2.2.1 h.2.2.2
  ⟨fun a ha ↦ h'.map_nonunit a ha⟩

/-- **The map of Stacks 0EMZ is pinned by lying over `𝒪_{U, u}`.** Every local homomorphism
`𝒪^h_{X, ξ} → 𝒪_{X, x̄}` agreeing with the canonical map of Stacks 05VP on the image of the local
ring of the chosen elementary étale neighbourhood of `ξ` is
`AlgebraicGeometry.Space.PrimeDivisor.henselianToEtaleLocalRing`. -/
theorem PrimeDivisor.eq_henselianToEtaleLocalRing
    (f : ↥(Z.genericHenselianLocalRing B S hS hX hdec) →+*
      (etaleLocalRing B S hS X xbar : Type (u + 1)))
    (hf : letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
      letI := isLocalRing_etaleLocalRing B S hS X hX xbar
      IsLocalHom f)
    (hcomp : ∀ r, f (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
          (Z.genericChart B S hS hX hdec) r) =
        Z.genericStalkToEtaleLocalRing B S hS hX hdec hxbar r) :
    f = Z.henselianToEtaleLocalRing B S hS hX hdec hxbar := by
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  let := Z.genericStalkAlgebra B S hS hX hdec
  let := isLocalRing_etaleLocalRing B S hS X hX xbar
  let := (Z.genericStalkToEtaleLocalRing B S hS hX hdec hxbar).toAlgebra
  let := Z.isLocalHom_genericStalkAlgebra B S hS hX hdec
  have h := Z.henselianToEtaleLocalRing_aux B S hS hX hdec hxbar
  let := h.1
  let := h.2.1
  exact congrArg AlgHom.toRingHom (HenselianLocalRing.indEtaleAlgHom_unique h.2.2.1 h.2.2.2
    { f with commutes' := hcomp } ⟨fun a ha ↦ hf.map_nonunit a ha⟩)

/-- The residue field extension along which `𝒪_{X, x̄}` is a strict henselization of
`𝒪^h_{X, ξ}`: the residue field of `𝒪_{X, x̄}` itself, over the residue field of `𝒪^h_{X, ξ}` by
the map induced by `AlgebraicGeometry.Space.PrimeDivisor.henselianToEtaleLocalRing`. -/
abbrev PrimeDivisor.henselianToEtaleLocalRingResidueAlgebra :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    letI := isLocalRing_etaleLocalRing B S hS X hX xbar
    Algebra (ResidueField ↥(Z.genericHenselianLocalRing B S hS hX hdec))
      (ResidueField (etaleLocalRing B S hS X xbar : Type (u + 1))) :=
  letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  letI := isLocalRing_etaleLocalRing B S hS X hX xbar
  letI := Z.isLocalHom_henselianToEtaleLocalRing B S hS hX hdec hxbar
  (ResidueField.map (Z.henselianToEtaleLocalRing B S hS hX hdec hxbar)).toAlgebra

/-- **Stacks 0EMZ along the named map.** The étale local ring at a geometric point over the
generic point of a prime divisor is a strict henselization of the henselian local ring at the
generic point along `AlgebraicGeometry.Space.PrimeDivisor.henselianToEtaleLocalRing`. -/
theorem PrimeDivisor.isHenselization_henselianToEtaleLocalRing :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    letI := isLocalRing_etaleLocalRing B S hS X hX xbar
    letI := Z.henselianToEtaleLocalRingResidueAlgebra B S hS hX hdec hxbar
    letI := (Z.henselianToEtaleLocalRing B S hS hX hdec hxbar).toAlgebra
    IsHenselization ↥(Z.genericHenselianLocalRing B S hS hX hdec)
      (ResidueField (etaleLocalRing B S hS X xbar : Type (u + 1)))
      (etaleLocalRing B S hS X xbar : Type (u + 1)) := by
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  let := Z.genericStalkAlgebra B S hS hX hdec
  let := isLocalRing_etaleLocalRing B S hS X hX xbar
  let := Z.isLocalHom_henselianToEtaleLocalRing B S hS hX hdec hxbar
  let := Z.henselianToEtaleLocalRingResidueAlgebra B S hS hX hdec hxbar
  let algA := (Z.genericStalkToEtaleLocalRing B S hS hX hdec hxbar).toAlgebra
  let := (Z.henselianToEtaleLocalRing B S hS hX hdec hxbar).toAlgebra
  let := Z.isLocalHom_genericStalkAlgebra B S hS hX hdec
  have h := Z.henselianToEtaleLocalRing_aux B S hS hX hdec hxbar
  let hR := Z.isHenselization_genericStalkToEtaleLocalRing B S hS hX hdec hxbar
  have : IsScalarTower ↥(Z.genericStalkRing B S hS hX hdec)
      ↥(Z.genericHenselianLocalRing B S hS hX hdec)
      (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
    IsScalarTower.of_algebraMap_eq fun r ↦
      (Z.henselianToEtaleLocalRing_stalkToHenselianLocalRing B S hS hX hdec hxbar r).symm
  refine ⟨h.2.1, StacksDraft.indEtale_of_comp h.2.2.1
    (IsHenselization.ind_etale
      (L := SeparableClosure (ResidueField ↥(Z.genericStalkRing B S hS hX hdec)))
      (R := ↥(Z.genericStalkRing B S hS hX hdec))), RingEquiv.refl _,
    fun y ↦ (ResidueField.map_residue _ y).symm⟩

/-- The map of Stacks 0EMZ is flat. -/
theorem PrimeDivisor.flat_henselianToEtaleLocalRing :
    (Z.henselianToEtaleLocalRing B S hS hX hdec hxbar).Flat :=
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  let := isLocalRing_etaleLocalRing B S hS X hX xbar
  let := Z.henselianToEtaleLocalRingResidueAlgebra B S hS hX hdec hxbar
  (flat_isLocalHom_map_maximalIdeal_of_isHenselization _
    (Z.isHenselization_henselianToEtaleLocalRing B S hS hX hdec hxbar)).1

/-- The map of Stacks 0EMZ extends the maximal ideal of `𝒪^h_{X, ξ}` to the maximal ideal of
`𝒪_{X, x̄}`. -/
theorem PrimeDivisor.map_maximalIdeal_henselianToEtaleLocalRing :
    letI := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
    letI := isLocalRing_etaleLocalRing B S hS X hX xbar
    (maximalIdeal ↥(Z.genericHenselianLocalRing B S hS hX hdec)).map
        (Z.henselianToEtaleLocalRing B S hS hX hdec hxbar) =
      maximalIdeal (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  let := isLocalRing_etaleLocalRing B S hS X hX xbar
  let := Z.henselianToEtaleLocalRingResidueAlgebra B S hS hX hdec hxbar
  (flat_isLocalHom_map_maximalIdeal_of_isHenselization _
    (Z.isHenselization_henselianToEtaleLocalRing B S hS hX hdec hxbar)).2.2

/-- The map of Stacks 0EMZ carries nonzerodivisors to nonzerodivisors, being flat. -/
theorem PrimeDivisor.henselianToEtaleLocalRing_mem_nonZeroDivisors
    {r : ↥(Z.genericHenselianLocalRing B S hS hX hdec)}
    (hr : r ∈ nonZeroDivisors ↥(Z.genericHenselianLocalRing B S hS hX hdec)) :
    Z.henselianToEtaleLocalRing B S hS hX hdec hxbar r ∈
      nonZeroDivisors (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
  let := henselianLocalRing_isLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec
  let := isLocalRing_etaleLocalRing B S hS X hX xbar
  let := Z.henselianToEtaleLocalRingResidueAlgebra B S hS hX hdec hxbar
  let := (Z.henselianToEtaleLocalRing B S hS hX hdec hxbar).toAlgebra
  let := Z.isHenselization_henselianToEtaleLocalRing B S hS hX hdec hxbar
  IsHenselization.algebraMap_mem_nonZeroDivisors
    (ResidueField (etaleLocalRing B S hS X xbar : Type (u + 1))) hr

/-! ### Dimension one -/

include hdec hxbar in
/-- **The étale local ring at a geometric point over the generic point of a prime divisor has
Krull dimension one**: it has the dimension of the local ring of `|X|` at the generic point,
which is one on a decent algebraic space by Stacks 0ED1. -/
theorem PrimeDivisor.ringKrullDim_etaleLocalRing_eq_one :
    ringKrullDim (etaleLocalRing B S hS X xbar : Type (u + 1)) = 1 := by
  rw [ringKrullDim_etaleLocalRing_eq_localRingDimension hX xbar, hxbar,
    PrimeDivisor.localRingDimension_genericPoint B S hS hX hdec Z]
  rfl

variable (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))

include hdec hxbar hN in
/-- **The local ring of an étale chart at a point over the generic point of a prime divisor has
Krull dimension one**, read at any spelling `p` of the chart point of a small étale neighbourhood
of a geometric point over the generic point: it maps flatly and locally to the étale local ring,
with closed fibre the residue field, so it has the dimension of the étale local ring. -/
theorem PrimeDivisor.ringKrullDim_chartStalk_eq_one (V : SmallEtaleNeighborhood xbar)
    {p : chartScheme V.chart} (hp : chartPoint B S hS X V = p) :
    ringKrullDim ((chartScheme V.chart).presheaf.stalk p) = 1 := by
  let := isLocalRing_etaleLocalRing B S hS X hX xbar
  let := isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS X hX hN xbar
  let : IsLocallyNoetherian (chartScheme V.chart) :=
    (exists_atlas_iff_forall_etale B S hS X (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) hX).mp
    hN V.chart.obj.left V.chart.obj.hom V.chart.property
  let := (chartStalkToEtaleLocalRing B S hS hX V hp).toAlgebra
  let : Module.Flat ((chartScheme V.chart).presheaf.stalk p)
      (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
    flat_chartStalkToEtaleLocalRing B S hS hX V hp
  have : IsLocalHom (algebraMap ((chartScheme V.chart).presheaf.stalk p)
      (etaleLocalRing B S hS X xbar : Type (u + 1))) :=
    isLocalHom_chartStalkToEtaleLocalRing B S hS hX V hp
  rw [Stacks.FlatLocalDimension.ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq
    (map_maximalIdeal_chartStalkToEtaleLocalRing B S hS hX V hp)]
  exact Z.ringKrullDim_etaleLocalRing_eq_one B S hS hX hdec hxbar

include hdec hxbar hN in
/-- **The local ring of a small étale neighbourhood of a geometric point over the generic point of
a prime divisor has Krull dimension one.** -/
theorem PrimeDivisor.ringKrullDim_chartLocalRing_eq_one (V : SmallEtaleNeighborhood xbar) :
    ringKrullDim ↥(chartLocalRing B S hS X V) = 1 :=
  Z.ringKrullDim_chartStalk_eq_one B S hS hX hdec hxbar hN V rfl

omit hxbar in
include hdec hN in
/-- **The local ring `𝒪_{V, q}` of an étale chart at a point over the generic point of a prime
divisor has Krull dimension one.** -/
theorem PrimeDivisor.ringKrullDim_stalk_eq_one (V : SmallEtale B S hS X) (q : chartScheme V)
    (hq : chartSchemeToPoints B S hS X V q = Z.genericPoint B S hS X) :
    ringKrullDim ((chartScheme V).presheaf.stalk q) = 1 :=
  Z.ringKrullDim_chartStalk_eq_one B S hS hX hdec
    ((chartGeometricPointAt_liesOver B S hS hX V q).trans hq) hN
    (chartNeighborhoodAt B S hS hX V q) (chartPoint_chartNeighborhoodAt B S hS hX V q)

end AlgebraicGeometry.Space

end
