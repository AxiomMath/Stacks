module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricEvaluationSections
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceSchemeComparison
public import StacksFrontier.Homology.Tor.IndependenceUniverseChange

/-!
# The `Type u` models of the étale local rings of a diagram of charts

The étale local ring of an algebraic space at a geometric point lives in `Type (u + 1)`, being a
colimit indexed by the small étale neighbourhoods of the point, while the rings of sections of a
scheme live in `Type u`.  For a *representable* algebraic space and its identity chart Stacks
04KF identifies the étale local ring with the strict henselization of the ordinary local ring of
the chart, which is in `Type u`; this file fixes that strict henselization as the `Type u` model
`AlgebraicGeometry.Space.yonedaChartSH`, transports the canonical homomorphism of étale local
rings of Stacks 04NG to it, and proves the two facts about the model that the comparison of
conditions (1) and (4) of Stacks 08IQ rests on:

* Tor independence of the étale local rings descends to Tor independence of the models, which is
  a change of universe and not a base change;
* the model is flat over the ring of sections of an affine open of the chart, and the induced
  map `Γ(U, U') ⊗_{Γ(W, W')} 𝒪^{sh}_{W, w̄} → 𝒪^{sh}_{U, ū}` is flat, which is Stacks 08HV.

## Main definitions

* `AlgebraicGeometry.Space.siteScheme` is the scheme underlying an object of the big fppf
  category over `S`.
* `AlgebraicGeometry.Space.yonedaChartLocalRing` and
  `AlgebraicGeometry.Space.yonedaChartSH` are the local ring of the identity chart at the point
  under a geometric point and its strict henselization.
* `AlgebraicGeometry.Space.yonedaChartSHEquiv` is Stacks 04KF at the identity chart.
* `AlgebraicGeometry.Space.yonedaChartSHAlgebra` and
  `AlgebraicGeometry.Space.yonedaChartSHAlgebraCongr` are the structure maps of the models over
  a morphism of the site, the second carrying the transport along an equality of the images of a
  pair of geometric points.
* `AlgebraicGeometry.Space.yonedaChartSHCongrEquiv` compares the two models of the étale local
  ring of the base attached to the two members of such a pair.

## Main results

* `AlgebraicGeometry.Space.algebraMap_yonedaChartSH_comp` is Stacks 05VU for the models.
* `AlgebraicGeometry.Space.torIndependent_yonedaChartSH`: Tor independence of the étale local
  rings at a compatible pair of geometric points gives Tor independence of the models.
* `AlgebraicGeometry.Space.flat_tensorProduct_lift_chart` and
  `AlgebraicGeometry.Space.flat_tensorProduct_lift_yonedaChart` are Stacks 08HV for a morphism
  of schemes over a pair of affine opens and for the identity charts of the site.
* `AlgebraicGeometry.Space.flat_algebraMap_yonedaChartSH`: the model is flat over the ring of
  sections of an affine open containing the point.

## Implementation notes

The two localizations `𝒪_{W, w}` and `𝒪_{U, u}` are parameters of
`AlgebraicGeometry.Space.flat_tensorProduct_lift_chart` rather than being taken to be the
stalks, with their localization presentations as hypotheses.  That is what lets the consumer
spell them as `AlgebraicGeometry.Space.yonedaChartLocalRing`, which is the spelling the
henselization-tower instances of
`AlgebraicGeometry.Space.chartHenselizationTower` are stated at: the two spellings are equal by
definition but not syntactically, and instance search does not unfold
`AlgebraicGeometry.Space.geometricPointMap`.

The structure map of the models is *defined* by transporting the canonical homomorphism of
Stacks 04NG along Stacks 04KF, so the compatibilities that
`RingTheory.TorIndependence.torIndependent_congr_universe` asks for hold by construction, and
Stacks 05VU for the models is Stacks 05VU for the étale local rings read through the
transport.

## References

* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 08HV](https://stacks.math.columbia.edu/tag/08HV)
* [Stacks Project, Tag 08IQ](https://stacks.math.columbia.edu/tag/08IQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The scheme underlying an object of the big fppf category over `S`. -/
abbrev siteScheme (X₀ : BigFppfOver B S hS) : Scheme.{u} :=
  (BigFppfOver.toScheme B S hS).obj X₀

/-- The local ring of the identity chart of a representable algebraic space at the point under a
geometric point. -/
abbrev yonedaChartLocalRing (U₀ : BigFppfOver B S hS)
    (x : GeometricPoint B S hS (yoneda.obj U₀)) : CommRingCat.{u} :=
  chartLocalRing B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ x)

/-- **The `Type u` model of the étale local ring of a representable algebraic space at a
geometric point**: the strict henselization, chosen in
`AlgebraicGeometry.Space.chartHenselizationTower`, of the local ring of the identity chart. -/
abbrev yonedaChartSH (U₀ : BigFppfOver B S hS)
    (x : GeometricPoint B S hS (yoneda.obj U₀)) : Type u :=
  (chartHenselizationTower B S hS (yoneda.obj U₀)
    (yonedaIdentityNeighborhood U₀ x)).strictHenselization

/-- **Stacks 04KF at the identity chart.**  The model is the étale local ring. -/
abbrev yonedaChartSHEquiv (U₀ : BigFppfOver B S hS)
    (x : GeometricPoint B S hS (yoneda.obj U₀)) :
    yonedaChartSH B S hS U₀ x ≃+* ↥(etaleLocalRing B S hS (yoneda.obj U₀) x) :=
  chartStrictHenselizationEquiv B S hS (yoneda.obj U₀) (isAlgebraicSpace_yoneda B S hS U₀)
    (yonedaIdentityNeighborhood U₀ x)

/-- **The structure map of the models over a morphism of the site.**  The canonical homomorphism
of étale local rings of Stacks 04NG, transported along Stacks 04KF.

Defining it by transport is what makes the compatibility hypotheses of
`RingTheory.TorIndependence.torIndependent_congr_universe` hold by construction. -/
@[instance_reducible]
def yonedaChartSHAlgebra {U₀ W₀ : BigFppfOver B S hS} (g : U₀ ⟶ W₀)
    (x : GeometricPoint B S hS (yoneda.obj U₀)) :
    Algebra (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map g) x))
      (yonedaChartSH B S hS U₀ x) :=
  RingHom.toAlgebra
    ((yonedaChartSHEquiv B S hS U₀ x).symm.toRingHom.comp
      ((etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS U₀) (yoneda.map g) x).comp
        (yonedaChartSHEquiv B S hS W₀ (geometricPointMap (yoneda.map g) x)).toRingHom))

/-- **Stacks 05VU for the models.**  The square of the local ring of the chart of the base, its
strict henselization, the local ring of the chart of the source and its strict henselization
commutes. -/
theorem algebraMap_yonedaChartSH_comp {U₀ W₀ : BigFppfOver B S hS} (g : U₀ ⟶ W₀)
    (x : GeometricPoint B S hS (yoneda.obj U₀))
    (s : ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map g) x))) :
    letI := yonedaChartSHAlgebra B S hS g x
    algebraMap (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map g) x))
        (yonedaChartSH B S hS U₀ x)
        (algebraMap ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map g) x))
          (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map g) x)) s) =
      algebraMap ↥(yonedaChartLocalRing B S hS U₀ x) (yonedaChartSH B S hS U₀ x)
        ((((BigFppfOver.toScheme B S hS).map g).stalkMap
          (chartPoint B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ x))).hom s) := by
  let := yonedaChartSHAlgebra B S hS g x
  let e := yonedaChartSHEquiv B S hS U₀ x
  exact e.injective ((e.apply_symm_apply _).trans (DFunLike.congr_fun
    (etaleLocalRingMap_comp_chartLocalRingToEtaleLocalRing_yoneda B S hS g x) s).symm)

/-- **The structure map of the models over the second morphism of a compatible pair.**  The
canonical homomorphism of étale local rings of Stacks 04NG at the second point, precomposed with
the transport along the equality of the two images in the base and transported along Stacks
04KF.

This is the structure map that the definition of Tor independence of algebraic spaces, Stacks
08IP, carries on the second factor: both factors are algebras over the étale local ring of the
base at the image of the *first* point. -/
@[instance_reducible]
def yonedaChartSHAlgebraCongr {U₀ V₀ W₀ : BigFppfOver B S hS} (uw : U₀ ⟶ W₀) (vw : V₀ ⟶ W₀)
    {ubar : GeometricPoint B S hS (yoneda.obj U₀)}
    {vbar : GeometricPoint B S hS (yoneda.obj V₀)}
    (hpt : geometricPointMap (yoneda.map uw) ubar = geometricPointMap (yoneda.map vw) vbar) :
    Algebra (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))
      (yonedaChartSH B S hS V₀ vbar) :=
  RingHom.toAlgebra
    ((yonedaChartSHEquiv B S hS V₀ vbar).symm.toRingHom.comp
      (((etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS V₀) (yoneda.map vw) vbar).comp
          (eqToHom (congrArg (etaleLocalRing B S hS (yoneda.obj W₀)) hpt)).hom).comp
        (yonedaChartSHEquiv B S hS W₀ (geometricPointMap (yoneda.map uw) ubar)).toRingHom))

/-- **The comparison of the two models of the étale local ring of the base.**  The two members of
a compatible pair of geometric points have equal images in the base, so the two models of the
étale local ring there — one for each member — are isomorphic, through the transport along that
equality and Stacks 04KF on both sides. -/
def yonedaChartSHCongrEquiv {U₀ V₀ W₀ : BigFppfOver B S hS} (uw : U₀ ⟶ W₀) (vw : V₀ ⟶ W₀)
    {ubar : GeometricPoint B S hS (yoneda.obj U₀)}
    {vbar : GeometricPoint B S hS (yoneda.obj V₀)}
    (hpt : geometricPointMap (yoneda.map uw) ubar = geometricPointMap (yoneda.map vw) vbar) :
    yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar) ≃+*
      yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map vw) vbar) :=
  ((yonedaChartSHEquiv B S hS W₀ (geometricPointMap (yoneda.map uw) ubar)).trans
    ((eqToIso (congrArg (etaleLocalRing B S hS (yoneda.obj W₀))
      hpt)).commRingCatIsoToRingEquiv)).trans
    (yonedaChartSHEquiv B S hS W₀ (geometricPointMap (yoneda.map vw) vbar)).symm

/-- The comparison of the two models of the étale local ring of the base carries the structure
map from the local ring of the chart to the structure map from the local ring of the chart at the
second point, up to the transport along the equality of the two chart local rings. -/
theorem yonedaChartSHCongrEquiv_algebraMap {U₀ V₀ W₀ : BigFppfOver B S hS}
    (uw : U₀ ⟶ W₀) (vw : V₀ ⟶ W₀)
    {ubar : GeometricPoint B S hS (yoneda.obj U₀)}
    {vbar : GeometricPoint B S hS (yoneda.obj V₀)}
    (hpt : geometricPointMap (yoneda.map uw) ubar = geometricPointMap (yoneda.map vw) vbar)
    (h₁ : yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map uw) ubar) =
      yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map vw) vbar))
    (s : ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))) :
    yonedaChartSHCongrEquiv B S hS uw vw hpt
        (algebraMap ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))
          (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar)) s) =
      algebraMap ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map vw) vbar))
        (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map vw) vbar))
        ((eqToHom h₁).hom s) := by
  let e := yonedaChartSHEquiv B S hS W₀ (geometricPointMap (yoneda.map vw) vbar)
  exact e.injective ((e.apply_symm_apply _).trans <| DFunLike.congr_fun
    (chartLocalRingToEtaleLocalRing_yonedaIdentityNeighborhood_congr B S hS W₀ hpt h₁
      (congrArg (etaleLocalRing B S hS (yoneda.obj W₀)) hpt)) s)

/-- The comparison of the two models of the étale local ring of the base is compatible with the
two structure maps into the model at the second point. -/
theorem algebraMap_yonedaChartSHCongrEquiv {U₀ V₀ W₀ : BigFppfOver B S hS}
    (uw : U₀ ⟶ W₀) (vw : V₀ ⟶ W₀)
    {ubar : GeometricPoint B S hS (yoneda.obj U₀)}
    {vbar : GeometricPoint B S hS (yoneda.obj V₀)}
    (hpt : geometricPointMap (yoneda.map uw) ubar = geometricPointMap (yoneda.map vw) vbar)
    (t : yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar)) :
    letI := yonedaChartSHAlgebra B S hS vw vbar
    letI := yonedaChartSHAlgebraCongr B S hS uw vw hpt
    algebraMap (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map vw) vbar))
        (yonedaChartSH B S hS V₀ vbar) (yonedaChartSHCongrEquiv B S hS uw vw hpt t) =
      algebraMap (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))
        (yonedaChartSH B S hS V₀ vbar) t :=
  congrArg (fun y => (yonedaChartSHEquiv B S hS V₀ vbar).symm
      (etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS V₀) (yoneda.map vw) vbar y))
    ((yonedaChartSHEquiv B S hS W₀
      (geometricPointMap (yoneda.map vw) vbar)).apply_symm_apply _)

/-- **Tor independence of the étale local rings descends to the models.**  If two representable
algebraic spaces are Tor independent over a third in the sense of Stacks 08IP, then at every
compatible pair of geometric points the three `Type u` models of the étale local rings are Tor
independent.

The existential witnesses of Stacks 08IP are replaced by the canonical homomorphisms of Stacks
04NG using `AlgebraicGeometry.Space.eq_etaleLocalRingMap`, which is what the structure maps of
the models are transported from, and the descent of the universe is
`RingTheory.TorIndependence.torIndependent_congr_universe`. -/
theorem torIndependent_yonedaChartSH {U₀ V₀ W₀ : BigFppfOver B S hS} (uw : U₀ ⟶ W₀)
    (vw : V₀ ⟶ W₀)
    (h : TorIndependent (isAlgebraicSpace_yoneda B S hS U₀) (isAlgebraicSpace_yoneda B S hS V₀)
      (isAlgebraicSpace_yoneda B S hS W₀) (yoneda.map uw) (yoneda.map vw))
    (ubar : GeometricPoint B S hS (yoneda.obj U₀))
    (vbar : GeometricPoint B S hS (yoneda.obj V₀))
    (hpt : geometricPointMap (yoneda.map uw) ubar = geometricPointMap (yoneda.map vw) vbar) :
    letI := yonedaChartSHAlgebra B S hS uw ubar
    letI := yonedaChartSHAlgebraCongr B S hS uw vw hpt
    RingTheory.TorIndependence.TorIndependent
      (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))
      (yonedaChartSH B S hS U₀ ubar) (yonedaChartSH B S hS V₀ vbar) := by
  let := yonedaChartSHAlgebra B S hS uw ubar
  let := yonedaChartSHAlgebraCongr B S hS uw vw hpt
  obtain ⟨φ, ψ, hφ, hψ, htor⟩ := h ubar vbar hpt
  obtain rfl := eq_etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS U₀) (yoneda.map uw) ubar hφ
  obtain rfl := eq_etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS V₀) (yoneda.map vw) vbar hψ
  let : Algebra ↥(etaleLocalRing B S hS (yoneda.obj W₀)
        (geometricPointMap (yoneda.map uw) ubar))
      ↥(etaleLocalRing B S hS (yoneda.obj U₀) ubar) :=
    (etaleLocalRingMap (isAlgebraicSpace_yoneda B S hS U₀) (yoneda.map uw) ubar).toAlgebra
  let : Algebra ↥(etaleLocalRing B S hS (yoneda.obj W₀)
        (geometricPointMap (yoneda.map uw) ubar))
      ↥(etaleLocalRing B S hS (yoneda.obj V₀) vbar) :=
    ((eqToHom (congrArg (etaleLocalRing B S hS (yoneda.obj W₀)) hpt) ≫
      CommRingCat.ofHom (etaleLocalRingMap
        (isAlgebraicSpace_yoneda B S hS V₀) (yoneda.map vw) vbar)).hom).toAlgebra
  exact (RingTheory.TorIndependence.torIndependent_congr_universe.{u, u + 1}
    (yonedaChartSHEquiv B S hS W₀ (geometricPointMap (yoneda.map uw) ubar))
    (yonedaChartSHEquiv B S hS U₀ ubar) (yonedaChartSHEquiv B S hS V₀ vbar)
    (fun _ => (yonedaChartSHEquiv B S hS U₀ ubar).apply_symm_apply _)
    (fun _ => (yonedaChartSHEquiv B S hS V₀ vbar).apply_symm_apply _)).mp htor

/-- **Stacks 08HV over a pair of affine opens of a morphism of schemes.**  Let `f : X ⟶ Y` be a
morphism of schemes, let `W' ⊆ Y` and `U' ⊆ f ⁻¹ᵁ W'` be affine opens and let `u ∈ U'`.  Let
`Rp`, `Sq` present the local rings of `Y` at `f u` and of `X` at `u` as localizations of the two
rings of sections, and let `Rsh`, `Ssh` be strict henselizations of them over a local
homomorphism.  Then the induced map `Γ(X, U') ⊗_{Γ(Y, W')} Rsh → Ssh` is flat.

The primes the two localizations are taken at are the primes of the two rings of sections
corresponding to the two points, and they lie over one another by
`AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE`, which is the only thing this adds to
`IsLocalRing.IsHenselization.flat_tensorProduct_lift_atPrime`. -/
theorem flat_tensorProduct_lift_chart {X Y : Scheme.{u}} (f : X ⟶ Y)
    {W' : Y.Opens} (hW' : IsAffineOpen W') {U' : X.Opens} (hU' : IsAffineOpen U')
    (hUW : U' ≤ f ⁻¹ᵁ W') {u : X} (hu : u ∈ U')
    (Rp Sq Rsh Ssh : Type u)
    [CommRing Rp] [IsLocalRing Rp] [CommRing Sq] [IsLocalRing Sq]
    [CommRing Rsh] [IsLocalRing Rsh] [CommRing Ssh] [IsLocalRing Ssh]
    [Algebra ↥Γ(Y, W') ↥Γ(X, U')]
    [Algebra ↥Γ(Y, W') Rp] [Algebra ↥Γ(X, U') Sq] [Algebra ↥Γ(Y, W') Sq]
    [Algebra Rp Sq] [IsScalarTower ↥Γ(Y, W') ↥Γ(X, U') Sq]
    [IsScalarTower ↥Γ(Y, W') Rp Sq]
    [IsLocalization.AtPrime Rp (hW'.primeIdealOf ⟨f.base u, hUW hu⟩).asIdeal]
    [IsLocalization.AtPrime Sq (hU'.primeIdealOf ⟨u, hu⟩).asIdeal]
    [Algebra Rp Rsh] [Algebra ↥Γ(Y, W') Rsh] [IsScalarTower ↥Γ(Y, W') Rp Rsh]
    [Algebra Sq Ssh] [Algebra ↥Γ(X, U') Ssh] [IsScalarTower ↥Γ(X, U') Sq Ssh]
    [Algebra Rp Ssh] [IsScalarTower Rp Sq Ssh] [Algebra ↥Γ(Y, W') Ssh]
    [IsScalarTower ↥Γ(Y, W') Rp Ssh] [IsScalarTower ↥Γ(Y, W') ↥Γ(X, U') Ssh]
    [Algebra Rsh Ssh] [IsScalarTower ↥Γ(Y, W') Rsh Ssh]
    [IsLocalHom (algebraMap Rsh Ssh)]
    (halg : ∀ r, algebraMap ↥Γ(Y, W') ↥Γ(X, U') r = (f.appLE W' U' hUW).hom r)
    (LR LS : Type u)
    [Field LR] [Algebra (ResidueField Rp) LR] [IsSepClosure (ResidueField Rp) LR]
    [IsHenselization Rp LR Rsh]
    [Field LS] [Algebra (ResidueField Sq) LS] [IsSepClosure (ResidueField Sq) LS]
    [IsHenselization Sq LS Ssh] :
    RingHom.Flat (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom ↥Γ(Y, W') ↥Γ(X, U') Ssh)
      (IsScalarTower.toAlgHom ↥Γ(Y, W') Rsh Ssh) fun _ _ => Commute.all _ _).toRingHom := by
  have : (hU'.primeIdealOf ⟨u, hu⟩).asIdeal.LiesOver
      (hW'.primeIdealOf ⟨f.base u, hUW hu⟩).asIdeal := by
    refine ⟨?_⟩
    have hc := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE (f := f) (x := u) W' hW' U' hU' hUW hu)
    have hmap : algebraMap ↥Γ(Y, W') ↥Γ(X, U') = (f.appLE W' U' hUW).hom :=
      RingHom.ext halg
    change (hW'.primeIdealOf ⟨f.base u, hUW hu⟩).asIdeal =
      Ideal.comap (algebraMap ↥Γ(Y, W') ↥Γ(X, U')) (hU'.primeIdealOf ⟨u, hu⟩).asIdeal
    rw [hmap]
    exact hc.symm
  exact IsLocalRing.IsHenselization.flat_tensorProduct_lift_atPrime
    (R := ↥Γ(Y, W')) (S := ↥Γ(X, U')) (Rp := Rp) (Sq := Sq)
    (Rsh := Rsh) (Ssh := Ssh) (LR := LR) (LS := LS)
    (hW'.primeIdealOf ⟨f.base u, hUW hu⟩).asIdeal (hU'.primeIdealOf ⟨u, hu⟩).asIdeal

/-- **Stacks 08HV at the identity charts of the site.**  For a morphism `g : U ⟶ W` of the big
fppf site of `S`, a geometric point `x̄` of the algebraic space `U` represents, affine opens
`W' ⊆ W` and `U' ⊆ g ⁻¹ᵁ W'` with the point of the chart of `U` in `U'`, the induced map
`Γ(U, U') ⊗_{Γ(W, W')} 𝒪^{sh}_{W, w̄} → 𝒪^{sh}_{U, x̄}` of the two models is flat. -/
theorem flat_tensorProduct_lift_yonedaChart {U₀ W₀ : BigFppfOver B S hS} (g : U₀ ⟶ W₀)
    (x : GeometricPoint B S hS (yoneda.obj U₀))
    {U' : (siteScheme B S hS U₀).Opens} (hU' : IsAffineOpen U')
    {W' : (siteScheme B S hS W₀).Opens} (hW' : IsAffineOpen W')
    (hUW : U' ≤ (BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ W')
    (hx : chartPoint B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ x) ∈ U')
    [Algebra ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS U₀, U')]
    [Algebra ↥Γ(siteScheme B S hS W₀, W')
      (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map g) x))]
    [Algebra ↥Γ(siteScheme B S hS U₀, U') (yonedaChartSH B S hS U₀ x)]
    [Algebra ↥Γ(siteScheme B S hS W₀, W') (yonedaChartSH B S hS U₀ x)]
    [IsScalarTower ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS U₀, U')
      (yonedaChartSH B S hS U₀ x)]
    [Algebra (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map g) x))
      (yonedaChartSH B S hS U₀ x)]
    [IsScalarTower ↥Γ(siteScheme B S hS W₀, W')
      (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map g) x))
      (yonedaChartSH B S hS U₀ x)]
    [IsLocalHom (algebraMap (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map g) x))
      (yonedaChartSH B S hS U₀ x))]
    (halg : ∀ r, algebraMap ↥Γ(siteScheme B S hS W₀, W')
        ↥Γ(siteScheme B S hS U₀, U') r =
      (((BigFppfOver.toScheme B S hS).map g).appLE W' U' hUW).hom r)
    (hRsh : ∀ r, algebraMap ↥Γ(siteScheme B S hS W₀, W')
        (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map g) x)) r =
      algebraMap ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map g) x))
        (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map g) x))
        (((siteScheme B S hS W₀).presheaf.germ W' _ (hUW hx)).hom r))
    (hSsh : ∀ a, algebraMap ↥Γ(siteScheme B S hS U₀, U') (yonedaChartSH B S hS U₀ x) a =
      algebraMap ↥(yonedaChartLocalRing B S hS U₀ x) (yonedaChartSH B S hS U₀ x)
        (((siteScheme B S hS U₀).presheaf.germ U' _ hx).hom a)) :
    RingHom.Flat (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS U₀, U')
        (yonedaChartSH B S hS U₀ x))
      (IsScalarTower.toAlgHom ↥Γ(siteScheme B S hS W₀, W')
        (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map g) x))
        (yonedaChartSH B S hS U₀ x)) fun _ _ => Commute.all _ _).toRingHom := by
  let : Algebra ↥Γ(siteScheme B S hS W₀, W')
      ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map g) x)) :=
    ((siteScheme B S hS W₀).presheaf.germ W'
      (((BigFppfOver.toScheme B S hS).map g).base
        (chartPoint B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ x)))
      (hUW hx)).hom.toAlgebra
  let : Algebra ↥Γ(siteScheme B S hS U₀, U') ↥(yonedaChartLocalRing B S hS U₀ x) :=
    ((siteScheme B S hS U₀).presheaf.germ U'
      (chartPoint B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ x))
      hx).hom.toAlgebra
  let : Algebra ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map g) x))
      ↥(yonedaChartLocalRing B S hS U₀ x) :=
    (((BigFppfOver.toScheme B S hS).map g).stalkMap
      (chartPoint B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ x))).hom.toAlgebra
  let : Algebra ↥Γ(siteScheme B S hS W₀, W') ↥(yonedaChartLocalRing B S hS U₀ x) :=
    ((algebraMap ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map g) x))
        ↥(yonedaChartLocalRing B S hS U₀ x)).comp
      (algebraMap ↥Γ(siteScheme B S hS W₀, W')
        ↥(yonedaChartLocalRing B S hS W₀
          (geometricPointMap (yoneda.map g) x)))).toAlgebra
  have : IsScalarTower ↥Γ(siteScheme B S hS W₀, W')
      ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map g) x))
      ↥(yonedaChartLocalRing B S hS U₀ x) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ↥Γ(siteScheme B S hS W₀, W') ↥Γ(siteScheme B S hS U₀, U')
      ↥(yonedaChartLocalRing B S hS U₀ x) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (germ_stalkMap_appLE_apply ((BigFppfOver.toScheme B S hS).map g) hUW hx r).trans
        (congrArg ((siteScheme B S hS U₀).presheaf.germ U' _ hx).hom (halg r)).symm
  have : IsLocalization.AtPrime
      ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map g) x))
      (hW'.primeIdealOf ⟨((BigFppfOver.toScheme B S hS).map g).base
        (chartPoint B S hS (yoneda.obj U₀) (yonedaIdentityNeighborhood U₀ x)),
        hUW hx⟩).asIdeal :=
    hW'.isLocalization_stalk ⟨_, hUW hx⟩
  have : IsLocalization.AtPrime ↥(yonedaChartLocalRing B S hS U₀ x)
      (hU'.primeIdealOf ⟨chartPoint B S hS (yoneda.obj U₀)
        (yonedaIdentityNeighborhood U₀ x), hx⟩).asIdeal :=
    hU'.isLocalization_stalk ⟨_, hx⟩
  let : Algebra ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map g) x))
      (yonedaChartSH B S hS U₀ x) :=
    ((algebraMap ↥(yonedaChartLocalRing B S hS U₀ x)
        (yonedaChartSH B S hS U₀ x)).comp
      (algebraMap ↥(yonedaChartLocalRing B S hS W₀
          (geometricPointMap (yoneda.map g) x))
        ↥(yonedaChartLocalRing B S hS U₀ x))).toAlgebra
  have : IsScalarTower
      ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map g) x))
      ↥(yonedaChartLocalRing B S hS U₀ x) (yonedaChartSH B S hS U₀ x) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ↥Γ(siteScheme B S hS W₀, W')
      ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map g) x))
      (yonedaChartSH B S hS U₀ x) :=
    IsScalarTower.of_algebraMap_eq fun r =>
      ((IsScalarTower.algebraMap_apply ↥Γ(siteScheme B S hS W₀, W')
          ↥Γ(siteScheme B S hS U₀, U') (yonedaChartSH B S hS U₀ x) r).trans
        (hSsh (algebraMap ↥Γ(siteScheme B S hS W₀, W')
          ↥Γ(siteScheme B S hS U₀, U') r))).trans
        (congrArg (algebraMap ↥(yonedaChartLocalRing B S hS U₀ x)
            (yonedaChartSH B S hS U₀ x))
          ((congrArg ((siteScheme B S hS U₀).presheaf.germ U' _ hx).hom (halg r)).trans
            (germ_stalkMap_appLE_apply ((BigFppfOver.toScheme B S hS).map g) hUW hx r).symm))
  have : IsScalarTower ↥Γ(siteScheme B S hS U₀, U')
      ↥(yonedaChartLocalRing B S hS U₀ x) (yonedaChartSH B S hS U₀ x) :=
    IsScalarTower.of_algebraMap_eq hSsh
  have : IsScalarTower ↥Γ(siteScheme B S hS W₀, W')
      ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map g) x))
      (yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map g) x)) :=
    IsScalarTower.of_algebraMap_eq hRsh
  exact flat_tensorProduct_lift_chart ((BigFppfOver.toScheme B S hS).map g) hW' hU' hUW hx
    (Rp := ↥(yonedaChartLocalRing B S hS W₀ (geometricPointMap (yoneda.map g) x)))
    (Sq := ↥(yonedaChartLocalRing B S hS U₀ x))
    (Rsh := yonedaChartSH B S hS W₀ (geometricPointMap (yoneda.map g) x))
    (Ssh := yonedaChartSH B S hS U₀ x) halg
    (LR := separableClosure (ResidueField ↥(yonedaChartLocalRing B S hS W₀
        (geometricPointMap (yoneda.map g) x)))
      (chartGeometricPoint (yonedaIdentityNeighborhood W₀
        (geometricPointMap (yoneda.map g) x))).residueField)
    (LS := separableClosure (ResidueField ↥(yonedaChartLocalRing B S hS U₀ x))
      (chartGeometricPoint (yonedaIdentityNeighborhood U₀ x)).residueField)

/-- **The model is flat over the ring of sections of an affine open through the point.**  The map
`Γ(W, W') → 𝒪^{sh}_{W, z̄}` is flat: it factors as the localization of `Γ(W, W')` at the point
of the chart followed by a strict henselization, and both are flat. -/
theorem flat_algebraMap_yonedaChartSH (W₀ : BigFppfOver B S hS)
    (z : GeometricPoint B S hS (yoneda.obj W₀))
    {W' : (siteScheme B S hS W₀).Opens} (hW' : IsAffineOpen W')
    (hz : chartPoint B S hS (yoneda.obj W₀) (yonedaIdentityNeighborhood W₀ z) ∈ W')
    [Algebra ↥Γ(siteScheme B S hS W₀, W') (yonedaChartSH B S hS W₀ z)]
    (hRsh : ∀ r, algebraMap ↥Γ(siteScheme B S hS W₀, W') (yonedaChartSH B S hS W₀ z) r =
      algebraMap ↥(yonedaChartLocalRing B S hS W₀ z) (yonedaChartSH B S hS W₀ z)
        (((siteScheme B S hS W₀).presheaf.germ W' _ hz).hom r)) :
    RingHom.Flat (algebraMap ↥Γ(siteScheme B S hS W₀, W')
      (yonedaChartSH B S hS W₀ z)) := by
  let : Algebra ↥Γ(siteScheme B S hS W₀, W') ↥(yonedaChartLocalRing B S hS W₀ z) :=
    ((siteScheme B S hS W₀).presheaf.germ W'
      (chartPoint B S hS (yoneda.obj W₀) (yonedaIdentityNeighborhood W₀ z))
      hz).hom.toAlgebra
  have : IsLocalization.AtPrime ↥(yonedaChartLocalRing B S hS W₀ z)
      (hW'.primeIdealOf ⟨chartPoint B S hS (yoneda.obj W₀)
        (yonedaIdentityNeighborhood W₀ z), hz⟩).asIdeal :=
    hW'.isLocalization_stalk ⟨_, hz⟩
  have : IsScalarTower ↥Γ(siteScheme B S hS W₀, W')
      ↥(yonedaChartLocalRing B S hS W₀ z) (yonedaChartSH B S hS W₀ z) :=
    IsScalarTower.of_algebraMap_eq hRsh
  have : Module.Flat ↥Γ(siteScheme B S hS W₀, W')
      ↥(yonedaChartLocalRing B S hS W₀ z) :=
    IsLocalization.flat _ (hW'.primeIdealOf ⟨chartPoint B S hS (yoneda.obj W₀)
      (yonedaIdentityNeighborhood W₀ z), hz⟩).asIdeal.primeCompl
  have : Module.Flat ↥(yonedaChartLocalRing B S hS W₀ z) (yonedaChartSH B S hS W₀ z) :=
    IsLocalRing.IsHenselization.flat
      (L := separableClosure (ResidueField ↥(yonedaChartLocalRing B S hS W₀ z))
        (chartGeometricPoint (yonedaIdentityNeighborhood W₀ z)).residueField)
  exact RingHom.flat_algebraMap_iff.mpr
    (Module.Flat.trans ↥Γ(siteScheme B S hS W₀, W')
      ↥(yonedaChartLocalRing B S hS W₀ z) (yonedaChartSH B S hS W₀ z))

end AlgebraicGeometry.Space

end
