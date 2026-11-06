module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceContainmentConstructible
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceFibreChartScheme
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.Henselization
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionQuasicoherent

/-!
# Weak association descends from the étale local ring without a finiteness hypothesis

Let `X` be an algebraic space over a scheme `S`, let `F` be a quasi-coherent `𝒪_X`-module and
let `φ : U → X` be an étale neighbourhood of a geometric point `x̄` whose chart `U` is a scheme
carrying the point `u`.  The geometric stalk is the base change of the Zariski stalk along the
faithfully flat local map `𝒪_{U, u} → 𝒪_{X, x̄}` (Stacks 05VP), so weak association of the
maximal ideal passes from `U` to `X` unconditionally.  Passing it back is flat descent, and
`StacksFrontier/AlgebraicGeometry/Spaces/WeaklyAssociatedTFAE.lean` has it only for a prime whose
contraction is finitely generated, which on a general chart is an extra hypothesis.

That hypothesis is not needed.  The étale local ring is a *strict henselization* of
`𝒪_{U, u}` (Stacks 04KF), and descent of weak association along a strict henselization is
Stacks 0CTU, `AlgebraicGeometry.weaklyAssociated_tfae_henselization`, which carries no
finiteness condition.  What it asks for instead is that the Zariski restriction of `F` to the
chart be a quasi-coherent `𝒪_U`-module — the Zariski clause of Stacks 03DX.  This file makes
that trade, and then discharges the traded hypothesis outright on a *represented* algebraic
space, where the Zariski restriction along the identity chart is quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme` at the identity chart.

## Main results

* `Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_comap_of_ringEquiv`: weak association
  transports along a ring isomorphism carrying one module to another.
* `IsLocalRing.HenselizationTower.isHenselization_residueField` and
  `IsLocalRing.HenselizationTower.isSepClosure_residueField`: the strict henselization in a
  chosen tower is a henselization of the base with residue field its own residue field.  This
  is the shape in which Stacks 0CTU consumes a strict henselization.
* `AlgebraicGeometry.isWeaklyAssociatedPoint_of_isWeaklyAssociatedPrime_strictHenselization`:
  the descent clause of Stacks 0CTU over a chosen henselization tower.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime_of_isQuasicoherent`
  and `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_iff_of_isQuasicoherent`:
  **Stacks 0CTW, (1) ⟺ (3)** with the finite-generation hypothesis of
  `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_iff` replaced by
  quasi-coherence of the Zariski chart restriction.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint_of_isQuasicoherent`:
  the same trade in **Stacks 0CTW, (1) ⟺ (2) at a point of a chart scheme**.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_idEtaleChart_iff`:
  **Stacks 0CTW on a represented algebraic space, with no hypothesis beyond quasi-coherence of
  the module itself.**

## Implementation notes

Stacks 0CTU is stated for a ring `Rsh` in the universe of the scheme, and the étale local ring
of an algebraic space lives one universe up, so it cannot be fed to Stacks 0CTU directly.  The
tower `AlgebraicGeometry.Space.chartHenselizationTower` supplies a strict henselization in the
right universe together with the isomorphism
`AlgebraicGeometry.Space.chartStrictHenselizationEquiv` to the étale local ring, which is an
isomorphism of algebras over `𝒪_{U, u}` by construction; the weak-association statement is
carried across it by
`Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_comap_of_ringEquiv` together with
`CategoryTheory.TensorProduct.congr` on the base change.  The contraction of the maximal ideal
along an isomorphism is maximal, hence the maximal ideal, which is what turns the `comap` of
that transport into the statement Stacks 0CTU wants.

Stacks 0CTU asks for `IsLocalRing.IsHenselization R (ResidueField Rsh) Rsh`, where a chosen
tower provides `IsLocalRing.IsHenselization R κsep Rsh` for its prescribed separable closure
`κsep`.  The two are reindexed along `HenselizationTower.strictHenselizationResidueEquiv`:
the `henselian` and `ind_etale` fields do not mention the residue field at all, and the residue
identification becomes the identity once the extension `κ(R) ⊆ ResidueField Rsh` is *defined*
as the composite of `κ(R) ⊆ κsep` with that isomorphism.  `IsSepClosure` transports along the
same isomorphism, by `IsSepClosed.of_ringEquiv` on one field and
`Algebra.IsSeparable.of_algHom` on the other.

Two module structures on the Zariski stalk of the chart restriction are in play, Mathlib's
colimit one and the one Stacks 01CB builds from germ representatives.  They are equal but not
definitionally equal across module boundaries, and which one instance search finds depends on
whether the local ring is spelled `AlgebraicGeometry.Space.chartLocalRing` or as the stalk of
the chart's structure sheaf.  Mathlib's is the one both Stacks 0CTU and
`AlgebraicGeometry.Space.chartZariskiModuleStalkStalkEquiv` are stated over, so it is pinned by
hand and the stalk spelling is used throughout.

## References

* [Stacks Project, Tag 0CTW](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 0CTU](https://stacks.math.columbia.edu/tag/0CTU)
* [Stacks Project, Tag 0CTX](https://stacks.math.columbia.edu/tag/0CTX)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v

namespace Stacks.WeaklyAssociatedPrimes

/-- Weak association transports along a ring isomorphism carrying one module to another: if
`e : A ≃+* A'` and `φ : M ≃+ M'` are compatible, a weakly associated prime of `M'` over `A'`
contracts to a weakly associated prime of `M` over `A`. -/
theorem isWeaklyAssociatedPrime_comap_of_ringEquiv {A A' M M' : Type*} [CommRing A] [CommRing A']
    [AddCommGroup M] [AddCommGroup M'] [Module A M] [Module A' M'] (e : A ≃+* A')
    (φ : M ≃+ M') (hφ : ∀ (a : A) (m : M), φ (a • m) = e a • φ m) {p : Ideal A'}
    (h : IsWeaklyAssociatedPrime A' M' p) :
    IsWeaklyAssociatedPrime A M (p.comap (e : A →+* A')) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨φ.symm m, ?_⟩
  have hI : (A ∙ φ.symm m).annihilator = ((A' ∙ m).annihilator).comap (e : A →+* A') := by
    ext a
    simp only [Submodule.mem_annihilator_span_singleton, Ideal.mem_comap, RingHom.coe_coe]
    have hkey : φ (a • φ.symm m) = e a • m := by
      rw [hφ a (φ.symm m), φ.apply_symm_apply]
    rw [← hkey, φ.map_eq_zero_iff]
  rw [hI, Ideal.comap_minimalPrimes_eq_of_surjective (f := (e : A →+* A')) e.surjective]
  exact ⟨p, hm, rfl⟩

end Stacks.WeaklyAssociatedPrimes

namespace IsLocalRing.HenselizationTower

variable {R : Type u} [CommRing R] [IsLocalRing R] {ksep : Type v} [Field ksep]
  [Algebra (ResidueField R) ksep] [IsSepClosure (ResidueField R) ksep]

/-- The residue field of the strict henselization in a chosen tower, read as an extension of
the residue field of the base through the tower's identification of it with `ksep`. -/
@[instance_reducible]
noncomputable def residueAlgebra (T : HenselizationTower R ksep) :
    Algebra (ResidueField R) (ResidueField T.strictHenselization) :=
  (T.strictHenselizationResidueEquiv.toRingHom.comp
    (algebraMap (ResidueField R) ksep)).toAlgebra

/-- The residue field of the strict henselization in a chosen tower is a separable closure of
the residue field of the base. -/
theorem isSepClosure_residueField (T : HenselizationTower R ksep) :
    letI := T.residueAlgebra
    IsSepClosure (ResidueField R) (ResidueField T.strictHenselization) := by
  have : IsSepClosed ksep := IsSepClosure.sep_closed (ResidueField R)
  let := T.residueAlgebra
  refine ⟨IsSepClosed.of_ringEquiv T.strictHenselizationResidueEquiv.symm, ?_⟩
  exact Algebra.IsSeparable.of_algHom _ _
    (show ResidueField T.strictHenselization ≃ₐ[ResidueField R] ksep from
      { T.strictHenselizationResidueEquiv.symm with
        commutes' := fun r => T.strictHenselizationResidueEquiv.symm_apply_apply
          (algebraMap (ResidueField R) ksep r) }).toAlgHom

/-- The strict henselization in a chosen tower is a henselization of the base with residue
field its own residue field.  This is the shape in which Stacks 0CTU consumes it. -/
theorem isHenselization_residueField (T : HenselizationTower R ksep) :
    letI := T.residueAlgebra
    IsHenselization R (ResidueField T.strictHenselization) T.strictHenselization := by
  have hH : IsHenselization R ksep T.strictHenselization := inferInstance
  let := T.residueAlgebra
  exact
    { henselian := hH.henselian
      ind_etale := hH.ind_etale
      exists_residueFieldEquiv :=
        ⟨RingEquiv.refl _, fun r => T.strictHenselizationResidueEquiv_residue r⟩ }

end IsLocalRing.HenselizationTower

namespace AlgebraicGeometry

/-- **The descent clause of Stacks 0CTU, over a chosen henselization tower.** If the maximal
ideal of the strict henselization of `𝒪_{X, x}` in a chosen tower is weakly associated to the
base change of the stalk of `F` there, then `x` is weakly associated to `F`.

The tag is carried by `AlgebraicGeometry.weaklyAssociated_tfae_henselization`; this is that
statement with the strict henselization presented by a tower. -/
theorem isWeaklyAssociatedPoint_of_isWeaklyAssociatedPrime_strictHenselization
    {X : Scheme.{u}} (F : X.Modules) [SheafOfModules.IsQuasicoherent F] (x : X)
    {ksep : Type v} [Field ksep] [Algebra (ResidueField ↥(X.presheaf.stalk x)) ksep]
    [IsSepClosure (ResidueField ↥(X.presheaf.stalk x)) ksep]
    (T : IsLocalRing.HenselizationTower ↥(X.presheaf.stalk x) ksep)
    (h : IsWeaklyAssociatedPrime T.strictHenselization
      (TensorProduct ↥(X.presheaf.stalk x) T.strictHenselization
        ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x))
      (maximalIdeal T.strictHenselization)) :
    Stacks.Divisors.IsWeaklyAssociatedPoint F x := by
  let := T.residueAlgebra
  have := T.isSepClosure_residueField
  have := T.isHenselization_residueField
  exact ((weaklyAssociated_tfae_henselization F x (Rh := T.henselization)
    (Rsh := T.strictHenselization)).out 4 1).mp h

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z : AlgebraicSpaces B S hS} {xbar : GeometricPoint B S hS Z.1}

/-- **Stacks 0CTW, (3) ⟹ (1), granted quasi-coherence of the Zariski chart restriction.** If
the maximal ideal of `𝒪_{X, x̄}` is a weakly associated prime of the geometric stalk `F_{x̄}`,
then the point of the chart under `x̄` is weakly associated to the restriction of `F` there, in
the Zariski sense of Stacks 056L.

Unlike `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime`
this carries no finite-generation hypothesis on the maximal ideal of the chart's local ring:
the descent is Stacks 0CTU along the strict henselization of Stacks 04KF, which asks instead
that the Zariski restriction be a quasi-coherent `𝒪_U`-module. -/
theorem isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime_of_isQuasicoherent
    (W : SmallEtaleNeighborhood xbar) (G : Modules.{u, u} B S hS Z.1 Z.2)
    [G.IsQuasicoherentOnSite]
    (hqc : (restrictToChart B S hS Z.2 G W.chart).IsQuasicoherent)
    (h : letI : IsLocalRing (etaleLocalRing B S hS Z.1 xbar) :=
          isLocalRing_etaleLocalRing B S hS Z.1 Z.2 xbar
        letI : Module (etaleLocalRing B S hS Z.1 xbar)
            (geometricModuleStalk B S hS Z xbar G) :=
          (geometricModuleStalk B S hS Z xbar G).isModule
        IsWeaklyAssociatedPrime (etaleLocalRing B S hS Z.1 xbar)
          (geometricModuleStalk B S hS Z xbar G)
          (IsLocalRing.maximalIdeal (etaleLocalRing B S hS Z.1 xbar))) :
    Stacks.Divisors.IsWeaklyAssociatedPoint (restrictToChart B S hS Z.2 G W.chart)
      (chartPoint B S hS Z.1 W) := by
  have : IsLocalRing (etaleLocalRing B S hS Z.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS Z.1 Z.2 xbar
  have := isIso_chartStalkTensorComparison B S hS Z.2 W G
  have := hqc
  let : Module ↥((chartScheme W.chart).presheaf.stalk (chartPoint B S hS Z.1 W))
      ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (chartRestrictionPresheafOfModules B S hS Z.2 W G).presheaf
        (chartPoint B S hS Z.1 W)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (chartRestrictionPresheafOfModules B S hS Z.2 W G) (chartPoint B S hS Z.1 W)
  let : Algebra ↥((chartScheme W.chart).presheaf.stalk (chartPoint B S hS Z.1 W))
      ↥(etaleLocalRing B S hS Z.1 xbar) :=
    (chartLocalRingToEtaleLocalRing B S hS Z.1 Z.2 W).toAlgebra
  let : IsScalarTower ↥((chartScheme W.chart).presheaf.stalk (chartPoint B S hS Z.1 W))
      ↥(etaleLocalRing B S hS Z.1 xbar) ↥(etaleLocalRing B S hS Z.1 xbar) :=
    IsScalarTower.right
  have h2 := IsWeaklyAssociatedPrime.of_linearEquiv
    (asIso (chartStalkTensorComparison B S hS Z.2 W G)).toLinearEquiv.symm h
  have h3 := (LinearEquiv.isWeaklyAssociatedPrime_iff
    (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl ↥(etaleLocalRing B S hS Z.1 xbar)
        ↥(etaleLocalRing B S hS Z.1 xbar))
      (chartZariskiModuleStalkStalkEquiv B S hS Z.2 W G))
    (IsLocalRing.maximalIdeal ↥(etaleLocalRing B S hS Z.1 xbar))).mp h2
  let algk : Algebra (ResidueField ↥(chartLocalRing B S hS Z.1 W))
      ↥(separableClosure (ResidueField ↥(chartLocalRing B S hS Z.1 W))
        (chartGeometricPoint W).residueField) := inferInstance
  have sepk : IsSepClosure (ResidueField ↥(chartLocalRing B S hS Z.1 W))
      ↥(separableClosure (ResidueField ↥(chartLocalRing B S hS Z.1 W))
        (chartGeometricPoint W).residueField) := inferInstance
  refine @isWeaklyAssociatedPoint_of_isWeaklyAssociatedPrime_strictHenselization
    (chartScheme W.chart) (restrictToChart B S hS Z.2 G W.chart) hqc (chartPoint B S hS Z.1 W)
    ↥(separableClosure (ResidueField ↥(chartLocalRing B S hS Z.1 W))
      (chartGeometricPoint W).residueField) inferInstance algk sepk
    (chartHenselizationTower B S hS Z.1 W) ?_
  let e : (chartHenselizationTower B S hS Z.1 W).strictHenselization ≃+*
      ↥(etaleLocalRing B S hS Z.1 xbar) := chartStrictHenselizationEquiv B S hS Z.1 Z.2 W
  let e' : (chartHenselizationTower B S hS Z.1 W).strictHenselization ≃ₐ[
      ↥((chartScheme W.chart).presheaf.stalk (chartPoint B S hS Z.1 W))]
      ↥(etaleLocalRing B S hS Z.1 xbar) :=
    { e with commutes' := fun _ => rfl }
  let φ := TensorProduct.congr e'.toLinearEquiv
    (LinearEquiv.refl ↥((chartScheme W.chart).presheaf.stalk (chartPoint B S hS Z.1 W))
      ↥(TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (chartRestrictionPresheafOfModules B S hS Z.2 W G).presheaf (chartPoint B S hS Z.1 W)))
  have hφ : ∀ a z, φ.toAddEquiv (a • z) = e a • φ.toAddEquiv z := by
    intro a z
    induction z using TensorProduct.inductionOn with
    | tmul b m =>
        rw [TensorProduct.smul_tmul']
        show φ ((a * b) ⊗ₜ m) = e a • φ (b ⊗ₜ m)
        show (e (a * b)) ⊗ₜ m = e a • ((e b) ⊗ₜ m)
        rw [map_mul, TensorProduct.smul_tmul', smul_eq_mul]
    | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
  have h4 := Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_comap_of_ringEquiv e
    φ.toAddEquiv hφ h3
  have hmax : (IsLocalRing.maximalIdeal ↥(etaleLocalRing B S hS Z.1 xbar)).comap
      (e : (chartHenselizationTower B S hS Z.1 W).strictHenselization →+*
        ↥(etaleLocalRing B S hS Z.1 xbar)) =
      IsLocalRing.maximalIdeal (chartHenselizationTower B S hS Z.1 W).strictHenselization :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective
        (f := (e : (chartHenselizationTower B S hS Z.1 W).strictHenselization →+*
          ↥(etaleLocalRing B S hS Z.1 xbar)))
        e.surjective)
  rwa [hmax] at h4

/-- **Stacks 0CTW, (1) ⟺ (3), granted quasi-coherence of the Zariski chart restriction.** The
point of an étale scheme chart under a geometric point `x̄` is weakly associated to the
restriction of `F` there exactly when the maximal ideal of `𝒪_{X, x̄}` is a weakly associated
prime of the geometric stalk `F_{x̄}`. -/
theorem isWeaklyAssociatedPoint_restrictToChart_iff_of_isQuasicoherent
    (W : SmallEtaleNeighborhood xbar) (G : Modules.{u, u} B S hS Z.1 Z.2)
    [G.IsQuasicoherentOnSite]
    (hqc : (restrictToChart B S hS Z.2 G W.chart).IsQuasicoherent) :
    Stacks.Divisors.IsWeaklyAssociatedPoint (restrictToChart B S hS Z.2 G W.chart)
        (chartPoint B S hS Z.1 W) ↔
      letI : IsLocalRing (etaleLocalRing B S hS Z.1 xbar) :=
        isLocalRing_etaleLocalRing B S hS Z.1 Z.2 xbar
      letI : Module (etaleLocalRing B S hS Z.1 xbar)
          (geometricModuleStalk B S hS Z xbar G) :=
        (geometricModuleStalk B S hS Z xbar G).isModule
      IsWeaklyAssociatedPrime (etaleLocalRing B S hS Z.1 xbar)
        (geometricModuleStalk B S hS Z xbar G)
        (IsLocalRing.maximalIdeal (etaleLocalRing B S hS Z.1 xbar)) :=
  ⟨isWeaklyAssociatedPrime_maximalIdeal_geometricModuleStalk_of_chart B S hS Z W G,
    isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime_of_isQuasicoherent
      B S hS W G hqc⟩

/-- **Stacks 0CTW, conditions (1) and (2) at a point of a chart scheme, granted quasi-coherence
of the Zariski chart restriction.** A point of an étale scheme chart of an algebraic space is
weakly associated to the restriction of a quasi-coherent module there, in the Zariski sense of
Stacks 056L, exactly when the point of the space it lies over is weakly associated to the
module in the sense of Stacks 0CTX.

This is
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint`
with its finite-generation hypothesis traded for quasi-coherence of the restriction. -/
theorem isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint_of_isQuasicoherent
    (F : Modules.{u, u} B S hS Z.1 Z.2) [F.IsQuasicoherentOnSite]
    (W : SmallEtale B S hS Z.1) (w : chartScheme W)
    (hqc : (restrictToChart B S hS Z.2 F W).IsQuasicoherent) :
    Stacks.Divisors.IsWeaklyAssociatedPoint (restrictToChart B S hS Z.2 F W) w ↔
      IsWeaklyAssociatedPoint B S hS Z F (chartSchemeToPoints B S hS Z.1 W w) := by
  set W₀ := (SmallEtale.toOver B S hS Z.1).obj W
  have hchart : chartSchemeToPoints B S hS Z.1 W w =
      pointsMap B S hS (yoneda.obj W₀) W.obj.hom
        ((pointsEquivScheme B S hS W₀).symm w) :=
    chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS Z.1 W w
  have hchartPoint : ∀ ybar : GeometricPoint B S hS (yoneda.obj W₀),
      ybar.image = (pointsEquivScheme B S hS W₀).symm w →
      chartPoint B S hS Z.1 (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS Z W ybar) = w :=
    fun ybar hy => (congrArg _ hy).trans ((pointsEquivScheme B S hS W₀).apply_symm_apply w)
  constructor
  · intro h
    obtain ⟨ybar, hybar⟩ :=
      exists_geometricRepresentative B S hS (yoneda.obj W₀) ((pointsEquivScheme B S hS W₀).symm w)
    obtain rfl := hchartPoint ybar hybar
    refine isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_restrictToChart B S hS Z F _ ?_
      (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS Z W ybar) h
    rw [hchart]
    exact (geometricPointMap_image W.obj.hom ybar).trans (congrArg _ hybar)
  · rintro ⟨xbar, hlies, h3⟩
    obtain ⟨ybar, hyb, hval⟩ := exists_geometricPoint_lift_of_isEtale B S hS
      (isAlgebraicSpace_yoneda B S hS W₀) Z.2 W.obj.hom (isEtale_chartToSpace B S hS Z W)
      xbar ((pointsEquivScheme B S hS W₀).symm w) (by rw [← hchart]; exact hlies.symm)
    have hxy : geometricPointMap W.obj.hom ybar = xbar := Subtype.ext hval
    obtain rfl := hchartPoint ybar hyb
    exact isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime_of_isQuasicoherent
      B S hS (SmallEtaleNeighborhood.ofChartGeometricPoint B S hS Z W ybar) F hqc (hxy ▸ h3)

/-- **Stacks 0CTW on a represented algebraic space, unconditionally.** Let `T` be a scheme of
the site, let `G` be a quasi-coherent `𝒪`-module on the algebraic space `T` represents and let
`t` be a point of `T`.  Then `t` is weakly associated to the restriction of `G` along the
identity chart, in the Zariski sense of Stacks 056L, exactly when the point of the represented
space it names is weakly associated to `G` in the sense of Stacks 0CTX.

No finite-generation hypothesis on the local ring of `T` at `t` is needed: the quasi-coherence
it is traded for is a theorem on a represented space, by
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChartScheme` at the identity chart, read through
`AlgebraicGeometry.Space.isQuasicoherent_restrictToChart_iff`. -/
theorem isWeaklyAssociatedPoint_restrictToChart_idEtaleChart_iff (T : BigFppfOver B S hS)
    (G : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    [G.IsQuasicoherentOnSite] (t : (BigFppfOver.toScheme B S hS).obj T) :
    Stacks.Divisors.IsWeaklyAssociatedPoint
        (restrictToChart B S hS (isAlgebraicSpace_yoneda B S hS T) G
          (idEtaleChart B S hS T)) t ↔
      IsWeaklyAssociatedPoint B S hS ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ G
        ((pointsEquivScheme B S hS T).symm t) := by
  have hqc : (restrictToChart B S hS (isAlgebraicSpace_yoneda B S hS T) G
      (idEtaleChart B S hS T)).IsQuasicoherent :=
    (isQuasicoherent_restrictToChart_iff B S hS (isAlgebraicSpace_yoneda B S hS T) G
      (idEtaleChart B S hS T)).2
      (isQuasicoherent_restrictToChartScheme B S hS (schemeSpace T) G
        (inferInstanceAs (SheafOfModules.IsQuasicoherentOnSite G)) (idEtaleChart B S hS T))
  rw [← chartSchemeToPoints_idEtaleChart B S hS T t]
  exact isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPoint_of_isQuasicoherent
    B S hS (Z := ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩) G (idEtaleChart B S hS T) t hqc

end Space

end AlgebraicGeometry

end
