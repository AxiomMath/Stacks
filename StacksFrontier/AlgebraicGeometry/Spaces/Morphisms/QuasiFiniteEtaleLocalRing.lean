module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart

/-!
# Étale local rings at a point where a morphism is quasi-finite

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, and let `x̄` be a geometric point of `X` at whose image point `f` is quasi-finite.  Then
the canonical homomorphism of étale local rings `𝒪_{Y, f(x̄)} → 𝒪_{X, x̄}` is finite.

## Main results

* `AlgebraicGeometry.Space.finite_etaleLocalRingMap_of_isQuasiFiniteAt`: the statement above.

## Implementation notes

The argument is the one for a finite morphism,
`AlgebraicGeometry.Space.finite_etaleLocalRingMap`, with the finiteness of the chart morphism
replaced by finite type and quasi-finiteness at the selected point.  On a commuting square of
pointed étale charts with affine chart schemes the two étale local rings are the strict
henselizations of the local rings of the charts at the selected points (Stacks 04KF), and the
canonical homomorphism agrees with the map of global sections on germs; the ring map of global
sections is of finite type and quasi-finite at the prime of the selected point, so Stacks 05WR,
`IsLocalRing.IsHenselization.finite_and_isPurelyInseparable_of_quasiFiniteAt`, applies.

## References

* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05WR](https://stacks.math.columbia.edu/tag/05WR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-- A henselization with prescribed residue extension `L` is also one with its own residue field,
and the latter is again a separable closure. -/
private theorem isHenselization_residueField_of_isHenselization {R L Rh : Type u} [CommRing R]
    [IsLocalRing R] [Field L] [Algebra (ResidueField R) L] [IsSepClosure (ResidueField R) L]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsLocalHom (algebraMap R Rh)] [IsHenselization R L Rh] :
    IsHenselization R (ResidueField Rh) Rh ∧ IsSepClosure (ResidueField R) (ResidueField Rh) := by
  obtain ⟨k, hk, hsep, he⟩ :=
    IsHenselization.exists_residueFieldAlgebra (R := R) (L := L) (Rh := Rh)
  have hk_eq : k = ResidueField.instAlgebra := by
    refine Algebra.algebra_ext _ _ fun a => ?_
    obtain ⟨r, rfl⟩ := residue_surjective a
    exact (he r).trans (ResidueField.algebraMap_residue (S := Rh) r).symm
  subst hk_eq
  exact ⟨hk, hsep inferInstance⟩

/-- **The map of strict henselizations along a ring map of finite type which is quasi-finite at
a prime is finite.** This is Stacks 05WR, read on chosen henselization towers. -/
theorem finite_of_henselizationTower_square_of_quasiFiniteAt
    {R A Rp Aq K L : Type u} [CommRing R] [CommRing A] [CommRing Rp] [CommRing Aq]
    [IsLocalRing Rp] [IsLocalRing Aq] [Field K] [Field L]
    [Algebra R A] [Algebra.FiniteType R A] [Algebra R Rp] [Algebra A Aq]
    (p : Ideal R) (q : Ideal A) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    [Algebra.QuasiFiniteAt R q]
    [IsLocalization.AtPrime Rp p] [IsLocalization.AtPrime Aq q]
    [Algebra (ResidueField Rp) K] [IsSepClosure (ResidueField Rp) K]
    [Algebra (ResidueField Aq) L] [IsSepClosure (ResidueField Aq) L]
    (T : HenselizationTower Rp K) (N : HenselizationTower Aq L)
    (ψ : T.strictHenselization →+* N.strictHenselization) [IsLocalHom ψ]
    (hψ : ∀ r : R, ψ (algebraMap Rp T.strictHenselization (algebraMap R Rp r)) =
      algebraMap Aq N.strictHenselization (algebraMap A Aq (algebraMap R A r))) :
    ψ.Finite := by
  let : Algebra R T.strictHenselization :=
    ((algebraMap Rp T.strictHenselization).comp (algebraMap R Rp)).toAlgebra
  let : Algebra A N.strictHenselization :=
    ((algebraMap Aq N.strictHenselization).comp (algebraMap A Aq)).toAlgebra
  let : Algebra R N.strictHenselization :=
    ((algebraMap A N.strictHenselization).comp (algebraMap R A)).toAlgebra
  let : Algebra T.strictHenselization N.strictHenselization := ψ.toAlgebra
  have : IsScalarTower R Rp T.strictHenselization := .of_algebraMap_eq' rfl
  have : IsScalarTower A Aq N.strictHenselization := .of_algebraMap_eq' rfl
  have : IsScalarTower R A N.strictHenselization := .of_algebraMap_eq' rfl
  have : IsScalarTower R T.strictHenselization N.strictHenselization :=
    .of_algebraMap_eq fun r => (hψ r).symm
  have : IsLocalHom (algebraMap Rp T.strictHenselization) := by
    rw [IsScalarTower.algebraMap_eq Rp T.henselization T.strictHenselization]
    infer_instance
  have : IsLocalHom (algebraMap Aq N.strictHenselization) := by
    rw [IsScalarTower.algebraMap_eq Aq N.henselization N.strictHenselization]
    infer_instance
  obtain ⟨_, _⟩ := isHenselization_residueField_of_isHenselization (R := Rp) (L := K)
    (Rh := T.strictHenselization)
  obtain ⟨_, _⟩ := isHenselization_residueField_of_isHenselization (R := Aq) (L := L)
    (Rh := N.strictHenselization)
  exact (IsHenselization.finite_and_isPurelyInseparable_of_quasiFiniteAt
    (Rp := Rp) (Sq := Aq) (Rsh := T.strictHenselization)
    (Ssh := N.strictHenselization) p q).1

/-- A homomorphism between strict henselizations of the local rings of a morphism of affine
schemes, locally of finite type and quasi-finite at the point, which agrees with the map on germs
of global sections, is finite. -/
theorem finite_of_strictHenselization_germs_of_quasiFiniteAt {Z W : Scheme.{u}} [IsAffine Z]
    [IsAffine W] (k : Z ⟶ W) [LocallyOfFiniteType k] (z : Z) (hkz : k.QuasiFiniteAt z) (w : W)
    (hzw : k z = w) {K L : Type u} [Field K]
    [Algebra (ResidueField (W.presheaf.stalk w)) K]
    [IsSepClosure (ResidueField (W.presheaf.stalk w)) K] [Field L]
    [Algebra (ResidueField (Z.presheaf.stalk z)) L]
    [IsSepClosure (ResidueField (Z.presheaf.stalk z)) L]
    (T : HenselizationTower (W.presheaf.stalk w) K)
    (N : HenselizationTower (Z.presheaf.stalk z) L) {C D : Type*} [CommRing C] [CommRing D]
    (eW : T.strictHenselization ≃+* C) (eZ : N.strictHenselization ≃+* D) (φ : C →+* D)
    (hφ : IsLocalHom φ)
    (hc : ∀ a : Γ(W, ⊤),
      φ (eW (algebraMap _ T.strictHenselization (W.presheaf.germ ⊤ w trivial a))) =
        eZ (algebraMap _ N.strictHenselization
          (Z.presheaf.germ ⊤ z trivial (k.appTop.hom a)))) :
    φ.Finite := by
  subst hzw
  have : IsLocalHom φ := hφ
  set ψ := eZ.symm.toRingHom.comp (φ.comp eW.toRingHom)
  have : IsLocalHom eW.toRingHom := Space.isLocalHom_ringEquiv eW
  have : IsLocalHom eZ.symm.toRingHom := Space.isLocalHom_ringEquiv eZ.symm
  have : IsLocalHom (φ.comp eW.toRingHom) := RingHom.isLocalHom_comp _ _
  have : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
  let : Algebra Γ(W, ⊤) (W.presheaf.stalk (k z)) :=
    TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨k z, trivial⟩ : (⊤ : W.Opens))
  let : Algebra Γ(Z, ⊤) (Z.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk Z.presheaf (⟨z, trivial⟩ : (⊤ : Z.Opens))
  let : Algebra Γ(W, ⊤) Γ(Z, ⊤) := k.appTop.hom.toAlgebra
  have : Algebra.FiniteType Γ(W, ⊤) Γ(Z, ⊤) :=
    HasRingHomProperty.appTop @LocallyOfFiniteType k inferInstance
  set p := ((isAffineOpen_top W).primeIdealOf (⟨k z, trivial⟩ : (⊤ : W.Opens))).asIdeal
  set q := ((isAffineOpen_top Z).primeIdealOf (⟨z, trivial⟩ : (⊤ : Z.Opens))).asIdeal
  have hqf : Algebra.QuasiFiniteAt Γ(W, ⊤) q := by
    have h := hkz.quasiFiniteAt (isAffineOpen_top Z) (isAffineOpen_top W) le_top trivial
    have e : (k.appLE ⊤ ⊤ le_top).hom = k.appTop.hom :=
      congrArg CommRingCat.Hom.hom (Scheme.Hom.app_eq_appLE (U := ⊤) k).symm
    unfold RingHom.QuasiFiniteAt at h
    rwa [e] at h
  have : IsLocalization.AtPrime (W.presheaf.stalk (k z)) p :=
    (isAffineOpen_top W).isLocalization_stalk (⟨k z, trivial⟩ : (⊤ : W.Opens))
  have : IsLocalization.AtPrime (Z.presheaf.stalk z) q :=
    (isAffineOpen_top Z).isLocalization_stalk (⟨z, trivial⟩ : (⊤ : Z.Opens))
  have : q.LiesOver p := by
    constructor
    change p = Ideal.comap k.appTop.hom q
    simpa [p, q, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      (congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE (f := k) ⊤
        (isAffineOpen_top W) ⊤ (isAffineOpen_top Z) le_top (Set.mem_univ z))).symm
  have hψfin : ψ.Finite := by
    refine finite_of_henselizationTower_square_of_quasiFiniteAt p q T N ψ fun r => ?_
    change eZ.symm (φ (eW (algebraMap _ T.strictHenselization
      (W.presheaf.germ ⊤ (k z) trivial r)))) = _
    rw [hc, RingEquiv.symm_apply_apply]
    rfl
  have hfac : eZ.toRingHom.comp (ψ.comp eW.symm.toRingHom) = φ := by
    ext a
    exact (eZ.apply_symm_apply (φ (eW (eW.symm a)))).trans (congrArg φ (eW.apply_symm_apply a))
  rw [← hfac]
  exact (RingHom.Finite.of_surjective _ eZ.surjective).comp
    (hψfin.comp (RingHom.Finite.of_surjective _ eW.symm.surjective))

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The canonical homomorphism of étale local rings at a point where a morphism is
quasi-finite is finite.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite type, and let `x̄` be a geometric point of `X` such that `f` is quasi-finite at
the image point of `x̄`.  Then `𝒪_{Y, f(x̄)} → 𝒪_{X, x̄}` is a finite ring map.

On a commuting square of pointed étale charts with affine chart schemes the chart morphism is
locally of finite type and quasi-finite at the selected point (its fibre dimension there is the
relative dimension of `f`, Stacks 04NL), and the statement is
`AlgebraicGeometry.finite_of_strictHenselization_germs_of_quasiFiniteAt`. -/
theorem finite_etaleLocalRingMap_of_isQuasiFiniteAt (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hlft : IsLocallyOfFiniteType B S hS f)
    (x : GeometricPoint B S hS X) (hx : IsQuasiFiniteAt B S hS f x.image) :
    (etaleLocalRingMap hX f x).Finite := by
  obtain ⟨U₀, V, g₀, hc₀, hp₀, _⟩ := exists_compatible_affine_chart_square B S hS hX hY f x
  obtain ⟨R, j, _, q, hq⟩ :=
    exists_affine_point_refinement (chartGeometricPoint U₀) (chartGeometricPoint U₀).hom
  have hB : B.Contains (Spec R) :=
    Scheme.size_lt_of_isOpenImmersion j U₀.chart.obj.left.left.property
  set Wo := chartRefinement U₀ hB j inferInstance q hq
  set U := Wo.left
  have : IsAffine (chartScheme U.chart) := inferInstanceAs (IsAffine (Spec R))
  set m : U.chart.obj.left ⟶ U₀.chart.obj.left := (SmallEtale.toOver B S hS X).map Wo.hom.hom
  set g := m ≫ g₀ with hg
  have hmc : yoneda.map m ≫ U₀.chart.obj.hom = U.chart.obj.hom :=
    CostructuredArrow.w Wo.hom.hom.hom
  have hcomm : U.chart.obj.hom ≫ f = yoneda.map g ≫ V.chart.obj.hom := by
    rw [← hmc, Category.assoc, hc₀, hg, Functor.map_comp, Category.assoc]
  have hpoint : U.point ≫ g = V.point := by
    rw [hg, ← Category.assoc, Wo.hom.point_comp, hp₀]
  set T := BigFppfOver.toScheme B S hS
  set k : chartScheme U.chart ⟶ chartScheme V.chart := T.map g
  have : LocallyOfFiniteType k :=
    hlft U.chart.obj.left V.chart.obj.left U.chart.obj.hom V.chart.obj.hom g U.chart.property
      V.chart.property hcomm.symm
  set u := (chartGeometricPoint U).hom (closedPoint (chartGeometricPoint U).residueField)
  set v := (chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField)
  have huv : k u = v :=
    congrArg (fun m ↦ (T.map m)
      (show T.obj x.val.siteObject from closedPoint x.val.carrier)) hpoint
  -- the point of the chart selected by the geometric point maps to the image of `x̄`
  set p : FieldValuedPoint B S hS (yoneda.obj U.chart.obj.left) :=
    { carrier := x.val.carrier
      contained := x.val.contained
      toBase := x.val.toBase
      value := U.point }
  have hmap : FieldValuedPoint.map B S hS _ U.chart.obj.hom p = x.val :=
    congrArg (fun a : X.obj (Opposite.op x.val.siteObject) => { x.val with value := a })
      U.point_comp
  have hpu : (pointsEquivScheme B S hS U.chart.obj.left).symm u =
      p.class B S hS (yoneda.obj U.chart.obj.left) :=
    (Equiv.symm_apply_eq _).2 rfl
  have hximage : pointsMap B S hS _ U.chart.obj.hom
      ((pointsEquivScheme B S hS U.chart.obj.left).symm u) = x.image := by
    rw [hpu, pointsMap_class, hmap]
  have hkqf : k.QuasiFiniteAt u := by
    have h1 := (isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero B S hS hX hY f hlft
      x.image).1 hx
    rw [← hximage] at h1
    exact ((AlgebraicGeometry.quasiFiniteAt_iff_fiberDimensionAt_eq_zero k u).2
      ((hasRelativeDimensionAt_pointsMap_iff B S hS 0 f U.chart.obj.left V.chart.obj.left
        U.chart.obj.hom V.chart.obj.hom g U.chart.property V.chart.property hcomm.symm u).1
        h1)).2
  set TV := henselizationTower ((chartScheme V.chart).presheaf.stalk v)
    (separableClosure (ResidueField ((chartScheme V.chart).presheaf.stalk v))
      (chartGeometricPoint V).residueField)
  set TU := henselizationTower ((chartScheme U.chart).presheaf.stalk u)
    (separableClosure (ResidueField ((chartScheme U.chart).presheaf.stalk u))
      (chartGeometricPoint U).residueField)
  refine finite_of_strictHenselization_germs_of_quasiFiniteAt k u hkqf v huv TV TU
    (strictHenselizationEquivEtaleLocalRing hY V (bigEtaleSiteOfFppfSite B)
      V.chart.obj.left.left.property TV)
    (strictHenselizationEquivEtaleLocalRing hX U (bigEtaleSiteOfFppfSite B)
      U.chart.obj.left.left.property TU)
    (etaleLocalRingMap hX f x) (isLocalHom_etaleLocalRingMap B S hS hX hY f x) fun a ↦ ?_
  calc
    _ = (etaleLocalRingMap hX f x)
          (etaleLocalRingGerm B S hS Y (geometricPointMap f x) (Opposite.op V) a) :=
      congrArg _ (strictHenselizationEquivEtaleLocalRing_germ hY V
        (bigEtaleSiteOfFppfSite B) V.chart.obj.left.left.property TV a)
    _ = etaleLocalRingGerm B S hS X x (Opposite.op U) ((Scheme.Γ.map k.op).hom a) :=
      (congrArg (fun m ↦ m a)
        (etaleLocalRingMap_isEtaleLocalRingMap hX f x U V g hcomm hpoint)).symm
    _ = _ := (strictHenselizationEquivEtaleLocalRing_germ hX U
      (bigEtaleSiteOfFppfSite B) U.chart.obj.left.left.property TU
      ((Scheme.Γ.map k.op).hom a)).symm

end AlgebraicGeometry.Space
