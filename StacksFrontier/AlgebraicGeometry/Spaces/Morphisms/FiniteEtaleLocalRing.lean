module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohenMacaulay.Source
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.RingTheory.Henselian.QuasiFiniteRingMaps
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite morphisms of algebraic spaces and their étale local rings

The canonical homomorphism of étale local rings `𝒪_{Y, ȳ} → 𝒪_{X, x̄}` induced by a finite
morphism `f : X ⟶ Y` of algebraic spaces at a geometric point `x̄` of its source is a finite
ring map.

## Main results

* `AlgebraicGeometry.Space.finite_etaleLocalRingMap`: the canonical homomorphism of étale local
  rings of a finite morphism of algebraic spaces is finite.
* `AlgebraicGeometry.Space.exists_compatible_finite_affine_chart_square`: over a finite morphism
  of algebraic spaces there is, at any prescribed geometric point of the source, a commuting
  square of pointed étale scheme charts whose two chart schemes are affine and whose chart
  morphism is a finite morphism of schemes.

## Implementation notes

Finiteness of a morphism of algebraic spaces is a condition on its base changes along
morphisms out of affine objects of the site. Tested at an affine étale chart `V` of the target
through the image point, it produces an affine object `U` of the site, finite over `V` as a
scheme, together with a Cartesian square; the lift of the geometric point to that base change
exists because the point itself is a morphism into the source over `V`, so `U` becomes a small
étale neighbourhood of `x̄` and the chart morphism `U ⟶ V` is the finite morphism of affine
schemes the argument needs. This is
`AlgebraicGeometry.Space.exists_compatible_finite_affine_chart_square`.

On that square the étale local rings are the strict henselizations of the local rings of the
two chart schemes at the two points, by Stacks 04KF, and the canonical homomorphism agrees with
the stalk map on germs of global sections. Since both chart schemes are affine the local rings
are localizations of the global sections, and the global sections upstairs are a finite module
over those downstairs. So the statement is the ring-theoretic one that the map of strict
henselizations along a ring map which is finite — hence of finite type and quasi-finite at every
prime — is finite, which is Stacks 05WR,
`IsLocalRing.IsHenselization.finite_and_isPurelyInseparable_of_quasiFiniteAt`.

The route is the one that
`StacksFrontier/AlgebraicGeometry/Spaces/CohenMacaulay/Source.lean` takes for localness of the same
homomorphism: the germ-level hypothesis pins the homomorphism down because the germs of global
sections of an affine scheme generate the local ring, and the two chosen identifications of the
strict henselizations with the étale local rings are then stripped off, finiteness being stable
under composition with a surjection.

## References

* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 05WR](https://stacks.math.columbia.edu/tag/05WR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

/-! ### The map of strict henselizations along a finite ring map -/

/-- The strict henselization of a henselization tower is a henselization of the base at its own
residue field, with separably closed residue field, and the structure map is local. -/
private theorem strictHenselization_properties {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (ResidueField R) K] [IsSepClosure (ResidueField R) K]
    (T : HenselizationTower R K) :
    ∃ _ : IsLocalHom (algebraMap R T.strictHenselization),
      letI : Algebra (ResidueField R) (ResidueField T.strictHenselization) :=
        ResidueField.instAlgebra
      IsHenselization R (ResidueField T.strictHenselization) T.strictHenselization ∧
        IsSepClosure (ResidueField R) (ResidueField T.strictHenselization) := by
  have : IsLocalHom (algebraMap R T.strictHenselization) := by
    rw [IsScalarTower.algebraMap_eq R T.henselization T.strictHenselization]
    infer_instance
  obtain ⟨k, hk, hsep, he⟩ := IsHenselization.exists_residueFieldAlgebra
    (R := R) (L := K) (Rh := T.strictHenselization)
  let k₀ : Algebra (ResidueField R) (ResidueField T.strictHenselization) :=
    ResidueField.instAlgebra
  have hk_eq : k = k₀ := Algebra.algebra_ext _ _ fun a ↦ by
    obtain ⟨r, rfl⟩ := residue_surjective a
    exact (he r).trans (ResidueField.algebraMap_residue (S := T.strictHenselization) r).symm
  subst hk_eq
  exact ⟨this, hk, hsep inferInstance⟩

/-- **The map of strict henselizations along a finite ring map is finite.** Let `R → A` be a
finite ring map, let `q` be a prime of `A` over the prime `p` of `R`, let `Rp` and `Aq` be the
localizations there and let `T` and `N` be chosen henselization towers over them. A local
homomorphism of the two strict henselizations lying over `R → A` is finite.

A finite ring map is of finite type and quasi-finite at every prime, so this is Stacks 05WR,
`IsLocalRing.IsHenselization.finite_and_isPurelyInseparable_of_quasiFiniteAt`. -/
@[sga "4 XVII 6.2.6" "special case"]
private theorem finite_of_henselizationTower_square
    {R A Rp Aq K L : Type u} [CommRing R] [CommRing A] [CommRing Rp] [CommRing Aq]
    [IsLocalRing Rp] [IsLocalRing Aq] [Field K] [Field L]
    [Algebra R A] [Module.Finite R A] [Algebra R Rp] [Algebra A Aq]
    (p : Ideal R) (q : Ideal A) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
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
  obtain ⟨_, hT⟩ := strictHenselization_properties T
  obtain ⟨_, hN⟩ := strictHenselization_properties N
  let : Algebra (ResidueField Rp) (ResidueField T.strictHenselization) := ResidueField.instAlgebra
  let : Algebra (ResidueField Aq) (ResidueField N.strictHenselization) := ResidueField.instAlgebra
  obtain ⟨_, _⟩ := hT
  obtain ⟨_, _⟩ := hN
  exact (IsHenselization.finite_and_isPurelyInseparable_of_quasiFiniteAt
    (Rp := Rp) (Sq := Aq) (Rsh := T.strictHenselization)
    (Ssh := N.strictHenselization) p q).1

/-- A homomorphism between strict henselizations of the local rings of a finite morphism of
affine schemes at a point and its image which agrees with the map on germs of global sections
is finite.

Affineness makes the two local rings localizations of the global sections, over which the
morphism being finite says exactly that the global sections upstairs are a finite module, so
`AlgebraicGeometry.finite_of_henselizationTower_square` applies; the germ condition pins the
homomorphism down because the germs of global sections of an affine scheme generate the local
ring. -/
private theorem finite_of_strictHenselization_germs {Z W : Scheme.{u}} [IsAffine Z] [IsAffine W]
    (k : Z ⟶ W) [IsFinite k] (z : Z) (w : W) (hzw : k z = w) {K L : Type u} [Field K]
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
  have h1 : IsLocalHom eW.toRingHom := Space.isLocalHom_ringEquiv eW
  have h2 : IsLocalHom eZ.symm.toRingHom := Space.isLocalHom_ringEquiv eZ.symm
  have : IsLocalHom (φ.comp eW.toRingHom) := RingHom.isLocalHom_comp _ _
  have hψlocal : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
  let : Algebra Γ(W, ⊤) (W.presheaf.stalk (k z)) :=
    TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨k z, trivial⟩ : (⊤ : W.Opens))
  let : Algebra Γ(Z, ⊤) (Z.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk Z.presheaf (⟨z, trivial⟩ : (⊤ : Z.Opens))
  let : Algebra Γ(W, ⊤) Γ(Z, ⊤) := k.appTop.hom.toAlgebra
  have hfin : Module.Finite Γ(W, ⊤) Γ(Z, ⊤) := k.finite_appTop
  set p := ((isAffineOpen_top W).primeIdealOf (⟨k z, trivial⟩ : (⊤ : W.Opens))).asIdeal
  set q := ((isAffineOpen_top Z).primeIdealOf (⟨z, trivial⟩ : (⊤ : Z.Opens))).asIdeal
  have : IsLocalization.AtPrime (W.presheaf.stalk (k z)) p :=
    (isAffineOpen_top W).isLocalization_stalk (⟨k z, trivial⟩ : (⊤ : W.Opens))
  have : IsLocalization.AtPrime (Z.presheaf.stalk z) q :=
    (isAffineOpen_top Z).isLocalization_stalk (⟨z, trivial⟩ : (⊤ : Z.Opens))
  have : q.LiesOver p := ⟨by
    show p = Ideal.comap k.appTop.hom q
    have he := IsAffineOpen.comap_primeIdealOf_appLE (f := k) (⊤ : W.Opens)
      (isAffineOpen_top W) (⊤ : Z.Opens) (isAffineOpen_top Z) le_top (Set.mem_univ z)
    simpa [p, q, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      (congrArg PrimeSpectrum.asIdeal he).symm⟩
  have hψfin : ψ.Finite := by
    refine finite_of_henselizationTower_square p q T N ψ fun r => ?_
    show eZ.symm (φ (eW (algebraMap _ T.strictHenselization
      (W.presheaf.germ ⊤ (k z) trivial r)))) = _
    rw [hc, RingEquiv.symm_apply_apply]
    rfl
  have hfac : eZ.toRingHom.comp (ψ.comp eW.symm.toRingHom) = φ := by
    ext a
    exact (eZ.apply_symm_apply (φ (eW (eW.symm a)))).trans (congrArg φ (eW.apply_symm_apply a))
  rw [← hfac]
  exact (RingHom.Finite.of_surjective _ eZ.surjective).comp
    (hψfin.comp (RingHom.Finite.of_surjective _ eW.symm.surjective))

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### A finite affine chart square over a finite morphism -/

/-- Over a finite morphism of algebraic spaces there is at any prescribed geometric point of
the source a commuting square of pointed étale scheme charts whose two chart schemes are affine
and whose chart morphism is a finite morphism of schemes.

Finiteness of the morphism is a condition on its base changes along morphisms out of affine
objects of the site. Tested at an affine étale chart of the target through the image point it
hands back an affine object of the site, finite over that chart, together with a Cartesian
square; the geometric point is a morphism into the source over the chart of the target, so it
lifts to the base change, which is therefore a small étale neighbourhood of the point. -/
theorem exists_compatible_finite_affine_chart_square (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsFinite B S hS f) (x : GeometricPoint B S hS X) :
    ∃ (U : SmallEtaleNeighborhood x) (V : SmallEtaleNeighborhood (geometricPointMap f x))
      (g : U.chart.obj.left ⟶ V.chart.obj.left),
      U.chart.obj.hom ≫ f = yoneda.map g ≫ V.chart.obj.hom ∧ U.point ≫ g = V.point ∧
      IsAffine (chartScheme U.chart) ∧ IsAffine (chartScheme V.chart) ∧
      _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map g) := by
  obtain ⟨N⟩ := nonempty_smallEtaleNeighborhood hY (geometricPointMap f x)
  obtain ⟨V, hV⟩ := exists_affine_smallEtaleNeighborhood N
  obtain ⟨U, g, a, hU, hg, hsq⟩ := hf V.chart.obj.left hV V.chart.obj.hom
  have hw : (yonedaEquiv.symm x.val.value : yoneda.obj x.val.siteObject ⟶ X) ≫ f =
      (yoneda.map V.point : yoneda.obj x.val.siteObject ⟶ _) ≫ V.chart.obj.hom := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_symm_naturality_right, Equiv.apply_symm_apply, yonedaEquiv_comp]
    exact ((congrArg (V.chart.obj.hom.app _) (yonedaEquiv_yoneda_map V.point)).trans
      V.point_comp).symm
  obtain ⟨r, hr⟩ := yoneda.map_surjective (hsq.lift _ _ hw)
  have hr₁ : a.app _ r = x.val.value := by
    have he : yoneda.map r ≫ a = (yonedaEquiv.symm x.val.value :
        yoneda.obj x.val.siteObject ⟶ X) := by
      rw [hr]; exact hsq.lift_fst _ _ hw
    have h1 : yonedaEquiv (yoneda.map r ≫ a) = a.app _ r :=
      (yonedaEquiv_comp (yoneda.map r) a).trans (congrArg (a.app _) (yonedaEquiv_yoneda_map r))
    exact h1.symm.trans ((congrArg yonedaEquiv he).trans (yonedaEquiv.apply_symm_apply _))
  have hr₂ : r ≫ g = V.point :=
    yoneda.map_injective (by rw [yoneda.map_comp, hr]; exact hsq.lift_snd _ _ hw)
  let : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a :=
    MorphismProperty.of_isPullback hsq.flip V.chart.property
  exact ⟨⟨⟨CostructuredArrow.mk a, ha⟩, r, hr₁⟩, V, g, hsq.w, hr₂, hU, hV, hg⟩

/-! ### Finiteness of the canonical homomorphism of étale local rings -/

/-- **The canonical homomorphism of étale local rings of a finite morphism of algebraic spaces
is finite.** Let `f : X ⟶ Y` be a finite morphism of algebraic spaces over `S` and let `x̄` be a
geometric point of `X`. Then `𝒪_{Y, ȳ} → 𝒪_{X, x̄}` is a finite ring map.

On an affine chart square over `f` with finite chart morphism, which is
`AlgebraicGeometry.Space.exists_compatible_finite_affine_chart_square`, the two étale local
rings are the strict henselizations of the two local rings of the chart schemes by Stacks 04KF,
and the canonical homomorphism agrees with the map of global sections on germs. The statement is
then the ring-theoretic one that strict henselization of a finite ring map stays finite, which
is Stacks 05WR. -/
theorem finite_etaleLocalRingMap (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsFinite B S hS f)
    (x : GeometricPoint B S hS X) :
    (etaleLocalRingMap hX f x).Finite := by
  obtain ⟨U, V, g, hcomm, hpoint, hUaffine, hVaffine, hgfinite⟩ :=
    exists_compatible_finite_affine_chart_square hY f hf x
  have : IsAffine (chartScheme U.chart) := hUaffine
  have : IsAffine (chartScheme V.chart) := hVaffine
  set k : chartScheme U.chart ⟶ chartScheme V.chart :=
    (BigFppfOver.toScheme B S hS).map g
  have : _root_.AlgebraicGeometry.IsFinite k := hgfinite
  set u := (chartGeometricPoint U).hom (closedPoint (chartGeometricPoint U).residueField)
  set v := (chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField)
  have huv : k u = v :=
    congrArg (fun m ↦ ((BigFppfOver.toScheme B S hS).map m)
      (show (BigFppfOver.toScheme B S hS).obj x.val.siteObject from
        closedPoint x.val.carrier)) hpoint
  set TV := henselizationTower ((chartScheme V.chart).presheaf.stalk v)
    (separableClosure (ResidueField ((chartScheme V.chart).presheaf.stalk v))
      (chartGeometricPoint V).residueField)
  set TU := henselizationTower ((chartScheme U.chart).presheaf.stalk u)
    (separableClosure (ResidueField ((chartScheme U.chart).presheaf.stalk u))
      (chartGeometricPoint U).residueField)
  refine finite_of_strictHenselization_germs k u v huv TV TU
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

end Space

end AlgebraicGeometry

end
