module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricPointStalkCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveSpecialization.ConstantCoefficientsSpecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTraceDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveFirstCohomologyCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveCupProductLevel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness of the stalks of `R^q f_* ℤ/ℓ` for a smooth proper family of curves

Let `f : X ⟶ S` be proper and smooth with geometrically connected fibres of dimension at most one
and `ℓ` a prime invertible on `S`. For every geometric point `s̄` of `S` and every `q`, the stalk
of `R^q f_* ℤ/ℓ` at `s̄` is finite. By proper base change (Tag 095T, through Tag 0DDF) it is
`H^q(X_s̄, ℤ/ℓ)`. The geometric fibre `X_s̄` is smooth proper and connected over the algebraically
closed field `κ(s̄)`, of relative dimension zero or one. In relative dimension zero it is finite
over `κ(s̄)` and has `H⁰ = ℤ/ℓ` and no higher cohomology (Tag 09AY). In relative dimension one it
is a smooth proper curve, with `#H⁰ = ℓ`, `#H¹ = ℓ^{2g}`, `#H² = ℓ` and `H^q = 0` for `q ≥ 3`
(Tags 03RQ, 03SF).

This is the finiteness input of Tag 0GKV.

## Main results

* `finite_smallEtaleStalkAb_homology_derivedDirectImage_constantZMod_of_isUnit`, in the namespace
  `Stacks.EtaleCohomology`.

## References

* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 0GKV](https://stacks.math.columbia.edu/tag/0GKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **The cohomology `H^q(Z, ℤ/ℓ)` of a smooth proper connected scheme of dimension at most one
over an algebraically closed field is finite**, for `ℓ` a prime invertible in the field. Such a
scheme is smooth of relative dimension zero (a point) or one (a smooth proper curve). -/
@[sga "4 XIV 1.11" "special case"]
theorem finite_constantExt_of_smooth_of_isProper {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {Z : Scheme.{u}} (π : Z ⟶ Spec (.of Ω)) [IsProper π] [Smooth π] [GeometricallyConnected π]
    (hd : topologicalKrullDim (π.fiber (IsLocalRing.closedPoint Ω)) ≤ 1) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : Ω)) (q : ℕ) : Finite (CurveFamily.H ℓ Z q) := by
  have hℓ0 : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have sq : IsPullback (𝟙 Z) π π (𝟙 (Spec (.of Ω))) := IsPullback.of_id_fst
  have hfin : ∀ {q m : ℕ}, Nat.card (CurveFamily.H ℓ Z q) = m → m ≠ 0 →
      Finite (CurveFamily.H ℓ Z q) := fun h hm => Nat.finite_of_card_ne_zero (h ▸ hm)
  have hcard0 : ConnectedSpace Z → Finite (CurveFamily.H ℓ Z 0) := fun _ =>
    hfin (Stacks.EtaleCohomology.LevelChange.natCard_ext_zero_unitSheaf (Y := Z) ℓ) hℓ0
  rcases smoothOfRelativeDimension_zero_or_one π hd with h0 | h1
  · obtain ⟨hconn, hsub⟩ :=
      CurveFamily.connectedSpace_and_subsingleton_of_smoothOfRelativeDimension_zero (ℓ := ℓ) π
        (𝟙 _) sq
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact hcard0 hconn
    · exact @Finite.of_subsingleton _ (hsub q hq)
  · obtain ⟨hcurve, hsm, hpr, hconn⟩ := CurveFamily.isCurve_of_isPullback π (𝟙 _) sq
    rcases Nat.lt_or_ge q 3 with hq | hq
    · interval_cases q
      · exact hcard0 hconn
      · exact hfin (Stacks.Kummer.natCard_ext_one_constantModuleSheaf_of_smoothProperCurve π hℓ)
          (pow_ne_zero _ hℓ0)
      · exact hfin (Stacks.Kummer.natCard_ext_two_constantModuleSheaf_of_smoothProperCurve π hℓ
          (fun L hL => Stacks.Picard.exists_nsmul_eq_of_picardDegree_eq_zero π _ hℓ L hL)) hℓ0
    · exact @Finite.of_subsingleton _
        (Stacks.Kummer.subsingleton_ext_constantModuleSheaf_of_smoothCurve π hℓ q hq)

/-- **The stalks of `R^q f_* ℤ/ℓ` along a smooth proper family of curves are finite.** Let
`f : X ⟶ S` be proper and smooth with geometrically connected fibres of dimension at most one and
`ℓ` a prime invertible on `S`. For every geometric point `s̄` of `S` and every `q`, the stalk at
`s̄` of `H^q(Rf_* ℤ/ℓ)` is finite: it is `H^q(X_s̄, ℤ/ℓ)` by proper base change, and `X_s̄` is a
point or a smooth proper curve over the algebraically closed field `κ(s̄)`. -/
theorem finite_smallEtaleStalkAb_homology_derivedDirectImage_constantZMod_of_isUnit
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) (ℓ : ℕ)
    [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : Γ(S, ⊤))) (s : GeometricPoint S) (q : ℤ) :
    Finite ((smallEtaleStalkAb s.hom).obj
      ((DerivedCategory.homologyFunctor (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((etaleAbelianDerivedDirectImage.{u, 0} f).obj
          ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
            ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              ((forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}).obj
                (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))))) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  let A := (forget₂ (ModuleCat.{u + 1} (ZMod ℓ)) AddCommGrpCat.{u + 1}).obj
    (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ)))
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A
  have hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F :=
    torsionSheafProperty_constantZModAb X ℓ
  rcases lt_or_ge q 0 with hq | hq
  · -- Negative degrees: the cohomology sheaf vanishes.
    have hZ : IsZero ((DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((etaleAbelianDerivedDirectImage.{u, 0} f).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) :=
      Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj
        (etaleAbelianDirectImage.{u, 0} f) ((DerivedCategory.singleFunctor _ 0).obj F) 0 q hq
    have hZ' := (smallEtaleStalkAb s.hom).map_isZero hZ
    have : Subsingleton ((smallEtaleStalkAb s.hom).obj
        ((DerivedCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((etaleAbelianDerivedDirectImage.{u, 0} f).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)))) :=
      AddCommGrpCat.subsingleton_of_isZero hZ'
    infer_instance
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    let y := s.hom
    let Z := pullback f y
    let g' := pullback.fst f y
    let π : Z ⟶ Spec (.of s.residueField) := pullback.snd f y
    -- The stalk is a stalk at the universe lift of the point.
    let e₁ := ((GrothendieckTopology.Point.uliftPresheafFiberIso.{u + 1}
      (A := AddCommGrpCat.{u + 1}) (Scheme.pointSmallEtale y)).app
        ((DerivedCategory.homologyFunctor
          (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) n).obj
          ((etaleAbelianDerivedDirectImage.{u, 0} f).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))).obj).symm
    -- The cohomology sheaf of `Rf_* F[0]` is `R^n f_* F`, whose stalk is `H^n(X_s̄, F)`.
    let e₂ := ((Scheme.pointSmallEtale y).ulift.{u + 1}).sheafFiber.mapIso
      (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
        (etaleAbelianDirectImage.{u, 0} f) (etaleAbelianDerivedDirectImage.{u, 0} f)
        (etaleAbelianDerivedDirectImageUnit.{u, 0} f)
        Stacks.DerivedFunctor.exists_quasiIso_isKInjective F n) ≪≫
      etaleAbelianSheafFiberRightDerivedDirectImageIso.{u, 0} f y
        (cohomologyCommutesWithBaseChange_of_isProper f) F hF n
    -- `H^n(X_s̄, g'⁻¹ ℤ/ℓ) = H^n(X_s̄, ℤ/ℓ)`.
    let e₃ := (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{0}
        Z.smallEtaleTopology n).symm.app ((etaleAbelianInverseImage.{u, 0} g').obj F) ≪≫
      ((Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived n).mapIso
        ((etaleAbelianInverseImageConstantIso.{u, 0} g').app A) ≪≫
      (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{0}
        Z.smallEtaleTopology n).app (constantZModAb Z ℓ)
    -- `H^n(X_s̄, ℤ/ℓ)` is finite.
    have hℓΩ : IsUnit (ℓ : s.residueField) := by
      have := hℓ.map (y.appTop ≫ (Scheme.ΓSpecIso (.of s.residueField)).hom).hom
      simpa using this
    have hd : topologicalKrullDim (π.fiber (IsLocalRing.closedPoint s.residueField)) ≤ 1 :=
      topologicalKrullDim_fiber_pullbackSnd_le f y _ hdim _
    have := finite_constantExt_of_smooth_of_isProper π hd ℓ hℓΩ n
    have hH₀ : Finite (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian Z (ZMod ℓ)).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod ℓ) Z.smallEtaleTopology)) n) :=
      Finite.of_surjective _ (extForgetSheafH_bijective (ZMod ℓ) Z n
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod ℓ) Z.smallEtaleTopology)).2
    have hH : Finite (Sheaf.H.{u + 1} (constantZModAb Z ℓ) n) :=
      Finite.of_surjective (Sheaf.H.map (constantZModAbIso Z ℓ).hom n) (fun z => ⟨Sheaf.H.map
        (constantZModAbIso Z ℓ).inv n z, by
          rw [← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply]⟩)
    have hH' : Finite (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} g').obj F) n) :=
      @Finite.of_equiv _ _ hH e₃.addCommGroupIsoToAddEquiv.toEquiv.symm
    exact @Finite.of_equiv _ _ hH' (e₁ ≪≫ e₂).addCommGroupIsoToAddEquiv.toEquiv.symm

end Stacks.EtaleCohomology

end
