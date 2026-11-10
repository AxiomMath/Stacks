module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedFiltrationCharSeries
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportExcisionCharSeries
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DescentSheafTraceIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisTwistDescentSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCharSeriesCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseStratumLocalFactor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistCompactSupport
public import StacksFrontier.Algebra.CharP.FiniteLocalRingPrimePow
public import StacksFrontier.LinearAlgebra.Matrix.GroupAlgebraTraceDetection

/-!
# The lisse case of [Stacks, Tag 03UZ]

Let `Z` be a separated scheme of finite type over a finite field `k` with an étale Galois covering
`C` with group `H`, `Λ` a finite local ring of order invertible in `k`, and `F` a sheaf of
`Λ`-modules on `Z` isomorphic to the descent sheaf of a representation `ρ` of `H` on a finite
projective (hence free) `Λ`-module `E`. Assume the trace formula, over every finite extension of
`k`, for the regular descent sheaf `PR_M` with coefficients `ℤ/ℓ^M[H]`. Then, for every
compactification, `RΓ_c(Z_k̄, F)` is perfect and

`det(1 - π_Z^* T | RΓ_c(Z_k̄, F)) · L(Z, F) = 1`.

## Main results

* `Stacks.EtaleCohomology.compactSupportCharSeriesInverts_of_galoisCovering`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius CategoryTheory.FilteredDerived Stacks.CharSeriesTraceDetection

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- The trace formula over the finite extensions of `k` for the regular descent sheaf of `C` with
coefficients `ℤ/ℓ^M[H]`: the trace of the Frobenius of `Z ×_k k'` on `RΓ_c` of the inverse image is
the sum of the local terms at its rational points. This is the instance of [Stacks, Tag 03V3]
consumed by the lisse case of Tag 03UZ. -/
def RegularDescentTraceFormula {k : Type u} [Field k] [Fintype k] {Z : Scheme.{u}}
    (fZ : Z ⟶ Spec (.of k)) (J : CompactificationOf (Over.mk fZ)) (kbar : Type u) [Field kbar]
    [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP kbar p] {H : Type}
    [Group H] [Fintype H] (C : EtaleGaloisCovering Z H) (ℓ M : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [Algebra k' kbar] [IsScalarTower k k' kbar]
    [CharP k' p]
    (m : ℕ) (hcard' : Fintype.card k' = p ^ (q * m)),
    ∃ (hs : ∀ s : rationalPoints (pullback.snd fZ (specAlgebraMap k k')),
        StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
          (rationalPointStalkComplex.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H) kbar s.1
            (baseChangeSingle (MonoidAlgebra (ZMod (ℓ ^ M)) H) fZ k'
              (C.descentSheaf.{u, 0, 0, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
                (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H)) (groupRingRightAction ℓ M H))))))
      (hperf' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
          (pullback.snd fZ (specAlgebraMap k k')) (compactificationFieldBaseChange fZ J k') kbar
          (baseChangeSingle (MonoidAlgebra (ZMod (ℓ ^ M)) H) fZ k'
            (C.descentSheaf.{u, 0, 0, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
              (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H)) (groupRingRightAction ℓ M H)))))),
      perfectDerivedTrace (MonoidAlgebra (ZMod (ℓ ^ M)) H) ⟨_, hperf'⟩ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
            (pullback.snd fZ (specAlgebraMap k k')) (compactificationFieldBaseChange fZ J k') kbar p
            (q * m) hcard'
            (baseChangeSingle (MonoidAlgebra (ZMod (ℓ ^ M)) H) fZ k'
              (C.descentSheaf.{u, 0, 0, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
                (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H)) (groupRingRightAction ℓ M H))))) =
        ∑ᶠ s : rationalPoints (pullback.snd fZ (specAlgebraMap k k')),
          perfectDerivedTrace (MonoidAlgebra (ZMod (ℓ ^ M)) H) ⟨_, hs s⟩ (DerivedCategory.Q.map
            (rationalPointStalkFrobenius.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H) kbar p (q * m)
              hcard' s.1
              (baseChangeSingle (MonoidAlgebra (ZMod (ℓ ^ M)) H) fZ k'
                (C.descentSheaf.{u, 0, 0, 0} (MonoidAlgebra (ZMod (ℓ ^ M)) H)
                  (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H)) (groupRingRightAction ℓ M H)))))

/-- Restricting the sum over the closed points of degree at most `N` to those of degree dividing
`m ≤ N`. -/
theorem sum_closedPointsDegreeLE_ite_dvd {k : Type u} [Field k] [Finite k] {Z : Scheme.{u}}
    (fZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType fZ] [QuasiCompact fZ] {A : Type*}
    [AddCommMonoid A] (G : closedPoints Z → A) {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ x ∈ closedPointsDegreeLE fZ N,
        (if residueDegree fZ x.1 ∣ m then residueDegree fZ x.1 • G x else 0) =
      ∑ x ∈ (closedPointsDegreeLE fZ m).filter (fun x => residueDegree fZ x.1 ∣ m),
        residueDegree fZ x.1 • G x := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, closedPointsDegreeLE, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨-, hd⟩
    exact ⟨Nat.le_of_dvd hm hd, hd⟩
  · rintro ⟨hle, hd⟩
    exact ⟨hle.trans hmN, hd⟩

section Lisse

variable (B : BigEtaleSite.{u}) (Z : B.Scheme) (Λ : Type) [CommRing Λ] [Finite Λ] [IsLocalRing Λ]
  (FZ : Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{u + 1} Λ))
  (hfin : ∀ s : GeometricPoint Z.obj,
    Module.Finite Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B Z Λ s).obj FZ))
  (hproj : ∀ s : GeometricPoint Z.obj,
    Module.Projective Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B Z Λ s).obj FZ))
  {k : Type u} [Field k] [Fintype k] (fZ : Z.obj ⟶ Spec (.of k)) [LocallyOfFiniteType fZ]
  [QuasiCompact fZ] (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  {H : Type} [Group H] [Fintype H] (C : EtaleGaloisCovering Z.obj H) (E : Type (u + 1))
  [AddCommGroup E] [Module Λ E] [Module.Finite Λ E] [Module.Projective Λ E]
  (ρ : H →* Module.End Λ E)
  (eF : (SmallEtale.sheafEquiv B Z.obj Z.property (ModuleCat.{u + 1} Λ)).functor.obj FZ ≅
    C.descentSheaf.{u, 0, 0, 0} Λ E ρ)

include eF in
/-- **The lisse case of [Stacks, Tag 03UZ].** On a scheme with an étale Galois covering along which
`F` is the descent sheaf of a finite projective module, given the trace formula for the regular
descent sheaves, `RΓ_c(Z_k̄, F)` is perfect and `det(1 - π_Z^* T | RΓ_c(Z_k̄, F)) · L(Z, F) = 1`
for every compactification. -/
theorem compactSupportCharSeriesInverts_of_galoisCovering (hΛ : ((Nat.card Λ : ℕ) : k) ≠ 0)
    (h03 : ∀ (J : CompactificationOf (Over.mk fZ)) (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ),
      ((ℓ : ℕ) : k) ≠ 0 →
      haveI : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
      RegularDescentTraceFormula fZ J kbar p q C ℓ M)
    (J : CompactificationOf (Over.mk fZ)) :
    CompactSupportCharSeriesInverts Λ kbar p q hcard fZ J
      ((SmallEtale.sheafEquiv B Z.obj Z.property (ModuleCat.{u + 1} Λ)).functor.obj FZ)
      (lFunctionOfFiniteProjectiveStalks.{u, u + 1, 0} B Z Λ FZ fZ hfin hproj) := by
  classical
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  obtain ⟨ℓ, a, hℓ, hℓdvd, hℓa⟩ := IsLocalRing.exists_prime_dvd_card_pow_natCast_eq_zero Λ
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓk : ((ℓ : ℕ) : k) ≠ 0 := ne_zero_of_dvd_ne_zero hΛ hℓdvd.natCast
  have : Module.Free Λ E := Module.free_of_flat_of_isLocalRing
  let r := Fintype.card (Module.Free.ChooseBasisIndex Λ E)
  let bE : E ≃ₗ[Λ] (Fin r → Λ) :=
    ((Module.Free.chooseBasis Λ E).reindex (Fintype.equivFin _)).equivFun
  choose lift hlift using C.exists_lift_geometricPointAt
  have hext : ∀ m : ℕ, 0 < m → ∃ (k' : IntermediateField k kbar) (_ : Fintype k'), CharP k' p ∧
      Fintype.card k' = p ^ (q * m) ∧ Module.finrank k k' = m := fun m hm => by
    obtain ⟨k', hk', hd⟩ := FiniteField.exists_intermediateField_card_eq_pow k kbar p q hcard hm
    have : Finite k' :=
      Nat.finite_of_card_ne_zero (by rw [hk']; exact (pow_pos (Fact.out : p.Prime).pos _).ne')
    have := Fintype.ofFinite k'
    exact ⟨k', this, charP_of_injective_algebraMap (algebraMap k k').injective p,
      by rw [← Nat.card_eq_fintype_card, hk'], hd⟩
  have key : ∀ N : ℕ, ∃ (R : Type) (_ : Ring R)
      (Φ : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} Λ) (_ : Φ.Additive) (O : ModuleCat.{u + 1} R)
      (eO : R ≃ₗ[R] O) (r : ℕ) (b : Φ.obj O ≃ₗ[Λ] (Fin r → Λ))
      (Q : CochainComplex (ModuleCat.{u + 1} R) ℤ) (hQ : finiteProjectiveComplex R Q) (g : Q ⟶ Q)
      (e : DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) ≅
        DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, 0} Λ fZ J kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ Z.obj) 0).obj
            ((SmallEtale.sheafEquiv B Z.obj Z.property (ModuleCat.{u + 1} Λ)).functor.obj FZ))))
      (_ : DerivedCategory.Q.map ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫ e.hom =
        e.hom ≫ DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0} Λ fZ J kbar p q
          hcard ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ Z.obj) 0).obj
            ((SmallEtale.sheafEquiv B Z.obj Z.property (ModuleCat.{u + 1} Λ)).functor.obj FZ))))
      (_ : TraceDetectionHypothesis (functorRep Φ eO b) N) (gP : closedPoints Z.obj → R),
      (∀ m, 0 < m → m ≤ N → ∃ h : Q ⟶ Q, (∀ i, (h.f i).hom = (g.f i).hom ^ m) ∧
        alternatingTrace R Q hQ h = ∑ x ∈ closedPointsDegreeLE fZ N,
          if residueDegree fZ x.1 ∣ m then
            residueDegree fZ x.1 • Stacks.CharSeriesTraceDetection.q R
              (gP x ^ (m / residueDegree fZ x.1)) else 0) ∧
      ∀ x ∈ closedPointsDegreeLE fZ N, finiteProjectiveLocalCharSeries B Z Λ FZ fZ hfin hproj x =
        (1 - (PowerSeries.X : PowerSeries Λ) ^ residueDegree fZ x.1 •
          (functorRep Φ eO b (gP x)).map (PowerSeries.C (R := Λ))).det := by
    intro N
    set M := a + Nat.log ℓ N with hM
    have hchar : ringChar Λ ∣ ℓ ^ M := by
      refine ((CharP.cast_eq_zero_iff Λ (ringChar Λ) (ℓ ^ a)).1 ?_).trans
        (pow_dvd_pow ℓ (by omega))
      rw [Nat.cast_pow]
      exact hℓa
    let : Algebra (ZMod (ℓ ^ M)) Λ := (ZMod.castHom hchar Λ).toAlgebra
    let : Module (ZMod (ℓ ^ M)) E := Module.compHom E (algebraMap (ZMod (ℓ ^ M)) Λ)
    have : IsScalarTower (ZMod (ℓ ^ M)) Λ E := ⟨fun x y z => by
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
    have : Finite E := Module.finite_of_finite Λ
    let R := MonoidAlgebra (ZMod (ℓ ^ M)) H
    let Ψ := twistFunctor (ZMod (ℓ ^ M)) H Λ E ρ
    let PR := C.descentSheaf.{u, 0, 0, 0} R (ULift.{u + 1} R) (groupRingRightAction ℓ M H)
    let KR := (Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} R Z.obj) 0).obj PR
    let τ : H → R := fun g => MonoidAlgebra.single g⁻¹ 1
    let eN : ULift.{u + 1} R ≃ₗ[R] R := ULift.moduleEquiv
    have hτ : ∀ g (x : ULift.{u + 1} R), eN (groupRingRightAction ℓ M H g x) = eN x * τ g :=
      fun g x => by
        simp [groupRingRightAction, rightMul_apply, τ, eN]
    obtain ⟨k₁, _, _, hk₁', hk₁d⟩ := hext 1 one_pos
    obtain ⟨hperfR, -⟩ := perfectDerivedTrace_pow_descentSheaf_eq_sum R fZ J kbar p q hcard C
      (ULift.{u + 1} R) (groupRingRightAction ℓ M H) eN τ hτ PR (Iso.refl _) lift
      hlift 1 one_pos k₁ hk₁' hk₁d (h03 J ℓ M hℓk k₁ 1 hk₁')
    obtain ⟨Q, hQ, g, eM, hg⟩ := exists_finiteProjectiveComplex_endo _ hperfR
      (DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, 0} R fZ J kbar p q hcard KR))
    have hQp : ∀ i, Projective (Q.X i) := fun i => by
      have := (hQ.2 i).1
      infer_instance
    obtain ⟨e₀, he₀⟩ := exists_iso_compactSupport_twistFunctor ℓ M H Λ E ρ fZ J kbar p q hcard KR
      (fun n => rightAcyclic_twistFunctor_single_descentSheaf_groupRing ℓ M H Λ E ρ C
        (groupRingRightAction ℓ M H) n) Q hQ.1.1 hQp g eM hg
    let iK : (sheafCompose Z.obj.smallEtaleTopology Ψ).mapCochainComplexPlus.obj KR ≅
        (Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ Z.obj) 0).obj
          ((SmallEtale.sheafEquiv B Z.obj Z.property (ModuleCat.{u + 1} Λ)).functor.obj FZ) :=
      (singlePlusObjMapIso (sheafCompose Z.obj.smallEtaleTopology Ψ) PR).symm ≪≫
        (Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ Z.obj) 0).mapIso
          ((descentSheafTwistIso ℓ M H Λ E ρ C).symm ≪≫ eF.symm)
    let e := e₀ ≪≫ (compactSupportFrobeniusFunctor.{u, 0} Λ fZ J kbar ⋙
      DerivedCategory.Plus.ι).mapIso iK
    have he : DerivedCategory.Q.map ((Ψ.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
        e.hom = e.hom ≫ DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0} Λ fZ J
          kbar p q hcard ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ Z.obj)
            0).obj ((SmallEtale.sheafEquiv B Z.obj Z.property (ModuleCat.{u + 1} Λ)).functor.obj
              FZ))) := by
      have hnat := (Functor.whiskerRight (canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ fZ J
        kbar p q hcard) DerivedCategory.Plus.ι).naturality iK.hom
      change _ ≫ (e₀.hom ≫ (compactSupportFrobeniusFunctor.{u, 0} Λ fZ J kbar ⋙
        DerivedCategory.Plus.ι).map iK.hom) = (e₀.hom ≫ (compactSupportFrobeniusFunctor.{u, 0} Λ fZ
          J kbar ⋙ DerivedCategory.Plus.ι).map iK.hom) ≫ _
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) he₀).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hnat.symm).trans
          (Category.assoc _ _ _).symm)))
    let O := groupRingRankOne ℓ M H
    let eO := groupRingRankOneEquiv ℓ M H
    let b := twistBasis ℓ M H Λ E ρ bE
    let gP : closedPoints Z.obj → R := fun x =>
      have := finite_residueField fZ x.1 x.2
      τ (C.pointElement (lift x.1) (hlift x.1) (frobeniusPointHom Z.obj x.1))
    refine ⟨R, inferInstance, Ψ, inferInstance, O, eO, r, b, Q, hQ, g, e, he,
      traceDetectionHypothesis_zmod_monoidAlgebra ℓ M a N (functorRep Ψ eO b) hℓa hM.le, gP,
      fun m hm hmN => ?_, fun x _ => ?_⟩
    · refine ⟨((End.of g) ^ m : End Q).asHom, hom_f_endPow g m, ?_⟩
      obtain ⟨km, _, _, hkm', hkmd⟩ := hext m hm
      obtain ⟨hperf, htr⟩ := perfectDerivedTrace_pow_descentSheaf_eq_sum R fZ J kbar p q hcard C
        (ULift.{u + 1} R) (groupRingRightAction ℓ M H) eN τ hτ PR (Iso.refl _) lift
        hlift m hm km hkm' hkmd (h03 J ℓ M hℓk km m hkm')
      have heR : DerivedCategory.Q.map g ≫ eM.hom = eM.hom ≫
          DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0} R fZ J kbar p q hcard
            KR) := by
        rw [hg]
        simp
      rw [alternatingTrace_endPow_eq_perfectDerivedTrace hQ g ⟨_, hperf⟩ _ eM heR m, htr,
        sum_closedPointsDegreeLE_ite_dvd fZ _ hm hmN]
      refine Finset.sum_congr rfl fun x _ => ?_
      have := finite_residueField fZ x.1 x.2
      rw [descentSheafLocalValue, dite_eq_left ‹Finite (Z.obj.residueField x.1)›]
      congr 2
      simp only [gP, τ]
      rw [MonoidAlgebra.single_pow, one_pow, inv_pow]
    · exact finiteProjectiveLocalCharSeries_eq_det_functorRep ℓ M H Λ E ρ B Z FZ fZ hfin hproj C
        eF bE x (lift x.1) (hlift x.1)
  obtain ⟨R, _, Φ, _, O, eO, r, b, Q, hQ, g, e, he, -, -, -, -⟩ := key 0
  have hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ fZ J kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ Z.obj) 0).obj
          ((SmallEtale.sheafEquiv B Z.obj Z.property (ModuleCat.{u + 1} Λ)).functor.obj FZ)))) :=
    StacksDraft.Perfect.isPerfect_of_iso e.symm ((isPerfect_iff Λ _).mpr
      ⟨_, finiteProjectiveComplex_functor Φ eO b Q hQ, ⟨Iso.refl _⟩⟩)
  exact ⟨hK, perfectDerivedCharSeries_mul_lFunctionOfFiniteProjectiveStalks_eq_one B Z Λ FZ fZ
    hfin hproj _ hK _ key⟩

end Lisse

end Stacks.EtaleCohomology
