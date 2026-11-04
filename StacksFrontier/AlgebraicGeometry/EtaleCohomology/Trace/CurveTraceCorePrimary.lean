module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceCore
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MonodromyDescentIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.DescentModuleProjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTraceCorner

/-!
# The core of the proof of Tag 03UG for coefficients killed by a power of `ℓ`

Let `U` be a smooth connected affine curve over a finite field `k` without `k`-rational points,
`k̄` an algebraic closure of `k`, `Λ` a finite ring killed by `ℓ^m` for a prime `ℓ` invertible in
`k`, and `F` a locally constant sheaf of `Λ`-modules on `U_étale` with finite projective values.
Then `RΓ_c(U_k̄, F)` is perfect and `Tr(π_U^* | RΓ_c(U_k̄, F)) = 0`: the end of Step 3 of the
proof of [Stacks, Tag 03UG], for the coefficient rings of the last bullet of Step 3. The
perfectness of `RΓ_c(U_k̄, D(A[H]))` over `A[H]` and Step 7 for `Φ' = Hom_{A[H]}(N^∨, -)` are
the hypothesis `hStep7`.

## Main results

* `Stacks.EtaleCohomology.compactSupportTraceVanishes_of_forall_primary`: the vanishing for all
  finite coefficient rings of invertible order follows from the case of primary coefficients.
* `Stacks.EtaleCohomology.compactSupportTraceVanishes_of_primary`: the vanishing for
  coefficients killed by a power of `ℓ` on a smooth connected curve without rational points.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived
open MonoidAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

namespace Stacks.EtaleCohomology

section General

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **From primary coefficients to all finite coefficients** (the last bullet of Step 3 of the
proof of [Stacks, Tag 03UG]). Suppose that for every finite ring `Λ'` killed by `ℓ^m`, `ℓ` a prime
invertible in `k`, and every locally constant sheaf `F'` of `Λ'`-modules on `X_étale` with finite
projective values, `RΓ_c(X_k̄, F')` is perfect and `Tr(π_X^* | RΓ_c(X_k̄, F')) = 0`. Then the
same holds for every finite ring `Λ` with `#Λ` invertible in `k`. -/
theorem compactSupportTraceVanishes_of_forall_primary
    (hprim : ∀ (Λ' : Type) [Ring Λ'] [Finite Λ'] (ℓ m : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ((ℓ ^ m : ℕ) : Λ') = 0 → ∀ F' : EtaleModules.{u, 0} Λ' X,
        Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ' X.smallEtaleTopology F' →
        CompactSupportTraceVanishes Λ' kbar p q hcard f j
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F'))
    (Λ : Type) [Ring Λ] [Finite Λ] (hΛ : (Nat.card Λ : k) ≠ 0) (F : EtaleModules.{u, 0} Λ X)
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ X.smallEtaleTopology F) :
    CompactSupportTraceVanishes Λ kbar p q hcard f j
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) := by
  induction hN : Nat.card Λ using Nat.strong_induction_on generalizing Λ with
  | _ N ih =>
  subst hN
  have hdvd_ne : ∀ d : ℕ, d ∣ Nat.card Λ → (d : k) ≠ 0 := fun d ⟨c, hc'⟩ h0 =>
    hΛ (by rw [hc', Nat.cast_mul, h0, zero_mul])
  have hcorner : ∀ {e : Λ} (he : IsIdempotentElem e) (hc : ∀ a : Λ, a * e = e * a), e ≠ 1 →
      ∀ G : EtaleModules.{u, 0} he.Corner X,
        Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant he.Corner X.smallEtaleTopology G →
        CompactSupportTraceVanishes Λ kbar p q hcard f j
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
                ((etaleModuleRestrictScalars (cornerRingHom he hc) X).obj G)) := by
    intro e he hc he1 G hG
    have hdvd : Nat.card he.Corner ∣ Nat.card Λ :=
      AddSubgroup.card_addSubgroup_dvd_card (NonUnitalRing.corner e).toAddSubgroup
    have hlt : Nat.card he.Corner < Nat.card Λ := by
      refine Finite.card_subtype_lt (p := fun x => x ∈ Subsemigroup.corner e) (x := 1) ?_
      intro h1
      exact he1 (by simpa using ((Subsemigroup.mem_corner_iff he).1 h1).1)
    exact compactSupportTraceVanishes_cornerRestrict f j kbar p q
      hcard he hc G (ih _ hlt he.Corner (hdvd_ne _ hdvd) G hG rfl)
  obtain ⟨ι, _, e, ℓ, a, hcoi, hc, hℓ, ha⟩ := exists_primary_completeOrthogonalIdempotents Λ
  by_cases hsplit : ∃ i, e i ≠ 0 ∧ e i ≠ 1
  · obtain ⟨i, h0, h1⟩ := hsplit
    have he := hcoi.idem i
    refine compactSupportTraceVanishes_of_corners f j kbar p q
      hcard he (hc i) F ?_ ?_
    · exact hcorner he (hc i) h1 _
        (isFiniteProjectiveLocallyConstant_sheafCorner.{u + 1, 0, u + 1, u} he (hc i) _ hF)
    · have hc' : ∀ a : Λ, a * (1 - e i) = (1 - e i) * a :=
        fun a => ((Commute.one_right a).sub_right (hc i a)).eq
      exact hcorner he.one_sub hc' (fun h => h0 (sub_eq_self.1 h)) _
        (isFiniteProjectiveLocallyConstant_sheafCorner.{u + 1, 0, u + 1, u} he.one_sub hc' _ hF)
  · push Not at hsplit
    by_cases htriv : Subsingleton Λ
    · obtain ⟨l, hpl, hl⟩ := Nat.exists_infinite_primes (p + 1)
      have : Fact l.Prime := ⟨hl⟩
      have hlk : (l : k) ≠ 0 := by
        rw [Ne, CharP.cast_eq_zero_iff k p]
        intro hdvd
        have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hl).1 hdvd
        lia
      exact hprim Λ l 0 hlk (Subsingleton.elim _ _) F hF
    · rw [not_subsingleton_iff_nontrivial] at htriv
      obtain ⟨i, hi⟩ : ∃ i, e i = 1 := by
        by_contra hne
        push Not at hne
        have h0 : ∀ i, e i = 0 := fun i => by
          by_contra h'
          exact hne i (hsplit i h')
        exact one_ne_zero (by rw [← hcoi.complete]; exact Finset.sum_eq_zero fun i _ => h0 i)
      have : Fact (ℓ i).Prime := ⟨hℓ i⟩
      have hkill : ((ℓ i ^ a i : ℕ) : Λ) = 0 := by simpa [hi] using ha i
      have hlk : (ℓ i : k) ≠ 0 := by
        have : CharP Λ (ringChar Λ) := ringChar.charP Λ
        have hchar : ringChar Λ ∣ ℓ i ^ a i := ringChar.dvd hkill
        obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow (hℓ i)).1 hchar
        have hb0 : b ≠ 0 := by
          rintro rfl
          exact (CharP.ringChar_ne_one (R := Λ)) (by simpa using hb)
        let : Fintype Λ := Fintype.ofFinite Λ
        have hcard' : ringChar Λ ∣ Nat.card Λ := by
          rw [Nat.card_eq_fintype_card]
          exact ringChar.dvd (Nat.cast_card_eq_zero Λ)
        exact hdvd_ne _ ((dvd_pow_self _ hb0).trans (hb ▸ hcard'))
      exact hprim Λ (ℓ i) (a i) hlk hkill F hF

end General

variable {k : Type u} [Field k] [Fintype k] {U : Scheme.{u}} (fU : U ⟶ Spec (.of k))
  [IsCurve k fU] [Smooth fU] [ConnectedSpace U] [IsEmpty (rationalPoints fU)]
  (J : CompactificationOf (Over.mk fU))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

omit [ConnectedSpace U] in
/-- **The core of the proof of [Stacks, Tag 03UG] for coefficients killed by a power of `ℓ`**:
for a finite ring `Λ` killed by `ℓ^m`, `ℓ` a prime invertible in `k`, and a locally constant
sheaf `F` of `Λ`-modules with finite projective values on a smooth connected curve `U` without
`k`-rational points, `RΓ_c(U_k̄, F)` is perfect and `Tr(π_U^* | RΓ_c(U_k̄, F)) = 0`, granted
(`hStep7`) the perfectness of `RΓ_c(U_k̄, D(A[H]))` over `A[H]` and Step 7 for
`Φ' = Hom_{A[H]}(N^∨, -)` along every connected finite étale Galois covering of `U`. -/
theorem compactSupportTraceVanishes_of_primary
    (ℓ m : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (Λ : Type) [Ring Λ] [Finite Λ]
    (hΛ : ((ℓ ^ m : ℕ) : Λ) = 0)
    (hStep7 : ∀ (H : Type) [Group H] [Fintype H] (G : EtaleGaloisCovering U H)
      [IsFinite (G.cover.hom : G.cover.left ⟶ U)] [ConnectedSpace G.cover.left] (n : ℕ),
      1 ≤ n → ∀ [Algebra (ZMod (ℓ ^ n)) Λ] {N : Type (u + 1)} [AddCommGroup N] [Module Λ N]
        [Module (ZMod (ℓ ^ n)) N] [IsScalarTower (ZMod (ℓ ^ n)) Λ N] [Finite N]
        [Module.Finite Λ N] [Module.Projective Λ N] (ρ : H →* Module.End Λ N),
      ∃ (hperf : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
          (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) fU J kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))))))
        (h2a : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
          (compactSupportFrobeniusCohomology.{u, 0} Λ fU J kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              ((etaleModuleHom (dualRepModule (A := ZMod (ℓ ^ n)) ρ)
                (dualRepRightAction (A := ZMod (ℓ ^ n)) ρ) U).obj
                  (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))))))),
        perfectDerivedTrace Λ ⟨_, h2a⟩ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, 0} Λ fU J kbar p q hcard
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              ((etaleModuleHom (dualRepModule (A := ZMod (ℓ ^ n)) ρ)
                (dualRepRightAction (A := ZMod (ℓ ^ n)) ρ) U).obj
                  (G.regularDescentSheaf (A := ZMod (ℓ ^ n))))))) =
          functorTraceMap (homFunctor (dualRepModule (A := ZMod (ℓ ^ n)) ρ)
              (dualRepRightAction (A := ZMod (ℓ ^ n)) ρ)) (𝟙 _)
            (preservesFiniteProjective_homFunctor (n := ℓ ^ n) ρ)
            (perfectDerivedTrace (MonoidAlgebra (ZMod (ℓ ^ n)) H) ⟨_, hperf⟩
              (DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0}
                (MonoidAlgebra (ZMod (ℓ ^ n)) H) fU J kbar p q hcard
                ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
                  (G.regularDescentSheaf (A := ZMod (ℓ ^ n))))))))
    (F : EtaleModules.{u, 0} Λ U)
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ U.smallEtaleTopology F) :
    CompactSupportTraceVanishes Λ kbar p q hcard fU J
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) := by
  have : IsIntegral U := IsCurve.toIsVariety.toIsIntegral (k := k) (f := fU)
  have : IsNormal (Spec (CommRingCat.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have : IsNormal U := isNormal_of_smooth fU
  have hX : IsGeometricallyUnibranch U := isGeometricallyUnibranch_of_isNormal
  let x : GeometricPoint U := GeometricPoint.ofPoint U (Classical.arbitrary U)
  obtain ⟨H, _, _, G, N, _, _, ρ, -, hGfin, hGconn, ⟨eF⟩⟩ :=
    exists_etaleGaloisCovering_iso_descentSheaf hX x F
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_isFiniteProjectiveLocallyConstant _ _ hF)
  have := hGfin
  have := hGconn
  have : ConnectedSpace ((𝟭 Scheme).obj G.cover.left) := hGconn
  obtain ⟨hNf, hNp⟩ := G.finite_projective_of_isFiniteProjectiveLocallyConstant hX N ρ F hF eF
  have := hNf
  have := hNp
  have : Finite N := Module.finite_of_finite Λ
  have hℓ1 : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  let n := m + Fintype.card H
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let : Algebra (ZMod (ℓ ^ n)) Λ :=
    zmodAlgebraOfNatCastEqZero Λ hΛ (pow_dvd_pow ℓ (Nat.le_add_right m _))
  let : Module (ZMod (ℓ ^ n)) N := Module.compHom N (algebraMap (ZMod (ℓ ^ n)) Λ)
  have : IsScalarTower (ZMod (ℓ ^ n)) Λ N :=
    ⟨fun a l y => by
      show ((algebraMap (ZMod (ℓ ^ n)) Λ a) * l) • y = algebraMap (ZMod (ℓ ^ n)) Λ a • l • y
      rw [mul_smul]⟩
  have hn : 1 ≤ n := le_trans (Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero) (Nat.le_add_left _ _)
  have hnm : ∀ v : ℕ, ℓ ^ v ∣ Fintype.card H → m + v ≤ n := fun v hv =>
    Nat.add_le_add_left ((Nat.lt_pow_self hℓ1).le.trans (Nat.le_of_dvd Fintype.card_pos hv)) m
  obtain ⟨hperf, h2a, h2b⟩ := hStep7 H G n hn ρ
  obtain ⟨hD, hDt⟩ :=
    perfectDerivedTrace_canonicalCompactSupportFrobenius_descentSheaf_eq_zero_of_hom
      J G kbar p q hcard ℓ n m hℓ hn hΛ hnm ρ hperf h2a h2b
  let e := (Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ U) 0).mapIso eF.symm
  have hperfF := isPerfect_compactSupportFrobeniusCohomology_of_iso Λ fU J kbar e hD
  unfold CompactSupportTraceVanishes
  exact ⟨hperfF, (perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_of_iso Λ fU J kbar p q
    hcard e hD hperfF).symm.trans hDt⟩

end Stacks.EtaleCohomology

end
