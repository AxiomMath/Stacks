module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DescentSheafTraceDecomposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.MonodromyDescentIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfCentralIdempotent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SectionwiseFunctorEtaleQuasiIso
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace formula for a lisse complex on a smooth curve without rational points

Let `k` be a finite field, `U` a smooth curve over `k` without `k`-rational points, `Λ` a finite
ring whose cardinality is prime to that of `k`, and `K` a bounded complex of sheaves of
`Λ`-modules on `U_étale` which are locally constant with finite projective values. Then
`RΓ_c(U_k̄, K)` is perfect and `Tr(π_U^* | RΓ_c(U_k̄, K)) = 0`, which is the trace formula for `K`
since `U(k) = ∅`; this is the case of [Stacks, Tag 03UG] to which Step 3 reduces, and the
present file carries out the remaining reductions of Step 3: from a complex to its terms
(`Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber_eq_sum_single`), from a sheaf to
the descent sheaf `D(M)` of its monodromy along a Galois covering
(`AlgebraicGeometry.exists_etaleGaloisCovering_iso_descentSheaf`), and from `Λ` to its primary
parts, along the primary idempotents of `Λ`
(`Stacks.EtaleCohomology.exists_primary_completeOrthogonalIdempotents`).

The perfectness of `RΓ_c(U_k̄, -)` on sheaves locally constant with finite projective values is
taken as the input `hP` of the statements here; it is supplied by
[Stacks, Tag 03TV] in its form for curves of dimension at most one.

## Main results

* `Stacks.EtaleCohomology.exists_canonicalCompactSupportLefschetzNumber_descentSheaf_eq_zero`.
* `Stacks.EtaleCohomology.exists_canonicalCompactSupportLefschetzNumber_eq_zero_of_lisse`.
* `Stacks.EtaleCohomology.canonicalTraceFormula_of_lisse_of_isEmpty`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 3.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u v r

attribute [local instance] HasDerivedCategory.standard


namespace Stacks.EtaleCohomology

open AlgebraicGeometry.EtaleGaloisCovering

section Zero

/-- **The descent sheaf of a zero module is zero.** -/
theorem isZero_descentSheaf {X : Scheme.{u}} {H : Type} [Group H] (G : EtaleGaloisCovering X H)
    (Λ : Type) [Ring Λ] (N : Type (u + 1)) [AddCommGroup N] [Module Λ N]
    (ρ : H →* Module.End Λ N) [Subsingleton N] :
    IsZero (G.descentSheaf.{u, 0, 0, u + 1} Λ N ρ) :=
  isZero_of_forall_isZero_moduleSections.{u, 0} Λ (G.descentSheaf.{u, 0, 0, u + 1} Λ N ρ)
    fun W =>
    have : Subsingleton (G.equivariantMaps Λ N ρ W) :=
      ⟨fun _ _ => Subtype.ext (LocallyConstant.ext fun _ => Subsingleton.elim _ _)⟩
    have : Subsingleton ((G.descentSheaf.{u, 0, 0, u + 1} Λ N ρ).obj.obj (op W)) :=
      inferInstanceAs (Subsingleton (G.equivariantMaps Λ N ρ W))
    ModuleCat.isZero_of_subsingleton _

variable {k : Type u} [Field k] [Fintype k] {U : Scheme.{u}} {pU : U ⟶ Spec (.of k)}
  (J : CompactificationOf (Over.mk pU))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q) {Λ : Type} [Ring Λ] [Finite Λ]

/-- The trace of `π^*` vanishes on the compactly supported cohomology of a zero sheaf. -/
theorem exists_canonicalCompactSupportLefschetzNumber_eq_zero_of_isZero
    (F : EtaleModules.{u, 0} Λ U) (hF : IsZero F) :
    ∃ hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ pU J kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F))),
      canonicalCompactSupportLefschetzNumber.{u, 0} Λ pU J kbar p q hcard
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) hX = 0 := by
  have hZ := isZero_compactSupportFrobeniusCohomology_of_isZero_X Λ J kbar
    ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) fun m => by
      by_cases hm : m = 0
      · subst hm
        exact IsZero.of_iso hF (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F)
      · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F m hm
  exact ⟨StacksDraft.Perfect.isPerfect_of_isZero _ hZ,
    canonicalCompactSupportLefschetzNumber_eq_zero_of_isZero Λ J kbar p q hcard _ _ hZ⟩

end Zero

section Prime

/-- **A nonzero element killed by `ℓ^a` in a finite ring whose cardinality is prime to `p` forces
`ℓ ≠ p`.** -/
theorem ne_of_natCast_pow_mul_eq_zero {Λ : Type} [Ring Λ] [Finite Λ] {p q ℓ a : ℕ}
    (hcop : Nat.Coprime (Nat.card Λ) (p ^ q)) (hq : q ≠ 0) {e : Λ} (he : e ≠ 0)
    (hkill : ((ℓ ^ a : ℕ) : Λ) * e = 0) : ℓ ≠ p := by
  rintro rfl
  have hcop' : Nat.Coprime (ℓ ^ a) (Nat.card Λ) :=
    Nat.Coprime.pow_left a ((Nat.Coprime.coprime_dvd_right (dvd_pow_self ℓ hq) hcop).symm)
  have h1 : addOrderOf e ∣ ℓ ^ a :=
    addOrderOf_dvd_of_nsmul_eq_zero (by rw [nsmul_eq_mul]; exact hkill)
  have h2 : addOrderOf e ∣ Nat.card Λ := addOrderOf_dvd_natCard e
  have h3 : addOrderOf e = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop') h2
  exact he (AddMonoid.addOrderOf_eq_one_iff.1 h3)

/-- A retract of a finite projective module is finite projective. -/
private theorem projective_finite_of_comp_eq_id {Λ : Type*} [Ring Λ] {M P : Type*}
    [AddCommGroup M] [Module Λ M] [AddCommGroup P] [Module Λ P] [Module.Finite Λ M]
    [Module.Projective Λ M] {i : P →ₗ[Λ] M} {s : M →ₗ[Λ] P} (h : s.comp i = LinearMap.id) :
    Module.Projective Λ P ∧ Module.Finite Λ P :=
  ⟨Module.Projective.of_split i s h,
    Module.Finite.of_surjective s fun x => ⟨_, LinearMap.congr_fun h x⟩⟩

end Prime

section Descent

variable {k : Type u} [Field k] [Fintype k] {U : Scheme.{u}} {pU : U ⟶ Spec (.of k)}
  [IsCurve k pU] [Smooth pU] (J : CompactificationOf (Over.mk pU))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)
  {Λ : Type} [Ring Λ] [Finite Λ] (hcop : Nat.Coprime (Nat.card Λ) (Fintype.card k))
  {H : Type} [Group H] [Finite H] (G : EtaleGaloisCovering U H)
  [ConnectedSpace G.cover.left] [IsFinite (G.cover.hom : G.cover.left ⟶ U)]

include hcop in
/-- **Steps 3–9 of [Stacks, Tag 03UG] for a descent sheaf.** For a finite projective `Λ`-module
`M` with an action of the group of a connected finite Galois covering `G` of a smooth curve `U`
without rational points, `RΓ_c(U_k̄, D(M))` is perfect and the trace of `π_U^*` on it vanishes,
granted perfectness of `RΓ_c(U_k̄, D((ℤ/ℓⁿ)[H]))` over `(ℤ/ℓⁿ)[H]` for all `ℓ` and `n`. -/
theorem exists_canonicalCompactSupportLefschetzNumber_descentSheaf_eq_zero
    [IsEmpty (rationalPoints pU)]
    (hperfD : ∀ (ℓ n : ℕ) [Fact ℓ.Prime] [NeZero (ℓ ^ n)],
      StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))))))
    (M : Type (u + 1)) [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] [Module.Projective Λ M]
    (ρ : H →* Module.End Λ M) :
    ∃ hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ pU J kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (G.descentSheaf.{u, 0, 0, u + 1} Λ M ρ)))),
      canonicalCompactSupportLefschetzNumber.{u, 0} Λ pU J kbar p q hcard
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (G.descentSheaf.{u, 0, 0, u + 1} Λ M ρ)) hX = 0 := by
  classical
  have := Fintype.ofFinite H
  obtain ⟨ι, _, e, ℓ, a, hCOI, hcen, hprime, hkill⟩ :=
    exists_primary_completeOrthogonalIdempotents Λ
  have hq : q ≠ 0 := by
    rintro rfl
    exact (Fintype.one_lt_card (α := k)).ne' (hcard.trans (pow_zero p))
  have hcop' : Nat.Coprime (Nat.card Λ) (p ^ q) := hcard ▸ hcop
  suffices h : ∀ S : Finset ι, ∀ (M : Type (u + 1)) [AddCommGroup M] [Module Λ M]
      [Module.Finite Λ M] [Module.Projective Λ M] (ρ : H →* Module.End Λ M),
      (∀ x : M, (∑ i ∈ S, e i) • x = x) →
      ∃ hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
          (compactSupportFrobeniusCohomology.{u, 0} Λ pU J kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              (G.descentSheaf.{u, 0, 0, u + 1} Λ M ρ)))),
        canonicalCompactSupportLefschetzNumber.{u, 0} Λ pU J kbar p q hcard
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (G.descentSheaf.{u, 0, 0, u + 1} Λ M ρ)) hX = 0 by
    exact h Finset.univ M ρ fun x => by rw [hCOI.complete, one_smul]
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro M _ _ _ _ ρ hM
    have : Subsingleton M := ⟨fun x y => by
      rw [← hM x, ← hM y, Finset.sum_empty, zero_smul, zero_smul]⟩
    exact exists_canonicalCompactSupportLefschetzNumber_eq_zero_of_isZero J kbar p q hcard _
      (isZero_descentSheaf G Λ M ρ)
  | insert i S hi ih =>
    intro M _ _ _ _ ρ hM
    have he : IsIdempotentElem (e i) := hCOI.idem i
    have hc : ∀ x : Λ, x * e i = e i * x := hcen i
    have hfr : (fixProj (e i) hc he).comp (fixPart (M := M) (e i) hc).subtype = LinearMap.id :=
      LinearMap.ext fun x => Subtype.ext ((mem_fixPart (e i) hc).1 x.2)
    have hkr : (killProj (e i) hc he).comp (killPart (M := M) (e i) hc).subtype = LinearMap.id :=
      LinearMap.ext fun x => Subtype.ext (by
        show (x : M) - e i • (x : M) = x
        rw [(mem_killPart (e i) hc).1 x.2, sub_zero])
    obtain ⟨_, _⟩ := projective_finite_of_comp_eq_id hfr
    obtain ⟨_, _⟩ := projective_finite_of_comp_eq_id hkr
    obtain ⟨h₁, hz₁⟩ : ∃ h₁ : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ pU J kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (G.descentSheaf.{u, 0, 0, u + 1} Λ (fixPart (M := M) (e i) hc)
              (fixRep ρ (e i) hc))))),
        canonicalCompactSupportLefschetzNumber.{u, 0} Λ pU J kbar p q hcard
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (G.descentSheaf.{u, 0, 0, u + 1} Λ (fixPart (M := M) (e i) hc)
              (fixRep ρ (e i) hc))) h₁ = 0 := by
      by_cases hei : e i = 0
      · have key : ∀ y : M, e i • y = 0 := fun y => by rw [hei, zero_smul]
        have : Subsingleton (fixPart (M := M) (e i) hc) := ⟨fun x y => Subtype.ext
          ((((mem_fixPart (e i) hc).1 x.2).symm.trans (key x)).trans
            (((mem_fixPart (e i) hc).1 y.2).symm.trans (key y)).symm)⟩
        exact exists_canonicalCompactSupportLefschetzNumber_eq_zero_of_isZero J kbar p q hcard _
          (isZero_descentSheaf G Λ _ _)
      · have : Fact (ℓ i).Prime := ⟨hprime i⟩
        have hℓp : ℓ i ≠ p := ne_of_natCast_pow_mul_eq_zero hcop' hq hei (hkill i)
        have hℓ : ((ℓ i : ℕ) : k) ≠ 0 := by
          rw [Ne, CharP.cast_eq_zero_iff k p]
          intro hdvd
          exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (hprime i)).1 hdvd).symm
        have heM : ∀ x : fixPart (M := M) (e i) hc, e i • x = x :=
          fun x => Subtype.ext ((mem_fixPart (e i) hc).1 x.2)
        have : NeZero (ℓ i ^ descentExponent (a i) (H := H)) :=
          ⟨pow_ne_zero _ (hprime i).ne_zero⟩
        let := descentZModModule (H := H) (ℓ i) (a i) (e i) (hkill i) heM
        have hn : 1 ≤ descentExponent (a i) (H := H) := by
          have := Fintype.card_pos (α := H)
          rw [descentExponent]
          omega
        have hnm : ∀ v : ℕ, ℓ i ^ v ∣ Fintype.card H →
            a i + v ≤ descentExponent (a i) (H := H) := by
          intro v hv
          have h1 : v < ℓ i ^ v := Nat.lt_pow_self (hprime i).one_lt
          have h2 : ℓ i ^ v ≤ Fintype.card H := Nat.le_of_dvd (Fintype.card_pos (α := H)) hv
          rw [descentExponent]
          omega
        exact canonicalCompactSupportLefschetzNumber_eq_zero_of_descentSheaf J kbar p q hcard
          (ℓ i) (a i) hℓ (e i) hc (hkill i) G (fixRep ρ (e i) hc) (descentExponent (a i) (H := H))
          hn hnm heM _ (Iso.refl _) (hperfD (ℓ i) (descentExponent (a i) (H := H)))
    obtain ⟨h₃, hz₃⟩ := ih (killPart (M := M) (e i) hc) (killRep ρ (e i) hc) fun x =>
      Subtype.ext (by
        have h1 := hM (x : M)
        rwa [Finset.sum_insert hi, add_smul, (mem_killPart (e i) hc).1 x.2, zero_add] at h1)
    obtain ⟨h₂, hsum⟩ := canonicalCompactSupportLefschetzNumber_descentSheaf_eq_add J kbar p q
      hcard G ρ (e i) hc he h₁ h₃
    exact ⟨h₂, hsum.trans (by rw [hz₁, hz₃, add_zero])⟩

end Descent

section Lisse

variable {k : Type u} [Field k] [Fintype k] {U : Scheme.{u}} {pU : U ⟶ Spec (.of k)}
  [IsCurve k pU] [Smooth pU] (J : CompactificationOf (Over.mk pU))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)
  {Λ : Type} [Ring Λ] [Finite Λ] (hcop : Nat.Coprime (Nat.card Λ) (Fintype.card k))

/-- The perfectness input: `RΓ_c(U_k̄, D)` is perfect over every finite ring `R`, for every
sheaf `D` of `R`-modules on `U_étale` locally constant with finite projective values. -/
abbrev LissePerfectness : Prop :=
  ∀ (R : Type) [Ring R] [Finite R] (D : EtaleModules.{u, 0} R U),
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant R U.smallEtaleTopology D →
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} R pU J kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D)))

include hcop in
/-- **The trace of `π_U^*` on `RΓ_c(U_k̄, ℱ)` vanishes for a lisse sheaf `ℱ` on a smooth curve
`U` without rational points**, `ℱ` being locally constant with finite projective values over a
finite ring `Λ` of cardinality prime to that of `k`, granted the perfectness input. -/
@[sga "4½ Rapport 5.13" "5.13 A, special case"]
theorem exists_canonicalCompactSupportLefschetzNumber_eq_zero_of_lisse
    [IsEmpty (rationalPoints pU)] (hP : LissePerfectness J kbar)
    (F : EtaleModules.{u, 0} Λ U)
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ U.smallEtaleTopology F) :
    ∃ hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ pU J kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F))),
      canonicalCompactSupportLefschetzNumber.{u, 0} Λ pU J kbar p q hcard
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) hX = 0 := by
  have : IsNormal U := isNormal_of_smooth_over_field pU
  have hX : IsGeometricallyUnibranch U := isGeometricallyUnibranch_of_isNormal
  have : IsIntegral U := IsCurve.toIsVariety.toIsIntegral (k := k) (f := pU)
  have : Nonempty U := inferInstance
  let x : GeometricPoint U := GeometricPoint.ofPoint U (Classical.arbitrary U)
  obtain ⟨H, _, _, G, M, _, _, ρ, hMfin, hGfin, hGconn, ⟨eF⟩⟩ :=
    exists_etaleGaloisCovering_iso_descentSheaf hX x F
      (Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_isFiniteProjectiveLocallyConstant Λ _ hF)
  have := hMfin
  have := hGfin
  have := hGconn
  have : Module.Projective Λ M := G.moduleProjective_of_iso_descentSheaf.{u, 0, 0, 0} Λ M ρ F hF eF
  have hperfD : ∀ (ℓ n : ℕ) [Fact ℓ.Prime] [NeZero (ℓ ^ n)],
      StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))))) := by
    intro ℓ n _ _
    have : Module.Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H)
        (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ n)) H)) :=
      Module.Finite.equiv ULift.moduleEquiv.symm
    have : Module.Projective (MonoidAlgebra (ZMod (ℓ ^ n)) H)
        (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ n)) H)) :=
      Module.Projective.of_equiv ULift.moduleEquiv.symm
    exact hP _ _ (G.isFiniteProjectiveLocallyConstant_descentSheaf _ _ _)
  obtain ⟨hD, hz⟩ := exists_canonicalCompactSupportLefschetzNumber_descentSheaf_eq_zero J kbar p q
    hcard hcop G hperfD M ρ
  have hX' := isPerfect_compactSupportFrobeniusCohomology_of_iso Λ _ J kbar
    ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).mapIso eF).symm hD
  exact ⟨hX', (canonicalCompactSupportLefschetzNumber_congr Λ J kbar p q hcard
    ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).mapIso eF) hX' hD).trans hz⟩

include hcop in
/-- **The trace formula for a bounded complex of lisse sheaves on a smooth curve without
rational points** (the case of [Stacks, Tag 03UG] to which Step 3 reduces), granted the
perfectness input: both sides vanish. -/
theorem canonicalTraceFormula_of_lisse_of_isEmpty [IsEmpty (rationalPoints pU)]
    (hP : LissePerfectness J kbar) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U)) (a b : ℤ)
    [K.obj.IsStrictlyGE a] [K.obj.IsStrictlyLE b]
    (hK : ∀ n, Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ U.smallEtaleTopology
      (K.obj.X n)) :
    CanonicalTraceFormula Λ kbar p q hcard pU J K := by
  choose h hz using fun n =>
    exists_canonicalCompactSupportLefschetzNumber_eq_zero_of_lisse J kbar p q hcard hcop hP
      (K.obj.X n) (hK n)
  obtain ⟨hX, hsum⟩ := canonicalCompactSupportLefschetzNumber_eq_sum_single Λ J kbar p q hcard K
    a b h
  refine ⟨hX, fun x => isEmptyElim x, ?_⟩
  rw [hsum, finsum_of_isEmpty]
  exact Finset.sum_eq_zero fun n _ => by rw [hz n, smul_zero]

end Lisse

end Stacks.EtaleCohomology

end
