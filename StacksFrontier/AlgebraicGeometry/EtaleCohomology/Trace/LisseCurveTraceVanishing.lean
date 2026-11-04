module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckConjugacyTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckPerfectness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroInjectiveStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaOpenClosedDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.RegularDescentDualHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoefficientChange
public import StacksFrontier.Algebra.Module.GroupAlgebraDualHomProjective
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.CentralIdempotentTrace

/-!
# Vanishing of the Frobenius trace of a lisse sheaf on a curve without rational points

Steps 4–9 of the proof of [Stacks, Tag 03UG]. Let `k` be a finite field, `U` a smooth curve over
`k` without `k`-rational points, `Λ` a finite ring killed by `ℓ^m` for a prime `ℓ` invertible in
`k`, and `ℱ` a sheaf of `Λ`-modules on `U_étale` which is the descent sheaf `D(M)` of a finite
projective `Λ`-module `M` with an action of the group `H` of a connected finite étale Galois
covering `G : V ⟶ U`. Then `Tr(π_U^* | RΓ_c(U_k̄, ℱ)) = 0` in `Λ^♮`, granted perfectness of
`RΓ_c(U_k̄, D(A[H]))` over `A[H]`, `A = ℤ/ℓⁿ`, `n = m + #H`.

## Main definitions

* `Stacks.EtaleCohomology.descentExponent`: the exponent `m + #H`.
* `Stacks.EtaleCohomology.descentZModModule`: the `ℤ/ℓⁿ`-module structure of `M`.

## Main results

* `Stacks.EtaleCohomology.canonicalCompactSupportLefschetzNumber_eq_zero_of_descentSheaf`: the
  trace of `π_U^*` on `RΓ_c(U_k̄, ℱ)` vanishes.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 4–9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived
open Stacks.GroupAlgebraDual

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] [Fintype k] {U : Scheme.{u}} {pU : U ⟶ Spec (.of k)}
  [IsCurve k pU] [Smooth pU] (J : CompactificationOf (Over.mk pU))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)
  {Λ : Type} [Ring Λ] [Finite Λ] (ℓ m : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
  (e : Λ) (hc : ∀ a : Λ, a * e = e * a) (hℓe : ((ℓ ^ m : ℕ) : Λ) * e = 0)
  {H : Type} [Group H] [Fintype H] (G : EtaleGaloisCovering U H)
  [ConnectedSpace G.cover.left] [IsFinite (G.cover.hom : G.cover.left ⟶ U)]
  {M : Type (u + 1)} [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] [Module.Projective Λ M]
  (ρ : H →* Module.End Λ M)

/-- The exponent `m + #H`. -/
abbrev descentExponent : ℕ := m + Fintype.card H

omit [Finite Λ] [Fact (Nat.Prime ℓ)] [Group H] [Module.Finite Λ M] [Module.Projective Λ M] in
include hℓe in
/-- If `ℓ^m e = 0` and `e` acts trivially on `M`, then `ℓ ^ (m + #H)` kills `M`. -/
lemma nsmul_descentExponent_eq_zero (heM : ∀ x : M, e • x = x) (x : M) :
    (ℓ ^ descentExponent m (H := H)) • x = 0 := by
  have h0 : ((ℓ ^ descentExponent m (H := H) : ℕ) : Λ) * e = 0 := by
    rw [descentExponent, add_comm, pow_add, Nat.cast_mul, mul_assoc, hℓe, mul_zero]
  rw [← heM x, ← Nat.cast_smul_eq_nsmul Λ, smul_smul, h0, zero_smul]

/-- The `ℤ/ℓⁿ`-module structure of `M`, `ℓⁿ e` vanishing and `e` acting trivially on `M`. -/
abbrev descentZModModule (heM : ∀ x : M, e • x = x) :
    Module (ZMod (ℓ ^ descentExponent m (H := H))) M :=
  haveI : NeZero (ℓ ^ descentExponent m (H := H)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  AddCommGroup.zmodModule (nsmul_descentExponent_eq_zero ℓ m e hℓe heM)

include hℓ hc hℓe in
/-- **Steps 4–9 of [Stacks, Tag 03UG]**: for a descent sheaf `ℱ ≅ D(M)` along a connected finite
Galois covering of a smooth curve `U` without rational points, with `M` finite projective over a
finite ring `Λ` on which a central `e` with `ℓ^m e = 0` acts trivially, `RΓ_c(U_k̄, ℱ)` is perfect
and `Tr(π_U^* | RΓ_c(U_k̄, ℱ)) = 0`, granted perfectness of `RΓ_c(U_k̄, D(A[H]))` over `A[H]`,
`A = ℤ/ℓⁿ`, for any `n ≥ 1` with `m + v ≤ n` whenever `ℓ^v ∣ #H`. -/
theorem canonicalCompactSupportLefschetzNumber_eq_zero_of_descentSheaf
    (n : ℕ) [NeZero (ℓ ^ n)] [Module (ZMod (ℓ ^ n)) M] (hn : 1 ≤ n)
    (hnm : ∀ v : ℕ, ℓ ^ v ∣ Fintype.card H → m + v ≤ n) (heM : ∀ x : M, e • x = x)
    [IsEmpty (rationalPoints pU)] (F : EtaleModules.{u, 0} Λ U)
    (eF : F ≅ G.descentSheaf.{u, 0, 0, u + 1} Λ M ρ)
    (hperf : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0}
        (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (G.regularDescentSheaf (A := ZMod (ℓ ^ n))))))) :
    ∃ hX : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        (compactSupportFrobeniusCohomology.{u, 0} Λ pU J kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F))),
      canonicalCompactSupportLefschetzNumber.{u, 0} Λ pU J kbar p q hcard
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) hX = 0 := by
  have : Finite M := Module.finite_of_finite Λ
  have : ConnectedSpace ((𝟭 Scheme).obj G.cover.left) := ‹ConnectedSpace G.cover.left›
  let D := G.regularDescentSheaf (A := ZMod (ℓ ^ n))
  let Y := Over.mk J.toBase
  let L := (etaleModuleExtensionByZero.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
      J.immersion).mapCochainComplexPlus.obj
    ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj D)
  have hΦ : PreservesFiniteProjective.{0, u + 1} (dualHomFunctor (ℓ ^ n) ρ) :=
    preservesFiniteProjective_bimoduleHom (ℓ ^ n) ρ
  have hR : Module.Baer (MonoidAlgebra (ZMod (ℓ ^ n)) H) (MonoidAlgebra (ZMod (ℓ ^ n)) H) :=
    baer_monoidAlgebra_zmod (ℓ ^ n)
  have hL := moduleInjective_sheafFiber_extensionByZeroComplex Y kbar J.immersion D
    (fun Ω _ _ s => moduleInjective_sheafFiber_regularDescentSheaf G (ℓ ^ n) _)
  obtain ⟨hperf', htr⟩ := perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_bimoduleHom
    (Dual (ℓ ^ n) ρ) Y kbar p q hcard hR hΦ L hL hperf
  have : IsProper (Over.mk J.toBase).hom := inferInstanceAs (IsProper J.toBase)
  have hjU : J.immersion ≫ (Over.mk J.toBase).hom = pU := Over.w J.obj.hom
  obtain ⟨C⟩ := nonempty_coverCompactification k pU (Over.mk J.toBase).hom J.immersion hjU
    (G.cover.hom : G.cover.left ⟶ U)
  have hzero := map_perfectDerivedTrace_canonicalCompactSupportFrobenius_regularDescent_eq_zero J G
    C kbar p q hcard ℓ n hℓ hn hperf
    (isPerfect_coverCompactification_extensionByZeroConstant C kbar ℓ n)
    (isPerfect_coverCompactification_selfMapCohomology C kbar ℓ n)
    (isPerfect_coverCompactification_boundarySelfMapCohomology C kbar ℓ n)
    (isPerfect_baseSectionsComplex_zmodConstant kbar ℓ n hℓ)
    ((centralMulQuotient e hc).rangeRestrict.comp
      (functorTraceMap (dualHomFunctor (ℓ ^ n) ρ) (𝟙 _) hΦ))
    (m := m) (fun y => by
      obtain ⟨_, z, rfl⟩ := y
      exact Subtype.ext (nsmul_centralMulQuotient_eq_zero e hc hℓe z)) hnm
  have hfix : ∀ (X : ModuleCat.{max 0 (u + 1)} (MonoidAlgebra (ZMod (ℓ ^ n)) H))
      (x : (dualHomFunctor (ℓ ^ n) ρ).obj X), e • x = x := fun X x =>
    (ModuleCat.BimoduleHom.ext_iff' _).2 fun φ =>
      (ModuleCat.BimoduleHom.smul_apply _ e x φ).trans (congrArg _ (ext_dual fun m' => by
        rw [toForm_op_smul, MulOpposite.unop_op, heM]))
  let E : (etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) ≅
      (etaleModuleCoefficient (dualHomFunctor (ℓ ^ n) ρ) Y.left).mapCochainComplexPlus.obj L :=
    (etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.mapIso
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).mapIso
          (eF ≪≫ (G.dualHomDescentIso (ℓ ^ n) Λ ρ).symm)) ≪≫
      (singlePlusFunctorCompMapCochainComplexPlusIso
        (etaleModuleExtensionByZero.{u, 0} Λ J.immersion)).app _ ≪≫
      (Stacks.DerivedIndexing.singlePlusFunctor _ 0).mapIso
        ((extensionByZeroCoefficientIso J.immersion (dualHomFunctor (ℓ ^ n) ρ)).app D) ≪≫
      ((singlePlusFunctorCompMapCochainComplexPlusIso
        (etaleModuleCoefficient (dualHomFunctor (ℓ ^ n) ρ) Y.left)).app _).symm ≪≫
      (etaleModuleCoefficient (dualHomFunctor (ℓ ^ n) ρ) Y.left).mapCochainComplexPlus.mapIso
        ((singlePlusFunctorCompMapCochainComplexPlusIso
          (etaleModuleExtensionByZero.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
            J.immersion)).app D).symm
  have hX := isPerfect_frobeniusRestriction_of_iso Λ Y kbar E.symm hperf'
  refine ⟨hX, ?_⟩
  refine (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_iso Λ Y kbar p q hcard E hX
    hperf').trans (htr.trans ?_)
  rw [← centralMulQuotient_functorTraceMap (dualHomFunctor (ℓ ^ n) ρ) (𝟙 _) hΦ e hc hfix]
  exact congrArg Subtype.val hzero

end Stacks.EtaleCohomology

end
