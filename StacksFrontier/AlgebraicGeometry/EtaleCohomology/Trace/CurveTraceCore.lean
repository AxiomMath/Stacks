module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DescentSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusTraceIso

/-!
# The trace vanishes on a curve without rational points

Let `U` be a smooth curve over a finite field `k` without `k`-rational points, `G : V ⟶ U` a
connected finite étale Galois covering with group `H`, `A = ℤ/ℓⁿ` with `ℓ` invertible in `k`, `Λ`
an `A`-algebra killed by `ℓ^m`, and `N` a finite `Λ`-module, finite projective over `Λ`, with an
action `ρ` of `H`. Then `Tr(π_U^* | RΓ_c(U_k̄, D(N))) = 0` for the descent sheaf `D(N)`, as soon as
`n ≥ m + v` whenever `ℓ^v` divides `#H`.

This is Steps 4 to 9 of the proof of [Stacks, Tag 03UG]:
* Steps 4 to 6: `D(N) ≅ Hom_{A[H]}(N^∨, D(A[H]))`
  (`AlgebraicGeometry.EtaleGaloisCovering.descentSheafHomIso`);
* Step 7: `Tr_Λ(π | RΓ_c(U, Hom_{A[H]}(N^∨, D(A[H])))) = Φ'♮(Tr_{A[H]}(π | RΓ_c(U, D(A[H]))))` for
  `Φ' = Hom_{A[H]}(N^∨, -)`, which is a hypothesis here, together with the perfectness of
  `RΓ_c(U, D(A[H]))` over `A[H]`;
* Steps 8 and 9: `Tr_{A[H]}(π | RΓ_c(U, D(A[H])))` dies in every quotient killed by `ℓ^m`
  (`map_perfectDerivedTrace_canonicalCompactSupportFrobenius_regularDescent_eq_zero_of_isPerfect`),
  and `Λ^♮` is killed by `ℓ^m`.

## Main results

* `perfectDerivedTrace_canonicalCompactSupportFrobenius_descentSheaf_eq_zero_of_hom`: the trace
  vanishes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived
open MonoidAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

namespace CategoryTheory.FilteredDerived

/-- The additive commutator quotient of a ring killed by `M` is killed by `M`. -/
theorem nsmul_additiveCommutatorQuotient_eq_zero {Λ : Type*} [Ring Λ] {M : ℕ} (h : (M : Λ) = 0)
    (y : AdditiveCommutatorQuotient Λ) : M • y = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul, h, zero_mul, QuotientAddGroup.mk_zero]

end CategoryTheory.FilteredDerived

namespace Stacks.EtaleCohomology

/-- **A ring killed by `M` is a `ℤ/N`-algebra for every multiple `N` of `M`**: the cast
`ℤ/N → Λ` is a ring morphism with central image. -/
@[instance_reducible]
def zmodAlgebraOfNatCastEqZero (Λ : Type*) [Ring Λ] {M N : ℕ} [NeZero N] (hM : (M : Λ) = 0)
    (hMN : M ∣ N) : Algebra (ZMod N) Λ :=
  haveI : CharP Λ (ringChar Λ) := ringChar.charP Λ
  have hdvd : ringChar Λ ∣ N := ((ringChar.spec Λ M).1 hM).trans hMN
  (ZMod.castHom hdvd Λ).toAlgebra' fun c x => by
    rw [← ZMod.natCast_zmod_val c, map_natCast]
    exact (Nat.cast_commute _ x).eq

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology

variable {k : Type u} [Field k] [Fintype k] [PerfectField k] {U : Scheme.{u}} {H : Type} [Group H]
  [Fintype H] {pU : U ⟶ Spec (.of k)} [IsCurve k pU] [Smooth pU]
  (J : CompactificationOf (Over.mk pU))
  (G : EtaleGaloisCovering U H) [IsFinite (G.cover.hom : G.cover.left ⟶ U)]
  [ConnectedSpace ((𝟭 Scheme).obj G.cover.left)]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ)
  [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- **The trace vanishes on a curve without rational points**: `Tr(π_U^* | RΓ_c(U_k̄, D(N))) = 0`
for the descent sheaf of a finite projective `Λ`-module `N` with an `H`-action along a Galois
covering of a curve without rational points, granted the perfectness of `RΓ_c(U_k̄, D(A[H]))`
over `A[H]` and the trace identity of Step 7 for `Φ' = Hom_{A[H]}(N^∨, -)`. -/
theorem perfectDerivedTrace_canonicalCompactSupportFrobenius_descentSheaf_eq_zero_of_hom
    [Algebra.IsAlgebraic k kbar] (ℓ n m : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) (hn : 1 ≤ n)
    [IsEmpty (rationalPoints pU)] {Λ : Type} [Ring Λ] [Algebra (ZMod (ℓ ^ n)) Λ]
    (hΛ : ((ℓ ^ m : ℕ) : Λ) = 0) (hnm : ∀ v : ℕ, ℓ ^ v ∣ Fintype.card H → m + v ≤ n)
    {N : Type (u + 1)} [AddCommGroup N] [Module Λ N] [Module (ZMod (ℓ ^ n)) N]
    [IsScalarTower (ZMod (ℓ ^ n)) Λ N] [Finite N] [Module.Finite Λ N] [Module.Projective Λ N]
    (ρ : H →* Module.End Λ N)
    (hperf : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))))))
    (h2a : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ pU J kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((etaleModuleHom (dualRepModule (A := ZMod (ℓ ^ n)) ρ)
            (dualRepRightAction (A := ZMod (ℓ ^ n)) ρ) U).obj
              (G.regularDescentSheaf (A := ZMod (ℓ ^ n))))))))
    (h2b : perfectDerivedTrace Λ ⟨_, h2a⟩ (DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, 0} Λ pU J kbar p q hcard
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            ((etaleModuleHom (dualRepModule (A := ZMod (ℓ ^ n)) ρ)
              (dualRepRightAction (A := ZMod (ℓ ^ n)) ρ) U).obj
                (G.regularDescentSheaf (A := ZMod (ℓ ^ n))))))) =
      functorTraceMap (homFunctor (dualRepModule (A := ZMod (ℓ ^ n)) ρ)
          (dualRepRightAction (A := ZMod (ℓ ^ n)) ρ)) (𝟙 _)
        (preservesFiniteProjective_homFunctor (n := ℓ ^ n) ρ)
        (perfectDerivedTrace (MonoidAlgebra (ZMod (ℓ ^ n)) H) ⟨_, hperf⟩
          (DerivedCategory.Plus.ι.map (canonicalCompactSupportFrobenius.{u, 0}
            (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar p q hcard
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))))))) :
    ∃ hF : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ pU J kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (G.descentSheaf.{u, 0, 0, u + 1} Λ N ρ)))),
      perfectDerivedTrace Λ ⟨_, hF⟩ (DerivedCategory.Plus.ι.map
        (canonicalCompactSupportFrobenius.{u, 0} Λ pU J kbar p q hcard
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (G.descentSheaf.{u, 0, 0, u + 1} Λ N ρ)))) = 0 := by
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let e := (Stacks.DerivedIndexing.singlePlusFunctor (EtaleModules.{u, 0} Λ U) 0).mapIso
    (G.descentSheafHomIso (n := ℓ ^ n) ρ)
  have hF := isPerfect_compactSupportFrobeniusCohomology_of_iso Λ pU J kbar e.symm h2a
  refine ⟨hF, ?_⟩
  rw [perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_of_iso Λ pU J kbar p q hcard e hF h2a,
    h2b]
  exact map_perfectDerivedTrace_canonicalCompactSupportFrobenius_regularDescent_eq_zero_of_isPerfect
    J G kbar p q hcard ℓ n hℓ hn hperf _ (nsmul_additiveCommutatorQuotient_eq_zero hΛ) hnm

end Stacks.EtaleCohomology

end
