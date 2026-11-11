module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisPoincareDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PoincareDualityHypothesesNotProjectiveLine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PoincarePairingDegreeTwoNatCard

/-!
# Tag 03VM, homological derived clause: `RΓ_c(X_k̄, ℱ_ρ) = LH₀(π₁(X_k̄, η̄), M(-1))` in `D(Λ[[Ẑ]])`

Let `X` be a geometrically connected smooth curve over a field `k`, `k̄` an algebraic closure of
`k` separable over `k` (for `k` finite this is automatic), `Λ` a finite ring (not necessarily
commutative) with `#Λ` invertible in `k`, and suppose `X_k̄ ≇ 𝐏¹_k̄`. For a finite `Λ`-module `M`
with a continuous action `ρ` of `π₁(X, η̄)`, [Stacks, Tag 03VM] asserts

`RΓ_c(X_k̄, ℱ_ρ) = LH₀(π₁(X_k̄, η̄), M(-1)) = M(-1) ⊗^L_{Λ[[π₁(X_k̄, η̄)]]} Λ` in `D(Λ[[Ẑ]])`,

`Ẑ = Gal(k̄/k)` for `k` finite. This file states it as a natural isomorphism
(`AlgebraicGeometry.compactSupportDerivedHomologyNatIso`)

`RΓ^{Gal}_c(X_k̄, ℱ_ρ) ≅ LH₀(π₁(X_k̄, η̄), M(-1))[-2]`

of functors from finite `Λ`-modules with continuous `π₁(X, η̄)`-action to the derived category of
`Λ[[Aut(k̄/k)]]`-modules, where:

* the left side is `AlgebraicGeometry.geometricGaloisCompactSupportDerived`, the
  Galois-equivariant `RΓ_c(X_k̄, ℱ_ρ) = RΓ(X̄_k̄, j_! ℱ_ρ)` of Remark 03UI (2), a complex of
  discrete `Λ[Aut(k̄/k)]`-modules; forgetting the action it is the base's
  `galoisCompactSupportCohomology` and the action of `σ` is `galoisCompactSupportAction σ`;
* `M(-1) = Hom(μ_n(k̄), M)` (`AlgebraicGeometry.geometricTateTwist`, `n = #Λ`), on which `σ` acts
  as `χ_cycl(σ)⁻¹ σ` when the geometric action is trivial, the twist of Section 03VJ;
* `LH₀(G, -)` (`AlgebraicGeometry.geometricDerivedHomology`) is the derived functor of the
  coinvariants of `G = π₁(X_k̄, η̄)` in the continuous (pseudocompact) sense, with its residual
  action of `π₁(X)/G = Aut(k̄/k)`: `LH₀(G, N) = (RH⁰(G, N^∨))^∨`, the dual of the derived
  invariants of the discrete dual (Section 03VI, "trivial duality"). Forgetting the action its
  cohomology is `H^{-i}(LH₀(G, N)) = H_i(G, N)`
  (`Stacks.ContinuousCohomology.kernelDerivedHomologyForgetHomologyIso`), so `LH₀` is a derived
  version of the coinvariants. The notes on homology of the source (`trace.tex`, lines
  3163–3169) write `H_i(G, N) = Tor_i^{Λ[[G]]}(N, Λ)`; in the pseudocompact sense this is what is
  used here. Abstract `Tor` over the ring `Λ[[G]]` agrees with it for `G` topologically finitely
  generated, which `π₁(X_k̄)` of an affine curve in characteristic `p` is not (see
  `StacksFrontier/AlgebraicGeometry/ContinuousCohomology/KernelDerivedHomology.lean`);
* the shift `[-2]` is implicit in the source, which writes `=` for complexes concentrated in
  degrees `[0, 2]` and `[-2, 0]`: in degree `2 - i` it is `H^{2-i}_c(X_k̄, ℱ_ρ) = H_i(G, M)(-1)`.

The isomorphism is the derived Poincaré duality
(`AlgebraicGeometry.galoisCompactSupportPoincareDualityNatIso`) followed by the group-theoretic
identification `AlgebraicGeometry.geometricDerivedHomologyTwistGaloisIso`. That identification
uses the cohomological derived clause of 03VM in its Galois form
(`AlgebraicGeometry.geometricGaloisDerivedInvariantsIso`, at `Λᵐᵒᵖ`) and
`M(-1)^∨ = Hom(M, μ_n)` (`AlgebraicGeometry.geometricTateTwistDualNatIso`). The hypotheses
`hEff` and `hcoeff` of the duality are discharged under `X_k̄ ≇ 𝐏¹_k̄` by the lemmas
`elementwiseEffaceable_geometricRepresentationCohomology_of_not_iso_projectiveLine` and
`coeffaceable_compactSupportRepresentationHomology_of_not_iso_projectiveLine` in the namespace
`AlgebraicGeometry`. The base case `hbase` is
`AlgebraicGeometry.isIso_homologyMap_poincarePairing_two`; the statement with `hbase` as a
hypothesis is `AlgebraicGeometry.compactSupportDerivedHomologyNatIso`, and the one without it is
`AlgebraicGeometry.compactSupportDerivedHomologyIso`. Over an arbitrary field, where `k̄` need not
be separable over `k`, the clause is
`AlgebraicGeometry.compactSupportDerivedHomologyIsoOfAlgClosure`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/DerivedVersionsAlgClosure.lean`).

## Main results

* `AlgebraicGeometry.compactSupportDerivedHomologyIso`: the derived clause, at the source's
  hypotheses.
* `AlgebraicGeometry.compactSupportDerivedHomologyNatIso`: the same, built from any proof of the
  base case of the Poincaré pairing.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology
open Stacks.ContinuousCohomology Stacks.AbelianInternalHom Stacks.GroupHomology

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (K : Type u) [Field K] [Algebra k K]
  [IsAlgClosure k K] [Algebra.IsSeparable k K]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) K)) (Λ : Type) [Ring Λ] [Finite Λ]
  (j : CompactificationOf (Over.mk f))

/-- **Tag 03VM, homological derived clause: `RΓ_c(X_k̄, ℱ_ρ) ≅ LH₀(π₁(X_k̄, η̄), M(-1))[-2]`** in
the derived category of `Λ[[Aut(k̄/k)]]`-modules, naturally in `ρ`, for `X` a geometrically
connected smooth curve over `k` with `X_k̄ ≇ 𝐏¹_k̄`, `k̄` an algebraic closure of `k` separable
over `k`, `Λ` a finite ring with `#Λ` invertible in `k`; the base case `hbase` of the derived
Poincaré duality is assumed. See the module docstring for the reading of each side. -/
def compactSupportDerivedHomologyNatIso (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : fieldBaseChange (Over.mk f) K ≅ projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (specAlgebraMap k K))
    (hbase : letI := connectedSpace_of_isCurve B X f
      haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
      haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
      haveI : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
      letI := zmodNatCardAlgebra Λ
      ∀ (K₀ : CochainComplex.InjectiveResolution
          ((CochainComplex.singleFunctor _ 0).obj
            ((etaleModuleExtensionByZero (ZMod (Nat.card Λ)) j.immersion).obj
              ((representationSheaf B X _ (ZMod (Nat.card Λ))).obj
                (cyclotomicContinuousModule B X f K y (Nat.card Λ))))))
        [K₀.cocomplex.IsStrictlyGE 0]
        (t : (show CochainComplex
              (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
            galoisHomOpG (Over.mk j.toBase) K
              (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀)) ⟶
            traceTarget.{u, u + 1} (K ≃ₐ[k] K) 2),
        DerivedCategory.Q.map t =
          @derivedTraceOfIsLE.{u, u + 1} (K ≃ₐ[k] K) _ _ _
            (show CochainComplex
                (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K)) ℤ from
              galoisHomOpG (Over.mk j.toBase) K
                (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀)) 2
            (isLE_galoisHomOpG_cyclotomic B X f K y (Nat.card Λ) j K₀)
            (galoisHomOpCyclotomicTrace B X f K y (Nat.card Λ) j K₀
              (isUnit_natCard_of_isUnit_field K Λ hΛ)) ≫
          (@DerivedCategory.Q
            (Stacks.Injectives.ContinuousModule.{0, u, max u (u + 1)} ℤ (K ≃ₐ[k] K))
            _ _ (HasDerivedCategory.standard _)).map (traceTargetι.{u, u + 1} (K ≃ₐ[k] K) 2) →
        ∀ i : PoincareIndex B X
            (y.map (fieldBaseChangeObjProj B X f K
              (contains_fieldBaseChange_of_isCurve B X f K)).hom) Λ f j,
          IsIso (HomologicalComplex.homologyMap
            (internalHomComplexOfPairing (poincarePairing K
              (cyclotomicIntResolution B X f K y (Nat.card Λ) j K₀) t i)) 2)) :
    letI := connectedSpace_of_isCurve B X f
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
    geometricGaloisCompactSupportDerived B X f K y Λ j ≅
      (geometricTateTwist B X f K y Λ ⋙ geometricDerivedHomology B X f K y Λ) ⋙
        shiftFunctor _ (-2 : ℤ) :=
  let := connectedSpace_of_isCurve B X f
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  have : IsGalois k K := { to_isSeparable := inferInstance, to_normal := inferInstance }
  let := zmodNatCardAlgebra Λ
  have hΛop : IsUnit ((Nat.card Λᵐᵒᵖ : ℕ) : k) := by
    rwa [Nat.card_congr MulOpposite.opEquiv.symm]
  galoisCompactSupportPoincareDualityNatIso B X f K y Λ j hΛ
      (elementwiseEffaceable_geometricRepresentationCohomology_of_not_iso_projectiveLine
        B X f K Λᵐᵒᵖ y hΛop hP)
      (coeffaceable_compactSupportRepresentationHomology_of_not_iso_projectiveLine
        B X f K Λ y j hΛ hP) hbase ≪≫
    Functor.isoWhiskerRight (geometricDerivedHomologyTwistGaloisIso B X f K y Λ hΛ hP).symm _

/-- **Tag 03VM, homological derived clause: `RΓ_c(X_k̄, ℱ_ρ) ≅ LH₀(π₁(X_k̄, η̄), M(-1))[-2]`** in
the derived category of `Λ[[Aut(k̄/k)]]`-modules (`Aut(k̄/k) ≅ Ẑ` for `k` finite), naturally in
the finite `Λ`-module `M` with continuous action `ρ` of `π₁(X, η̄)`. Here `X` is a geometrically
connected smooth curve over `k` with `X_k̄ ≇ 𝐏¹_k̄`, `k̄` is an algebraic closure of `k` separable
over `k` (automatic for `k` finite), and `Λ` is a finite ring with `#Λ` invertible in `k`. The left
side is the Galois-equivariant `RΓ_c` of Remark 03UI (2), `M(-1) = Hom(μ_n(k̄), M)`, and `LH₀` is
the derived functor of the coinvariants in the continuous sense, `M ⊗^L_{Λ[[π₁(X_k̄)]]} Λ` computed
on pseudocompact modules (see the module docstring). The case of an arbitrary field `k`, where `k̄`
need not be separable over `k`, is `AlgebraicGeometry.compactSupportDerivedHomologyIsoOfAlgClosure`,
which reduces to this one over the perfect closure of `k` in `k̄`. -/
def compactSupportDerivedHomologyIso (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hP : ¬ ∃ e : fieldBaseChange (Over.mk f) K ≅ projectiveSpaceOver 1 (Spec (.of K)),
      e.hom ≫ (projectiveSpaceOver 1 (Spec (.of K)) ↘ Spec (.of K)) =
        pullback.snd (Over.mk f).hom (specAlgebraMap k K)) :
    letI := connectedSpace_of_isCurve B X f
    haveI : IsAlgClosed K := IsAlgClosure.isAlgClosed k
    haveI : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
    geometricGaloisCompactSupportDerived B X f K y Λ j ≅
      (geometricTateTwist B X f K y Λ ⋙ geometricDerivedHomology B X f K y Λ) ⋙
        shiftFunctor _ (-2 : ℤ) :=
  compactSupportDerivedHomologyNatIso B X f K y Λ j hΛ hP
    (isIso_homologyMap_poincarePairing_two B X f K y Λ j hΛ)

end AlgebraicGeometry

end
