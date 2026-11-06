module

public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyFieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DegreeTwoCocyclesOfDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.TorsionModuleAlgebra
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DeJongConjectureFlatness
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GenusZeroSimplyConnected

/-!
# Flatness of the deformation ring of `ρ₀` from `H ²(π₁(X_k̄), ad⁰ ρ₀) = 0` in positive genus

`AlgebraicGeometry.flat_of_isUniversalFixedDeterminantDeformation_of_vanishesTwo` derives the
flatness half of [Stacks, Tag 03W1] from the cochain-level vanishing of `H ²(π₁(X_k̄), ad⁰)`. This
file supplies that input in two cases:

* if `X_k̄` has genus `0`, then `π₁(X_k̄)` is trivial
  (`AlgebraicGeometry.subsingleton_etaleFundamentalGroup_of_genus_eq_zero`), and there is nothing
  to prove;
* otherwise it follows from the vanishing of the derived-functor group
  `H ²(π₁(X_k̄), ad⁰)` of [Stacks, Tag 04JR], by
  `Stacks.GroupCohomology.vanishesTwo_of_isZero_continuousGroupCohomology_two`.

## Main definitions

* `Deformation.AdZero.continuousGModule`: `ad⁰ ρ` as a discrete `G`-module, its carrier lifted to
  the universe of `G`.

## Main results

* `flat_of_isUniversalFixedDeterminantDeformation_of_isZero_continuousGroupCohomology`:
  flatness, given `H ²(π₁(X_k̄), ad⁰) = 0` when `X_k̄` has positive genus.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Stacks.GroupCohomology
open scoped PowerSeries.WithPiTopology Stacks.DiscreteModuleTopology

universe u v

namespace Deformation.AdZero

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n ℓ : ℕ} [Fact ℓ.Prime]

/-- `ad⁰ ρ` is discrete after lifting its carrier to the universe of `G`. -/
theorem isContinuous_ulift (ρ : G →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)) :
    (actionOfDistribMulAction G (ULift.{u} (AdZero ρ.toMonoidHom))).IsContinuous := by
  rw [isContinuous_ofDistribMulAction_iff]
  intro X
  have h := hasOpenStabilizers (ρ := ρ) X.down
  have hset : {g : G | g • X = X} = {g : G | g • X.down = X.down} := by
    ext g
    exact ⟨fun h => congrArg ULift.down h, fun h => ULift.ext h⟩
  rw [hset]
  exact h

/-- **`ad⁰ ρ` as a discrete `G`-module**, its carrier lifted to the universe of `G`. -/
def continuousGModule (ρ : G →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ)) :
    ContinuousGModule.{u, u} G :=
  ofDistribMulAction (isContinuous_ulift ρ)

/-- The cochain-level vanishing for the discrete `G`-module `ad⁰ ρ` is the one for `ad⁰ ρ`. -/
theorem vanishesTwo_of_continuousGModule (ρ : G →ₜ* Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (h : letI := carrierAction (continuousGModule ρ)
      VanishesTwo G (continuousGModule ρ).obj.obj.V) :
    VanishesTwo G (AdZero ρ.toMonoidHom) :=
  let := carrierAction (continuousGModule ρ)
  vanishesTwo_of_addEquiv (M := (continuousGModule ρ).obj.obj.V) AddEquiv.ulift
    (fun _ _ => rfl) h

end Deformation.AdZero

namespace AlgebraicGeometry

/-- **Flatness half of Stacks 03W1, given `H ²(π₁(X_k̄), ad⁰) = 0` in positive genus.** Let `X` be
a smooth, geometrically irreducible, projective curve over a finite field `k`, `k̄` an algebraic
closure of `k` with `X_k̄` connected, and `ρ₀ : π₁(X) → GLₙ(𝐅_ℓ)` continuous with `ℓ ≠ p`,
`ℓ ∤ n` and `ρ₀|_{π₁(X_k̄)}` absolutely irreducible. Assume de Jong's conjecture for `X` in every
rank. If, when `X_k̄` has positive genus, the continuous group cohomology
`H ²(π₁(X_k̄), ad⁰ ρ₀)` of [Stacks, Tag 04JR] vanishes, then the universal deformation ring of
`ρ₀` with determinant fixed to `δ` is flat over `ℤ_[ℓ]`. In genus `0` there is no condition,
`π₁(X_k̄)` being trivial. -/
theorem flat_of_isUniversalFixedDeterminantDeformation_of_isZero_continuousGroupCohomology
    (k kbar : Type u) [Field k] [Finite k] [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (p ℓ n : ℕ) [CharP k p] [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hn : ¬ ℓ ∣ n)
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] [IsProper f] [GeometricallyIrreducible f] [ConnectedSpace X]
    [ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (x : GeometricPoint (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))))
    (ρ₀ : EtaleFundamentalGroup X (x.map (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) →ₜ*
        Matrix.GeneralLinearGroup (Fin n) (ZMod ℓ))
    (δ : EtaleFundamentalGroup X (x.map (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) →ₜ* ℤ_[ℓ]ˣ)
    (hconj : ∀ (m : ℕ) (ρ : EtaleFundamentalGroup X (x.map (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) →ₜ*
        Matrix.GeneralLinearGroup (Fin m) (PowerSeries (ZMod ℓ))),
      (Set.range fun g : EtaleFundamentalGroup _ x => ρ (etaleFundamentalGroupMap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x g)).Finite)
    (hirred : Deformation.IsAbsolutelyIrreducible fun g : EtaleFundamentalGroup _ x =>
      ρ₀ (etaleFundamentalGroupMap (pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x g))
    (R : Type v) [CommRing R] [IsLocalRing R] [TopologicalSpace R] [Algebra ℤ_[ℓ] R]
    (reduce : R →+* ZMod ℓ)
    (ρuniv : EtaleFundamentalGroup X (x.map (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))) →ₜ*
        Matrix.GeneralLinearGroup (Fin n) R)
    (hR : Deformation.IsUniversalFixedDeterminantDeformation ℓ n _ ρ₀ δ R reduce ρuniv)
    (hH2 : 1 ≤ genus (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) →
      IsZero (continuousGroupCohomology.{u + 1, u + 1} (EtaleFundamentalGroup _ x) 2
        (Deformation.AdZero.continuousGModule (ρ₀.comp (etaleFundamentalGroupMap
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) x))))) :
    Module.Flat ℤ_[ℓ] R := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  refine flat_of_isUniversalFixedDeterminantDeformation_of_vanishesTwo k kbar p ℓ n hℓp hn X f x
    ρ₀ δ hconj hirred R reduce ρuniv hR ?_
  have := isCurve_pullback_snd k kbar f
  by_cases hg : genus (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k kbar)))) = 0
  · have := subsingleton_etaleFundamentalGroup_of_genus_eq_zero kbar _ hg x
    exact vanishesTwo_of_subsingleton _ _
  · have := compactSpace_etaleFundamentalGroup _ x
    have := totallyDisconnectedSpace_etaleFundamentalGroup _ x
    exact Deformation.AdZero.vanishesTwo_of_continuousGModule _
      (vanishesTwo_of_isZero_continuousGroupCohomology_two _ (hH2 (Nat.one_le_iff_ne_zero.2 hg)))

end AlgebraicGeometry

end
