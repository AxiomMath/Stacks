module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveBound

/-!
# The weight bound of Weil II on open subschemes of the affine line

The weight bound of Weil II on curves (Weil II 3.2.3; Kedlaya, *Fourier transforms and p-adic
Weil II*, §6), stated for the curves `U` over a finite field `k` which are affine and come with an
open immersion `U ⟶ 𝔸¹_k` over `k`.

## Main definitions

* `Stacks.EtaleCohomology.WeilIICurveBoundOpenAffineLine`: the statement of
  `Stacks.EtaleCohomology.WeilIICurveBound` for affine opens of the affine line.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-- The weight bound of Weil II on affine opens of the affine line: the statement of
`Stacks.EtaleCohomology.WeilIICurveBound` for the curves `U` over `k` which are affine and admit
an open immersion `e : U ⟶ 𝔸¹_k = Spec k[T]` over `k`. -/
public def WeilIICurveBoundOpenAffineLine : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1) {r : ℕ} (ρ : EtaleFundamentalGroup U.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ) (ι : ℚ_[ℓ] →+* ℂ) (w : ℤ),
    IsPointwiseMixedOfWeightLE f x (p ^ n) ι w ρ → IsIotaRealizable f x ι ρ →
    ∀ (i : ℤ) [FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x ρ hρ) i)] (z : ℂ),
      ((ModuleCat.Hom.hom (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B U ℓ f j kbar
        p n hcard (LAdicSheaf.representationSheaf B U x ρ hρ) i)).charpoly.map ι).IsRoot z →
      ∃ w' : ℤ, w' ≤ w + i ∧ ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ ((w' : ℝ) / 2)

end Stacks.EtaleCohomology

end
