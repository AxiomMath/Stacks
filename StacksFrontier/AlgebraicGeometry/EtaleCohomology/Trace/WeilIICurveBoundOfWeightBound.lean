module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IotaRealizableSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointwiseMixedSheaf
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitDescent

/-!
# The curve case of Weil II from the weight bound for lisse sheaves

The curve case of the weight bound of Weil II (Weil II 3.2.3,
`Stacks.EtaleCohomology.WeilIICurveBound`) is stated for the sheaf `ℱ_ρ` of a continuous
representation `ρ`, pointwise `ι`-mixed and `ι`-realizable. The sheaf `ℱ_ρ` is lisse, pointwise
`ι`-mixed and `ι`-realizable exactly when `ρ` is
(`Stacks.EtaleCohomology.LAdicSheaf.isPointwiseMixedOfWeightLE_representationSheaf_iff`,
`Stacks.EtaleCohomology.LAdicSheaf.isIotaRealizable_representationSheaf`), so the curve case
follows from the weight bound for lisse sheaves on every curve
(`Stacks.EtaleCohomology.LAdicSheaf.SatisfiesWeightBound`). This is the last step of the reduction
of the curve case to opens of the affine line, in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.weilIICurveBound_of_satisfiesWeightBound`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-- **The curve case of Weil II from the weight bound for lisse sheaves on curves**: if every
smooth separated geometrically connected curve over a finite field satisfies the weight bound for
lisse ℓ-adic sheaves (`ℓ` prime to the characteristic), then `WeilIICurveBound` holds, by
applying it to `ℱ_ρ`. -/
public theorem weilIICurveBound_of_satisfiesWeightBound
    (hS : ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
      [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
        ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
          (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
          (SmallEtale.topology B S.1 S.property)
          (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
      [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
        HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
          (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
      [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
      [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
      (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
      (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
      [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
      (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
      (ι : ℚ_[ℓ] →+* ℂ), LAdicSheaf.SatisfiesWeightBound B ℓ kbar p n hcard ι U f) :
    WeilIICurveBound.{u} := by
  intro B U ℓ i1 i2 _ _ _ _ k _ _ f _ _ _ _ j kbar _ _ _ _ p n _ _ hcard hℓ x r ρ hρ ι w hmix hreal
    i _ z hz
  have i3 : ∀ (m : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (m + 1)))) := fun m T =>
    AlgebraicGeometry.hasWeakSheafify_smallEtale_of_scheme B
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (m + 1)))) T
  have h := @hS B U ℓ i1 i2 i3 _ _ _ k _ _ f _ _ _ _ kbar _ _ _ _ p n _ _ hcard hℓ ι j
    (LAdicSheaf.representationSheaf B U x ρ hρ) w
    (LAdicSheaf.representationSheaf_isLisse B U x ρ hρ)
    ((LAdicSheaf.isPointwiseMixedOfWeightLE_representationSheaf_iff B U ℓ f x ρ hρ (p ^ n) ι w).2
      hmix)
    (LAdicSheaf.isIotaRealizable_representationSheaf B U ℓ f x ρ hρ hreal) i
  exact h z hz

end Stacks.EtaleCohomology

end
