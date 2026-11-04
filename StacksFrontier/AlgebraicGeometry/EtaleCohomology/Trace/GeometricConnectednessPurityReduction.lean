module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIFinalAssembly
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.ConnectedRelativeDimension

/-!
# The reduction of purity to geometrically connected `X`, up to the components of `X_k̄`

`Stacks.EtaleCohomology.LAdicSheaf.GeometricConnectednessPurityReductionInput` (an input of the
purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) asks for purity on `X`
connected, smooth and proper over a finite field, given purity for `X` geometrically connected of
pure relative dimension. A connected scheme smooth over a field has a pure relative dimension
(`AlgebraicGeometry.exists_smoothOfRelativeDimension_of_connectedSpace`); what remains is the
passage from `X_k̄` connected to `X_k̄` arbitrary, stated as
`Stacks.EtaleCohomology.LAdicSheaf.GeometricComponentsPurityReductionInput`.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.GeometricComponentsPurityReductionInput`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.geometricConnectednessPurityReductionInput_of_componentsInput`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
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

/-- **The reduction of purity to `X_k̄` connected** (input): for `X` connected, proper and smooth
of pure relative dimension `d` over a finite field `k`, purity holds given it for `X`
geometrically connected of pure relative dimension. (`X` is geometrically connected over the
finite field `k' = Γ(X, 𝒪_X)`; `X_k̄` is the disjoint union of the `[k' : k]` conjugates
`X ×_{k', σ} k̄`, permuted cyclically by the Frobenius of `k`, whose `[k' : k]`-th power is the
Frobenius of `k'` on each of them, and purity of weight `i` for a power is purity of weight
`i`.) -/
def LAdicSheaf.GeometricComponentsPurityReductionInput : Prop :=
  LAdicSheaf.GeometricPurity B ℓ →
    ∀ (k : Type u) [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
      [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q),
      ℓ ≠ p → ∀ (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
        [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsProper f] (d : ℕ)
        [SmoothOfRelativeDimension d f],
        LAdicSheaf.RepresentationPurityAt B ℓ X f kbar p q hcard

/-- **The reduction of purity to geometrically connected `X` of pure relative dimension**
(`Stacks.EtaleCohomology.LAdicSheaf.GeometricConnectednessPurityReductionInput`), given the
passage to `X_k̄` disconnected: a connected `X` smooth over `k` is smooth of pure relative
dimension (`AlgebraicGeometry.exists_smoothOfRelativeDimension_of_connectedSpace`). -/
theorem LAdicSheaf.geometricConnectednessPurityReductionInput_of_componentsInput
    (h : LAdicSheaf.GeometricComponentsPurityReductionInput B ℓ) :
    LAdicSheaf.GeometricConnectednessPurityReductionInput B ℓ := by
  intro hP k _ _ kbar _ _ _ p q _ _ hcard hℓ X _ _ f _ _ _ _ _
  obtain ⟨d, hd⟩ := exists_smoothOfRelativeDimension_of_connectedSpace f
  exact h hP k kbar p q hcard hℓ X f d

end Stacks.EtaleCohomology

end
