module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveFiniteLevelCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDevissage

/-!
# Finiteness of compactly supported ℓ-adic cohomology in dimension at most one

For a scheme `X` separated of finite type over a finite field `k` with `topologicalKrullDim X ≤ 1`
and an algebraically closed extension `k̄` of `k`, the finite levels `Hⁱ_c(X_k̄, Fₙ)` of every
ℓ-adic sheaf `F` are finite (in the namespace `Stacks.EtaleCohomology.LAdicSheaf`,
`finite_geometricCompactSupportPadicCohomology_padicLevel_of_topologicalKrullDim_le_one`) and
`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is finite dimensional
(`finite_rationalGeometricCompactlySupportedCohomology_of_topologicalKrullDim_le_one`). Together
they are the finiteness input `Stacks.EtaleCohomology.LAdicSheaf.HasFiniteCompactSupportCohomology`
of the dévissage of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) on curves.

## Main results

* `LAdicSheaf.hasFiniteCompactSupportCohomology_of_topologicalKrullDim_le_one`: every ℓ-adic
  sheaf on such a scheme has finite compactly supported cohomology.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

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
  {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

include p q hcard in
/-- **Finiteness of compactly supported ℓ-adic cohomology in dimension at most one** (Tag 03V3
at the finite levels and its ℓ-adic consequence, for curves). -/
public theorem LAdicSheaf.hasFiniteCompactSupportCohomology_of_topologicalKrullDim_le_one
    (X : B.Scheme) [IsNoetherian X.1] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated f] (hdim : topologicalKrullDim X.1 ≤ 1) :
    LAdicSheaf.HasFiniteCompactSupportCohomology B ℓ kbar X f := by
  intro j F i
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  refine ⟨
    LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_topologicalKrullDim_le_one
      B X ℓ f j kbar p q hcard hdim F i, fun n => ?_⟩
  exact finite_geometricCompactSupportPadicCohomology_padicLevel_of_topologicalKrullDim_le_one
    B X ℓ f j kbar hdim F i n.unop

end Stacks.EtaleCohomology

end
