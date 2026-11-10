module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IdempotentCoefficientReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StagePieceSheafComparison
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reduction of [Stacks, Tag 03UZ] to the strata of a closed filtration

Let `X` be a scheme of finite type over a finite field `k`, `F` a constructible flat sheaf of
`Λ`-modules, and `X = Y 0 ⊇ Y 1 ⊇ ⋯ ⊇ Y n = ∅` a closed filtration, with open strata
`Z i = Y i \ Y (i + 1)`. If on every stratum, for every compactification, `RΓ_c(Z i_k̄, F|_{Z i})`
is perfect and `det(1 - π^* T | RΓ_c(Z i_k̄, F|_{Z i})) · L(Z i, F|_{Z i}) = 1`, then the same
holds on `X`, for every compactification: the characteristic series is multiplicative along the
filtration
(`Stacks.EtaleCohomology.compactSupportCharSeriesInverts_of_closedFiltration`) and so is the
L-function (`Stacks.EtaleCohomology.lFunctionOfFiniteProjectiveStalks_eq_prod_stratification`).

## Main definitions

* `Stacks.EtaleCohomology.stageLFunction`: the L-function of the restriction to an open stratum.

## Main results

* `Stacks.EtaleCohomology.compactSupportCharSeriesInverts_lFunction_of_stages`.
* `Stacks.EtaleCohomology.lFunctionCharSeriesIdentity_of_compactSupportCharSeriesInverts`: the
  identity `L = det(1 - π^* T | RΓ_c)⁻¹` of `Stacks.EtaleCohomology.LFunctionCharSeriesIdentity`
  from `det(1 - π^* T | RΓ_c) · L = 1`.
* `Stacks.EtaleCohomology.nonempty_compactificationOf`: a compactification exists (Tag 0F41).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type) [CommRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
  (hfin : ∀ s : GeometricPoint X.obj,
    Module.Finite Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj F))
  (hproj : ∀ s : GeometricPoint X.obj,
    Module.Projective Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj F))
  {k : Type u} [Field k] [Fintype k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] {s : ConstructibleStratification B X ⊤} (Φ : s.ClosedFiltration)

/-- The L-function `L(Z i, F|_{Z i})` of the restriction of `F` to the `i`-th open stratum of a
closed filtration. -/
def stageLFunction (i : Fin s.n) : PowerSeries Λ :=
  haveI := noetherianSpace_stratum B X f Φ.toStageStratification i
  haveI : IsImmersion (fS B (Φ.toStageStratification.inclusion i)) :=
    Φ.toStageStratification.isImmersion i
  lFunctionOfFiniteProjectiveStalks.{u, u + 1, 0} B (Φ.toStageStratification.piece i) Λ
    (smallEtalePullObj B (Φ.toStageStratification.inclusion i) F)
    (fS B (Φ.toStageStratification.inclusion i) ≫ f)
    (finite_etaleModuleStalk_smallEtalePullObj B (Φ.toStageStratification.inclusion i) Λ F hfin)
    (projective_etaleModuleStalk_smallEtalePullObj B (Φ.toStageStratification.inclusion i) Λ F
      hproj)

/-- `L(X, F) = ∏ᵢ L(Z i, F|_{Z i})` along the open strata of a closed filtration. -/
theorem lFunctionOfFiniteProjectiveStalks_eq_prod_stageLFunction :
    lFunctionOfFiniteProjectiveStalks.{u, u + 1, 0} B X Λ F f hfin hproj =
      ∏ i : Fin s.n, stageLFunction B X Λ F hfin hproj f Φ i :=
  lFunctionOfFiniteProjectiveStalks_eq_prod_stratification B X Λ F hfin hproj f
    Φ.toStageStratification

variable (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **Reduction to the open strata.** If on every open stratum of a closed filtration, for every
compactification, `RΓ_c` of the restriction of `F` is perfect with characteristic series inverse to
the L-function of the restriction, then the same holds on `X` for every compactification. -/
theorem compactSupportCharSeriesInverts_lFunction_of_stages
    (hstratum : ∀ i : Fin s.n, ∀ J : CompactificationOf (Over.mk
        (B.inclusion.map (Φ.stageOpenInclusion i ≫ Φ.stageInclusion i) ≫ f)),
      CompactSupportCharSeriesInverts Λ kbar p q hcard _ J
        ((SmallEtale.sheafEquiv B (Φ.stageOpenObj i).obj (Φ.stageOpenObj i).property
          (ModuleCat.{u + 1} Λ)).functor.obj
          (smallEtalePullObj B (Φ.stageOpenInclusion i ≫ Φ.stageInclusion i) F))
        (stageLFunction B X Λ F hfin hproj f Φ i))
    (J : CompactificationOf (Over.mk f)) :
    CompactSupportCharSeriesInverts Λ kbar p q hcard f J
      ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).functor.obj F)
      (lFunctionOfFiniteProjectiveStalks.{u, u + 1, 0} B X Λ F f hfin hproj) := by
  classical
  let L : ℕ → PowerSeries Λ := fun n =>
    if h : n < s.n then stageLFunction B X Λ F hfin hproj f Φ ⟨n, h⟩ else 1
  have hL : lFunctionOfFiniteProjectiveStalks.{u, u + 1, 0} B X Λ F f hfin hproj =
      ∏ i ∈ Finset.range s.n, L i := by
    rw [lFunctionOfFiniteProjectiveStalks_eq_prod_stageLFunction B X Λ F hfin hproj f Φ,
      ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [L, dite_eq_left i.2]
  rw [hL]
  refine compactSupportCharSeriesInverts_of_closedFiltration Λ kbar p q hcard f Φ _ L
    (fun i hi J' => ?_) J
  have h := compactSupportCharSeriesInverts_of_eq (map_comp_eq_filtrationPieceMap f Φ i).symm
    (hstratum ⟨i, hi⟩) J'
  simp only [L, dite_eq_left hi]
  exact h.of_iso (filtrationPieceSheafIso Λ Φ F i).symm

section Identity

variable [HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)]
  [HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ)]

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] in
/-- **A compactification exists** (Nagata, Tag 0F41): a separated morphism of finite type to the
spectrum of a field. -/
@[sga "4½ Arcata 4.5.1" "special case"]
theorem nonempty_compactificationOf [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :
    Nonempty (CompactificationOf (Over.mk f)) :=
  ⟨(hasCompactification_of_compactSpace_quasiSeparatedSpace f).choose⟩

/-- The identity of Tag 03UZ from `det(1 - π^* T | RΓ_c) · L = 1`. -/
theorem lFunctionCharSeriesIdentity_of_compactSupportCharSeriesInverts
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) (J : CompactificationOf (Over.mk f))
    (h : CompactSupportCharSeriesInverts Λ kbar p q hcard f J
      ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).functor.obj F)
      (constructibleFlatLFunction B X Λ F f hF)) :
    LFunctionCharSeriesIdentity B X Λ f kbar F hF J p q hcard := by
  obtain ⟨hp, hL⟩ := h
  exact ⟨hp, (Units.inv_eq_of_mul_eq_one_right hL).symm⟩

end Identity

end Stacks.EtaleCohomology
