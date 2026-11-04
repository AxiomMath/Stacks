module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaCompactificationChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FibrationTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperCohomologyExtComparison
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.FiniteReducedEtale
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# The trace formula in dimension zero

Step 2 of the proof of [Stacks, Tag 03UG]: the trace formula

`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`

holds for every separated scheme `X` of finite type over a finite field `k` of dimension at most
zero, every compactification of `X` and every `K ∈ D_ctf(X, Λ)`.

For `X` finite étale over `k`, `X` is its own compactification, `RΓ_c(X_k̄, K) = RΓ(X_k̄, K)` is
the direct sum of the stalks of `K` at the `k̄`-points of `X_k̄`, and the fixed points of `π_X` on
those are the rational points
(`perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_sum_of_etale'`).
The formula does not depend on the compactification
(`Stacks.EtaleCohomology.canonicalTraceFormula_of_compactification`). In general, `X` has finitely
many points, so it is finite over `k`, and its reduction `X_red` is finite and reduced over the
perfect field `k`, hence étale; the open and closed dévissage along the empty open and the
closed subscheme `X_red` (with the same underlying space) reduces `X` to `X_red`.

## Main results

* `Stacks.EtaleCohomology.canonicalTraceFormula_of_etale`: the trace formula for `X` finite
  étale over `k`, through any compactification.
* `Stacks.EtaleCohomology.traceFormulaUpToDim_zero`: the trace formula up to dimension zero.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.FilteredDerived Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

section Etale

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- Extension by zero along the identity, applied degreewise to a bounded below complex, is the
identity. -/
def extensionByZeroIdComplexIso {X : Scheme.{u}}
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleExtensionByZero.{u, 0} Λ (𝟙 X)).mapCochainComplexPlus.obj K ≅ K :=
  (CochainComplex.Plus.fullyFaithfulι _).preimageIso
    (HomologicalComplex.Hom.isoOfComponents
      (fun n => (etaleModuleExtensionByZeroIdIso Λ X).app (K.obj.X n))
      (fun a b _ => ((etaleModuleExtensionByZeroIdIso Λ X).hom.naturality (K.obj.d a b)).symm))

/-- **The trace formula for a scheme finite étale over `k`, through itself as compactification.**
If the stalks of `K` at all geometric points are perfect, `RΓ(X_k̄, K)` is perfect and
`Tr(π_X^* | RΓ(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`. -/
theorem canonicalTraceFormula_ofProper_of_etale {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Etale f] [IsFinite f] (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hstalk : ∀ s : GeometricPoint X, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{max (u + 1) 0} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
          K.obj))) :
    CanonicalTraceFormula Λ kbar p q hcard f (CompactificationOf.ofProper f) K := by
  classical
  have : Finite (rationalPoints f) := finite_rationalPoints f
  let : Fintype (rationalPoints f) := Fintype.ofFinite _
  let : Fintype (rationalPoints (Over.mk f).hom) := ‹Fintype (rationalPoints f)›
  have : Etale (Over.mk f).hom := ‹Etale f›
  have : IsFinite (Over.mk f).hom := ‹IsFinite f›
  have hY := isPerfect_frobeniusRestriction_of_etale Λ (Over.mk f) kbar K hstalk
  let e := extensionByZeroIdComplexIso Λ K
  have hX := isPerfect_frobeniusRestriction_of_iso Λ (Over.mk f) kbar e.symm hY
  refine ⟨hX, fun x => hstalk _, ?_⟩
  rw [finsum_eq_sum_of_fintype]
  exact (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_iso Λ (Over.mk f) kbar p q
    hcard e hX hY).trans
    (perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_sum_of_etale' Λ (Over.mk f) kbar p q
      hcard K hY hstalk)

/-- **The trace formula for a scheme finite étale over `k`**, through any compactification: if
the stalks of `K` at all geometric points are perfect, the trace formula holds for `K`. -/
theorem canonicalTraceFormula_of_etale {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Etale f]
    [IsFinite f] (j : CompactificationOf (Over.mk f))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hstalk : ∀ s : GeometricPoint X, StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      (((Scheme.pointSmallEtale s.hom).sheafFiber
        (A := ModuleCat.{max (u + 1) 0} Λ)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj
          K.obj))) :
    CanonicalTraceFormula Λ kbar p q hcard f j K :=
  canonicalTraceFormula_of_compactification Λ
    (fun _ E => torsionCohomologyProperty_etaleModuleForgetDerived_of_finite Λ E) kbar p q hcard f
    (CompactificationOf.ofProper f) j K
    (canonicalTraceFormula_ofProper_of_etale Λ kbar p q hcard f K hstalk)

end Etale

section DimensionZero

variable (B : BigEtaleSite.{u}) (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

omit [Fintype k] in
/-- A quasi-compact scheme locally of finite type over a field, of dimension at most zero, is
finite over it: it has finitely many points. -/
theorem isFinite_of_topologicalKrullDim_le_zero {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [QuasiCompact f] [LocallyOfFiniteType f] (hX : topologicalKrullDim X ≤ 0) : IsFinite f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have : LocallyQuasiFinite f := locallyQuasiFinite_iff_finite_preimage_singleton.2 fun _ =>
    (Stacks.Topology.Dimension.finite_of_topologicalKrullDim_le_zero hX).subset (Set.subset_univ _)
  exact IsFinite.of_locallyQuasiFinite f

/-- **The trace formula up to dimension zero** (Step 2 of [Stacks, Tag 03UG]): for every
separated scheme `X` of finite type over `k` in `B` of dimension at most zero, every
compactification of `X` and every `K ∈ D_ctf(X, Λ)`, the trace formula holds. -/
theorem traceFormulaUpToDim_zero : TraceFormulaUpToDim B Λ kbar p q hcard 0 := by
  intro X f _ _ _ hX j K hK
  have hX0 : topologicalKrullDim X.obj ≤ 0 := by exact_mod_cast hX
  have := isFinite_of_topologicalKrullDim_le_zero f hX0
  -- the reduced closed subscheme with the same underlying space
  let C : TopologicalSpace.Closeds X.obj := ⊤
  let Z := (Scheme.IdealSheafData.vanishingIdeal C).subscheme
  let i : Z ⟶ X.obj := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have hrange : Set.range i.base = Set.univ :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal C
  let jU : (∅ : Scheme.{u}) ⟶ X.obj := Scheme.emptyTo X.obj
  have hij : Set.range jU.base = (Set.range i.base)ᶜ := by
    rw [hrange, Set.compl_univ, Set.range_eq_empty_iff]
    infer_instance
  have hZB : B.Contains Z := Scheme.size_lt_of_isClosedImmersion i X.property
  refine canonicalTraceFormula_of_openClosed Λ kbar p q hcard j jU i hij K ?_ ?_
  · -- the empty open
    have : IsClosedImmersion (jU ≫ f) := .of_isPreimmersion _ (by simp)
    exact canonicalTraceFormula_of_etale Λ kbar p q hcard (jU ≫ f) _ _ fun s =>
      (IsEmpty.false (s.hom.base (Nonempty.some inferInstance))).elim
  · -- the reduction, finite and reduced over the perfect field `k`, hence étale
    have : Etale (i ≫ f) :=
      Stacks.AlgebraicGeometry.ProperSectionsGeom.etale_of_isFinite_of_isReduced (i ≫ f)
    exact canonicalTraceFormula_of_etale Λ kbar p q hcard (i ≫ f) _ _ fun s =>
      isPerfect_stalkComplex_of_isCtf B ⟨Z, hZB⟩ Λ _ (isCtf_inverseImage B Λ i hZB _ _ hK) s

end DimensionZero

end Stacks.EtaleCohomology

end
