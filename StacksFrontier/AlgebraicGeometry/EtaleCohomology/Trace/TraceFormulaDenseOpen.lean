module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDimensionInduction

/-!
# The trace formula from a dense open depending on the coefficients

A variant of `Stacks.EtaleCohomology.traceFormulaUpToDim_succ_of_dense` in which the dense open
`U` on which the trace formula is known may depend on the compactification and on the
coefficient complex `K`: if for every separated scheme `X` of finite type over `k` of dimension
at most `n + 1`, every compactification and every `K ∈ D_ctf(X, Λ)` there is a dense open `U` with
the trace formula for `K|_U`, then the trace formula up to dimension `n` implies it up to
dimension `n + 1`.  In the proof of [Stacks, Tag 03UG] (Step 3) the open `U` is where `K` is
represented by a complex of finite locally constant sheaves, which depends on `K`.

## Main results

* `Stacks.EtaleCohomology.traceFormulaUpToDim_succ_of_dense_of_forall`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 1 and 3.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable {B : BigEtaleSite.{u}} {Λ : Type} [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k]
  {kbar : Type u} [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] {p q : ℕ} [Fact p.Prime]
  [CharP k p] [CharP kbar p] {hcard : Fintype.card k = p ^ q}

/-- **The inductive step, with a dense open depending on the coefficients.**  Suppose that for
every separated scheme `X` of finite type over `k` in `B`, of dimension at most `n + 1`, every
compactification `j` of `X` and every `K ∈ D_ctf(X, Λ)` there is a dense open `U` of `X` on which
the trace formula holds for `K|_U` through the induced compactification.  Then the trace formula
up to dimension `n` implies it up to dimension `n + 1`. -/
theorem traceFormulaUpToDim_succ_of_dense_of_forall (n : ℕ)
    (hn : TraceFormulaUpToDim B Λ kbar p q hcard n)
    (hU : ∀ (X : B.Scheme) (f : X.obj ⟶ Spec (.of k)) [QuasiCompact f] [LocallyOfFiniteType f]
      [IsSeparated f], topologicalKrullDim X.obj ≤ ((n + 1 : ℕ) : WithBot ℕ∞) →
      ∀ (j : CompactificationOf (Over.mk f))
        (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj)),
        IsCtf B X Λ (DerivedCategory.Q.obj K.obj) →
        ∃ (U : Scheme.{u}) (jU : U ⟶ X.obj) (_ : IsOpenImmersion jU), Dense (Set.range jU.base) ∧
          CanonicalTraceFormula Λ kbar p q hcard (jU ≫ f) (j.restrictOpen jU)
            ((etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K)) :
    TraceFormulaUpToDim B Λ kbar p q hcard (n + 1) := by
  intro X f _ _ _ hX j K hK
  obtain ⟨U, jU, _, hdense, hUtf⟩ := hU X f hX j K hK
  have : IsLocallyNoetherian X.obj := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X.obj := ⟨⟩
  have hcl := jU.isOpenEmbedding.isOpen_range.isClosed_compl
  let C : TopologicalSpace.Closeds X.obj := ⟨(Set.range jU.base)ᶜ, hcl⟩
  let Z := (Scheme.IdealSheafData.vanishingIdeal C).subscheme
  let i : Z ⟶ X.obj := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have hrange : Set.range i.base = (Set.range jU.base)ᶜ :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _
  have hij : Set.range jU.base = (Set.range i.base)ᶜ := by rw [hrange, compl_compl]
  have hZB : B.Contains Z := Scheme.size_lt_of_isClosedImmersion i X.property
  have hnd : IsNowhereDense (Set.range i.base) := by
    rw [hrange, hcl.isNowhereDense_iff, interior_compl, Set.compl_empty_iff]
    exact hdense.closure_eq
  have hZdim : topologicalKrullDim (⟨Z, hZB⟩ : B.Scheme).obj ≤ (n : WithBot ℕ∞) :=
    (topologicalKrullDim_le_of_range_subset i _ subset_rfl).trans
      (hnd.topologicalKrullDim_le_of_le_natCast_succ (hrange ▸ hcl) n hX)
  have hZ := hn ⟨Z, hZB⟩ (i ≫ f) hZdim (j.restrictClosed i)
    ((etaleModuleInverseImage.{u, 0} Λ i).mapCochainComplexPlus.obj K)
    ((IsCtf.pullback B Λ (ObjectProperty.homMk i : (⟨Z, hZB⟩ : B.Scheme) ⟶ X) hK).of_iso B _ Λ
      ((etaleModuleInverseImage.{u, 0} Λ i).mapDerivedCategoryFactors.app K.obj))
  exact canonicalTraceFormula_of_openClosed Λ kbar p q hcard j jU i hij K hUtf hZ

end Stacks.EtaleCohomology

end
