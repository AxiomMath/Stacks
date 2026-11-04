module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaOpenClosedDevissage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.ClosedSupportFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.NoetherNormalizationFibration
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# The induction on dimension for the trace formula

Let `k` be a finite field and `Λ` a finite ring. Write `TF_n` for the statement that the trace
formula

`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`

(`Stacks.EtaleCohomology.CanonicalTraceFormula`) holds for every separated scheme `X` of finite
type over `k` in the big étale site, of dimension at most `n`, every compactification of `X` and
every `K ∈ D_ctf(X, Λ)`.

The trace formula in any dimension, [Stacks, Tag 03UI] (1), is proved by induction on `n`, with
the curve case [Stacks, Tag 03UG] as the start. This file contains the formal part of that
induction: if every such `X` of dimension at most `n + 1` has a dense open `U` on which the
trace formula holds (for the induced compactification), then `TF_n` implies `TF_{n+1}`. The
complement `Z = X ∖ U`, with its reduced structure, is nowhere dense, hence of dimension at most
`n` (`IsNowhereDense.topologicalKrullDim_le_of_le_natCast_succ`), and `K|_Z ∈ D_ctf(Z, Λ)`
(Tag 0963), so `TF_n` applies to it; the open and closed dévissage
(`Stacks.EtaleCohomology.canonicalTraceFormula_of_openClosed`) then gives the formula on `X`.
Finally, a separated scheme of finite type over `k` has finite dimension, so the formula holds in
every dimension as soon as each `TF_n` does.

## Main results

* `Stacks.EtaleCohomology.TraceFormulaUpToDim`: the statement `TF_n`.
* `Stacks.EtaleCohomology.traceFormulaUpToDim_succ_of_dense`: the inductive step.
* `Stacks.EtaleCohomology.canonicalTraceFormula_of_forall_traceFormulaUpToDim`: `TF_n` for all
  `n` gives the trace formula for every `X`.

## References

* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI), item (1).
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

section

variable (B : BigEtaleSite.{u}) (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- **The trace formula up to dimension `n`.** For every separated scheme `X` of finite type over
`k` lying in the big étale site `B`, of dimension at most `n`, every compactification `j` of `X`
over `k` and every bounded below complex `K` of sheaves of `Λ`-modules on `X_étale` whose class
lies in `D_ctf(X, Λ)`, the trace formula `CanonicalTraceFormula` holds. -/
def TraceFormulaUpToDim (n : ℕ) : Prop :=
  ∀ (X : B.Scheme) (f : X.obj ⟶ Spec (.of k)) [QuasiCompact f] [LocallyOfFiniteType f]
    [IsSeparated f], topologicalKrullDim X.obj ≤ (n : WithBot ℕ∞) →
    ∀ (j : CompactificationOf (Over.mk f)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj)),
      IsCtf B X Λ (DerivedCategory.Q.obj K.obj) → CanonicalTraceFormula Λ kbar p q hcard f j K

variable {B Λ kbar p q hcard}

/-- The trace formula up to dimension `n` implies it up to any smaller dimension. -/
theorem TraceFormulaUpToDim.mono {m n : ℕ} (h : TraceFormulaUpToDim B Λ kbar p q hcard n)
    (hmn : m ≤ n) : TraceFormulaUpToDim B Λ kbar p q hcard m :=
  fun X f _ _ _ hX j K hK => h X f (hX.trans (by exact_mod_cast hmn)) j K hK

/-- The inverse image of a bounded below complex in `D_ctf(X, Λ)` along a morphism `g : Y ⟶ X` of
the big étale site lies in `D_ctf(Y, Λ)`. -/
private theorem isCtf_inverseImage {Λ : Type} [Ring Λ] {X Y : B.Scheme} (g : Y.obj ⟶ X.obj)
    {K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj)}
    (hK : IsCtf B X Λ (DerivedCategory.Q.obj K.obj)) :
    IsCtf B Y Λ (DerivedCategory.Q.obj
      ((etaleModuleInverseImage.{u, 0} Λ g).mapCochainComplexPlus.obj K).obj) :=
  (IsCtf.pullback B Λ (ObjectProperty.homMk g : Y ⟶ X) hK).of_iso B _ Λ
    ((etaleModuleInverseImage.{u, 0} Λ g).mapDerivedCategoryFactors.app K.obj)

/-- **Restriction of `D_ctf` to an open subscheme (Tag 0963).** For an open immersion
`j_U : U ⟶ X` with `U` in the big étale site, the restriction of a bounded below complex in
`D_ctf(X, Λ)` lies in `D_ctf(U, Λ)`. -/
theorem isCtf_restriction {X : B.Scheme} {U : Scheme.{u}} (hU : B.Contains U) (jU : U ⟶ X.obj)
    [IsOpenImmersion jU] {K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj)}
    (hK : IsCtf B X Λ (DerivedCategory.Q.obj K.obj)) :
    IsCtf B ⟨U, hU⟩ Λ (DerivedCategory.Q.obj
      ((etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K).obj) :=
  (isCtf_inverseImage (Y := ⟨U, hU⟩) jU hK).of_iso B _ Λ
    (DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex (etaleModuleInverseImageRestrictionIso.{u, 0} Λ jU)
      (ComplexShape.up ℤ)).app K.obj))

/-- **The inductive step.** Suppose that every separated scheme `X` of finite type over `k` in
`B`, of dimension at most `n + 1`, has a dense open `U` on which the trace formula holds for
every compactification of `X` and every `K ∈ D_ctf(X, Λ)` (through the induced compactification
and for `K|_U`). Then the trace formula up to dimension `n` implies it up to dimension `n + 1`.
The complement of `U` is nowhere dense, hence of dimension at most `n`, and the open and closed
dévissage combines the two. -/
theorem traceFormulaUpToDim_succ_of_dense (n : ℕ) (hn : TraceFormulaUpToDim B Λ kbar p q hcard n)
    (hU : ∀ (X : B.Scheme) (f : X.obj ⟶ Spec (.of k)) [QuasiCompact f] [LocallyOfFiniteType f]
      [IsSeparated f], topologicalKrullDim X.obj ≤ ((n + 1 : ℕ) : WithBot ℕ∞) →
      ∃ (U : Scheme.{u}) (jU : U ⟶ X.obj) (_ : IsOpenImmersion jU), Dense (Set.range jU.base) ∧
        ∀ (j : CompactificationOf (Over.mk f))
          (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj)),
          IsCtf B X Λ (DerivedCategory.Q.obj K.obj) →
          CanonicalTraceFormula Λ kbar p q hcard (jU ≫ f) (j.restrictOpen jU)
            ((etaleModuleRestriction.{u, 0} Λ jU).mapCochainComplexPlus.obj K)) :
    TraceFormulaUpToDim B Λ kbar p q hcard (n + 1) := by
  intro X f _ _ _ hX j K hK
  obtain ⟨U, jU, _, hdense, hUtf⟩ := hU X f hX
  have : IsLocallyNoetherian X.obj := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X.obj := ⟨⟩
  -- the reduced closed complement `Z` of `U`
  have hC : IsClosed (Set.range jU.base)ᶜ := jU.isOpenEmbedding.isOpen_range.isClosed_compl
  let C : TopologicalSpace.Closeds X.obj := ⟨_, hC⟩
  let Z := (Scheme.IdealSheafData.vanishingIdeal C).subscheme
  let i : Z ⟶ X.obj := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have hrange : Set.range i.base = (Set.range jU.base)ᶜ :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _
  have hij : Set.range jU.base = (Set.range i.base)ᶜ := by rw [hrange, compl_compl]
  have hZB : B.Contains Z := Scheme.size_lt_of_isClosedImmersion i X.property
  -- `Z` has dimension at most `n`
  have hnd : IsNowhereDense (Set.range i.base) := by
    rw [hrange, hC.isNowhereDense_iff,
      interior_compl, Set.compl_empty_iff]
    exact hdense.closure_eq
  have hZdim : topologicalKrullDim (⟨Z, hZB⟩ : B.Scheme).obj ≤ (n : WithBot ℕ∞) :=
    (topologicalKrullDim_le_of_range_subset i _ subset_rfl).trans
      (hnd.topologicalKrullDim_le_of_le_natCast_succ
        (hrange ▸ hC) n hX)
  have hZ := hn ⟨Z, hZB⟩ (i ≫ f) hZdim (j.restrictClosed i)
    ((etaleModuleInverseImage.{u, 0} Λ i).mapCochainComplexPlus.obj K)
    (isCtf_inverseImage (Y := ⟨Z, hZB⟩) i hK)
  exact canonicalTraceFormula_of_openClosed Λ kbar p q hcard j jU i hij K (hUtf j K hK) hZ

/-- **Finite dimension suffices.** If the trace formula holds up to every dimension `n`, it
holds for every separated scheme of finite type over `k` in `B`: such a scheme has finite
dimension. -/
theorem canonicalTraceFormula_of_forall_traceFormulaUpToDim
    (h : ∀ n, TraceFormulaUpToDim B Λ kbar p q hcard n) (X : B.Scheme)
    (f : X.obj ⟶ Spec (.of k)) [QuasiCompact f] [LocallyOfFiniteType f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X.obj))
    (hK : IsCtf B X Λ (DerivedCategory.Q.obj K.obj)) :
    CanonicalTraceFormula Λ kbar p q hcard f j K := by
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨n, hn⟩ := exists_natCast_le_of_ne_top
    (topologicalKrullDim_ne_top_of_locallyOfFiniteType k f)
  exact h n X f hn j K hK

variable (B Λ kbar p q hcard) in
/-- **The trace formula on schemes fibred in curves over `𝔸^n_k`.** For every separated scheme `U`
of finite type over `k` in `B` with a morphism `g : U ⟶ 𝔸^n_k = Spec k[X_0, …, X_{n-1}]` over `k`
all of whose fibres have dimension at most one, every compactification `j` of `U` and every
`K ∈ D_ctf(U, Λ)`, the trace formula holds. This is the fibration step of the proof of
[Stacks, Tag 03UI] (1); it follows from the trace formula on `𝔸^n_k` and on the fibres
(Tag 03UG) by the Leray spectral sequence and proper base change for `Rg_!`. -/
def FibredTraceFormula (n : ℕ) : Prop :=
  ∀ (U : B.Scheme) (fU : U.obj ⟶ Spec (.of k)) [QuasiCompact fU] [LocallyOfFiniteType fU]
    [IsSeparated fU] (g : U.obj ⟶ Spec (.of (MvPolynomial (Fin n) k))),
    g ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))) = fU →
    (∀ y, topologicalKrullDim (g.fiber y) ≤ 1) →
    ∀ (j : CompactificationOf (Over.mk fU)) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ U.obj)),
      IsCtf B U Λ (DerivedCategory.Q.obj K.obj) → CanonicalTraceFormula Λ kbar p q hcard fU j K

/-- **The inductive step, with the dense open fibred in curves.** By Noether normalization a
separated scheme of finite type over `k` of dimension at most `n + 1` has a dense affine open
fibred in curves over `𝔸^n_k` (`AlgebraicGeometry.exists_dense_isOpenImmersion_fiber_le_one`), so
the trace formula up to dimension `n` and on schemes fibred in curves over `𝔸^n_k` give it up to
dimension `n + 1`. -/
theorem traceFormulaUpToDim_succ (n : ℕ) (hn : TraceFormulaUpToDim B Λ kbar p q hcard n)
    (hF : FibredTraceFormula B Λ kbar p q hcard n) :
    TraceFormulaUpToDim B Λ kbar p q hcard (n + 1) := by
  refine traceFormulaUpToDim_succ_of_dense n hn fun X f _ _ _ hX => ?_
  obtain ⟨A, jU, _, g, hdense, hg, hfib⟩ := exists_dense_isOpenImmersion_fiber_le_one f n hX
  refine ⟨Spec A, jU, inferInstance, hdense, fun j K hK => ?_⟩
  have hUB : B.Contains (Spec A) := Scheme.size_lt_of_isOpenImmersion jU X.property
  have : QuasiCompact (jU ≫ f) := inferInstance
  exact hF ⟨Spec A, hUB⟩ (jU ≫ f) g hg hfib (j.restrictOpen jU) _ (isCtf_restriction hUB jU hK)

/-- **The induction on dimension.** If the trace formula holds for curves (dimension at most one,
Tag 03UG) and, whenever it holds up to dimension `n`, it holds on schemes fibred in curves over
`𝔸^n_k`, then it holds up to every dimension. -/
theorem traceFormulaUpToDim_of_fibred (h₁ : TraceFormulaUpToDim B Λ kbar p q hcard 1)
    (hF : ∀ n, TraceFormulaUpToDim B Λ kbar p q hcard n → FibredTraceFormula B Λ kbar p q hcard n) :
    ∀ n, TraceFormulaUpToDim B Λ kbar p q hcard n
  | 0 => h₁.mono zero_le_one
  | n + 1 =>
    have ih := traceFormulaUpToDim_of_fibred h₁ hF n
    traceFormulaUpToDim_succ n ih (hF n ih)

end

end Stacks.EtaleCohomology

end
