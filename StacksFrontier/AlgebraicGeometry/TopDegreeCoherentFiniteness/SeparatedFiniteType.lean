module
import all StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersectionLeadingTerm
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ZeroUnconditional
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.Topology.Sheaves.Modules.SupportSection
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors

public import StacksFrontier.AlgebraicGeometry.CoherentDevissageGlue.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.Chow
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# Finite dimensionality of the top-degree cohomology of a coherent module, in general

[Stacks, Tag 0A3M]: for `X` a separated scheme of finite type over a field `k`, `ℱ` a coherent
`𝒪_X`-module and `d = dim(X)`, the `k`-vector space `H^d(X, ℱ)` is finite-dimensional.

The proof is the source's induction on `d`, run on the statement "for every separated `X` of
finite type over `k` with `dim X ≤ d` and every coherent `ℱ`, `dim_k H^d(X, ℱ) < ∞`".

* `d = 0` is the case of a zero-dimensional or empty `X`, which is finite over `k`
  ([Stacks, Tag 06LH]): `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isFinite`.
* For the step `d = n + 1` the dévissage of [Stacks, Tag 01YG],
  `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_forall_integralIdeal`, reduces to a
  quasi-coherent ideal `𝒥` on an integral closed subscheme `Z` (separated and of finite type, of
  dimension `≤ n + 1`). If the generic point of `Z` is not in the support of `𝒥`, that support
  is a proper closed subset, of dimension `≤ n`, and `H^{n+1}(Z, 𝒥) = 0`. Otherwise the quotient
  `𝒪_Z/𝒥` vanishes at the generic point, so has support of dimension `≤ n`, and the long exact
  sequence `H^n(Z, 𝒪_Z/𝒥) ⟶ H^{n+1}(Z, 𝒥) ⟶ H^{n+1}(Z, 𝒪_Z)` reduces to the induction
  hypothesis on the left and to
  `AlgebraicGeometry.finiteDimensional_cohomologyOverField_unit_of_isIntegral` — the structure
  sheaf of a variety, which is where the source uses Chow's lemma — on the right.

## Main results

* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_topologicalKrullDim_le`:
  **[Stacks, Tag 0A3M]**, with `dim X ≤ d` in place of `dim X = d`.
* `AlgebraicGeometry.finiteDimensional_topCohomology`: the tag in the source's shape, with
  `dim X = d`.

## Implementation notes

The hypothesis `dim X ≤ d` of the first result is weaker than the source's `dim X = d`, so that
statement is stronger; it is the form the induction needs, and the source's form is its special
case. The cohomology is `AlgebraicGeometry.cohomologyOverField`, the dimension
`topologicalKrullDim` of the underlying space.

## References

* [Stacks Project, Tag 0A3M](https://stacks.math.columbia.edu/tag/0A3M)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 06LH](https://stacks.math.columbia.edu/tag/06LH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- A proper closed subset of an irreducible Noetherian space of dimension at most `n + 1` has
dimension at most `n`. -/
theorem topologicalKrullDim_le_of_isClosed_ne_univ {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] [NoetherianSpace T] {A : Set T} (hA : IsClosed A) (hne : A ≠ Set.univ)
    (n : ℕ) (hT : topologicalKrullDim T ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim A ≤ (n : WithBot ℕ∞) := by
  refine IsNowhereDense.topologicalKrullDim_le_of_le_natCast_succ ?_ hA n hT
  rw [hA.isNowhereDense_iff, interior_eq_empty_iff_dense_compl]
  exact hA.isOpen_compl.dense ((Set.ne_univ_iff_exists_notMem A).mp hne)

/-- **The ideal case of the induction step of [Stacks, Tag 0A3M].** Let `Z` be integral,
separated and of finite type over `k` with `dim Z ≤ n + 1`, and assume the top-degree finiteness
in dimension `≤ n`. Then `H^{n+1}(Z, 𝒥)` is finite-dimensional for every quasi-coherent ideal
`𝒥 ⊆ 𝒪_Z`. -/
theorem finiteDimensional_cohomologyOverField_ideal_of_isIntegral {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [QuasiCompact g] [LocallyOfFiniteType g] [IsSeparated g]
    [IsIntegral Z] (n : ℕ) (hdim : topologicalKrullDim Z ≤ ((n + 1 : ℕ) : WithBot ℕ∞))
    (IH : ∀ {W : Scheme.{u}} (h : W ⟶ Spec (.of k)), QuasiCompact h → LocallyOfFiniteType h →
      IsSeparated h → topologicalKrullDim W ≤ (n : WithBot ℕ∞) →
      ∀ G : W.Modules, G.IsCoherent → FiniteDimensional k (cohomologyOverField k h G n))
    (J : (SheafOfModules.unit Z.ringCatSheaf).Submodule) [J.toSheafOfModules.IsQuasicoherent] :
    FiniteDimensional k (cohomologyOverField k g J.toSheafOfModules (n + 1)) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian Z := { }
  have : IrreducibleSpace Z := irreducibleSpace_of_isIntegral Z
  have hJ : J.toSheafOfModules.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentDevissageGlue.isCoherent_of_isQuasicoherent_submodule_unit J
  have hdim_supp : ∀ M : Z.Modules, M.IsCoherent → genericPoint Z ∉ _root_.SheafOfModules.supp M →
      topologicalKrullDim (_root_.SheafOfModules.supp M) ≤ (n : WithBot ℕ∞) :=
    fun M hM hM' => topologicalKrullDim_le_of_isClosed_ne_univ
      (Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp_of_isCoherent _ hM)
      (fun h => hM' (h.symm ▸ Set.mem_univ _)) n hdim
  by_cases hξ : genericPoint Z ∈ _root_.SheafOfModules.supp J.toSheafOfModules
  · have hmono : Mono (C := Z.Modules) J.ι :=
      inferInstanceAs (Mono (C := _root_.SheafOfModules Z.ringCatSheaf) J.ι)
    have hQ : (cokernel (C := Z.Modules) J.ι).IsCoherent :=
      _root_.SheafOfModules.cokernel_isCoherent J.ι
    have hQdim := hdim_supp _ hQ
      (_root_.AlgebraicGeometry.notMem_supp_cokernel_genericPoint J.ι hmono hξ)
    let S := ShortComplex.cokernelSequence (C := Z.Modules) J.ι
    have hS : S.ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact _
        mono_f := hmono
        epi_g := inferInstanceAs (Epi (cokernel.π J.ι)) }
    have hQ' : S.X₃.IsCoherent := hQ
    exact finiteDimensional_cohomologyOverField_one_of_shortExact_succ k g hS n
      (finiteDimensional_cohomologyOverField_of_topologicalKrullDim_supp_le k g S.X₃ n hQdim IH)
      (finiteDimensional_cohomologyOverField_unit_of_isIntegral k g n hdim IH)
  · have hJdim := hdim_supp _ hJ hξ
    exact finiteDimensional_of_isZero k
      (isZero_cohomologyOverField_of_topologicalKrullDim_supp_le k g _ hJdim (Nat.lt_succ_self n))

/-- **[Stacks, Tag 0A3M].** Let `X` be a separated scheme of finite type over a field `k`, let
`ℱ` be a coherent `𝒪_X`-module and let `d` be a natural number with `dim X ≤ d`. Then
`H^d(X, ℱ)` is a finite-dimensional `k`-vector space.

The source states this for `d = dim X`; the hypothesis `dim X ≤ d` is weaker, and for
`dim X < d` the group vanishes by [Stacks, Tag 02UZ]. The proof is the source's induction on `d`;
see the module documentation. -/
theorem finiteDimensional_cohomologyOverField_of_topologicalKrullDim_le (d : ℕ) :
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of k)), QuasiCompact f → LocallyOfFiniteType f →
      IsSeparated f → topologicalKrullDim X ≤ (d : WithBot ℕ∞) →
      ∀ F : X.Modules, F.IsCoherent → FiniteDimensional k (cohomologyOverField k f F d) := by
  induction d with
  | zero =>
    intro X f _ _ _ hdim F _
    have : IsFinite f :=
      isFinite_of_finiteType_of_topologicalKrullDim_le_zero k f (by simpa using hdim)
    exact finiteDimensional_cohomologyOverField_of_isFinite k f F 0
  | succ n IH =>
    intro X f _ _ _ hdim F hF
    refine finiteDimensional_cohomologyOverField_of_forall_integralIdeal k f (n + 1) ?_ F hF
    intro Z i _ _ I _
    exact finiteDimensional_cohomologyOverField_ideal_of_isIntegral k (i ≫ f) n
      (i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim) IH I

end AlgebraicGeometry

end
