module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Devissage
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IdealPushforwardCriterion
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EmptySupport
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite dimensionality of the top-degree cohomology of a coherent module

For `X` a separated scheme of finite type over a field `k`, `ℱ` a coherent `𝒪_X`-module and
`d = dim(X)`, the `k`-vector space `H^d(X, ℱ)` is finite-dimensional ([Stacks, Tag 0A3M]). This
file proves it when `dim(X) = 0`, in every degree and without separatedness, and when `X` is
affine, and reduces it, in any degree, to the quasi-coherent ideal sheaves on the integral closed
subschemes of `X`.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `finiteDimensional_cohomologyOverField_of_affineCoverNum_le_of_isSeparated`: on a scheme
  quasi-compact and **separated** over a field the cohomology of a quasi-coherent module is
  finite-dimensional in every degree at least the affine covering number, because it vanishes
  there ([Stacks, Tag 01XI] read over a field).
* `finiteDimensional_cohomologyOverField_of_finiteType_of_dimension_zero`:
  **[Stacks, Tag 0A3M] for `dim(X) = 0`**, in every degree and with no separatedness
  hypothesis.
* `finiteDimensional_cohomologyOverField_pushforward_of_finiteType_of_dimension_zero`: the same
  for a coherent module pushed forward from a zero-dimensional closed subscheme.
* `finiteDimensional_topCohomology_of_isAffine`: **[Stacks, Tag 0A3M] for an affine `X`**.
* `finiteDimensional_cohomologyOverField_of_forall_integralIdeal`: the reduction of the tag, in
  any degree, to ideal sheaves on integral closed subschemes.

## Implementation notes

The reduction to ideal sheaves is stated in an arbitrary degree `n`: nothing in it refers to the
dimension of `X`.

The dévissage hypothesis writes coherence as `_root_.SheafOfModules.IsCoherent`, which is what
`F.IsCoherent` means for `F : X.Modules`, to tell it apart from the constant of the same name in
the `Stacks` namespace.

## References

* [Stacks Project, Tag 0A3M](https://stacks.math.columbia.edu/tag/0A3M)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 06LH](https://stacks.math.columbia.edu/tag/06LH)
* [Stacks Project, Tag 0A3G](https://stacks.math.columbia.edu/tag/0A3G)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### Vanishing above the affine covering number of a separated scheme -/

/-- **[Stacks, Tag 01XI] over a field, for a separated structure morphism.** The cohomology of a
quasi-coherent module on a scheme quasi-compact and separated over a field `k` is a
finite-dimensional `k`-vector space in every degree at least the affine covering number `t(X)`,
because it vanishes there. -/
theorem finiteDimensional_cohomologyOverField_of_affineCoverNum_le_of_isSeparated
    [QuasiCompact f] [IsSeparated f] (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (hn : X.affineCoverNum ⊤ ≤ n) :
    FiniteDimensional k (cohomologyOverField k f F n) := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsSeparated (terminal.from X) := by
    have : IsSeparated (f ≫ terminal.from (Spec (.of k))) := inferInstance
    simpa using this
  have : IsAffineHom (pullback.diagonal (terminal.from X)) := inferInstance
  exact finiteDimensional_of_isZero k
    ((isZero_cohomologyOverField_iff_isZero_hgroup k f F n).mpr
      (isZero_cohomology_of_affineCoverNum_le X F n hn))

/-! ### The case of dimension zero -/

/-- For `X` of finite type over a field `k` with `dim(X) = 0` and `ℱ` coherent, every
`Hⁿ(X, ℱ)` is a finite-dimensional `k`-vector space. -/
@[stacks 0A3M "the case `dim X = 0`, in every degree and without the separatedness hypothesis"]
theorem finiteDimensional_cohomologyOverField_of_finiteType_of_dimension_zero
    [LocallyOfFiniteType f] [QuasiCompact f] (hdim : topologicalKrullDim (X : Type u) = 0)
    (F : X.Modules) [F.IsCoherent] (n : ℕ) :
    FiniteDimensional k (cohomologyOverField k f F n) :=
  have : IsFinite f := isFinite_of_finiteType_of_dimension_zero k f hdim
  finiteDimensional_cohomologyOverField_of_isFinite k f F n

/-- **[Stacks, Tag 0A3M] for a coherent module pushed forward from a zero-dimensional closed
subscheme**, in every degree. If `i : W ⟶ X` is a closed immersion with `dim(W) = 0`,
`f : X ⟶ Spec k` is of finite type and `𝒢` is coherent on `W`, then every `Hⁿ(X, i_* 𝒢)` is a
finite-dimensional `k`-vector space. -/
theorem finiteDimensional_cohomologyOverField_pushforward_of_finiteType_of_dimension_zero
    [LocallyOfFiniteType f] [QuasiCompact f] {W : Scheme.{u}} (i : W ⟶ X) [IsClosedImmersion i]
    (hdim : topologicalKrullDim (W : Type u) = 0) (G : W.Modules) [G.IsCoherent] (n : ℕ) :
    FiniteDimensional k (cohomologyOverField k f ((Scheme.Modules.pushforward i).obj G) n) :=
  have : IsFinite (i ≫ f) := isFinite_of_finiteType_of_dimension_zero k (i ≫ f) hdim
  finiteDimensional_cohomologyOverField_pushforward_of_isFinite k i f G n

/-! ### The case of an affine scheme -/

/-- Let `X` be an affine scheme separated and of finite type over a field `k`, let `ℱ` be a
coherent `𝒪_X`-module and let `d = dim(X)`. Then `H^d(X, ℱ)` is a finite-dimensional `k`-vector
space. -/
@[stacks 0A3M "the case of an affine `X`"]
theorem finiteDimensional_topCohomology_of_isAffine [IsAffine X] [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated f] (F : X.Modules) [F.IsCoherent] (d : ℕ)
    (hd : topologicalKrullDim (X : Type u) = (d : WithBot ℕ∞)) :
    FiniteDimensional k (cohomologyOverField k f F d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · exact finiteDimensional_cohomologyOverField_of_finiteType_of_dimension_zero k f
      (by simpa using hd) F 0
  · have hq : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
    have hcov : X.affineCoverNum ⊤ ≤ 1 :=
      Scheme.affineCoverNum_le (n := 1) (fun _ ↦ ⊤) (fun _ ↦ isAffineOpen_top X) (by simp)
    exact finiteDimensional_cohomologyOverField_of_affineCoverNum_le_of_isSeparated k f F d
      (hcov.trans hpos)

/-! ### The dévissage: reduction to ideal sheaves on integral closed subschemes -/

/-- **Reduction of [Stacks, Tag 0A3M] to ideal sheaves on integral closed subschemes.** Let `X` be
of finite type over a field `k` and fix a degree `n`. If `dim_k Hⁿ(Z, ℐ) < ∞` for every
quasi-coherent ideal sheaf `ℐ ⊆ 𝒪_Z` on every integral closed subscheme `i : Z ⟶ X`, then
`dim_k Hⁿ(X, ℱ) < ∞` for every coherent `𝒪_X`-module `ℱ`. -/
theorem finiteDimensional_cohomologyOverField_of_forall_integralIdeal
    [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X), IsClosedImmersion i → IsIntegral Z →
      ∀ I : (SheafOfModules.unit Z.ringCatSheaf).Submodule,
        I.toSheafOfModules.IsQuasicoherent →
        FiniteDimensional k (cohomologyOverField k (i ≫ f) I.toSheafOfModules n))
    (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F) :
    FiniteDimensional k (cohomologyOverField k f F n) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := (isNoetherian_iff X).2 ⟨inferInstance, inferInstance⟩
  refine Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent X
    (fun G ↦ FiniteDimensional k (cohomologyOverField k f G n)) ?_ ?_ ?_ F hF
  · exact finiteDimensional_of_isZero k
      (isZero_cohomologyOverField_of_isZero k f
        Stacks.AlgebraicGeometry.CoherentDevissage.isZero_terminal n)
  · intro S hS _ _ _ h₁ h₃
    exact finiteDimensional_cohomologyOverField_of_shortExact k f hS n h₁ h₃
  · intro Z i hi hZ I hI
    have := hi
    exact finiteDimensional_cohomologyOverField_pushforward_of_isClosedImmersion k i f
      I.toSheafOfModules n (hideal i hi hZ I hI)

end AlgebraicGeometry

end
