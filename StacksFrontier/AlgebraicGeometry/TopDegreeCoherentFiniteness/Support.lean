module
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtensionGeneral
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.Topology.Sheaves.Modules.SupportSection

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticSupport.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersectionLeadingTerm

/-!
# Cohomology of a coherent module in degrees at least the dimension of its support

Let `X` be of finite type over a field `k` and let `ℱ` be a coherent `𝒪_X`-module whose support
has dimension at most `d`. A coherent module is the direct image of a coherent module on its
scheme-theoretic support ([Stacks, Tag 02OM]), a closed subscheme whose underlying space is the
support of `ℱ`, and a closed immersion does not change cohomology. So the cohomology of `ℱ`
vanishes above `d` by [Stacks, Tag 02UZ], and in degree `d` it is finite-dimensional as soon as
the top-degree cohomology of every coherent module on every separated scheme of finite type of
dimension at most `d` is. The second statement is the form in which the induction of
[Stacks, Tag 0A3M] uses its induction hypothesis on modules supported in smaller dimension.

## Main results

* `AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_supp_le`: `Hⁱ(X, ℱ) = 0`
  for `i > dim (Supp ℱ)`.
* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_topologicalKrullDim_supp_le`:
  top-degree finiteness transfers from schemes of dimension at most `d` to modules with support
  of dimension at most `d`.

## References

* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 0A3M](https://stacks.math.columbia.edu/tag/0A3M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The scheme-theoretic support of a coherent module has the dimension of its support. -/
theorem topologicalKrullDim_subscheme_annihilatorIdeal [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] :
    topologicalKrullDim (annihilatorIdeal F).subscheme =
      topologicalKrullDim (_root_.SheafOfModules.supp F) := by
  rw [supp_eq_support_annihilatorIdeal, topologicalKrullDim_support_eq]

/-- **The cohomology of a coherent module vanishes above the dimension of its support.** For
`f : X ⟶ Spec k` quasi-compact and locally of finite type and `ℱ` coherent with
`dim (Supp ℱ) ≤ d`, the `k`-vector space `Hⁱ(X, ℱ)` is zero for every `i > d`.

The module is the direct image of a coherent module on its scheme-theoretic support
([Stacks, Tag 02OM]), whose dimension is that of `Supp ℱ`; there the cohomology vanishes above
`d` by [Stacks, Tag 02UZ], and a closed immersion does not change cohomology. -/
theorem isZero_cohomologyOverField_of_topologicalKrullDim_supp_le [QuasiCompact f]
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] {d i : ℕ}
    (hF : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ (d : WithBot ℕ∞)) (hi : d < i) :
    IsZero (cohomologyOverField k f F i) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_isCoherent_pushforward_iso_subschemeι_annihilatorIdeal F
  have hvan : IsZero (cohomologyOverField k ((annihilatorIdeal F).subschemeι ≫ f) G i) :=
    _root_.AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_le' k _ G
      ((topologicalKrullDim_subscheme_annihilatorIdeal F).trans_le hF) hi
  exact hvan.of_iso
    ((cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k _ f G i).trans
      (cohomologyOverFieldIso k f e i)).symm

/-- **Top-degree finiteness passes from schemes to supports.** Let `f : X ⟶ Spec k` be
separated, quasi-compact and locally of finite type, and suppose that for every scheme `W`
separated and of finite type over `k` with `dim W ≤ d` the cohomology `H^d(W, 𝒢)` of every
coherent `𝒢` is finite-dimensional. Then `H^d(X, ℱ)` is finite-dimensional for every coherent
`ℱ` on `X` with `dim (Supp ℱ) ≤ d`.

Apply the hypothesis on the scheme-theoretic support of `ℱ` ([Stacks, Tag 02OM]), a closed
subscheme, hence separated and of finite type over `k`, of the dimension of `Supp ℱ`. -/
theorem finiteDimensional_cohomologyOverField_of_topologicalKrullDim_supp_le [QuasiCompact f]
    [LocallyOfFiniteType f] [IsSeparated f] (F : X.Modules) [F.IsCoherent] (d : ℕ)
    (hF : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ (d : WithBot ℕ∞))
    (h : ∀ {W : Scheme.{u}} (g : W ⟶ Spec (.of k)), QuasiCompact g → LocallyOfFiniteType g →
      IsSeparated g → topologicalKrullDim W ≤ (d : WithBot ℕ∞) →
      ∀ G : W.Modules, G.IsCoherent → FiniteDimensional k (cohomologyOverField k g G d)) :
    FiniteDimensional k (cohomologyOverField k f F d) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_isCoherent_pushforward_iso_subschemeι_annihilatorIdeal F
  have hfin := h ((annihilatorIdeal F).subschemeι ≫ f) inferInstance inferInstance inferInstance
    ((topologicalKrullDim_subscheme_annihilatorIdeal F).trans_le hF) G hG
  exact Module.Finite.equiv
    ((cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k _ f G d).trans
      (cohomologyOverFieldIso k f e d)).toLinearEquiv

end AlgebraicGeometry

end
