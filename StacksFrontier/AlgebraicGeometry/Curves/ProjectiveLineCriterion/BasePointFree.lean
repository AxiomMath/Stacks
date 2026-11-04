module

public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.BasePointFree
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonShortExact
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Ratio
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection

/-!
# A second section without common zeros

Let `k` be a field and `X` a proper integral scheme of dimension at most one over `k` with
`H¹(X, 𝒪_X) = 0`, let `ℒ` be an invertible `𝒪_X`-module and `s` a nonzero global section of `ℒ`
with zero scheme `i : D ⟶ X`. The sequence `0 ⟶ 𝒪_X ⟶ ℒ ⟶ i_* i^* ℒ ⟶ 0` of [Stacks, Tag 0C6K]
and `H¹(X, 𝒪_X) = 0` make `Γ(X, ℒ) ⟶ Γ(D, i^* ℒ)` surjective; lifting a trivialisation of the
restriction of `ℒ` to the zero-dimensional scheme `D` gives a section `t` with no common zero
with `s`. This is the base point freeness step in the proof of [Stacks, Tag 0C6T].

## Main results

* `AlgebraicGeometry.ProjectiveLineCriterion.topologicalKrullDim_eq_one_of_sup_nvOpen_eq_top`:
  two sections without common zero, neither nowhere vanishing, force dimension one.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 0C6T](https://stacks.math.columbia.edu/tag/0C6T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules (nonvanishingLocus sectionsOfTop)
open Stacks.ProjectiveFromSections (nvOpen resT)

universe u

namespace AlgebraicGeometry.ProjectiveLineCriterion

/-! ### Nonvanishing opens of combinations of sections -/

section General

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-- The nonvanishing open of a multiple of a section lies in that of the section. -/
private theorem nvOpen_smul_le_aux (c : Γ(X, ⊤)) (s : Γ(L, ⊤)) : nvOpen L (c • s) ≤ nvOpen L s := by
  intro y hy
  rw [Stacks.NonvanishingOpen.mem_nonvanishingOpen, Stacks.Ample.mem_nonvanishingLocus_iff]
    at hy ⊢
  intro hs
  apply hy
  have hg : (L.presheaf.Γgerm y).hom (c • s) =
      (X.presheaf.germ ⊤ y trivial).hom c • (L.presheaf.Γgerm y).hom s :=
    Stacks.ModuleStalk.germ_smul L y ⊤ trivial c s
  rw [hg, Stacks.ModuleStalk.smul_mem_maximalSmul_iff]
  exact Or.inr hs

/-- **A combination of sections vanishes where all of them vanish**: the nonvanishing open of
`∑ cⱼ • sⱼ` lies in the union of those of the `sⱼ`. -/
theorem nvOpen_sum_smul_le {ι : Type*} [Fintype ι] (c : ι → Γ(X, ⊤)) (s : ι → Γ(L, ⊤)) :
    nvOpen L (∑ j, c j • s j) ≤ ⨆ j, nvOpen L (s j) := by
  intro y hy
  by_contra h
  rw [Stacks.NonvanishingOpen.mem_nonvanishingOpen, Stacks.Ample.mem_nonvanishingLocus_iff]
    at hy
  apply hy
  rw [map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hj : y ∉ nvOpen L (c j • s j) := fun hj =>
    h (TopologicalSpace.Opens.mem_iSup.mpr ⟨j, nvOpen_smul_le_aux L _ _ hj⟩)
  rwa [Stacks.NonvanishingOpen.mem_nonvanishingOpen, Stacks.Ample.mem_nonvanishingLocus_iff,
    not_not] at hj

/-- **The nonvanishing open of a multiple of a section lies in that of the section.** -/
theorem nvOpen_smul_le (c : Γ(X, ⊤)) (s : Γ(L, ⊤)) : nvOpen L (c • s) ≤ nvOpen L s :=
  nvOpen_smul_le_aux L c s

/-- **Two sections without common zero, neither of them nowhere vanishing, force dimension at
least one**: a zero `x` of `s` and a point `y` where `s` does not vanish give the strict
inclusion of irreducible closed subsets `{x}⁻ ⊊ X`. -/
theorem one_le_topologicalKrullDim_of_sup_nvOpen_eq_top [IrreducibleSpace X] (s t : Γ(L, ⊤))
    (hst : nvOpen L s ⊔ nvOpen L t = ⊤) (hs : nvOpen L s ≠ ⊤) (ht : nvOpen L t ≠ ⊤) :
    1 ≤ topologicalKrullDim X := by
  have hex : ∀ u : Opens X, u ≠ ⊤ → ∃ x, x ∉ u := fun u hu => by
    by_contra! h
    exact hu (eq_top_iff.mpr fun x _ => h x)
  obtain ⟨x, hx⟩ := hex _ hs
  obtain ⟨y, hy⟩ : ∃ y, y ∈ nvOpen L s := by
    obtain ⟨y, hy⟩ := hex _ ht
    have hy' : y ∈ nvOpen L s ⊔ nvOpen L t := by rw [hst]; trivial
    exact ⟨y, (TopologicalSpace.Opens.mem_sup.mp hy').resolve_right hy⟩
  rw [topologicalKrullDim, Order.one_le_krullDim_iff]
  let Z : IrreducibleCloseds X := ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  refine ⟨Z, T, lt_of_le_of_ne (fun z _ => Set.mem_univ z) fun hZT => ?_⟩
  have hyZ : y ∈ (Z : Set X) := hZT ▸ Set.mem_univ y
  have hsub : closure ({x} : Set X) ⊆ (nvOpen L s : Set X)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr hx) (nvOpen L s).isOpen.isClosed_compl
  exact hsub hyZ hy

end General

/-! ### Sections of positive degree vanish somewhere -/

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### Surjectivity onto the sections along the zero scheme -/

/-! ### A base point free pencil -/

end AlgebraicGeometry.ProjectiveLineCriterion

end
