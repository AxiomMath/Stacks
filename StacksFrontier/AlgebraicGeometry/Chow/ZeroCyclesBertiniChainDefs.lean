module

public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesSeparablePoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniVanishingCut
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic

/-!
# Iterated cuts by sections of an invertible module

For global sections `s_1, …, s_d` of an invertible module `ℒ` on a scheme `X` over a field `k`,
and a closed subscheme `Z` of `X`, this file defines the closed subschemes `H_1 ∩ ⋯ ∩ H_j` cut out
by the first `j` sections and two conditions on them: off `Z` every point of `H_1 ∩ ⋯ ∩ H_j` has
`δ`-dimension at most `d - j`, and a further section does not vanish at the generic points of
`H_1 ∩ ⋯ ∩ H_j` off `Z`. These are the conditions of the iterated Bertini cut in
[Stacks, Tag 0FH5].

## Main definitions

* `Stacks.Chow.BertiniChain.familyCut`: the intersection of the zero schemes of a family of
  sections.
* `Stacks.Chow.BertiniChain.prefixFamily`: the first `j` members of a family indexed by `Fin d`.
* `Stacks.Chow.BertiniChain.DimBoundOff`: the `δ`-dimension bound off a closed subscheme.
* `Stacks.Chow.BertiniChain.NonvanishingAtGenericOff`: nonvanishing of a section at the generic
  points off a closed subscheme.
* `Stacks.Chow.BertiniChain.restrictedSection`: the restriction of a global section to a closed
  subscheme.

## References

* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Stacks.Ample

universe u

namespace Stacks.Chow.BertiniChain

attribute [local instance] Stacks.SectionsVanishingOnSubscheme.isInvertible_of_isInvertibleModule

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The scheme-theoretic intersection `H_1 ∩ ⋯ ∩ H_j` of the zero schemes of a family of global
sections of an invertible module, as a quasi-coherent sheaf of ideals. -/
def familyCut (M : X.Modules) [IsInvertibleModule X M] {ι : Type*} (s : ι → Γ(M, ⊤)) :
    X.IdealSheafData :=
  ⨆ i, Stacks.Divisors.zeroScheme X M (s i)

/-- The first `j` members of a family indexed by `Fin d`. -/
abbrev prefixFamily {α : Type*} {d : ℕ} (s : Fin d → α) (j : ℕ) (hj : j ≤ d) : Fin j → α :=
  fun i => s (Fin.castLE hj i)

/-- **The dimension bound off `Z`**: every point of the closed subscheme cut out by `T` which is
not in the support of `I` has `δ`-dimension at most `e` over `k`. -/
def DimBoundOff (f : X ⟶ Spec (.of k)) (I T : X.IdealSheafData) (e : ℤ) : Prop :=
  ∀ y ∈ T.support, y ∉ I.support →
    relativeDimension (fieldChowSituation k).dimensionFunction f y ≤ e

/-- **Nonvanishing at the generic points off `Z`**: the section `s` does not vanish at the image of
any generic point of the closed subscheme cut out by `T` lying off the support of `I`. -/
def NonvanishingAtGenericOff (I T : X.IdealSheafData) (M : X.Modules) [IsInvertibleModule X M]
    (s : Γ(M, ⊤)) : Prop :=
  ∀ η ∈ genericPoints T.subscheme, T.subschemeι η ∉ I.support →
    T.subschemeι η ∈ Stacks.ProjectiveFromSections.nvOpen M s

/-- The restriction of a global section to the closed subscheme cut out by `T`, as a section of
the pulled-back module. -/
def restrictedSection (T : X.IdealSheafData) (M : X.Modules) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback T.subschemeι).obj M).sections :=
  Stacks.SheafOfModules.sectionsOfTopOfRingSheaf _ (pullbackGlobalSections T.subschemeι M s)

/-- The value of `restrictedSection T M s` on the whole closed subscheme is the pullback of `s`
along `T.subschemeι`. -/
@[simp]
theorem restrictedSection_eval_top (T : X.IdealSheafData) (M : X.Modules) (s : Γ(M, ⊤)) :
    (restrictedSection T M s).eval (op ⊤) = pullbackGlobalSections T.subschemeι M s :=
  Stacks.SheafOfModules.sectionsOfTopOfRingSheaf_eval_top _ _

end Stacks.Chow.BertiniChain

end
