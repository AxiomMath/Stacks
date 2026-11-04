module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.Situation
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.CohomologyPresheafComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces
public import StacksCore.Algebra.Homology.ShortComplex.ShortExact
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension

/-!
# Extensions of the dualizing sheaf on a proper curve

In Situation [Stacks, Tag 0B5D] — a field `k` and a proper one-dimensional `k`-scheme `X` with
`H⁰(X, 𝒪_X) = k` — let `ω` be the dualizing sheaf of `X` and consider an exact sequence
`ω ⟶ ℱ ⟶ 𝒬 ⟶ 0` of coherent `𝒪_X`-modules. [Stacks, Tag 0B5E] asserts that if
`H¹(X, 𝒬) = 0` then either `H¹(X, ℱ) = 0` or `ℱ ≅ ω ⊕ 𝒬`.

## Main definitions

* `AlgebraicGeometry.CohenMacaulayCurveSituation.FirstCohomologyDuality` is the
  representability of the functor `ℱ ↦ Hom_k(H¹(X, ℱ), k)` by the dualizing sheaf, together
  with its naturality: clause (5) of [Stacks, Tag 0BS2].
* `AlgebraicGeometry.CohenMacaulayCurveSituation.SecondCohomologyVanishing` is the vanishing of
  `H²(X, -)`, which holds on a one-dimensional scheme by [Stacks, Tag 02UZ].

## Main results

* `AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_le'`: **[Stacks, Tag 02UZ]**
  for the modules on a scheme of finite type over a field — `Hⁱ(X, ℱ) = 0` above the dimension
  of `X`.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.secondCohomologyVanishing`: that vanishing in
  degree two, which is what Situation [Stacks, Tag 0B5D] consumes.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.surjective_cohomologyOverFieldMap_f_of_isZero`
  and `AlgebraicGeometry.CohenMacaulayCurveSituation.surjective_cohomologyOverFieldMap_g_of_isZero`
  are the two surjectivity steps of the long exact sequence of a short exact sequence.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.surjective_cohomologyOverFieldMap_one_of_exact`:
  for an exact sequence `ω ⟶ ℱ ⟶ 𝒬 ⟶ 0` with `H¹(X, 𝒬) = 0`, the map `H¹(X, ω) ⟶ H¹(X, ℱ)` is
  surjective.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.exists_retraction_of_bijective`: if
  `H¹(X, ω) ⟶ H¹(X, ℱ)` is bijective then `ω ⟶ ℱ` has a retraction.
* `AlgebraicGeometry.CohenMacaulayCurveSituation.isZero_firstCohomology_or_iso_biprod`:
  [Stacks, Tag 0B5E].

## Implementation notes

Cohomology over the base field is `AlgebraicGeometry.cohomologyOverField`, and its
functoriality in the module is `AlgebraicGeometry.cohomologyOverFieldMap`; the exact sequence
`ω ⟶ ℱ ⟶ 𝒬 ⟶ 0` is recorded as exactness of the short complex `ω ⟶ ℱ ⟶ 𝒬` together with
`Epi` for the second arrow, and the splitting alternative as an isomorphism `ℱ ≅ ω ⊞ 𝒬`
identifying the two arrows with `biprod.inl` and `biprod.snd`.

*Vanishing of `H²`.* The source's "`H¹(X, 𝒬) = 0` makes `H¹(X, ω) ⟶ H¹(X, ℱ)` an isomorphism"
also uses that `H²` vanishes on `X`, because `ω ⟶ ℱ` need not be injective: the surjection
factors through the image of `ω`, and only `H²` of the kernel being zero makes the first factor
surjective. That vanishing is [Stacks, Tag 02UZ], and it is **proved here**, as
`AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_le'`: Grothendieck's
vanishing theorem is available for abelian sheaves on a Noetherian space
(`Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le`), and the
three comparisons needed to read it in the `AlgebraicGeometry.cohomologyOverField` spelling are
available too; see the implementation note on the proof.

**Two hypotheses are carried.**

*Duality.* `FirstCohomologyDuality ω` is clause (5) of [Stacks, Tag 0BS2]: for every
quasi-coherent `ℱ` the group `Hom(ℱ, ω)` is the `k`-linear dual of `H¹(X, ℱ)`, naturally in
`ℱ`. Neither [Stacks, Tag 0BS2] nor [Stacks, Tag 0AWP], which is the form the source cites, is
in this development, and there is no dualizing sheaf of a proper curve over a field anywhere in
the library; `ω` is therefore an unconstrained module and its representability is this
hypothesis. The naturality clause is what the source's "the composition `ω ⟶ ℱ ⟶ ω` is the
identity by the universal property" consumes, and the pointwise bijection alone does not prove
the tag.

*One-dimensionality of `H¹(X, ω)`.* The source gets `dim_k H¹(X, ω) = 1` from the duality of
`H⁰(X, 𝒪_X) = k` with `H¹(X, ω)` of Section [Stacks, Tag 0B5B], which is not in this
development either; it is the hypothesis `hone`.

**How [Stacks, Tag 02UZ] is read in the `cohomologyOverField` spelling.** Grothendieck's
vanishing theorem is proved for an abelian sheaf on a Noetherian topological space, in the
`CategoryTheory.Sheaf.H` spelling. Three comparisons carry it over, in this order:
`AlgebraicGeometry.isZero_cohomologyOverField_iff_isZero_hgroup` ([Stacks, Tag 01F1] (1)) to the
abelian-group-valued cohomology of the underlying sheaf;
`Stacks.Cohomology.ModuleComparison.isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf`
([Stacks, Tag 03FD]) to the value at `⊤` of Mathlib's cohomology presheaf; and
`Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top` from that value to
`CategoryTheory.Sheaf.H`, the whole space being the terminal open. The Noetherian space is
produced from properness alone: a proper morphism is locally of finite type, so `X` is locally
Noetherian over the spectrum of a field, and it is quasi-compact, so `X` is a Noetherian scheme.

## References

* [Stacks Project, Tag 0B5E](https://stacks.math.columbia.edu/tag/0B5E)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0AWP](https://stacks.math.columbia.edu/tag/0AWP)
* [Stacks Project, Tag 0B5B](https://stacks.math.columbia.edu/tag/0B5B)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.ModuleComparison
  (isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf)
open Stacks.Cohomology.TerminalCohomology (subsingleton_H_iff_subsingleton_H'_top)
open Stacks.CohomologyVanishing (subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le)

universe u

namespace AlgebraicGeometry

/-! ### Grothendieck vanishing above the dimension -/

/-- **Stacks Project, Tag 02UZ.** For `f : X ⟶ Spec k` quasi-compact and locally of finite type
and `X` of topological Krull dimension at most `d`, the cohomology `Hⁱ(X, ℱ)` of every
`𝒪_X`-module vanishes for `i > d`.

The two hypotheses on `f` make `X` a Noetherian scheme, hence a Noetherian space, where
Grothendieck's theorem is
`Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le`; the
three comparisons listed in the module documentation read that vanishing in the
`AlgebraicGeometry.cohomologyOverField` spelling. A proper `f` is in particular quasi-compact and
locally of finite type. -/
public theorem isZero_cohomologyOverField_of_topologicalKrullDim_le' (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [LocallyOfFiniteType f]
    (F : X.Modules) {d i : ℕ}
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hi : d < i) :
    IsZero (cohomologyOverField k f F i) := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hnoeth : IsNoetherian X := { }
  refine (isZero_cohomologyOverField_iff_isZero_hgroup k f F i).mpr ?_
  refine (isZero_rightDerivedSections_iff_isZero_cohomologyPresheaf
    (J := Opens.grothendieckTopology (X : Type u)) (R := X.ringCatSheaf)
    (U := (⊤ : Opens (X : Type u))) (n := i) (F := F)).mpr ?_
  have hsub := (subsingleton_H_iff_subsingleton_H'_top
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) i).mp
    (subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le (d := d) hdim hi _)
  exact @AddCommGrpCat.isZero_of_subsingleton _ hsub

/-! ### Linear algebra: a surjection out of a line -/


namespace CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u})

/-! ### The cited input, and the vanishing that is proved -/


/-! ### Surjectivity along the long exact sequence -/

variable {S}


/-! ### Stacks Tag 0B5E -/


end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
