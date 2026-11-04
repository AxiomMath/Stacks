module

public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Trivialize
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Basic

/-!
# The basic open cut out by a ratio of two sections

Let `M` be an invertible `𝒪_X`-module, let `a` and `t` be global sections of `M` and let `U` be an
open on which `a` does not vanish. On `U` the section `a` is a basis of `M`, so `t|_U = f · a|_U`
for a unique `f ∈ Γ(X, U)` — the ratio `t / a`. This file proves the one thing that ratio is
wanted for:

`X.basicOpen (t / a) = U ⊓ X_t`.

That is the step which turns a nonvanishing locus of a section of a *tensor power* of an
invertible module into a basic open of the *structure sheaf* over `U`, which is what Mathlib's
criterion for quasi-affineness
(`AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen`) consumes. It is used by
`Stacks.AmpleAffineAvoidance.exists_affine_basicOpen_mem`, on the way to part (3) of Stacks
Tag 01ZY, on the nonvanishing locus produced by graded prime avoidance.

## The route

Both inputs are available in the library and neither is reproved here.

* **Division.** `Stacks.NonvanishingSpelling.existsUnique_smul_eq` is the trivialization clause of
  Stacks Tag 01CY in elementary form: over an open inside `X_a`, every section of `M` is a unique
  multiple of `a`. That supplies `f`.
* **Germ arithmetic.** `Stacks.ModuleStalk.smul_mem_maximalSmul_iff` says `ρ · m ∈ 𝔪_y M_y`
  precisely when `ρ` is a non-unit or `m ∈ 𝔪_y M_y`. Applied to
  `germ_y t = germ_y f · germ_y a`, and with the second alternative excluded because `y ∈ U ≤ X_a`,
  it gives `y ∈ X_t ↔ IsUnit (germ_y f)`, which is `y ∈ X.basicOpen f`.

The second step is the argument of `Stacks.NonvanishingOpen.mem_nonvanishingLocus_iff_isUnit` with
the basis section of a sectionwise trivialization replaced by the global section `a`. That
replacement is what makes no trivialization of `M` over `U` necessary: the only property of the
basis used there is that its germ avoids `𝔪_y M_y`, and for `a` that is the hypothesis
`U ≤ X_a` itself. In particular `U` is *not* assumed affine, which is the whole point — the `U`
this is applied to is a nonvanishing locus and is not affine in general.

## Main results

* `Stacks.AmpleAffineAvoidance.mem_nonvanishingLocus_iff_isUnit_of_smul`: on `U`, the section `t`
  fails to vanish exactly where its ratio by `a` is a unit.
* `Stacks.AmpleAffineAvoidance.exists_basicOpen_eq_inf`: **`U ⊓ X_t` is a basic open of `U`.**

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)

## What is not done

Nothing here is about tensor powers, about ampleness or about any Stacks tag, and no tag
attribute is attached: this is the elementary step, stated for two sections of one module. The
ratio is produced existentially rather than as a named function — no consumer needs its value,
only the open set it cuts out — so there is no `div` here and no arithmetic of ratios.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.ModuleStalk Stacks.NonvanishingOpen Stacks.SectionExtension

universe u

namespace Stacks.AmpleAffineAvoidance

variable {X : Scheme.{u}} {M : X.Modules} [IsInvertibleModule X M]

/-- **On an open where `a` does not vanish, a section `t` of the same module fails to vanish
exactly where its ratio by `a` is a unit.** The hypothesis `hf` says `f` is that ratio. -/
theorem mem_nonvanishingLocus_iff_isUnit_of_smul {a t : Γ(M, ⊤)} {U : X.Opens}
    (hU : U ≤ nonvanishingOpen X M a) {f : Γ(X, U)}
    (hf : resTop U t = f • resTop U a) {y : X} (hy : y ∈ U) :
    y ∈ nonvanishingLocus M t ↔ IsUnit ((X.presheaf.germ U y hy).hom f) := by
  have hg : (M.presheaf.Γgerm y).hom t =
      (X.presheaf.germ U y hy).hom f • (M.presheaf.Γgerm y).hom a := by
    rw [← TopCat.Presheaf.Γgerm_res_apply (i := homOfLE (le_top : U ≤ ⊤)) M.presheaf y hy t,
      show M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t = f • resTop U a from hf, germ_smul,
      TopCat.Presheaf.Γgerm_res_apply]
  rw [mem_nonvanishingLocus_iff, hg, smul_mem_maximalSmul_iff, not_or, not_not]
  refine and_iff_left ?_
  have := hU hy
  rwa [Stacks.NonvanishingOpen.mem_nonvanishingOpen] at this

/-- **The nonvanishing locus of a section, cut down to an open where another section of the same
module does not vanish, is a basic open of the structure sheaf there.** For `a` nonvanishing on
`U` and `t` an arbitrary global section of the same invertible module, `U ⊓ X_t` is
`X.basicOpen (t / a)`.

No affineness of `U` is used or needed. -/
theorem exists_basicOpen_eq_inf (a t : Γ(M, ⊤)) {U : X.Opens}
    (hU : U ≤ nonvanishingOpen X M a) :
    ∃ f : Γ(X, U), X.basicOpen f = U ⊓ nonvanishingOpen X M t := by
  obtain ⟨f, hf, -⟩ := Stacks.NonvanishingSpelling.existsUnique_smul_eq X M a hU (resTop U t)
  refine ⟨f, TopologicalSpace.Opens.ext ?_⟩
  ext y
  simp only [Opens.coe_inf, coe_nonvanishingOpen, Set.mem_inter_iff, SetLike.mem_coe]
  constructor
  · intro hy
    have hyU : y ∈ U := X.basicOpen_le f hy
    exact ⟨hyU, (mem_nonvanishingLocus_iff_isUnit_of_smul hU hf.symm hyU).mpr
      ((X.mem_basicOpen f y hyU).mp hy)⟩
  · rintro ⟨hyU, hyt⟩
    exact (X.mem_basicOpen f y hyU).mpr
      ((mem_nonvanishingLocus_iff_isUnit_of_smul hU hf.symm hyU).mp hyt)

end Stacks.AmpleAffineAvoidance

end
