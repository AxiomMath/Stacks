module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.Trivialize
public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingLocusRestrict
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A spanning section of an invertible module vanishes nowhere on an affine open

`Stacks.ProjectiveBundleConormal.exists_affine_open_splitting_span` produces, around every point
of the base, an affine open `U` and a section of `ℰ` whose image under the invertible quotient
*spans* `Γ(𝓛, U)`. What clause 3 of [Stacks, Tag 0B3V] needs of that section is that it
**vanishes nowhere on `U`**: only then does the section `σ` of the bundle land in the standard
open cut out by it, which is the factorization the chart computation runs on.

`Stacks.ProjectiveBundleConormal.restrictIsoUnitOfSpanEqTop` already passes from the span to a
trivialisation of `𝓛|_U`, and its proof establishes the germ condition on the way. This file
states that condition on its own, in the vocabulary
`Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn` that the locality argument speaks.

**Affineness is not decoration**; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.Trivialize`, which exhibits `𝒪(-1)` on
`𝐏¹` as a counterexample over a non-affine open.

## Main results

* `Stacks.ProjectiveBundleConormal.notMem_maximalSmul_germ_of_span_eq_top`: the germ of a
  spanning section at a point of the affine open avoids `𝔪_y 𝓛_y`.
* `Stacks.ProjectiveBundleConormal.mem_nonvanishingLocusOn_of_span_eq_top`: **the same statement
  as membership of the nonvanishing locus over `U`.**
* `Stacks.ProjectiveBundleConormal.exists_eq_smul_res_of_subset_nonvanishingLocusOn`: the
  converse direction, and the one a chart consumes: **a section of an invertible module that
  vanishes nowhere on an open generates the sections there**, so every section over that open is
  a function times it. No affineness, and the open is not a neighbourhood of one point but the
  whole of the nonvanishing locus.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.ProjectiveBundleConormal

variable {X : Scheme.{u}}

/-- **The germ of a spanning section of an invertible module avoids `𝔪_y 𝓛_y`.** If `t` spans
`Γ(L, U)` over `Γ(X, U)` and `U` is affine, then at every point of `U` the germ of `t` generates
the stalk, so in particular it is not killed modulo the maximal ideal.

The argument is the one inside
`Stacks.ProjectiveBundleConormal.restrictIsoUnitOfSpanEqTop`: by
`Stacks.PicSurjectiveOpen.exists_smul_germ_eq_of_surjective_smul` every element of the stalk is a
multiple of the germ of `t`, so a germ lying in `𝔪_y L_y` would force `𝔪_y L_y = L_y`, which
`Stacks.SheafOfModules.maximalIdeal_smul_top_ne_top_of_isInvertible` forbids. -/
theorem notMem_maximalSmul_germ_of_span_eq_top (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    {U : X.Opens} (hU : IsAffineOpen U) (t : Γ(L, U))
    (ht : Submodule.span Γ(X, U) {t} = ⊤) {y : X} (hy : y ∈ U) :
    (L.presheaf.germ U y hy).hom t ∉ Stacks.ModuleStalk.maximalSmul L y := by
  have : ∀ z : X.toRingedSpace.carrier, IsLocalRing (ringStalk X.toRingedSpace z) :=
    fun z => inferInstance
  have hinvRS : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L).2 inferInstance
  have hsurj : Function.Surjective fun c : Γ(X, U) => c • t := fun m =>
    Submodule.mem_span_singleton.1 (ht ▸ Submodule.mem_top (x := m))
  have hinst := Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace L.val y
  have hproper := Stacks.SheafOfModules.maximalIdeal_smul_top_ne_top_of_isInvertible
    (X := X.toRingedSpace) L y
  intro hmem
  refine hproper ((Stacks.SheafOfModules.maximalIdeal_smul_top_eq_top_iff_of_module_eq
      (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace L.val y) _
      hinst).mpr (le_antisymm le_top fun z _ => ?_))
  obtain ⟨c, hc⟩ := Stacks.PicSurjectiveOpen.exists_smul_germ_eq_of_surjective_smul
    L hU t hsurj hy z
  rw [hc]
  exact Submodule.smul_mem _ c hmem

/-- **A spanning section of an invertible module on an affine open does not vanish anywhere on
it.** This is `Stacks.ProjectiveBundleConormal.notMem_maximalSmul_germ_of_span_eq_top` read
through `Stacks.NonvanishingLocusRestrict.mem_nonvanishingLocusOn_iff`. -/
theorem mem_nonvanishingLocusOn_of_span_eq_top (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    {U : X.Opens} (hU : IsAffineOpen U) (t : Γ(L, U))
    (ht : Submodule.span Γ(X, U) {t} = ⊤) {y : X} (hy : y ∈ U) :
    y ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn L U t :=
  (Stacks.NonvanishingLocusRestrict.mem_nonvanishingLocusOn_iff L U hy).mpr
    (notMem_maximalSmul_germ_of_span_eq_top L hU t ht hy)

/-- **A section of an invertible module that vanishes nowhere on an open generates the sections
there.** Let `t` be a section of an invertible `ℒ` over an open `U` and let `V ≤ U` be an open
every point of which lies in the nonvanishing locus `U_t`. Then every section of `ℒ` over `V` is
a function on `V` times the restriction of `t`.

This is the direction the chart computation of clause 3 of [Stacks, Tag 0B3V] consumes, and it is
not the trivialisation statements the development already has: those are stated either for a
*global* section over `V ≤ X_s` (`Stacks.NonvanishingSpelling.bijective_smul`), or for a
neighbourhood of a single point
(`Stacks.SheafOfModules.exists_bijective_smul_of_germ_notMem_maximalIdeal_smul_top`), whereas the
section cutting out a chart of `𝐏(ℰ)` lives over `π⁻¹W` and the open wanted is the whole of its
nonvanishing locus.

`Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top` is exactly
that statement in the germ vocabulary, and
`Stacks.NonvanishingPullback.mem_maximalSmul_iff` crosses the two spellings of `𝔪_y ℒ_y` — the
`Stacks.ModuleStalk.maximalSmul` of
`Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn` and the submodule formed in the stalk
module structure of [Stacks, Tag 01CB] that the germ statement is written at. Nothing in the
development previously combined `nonvanishingLocusOn` with a bijectivity statement. -/
@[ega "0 5.5.2" "partial"]
theorem exists_eq_smul_res_of_subset_nonvanishingLocusOn {Y : Scheme.{u}} (L : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y L] {U : Y.Opens} (t : Γ(L, U))
    (V : Y.Opens) (hVU : V ≤ U)
    (hV : (V : Set Y) ⊆ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn L U t)
    (x : Γ(L, V)) :
    ∃ g : Γ(Y, V), x = (L.smul g).hom (L.presheaf.map (homOfLE hVU).op t) := by
  have hbij := Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
    (X := Y.toRingedSpace) L t V hVU (fun y hy hmem => (hV hy).2
      ((Stacks.NonvanishingPullback.mem_maximalSmul_iff L y _).mpr hmem))
  obtain ⟨g, hg⟩ := hbij.surjective x
  exact ⟨g, hg.symm⟩

end Stacks.ProjectiveBundleConormal

end
