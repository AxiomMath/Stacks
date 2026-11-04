module

public import StacksFrontier.AlgebraicGeometry.ClopenLift.ClopenSection
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.NonvanishingAffineIntersection.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Stacks Tag 0B5P, reduced to the surjectivity of one restriction map

[Stacks, Tag 0B5P] is the cohomological criterion for ampleness: an invertible `𝒪_X`-module `L`
on a quasi-compact scheme `X` is ample as soon as, for every quasi-coherent ideal sheaf
`I ⊆ 𝒪_X`, some positive tensor power satisfies `H¹(X, I ⊗ L^{⊗ n}) = 0`.

This file proves the *geometric* half of that criterion, with the cohomology replaced by its one
consequence: given a closed point `x` of an affine open `U`, write `Z = (X ∖ U) ∪ {x}` and let
`i : Z' ⟶ X` be the reduced closed subscheme on `Z`. If global sections of `L^{⊗ n}` surject onto
global sections of `i^* L^{⊗ n}`, then `x` lies in an affine nonvanishing locus of a section of
`L^{⊗ n}`. Quantified over the closed points, that is ampleness.

The choice of `Z` is the whole trick, and it is the one the source makes: `x` is isolated in `Z`,
because `i^{-1}(U) = {x}` and `i^{-1}({x}) = {x}`, so `{x}` is a *clopen* point of `Z'`. On `Z'`
one therefore has a section of `i^* L^{⊗ n}` whose nonvanishing locus is exactly that point
(`Stacks.Tag0B5PClopenLift.exists_nonvanishingLocus_eq_singleton`), and its lift `s` to `X`
satisfies `i^{-1}(X_s) = {x}` by [Stacks, Tag 0H78], which forces `x ∈ X_s` and `X_s ⊆ U`. Then
`X_s = U ∩ X_s` is affine by [Stacks, Tag 01PV].

## Main definitions

* `Stacks.Tag0B5PClopenLift.avoidClosed U hx`: the closed set `(X ∖ U) ∪ {x}`.
* `Stacks.Tag0B5PClopenLift.avoidι U hx`: the reduced closed subscheme on it, as a closed
  immersion into `X`.

## Main results

* `Stacks.Tag0B5PClopenLift.isClosed_singleton_preimage` and
  `Stacks.Tag0B5PClopenLift.isOpen_singleton_preimage`: the point of `avoidι U hx` over `x` is
  clopen.
* `Stacks.Tag0B5PClopenLift.surjective_pullbackGlobalSection_of_epi`: the restriction of global
  sections to a closed subscheme is surjective as soon as the evaluation of the unit of the
  module pullback–pushforward adjunction at `⊤` is an epimorphism.
* `Stacks.Tag0B5PClopenLift.exists_affine_nonvanishingLocus_of_surjective`: **the geometric step
  of [Stacks, Tag 0B5P]** at one closed point.
* `Stacks.Tag0B5PClopenLift.isAmple_of_forall_surjective`: **[Stacks, Tag 0B5P] with its
  cohomological hypothesis replaced by the surjectivity it is used to produce.**

## What is still missing, exactly

No `stacks` attribute is attached anywhere in this directory, and Tag 0B5P is **not** proved.
What is owed is the single implication

  `H¹(X, I_Z ⊗ L^{⊗ n}) = 0` ⟹ `Γ(X, L^{⊗ n}) ⟶ Γ(Z', i^* L^{⊗ n})` surjective,

for `I_Z` the ideal sheaf of the reduced closed subscheme `i : Z' ⟶ X`. Its two halves are in
very different states.

* The cohomological half is **proved**: `Stacks.AmpleCohomologicalCriterion.epi_evaluation_map_g`
  turns the vanishing of `H¹` of the left-hand term of a short exact
  sequence into surjectivity on global sections,
  `Stacks.AmpleCohomologicalCriterion.shortExact_map_tensorRight`
  tensors a short exact sequence of `𝒪_X`-modules by an invertible one,
  and `Stacks.AmpleCohomologicalCriterion.kerSubobject` with
  `Stacks.AmpleCohomologicalCriterion.isQuasicoherent_kerSubobject` supply the ideal sheaf as a
  quasi-coherent subobject of `𝒪_X`, which is what the hypothesis of the tag quantifies over.
  Together these give
  `Γ(X, 𝒪_X ⊗ L^{⊗ n}) ⟶ Γ(X, i_* 𝒪_{Z'} ⊗ L^{⊗ n})` epi.
* The missing half is the **projection formula**, [Stacks, Tag 0FZE] / [Stacks, Tag 01E8]: the
  isomorphism `i_* 𝒪_{Z'} ⊗ L^{⊗ n} ≅ i_* (i^* L^{⊗ n})` for the affine morphism `i`, together
  with the identification of the resulting map on global sections with the unit of the pullback
  adjunction. **No declaration in either Lean tree states the projection formula for sheaves of
  modules on a scheme**, and `../ComponentDegrees/Basic.lean` records
  its absence. It is a genuine gap in the mathematics, not a spelling problem: the
  comparison map `f_* F ⊗ G ⟶ f_*(F ⊗ f^* G)` itself has to be built, and the only existing
  ingredient is `Stacks.RingedSpace.comparison`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparison.lean`), which goes the
  other way, `f^*(A ⊗ B) ⟶ f^* A ⊗ f^* B`.

`Stacks.Tag0B5PClopenLift.surjective_pullbackGlobalSection_of_epi` is stated so that the gap is
exactly one morphism-level comparison: a proof of the projection formula closes Tag 0B5P by
composing it with `isAmple_of_forall_surjective`. The sibling file `Cohomology.lean` carries out
that composition: it spends the tag's hypothesis at the ideal sheaf of a closed immersion, names
the residue as `Stacks.Tag0B5PClopenLift.ProjectionFormulaConsequence`, and derives Tag 0B5P
from it.

## References

* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Tag0B5PClopenLift

variable {X : Scheme.{u}}

/-! ### The auxiliary closed subscheme -/

/-- The closed set `(X ∖ U) ∪ {x}` of [Stacks, Tag 0B5P]: the complement of an open `U`, with one
closed point of `U` added back. -/
def avoidClosed (U : X.Opens) {x : X} (hx : IsClosed ({x} : Set X)) : Closeds X :=
  ⟨(U : Set X)ᶜ ∪ {x}, U.isOpen.isClosed_compl.union hx⟩

/-- The underlying set of `avoidClosed U hx` is `(X ∖ U) ∪ {x}`. -/
@[simp] theorem coe_avoidClosed (U : X.Opens) {x : X} (hx : IsClosed ({x} : Set X)) :
    (avoidClosed U hx : Set X) = (U : Set X)ᶜ ∪ {x} := rfl

/-- The reduced closed subscheme on `(X ∖ U) ∪ {x}`. -/
noncomputable def avoidSubscheme (U : X.Opens) {x : X} (hx : IsClosed ({x} : Set X)) :
    Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (avoidClosed U hx)).subscheme

/-- The closed immersion of the reduced closed subscheme on `(X ∖ U) ∪ {x}` into `X`. -/
noncomputable def avoidι (U : X.Opens) {x : X} (hx : IsClosed ({x} : Set X)) :
    avoidSubscheme U hx ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal (avoidClosed U hx)).subschemeι

/-- The morphism `avoidι U hx` is a closed immersion. -/
instance isClosedImmersion_avoidι (U : X.Opens) {x : X} (hx : IsClosed ({x} : Set X)) :
    IsClosedImmersion (avoidι U hx) :=
  inferInstanceAs (IsClosedImmersion
    (Scheme.IdealSheafData.vanishingIdeal (avoidClosed U hx)).subschemeι)

/-- The image of the auxiliary closed subscheme is `(X ∖ U) ∪ {x}`. -/
theorem range_avoidι (U : X.Opens) {x : X} (hx : IsClosed ({x} : Set X)) :
    Set.range (avoidι U hx) = (U : Set X)ᶜ ∪ {x} :=
  (Scheme.IdealSheafData.range_subschemeι _).trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal (avoidClosed U hx))

/-- `x` is in the image of the auxiliary closed subscheme. -/
theorem exists_avoidι_eq (U : X.Opens) {x : X} (hx : IsClosed ({x} : Set X)) :
    ∃ z : avoidSubscheme U hx, avoidι U hx z = x := by
  have : x ∈ Set.range (avoidι U hx) := by
    rw [range_avoidι]
    exact Or.inr rfl
  exact this

/-- A point over `x` is the preimage of any `S` meeting `(X ∖ U) ∪ {x}` exactly in `{x}`. -/
private theorem singleton_eq_preimage_avoidι (U : X.Opens) {x : X} (hx : IsClosed ({x} : Set X))
    {z : avoidSubscheme U hx} (hz : avoidι U hx z = x) {S : Set X}
    (hS : S ∩ ((U : Set X)ᶜ ∪ {x}) = {x}) :
    ({z} : Set (avoidSubscheme U hx)) = (avoidι U hx).base ⁻¹' S := by
  ext w
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · rw [hw, hz]
    exact (hS.ge rfl).1
  · have hwC : avoidι U hx w ∈ S ∩ ((U : Set X)ᶜ ∪ {x}) :=
      ⟨hw, by rw [← range_avoidι U hx]; exact Set.mem_range_self w⟩
    rw [hS] at hwC
    exact (IsClosedImmersion.isClosedEmbedding (avoidι U hx)).injective (hwC.trans hz.symm)

/-- The point of the auxiliary closed subscheme over `x` is the preimage of `U`, hence **open**.
A point of the subscheme either lies outside `U` -- and then it is not in the preimage of `U` --
or equals `x`. -/
theorem isOpen_singleton_preimage (U : X.Opens) {x : X} (hx : IsClosed ({x} : Set X))
    (hxU : x ∈ U) {z : avoidSubscheme U hx} (hz : avoidι U hx z = x) :
    IsOpen ({z} : Set (avoidSubscheme U hx)) := by
  rw [singleton_eq_preimage_avoidι U hx hz (S := U)]
  · exact U.isOpen.preimage (avoidι U hx).base.hom.continuous
  · ext w
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun h => h.2.resolve_left (not_not.mpr h.1), by rintro rfl; exact ⟨hxU, Or.inr rfl⟩⟩

/-- The point of the auxiliary closed subscheme over `x` is the preimage of the closed set `{x}`,
hence **closed**. -/
theorem isClosed_singleton_preimage (U : X.Opens) {x : X} (hx : IsClosed ({x} : Set X))
    {z : avoidSubscheme U hx} (hz : avoidι U hx z = x) :
    IsClosed ({z} : Set (avoidSubscheme U hx)) := by
  rw [singleton_eq_preimage_avoidι U hx hz (S := {x})
    (Set.inter_eq_left.mpr Set.subset_union_right)]
  exact hx.preimage (avoidι U hx).base.hom.continuous

/-! ### Surjectivity of the restriction of global sections -/

/-- **Restriction of global sections to a closed subscheme, as the unit of the adjunction.** If
the evaluation at `⊤` of the unit of `i^* ⊣ i_*` is an epimorphism of modules, then the pullback
of global sections of [Stacks, Tag 0H78] is surjective.

There is nothing to it: `Stacks.NonvanishingPullback.pullbackGlobalSection` *is* that component
of the unit, by `Stacks.RingedSpace.pullbackUnit`, and an epimorphism of modules is a surjection.
The lemma exists so that the one statement this directory still owes -- the projection formula,
see the module documentation -- can be named at the shape its consumer wants. -/
theorem surjective_pullbackGlobalSection_of_epi {Y : Scheme.{u}} (i : Y ⟶ X) (M : X.Modules)
    (h : Epi ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
      ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app M))) :
    Function.Surjective (Stacks.NonvanishingPullback.pullbackGlobalSection i M) := by
  intro t
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective _).mp h t
  exact ⟨a, ha⟩

/-! ### The geometric step of Stacks Tag 0B5P -/

/-- **The geometric step of [Stacks, Tag 0B5P].** Let `P` be an invertible `𝒪_X`-module, `x` a
closed point of `X` and `U` an affine open containing `x`. If global sections of `P` surject onto
global sections of the pullback of `P` to the reduced closed subscheme on `(X ∖ U) ∪ {x}`, then
`x` lies in an affine nonvanishing locus of a global section of `P`.

The section is produced on the auxiliary subscheme, where `x` is a clopen point, and lifted. -/
theorem exists_affine_nonvanishingLocus_of_surjective (P : X.Modules)
    [Stacks.Ample.IsInvertibleModule X P] {x : X} (hx : IsClosed ({x} : Set X))
    {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U)
    (hsurj : Function.Surjective
      (Stacks.NonvanishingPullback.pullbackGlobalSection (avoidι U hx) P)) :
    ∃ s : Γ(P, ⊤), ∃ V : X.Opens,
      (V : Set X) = Stacks.Ample.nonvanishingLocus P s ∧ x ∈ V ∧ IsAffineOpen V := by
  obtain ⟨z, hz⟩ := exists_avoidι_eq U hx
  obtain ⟨t, ht⟩ := exists_nonvanishingLocus_eq_singleton
    ((modulePullback (avoidι U hx).toLRSHom.toShHom).obj P) z
    (isOpen_singleton_preimage U hx hxU hz) (isClosed_singleton_preimage U hx hz)
  obtain ⟨s, hs⟩ := hsurj t
  have hpre : (avoidι U hx).base ⁻¹' Stacks.Ample.nonvanishingLocus P s =
      ({z} : Set (avoidSubscheme U hx)) := by
    rw [Stacks.NonvanishingPullback.preimage_nonvanishingLocus (avoidι U hx) P s, hs, ht]
  have hxs : x ∈ Stacks.Ample.nonvanishingLocus P s := by
    rw [← hz]
    exact (Set.ext_iff.mp hpre z).mpr rfl
  have hle : Stacks.NonvanishingOpen.nonvanishingOpen X P s ≤ U := by
    intro w hw
    by_contra hwU
    obtain ⟨v, hv⟩ : w ∈ Set.range (avoidι U hx) := by
      rw [range_avoidι]
      exact Or.inl hwU
    have hvz : v = z := (Set.ext_iff.mp hpre v).mp (by
      rw [Set.mem_preimage, hv]
      exact hw)
    rw [hvz, hz] at hv
    exact hwU (hv ▸ hxU)
  refine ⟨s, Stacks.NonvanishingOpen.nonvanishingOpen X P s, rfl, hxs, ?_⟩
  have := Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen P s hU
  rwa [inf_eq_right.mpr hle] at this

/-- **[Stacks, Tag 0B5P] with the cohomology replaced by the surjectivity it produces.** An
invertible `𝒪_X`-module on a quasi-compact scheme is ample as soon as, at every closed point `x`
and every affine open `U` containing it, some positive tensor power has its global sections
surjecting onto those of its pullback to the reduced closed subscheme on `(X ∖ U) ∪ {x}`.

The reduction to closed points is
`Stacks.AmpleCohomologicalCriterion.isAmple_of_closed_points`; an affine open
through the point exists because the affine opens are a basis. -/
theorem isAmple_of_forall_surjective (X : Scheme.{u}) [CompactSpace X] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (h : ∀ (x : X) (hx : IsClosed ({x} : Set X)) (U : X.Opens), IsAffineOpen U → x ∈ U →
      ∃ n : ℕ, 1 ≤ n ∧ Function.Surjective
        (Stacks.NonvanishingPullback.pullbackGlobalSection (avoidι U hx)
          (Stacks.Ample.tensorPowModule X L (n : ℤ)))) :
    Stacks.Ample.IsAmple X L := by
  refine Stacks.AmpleCohomologicalCriterion.isAmple_of_closed_points X L fun x hx => ?_
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨n, hn, hsurj⟩ := h x hx U hU hxU
  obtain ⟨s, V, hV, hxV, hVaff⟩ :=
    exists_affine_nonvanishingLocus_of_surjective
      (Stacks.Ample.tensorPowModule X L (n : ℤ)) hx hU hxU hsurj
  exact ⟨n, hn, s, V, hV, hxV, hVaff⟩

end Stacks.Tag0B5PClopenLift

end
