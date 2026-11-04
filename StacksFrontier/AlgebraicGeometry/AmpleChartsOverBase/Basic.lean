module

public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Generation
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers
public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers

/-!
# Step 1 of Stacks Tag 01VS, with the clause over the base

Step 1 of the proof of [Stacks, Tag 01VS] asks for a *finite* family of global sections of one
common positive tensor power of an ample `L` whose nonvanishing opens are affine, cover `X`, **and
each map into an affine open of the base `S`**. The last clause is what step 2 of the source
consumes: it is the clause that makes the ring map `𝒪_S(Vᵢ) → 𝒪_X(X_{aᵢ})` a map of rings of
global sections of two affine schemes, so that [Stacks, Tag 01T2] applies to it.

`Stacks.AmpleImmersionReduction.exists_generating_family_of_isAmple` already supplies the family
without that clause, and
`../AmpleImmersionReduction/Basic.lean` records in its step 1 that the clause is missing and that
its signature "mentions no base scheme at all", so the refinement was folded into the hypothesis
`Stacks.AmpleImmersionReduction.ChartImmersion`. This file proves the clause instead.

## The argument

The refinement costs nothing beyond ampleness, because ampleness gives a *basis*, not merely a
cover. For `x : X` pick any affine open `V ∋ f(x)` of `S` — the affine opens of a scheme are a
basis, `AlgebraicGeometry.Scheme.isBasis_affineOpens` — and then apply clause (4) of
[Stacks, Tag 01Q3] to the open `f⁻¹(V) ∋ x`:
`Stacks.SectionExtension.isBasisAffineNonvanishing_of_isAmple` returns a degree `n ≥ 1` and a
global section `s` of `L ^⊗ n` with `X_s` affine, containing `x` and **contained in `f⁻¹(V)`**.
Quasi-compactness of `X` (part of ampleness) cuts the resulting cover down to a finite subfamily,
and `Stacks.FinGenFromCover.exists_common_degree_family` equalises the degrees by replacing each
member with a power of itself — which leaves `X_{aᵢ}` *unchanged*, so both the affineness and the
containment in `f⁻¹(Vᵢ)` survive the equalisation. That is the whole point of stating the
equalisation with `nvLocus L (a' i) = nvLocus L (a i)` rather than with an inclusion.

## Main results

* `Stacks.AmpleChartsOverBase.exists_pos_affine_nvOpen_le_preimage`: the pointwise form — every
  point of `X` lies in an affine `X_s`, for `s` a global section of a positive power of `L`, which
  maps into an affine open of `S`.
* `Stacks.AmpleChartsOverBase.exists_generating_family_over_of_isAmple`: **step 1 of
  [Stacks, Tag 01VS] in full**, with every clause the source states. It is
  `Stacks.AmpleImmersionReduction.exists_generating_family_of_isAmple` plus the clause over the
  base.
* `Stacks.AmpleChartsOverBase.exists_generating_hom_over_of_isAmple`: steps 1 and 3 together —
  the same family, with the morphism to `ℙⁿ_S` that it defines, pinned on every chart.

## What this does *not* do

It does not prove `Stacks.AmpleImmersionReduction.ChartImmersion`, and it attaches no tag. Beyond
step 1 that condition still owes the finite type generators of [Stacks, Tag 01T2], the
equalisation of the degrees of those generators' numerators against the degree produced here, and
the passage from surjectivity on each chart to `AlgebraicGeometry.IsImmersion`. What this file
supplies towards it is exactly the cover refinement.

The degree produced here is in general *larger* than the one
`Stacks.AmpleImmersionReduction.exists_generating_family_of_isAmple` produces, and neither is
canonical: both are products of the degrees occurring in one `Classical.choice`-chosen finite
subcover.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01T2](https://stacks.math.columbia.edu/tag/01T2)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample Stacks.ProjectiveFromSections

universe u

namespace Stacks.AmpleChartsOverBase

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]

/-! ### The pointwise refinement -/

/-- **Every point lies in an affine `X_s` mapping into an affine open of the base.** The degree is
positive, `s` is a global section of that power of `L`, and `X_s` is affine.

The affine opens of `S` are a basis, so an affine `V ∋ f(x)` can be chosen first; clause (4) of
[Stacks, Tag 01Q3] — which ampleness supplies unconditionally, by
`Stacks.SectionExtension.isBasisAffineNonvanishing_of_isAmple` — then produces `X_s` *inside*
`f⁻¹(V)`. Ampleness is used as a basis statement and not as a cover statement, and that is the
only reason the refinement is free. -/
theorem exists_pos_affine_nvOpen_le_preimage (hL : IsAmple X L) {S : Scheme.{u}} (f : X ⟶ S)
    (x : X) :
    ∃ (n : ℕ) (s : Γ(tensorPowModule X L (n : ℤ), ⊤)) (V : S.Opens),
      1 ≤ n ∧ IsAffineOpen V ∧ IsAffineOpen (nvOpen (tensorPowModule X L (n : ℤ)) s) ∧
        x ∈ nvOpen (tensorPowModule X L (n : ℤ)) s ∧
        nvOpen (tensorPowModule X L (n : ℤ)) s ≤ f ⁻¹ᵁ V := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  obtain ⟨n, hn, s, haff, hxs, hsV⟩ :=
    Stacks.SectionExtension.isBasisAffineNonvanishing_of_isAmple X L hL x (f ⁻¹ᵁ V) hxV
  exact ⟨n, s, V, hn, hV, haff, hxs, hsV⟩

/-! ### Step 1 of Stacks Tag 01VS -/

/-- **Step 1 of the proof of [Stacks, Tag 01VS], with every clause the source states.** From
ampleness alone: one degree `N ≥ 1`, a family of global sections of `L ^⊗ N` indexed by
`Fin (n + 1)` which generates every stalk, whose nonvanishing opens are affine, **and each of
which maps into an affine open of `S`**.

This is `Stacks.AmpleImmersionReduction.exists_generating_family_of_isAmple` with the last clause
added. The construction is that theorem's, run on
`Stacks.AmpleChartsOverBase.exists_pos_affine_nvOpen_le_preimage` instead of on the pointwise
cover with no base clause, and it goes through because
`Stacks.FinGenFromCover.exists_common_degree_family` leaves each `X_{aᵢ}` unchanged while
equalising degrees. The padding index carries the zero section, whose nonvanishing open is `⊥`;
it maps into the affine open `⊥` of `S`. -/
theorem exists_generating_family_over_of_isAmple (hL : IsAmple X L) {S : Scheme.{u}} (f : X ⟶ S) :
    ∃ (N : ℕ) (n : ℕ) (s : Fin (n + 1) → Γ(tensorPowModule X L (N : ℤ), ⊤)),
      1 ≤ N ∧ GeneratesStalks s ∧ (∀ i, IsAffineOpen (nvCover s i)) ∧
        ∀ i, ∃ V : S.Opens, IsAffineOpen V ∧ nvCover s i ≤ f ⁻¹ᵁ V := by
  classical
  have := hL.compactSpace
  choose m a V hm hVaff haff hmem hle using exists_pos_affine_nvOpen_le_preimage L hL f
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun y : X => (nvOpen (tensorPowModule X L (m y : ℤ)) (a y) : Set X))
    (fun y => (nvOpen (tensorPowModule X L (m y : ℤ)) (a y)).2)
    fun x _ => Set.mem_iUnion.mpr ⟨x, hmem x⟩
  choose b hb using fun y : X =>
    Stacks.AmpleFiniteAvoidance.exists_powSections_nvLocus_eq L (m y) (a y)
  obtain ⟨N, b', hN, hb'⟩ :=
    Stacks.FinGenFromCover.exists_common_degree_family L (ι := {y : X // y ∈ F})
      (fun i => m i.1) (fun i => hm i.1) fun i => b i.1
  choose t ht using fun i : {y : X // y ∈ F} =>
    Stacks.FinGenFromCover.exists_global_nonvanishingLocus_eq L N (b' i)
  set eqv := F.equivFin
  set s : Fin (F.card + 1) → Γ(tensorPowModule X L (N : ℤ), ⊤) :=
    Fin.lastCases 0 fun j => t (eqv.symm j) with hs
  -- The padding chart is `⊥`, and the equalised family has exactly the original charts.
  have hlast : nvCover s (Fin.last _) = ⊥ := by
    rw [hs, nvCover, Fin.lastCases_last]
    refine TopologicalSpace.Opens.ext ?_
    rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen, nonvanishingLocus_zero]
    rfl
  have hcs : ∀ j, nvCover s j.castSucc = nvOpen (tensorPowModule X L (m (eqv.symm j).1 : ℤ))
      (a (eqv.symm j).1) := fun j => by
    rw [hs, nvCover, Fin.lastCases_castSucc]
    refine TopologicalSpace.Opens.ext ?_
    rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen,
      Stacks.NonvanishingOpen.coe_nonvanishingOpen, ht, hb', hb]
  have hP : ∀ i, IsAffineOpen (nvCover s i) ∧
      ∃ V : S.Opens, IsAffineOpen V ∧ nvCover s i ≤ f ⁻¹ᵁ V := by
    refine Fin.lastCases ?_ fun j => ?_
    · rw [hlast]
      exact ⟨isAffineOpen_bot X, ⊥, isAffineOpen_bot S, bot_le⟩
    · rw [hcs]
      exact ⟨haff _, V _, hVaff _, hle _⟩
  refine ⟨N, F.card, s, hN, ?_, fun i => (hP i).1, fun i => (hP i).2⟩
  refine Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ x))
  exact ⟨(eqv ⟨y, hy⟩).castSucc, by rwa [hcs, Equiv.symm_apply_apply]⟩

/-! ### Step 2's first input, from Mathlib -/

/-- **Step 1 of [Stacks, Tag 01VS] together with the first input of step 2.** On each chart of the
refined cover the ring map `𝒪_S(Vᵢ) ⟶ 𝒪_X(X_{aᵢ})` is of finite type.

This is [Stacks, Tag 01T2], and **it is in Mathlib**: `LocallyOfFiniteType` is registered as a
`AlgebraicGeometry.HasRingHomProperty` for `RingHom.FiniteType`
(`Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean`), and
`AlgebraicGeometry.HasRingHomProperty.appLE` is exactly the statement that the induced map between
the sections over an affine open of the target and an affine open of the source inside its
preimage has the ring-level property. No project tag `01T2` exists anywhere in this repository, so
the statement looks absent; the content is not.

What makes it applicable is the clause over the base — without an affine `V` containing the image
of the chart there is no affine source of the ring map, which is why this could not be stated
against `Stacks.AmpleImmersionReduction.exists_generating_family_of_isAmple`. What remains of step
2 is [Stacks, Tag 01PW]: writing the finitely many algebra generators this produces as ratios
`a_{ij} / aᵢ^{e_{ij}}`, and equalising the resulting degrees against `N`. -/
theorem exists_generating_family_finiteType_of_isAmple (hL : IsAmple X L) {S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    ∃ (N : ℕ) (n : ℕ) (s : Fin (n + 1) → Γ(tensorPowModule X L (N : ℤ), ⊤)),
      1 ≤ N ∧ GeneratesStalks s ∧ (∀ i, IsAffineOpen (nvCover s i)) ∧
        ∀ i, ∃ (V : S.Opens) (_ : IsAffineOpen V) (e : nvCover s i ≤ f ⁻¹ᵁ V),
          RingHom.FiniteType (f.appLE V (nvCover s i) e).hom := by
  obtain ⟨N, n, s, hN, hgen, haff, hover⟩ := exists_generating_family_over_of_isAmple L hL f
  refine ⟨N, n, s, hN, hgen, haff, fun i => ?_⟩
  obtain ⟨V, hV, hle⟩ := hover i
  exact ⟨V, hV, hle, AlgebraicGeometry.HasRingHomProperty.appLE @LocallyOfFiniteType f
    ‹LocallyOfFiniteType f› ⟨V, hV⟩ ⟨nvCover s i, haff i⟩ hle⟩

/-! ### Steps 1 and 3 together -/

/-- **Steps 1 and 3 of the proof of [Stacks, Tag 01VS], with every clause of step 1.** The family
of `Stacks.AmpleChartsOverBase.exists_generating_family_over_of_isAmple` together with the
morphism to projective space over `S` that
`Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks` builds from
it, pinned on every chart.

This is `Stacks.AmpleImmersionReduction.exists_generating_hom_of_isAmple` with the clause over the
base added; it says nothing about `𝒪(1)`, which remains
`Stacks.AmpleImmersionReduction.TwistPullback`. -/
theorem exists_generating_hom_over_of_isAmple (hL : IsAmple X L) {S : Scheme.{u}} (f : X ⟶ S) :
    ∃ (N : ℕ) (n : ℕ) (s : Fin (n + 1) → Γ(tensorPowModule X L (N : ℤ), ⊤))
      (p : X ⟶ projectiveSpaceOver n S),
      1 ≤ N ∧ GeneratesStalks s ∧ (∀ i, IsAffineOpen (nvCover s i)) ∧
        (∀ i, ∃ V : S.Opens, IsAffineOpen V ∧ nvCover s i ≤ f ⁻¹ᵁ V) ∧
        p ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
        ∀ i, (nvCover s i).ι ≫ p ≫ projectiveSpaceOver.toIntegralAtUniverse n S =
          Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse (chartRatio s i)
            (span_range_chartRatio s i) := by
  obtain ⟨N, n, s, hN, hgen, haff, hover⟩ := exists_generating_family_over_of_isAmple L hL f
  obtain ⟨p, hpf, hchart⟩ :=
    Stacks.ProjGlobalSectionsAppTop.exists_hom_projectiveSpaceOver_of_generatesStalks s hgen f
  exact ⟨N, n, s, p, hN, hgen, haff, hover, hpf, hchart⟩

end Stacks.AmpleChartsOverBase

end
