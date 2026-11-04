module

public import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.Cocycle

/-!
# Extending an invertible module from an open subscheme

Let `U` be an open of a scheme `X` and let `N` be an invertible `𝒪_U`-module. Suppose given a
family of opens `W : ι → X.Opens` covering `X`, meeting pairwise inside `U`, and such that `N`
is trivial on each `U.ι ⁻¹ᵁ W i`. Then `N` is the pullback of an invertible `𝒪_X`-module: the
transition units of the chart generators of `N` are carried to a unit cocycle on `X`
(`Stacks.PicSurjectiveOpen.cocycleX`), and the module glued from that cocycle pulls back to `N`.

This is the gluing half of clause (2) of
[Stacks, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA), which asserts that
`Pic(X) → Pic(U)` is surjective for a retrocompact open `U` with discrete complement along which
the local rings are Noetherian of dimension at most one. In that situation the charts are a
trivializing cover of `U` together with one isolating neighbourhood per point of the complement:
two isolating neighbourhoods meet only inside `U` because each meets the complement in one
point, and the remaining input — triviality of `N` on the part of an isolating neighbourhood
inside `U` — is the spreading-out statement of
`StacksFrontier/AlgebraicGeometry/Variety/NoetherianDimensionOne/PuncturedFreeness.lean`.

Nothing here is specific to that situation: no finiteness, Noetherian or dimension hypothesis
appears, and the complement of `U` is arbitrary.

## Main results

* `Stacks.PicSurjectiveOpen.exists_isInvertible_modulePullback_iso`: **the extension statement**
  — an invertible module on `U` trivialized by such a family is the pullback of an invertible
  module on `X`.
* `Stacks.PicSurjectiveOpen.isInvertible_glue_cocycleX`: the glued module is invertible.
* `Stacks.PicSurjectiveOpen.ratio_pullbackGenerator`: the transition units of the pulled-back
  chart generators of the glued module are those of the chart generators of `N`.

## The comparison

Invertibility of the glued module is free: it is clause 1 of Tag 0B8M applied to the chart
trivializations, which is `Stacks.SheafOfModules.UnitTransitionCocycle.isInvertible_glue`. The
comparison with `N` is recognition, `Stacks.SheafOfModules.isoOfChartGenerators`: two modules on
the same space carrying generators over a common covering family with the same transition units
are isomorphic. The two modules live on `U`, the common family is the preimages
`U.ι ⁻¹ᵁ W i`, and the generators are those of `N` on one side and, on the other, the pullbacks
along `U.ι` of the chart generators of the glue
(`Stacks.SheafOfModules.pullbackGenerator`).

That their transition units agree is `ratio_pullbackGenerator`, and it is where every ingredient
meets. Over the overlap of two *distinct* charts — an open inside `U` — the ratio of two
pulled-back generators is the pullback of the ratio upstairs
(`Stacks.SheafOfModules.generatorRatioUnit_pullbackGenerator`), that ratio is the transition unit
of the glued cocycle
(`Stacks.SheafOfModules.UnitTransitionCocycle.generatorRatioUnit_chartGenerator`), and the
transition unit was defined as the ratio downstairs carried along `invApp`, which the pullback
undoes. Over an open inside a *single* chart both ratios are `1`. A general open inside two
charts is reduced to the overlap of the two charts by
`Stacks.SheafOfModules.generatorRatioUnit_restrict`.

## Implementation notes

Every rewrite against the generator API is performed on a fully instantiated form of the lemma.
The reason is the transparency gap the repository documents elsewhere: `N` is presented as
`U.toScheme.Modules`, i.e. over `U.toScheme.ringCatSheaf`, while the generator API is stated over
`Stacks.SheafOfModules.structureSheaf _.sheaf`, and the two are equal only by unfolding a plain
`def`. Elaboration of an explicit argument crosses that gap; `rw`, which unifies at reducible
transparency, does not — `rw [generatorRatioUnit_restrict]` fails on a goal whose
module is `N` while `rw [generatorRatioUnit_restrict N …]` succeeds on the same goal.

The pullback is `RingedSpaceModuleAdjunction.modulePullback U.ι.toLRSHom.toShHom`, which is the
spelling `Stacks.SheafOfModules.pullbackGenerator` produces and the one Tag 09NY is stated at in
`StacksFrontier/AlgebraicGeometry/LiftInvertible/Basic.lean`; it is equal to
`AlgebraicGeometry.Scheme.Modules.pullback U.ι` by `rfl`.

## References

* [Stacks Project, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules RingedSpaceModuleAdjunction

universe u

namespace Stacks.PicSurjectiveOpen

variable {X : Scheme.{u}} {U : X.Opens} {ι : Type u} {W : ι → X.Opens}

/-- For an open `V ≤ U` of `X`, the map `U.ι.app V` on sections inverts `invApp`. -/
theorem app_invApp_apply {V : X.Opens} (hV : V ≤ U) (r : Γ(U.toScheme, U.ι ⁻¹ᵁ V)) :
    (U.ι.app V).hom ((invApp hV).hom r) = r := by
  rw [← CommRingCat.comp_apply, invApp_app]
  rfl

/-- For an open `V ≤ U` of `X`, the map `U.ι.app V` on units of sections inverts `invApp`. -/
theorem app_invApp_units {V : X.Opens} (hV : V ≤ U) (u : (Γ(U.toScheme, U.ι ⁻¹ᵁ V))ˣ) :
    Units.map (U.ι.app V).hom.toMonoidHom (Units.map (invApp hV).hom.toMonoidHom u) = u := by
  refine Units.ext ?_
  show (U.ι.app V).hom ((invApp hV).hom (u : Γ(U.toScheme, U.ι ⁻¹ᵁ V))) = (u : _)
  exact app_invApp_apply hV _

/-- If the opens `W i` cover `X`, then their preimages `U.ι ⁻¹ᵁ W i` cover `U`. -/
theorem top_le_iSup_preimage (hcov : (⊤ : X.Opens) ≤ ⨆ i, W i) :
    (⊤ : Opens U.toScheme.carrier) ≤ ⨆ i, U.ι ⁻¹ᵁ W i := by
  intro x _
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov (show U.ι.base x ∈ (⊤ : X.Opens) from trivial))
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

variable {N : U.toScheme.Modules}
  (q : ∀ i, GeneratorSections U.toScheme.toRingedSpace N (U.ι ⁻¹ᵁ W i))
  (hWU : ∀ i j, i ≠ j → W i ⊓ W j ≤ U)
  (hcov : (⊤ : X.Opens) ≤ ⨆ i, W i)

include hcov in
/-- The module glued from the cocycle `cocycleX` of the chart generators of `N` is invertible. -/
theorem isInvertible_glue_cocycleX :
    IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property
      (cocycleX (cocycleOfChartGenerators q) hWU).glue :=
  (cocycleX (cocycleOfChartGenerators q) hWU).isInvertible_glue hcov

/-- The transition units of the pulled-back chart generators are those of the chart generators
of `N`, over the overlap of two distinct charts. -/
theorem ratio_pullbackGenerator_inf (i j : ι) (hij : i ≠ j) :
    generatorRatioUnit N (U.ι ⁻¹ᵁ (W i ⊓ W j))
        (generatorRestrict N (preimage_mono (inf_le_right : W i ⊓ W j ≤ W j)) (q j))
        (generatorRestrict N (preimage_mono (inf_le_left : W i ⊓ W j ≤ W i)) (q i)) =
      generatorRatioUnit
        ((modulePullback U.ι.toLRSHom.toShHom).obj (cocycleX (cocycleOfChartGenerators q) hWU).glue)
        (U.ι ⁻¹ᵁ (W i ⊓ W j))
        (generatorRestrict _ (preimage_mono (inf_le_right : W i ⊓ W j ≤ W j))
          (pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W j)
            ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov j)))
        (generatorRestrict _ (preimage_mono (inf_le_left : W i ⊓ W j ≤ W i))
          (pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W i)
            ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov i))) := by
  have e1 : generatorRestrict _ (preimage_mono (inf_le_right : W i ⊓ W j ≤ W j))
        (pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W j)
          ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov j)) =
      pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W i ⊓ W j)
        (generatorRestrict _ (inf_le_right : W i ⊓ W j ≤ W j)
          ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov j)) :=
    pullbackGenerator_restrict U.ι _ (isInvertible_glue_cocycleX q hWU hcov)
      (inf_le_right : W i ⊓ W j ≤ W j) _
  have e2 : generatorRestrict _ (preimage_mono (inf_le_left : W i ⊓ W j ≤ W i))
        (pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W i)
          ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov i)) =
      pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W i ⊓ W j)
        (generatorRestrict _ (inf_le_left : W i ⊓ W j ≤ W i)
          ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov i)) :=
    pullbackGenerator_restrict U.ι _ (isInvertible_glue_cocycleX q hWU hcov)
      (inf_le_left : W i ⊓ W j ≤ W i) _
  have h3 := generatorRatioUnit_pullbackGenerator U.ι
      (cocycleX (cocycleOfChartGenerators q) hWU).glue (isInvertible_glue_cocycleX q hWU hcov)
      (W i ⊓ W j)
      (generatorRestrict _ (inf_le_right : W i ⊓ W j ≤ W j)
        ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov j))
      (generatorRestrict _ (inf_le_left : W i ⊓ W j ≤ W i)
        ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov i))
  have h4 := (cocycleX (cocycleOfChartGenerators q) hWU).generatorRatioUnit_chartGenerator hcov
      i j (inf_le_left : W i ⊓ W j ≤ W i) (inf_le_right : W i ⊓ W j ≤ W j)
  rw [e1, e2, h3, h4,
    cocycleX_transition,
    transitionX_of_le _ hWU i j (W i ⊓ W j) inf_le_left inf_le_right (hWU i j hij), transUnit,
    app_invApp_units]
  exact (cocycleOfChartGenerators_transition q i j _ _ _).symm

include hcov in
/-- The transition units of the pulled-back chart generators agree with those of the chart
generators of `N` over every open inside two charts. -/
theorem ratio_pullbackGenerator (i j : ι) (A : Opens U.toScheme.carrier)
    (hi : A ≤ U.ι ⁻¹ᵁ W i) (hj : A ≤ U.ι ⁻¹ᵁ W j) :
    generatorRatioUnit N A (generatorRestrict N hj (q j)) (generatorRestrict N hi (q i)) =
      generatorRatioUnit
        ((modulePullback U.ι.toLRSHom.toShHom).obj (cocycleX (cocycleOfChartGenerators q) hWU).glue)
        A
        (generatorRestrict _ hj
          (pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W j)
            ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov j)))
        (generatorRestrict _ hi
          (pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W i)
            ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov i))) := by
  by_cases hij : i = j
  · subst hij
    exact (generatorRatioUnit_self N A _).trans (generatorRatioUnit_self _ A _).symm
  · have hAB : A ≤ U.ι ⁻¹ᵁ (W i ⊓ W j) := fun x hx => ⟨hi hx, hj hx⟩
    have hNj : generatorRestrict N hj (q j) =
        generatorRestrict N hAB
          (generatorRestrict N (preimage_mono (inf_le_right : W i ⊓ W j ≤ W j)) (q j)) :=
      (generatorRestrict_trans N _ _ _).symm
    have hNi : generatorRestrict N hi (q i) =
        generatorRestrict N hAB
          (generatorRestrict N (preimage_mono (inf_le_left : W i ⊓ W j ≤ W i)) (q i)) :=
      (generatorRestrict_trans N _ _ _).symm
    have hPj : generatorRestrict _ hj
          (pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W j)
            ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov j)) =
        generatorRestrict _ hAB
          (generatorRestrict _ (preimage_mono (inf_le_right : W i ⊓ W j ≤ W j))
            (pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W j)
              ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov j))) :=
      (generatorRestrict_trans _ _ _ _).symm
    have hPi : generatorRestrict _ hi
          (pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W i)
            ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov i)) =
        generatorRestrict _ hAB
          (generatorRestrict _ (preimage_mono (inf_le_left : W i ⊓ W j ≤ W i))
            (pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W i)
              ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov i))) :=
      (generatorRestrict_trans _ _ _ _).symm
    have eN := generatorRatioUnit_restrict N hAB
      (generatorRestrict N (preimage_mono (inf_le_right : W i ⊓ W j ≤ W j)) (q j))
      (generatorRestrict N (preimage_mono (inf_le_left : W i ⊓ W j ≤ W i)) (q i))
    have eP := generatorRatioUnit_restrict
      ((modulePullback U.ι.toLRSHom.toShHom).obj
        (cocycleX (cocycleOfChartGenerators q) hWU).glue) hAB
      (generatorRestrict _ (preimage_mono (inf_le_right : W i ⊓ W j ≤ W j))
        (pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W j)
          ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov j)))
      (generatorRestrict _ (preimage_mono (inf_le_left : W i ⊓ W j ≤ W i))
        (pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W i)
          ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov i)))
    rw [hNj, hNi, hPj, hPi, eN, eP, ratio_pullbackGenerator_inf q hWU hcov i j hij]

include q hWU hcov in
/-- **Every invertible module on an open subscheme trivialized by a family of opens of the
ambient scheme meeting pairwise inside it is the pullback of an invertible module.** -/
theorem exists_isInvertible_modulePullback_iso :
    ∃ (L : X.Modules)
      (_ : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L),
      Nonempty ((modulePullback U.ι.toLRSHom.toShHom).obj L ≅ N) :=
  ⟨(cocycleX (cocycleOfChartGenerators q) hWU).glue, isInvertible_glue_cocycleX q hWU hcov,
    ⟨isoOfChartGenerators _ N
      (fun i => pullbackGenerator U.ι _ (isInvertible_glue_cocycleX q hWU hcov) (W i)
        ((cocycleX (cocycleOfChartGenerators q) hWU).chartGenerator hcov i))
      q (ratio_pullbackGenerator q hWU hcov) (top_le_iSup_preimage hcov)⟩⟩

end Stacks.PicSurjectiveOpen

end
