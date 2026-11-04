module

public import StacksFrontier.AlgebraicGeometry.AmpleThickeningAscent.FirstOrder
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.StalkBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Filtration

/-!
# Ampleness ascends along a thickening of finite order

Let `t : Y ⟶ Y'` be a closed immersion some power of whose ideal sheaf vanishes, and let `𝓛'` be
an invertible `𝒪_{Y'}`-module with `t^* 𝓛'` ample. Then `𝓛'` is ample. This is the hard
implication of [Stacks, Tag 09MS] for a thickening of finite order, with no Noetherian hypothesis;
over a quasi-compact locally Noetherian scheme every thickening is of finite order, which gives
the implication of [Stacks, Tag 09MS] itself.

The closed subschemes `Yᵢ` cut out by the powers `ℐ ^ (i + 1)` of the ideal sheaf of `t` form a
chain `Y ≅ Y₀ ⟶ Y₁ ⟶ ⋯ ⟶ Yₙ ≅ Y'` of first-order thickenings
(`Stacks.Thickenings.PowerFiltration.baseStep_firstOrder`), and ampleness climbs it one step at a
time by `Stacks.AmpleThickeningAscent.isAmple_of_isAmple_pullback_of_isFirstOrderThickening`.

## Main results

* `Stacks.AmpleThickeningAscent.isAmple_of_isAmple_pullback_of_isIso`: ampleness descends along
  an isomorphism of schemes.
* `Stacks.AmpleThickeningAscent.isAmple_of_isAmple_pullback_of_isFiniteOrderThickening`.
* `Stacks.AmpleThickeningAscent.isAmple_of_isAmple_pullback_of_isLocallyNoetherian`: the case of a
  locally Noetherian ambient scheme.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.Ample
open Stacks.Thickenings
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.AmpleThickeningAscent

/-- **Ampleness descends along an isomorphism of schemes.** If `f : A ⟶ B` is an isomorphism and
`f^* M` is ample then `M` is ample: pull back along `f⁻¹` and use `(f⁻¹ ≫ f)^* M ≅ 𝟙^* M ≅ M`. -/
theorem isAmple_of_isAmple_pullback_of_isIso {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (M : B.Modules) [IsInvertibleModule B M] (h : IsAmple A (pullbackModule f M)) :
    IsAmple B M := by
  have h1 : IsAmple B (pullbackModule (inv f ≫ f) M) :=
    Stacks.AmpleFibreNeighbourhood.isAmple_pullbackModule_comp_of_isIso (inv f) f M h
  have h2 : IsAmple B (pullbackModule (𝟙 B) M) :=
    (Stacks.RelativeVeryAmple.isAmple_congr _ _
      (Stacks.RelativeAmpleBaseChange.pullbackModuleCongr (IsIso.inv_hom_id f) M)).mp h1
  have : IsInvertibleModule B (pullbackModule (𝟙 B) M) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback (𝟙 B) M
  exact (Stacks.RelativeVeryAmple.isAmple_congr (pullbackModule (𝟙 B) M) M
    ((Stacks.PullbackPseudofunctor.modulePullbackIdIso B.toRingedSpace).app M)).mp h2

/-- **Ampleness ascends along a thickening of finite order.** For a closed immersion
`t : Y ⟶ Y'` with `ℐ ^ (n + 1) = 0` for its ideal sheaf `ℐ`, and an invertible `𝒪_{Y'}`-module
`𝓛'`, ampleness of `t^* 𝓛'` gives ampleness of `𝓛'`. -/
theorem isAmple_of_isAmple_pullback_of_isFiniteOrderThickening {Y Y' : Scheme.{u}} {t : Y ⟶ Y'}
    (ht : IsFiniteOrderThickening t) (L' : Y'.Modules) [IsInvertibleModule Y' L']
    (h : IsAmple Y (pullbackModule t L')) : IsAmple Y' L' := by
  obtain ⟨hclosed, n, hn⟩ := ht
  have key : ∀ i : ℕ,
      IsAmple (PowerFiltration.baseLevel t i)
        (pullbackModule (PowerFiltration.baseInclusion t i) L') := by
    intro i
    induction i with
    | zero =>
      have := PowerFiltration.baseInitialMap_isIso t hclosed
      refine isAmple_of_isAmple_pullback_of_isIso (PowerFiltration.baseInitialMap t) _ ?_
      refine (Stacks.RelativeVeryAmple.isAmple_congr _ _
        (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso _ _ L')).mp ?_
      refine (Stacks.RelativeVeryAmple.isAmple_congr _ _
        (Stacks.RelativeAmpleBaseChange.pullbackModuleCongr
          (PowerFiltration.baseInitialMap_comp_inclusion t).symm L')).mp h
    | succ i ih =>
      refine isAmple_of_isAmple_pullback_of_isFirstOrderThickening
        (PowerFiltration.baseStep_firstOrder t i) _ ?_
      refine (Stacks.RelativeVeryAmple.isAmple_congr _ _
        (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso _ _ L')).mp ?_
      exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
        (Stacks.RelativeAmpleBaseChange.pullbackModuleCongr
          (PowerFiltration.baseStep_comp_inclusion t i).symm L')).mp ih
  have := PowerFiltration.baseInclusion_isIso t hn
  exact isAmple_of_isAmple_pullback_of_isIso _ L' (key n)

/-- **Ampleness ascends along a thickening of a locally Noetherian scheme**: such a thickening is
of finite order (`Stacks.Thickenings.isFiniteOrderThickening_of_isThickening`), the ambient scheme
being quasi-compact because it is homeomorphic to the closed subscheme. -/
theorem isAmple_of_isAmple_pullback_of_isLocallyNoetherian {Y Y' : Scheme.{u}} {t : Y ⟶ Y'}
    (ht : IsThickening t) [IsLocallyNoetherian Y'] (L' : Y'.Modules) [IsInvertibleModule Y' L']
    (h : IsAmple Y (pullbackModule t L')) : IsAmple Y' L' := by
  have : CompactSpace Y := h.1
  have : CompactSpace Y' := ht.homeomorph.compactSpace
  exact isAmple_of_isAmple_pullback_of_isFiniteOrderThickening
    (isFiniteOrderThickening_of_isThickening ht) L' h

end Stacks.AmpleThickeningAscent

end
