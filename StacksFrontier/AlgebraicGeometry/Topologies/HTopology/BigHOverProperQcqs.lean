module

public import StacksFrontier.AlgebraicGeometry.Topologies.H.Limits
public import StacksFrontier.CategoryTheory.Sites.Descent.RestrictedBaseDescentData
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The chosen pullbacks of a proper morphism to an affine object of `(Sch/S)_h` are qcqs

Let `f : X ⟶ Y` be a morphism of `(Sch/S)_h` whose underlying morphism of schemes is proper, with
`Y` affine. Then `X`, `X ×_Y X` and `X ×_Y X ×_Y X` are quasi-compact and quasi-separated.

## Main results

* `AlgebraicGeometry.BigHOver.compactSpace_of_isProper` and
  `AlgebraicGeometry.BigHOver.quasiSeparatedSpace_of_isProper`: an object with a proper morphism
  to a quasi-compact quasi-separated object is quasi-compact quasi-separated.
* `AlgebraicGeometry.BigHOver.isProper_toScheme_map_of_isPullback`: properness of the underlying
  morphism of schemes is stable under base change in `(Sch/S)_h`.
* `AlgebraicGeometry.BigHOver.compactSpace_chosenPullback`, `…quasiSeparatedSpace_chosenPullback`,
  `…compactSpace_chosenPullback₃` and `…quasiSeparatedSpace_chosenPullback₃`: the self-fibre
  product and the triple self-fibre product of a proper morphism to an affine object are
  quasi-compact quasi-separated, in the chosen-pullback spelling
  `CategoryTheory.Limits.ChosenPullback.ofHasPullback` and
  `CategoryTheory.Limits.ChosenPullback₃.ofHasPullbacks`.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An object of `(Sch/S)_h` with a proper morphism to a quasi-compact object is quasi-compact. -/
theorem compactSpace_of_isProper {Z W : BigHOver B S hS} (g : Z ⟶ W)
    (hg : IsProper ((toScheme B S hS).map g)) [CompactSpace ((toScheme B S hS).obj W)] :
    CompactSpace ((toScheme B S hS).obj Z) :=
  QuasiCompact.compactSpace_of_compactSpace ((toScheme B S hS).map g)

/-- An object of `(Sch/S)_h` with a proper morphism to a quasi-separated object is
quasi-separated. -/
theorem quasiSeparatedSpace_of_isProper {Z W : BigHOver B S hS} (g : Z ⟶ W)
    (hg : IsProper ((toScheme B S hS).map g)) [QuasiSeparatedSpace ((toScheme B S hS).obj W)] :
    QuasiSeparatedSpace ((toScheme B S hS).obj Z) :=
  quasiSeparatedSpace_of_quasiSeparated ((toScheme B S hS).map g)

/-- Properness of the underlying morphism of schemes is stable under base change in
`(Sch/S)_h`. -/
theorem isProper_toScheme_map_of_isPullback {P X' X Y : BigHOver B S hS} {fst : P ⟶ X'}
    {snd : P ⟶ X} {f' : X' ⟶ Y} {f : X ⟶ Y} (h : IsPullback fst snd f' f)
    (hf' : IsProper ((toScheme B S hS).map f')) :
    IsProper ((toScheme B S hS).map snd) :=
  MorphismProperty.of_isPullback (P := @IsProper) (h.map (toScheme B S hS)) hf'

variable {X Y : BigHOver B S hS} (f : X ⟶ Y)

/-- The source of a proper morphism to an affine object of `(Sch/S)_h` is quasi-compact. -/
theorem compactSpace_source_of_isProper (hY : IsAffine ((toScheme B S hS).obj Y))
    (hf : IsProper ((toScheme B S hS).map f)) : CompactSpace ((toScheme B S hS).obj X) :=
  compactSpace_of_isProper f hf

/-- The source of a proper morphism to an affine object of `(Sch/S)_h` is quasi-separated. -/
theorem quasiSeparatedSpace_source_of_isProper (hY : IsAffine ((toScheme B S hS).obj Y))
    (hf : IsProper ((toScheme B S hS).map f)) : QuasiSeparatedSpace ((toScheme B S hS).obj X) :=
  quasiSeparatedSpace_of_isProper f hf

/-- The first projection of the chosen self-fibre product of a proper morphism is proper. -/
theorem isProper_chosenPullback_p₁ (hf : IsProper ((toScheme B S hS).map f)) :
    IsProper ((toScheme B S hS).map (ChosenPullback.ofHasPullback f f).p₁) :=
  isProper_toScheme_map_of_isPullback (IsPullback.of_hasPullback f f).flip hf

/-- The chosen self-fibre product of a proper morphism to an affine object of `(Sch/S)_h` is
quasi-compact. -/
theorem compactSpace_chosenPullback (hY : IsAffine ((toScheme B S hS).obj Y))
    (hf : IsProper ((toScheme B S hS).map f)) :
    CompactSpace ((toScheme B S hS).obj (ChosenPullback.ofHasPullback f f).pullback) :=
  have := compactSpace_source_of_isProper f hY hf
  compactSpace_of_isProper _ (isProper_chosenPullback_p₁ f hf)

/-- The chosen self-fibre product of a proper morphism to an affine object of `(Sch/S)_h` is
quasi-separated. -/
theorem quasiSeparatedSpace_chosenPullback (hY : IsAffine ((toScheme B S hS).obj Y))
    (hf : IsProper ((toScheme B S hS).map f)) :
    QuasiSeparatedSpace ((toScheme B S hS).obj (ChosenPullback.ofHasPullback f f).pullback) :=
  have := quasiSeparatedSpace_source_of_isProper f hY hf
  quasiSeparatedSpace_of_isProper _ (isProper_chosenPullback_p₁ f hf)

/-- The first projection of the chosen triple self-fibre product of a proper morphism, to the
self-fibre product, is proper. -/
theorem isProper_chosenPullback₃_p₁₂ (hf : IsProper ((toScheme B S hS).map f)) :
    IsProper ((toScheme B S hS).map (ChosenPullback₃.ofHasPullbacks
      (ChosenPullback.ofHasPullback f f) (ChosenPullback.ofHasPullback f f)
      (ChosenPullback.ofHasPullback f f)).chosenPullback.p₁) :=
  isProper_toScheme_map_of_isPullback (IsPullback.of_hasPullback
      (ChosenPullback.ofHasPullback f f).p₂ (ChosenPullback.ofHasPullback f f).p₁).flip
    (isProper_chosenPullback_p₁ f hf)

/-- The chosen triple self-fibre product of a proper morphism to an affine object of
`(Sch/S)_h` is quasi-compact. -/
theorem compactSpace_chosenPullback₃ (hY : IsAffine ((toScheme B S hS).obj Y))
    (hf : IsProper ((toScheme B S hS).map f)) :
    CompactSpace ((toScheme B S hS).obj (ChosenPullback₃.ofHasPullbacks
      (ChosenPullback.ofHasPullback f f) (ChosenPullback.ofHasPullback f f)
      (ChosenPullback.ofHasPullback f f)).pullback) :=
  have := compactSpace_chosenPullback f hY hf
  compactSpace_of_isProper _ (isProper_chosenPullback₃_p₁₂ f hf)

/-- The chosen triple self-fibre product of a proper morphism to an affine object of
`(Sch/S)_h` is quasi-separated. -/
theorem quasiSeparatedSpace_chosenPullback₃ (hY : IsAffine ((toScheme B S hS).obj Y))
    (hf : IsProper ((toScheme B S hS).map f)) :
    QuasiSeparatedSpace ((toScheme B S hS).obj (ChosenPullback₃.ofHasPullbacks
      (ChosenPullback.ofHasPullback f f) (ChosenPullback.ofHasPullback f f)
      (ChosenPullback.ofHasPullback f f)).pullback) :=
  have := quasiSeparatedSpace_chosenPullback f hY hf
  quasiSeparatedSpace_of_isProper _ (isProper_chosenPullback₃_p₁₂ f hf)

end AlgebraicGeometry.BigHOver

end
