module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams

/-!
# Both sides of the base change map of higher direct images are quasi-coherent

Let

```
  X' ———→ X
   | f'    | f
   v       v
  Y' ———→ Y
      g
```

be a commutative square of algebraic spaces over a scheme `S`.  The base change map of
**Stacks 0736** read as a map of higher direct images,
`AlgebraicGeometry.Space.higherDirectImageBaseChangeMap`, is a morphism

`g^*R^if_*𝓕 ⟶ R^if'_*((g')^*𝓕)`

of `𝒪_{Y'}`-modules, and its source and target are the two functors

`(AlgebraicGeometry.Space.modulePushforward B S hS f).rightDerived i ⋙
  AlgebraicGeometry.Space.modulePullback B S hS g`

and

`AlgebraicGeometry.Space.modulePullback B S hS g' ⋙
  (AlgebraicGeometry.Space.modulePushforward B S hS f').rightDerived i`

evaluated at `𝓕`.  This file records that **both of those modules are quasi-coherent** whenever
`𝓕` is, with no hypothesis on the square beyond quasi-compactness and quasi-separatedness of the
direct image being taken.

Nothing here asserts that the comparison map is invertible.

## Main results

* `isQuasicoherentOnSite_modulePullback_obj_rightDerived_modulePushforward_obj` and
  `isQuasicoherentOnSite_higherDirectImageBaseChangeSource_obj`:
  **the source `g^*R^if_*𝓕` is quasi-coherent**, the second at the composed spelling the
  comparison map's own type is written with.
* `isQuasicoherentOnSite_rightDerived_modulePushforward_obj_modulePullback_obj` and
  `isQuasicoherentOnSite_higherDirectImageBaseChangeTarget_obj`:
  **the target `R^if'_*((g')^*𝓕)` is quasi-coherent**, likewise.
* `isQuasicoherentOnSite_higherDirectImageBaseChangeTarget_obj_of_isPullback`:
  the target again, for a *cartesian* square, with quasi-compactness and quasi-separatedness
  assumed of `f` rather than of `f'` — so that the hypotheses are exactly part (1)'s.

## Implementation notes

*The seating.*  The direct image appearing in the source and target of
`AlgebraicGeometry.Space.higherDirectImageBaseChangeMap` is
`AlgebraicGeometry.Space.modulePushforward`, not
`AlgebraicGeometry.Space.toposModulePushforward`;  the base change map of `D⁺` is seated at the
latter, but the map of higher direct images is stated at the former, having crossed the two
seatings by `AlgebraicGeometry.Space.higherDirectImageIso`.  Everything below is therefore stated
at `modulePushforward`, which is also the seating of **Stacks 0720**,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_rightDerived_modulePushforward'`:  no crossing of
the direct image is needed for quasi-coherence of the two sides, and none is performed.

*Two spellings of each side, deliberately.*  `CategoryTheory.Functor.comp_obj` holds by
definition, so `(G ⋙ H).obj 𝓕` and `H.obj (G.obj 𝓕)` are the same module;  but instance search does
not cross a definitional unfolding, and `SheafOfModules.IsQuasicoherentOnSite` is a class.  Each
side is therefore stated twice, once unfolded and once at the composed spelling that
`higherDirectImageBaseChangeMap`'s type literally uses, so that either can be supplied as an
instance without the consumer rewriting its goal.

*Why `HasInjectiveResolutions` is a binder.*
`CategoryTheory.Functor.rightDerived` takes an instance of
`CategoryTheory.HasInjectiveResolutions`, and this development produces that instance in more than
one way — `AlgebraicGeometry.Space.hasInjectiveResolutions_modules` directly, and from
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives`.  The class is a `Prop`, so the witnesses
are all definitionally equal and the choice is immaterial;  taking it as a hypothesis rather than
pinning one witness means the statements below apply verbatim to a higher direct image elaborated
against whichever witness its own file installed.

*What is assumed, and what is not.*  Quasi-coherence of the source needs `f` quasi-compact and
quasi-separated (**Stacks 0720**) and nothing of `g`:  pullback preserves quasi-coherence along an
arbitrary morphism, which is **Stacks 03GA**,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`.
Quasi-coherence of the target needs `f'` quasi-compact and quasi-separated and nothing of `g'`.
Neither needs flatness of `g`, cartesianness of the square, affineness of `Y` or `Y'`, or that the
big fppf site contain a terminal scheme.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0720](https://stacks.math.columbia.edu/tag/0720)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X X' Y Y' : AlgebraicSpaces B S hS}

/-! ### The source `g^*R^if_*𝓕` -/

/-- **The source of the base change map of higher direct images is quasi-coherent.**  For
`f : X ⟶ Y` quasi-compact and quasi-separated, `g : Y' ⟶ Y` arbitrary and `𝓕` a quasi-coherent
`𝒪_X`-module, the `𝒪_{Y'}`-module `g^*R^if_*𝓕` is quasi-coherent. -/
theorem isQuasicoherentOnSite_modulePullback_obj_rightDerived_modulePushforward_obj
    [HasInjectiveResolutions (Modules.{u, u} B S hS X.1 X.2)]
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (i : ℕ)
    (𝓕 : Modules.{u, u} B S hS X.1 X.2) (h𝓕 : 𝓕.IsQuasicoherentOnSite) :
    ((modulePullback B S hS g).obj
      (((modulePushforward B S hS f).rightDerived i).obj 𝓕)).IsQuasicoherentOnSite := by
  have := h𝓕
  exact isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g _
    (isQuasicoherentOnSite_rightDerived_modulePushforward' B S hS f hfqc hfqs 𝓕 i)

/-- **The source of the base change map of higher direct images is quasi-coherent**, at the
composed spelling `AlgebraicGeometry.Space.higherDirectImageBaseChangeMap`'s type is written with:
the source functor is
`(modulePushforward B S hS f).rightDerived i ⋙ modulePullback B S hS g`. -/
theorem isQuasicoherentOnSite_higherDirectImageBaseChangeSource_obj
    [HasInjectiveResolutions (Modules.{u, u} B S hS X.1 X.2)]
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (i : ℕ)
    (𝓕 : Modules.{u, u} B S hS X.1 X.2) (h𝓕 : 𝓕.IsQuasicoherentOnSite) :
    (((modulePushforward B S hS f).rightDerived i ⋙ modulePullback B S hS g).obj
      𝓕).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_obj_rightDerived_modulePushforward_obj f g hfqc hfqs i 𝓕 h𝓕

/-! ### The target `R^if'_*((g')^*𝓕)` -/

/-- **The target of the base change map of higher direct images is quasi-coherent.**  For
`f' : X' ⟶ Y'` quasi-compact and quasi-separated, `g' : X' ⟶ X` arbitrary and `𝓕` a quasi-coherent
`𝒪_X`-module, the `𝒪_{Y'}`-module `R^if'_*((g')^*𝓕)` is quasi-coherent. -/
theorem isQuasicoherentOnSite_rightDerived_modulePushforward_obj_modulePullback_obj
    [HasInjectiveResolutions (Modules.{u, u} B S hS X'.1 X'.2)]
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (hf'qc : IsQuasiCompact B S hS f'.hom)
    (hf'qs : IsQuasiSeparated B S hS f'.hom) (i : ℕ)
    (𝓕 : Modules.{u, u} B S hS X.1 X.2) (h𝓕 : 𝓕.IsQuasicoherentOnSite) :
    (((modulePushforward B S hS f').rightDerived i).obj
      ((modulePullback B S hS g').obj 𝓕)).IsQuasicoherentOnSite := by
  have := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g' 𝓕 h𝓕
  exact isQuasicoherentOnSite_rightDerived_modulePushforward' B S hS f' hf'qc hf'qs _ i

/-- **The target of the base change map of higher direct images is quasi-coherent**, at the
composed spelling `AlgebraicGeometry.Space.higherDirectImageBaseChangeMap`'s type is written with:
the target functor is
`modulePullback B S hS g' ⋙ (modulePushforward B S hS f').rightDerived i`. -/
theorem isQuasicoherentOnSite_higherDirectImageBaseChangeTarget_obj
    [HasInjectiveResolutions (Modules.{u, u} B S hS X'.1 X'.2)]
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (hf'qc : IsQuasiCompact B S hS f'.hom)
    (hf'qs : IsQuasiSeparated B S hS f'.hom) (i : ℕ)
    (𝓕 : Modules.{u, u} B S hS X.1 X.2) (h𝓕 : 𝓕.IsQuasicoherentOnSite) :
    ((modulePullback B S hS g' ⋙ (modulePushforward B S hS f').rightDerived i).obj
      𝓕).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_rightDerived_modulePushforward_obj_modulePullback_obj f' g' hf'qc hf'qs i 𝓕
    h𝓕

/-! ### The target of a cartesian square, from the hypotheses on `f` -/

/-- **The target of the base change map of higher direct images is quasi-coherent, for a cartesian
square, under part (1)'s own hypotheses.**  Quasi-compactness and quasi-separatedness are assumed
of `f`, not of its base change `f'`. -/
theorem isQuasicoherentOnSite_higherDirectImageBaseChangeTarget_obj_of_isPullback
    [HasInjectiveResolutions (Modules.{u, u} B S hS X'.1 X'.2)]
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom) (i : ℕ)
    (𝓕 : Modules.{u, u} B S hS X.1 X.2) (h𝓕 : 𝓕.IsQuasicoherentOnSite) :
    ((modulePullback B S hS g' ⋙ (modulePushforward B S hS f').rightDerived i).obj
      𝓕).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_higherDirectImageBaseChangeTarget_obj f' g'
    (isQuasiCompact_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq) hfqc)
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) => IsQuasiSeparated B S hS k.hom)
      sq hfqs)
    i 𝓕 h𝓕

end AlgebraicGeometry.Space

end
