module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback

/-!
# Pullback of a module of finite presentation along a morphism of schemes

Specialisation of the ringed-space statement
`Stacks.SheafOfModules.modulePullback_isFinitePresentation` (Stacks 01BQ) to a morphism of
schemes, in the vocabulary of `AlgebraicGeometry.Scheme.Modules`, together with the fact that
pulling back along an *isomorphism* reflects finite presentation.

## Main results

* `Stacks.Modules.isFinitePresentation_pullback`, and its instance form
  `Stacks.Modules.instIsFinitePresentationPullbackObj`: the pullback of a module of finite
  presentation along an arbitrary morphism of schemes is of finite presentation.
* `Stacks.Modules.isFinitePresentation_of_pullback_isIso`: conversely, if the pullback along an
  isomorphism is of finite presentation then so is the module.
* `Stacks.Modules.isFinitePresentation_of_restrict_eq_top`: a module whose restriction to an
  open subscheme that happens to be the whole space is of finite presentation is of finite
  presentation.
* `Stacks.Modules.isQuasicoherent_of_isFinitePresentation`: a module of finite presentation is
  quasi-coherent, in the form instance search can actually use at
  `AlgebraicGeometry.Scheme.Modules`.

## Implementation notes

No mathematics happens in the first result: for a morphism of schemes `f : X ⟶ Y` the
comparison between the scheme-level and the ringed-space-level pullback is definitional, exactly
as recorded in `StacksFrontier/AlgebraicGeometry/Modules/QuasicoherentPullbackScheme.lean` for the
quasi-coherent analogue (Stacks 01BG), whose shape this file copies.

The reflection along an isomorphism is a two-step pullback: pulling back along `j` and then
along `CategoryTheory.inv j` is pulling back along the identity, by
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackId`. Phrasing it for a general isomorphism rather than
for `Scheme.topIso` keeps every instance argument behind a variable, which is why the proof needs
no transparency device.

`Stacks.Modules.isFinitePresentation_of_restrict_eq_top` takes the hypothesis `U = ⊤` rather
than `U` being literally `⊤`, so that it applies to an open such as `f ⁻¹ᵁ ⊤` which is only
*provably* the whole space; substituting the equation first is what makes
`AlgebraicGeometry.Scheme.Opens.ι` an isomorphism without a dependent rewrite under the
`IsOpenImmersion` instance argument of `AlgebraicGeometry.Scheme.Modules.restrict`.

## References

* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Stacks 01BQ for schemes.** The pullback of a module of finite presentation along an
arbitrary morphism of schemes is of finite presentation. This is the specialisation of
`Stacks.SheafOfModules.modulePullback_isFinitePresentation` along the definitional
identification of `AlgebraicGeometry.Scheme.Modules.pullback f` with pullback on the underlying
ringed spaces. -/
theorem isFinitePresentation_pullback (M : Y.Modules) (hM : M.IsFinitePresentation) :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation :=
  @Stacks.SheafOfModules.modulePullback_isFinitePresentation
    X.toLocallyRingedSpace.toRingedSpace Y.toLocallyRingedSpace.toRingedSpace
    f.toLRSHom.toShHom M hM

/-- **Stacks 01BQ for schemes**, in instance form, so that finite presentation of a pullback is
found by instance search. -/
instance instIsFinitePresentationPullbackObj (M : Y.Modules) [h : M.IsFinitePresentation] :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation :=
  isFinitePresentation_pullback f M h

variable {f}

/-- Pulling back along an isomorphism reflects finite presentation: pull back again along the
inverse. -/
theorem isFinitePresentation_of_pullback_isIso (j : Y ⟶ X) [IsIso j] (ℱ : X.Modules)
    (h : ((Scheme.Modules.pullback j).obj ℱ).IsFinitePresentation) : ℱ.IsFinitePresentation := by
  have h2 := isFinitePresentation_pullback (CategoryTheory.inv j) _ h
  have e : (Scheme.Modules.pullback (CategoryTheory.inv j)).obj
      ((Scheme.Modules.pullback j).obj ℱ) ≅ ℱ :=
    (Scheme.Modules.pullbackComp (CategoryTheory.inv j) j).app ℱ ≪≫
      (Scheme.Modules.pullbackCongr (IsIso.inv_hom_id j)).app ℱ ≪≫
      (Scheme.Modules.pullbackId X).app ℱ
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e h2

/-- A module of finite presentation on a scheme is quasi-coherent.

Mathlib records this as an instance
(`Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`), but instance search does **not**
find it at `AlgebraicGeometry.Scheme.Modules` on this pin: the universe of the quasi-coherent
data is a parameter of both classes and is left undetermined by the goal. Going through
`SheafOfModules.IsFinitePresentation.exists_quasicoherentData` pins it, because the `shrink`
inside `SheafOfModules.QuasicoherentData.isQuasicoherent` fixes the universe.

The same statement is proved at a *variable* sheaf of rings as the root-level
`isQuasicoherent_of_isFinitePresentation`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`, tag 01BW (2));
that file is a 2700-line chapter file, so importing it into a foundation module under
`AlgebraicGeometry/Modules/` would be an import inversion. The two statements are
duplicates. -/
theorem isQuasicoherent_of_isFinitePresentation (ℱ : X.Modules) [h : ℱ.IsFinitePresentation] :
    ℱ.IsQuasicoherent := by
  obtain ⟨σ, -⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData ℱ (self := h)
  exact σ.isQuasicoherent

/-- The inclusion of an open subscheme that is the whole space is an isomorphism. -/
theorem isIso_ι_of_eq_top {U : X.Opens} (hU : U = ⊤) : IsIso U.ι := by
  subst hU
  exact inferInstanceAs (IsIso X.topIso.hom)

/-- A module whose restriction to an open subscheme that is the whole space is of finite
presentation is itself of finite presentation. -/
theorem isFinitePresentation_of_restrict_eq_top {U : X.Opens} (hU : U = ⊤) (ℱ : X.Modules)
    (h : (ℱ.restrict U.ι).IsFinitePresentation) : ℱ.IsFinitePresentation := by
  have _ : IsIso U.ι := isIso_ι_of_eq_top hU
  have h' : ((Scheme.Modules.pullback U.ι).obj ℱ).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation U.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app ℱ) h
  exact isFinitePresentation_of_pullback_isIso U.ι ℱ h'

end Stacks.Modules

end
