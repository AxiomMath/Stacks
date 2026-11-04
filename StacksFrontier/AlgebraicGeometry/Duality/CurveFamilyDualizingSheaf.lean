module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexTensorDescription
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekChartConsequences
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekCohenMacaulayTwist
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexOfCharts
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackSingleAnyModel

/-!
# The relative dualizing sheaf of a proper flat Cohen–Macaulay family of curves

Let `S` be a Noetherian scheme and `f : X ⟶ S` a proper, flat, Cohen–Macaulay morphism all of
whose fibres have dimension one at every point. The relative dualizing complex
`ω^•_{X/S} = a(𝒪_S)` of [Stacks, Tag 0B6S] is then a single sheaf placed in degree `-1`
([Stacks, Tag 0BV8]), the *relative dualizing sheaf* `ω_{X/S} = H^{-1}(ω^•_{X/S})`
(`Stacks.Duality.relativeDualizingSheaf` at the compactification `X` of itself). Its pullback to
the fibre `X_K = X ×_S Spec K` over any field-valued point `Spec K ⟶ S` is the dualizing sheaf
`ω_{X_K} = H^{-1}(a_K(𝒪_{Spec K}))` of [Stacks, Tag 0BS2]: the relative dualizing complex commutes
with base change ([Stacks, Tag 0B6S], last sentence), and the top cohomology of a derived pullback
is the pullback of the top cohomology. This is the scheme case of the relative dualizing sheaf of
a family of curves of [Stacks, Tag 0E6Q] and of its base change property.

## Main results

* `Stacks.Duality.nonempty_relativeDualizingComplexStructureSheaf_iso_shift`:
  `a(𝒪_S) ≅ ω_{X/S}[1]`.
* `Stacks.Duality.nonempty_pullback_relativeDualizingSheaf_iso`: `g'^*ω_{X/S} ≅ ω_{X_K}` for
  every cartesian square over a field-valued point of `S`.

## References

* [Stacks Project, Tag 0B6S](https://stacks.math.columbia.edu/tag/0B6S)
* [Stacks Project, Tag 0BV8](https://stacks.math.columbia.edu/tag/0BV8)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

open DerivedPushforward

variable {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]

/-- The underlying morphism `X ⟶ S` of `ftsHomToBase f` is proper, since it is `f`. -/
instance isProper_ftsHomToBase_left : IsProper (ftsHomToBase f).left :=
  inferInstanceAs (IsProper f)

/-- **`a(𝒪_S) ≅ ω_{X/S}[1]`** for a proper Cohen–Macaulay morphism `f : X ⟶ S` all of whose fibres
have local dimension one ([Stacks, Tag 0BV8] at the compactification `X` of itself). -/
theorem nonempty_relativeDualizingComplexStructureSheaf_iso_shift
    (hCM : f.IsCohenMacaulay (isLocallyNoetherian_fiber_left (ftsHomToBase f)))
    (hd : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = ((1 : ℕ) : WithBot ℕ∞)) :
    Nonempty ((relativeDualizingComplexStructureSheaf f).obj ≅
      ((DerivedCategory.singleFunctor X.Modules 0).obj (relativeDualizingSheaf (ftsHomToBase f)
        (properCompactification (ftsHomToBase f)) 1))⟦(1 : ℤ)⟧) := by
  obtain ⟨e⟩ := nonempty_relativeDualizingComplexObj_iso_shift (ftsHomToBase f)
    (properCompactification (ftsHomToBase f)) hCM 1 hd
  let φ : relativeDualizingComplexObj (ftsHomToBase f) (properCompactification (ftsHomToBase f)) ≅
      (relativeDualizingComplexStructureSheaf f).obj :=
    (ObjectProperty.ι _).mapIso ((upperShriekProperIso (ftsHomToBase f)).app
      (derivedStructureSheaf S))
  exact ⟨φ.symm ≪≫ e⟩

/-- **The relative dualizing sheaf restricts to the dualizing sheaf of each fibre.** Let
`f : X ⟶ S` be proper, flat and Cohen–Macaulay with one-dimensional fibres, and let
`X' = X ×_S Spec K` be its fibre over a field-valued point `y : Spec K ⟶ S`, with projections
`g' : X' ⟶ X` and `f' : X' ⟶ Spec K`. Then `g'^*ω_{X/S} ≅ ω_{X'}`, the dualizing sheaf
`H^{-1}(a_{f'}(𝒪_{Spec K}))` of [Stacks, Tag 0BS2]. -/
theorem nonempty_pullback_relativeDualizingSheaf_iso [Flat f]
    (hCM : f.IsCohenMacaulay (isLocallyNoetherian_fiber_left (ftsHomToBase f)))
    (hd : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = ((1 : ℕ) : WithBot ℕ∞))
    {K : Type u} [Field K] {X' : Scheme.{u}} {y : Spec (CommRingCat.of K) ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of K)} (sq : IsPullback g' f' f y)
    [hf' : IsProper f'] :
    Nonempty ((Scheme.Modules.pullback g').obj (relativeDualizingSheaf (ftsHomToBase f)
        (properCompactification (ftsHomToBase f)) 1) ≅
      dualizingSheafOverField f') := by
  obtain ⟨e₁⟩ := nonempty_relativeDualizingComplexStructureSheaf_iso_shift f hCM hd
  let eBC := relativeDualizingBaseChangeIso f sq
  let L := derivedPullback g'
  let e₂ : (DerivedCategory.homologyFunctor X'.Modules (-1)).obj
      (L.obj (relativeDualizingComplexStructureSheaf f).obj) ≅ dualizingSheafOverField f' :=
    (DerivedCategory.homologyFunctor X'.Modules (-1)).mapIso ((ObjectProperty.ι _).mapIso eBC)
  let e₃ : (DerivedCategory.homologyFunctor X'.Modules (-1)).obj
      (L.obj (relativeDualizingComplexStructureSheaf f).obj) ≅
      (DerivedCategory.homologyFunctor X'.Modules (-1)).obj
        (L.obj ((DerivedCategory.singleFunctor X.Modules (-1)).obj
          (relativeDualizingSheaf (ftsHomToBase f) (properCompactification (ftsHomToBase f)) 1))) :=
    (DerivedCategory.homologyFunctor X'.Modules (-1)).mapIso
        (L.mapIso (e₁ ≪≫ ((DerivedCategory.singleFunctors X.Modules).shiftIso 1 (-1) 0
          (by norm_num)).app _))
  exact ⟨(Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleIsoAnyModel
    g'.toLRSHom.toShHom (relativeDualizingSheaf (ftsHomToBase f)
      (properCompactification (ftsHomToBase f)) 1) (-1)).symm ≪≫ e₃.symm ≪≫ e₂⟩

end Stacks.Duality

end
