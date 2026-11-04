module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ProperOverBase.CoherentSerreClass
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.NonvanishingInDegreeZero
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GrothendieckExistence

/-!
# A nonzero coherent module with support proper over the base

`AlgebraicGeometry.isSerreClass_hasProperSupport_coherentModules` says that the coherent
`𝒪_X`-modules with support proper over `S` form a Serre subcategory of `Coh(𝒪_X)`. That
statement is also true for reasons that would make it empty of content: the zero module has
empty support, and the empty subset of `X` is proper over `S`, so the property defining the
subcategory is satisfied by the zero object alone. This file rules that reading out by naming an
object of `Coh(𝒪_X)` which is **not** zero and whose support is proper over `S`.

The witness is `𝒪_X/𝔪_x^t` at a closed point `x` and `t ≥ 1`, which is
`AlgebraicGeometry.pointTestModule`: coherent on a locally Noetherian scheme, nonzero because its
support is the nonempty set `{x}`, and of proper support whenever `f` is proper, since a closed
immersion followed by a proper morphism is proper.

## Main definitions

* `AlgebraicGeometry.properSupportTestObject`: `𝒪_X/𝔪_x^t` as an object of `Coh(𝒪_X)`.

## Main results

* `AlgebraicGeometry.not_isZero_properSupportTestObject`: it is not a zero object.
* `AlgebraicGeometry.hasProperSupport_properSupportTestObject`: its support is proper over `S`.
* `AlgebraicGeometry.exists_not_isZero_hasProperSupport_coherentModules`: the three facts
  together, as the statement that the Serre subcategory of
  `isSerreClass_hasProperSupport_coherentModules` contains a nonzero object.

These carry no `@[stacks 0CYU]` attribute. Tag 0CYU asserts that the subcategory is a Serre
subcategory and says nothing about its being nonzero, so a non-degeneracy certificate is not one
of its clauses.

## References

* [Stacks Project, Tag 0CYU](https://stacks.math.columbia.edu/tag/0CYU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- `𝒪_X/𝔪_x^t`, regarded as an object of the abelian category `Coh(𝒪_X)` of coherent
`𝒪_X`-modules on a locally Noetherian scheme. -/
noncomputable def properSupportTestObject [IsLocallyNoetherian X] (x : X) (t : ℕ) :
    SheafOfModules.CoherentModules X.ringCatSheaf :=
  ⟨pointTestModule x t, isCoherent_pointTestModule x t⟩

/-- The underlying sheaf of modules of `properSupportTestObject x t` is `pointTestModule x t`. -/
@[simp]
theorem properSupportTestObject_obj [IsLocallyNoetherian X] (x : X) (t : ℕ) :
    (properSupportTestObject x t).obj = pointTestModule x t :=
  rfl

/-- **The witness is not a zero object.** Its support is `{x}`, and a zero module has empty
support. -/
theorem not_isZero_properSupportTestObject [IsLocallyNoetherian X] (x : X)
    (hx : IsClosed ({x} : Set X)) {t : ℕ} (ht : t ≠ 0) :
    ¬ IsZero (properSupportTestObject x t).obj :=
  not_isZero_pointTestModule x hx ht

/-- **The witness has support proper over the base**, for `f` proper: a coherent module is of
finite type, and over a proper base every finite type module has proper support. -/
theorem hasProperSupport_properSupportTestObject [IsProper f] [IsLocallyNoetherian X] (x : X)
    (t : ℕ) :
    Stacks.Algebraization.HasProperSupport f (properSupportTestObject x t).obj :=
  have : (pointTestModule x t).IsCoherent := isCoherent_pointTestModule x t
  have : (pointTestModule x t).IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType (M := pointTestModule x t)
  Stacks.Algebraization.hasProperSupport_of_isProper f (pointTestModule x t)

/-- **The Serre subcategory of Tag 0CYU contains a nonzero object.** For `f : X ⟶ S` proper with
`X` locally Noetherian and `x` a closed point of `X`, the coherent module `𝒪_X/𝔪_x^t` with
`t ≥ 1` is not zero and has support proper over `S`.

This is the non-degeneracy certificate for
`AlgebraicGeometry.isSerreClass_hasProperSupport_coherentModules`: without it that theorem would
be compatible with the property defining the subcategory holding only for zero objects. -/
theorem exists_not_isZero_hasProperSupport_coherentModules [IsProper f] [IsLocallyNoetherian X]
    (x : X) (hx : IsClosed ({x} : Set X)) {t : ℕ} (ht : t ≠ 0) :
    ∃ F : SheafOfModules.CoherentModules X.ringCatSheaf,
      ¬ IsZero F.obj ∧ Stacks.Algebraization.HasProperSupport f F.obj :=
  ⟨properSupportTestObject x t, not_isZero_properSupportTestObject x hx ht,
    hasProperSupport_properSupportTestObject f x t⟩

end AlgebraicGeometry

end
