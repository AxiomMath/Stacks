module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The non-smooth locus of a morphism as a reduced closed subscheme

Let `f : X ⟶ Y` be a morphism of schemes which is locally of finite presentation. Mathlib
provides the *open* subset `AlgebraicGeometry.Scheme.Hom.smoothLocus` of points of `X` at which
`f` is smooth. Its complement, the locus where `f` fails to be smooth, is therefore closed, and
this file equips it with its reduced induced closed subscheme structure together with the two
structural morphisms (the closed immersion into `X` and the composite to `Y`).

This is what lets results stated for *morphisms of schemes* — fibre dimension bounds, for
instance — be applied to the non-smooth locus of a family.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.nonSmoothLocus`: the complement of the smooth locus, as a closed
  subset of `X`.
* `AlgebraicGeometry.Scheme.Hom.nonSmoothSubscheme`: that closed subset with its reduced induced
  closed subscheme structure.
* `AlgebraicGeometry.Scheme.Hom.nonSmoothSubschemeι`: the closed immersion into `X`.
* `AlgebraicGeometry.Scheme.Hom.nonSmoothSubschemeToBase`: the composite morphism to `Y`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.mem_nonSmoothLocus`: a point lies in the non-smooth locus exactly
  when the stalk map there is not formally smooth.
* `AlgebraicGeometry.Scheme.Hom.range_nonSmoothSubschemeι` and
  `AlgebraicGeometry.Scheme.Hom.mem_range_nonSmoothSubschemeι`: the subscheme is supported
  exactly on the non-smooth points.
* `AlgebraicGeometry.Scheme.Hom.isEmpty_nonSmoothSubscheme_iff`: the subscheme is empty precisely
  when `f` is smooth.
* instances recording that `nonSmoothSubschemeι` is a closed immersion and that
  `nonSmoothSubscheme` is reduced.

## Implementation notes

The reduced induced structure is `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`
followed by `AlgebraicGeometry.Scheme.IdealSheafData.subscheme`; reducedness of the result is
`AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal` and its support is
`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι_vanishingIdeal`. Since
`nonSmoothSubscheme` and `nonSmoothSubschemeι` are definitions rather than abbreviations, the
instances that typeclass search would otherwise find through them are restated here.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]

/-- The non-smooth locus of a morphism locally of finite presentation: the complement of
`AlgebraicGeometry.Scheme.Hom.smoothLocus`, as a closed subset of the source. -/
@[sga "7 VI 4.5"]
def nonSmoothLocus : Closeds X := f.smoothLocus.compl

/-- The underlying set of the non-smooth locus is the complement of the smooth locus. -/
@[simp]
theorem coe_nonSmoothLocus : (f.nonSmoothLocus : Set X) = (f.smoothLocus : Set X)ᶜ := rfl

/-- The set of points at which a morphism locally of finite presentation fails to be smooth is
closed, being the complement of the open set `AlgebraicGeometry.Scheme.Hom.smoothLocus`. -/
@[ega "IV 12.1.7", ega "IV 6.8.7" "more general", sga "4 XI 2.1" "partial"]
theorem isClosed_compl_smoothLocus : IsClosed ((f.smoothLocus : Set X)ᶜ) :=
  f.smoothLocus.isOpen.isClosed_compl

/-- A point lies in the non-smooth locus exactly when the stalk map of `f` there fails to be
formally smooth. -/
@[simp]
theorem mem_nonSmoothLocus {x : X} :
    x ∈ f.nonSmoothLocus ↔ ¬ (f.stalkMap x).hom.FormallySmooth := Iff.rfl

/-- The non-smooth locus is empty exactly when the morphism is smooth. -/
theorem coe_nonSmoothLocus_eq_empty_iff : (f.nonSmoothLocus : Set X) = ∅ ↔ Smooth f := by
  rw [coe_nonSmoothLocus, Set.compl_empty_iff, ← smoothLocus_eq_top_iff]
  exact ⟨fun h ↦ Opens.ext (by simp [h]), fun h ↦ by rw [h]; simp⟩

/-- The non-smooth locus of a morphism locally of finite presentation, carrying its reduced
induced closed subscheme structure: the closed subscheme of the source cut out by the vanishing
ideal sheaf of `AlgebraicGeometry.Scheme.Hom.nonSmoothLocus`. -/
noncomputable def nonSmoothSubscheme : Scheme.{u} :=
  (IdealSheafData.vanishingIdeal f.nonSmoothLocus).subscheme

/-- The closed immersion of the non-smooth locus of `f` into the source of `f`. -/
noncomputable def nonSmoothSubschemeι : f.nonSmoothSubscheme ⟶ X :=
  (IdealSheafData.vanishingIdeal f.nonSmoothLocus).subschemeι

/-- The non-smooth locus subscheme is a closed subscheme of the source, being cut out by an
ideal sheaf. -/
instance isClosedImmersion_nonSmoothSubschemeι : IsClosedImmersion f.nonSmoothSubschemeι :=
  inferInstanceAs (IsClosedImmersion (IdealSheafData.vanishingIdeal f.nonSmoothLocus).subschemeι)

/-- The non-smooth locus subscheme is reduced, carrying the reduced induced structure of a
vanishing ideal sheaf. -/
instance isReduced_nonSmoothSubscheme : IsReduced f.nonSmoothSubscheme :=
  inferInstanceAs (IsReduced (IdealSheafData.vanishingIdeal f.nonSmoothLocus).subscheme)

/-- The non-smooth locus subscheme is supported exactly on the complement of the smooth locus. -/
@[simp]
theorem range_nonSmoothSubschemeι :
    Set.range f.nonSmoothSubschemeι = (f.smoothLocus : Set X)ᶜ :=
  IdealSheafData.range_subschemeι_vanishingIdeal f.nonSmoothLocus

/-- A point of the source comes from the non-smooth locus subscheme exactly when the stalk map of
`f` there fails to be formally smooth. -/
@[simp]
theorem mem_range_nonSmoothSubschemeι {x : X} :
    x ∈ Set.range f.nonSmoothSubschemeι ↔ ¬ (f.stalkMap x).hom.FormallySmooth := by
  rw [range_nonSmoothSubschemeι]
  exact Iff.rfl

/-- Every point of the non-smooth locus subscheme maps to a point of the source outside the
smooth locus. -/
theorem notMem_smoothLocus_nonSmoothSubschemeι (z : f.nonSmoothSubscheme) :
    f.nonSmoothSubschemeι z ∉ f.smoothLocus :=
  (mem_range_nonSmoothSubschemeι f).mp ⟨z, rfl⟩

/-- The non-smooth locus subscheme is empty exactly when the morphism is smooth. -/
theorem isEmpty_nonSmoothSubscheme_iff : IsEmpty f.nonSmoothSubscheme ↔ Smooth f := by
  rw [← Set.range_eq_empty_iff (f := ⇑f.nonSmoothSubschemeι), range_nonSmoothSubschemeι,
    ← coe_nonSmoothLocus, coe_nonSmoothLocus_eq_empty_iff]

/-- The structural morphism from the non-smooth locus of `f` to the target of `f`, namely the
closed immersion into the source followed by `f`. -/
noncomputable def nonSmoothSubschemeToBase : f.nonSmoothSubscheme ⟶ Y :=
  f.nonSmoothSubschemeι ≫ f

/-- The structural morphism to the target factors as the closed immersion into the source
followed by `f`, by definition. -/
theorem nonSmoothSubschemeToBase_eq :
    f.nonSmoothSubschemeToBase = f.nonSmoothSubschemeι ≫ f := rfl

/-- The structural morphism from the non-smooth locus subscheme to the target is locally of
finite type, being a closed immersion followed by a morphism locally of finite presentation. -/
instance locallyOfFiniteType_nonSmoothSubschemeToBase :
    LocallyOfFiniteType f.nonSmoothSubschemeToBase :=
  inferInstanceAs (LocallyOfFiniteType (f.nonSmoothSubschemeι ≫ f))

end Scheme.Hom

end AlgebraicGeometry

end
