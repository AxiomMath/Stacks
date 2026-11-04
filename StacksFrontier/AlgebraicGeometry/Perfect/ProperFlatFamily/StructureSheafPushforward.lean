module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected

/-!
# Global sections of the fibres of a proper map with reduced connected geometric fibres

For a proper morphism of schemes whose geometric fibres are reduced and connected, the canonical
ring homomorphism `κ(s) ⟶ H⁰(X_s, 𝒪_{X_s})` is bijective at every point `s` of the base: each
fibre is proper, geometrically reduced and geometrically connected over its residue field, so its
ring of global sections is that residue field.

This is the fibrewise statement. It is the input that part (a) of [Stacks, Tag 0E62] turns into
`f_*𝒪_X = 𝒪_S` for a proper, flat, finitely presented `f`, which is [Stacks, Tag 0E0L]; part (a)
of Tag 0E62 is not available in this library, so neither tag is carried here. Tag 0E62 is carried
in `StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatFamily/AffineLocalSplitting.lean`, whose
clause string records that it covers part (b) only, in an affine-local algebraic form about an
abstract object of `D(R)`.

## Main results

In the namespace `Stacks.AlgebraicGeometry.ProperFlatStructureSheaf`:

* `bijective_fiber_appTop_of_geomReducedConnected`: the ring map `κ(s) ⟶ H⁰(X_s, 𝒪_{X_s})` is
  bijective.
* `isIso_fiber_unit_of_geomReducedConnected`: the same statement, as invertibility of the
  comparison of sheaves of modules.

## Implementation notes

Neither flatness nor finite presentation of `f` is used; properness together with geometric
reducedness and geometric connectedness suffices, these being the hypotheses the fibre inherits.

`GeometricallyReduced f` and `GeometricallyConnected f` say that `X ×_S Spec K` has the property
for every field `K` and every `Spec K ⟶ S`, which is how the source reads "the geometric fibres
of `f` are reduced and connected".

The second result is stated in the spelling that
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatFamily/UniversalDirectImage.lean` uses for a
comparison of sheaves of modules, so that it composes with the transfer lemmas of that file.

## References

* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
* [Stacks Project, Tag 0E62](https://stacks.math.columbia.edu/tag/0E62)
* [Stacks Project, Tag 0E0L](https://stacks.math.columbia.edu/tag/0E0L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProperFlatFamilyUnit
open Stacks.AlgebraicGeometry.ProperSectionsGeom

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatStructureSheaf

variable {X S : Scheme.{u}}

/-- For a proper morphism whose geometric fibres are reduced and connected, the canonical ring
homomorphism `κ(s) ⟶ H⁰(X_s, 𝒪_{X_s})` is bijective at every point `s` of the base.

The fibre `X_s` is proper over `Spec κ(s)` because properness is stable under base change, and it
is geometrically reduced and geometrically connected over `κ(s)` because those properties are
inherited by the fibre morphism; the conclusion is then the reduced-and-connected part of
[Stacks, Tag 0BUG]. Flatness and finite presentation of `f` are not used. -/
theorem bijective_fiber_appTop_of_geomReducedConnected (f : X ⟶ S) [IsProper f]
    [GeometricallyReduced f] [GeometricallyConnected f] (s : S) :
    Function.Bijective ((Scheme.ΓSpecIso (S.residueField s)).inv ≫
      (f.fiberToSpecResidueField s).appTop) := by
  have : IsProper (f.fiberToSpecResidueField s) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) ‹_›
  exact (ConcreteCategory.isIso_iff_bijective _).mp
    (isIso_globalSections_of_isProper (S.residueField s : Type u) (f.fiberToSpecResidueField s))

/-- The bijectivity of `κ(s) ⟶ H⁰(X_s, 𝒪_{X_s})`, restated as invertibility of the comparison
`𝒪 ⟶ (X_s ⟶ Spec κ(s))_* 𝒪` of sheaves of modules over the residue field at `s`. -/
theorem isIso_fiber_unit_of_geomReducedConnected (f : X ⟶ S) [IsProper f]
    [GeometricallyReduced f] [GeometricallyConnected f] (s : S) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit
      (f.fiberToSpecResidueField s).toRingCatSheafHom) :=
  (isIso_fiberToSpecResidueField_unit_iff f s).mpr
    (bijective_fiber_appTop_of_geomReducedConnected f s)

end Stacks.AlgebraicGeometry.ProperFlatStructureSheaf

end
