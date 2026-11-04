module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.SchemeTheoreticallyDense
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.FibrewiseContainment
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPoints05KR
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic

/-!
# An open scheme-theoretically dense in the generic fibre is so in all nearby fibres

Let `f : X ⟶ Y` be a finite type morphism onto an irreducible base with generic point `η`, and
let `U ⊆ X` be an open subscheme whose trace on the fibre `X_η` is scheme-theoretically dense
there. Then the trace of `U` on `X_y` is scheme-theoretically dense for every `y` in some
nonempty open subset of `Y`.

## Main results

* `AlgebraicGeometry.isSchemeTheoreticallyDense_fiber_iff_associatedPoints_subset`:
  scheme-theoretic density of the trace of an open on a fibre is containment in it of the
  associated points of the structure sheaf of that fibre.
* `AlgebraicGeometry.exists_open_isSchemeTheoreticallyDense_fiber`: the shrinking statement.

## Implementation notes

The fibre of `U` over `y` is its inverse image along `f.fiberι y`. A fibre of a morphism locally
of finite type is locally Noetherian, so scheme-theoretic density of an open in it is containment
of the associated points of its structure sheaf; the structure sheaf of the fibre is the pullback
of the structure sheaf of `X`, which is quasi-coherent and of finite type, so the fibrewise
containment statement for a finite type quasi-coherent module applies to it.

## References

* [Stacks Project, Tag 0573](https://stacks.math.columbia.edu/tag/0573)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An open subscheme of a fibre of a morphism locally of finite type is scheme-theoretically
dense exactly when it contains every associated point of the pullback of the structure sheaf of
the source, that pullback being the structure sheaf of the fibre. -/
public theorem isSchemeTheoreticallyDense_fiber_iff_associatedPoints_subset
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (U : X.Opens) (y : Y) :
    Scheme.Opens.IsSchemeTheoreticallyDense (f.fiberι y ⁻¹ᵁ U) ↔
      Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback (f.fiberι y)).obj (SheafOfModules.unit X.ringCatSheaf)) ⊆
        f.fiberι y ⁻¹' (U : Set X) := by
  have hnoeth : IsLocallyNoetherian (f.fiber y) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f y
  have hiso : Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pullback (f.fiberι y)).obj (SheafOfModules.unit X.ringCatSheaf)) =
      Stacks.Divisors.schemeAssociatedPoints (f.fiber y) :=
    Stacks.Divisors.associatedPoints_congr (Scheme.Modules.pullbackUnitIso (f.fiberι y))
  have hcoe : ((f.fiberι y ⁻¹ᵁ U : (f.fiber y).Opens) : Set (f.fiber y)) =
      f.fiberι y ⁻¹' (U : Set X) := rfl
  rw [hiso, ← hcoe]
  exact (isSchemeTheoreticallyDense_tfae (f.fiber y) (f.fiberι y ⁻¹ᵁ U)).out 1 3

/-- **Stacks Project, Tag 0573.** Let `f : X ⟶ Y` be a finite type morphism of schemes with `Y`
irreducible with generic point `η`, and let `U ⊆ X` be an open subscheme whose trace on the fibre
over `η` is scheme-theoretically dense there. Then there is a nonempty open `V ⊆ Y` such that the
trace of `U` on the fibre over `y` is scheme-theoretically dense for every `y ∈ V`. -/
@[stacks 0573]
public theorem exists_open_isSchemeTheoreticallyDense_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace Y] [LocallyOfFiniteType f] [QuasiCompact f] (U : X.Opens) (η : Y)
    (hη : IsGenericPoint η Set.univ)
    (hηU : Scheme.Opens.IsSchemeTheoreticallyDense (f.fiberι η ⁻¹ᵁ U)) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ ∀ y ∈ V,
      Scheme.Opens.IsSchemeTheoreticallyDense (f.fiberι y ⁻¹ᵁ U) := by
  have : (SheafOfModules.unit.{u} X.ringCatSheaf).IsFiniteType := structureSheaf_isFiniteType X
  obtain ⟨V, hV, hVsub⟩ := Stacks.Divisors.exists_open_associatedPoints_fiber_subset f
    (SheafOfModules.unit X.ringCatSheaf) U η hη
    ((isSchemeTheoreticallyDense_fiber_iff_associatedPoints_subset f U η).mp hηU)
  exact ⟨V, hV, fun y hy =>
    (isSchemeTheoreticallyDense_fiber_iff_associatedPoints_subset f U y).mpr (hVsub y hy)⟩

end AlgebraicGeometry

end
