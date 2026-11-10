module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBounded

/-!
# An immersion has universally bounded fibres

Every fibre of an immersion of schemes is empty or a single reduced point, so the integer one
bounds the degrees of all of them.

## Main results

* `AlgebraicGeometry.isIso_appTop`: an isomorphism of schemes induces an isomorphism on global
  sections.
* `AlgebraicGeometry.hasUniversallyBoundedFibers_of_isImmersion`: an immersion has universally
  bounded fibres.

## References

* [Stacks Project, Tag 03J9](https://stacks.math.columbia.edu/tag/03J9)
* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An isomorphism of schemes induces an isomorphism on rings of global sections. -/
theorem isIso_appTop {Z W : Scheme.{u}} (g : Z ⟶ W) [IsIso g] :
    IsIso (Scheme.Hom.appTop g) :=
  have h : Scheme.Γ.map g.op = Scheme.Hom.appTop g := rfl
  have : IsIso g.op := inferInstance
  h ▸ Functor.map_isIso Scheme.Γ g.op

/-- An immersion of schemes has universally bounded fibres; the integer one bounds the degrees of
its fibres. -/
@[stacks 03J9]
theorem hasUniversallyBoundedFibers_of_isImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] : HasUniversallyBoundedFibers f := by
  refine ⟨1, fun y ↦ ?_⟩
  have hgi : IsImmersion (f.fiberToSpecResidueField y) := by
    change IsImmersion (pullback.snd f (Y.fromSpecResidueField y))
    infer_instance
  let : Algebra ↑(Y.residueField y) ↑Γ(f.fiber y, ⊤) :=
    ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
      Scheme.Hom.appTop (f.fiberToSpecResidueField y)).hom.toAlgebra
  by_cases hempty : IsEmpty (f.fiber y)
  · have hci : IsClosedImmersion (f.fiberToSpecResidueField y) := inferInstance
    have haff : IsAffineHom (f.fiberToSpecResidueField y) :=
      (isClosedImmersion_iff_isAffineHom.mp hci).1
    have hsub : Subsingleton ↑Γ(f.fiber y, ⊤) := by
      have : IsAffine (f.fiber y) := isAffine_of_isAffineHom (f.fiberToSpecResidueField y)
      exact PrimeSpectrum.isEmpty_iff_subsingleton.mp
        ⟨fun p ↦ hempty.elim ((f.fiber y).isoSpec.inv p)⟩
    exact ⟨0, by norm_num, Stacks.Morphisms.isFiniteLocallyFreeOfRank_of_basis _ 0
      ⟨Module.Basis.empty _⟩⟩
  · have hsurj : Function.Surjective (f.fiberToSpecResidueField y) := by
      obtain ⟨x⟩ := not_isEmpty_iff.mp hempty
      exact fun z ↦ ⟨x, Subsingleton.elim _ _⟩
    have hci : IsClosedImmersion (f.fiberToSpecResidueField y) :=
      IsClosedImmersion.of_isPreimmersion _ (Set.range_eq_univ.mpr hsurj ▸ isClosed_univ)
    have hsur : Surjective (f.fiberToSpecResidueField y) := ⟨hsurj⟩
    have hiso : IsIso (f.fiberToSpecResidueField y) :=
      isIso_of_isClosedImmersion_of_surjective _
    have happ : IsIso (Scheme.Hom.appTop (f.fiberToSpecResidueField y)) := isIso_appTop _
    have hbij : Function.Bijective ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
        Scheme.Hom.appTop (f.fiberToSpecResidueField y)).hom :=
      (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
    exact ⟨1, le_rfl, Stacks.Morphisms.isFiniteLocallyFreeOfRank_of_basis _ 1
      ⟨(Module.Basis.singleton (Fin 1) ↑(Y.residueField y)).map
        (LinearEquiv.ofBijective (Algebra.linearMap ↑(Y.residueField y) ↑Γ(f.fiber y, ⊤)) hbij)⟩⟩

end AlgebraicGeometry

end
