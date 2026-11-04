module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.SpecTarget
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Finite
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite flat morphisms

A morphism of schemes is finite locally free if and only if it is finite, flat and locally of
finite presentation. Over a locally Noetherian base the finite presentation condition is
automatic for a finite flat morphism, so there finite local freeness is finiteness together with
flatness.

## Main results

* `Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation`
  characterises finite locally free morphisms.
* `Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian` gives the
  simplified characterisation over a locally Noetherian base.

## Implementation notes

All four properties involved are Zariski local on the base, so the characterisation follows from
the case of a target which is the spectrum of a ring, applied to the members of the affine cover
of the base. The restated Zariski locality of finiteness, flatness and local finite presentation
is needed because instance synthesis cannot solve for the affine-target or ring-homomorphism
parameter of `AlgebraicGeometry.HasAffineProperty` and
`AlgebraicGeometry.HasRingHomProperty` without reducibility settings this development does not
use.

## References

* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Morphisms

/-- Finiteness of a morphism is Zariski local on the base. -/
public alias isFinite_isZariskiLocalAtTarget := AlgebraicGeometry.isZariskiLocalAtTarget_isFinite

/-- Flatness of a morphism is Zariski local on the base. -/
alias flat_isZariskiLocalAtTarget := Stacks.Descent.flat_isZariskiLocalAtTarget

/-- Being locally of finite presentation is Zariski local on the base. -/
alias locallyOfFinitePresentation_isZariskiLocalAtTarget :=
  Stacks.Descent.locallyOfFinitePresentation_isZariskiLocalAtTarget

/-- Finiteness of a morphism is invariant under precomposition and postcomposition with
isomorphisms, being a consequence of its stability under base change. -/
theorem isFinite_respectsIso :
    MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- **Stacks Project, Tag 02KB.** A morphism of schemes is finite locally free if and only if it
is finite, flat, and locally of finite presentation. -/
@[stacks 02KB "conditions (1) and (2)"]
theorem isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) :
    IsFiniteLocallyFree f ↔
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f := by
  have hfinloc := isFinite_isZariskiLocalAtTarget.{u}
  have hflatloc := flat_isZariskiLocalAtTarget.{u}
  have hlfploc := locallyOfFinitePresentation_isZariskiLocalAtTarget.{u}
  have hcard := IsZariskiLocalAtTarget.iff_of_openCover
    (P := @IsFiniteLocallyFree) (f := f) S.affineCover
  have hfincov := IsZariskiLocalAtTarget.iff_of_openCover
    (P := @IsFinite) (f := f) S.affineCover
  have hflatcov := IsZariskiLocalAtTarget.iff_of_openCover
    (P := @Flat) (f := f) S.affineCover
  have hlfpcov := IsZariskiLocalAtTarget.iff_of_openCover
    (P := @LocallyOfFinitePresentation) (f := f) S.affineCover
  constructor
  · intro h
    have h' (i) := (isFiniteLocallyFree_iff_of_specTarget
      (S.affineCover.pullbackHom f i)).mp (hcard.mp h i)
    exact ⟨hfincov.mpr fun i ↦ (h' i).1, hflatcov.mpr fun i ↦ (h' i).2.1,
      hlfpcov.mpr fun i ↦ (h' i).2.2⟩
  · rintro ⟨hfin, hflat, hlfp⟩
    exact hcard.mpr fun i ↦ (isFiniteLocallyFree_iff_of_specTarget _).mpr
      ⟨hfincov.mp hfin i, hflatcov.mp hflat i, hlfpcov.mp hlfp i⟩

/-- **Stacks Project, Tag 02KB.** Over a locally Noetherian base, a morphism of schemes is finite
locally free if and only if it is finite and flat. -/
@[stacks 02KB "condition (3) over a locally Noetherian base"]
theorem isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian
    {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] :
    IsFiniteLocallyFree f ↔ IsFinite f ∧ Flat f := by
  rw [isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation]
  refine ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, ?_⟩⟩
  have hfin : IsFinite f := h.1
  infer_instance

end Stacks.Morphisms

end
