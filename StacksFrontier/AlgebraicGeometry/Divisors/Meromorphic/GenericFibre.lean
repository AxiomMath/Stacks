module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute

/-!
# Integrality from the generic fibre of a flat morphism

The source of a flat morphism to an integral scheme is integral as soon as its generic fibre
is integral.

## Main results

* `AlgebraicGeometry.isIntegral_of_flat_of_isIntegral_genericFiber`: integrality of the source
  follows from integrality of the target and of the generic fibre.

## Implementation notes

The generic fibre is Mathlib's scheme-theoretic fibre over the canonical `genericPoint` of the
integral target. Irreducibility of the source comes from the fact that a flat morphism is
generalizing, so every point of the source specializes from a point of the generic fibre;
reducedness comes from scheme-theoretic dominance of the base change of `f` along the inclusion
of the generic point.

## References

* [Stacks Project, Tag 0BCM](https://stacks.math.columbia.edu/tag/0BCM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

private theorem irreducibleSpace_of_integral_genericFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsIntegral Y]
    [IsIntegral (f.fiber (genericPoint Y))] : IrreducibleSpace X := by
  let η : Y := genericPoint Y
  let g : f.fiber η ⟶ X := f.fiberι η
  have hRange : IsIrreducible (Set.range g) := by
    simpa [g, Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (f.fiber η)).image g g.continuous.continuousOn
  have hdense : closure (Set.range g) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x _ htmem
    rcases htmem with ⟨ht, hsub⟩
    obtain ⟨z, hzx, hη⟩ := AlgebraicGeometry.Flat.generalizingMap f
      (genericPoint_specializes (f x))
    exact hzx.mem_closed ht (hsub ⟨(f.fiberHomeo η).symm ⟨z, hη⟩, by simp [g]⟩)
  have hX : IsIrreducible (Set.univ : Set X) := by
    rw [← hdense]
    exact hRange.closure
  exact { toPreirreducibleSpace := ⟨hX.2⟩, toNonempty := ⟨hX.1.some⟩ }

private theorem isReduced_of_flat_of_isIntegral_genericFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsIntegral Y]
    [IsIntegral (f.fiber (genericPoint Y))] : IsReduced X := by
  let η := genericPoint Y
  let i := Y.fromSpecResidueField η
  have : IsDominant i := by
    simp [isDominant_iff, denseRange_iff_closure_range, Y.range_fromSpecResidueField, η, i]
  have : IsSchemeTheoreticallyDominant i := .of_isDominant i
  have : QuasiCompact i := ⟨fun U _ _ => (Set.toFinite (i ⁻¹' U)).isCompact⟩
  have : IsReduced (pullback f i) := by
    simpa [Scheme.Hom.fiber, η, i] using
      (inferInstance : IsReduced (f.fiber (genericPoint Y)))
  exact IsSchemeTheoreticallyDominant.isReduced (Limits.pullback.fst f i)

/-- **Stacks Project, Tag 0BCM.** If a flat morphism has integral target and integral generic
fibre, then its source is integral. -/
@[stacks 0BCM]
theorem isIntegral_of_flat_of_isIntegral_genericFiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsIntegral Y]
    [IsIntegral (f.fiber (genericPoint Y))] : IsIntegral X := by
  have : IrreducibleSpace X := irreducibleSpace_of_integral_genericFiber f
  have : IsReduced X := isReduced_of_flat_of_isIntegral_genericFiber f
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end AlgebraicGeometry
