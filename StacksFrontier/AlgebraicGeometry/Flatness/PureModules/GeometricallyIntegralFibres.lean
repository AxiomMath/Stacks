module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Limits.IsConnected
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Reduced
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# Universal purity of a flat morphism with geometrically integral fibres

A flat finite type morphism with geometrically integral fibres has universally pure structure
sheaf relative to its base.

The reason is that on an integral scheme the only associated point of the structure sheaf is the
generic point. An impurity would produce a point of the relative assassin of the pulled-back
structure sheaf over the generalization `t'`, hence the generic point of the fibre over `t'`.
Flatness makes the base change generalizing, so that point generalizes a point of the fibre over
`t`, which therefore lies in the closure the impurity asks to be disjoint from that fibre.

## Main results

* `AlgebraicGeometry.universallyPure_of_flat_geometricallyIntegral`: universal purity of the
  structure sheaf of a flat finite type morphism with geometrically integral fibres.

## Implementation notes

Finite type is expressed by local finite type together with quasi-compactness, and universal
purity of a scheme by applying relative universal purity to its structure sheaf. The pullback of
the structure sheaf along a morphism is identified with the structure sheaf of the source by
`SheafOfModules.pullbackObjUnitToUnit`, which is an isomorphism because the inverse-image
functor on opens is final.

## References

* [Stacks Project, Tag 05K5](https://stacks.math.columbia.edu/tag/05K5)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- On an integral scheme the only associated point of the structure sheaf is the generic
point. -/
private theorem associatedPoint_eq_genericPoint_of_integral {Z : Scheme.{u}} (z : Z)
    (hz : z ∈ Stacks.Divisors.associatedPoints (SheafOfModules.unit Z.ringCatSheaf))
    [IsIntegral Z] : z = genericPoint Z := by
  have hweak : z ∈ Stacks.Divisors.schemeWeaklyAssociatedPoints Z := by
    simpa [Stacks.Divisors.schemeWeaklyAssociatedPoints] using
      Stacks.Divisors.associatedPoints_subset (SheafOfModules.unit Z.ringCatSheaf) hz
  rw [weaklyAssociatedPointsOfScheme_eq_genericPoints Z, genericPoints_eq_singleton] at hweak
  simpa using hweak

/-- **Stacks Project, Tag 05K5.** A flat finite type morphism with geometrically integral
fibres has universally pure structure sheaf over its base. -/
@[stacks 05K5]
theorem universallyPure_of_flat_geometricallyIntegral {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] [Flat f] [GeometricallyIntegral f] :
    @IsUniversallyPureRelative.{u} X S f _ _
      (SheafOfModules.unit.{u} X.ringCatSheaf)
      (structureSheaf_isFiniteType X)
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X) := by
  intro s
  let P : PrePureSituation.{u} :=
    { S := S
      X := X
      f := f
      F := SheafOfModules.unit X.ringCatSheaf
      isFiniteType := structureSheaf_isFiniteType X
      isQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
      s := s }
  show ∀ D : ImpurityDiagram P, ¬ IsImpurity P D
  rintro D ⟨hAss, hDisjoint⟩
  obtain ⟨s', x', hx', hxi⟩ :=
    (Stacks.Divisors.mem_relativeAssassin D.toT (D.pulledBack P) D.xi).mp hAss
  have hb (t : D.T) (z : D.toT.fiber t) : D.toT.base (D.toT.fiberι t z) = t :=
    (D.toT.fiberHomeo t z).2
  obtain rfl : s' = D.t' := ((hb s' x').symm.trans (congrArg D.toT.base hxi)).trans D.xi_liesOver
  have _ : Flat D.toT := Flat.isStableUnderBaseChange.of_isPullback D.isPullback inferInstance
  have _ : GeometricallyIntegral D.toT :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) D.isPullback inferInstance
  have fiberIso : (Scheme.Modules.pullback ((D.toT).fiberι D.t')).obj (D.pulledBack P) ≅
      SheafOfModules.unit ((D.toT).fiber D.t').ringCatSheaf := by
    dsimp [P, ImpurityDiagram.pulledBack]
    exact (Scheme.Modules.pullbackComp ((D.toT).fiberι D.t') D.toX).app
        (SheafOfModules.unit X.ringCatSheaf) ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackUnitIso ((D.toT).fiberι D.t' ≫ D.toX)
  have _ : IsIso fiberIso.hom := fiberIso.isIso_hom
  have _ : Mono fiberIso.hom := IsIso.mono_of_iso _
  have hxGeneric : x' = genericPoint ((D.toT).fiber D.t') :=
    associatedPoint_eq_genericPoint_of_integral x'
      (associatedPoints_subset_of_mono fiberIso.hom hx')
  let z₀ : (D.toT).fiber D.t := genericPoint ((D.toT).fiber D.t)
  have hspec : D.t' ⤳ D.toT.base ((D.toT).fiberι D.t z₀) := by
    simpa [hb] using D.specializes
  obtain ⟨z', hz'z₀, hz't'⟩ := (Flat.generalizingMap D.toT) hspec
  let y' : (D.toT).fiber D.t' := (D.toT).fiberHomeo D.t' |>.symm ⟨z', hz't'⟩
  have hy' : D.toT.fiberι D.t' y' = z' := by simp [y']
  have hgenSpec : D.xi ⤳ z' := by
    rw [← hxi, hxGeneric, ← hy']
    exact (genericPoint_specializes y').map (D.toT.fiberι D.t').continuous
  have hmeet : D.toT.fiberι D.t z₀ ∈ closure {D.xi} ∩ Set.range (D.toT.fiberι D.t) :=
    ⟨(hgenSpec.trans hz'z₀).mem_closure, z₀, rfl⟩
  rw [hDisjoint] at hmeet
  exact hmeet

end AlgebraicGeometry
