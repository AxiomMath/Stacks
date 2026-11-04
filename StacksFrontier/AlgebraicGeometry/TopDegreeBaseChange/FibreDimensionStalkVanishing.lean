module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeTensorProjection

/-!
# Both parts of Tag 0E7D

[Stacks, Tag 0E7D] fixes a proper morphism `f : X ⟶ Y` and a point `y ∈ Y` with `dim(X_y) = d`,
and asserts that `(Rⁱ f_* F)_y = 0` for `i > d` and every quasi-coherent `F` (part 1), and that
`y` has an affine open neighbourhood `V` over which `f ⁻¹ V ⟶ V` and `d` satisfy the hypotheses
and the conclusions of [Stacks, Tag 0EX3] (part 2).

`AffineBaseCohomology.lean` reduces both parts to the vanishing of the absolute cohomology
`Hⁱ(X₀, F)` above `d` for a proper morphism onto an **affine** base all of whose fibres have
dimension at most `d`. `AffineBaseVanishing.lean` proves that vanishing, for quasi-coherent
modules and with no Noetherian hypothesis on the base, by the source's two limit reductions down
to the Noetherian case. This file composes the two.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `isZero_stalk_rightDerivedPlus_of_topologicalKrullDim_fiber_le`: **part (1) of
  [Stacks, Tag 0E7D]**.
* `exists_isAffineOpen_topDegreeBaseChange_of_topologicalKrullDim_fiber_le`: **part (2) of
  [Stacks, Tag 0E7D]**, with the hypotheses of [Stacks, Tag 0EX3] for `f ∣_ V` and its
  conclusions (a) and (b) for every cartesian square over `V`.

## Implementation notes

The fibre-dimension hypothesis is `dim(X_y) ≤ d` rather than `dim(X_y) = d`: this is more
general, and it is the form the proof uses ([Stacks, Tag 02FZ] spreads it to a neighbourhood).

## References

* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens

noncomputable section

/-- **[Stacks, Tag 0E7D] part (1).** For `f : X ⟶ Y` proper, `y ∈ Y` whose fibre has topological
Krull dimension at most `d`, and `F` quasi-coherent, the stalk at `y` of `Rⁱ f_* F` vanishes for
every `i > d`.

This is `isZero_stalk_rightDerivedPlus_of_cohomology_vanishing` with its hypothesis supplied by
`cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le`. -/
@[stacks 0E7D "part (1)"]
theorem isZero_stalk_rightDerivedPlus_of_topologicalKrullDim_fiber_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsQuasicoherent] (i : ℤ) (hi : (d : ℤ) < i) :
    IsZero ((((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F).presheaf.stalk y) :=
  isZero_stalk_rightDerivedPlus_of_cohomology_vanishing f y d hdim
    (cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le d) F i hi

/-- **[Stacks, Tag 0E7D] part (2).** For `f : X ⟶ Y` proper and `y ∈ Y` whose fibre has
topological Krull dimension at most `d`, the point `y` has an affine open neighbourhood `V` such
that `f ∣_ V : f ⁻¹ V ⟶ V` and `d` satisfy

* the hypotheses of [Stacks, Tag 0EX3]: `f ⁻¹ V` and `V` are quasi-compact and
  quasi-separated, and `Rⁱ (f ∣_ V)_* F = 0` for `i > d` and every quasi-coherent `F`;
* conclusion (a) of [Stacks, Tag 0EX3]: for every cartesian square
  `X' ⟶ f ⁻¹ V`, `f' : X' ⟶ Y'`, `Y' ⟶ V`, `Rⁱ f'_* F' = 0` for `i > d` and every
  quasi-coherent `F'` on `X'`;
* conclusion (b) of [Stacks, Tag 0EX3]: for every such square and quasi-coherent `F'` on `X'`
  and `G'` on `Y'`, `Rᵈ f'_*(F' ⊗ (f')^* G') ≅ Rᵈ f'_* F' ⊗ G'`, with `Rᵈ f'_*` read as the
  degree-`d` cohomology of the derived direct image of a module placed in degree `0`. -/
@[stacks 0E7D "part (2): the hypotheses of Tag 0EX3 and its conclusions (a) and (b)"]
theorem exists_isAffineOpen_topDegreeBaseChange_of_topologicalKrullDim_fiber_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y) (d : ℕ)
    (hdim : topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞)) :
    ∃ V : Y.Opens,
      y ∈ V ∧ IsAffineOpen V ∧
      CompactSpace (f ⁻¹ᵁ V).toScheme ∧
      QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme ∧
      CompactSpace V.toScheme ∧ QuasiSeparatedSpace V.toScheme ∧
      (∀ (i : ℤ), (d : ℤ) < i →
        ∀ (F : (f ⁻¹ᵁ V).toScheme.Modules), F.IsQuasicoherent →
          IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus i).obj F)) ∧
      (∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ (f ⁻¹ᵁ V).toScheme) (f' : X' ⟶ Y')
          (g : Y' ⟶ V.toScheme), IsPullback g' f' (f ∣_ V) g →
        ∀ (i : ℤ), (d : ℤ) < i → ∀ (F' : X'.Modules), F'.IsQuasicoherent →
          IsZero (((Scheme.Modules.pushforward f').rightDerivedPlus i).obj F')) ∧
      (∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ (f ⁻¹ᵁ V).toScheme) (f' : X' ⟶ Y')
          (g : Y' ⟶ V.toScheme), IsPullback g' f' (f ∣_ V) g →
        ∀ (F' : SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)), F'.IsQuasicoherent →
        ∀ (G' : SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace)), G'.IsQuasicoherent →
          Nonempty ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace)) (d : ℤ)).obj
              ((derivedPushforward f'.toLRSHom.toShHom).obj
                ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) 0).obj
                  (((Stacks.SheafOfModules.Tensor.sheafTensor X'.toRingedSpace.sheaf).obj F').obj
                    ((RingedSpaceModuleAdjunction.modulePullback f'.toLRSHom.toShHom).obj
                      G')))) ≅
            ((Stacks.SheafOfModules.Tensor.sheafTensor Y'.toRingedSpace.sheaf).obj
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace)) (d : ℤ)).obj
                ((derivedPushforward f'.toLRSHom.toShHom).obj
                  ((DerivedCategory.singleFunctor
                    (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) 0).obj F')))).obj
              G')) := by
  obtain ⟨V, hyV, hV, hcX, hqX, hcY, hqY, hvan⟩ :=
    exists_isAffineOpen_vanishing_of_cohomology_vanishing f y d hdim
      (cohomology_vanishing_of_forall_topologicalKrullDim_fiber_le d)
  let S : ∀ {X' Y' : Scheme.{u}} (g' : X' ⟶ (f ⁻¹ᵁ V).toScheme) (f' : X' ⟶ Y')
      (g : Y' ⟶ V.toScheme), IsPullback g' f' (f ∣_ V) g →
      Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u} :=
    fun {X' Y'} g' f' g sq =>
      { X := (f ⁻¹ᵁ V).toScheme, Y := V.toScheme, f := f ∣_ V, d := d
        isCompact_X := hcX, isQuasiSeparated_X := hqX
        isCompact_Y := hcY, isQuasiSeparated_Y := hqY
        vanishes_above := hvan
        X' := X', Y' := Y', g' := g', f' := f', g := g, isPullback := sq }
  refine ⟨V, hyV, hV, hcX, hqX, hcY, hqY, hvan, ?_, ?_⟩
  · intro X' Y' g' f' g sq i hi F' _
    exact isZero_rightDerivedPlus_pushforward_baseChange (S g' f' g sq) i hi F'
  · intro X' Y' g' f' g sq F' _ G' _
    exact ⟨(S g' f' g sq).topDegreeTensorSheafIso F' G'⟩

end

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
