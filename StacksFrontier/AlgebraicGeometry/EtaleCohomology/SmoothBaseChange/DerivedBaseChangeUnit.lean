module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeMateUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition

/-!
# The derived base change map of small étale sites computes pullback on morphisms

Let

```
X' ←-h-- Y
|f'      |e
S  ←-g-- T
```

be a commutative square of schemes. The derived base change map
`β = Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb f' g h e w : Rg_* ⋙ f'⁻¹ ⟶ e⁻¹ ⋙ Rh_*`
on bounded below derived categories of abelian sheaves on the small étale sites is the descent of
the mate of the comparison `e_* ⋙ g_* ≅ h_* ⋙ f'_*` of the composite direct images. This file reads
`Stacks.Cohomology.BaseChange.map_derivedUnit_comp_derivedMate_app` and its consequences in that
situation:

* `Stacks.EtaleCohomology.map_derivedUnit_comp_smallEtaleDerivedBaseChangeAb_app` — for `M` in
  `D⁺(S_étale)`, `f'⁻¹` of the unit of `g⁻¹ ⊣ Rg_*` at `M` followed by `β` at `g⁻¹M` is the unit of
  `h⁻¹ ⊣ Rh_*` at `f'⁻¹M` followed by `Rh_*` of the comparison `h⁻¹f'⁻¹ ≅ e⁻¹g⁻¹`;
* `Stacks.EtaleCohomology.bijective_smallEtaleDerivedPullback_map_of_isIso` — if `β` is invertible
  at `N` and `f'⁻¹` is bijective on `Hom(M, Rg_*N)`, then `e⁻¹` is bijective on `Hom(g⁻¹M, N)`.

Here `M` plays the rôle of a coefficient object on the base, so that `Hom(g⁻¹M, N)` is cohomology
of `N` with coefficients in `M`, and the second statement is the form in which a base change
theorem gives the invariance of cohomology under the base change `e`.

## Implementation notes

`smallEtaleDerivedBaseChangeAb` is, by its definition, `Stacks.Cohomology.BaseChange.derivedMate`
at the four abelian adjunctions `Stacks.EtaleCohomology.smallEtaleAdjunctionAb` and at the
comparison of composite direct images `smallEtaleDirectImageSquareIso` below; the two statements
are the general ones at those arguments. The standard model of the derived category is the one
`smallEtaleDerivedBaseChangeAb` is built under.

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

-- `smallEtaleDerivedBaseChangeAb` is built under the standard model, so its components live in
-- the standard bounded below derived categories.
attribute [local instance] HasDerivedCategory.standard

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- The comparison `e_* ⋙ g_* ≅ h_* ⋙ f'_*` of the two composite direct images of a commutative
square, whose mate is the underived base change map
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb`. -/
abbrev smallEtaleDirectImageSquareIso :
    smallEtalePushforwardAb e ⋙ smallEtalePushforwardAb g ≅
      smallEtalePushforwardAb h ⋙ smallEtalePushforwardAb f' :=
  (smallEtalePushforwardAbCompIso e g).trans
    ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
      (smallEtalePushforwardAbCompIso h f').symm)

/-- The derived comparison `f'⁻¹ ⋙ h⁻¹ ≅ g⁻¹ ⋙ e⁻¹` of the two composite inverse images of a
commutative square, on bounded below derived categories. -/
abbrev smallEtaleDerivedPullbackSquareIso :
    (smallEtalePullbackAb f').rightDerivedFunctorPlus ⋙
        (smallEtalePullbackAb h).rightDerivedFunctorPlus ≅
      (smallEtalePullbackAb g).rightDerivedFunctorPlus ⋙
        (smallEtalePullbackAb e).rightDerivedFunctorPlus :=
  Stacks.Cohomology.BaseChange.derivedSquareLeftIso (smallEtaleAdjunctionAb g)
    (smallEtaleAdjunctionAb f') (smallEtaleAdjunctionAb e) (smallEtaleAdjunctionAb h)
    (smallEtaleDirectImageSquareIso f' g h e w)

/-- `smallEtaleDerivedBaseChangeAb` is `Stacks.Cohomology.BaseChange.derivedMate` at the abelian
adjunctions and the comparison of composite direct images. -/
theorem smallEtaleDerivedBaseChangeAb_eq_derivedMate :
    smallEtaleDerivedBaseChangeAb f' g h e w =
      Stacks.Cohomology.BaseChange.derivedMate (smallEtaleAdjunctionAb f')
        (smallEtaleAdjunctionAb e) (smallEtaleDirectImageSquareIso f' g h e w) :=
  rfl

/-- **The derived base change map and the units.** For `M` in `D⁺(S_étale)`, `f'⁻¹` of the unit of
`g⁻¹ ⊣ Rg_*` at `M`, followed by the derived base change map at `g⁻¹M`, is the unit of
`h⁻¹ ⊣ Rh_*` at `f'⁻¹M` followed by `Rh_*` of the comparison of the composite inverse images. -/
theorem map_derivedUnit_comp_smallEtaleDerivedBaseChangeAb_app
    (M : DerivedCategory.Plus (Sheaf (smallEtaleTopology S) Ab.{u + 1})) :
    (smallEtalePullbackAb f').rightDerivedFunctorPlus.map
        ((smallEtaleAdjunctionAb g).rightDerivedFunctorPlus.unit.app M) ≫
      (smallEtaleDerivedBaseChangeAb f' g h e w).app
        ((smallEtalePullbackAb g).rightDerivedFunctorPlus.obj M) =
    (smallEtaleAdjunctionAb h).rightDerivedFunctorPlus.unit.app
        ((smallEtalePullbackAb f').rightDerivedFunctorPlus.obj M) ≫
      (smallEtalePushforwardAb h).rightDerivedFunctorPlus.map
        ((smallEtaleDerivedPullbackSquareIso f' g h e w).hom.app M) :=
  Stacks.Cohomology.BaseChange.map_derivedUnit_comp_derivedMate_app _ _ _ _ _ M

/-- **Pullback is bijective on morphisms out of a pullback when the base change map is
invertible.** If the derived base change map is invertible at `N` and `f'⁻¹` is bijective on
`Hom(M, Rg_*N)`, then `e⁻¹` is bijective on `Hom(g⁻¹M, N)`. -/
theorem bijective_smallEtaleDerivedPullback_map_of_isIso
    (M : DerivedCategory.Plus (Sheaf (smallEtaleTopology S) Ab.{u + 1}))
    (N : DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}))
    (hN : IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app N))
    (hM : Function.Bijective
      (fun ψ : M ⟶ (smallEtalePushforwardAb g).rightDerivedFunctorPlus.obj N ↦
        (smallEtalePullbackAb f').rightDerivedFunctorPlus.map ψ)) :
    Function.Bijective (fun φ : (smallEtalePullbackAb g).rightDerivedFunctorPlus.obj M ⟶ N ↦
      (smallEtalePullbackAb e).rightDerivedFunctorPlus.map φ) :=
  Stacks.Cohomology.BaseChange.bijective_map_of_isIso_derivedMate_app (smallEtaleAdjunctionAb g)
    (smallEtaleAdjunctionAb f') (smallEtaleAdjunctionAb e) (smallEtaleAdjunctionAb h)
    (smallEtaleDirectImageSquareIso f' g h e w) M N hN hM

end Stacks.EtaleCohomology
