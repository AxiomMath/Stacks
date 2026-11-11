module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.InjectiveVanishingBaseChange

/-!
# Base change for a proper direct image of étale sheaves: Stacks 0A3T, 0A3U and 0A4B

The reductions such as
`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper_of_strictHenselizationSet`
carry one input, [Stacks, Tag 03Q9] in degree zero for sheaves of sets at the strict
henselization. That input is
`Stacks.EtaleCohomology.isIso_inverseImage_smallEtaleSetBaseChange_strictHenselization`, so the
statements hold unconditionally.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper` — **[Stacks, Tag 0A3U]**:
  for `f` proper and a cartesian square, `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism for every
  sheaf of sets `F`.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isProper` — the same for abelian
  sheaves.
* `Stacks.EtaleCohomology.isIso_properGeometricFibreComparison_of_isProper` —
  **[Stacks, Tag 0A3T]**: for `f` proper and a geometric point `x` of the base, the map
  `(f_* F)_x ⟶ Γ(X_x, F_x)` is bijective for every sheaf of sets `F`.
* `cohomologyCommutesWithBaseChange_iff_higherDirectImagesVanishOnInjectives` —
  **[Stacks, Tag 0A4B]**.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **Stacks Project, Tag 0A3U.** Let `f : X ⟶ Y` be proper, `g : Y' ⟶ Y` any morphism and
`X' = Y' ×_Y X` with projections `f' : X' ⟶ Y'`, `g' : X' ⟶ X`. For every sheaf of sets `F` on
`X_étale`, the canonical map `g⁻¹ f_* F ⟶ f'_* (g')⁻¹ F` is an isomorphism. -/
theorem isIso_smallEtaleSetBaseChange_of_isProper
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (sq : IsPullback g' f' f g) :
    IsIso (smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w) :=
  isIso_smallEtaleSetBaseChange_of_isProper_of_strictHenselizationSet
    (fun _ S φ _ s F ↦ isIso_inverseImage_smallEtaleSetBaseChange_strictHenselization _ S _ s φ F)
    f g g' f' sq

/-- [Stacks, Tag 0A3U] for abelian sheaves: for `f` proper and a cartesian square, the base change
map `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of abelian étale sheaves is an isomorphism. -/
theorem isIso_etaleAbelianBaseChange_of_isProper
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (sq : IsPullback g' f' f g) :
    IsIso (etaleAbelianBaseChange.{u, 0} f g g' f' sq.w) :=
  isIso_etaleAbelianBaseChange_of_isProper_of_strictHenselizationSet
    (fun _ S φ _ s F ↦ isIso_inverseImage_smallEtaleSetBaseChange_strictHenselization _ S _ s φ F)
    f g g' f' sq

/-- **Stacks Project, Tag 0A3T.** Let `f : X ⟶ S` be proper and `x : Spec Ω ⟶ S` a geometric
point (`Ω` separably closed). For every sheaf of sets `F` on `X_étale` the canonical map
`(f_* F)_x ⟶ Γ(X_x, F_x)` is bijective. -/
@[stacks 0A3T "for every sheaf of sets on the small étale site of `X`, naturally in the sheaf"]
theorem isIso_properGeometricFibreComparison_of_isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ S) :
    IsIso (properGeometricFibreComparison.{u, 0} f x) :=
  isIso_properGeometricFibreComparison_of_strictHenselizationSet
    (fun _ S φ _ s F ↦ isIso_inverseImage_smallEtaleSetBaseChange_strictHenselization _ S _ s φ F)
    f x

/-- **Stacks Project, Tag 0A4B.** For `f` proper, cohomology commutes with base change for `f`
exactly when, for every prime `ℓ`, every injective sheaf `I` of `ℤ/ℓℤ`-modules on `X_étale` and
every cartesian square, `R^q f'_* (g')⁻¹ I = 0` for `q > 0`. -/
theorem cohomologyCommutesWithBaseChange_iff_higherDirectImagesVanishOnInjectives
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    CohomologyCommutesWithBaseChange.{u, 0} f ↔ HigherDirectImagesVanishOnInjectives.{u, 0} f :=
  ⟨CohomologyCommutesWithBaseChange.higherDirectImagesVanishOnInjectives,
    cohomologyCommutesWithBaseChange_of_higherDirectImagesVanishOnInjectives f
      (fun _ _ g g' f' sq ↦ isIso_etaleAbelianBaseChange_of_isProper f g g' f' sq)⟩

end Stacks.EtaleCohomology

end
