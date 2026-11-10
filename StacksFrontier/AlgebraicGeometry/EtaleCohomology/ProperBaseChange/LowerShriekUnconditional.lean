module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived lower shriek: independence, composition and base change, unconditionally

The comparisons of the derived lower shriek `Rf_! = Rf̄_* ∘ Rj_!` on `D(-_étale, Λ)` with respect
to a change of compactification ([Stacks, Tag 0F7I]), to composition ([Stacks, Tag 0F7J]) and to
base change ([Stacks, Tag 0F7L]), and the base change theorem for sheaves of `Λ`-modules
([Stacks, Tag 0DDE]), are proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekComposition`,
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekBaseChange` and
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.DerivedAdjunctionUnbounded` from
the statement that cohomology commutes with base change for every proper morphism. That statement is
the proper base change theorem ([Stacks, Tag 095T]),
`Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper`, which is a theorem for
coefficients in `AddCommGrpCat.{u + 1}`. This file substitutes it, so the results below hold for
every ring `Λ : Type` with no further input.

All objects are bounded below with torsion underlying cohomology sheaves (the category
`D^+_{tors}(X_étale, Λ)` of [Stacks, Section 0F7H]).

## Main results

* `Stacks.EtaleCohomology.isIso_etaleModuleUnboundedDerivedBaseChange_of_isProper` — **Tag 0DDE
  for sheaves of `Λ`-modules**: for `f` proper and a cartesian square,
  `g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` is an isomorphism.
* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_of_isProper_of_finite` — the same for
  a finite ring `Λ`, with no torsion hypothesis: every complex of sheaves of `Λ`-modules then has
  torsion cohomology
  (`Stacks.EtaleCohomology.torsionCohomologyProperty_etaleModuleForgetDerived_of_finite`).
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedIndependenceIso` — **Tag 0F7I**:
  `Rf_!^{(1)} K ≅ Rf_!^{(2)} K` for two compactifications.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompositionIso` — **Tag 0F7J**:
  `Rg_! (Rf_! K) ≅ R(g ∘ f)_! K`.
* `Stacks.EtaleCohomology.isIso_derivedLowerShriekRingUnboundedBaseChange_app` — **Tag 0F7L**:
  the base change map `g⁻¹ Rf_! K ⟶ Rf'_! (g')⁻¹ K` is an isomorphism, `Rf'_!` being computed
  through the base change of the compactification.

## References

* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.CompactificationOf

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ]

/-- **Stacks 0DDE for sheaves of `Λ`-modules.** Let `f : X ⟶ Y` be proper and
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
a cartesian square. For every object `E` of `D(X_étale, Λ)` which is bounded below and whose
underlying complex of abelian sheaves has torsion cohomology sheaves, the base change map
`g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` is an isomorphism. -/
@[sga "4 XVII 4.3.2" "(ii)"]
theorem isIso_etaleModuleUnboundedDerivedBaseChange_of_isProper {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    (E : DerivedCategory (EtaleModules.{u, 0} Λ X)) (n : ℤ) [E.IsGE n]
    (hT : Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, 0} Λ X).obj E)) :
    IsIso ((etaleModuleDerivedBaseChangeGeneral.{u, 0} Λ f g g' f' sq.w).app E) :=
  isIso_etaleModuleDerivedBaseChange_of_cohomologyCommutesWithBaseChange Λ
    (cohomologyCommutesWithBaseChange_of_isProper f) sq E n hT

/-- **Sheaves of modules over a finite ring are torsion.** If `Λ` is finite then the abelian sheaf
underlying a sheaf of `Λ`-modules on `X_étale` is torsion: every section is killed by the
cardinality of `Λ`. -/
theorem torsionSheafProperty_etaleModuleForget_of_finite [Finite Λ] {X : Scheme.{u}}
    (M : EtaleModules.{u, 0} Λ X) :
    Stacks.Torsion.torsionSheafProperty.{u + 1} X.smallEtaleTopology
      ((etaleModuleForgetAb.{u, 0} Λ X).obj M) := by
  have := Fintype.ofFinite Λ
  intro U x
  refine ⟨⊤, X.smallEtaleTopology.top_mem U, fun V f _ ↦ ⟨Fintype.card Λ, Fintype.card_pos, ?_⟩⟩
  change Fintype.card Λ • (M.obj.map f.op x : M.obj.obj (Opposite.op V)) = 0
  rw [← one_smul Λ (M.obj.map f.op x), ← smul_assoc, card_nsmul_eq_zero, zero_smul]

/-- **Complexes of sheaves of modules over a finite ring have torsion cohomology.** If `Λ` is
finite then for every object `E` of `D(X_étale, Λ)` the cohomology sheaves of the underlying
complex of abelian sheaves are torsion. -/
theorem torsionCohomologyProperty_etaleModuleForgetDerived_of_finite [Finite Λ]
    {X : Scheme.{u}} (E : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, 0} Λ X).obj E) := fun i ↦
  Stacks.Torsion.torsionSheafProperty_of_iso X.smallEtaleTopology
    (((etaleModuleForgetAb.{u, 0} Λ X).mapDerivedCategoryHomologyIso i).app E).symm
    (torsionSheafProperty_etaleModuleForget_of_finite Λ _)

/-- **Stacks 0DDE for sheaves of modules over a finite ring.** Let `Λ` be a finite ring,
`f : X ⟶ Y` proper and
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
a cartesian square. For every bounded below object `E` of `D(X_étale, Λ)` the base change map
`g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` is an isomorphism. -/
theorem isIso_etaleModuleDerivedBaseChange_of_isProper_of_finite [Finite Λ]
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) (E : DerivedCategory (EtaleModules.{u, 0} Λ X)) (n : ℤ)
    [E.IsGE n] :
    IsIso ((etaleModuleDerivedBaseChangeGeneral.{u, 0} Λ f g g' f' sq.w).app E) :=
  isIso_etaleModuleUnboundedDerivedBaseChange_of_isProper Λ f sq E n
    (torsionCohomologyProperty_etaleModuleForgetDerived_of_finite Λ E)

section LowerShriek

variable {X Y Z : Scheme.{u}}

/-- **Stacks 0F7I.** Let `f : X ⟶ Y` be a quasi-compact morphism with two compactifications
`j₁ : X ⟶ X̄₁` and `j₂ : X ⟶ X̄₂` over `Y`. For every `K` in `D(X_étale, Λ)` which is bounded
below and whose underlying complex of abelian sheaves has torsion cohomology sheaves,
`Rf_!^{(1)} K ≅ Rf_!^{(2)} K`, through the compactification dominating both. -/
def derivedLowerShriekUnboundedIndependenceIso {f : X ⟶ Y} [QuasiCompact f]
    (j₁ j₂ : CompactificationOf (Over.mk f)) (K : DerivedCategory (EtaleModules.{u, 0} Λ X))
    (n : ℤ) [K.IsGE n]
    (hK : Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, 0} Λ X).obj K)) :
    (derivedLowerShriekUnbounded.{u, 0} f j₁ Λ).obj K ≅
      (derivedLowerShriekUnbounded.{u, 0} f j₂ Λ).obj K :=
  derivedLowerShriekUnboundedCompactificationIsoUnconditional.{u, 0} Λ j₁ j₂
    (fun _ _ p _ ↦ cohomologyCommutesWithBaseChange_of_isProper p) K n hK

/-- **Stacks 0F7J.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be quasi-compact morphisms with
compactifications `j_f`, `j_g` and `j_{g ∘ f}` of `f`, `g` and `g ∘ f`. For every `K` in
`D(X_étale, Λ)` which is bounded below and whose underlying complex of abelian sheaves has
torsion cohomology sheaves, `Rg_! (Rf_! K) ≅ R(g ∘ f)_! K`, the three functors computed through
`j_g`, `j_f` and `j_{g ∘ f}`. -/
def derivedLowerShriekUnboundedCompositionIso {f : X ⟶ Y} {g : Y ⟶ Z} [QuasiCompact f]
    [QuasiCompact g] (jg : CompactificationOf (Over.mk g)) (jf : CompactificationOf (Over.mk f))
    (jgf : CompactificationOf (Over.mk (f ≫ g))) (K : DerivedCategory (EtaleModules.{u, 0} Λ X))
    (n : ℤ) [K.IsGE n]
    (hK : Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, 0} Λ X).obj K)) :
    (derivedLowerShriekUnbounded.{u, 0} g jg Λ).obj
        ((derivedLowerShriekUnbounded.{u, 0} f jf Λ).obj K) ≅
      (derivedLowerShriekUnbounded.{u, 0} (f ≫ g) jgf Λ).obj K :=
  derivedLowerShriekUnboundedCompIsoUniv.{u, 0} Λ jg
    (fun _ _ p _ ↦ cohomologyCommutesWithBaseChange_of_isProper p) jf jgf K n hK

/-- **Stacks 0F7L.** Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square and `j` a compactification of `f`, with base change `j'` a compactification
of `f'`. For every `K` in `D(X_étale, Λ)` which is bounded below and whose underlying complex of
abelian sheaves has torsion cohomology sheaves, the base change map
`g⁻¹ Rf_! K ⟶ Rf'_! (g')⁻¹ K` is an isomorphism. -/
theorem isIso_derivedLowerShriekRingUnboundedBaseChange_app {X' Y' : Scheme.{u}} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    (j : CompactificationOf (Over.mk f))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) (n : ℤ) [K.IsGE n]
    (hK : Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology
      ((etaleModuleForgetDerived.{u, 0} Λ X).obj K)) :
    IsIso ((derivedLowerShriekBaseChangeGeneral.{u, 0} Λ sq j).app K) :=
  isIso_derivedLowerShriekBaseChange_app_of_proper_base_change.{u, 0} Λ sq j
    (fun _ _ p _ ↦ cohomologyCommutesWithBaseChange_of_isProper p) K n hK

end LowerShriek

end Stacks.EtaleCohomology

end
