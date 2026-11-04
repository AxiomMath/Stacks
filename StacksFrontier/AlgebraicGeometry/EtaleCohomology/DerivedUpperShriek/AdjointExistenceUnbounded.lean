module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperDirectImageDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedBelowDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.DirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModel
public import StacksFrontier.Homology.DerivedCategory.MapDerivedCategoryDirectSums
public import StacksFrontier.Homology.Injectives.BrownRepresentabilityRightAdjoint
import StacksCore.Tactic.StacksAttribute

/-!
# The right adjoint `Rf^!` of the unbounded derived lower shriek

Let `f : X ⟶ Y` be a finite type separated morphism of quasi-compact and quasi-separated schemes
and let `Λ` be a ring. Then `Rf_!` commutes with direct sums of families in `D⁺(X_étale, Λ)` with a
common lower bound, [Stacks, Tag 0G29] (1). If `Λ` is torsion, the functor
`Rf_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` commutes with direct sums, [Stacks, Tag 0G29] (2), and has
a right adjoint `Rf^! : D(Y_étale, Λ) ⟶ D(X_étale, Λ)`, [Stacks, Tag 0G2C].

Here `Rf_!` is `Stacks.EtaleCohomology.derivedLowerShriekUnbounded f j Λ = Rf̄_* ∘ Rj_!` for a
compactification `f = f̄ ∘ j` (which exists by [Stacks, Tag 0F41]); both statements hold for every
compactification, and by [Stacks, Tag 0F7I] the functors of different compactifications are
canonically isomorphic.

## Main results

* `Stacks.EtaleCohomology.preservesColimit_derivedLowerShriek_of_isGE`: [Stacks, Tag 0G29] (1).
* `Stacks.EtaleCohomology.preservesColimitsOfShape_derivedLowerShriekUnbounded`:
  [Stacks, Tag 0G29] (2).
* `Stacks.EtaleCohomology.isLeftAdjoint_derivedLowerShriekUnbounded` and
  `Stacks.EtaleCohomology.isLeftAdjoint_derivedLowerShriekUnbounded_of_compactification`:
  [Stacks, Tag 0G2C].
* `Stacks.EtaleCohomology.derivedUpperShriekUnbounded`: the functor `Rf^!`, with
  `Stacks.EtaleCohomology.derivedLowerShriekUnboundedAdjunction` the adjunction `Rf_! ⊣ Rf^!` and
  `Stacks.EtaleCohomology.derivedUpperShriekUnbounded_isTriangulated` its exactness.

## Implementation notes

The proof is the source's. `Rj_!` is extension by zero applied degreewise, extension by zero being
exact ([Stacks, Tag 03S5]) and a left adjoint, so it commutes with direct sums; `Rf̄_*` commutes
with direct sums because `f̄` is proper and `Λ` is torsion, [Stacks, Tag 0F0D]
(`preservesColimitsOfShape_etaleModuleDerivedDirectImageUnbounded_of_isProper`). Both are exact,
so Brown representability in the form `Stacks.Injectives.isLeftAdjoint_of_isGrothendieckAbelian`
([Stacks, Tag 0F5Y]) applies: sheaves of `Λ`-modules on `X_étale` form a Grothendieck abelian
category relative to their morphism universe `max (u + 1) r`, direct sums are indexed by that
universe, and the derived category of sheaves on `Y_étale` is locally small in it
(`Stacks.Injectives.locallySmall_standardDerivedCategory`).

The commutation of `Rf_!` with the shift is the one given by the universal properties of the two
derived functors (`Stacks.Injectives.KInjectiveResolution.commShiftOfIsRightDerivedFunctor`); it is
a definition rather than an instance, as for its two factors. Being a left adjoint does not depend
on it.

The coefficient ring is an arbitrary torsion ring `Λ : Type r`, in any universe.

## References

* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
* [Stacks Project, Tag 0G29](https://stacks.math.columbia.edu/tag/0G29)
* [Stacks Project, Tag 0F5Y](https://stacks.math.columbia.edu/tag/0F5Y)
* [Stacks Project, Tag 0F0D](https://stacks.math.columbia.edu/tag/0F0D)
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Injectives.KInjectiveResolution

universe u r

namespace Stacks.EtaleCohomology

/- `etaleModules_enoughInjectives_univZero` is stated for the coefficient ring in `Type`; instance
search would try to unify an arbitrary coefficient universe with it and fail on the universe
constraint, so it is switched off here. -/
attribute [-instance] etaleModules_enoughInjectives_univZero

attribute [local instance 2000] etaleModules_enoughInjectives

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type r) [Ring Λ]

/-! ### Extension by zero and direct sums -/

/-- The unbounded derived extension by zero `Rj_!` along an étale morphism commutes with direct
sums: it is extension by zero applied degreewise, and extension by zero is exact and a left
adjoint. -/
theorem preservesColimitsOfShape_etaleModuleDerivedExtensionByZeroUnbounded {U X : Scheme.{u}}
    (j : U ⟶ X) [Etale j] (I : Type (max (u + 1) r)) :
    PreservesColimitsOfShape (Discrete I)
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j) := by
  have : PreservesColimitsOfShape (Discrete I) (etaleModuleExtensionByZero.{u, r} Λ j) :=
    (etaleModuleExtensionByZeroAdj.{u, r} Λ j).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have := Stacks.SmallDerivedCategory.preservesColimitsOfShape_discrete_mapDerivedCategory
    (etaleModuleExtensionByZero.{u, r} Λ j) I
  exact preservesColimitsOfShape_of_natIso
    (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j).symm

/-! ### `Rf_!` commutes with direct sums -/

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- **[Stacks, Tag 0G29] (2).** Let `Λ` be a torsion ring and let
`Rf_! = Rf̄_* ∘ Rj_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` be the derived lower shriek of a
compactification `f = f̄ ∘ j`. Then `Rf_!` commutes with direct sums. -/
@[stacks 0G29 "(2) for Λ a torsion ring in any universe, on D(X_étale, Λ): Rf_! = Rf̄_* ∘ j_! \
commutes with direct sums. The base declarations of (2) assume the proper case (Tag 0F0D); here \
it is proved"]
theorem preservesColimitsOfShape_derivedLowerShriekUnbounded
    (j : CompactificationOf (Over.mk f)) (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)
    (I : Type (max (u + 1) r)) :
    PreservesColimitsOfShape (Discrete I) (derivedLowerShriekUnbounded.{u, r} f j Λ) := by
  have := preservesColimitsOfShape_etaleModuleDerivedExtensionByZeroUnbounded Λ j.immersion I
  have := preservesColimitsOfShape_etaleModuleDerivedDirectImageUnbounded_of_isProper Λ j.toBase
    hΛ I
  exact Limits.comp_preservesColimitsOfShape _ _

/-- **[Stacks, Tag 0G29] (1).** Let `f : X ⟶ Y` be a finite type separated morphism of
quasi-compact and quasi-separated schemes, let `Λ` be a ring, in any universe, and let
`Rf_! = R(fbar)_* ∘ j_!` be the derived lower shriek of a compactification `j` of `f`, on bounded
below derived categories. Let `K : I → D⁺(X_étale, Λ)` be a family of objects and `a : ℤ` such
that `H^n(K i) = 0` for `n < a` and all `i`. Then `Rf_!(⨁ i, K i) = ⨁ i, Rf_!(K i)`.

The source states this for `K i` in `D⁺_tors(X_étale, Λ)`; no torsion hypothesis is used, so it is
stated for all of `D⁺(X_étale, Λ)`. The three inputs of the source's proof are proved: the
adjunction `j_! ⊣ j^{-1}` ([Stacks, Tag 08FJ],
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroAdj`), that `j_!` preserves the lower
bound (a right derived functor does), and [Stacks, Tag 0GIW] for the proper morphism `fbar`
(`Stacks.EtaleCohomology.preservesColimit_etaleModuleDerivedDirectImage_of_isGE`, whose input
[Stacks, Tag 09Z1] is
`preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage_univ`). -/
@[stacks 0G29 "(1) Rf_!(⨁ K_i) = ⨁ Rf_! K_i for a family of D⁺(X_étale, Λ) with common lower \
bound a, Λ a ring in any universe; the base declaration of (1) assumes Tags 08FJ, 03S5 and 0GIW, \
here they are proved"]
theorem preservesColimit_derivedLowerShriek_of_isGE {X Y : Scheme.{u}} {f : X ⟶ Y}
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (j : CompactificationOf (Over.mk f)) {I : Type (max (u + 1) r)}
    (K : I → DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) (a : ℤ) (hK : ∀ i, (K i).IsGE a) :
    PreservesColimit (Discrete.functor K) (derivedLowerShriek.{u, r} f j Λ) := by
  have := quasiCompact_of_isProper j.toBase
  have := quasiSeparated_of_isProper j.toBase
  exact DerivedUpperShriek.preservesColimit_derivedLowerShriek_of_isGE j Λ K a hK
    (etaleModuleDerivedExtensionByZeroAdj.{u, r} Λ j.immersion)
    (fun b M hM ↦ have := hM; Functor.isGE_rightDerivedFunctorPlus_obj _ M b)
    (fun L hL ↦ preservesColimit_etaleModuleDerivedDirectImage_of_isGE Λ j.toBase
      (fun p ↦ preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage_univ Λ
        j.toBase p I) L a hL)

/-! ### `Rf_!` is exact -/

/-- The commutation with the shift of the unbounded derived extension by zero `Rj_!`, given by
its universal property. -/
@[instance_reducible]
def etaleModuleDerivedExtensionByZeroUnboundedCommShift {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] : (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j).CommShift ℤ :=
  commShiftOfIsRightDerivedFunctor (etaleModuleExtensionByZero.{u, r} Λ j) _
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j)

/-- The commutation with the shift of `Rf_! = Rf̄_* ∘ Rj_!`, composed from those of its two
factors. -/
@[instance_reducible]
def derivedLowerShriekUnboundedCommShift (j : CompactificationOf (Over.mk f)) :
    (derivedLowerShriekUnbounded.{u, r} f j Λ).CommShift ℤ :=
  letI := etaleModuleDerivedExtensionByZeroUnboundedCommShift.{u, r} Λ j.immersion
  letI := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ j.toBase
  inferInstanceAs ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion ⋙
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase).CommShift ℤ)

/-- `Rf_! = Rf̄_* ∘ Rj_!` is a triangulated functor. -/
theorem derivedLowerShriekUnbounded_isTriangulated (j : CompactificationOf (Over.mk f)) :
    letI := derivedLowerShriekUnboundedCommShift.{u, r} Λ j
    (derivedLowerShriekUnbounded.{u, r} f j Λ).IsTriangulated := by
  let := etaleModuleDerivedExtensionByZeroUnboundedCommShift.{u, r} Λ j.immersion
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ j.toBase
  have : (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).IsTriangulated :=
    isTriangulated_of_isRightDerivedFunctor (etaleModuleExtensionByZero.{u, r} Λ j.immersion) _
      (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j.immersion)
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, r} Λ j.toBase
  exact inferInstanceAs ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion ⋙
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase).IsTriangulated)

/-! ### The right adjoint -/

/-- **[Stacks, Tag 0G2C].** Let `Λ` be a torsion ring, in any universe, and let
`Rf_! = Rf̄_* ∘ Rj_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` be the derived lower shriek of a
compactification `f = f̄ ∘ j` of `X` over `Y`. Then `Rf_!` has a right
adjoint `Rf^! : D(Y_étale, Λ) ⟶ D(X_étale, Λ)`.

This is the source's proof: `Rf_!` is exact and commutes with direct sums ([Stacks, Tag 0G29]),
so Brown representability ([Stacks, Tag 0F5Y]) gives the right adjoint. -/
@[sga "4 XVIII 0.1" "partial"]
theorem isLeftAdjoint_derivedLowerShriekUnbounded
    (j : CompactificationOf (Over.mk f)) (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    (derivedLowerShriekUnbounded.{u, r} f j Λ).IsLeftAdjoint := by
  let := derivedLowerShriekUnboundedCommShift.{u, r} Λ j
  have := derivedLowerShriekUnbounded_isTriangulated.{u, r} Λ j
  have := preservesColimitsOfShape_derivedLowerShriekUnbounded Λ j hΛ
  have := Stacks.Injectives.locallySmall_standardDerivedCategory.{max (u + 1) r}
    (EtaleModules.{u, r} Λ Y)
  exact Stacks.Injectives.isLeftAdjoint_of_isGrothendieckAbelian (EtaleModules.{u, r} Λ X)
    (derivedLowerShriekUnbounded.{u, r} f j Λ) fun _ _ ↦ inferInstance

/-- **[Stacks, Tag 0G2C].** Let `f : X ⟶ Y` be a finite type separated morphism of quasi-compact
and quasi-separated schemes and let `Λ` be a torsion ring, in any universe. The functor
`Rf_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` has a right adjoint
`Rf^! : D(Y_étale, Λ) ⟶ D(X_étale, Λ)`.

Here `Rf_!` is `Rf̄_* ∘ Rj_!` for a compactification `f = f̄ ∘ j`, as in [Stacks, Tag 0F7H]: such
a compactification exists ([Stacks, Tag 0F41]), and for every one of them `Rf_!` is a left
adjoint. -/
@[stacks 0G2C "Rf_! = Rf̄_* ∘ Rj_! on D(X_étale, Λ), Λ a torsion ring in any universe, for every \
compactification", sga "4 XVII 3.2.6" "(i), special case"]
theorem isLeftAdjoint_derivedLowerShriekUnbounded_of_compactification (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    (∃ j : CompactificationOf (Over.mk f), QuasiCompact j.immersion) ∧
      ∀ j : CompactificationOf (Over.mk f),
        (derivedLowerShriekUnbounded.{u, r} f j Λ).IsLeftAdjoint :=
  ⟨hasCompactification_of_compactSpace_quasiSeparatedSpace f,
    fun j ↦ isLeftAdjoint_derivedLowerShriekUnbounded Λ j hΛ⟩

variable (j : CompactificationOf (Over.mk f)) (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)

/-- `Rf^! : D(Y_étale, Λ) ⟶ D(X_étale, Λ)`, the right adjoint of the derived lower shriek
`Rf_! = Rf̄_* ∘ Rj_!` of a compactification, provided by [Stacks, Tag 0G2C]. -/
abbrev derivedUpperShriekUnbounded :
    DerivedCategory (EtaleModules.{u, r} Λ Y) ⥤ DerivedCategory (EtaleModules.{u, r} Λ X) :=
  letI := isLeftAdjoint_derivedLowerShriekUnbounded Λ j hΛ
  (derivedLowerShriekUnbounded.{u, r} f j Λ).rightAdjoint

/-- The adjunction `Rf_! ⊣ Rf^!` of [Stacks, Tag 0G2C]. -/
def derivedLowerShriekUnboundedAdjunction :
    derivedLowerShriekUnbounded.{u, r} f j Λ ⊣ derivedUpperShriekUnbounded Λ j hΛ :=
  letI := isLeftAdjoint_derivedLowerShriekUnbounded Λ j hΛ
  Adjunction.ofIsLeftAdjoint (derivedLowerShriekUnbounded.{u, r} f j Λ)

/-- `Rf^!` is exact: it commutes with the shift and is a triangulated functor, being the right
adjoint of a triangulated functor. -/
theorem derivedUpperShriekUnbounded_isTriangulated :
    ∃ commShift : (derivedUpperShriekUnbounded Λ j hΛ).CommShift ℤ,
      letI := commShift
      (derivedUpperShriekUnbounded Λ j hΛ).IsTriangulated := by
  let := derivedLowerShriekUnboundedCommShift.{u, r} Λ j
  have := derivedLowerShriekUnbounded_isTriangulated.{u, r} Λ j
  let adj := derivedLowerShriekUnboundedAdjunction Λ j hΛ
  let _ := adj.rightAdjointCommShift ℤ
  let _ : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  exact ⟨inferInstance, adj.isTriangulated_rightAdjoint⟩

end Stacks.EtaleCohomology

end
