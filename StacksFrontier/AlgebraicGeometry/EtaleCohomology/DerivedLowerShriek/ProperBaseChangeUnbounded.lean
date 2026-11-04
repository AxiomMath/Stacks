module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperBaseChangeUnbounded

/-!
# Base change for `Rf_!` on unbounded derived categories

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes, `j : X ⟶ X̄` a compactification of `X` over `Y` with structure
morphism `f̄ : X̄ ⟶ Y`, and `j' : X' ⟶ X̄' = X̄ ×_Y Y'` its base change
(`AlgebraicGeometry.CompactificationOf.baseChange`), with projections `f̄' : X̄' ⟶ Y'` and
`ḡ' : X̄' ⟶ X̄`. Following [Stacks, Tag 0F7L], the base change map for `Rf_! = Rf̄_* ∘ Rj_!` on
the unbounded derived categories `D(X_étale, Λ)` is the composite
```
g⁻¹ ∘ Rf̄_* ∘ Rj_! ⟶ Rf̄'_* ∘ (ḡ')⁻¹ ∘ Rj_! ≅ Rf̄'_* ∘ Rj'_! ∘ (g')⁻¹
```
of the unbounded base change map of the square `f̄', ḡ', f̄, g` and the inverse of the
isomorphism exchanging extension by zero and inverse image. When `Λ` is torsion the first arrow
is invertible by the unbounded proper base change theorem ([Stacks, Tag 0F0C]), so the composite
is an isomorphism. This is the counterpart on `D(X_étale, Λ)` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedLowerShriek/ProperBaseChange.lean`, which
treats `D⁺_tors(X_étale, Λ)`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnboundedBaseChangeIso`: the
  isomorphism `(g')⁻¹ ⋙ Rj'_! ≅ Rj_! ⋙ (ḡ')⁻¹` on unbounded derived categories.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChange`: the base change map
  `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` on `D(X_étale, Λ)`.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChangeIso`: the isomorphism
  `g⁻¹ ∘ Rf_! ≅ Rf'_! ∘ (g')⁻¹` on `D(X_étale, Λ)` for a torsion ring `Λ`.

## Main results

* `Stacks.EtaleCohomology.isIso_derivedLowerShriekUnboundedBaseChange_app`: the base change map
  is invertible on `D(X_étale, Λ)` when `Λ` is torsion.

## References

* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
* [Stacks Project, Tag 0F0C](https://stacks.math.columbia.edu/tag/0F0C)
* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [Ring Λ] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g) (j : CompactificationOf (Over.mk f))

/-- **Extension by zero commutes with inverse image across the base change of a compactification,
on unbounded derived categories** ([Stacks, Tag 03S6]): `(g')⁻¹ ⋙ Rj'_! ≅ Rj_! ⋙ (ḡ')⁻¹` on
`D(X_étale, Λ)`, for `j'` the immersion of `AlgebraicGeometry.CompactificationOf.baseChange` and
`ḡ'` the projection `X̄ ×_Y Y' ⟶ X̄`. Both extensions by zero are computed degreewise
(`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnboundedIso`), so this is the
underived isomorphism `Stacks.EtaleCohomology.etaleModuleInverseImageExtensionByZeroIso` read on
derived categories. -/
def etaleModuleDerivedExtensionByZeroUnboundedBaseChangeIso :
    (etaleModuleInverseImage.{u, r} Λ g').mapDerivedCategory ⋙
        etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ
          (CompactificationOf.baseChangeImmersion sq j) ≅
      etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion ⋙
        (etaleModuleInverseImage.{u, r} Λ (pullback.fst j.toBase g)).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ _) ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ
        (CompactificationOf.isPullback_baseChangeImmersion sq j)) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ _).symm _

section Map

variable (Λ : Type r) [CommRing Λ] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g) (j : CompactificationOf (Over.mk f))

/-- **The base change map for `Rf_!` on unbounded derived categories** ([Stacks, Tag 0F7L]): for
a cartesian square `f' ≫ g = g' ≫ f` and a compactification `j` of `X` over `Y`, the map
`g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of functors on `D(X_étale, Λ)`, where `Rf'_!` is computed with the
base change of `j`. It is `g⁻¹ Rf̄_* Rj_! ⟶ Rf̄'_* (ḡ')⁻¹ Rj_!`, the unbounded base change map
`Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded` of the square of the
compactifications, followed by `Rf̄'_*` of the inverse of
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnboundedBaseChangeIso`. -/
def derivedLowerShriekUnboundedBaseChange :
    derivedLowerShriekUnbounded.{u, r} f j Λ ⋙ etaleModuleDerivedInverseImage.{u, r} Λ g ⟶
      etaleModuleDerivedInverseImage.{u, r} Λ g' ⋙
        derivedLowerShriekUnbounded.{u, r} f' (j.baseChange sq) Λ :=
  Functor.whiskerLeft (etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion)
      (etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ j.toBase g (pullback.fst j.toBase g)
        (pullback.snd j.toBase g) pullback.condition) ≫
    Functor.whiskerRight (etaleModuleDerivedExtensionByZeroUnboundedBaseChangeIso.{u, r} Λ sq j).inv
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (pullback.snd j.toBase g))

/-- The base change map for `Rf_!` is invertible at `K` as soon as the base change map of the
square of the compactifications is invertible at `Rj_! K`: its second factor is `Rf̄'_*` of an
isomorphism. -/
theorem isIso_derivedLowerShriekUnboundedBaseChange_app_of_isIso
    (K : DerivedCategory (EtaleModules.{u, r} Λ X))
    (hK : IsIso ((etaleModuleDerivedBaseChangeUnbounded.{u, r} Λ j.toBase g
      (pullback.fst j.toBase g) (pullback.snd j.toBase g) pullback.condition).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).obj K))) :
    IsIso ((derivedLowerShriekUnboundedBaseChange.{u, r} Λ sq j).app K) :=
  IsIso.comp_isIso' hK
    (Functor.map_isIso (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (pullback.snd j.toBase g))
      ((etaleModuleDerivedExtensionByZeroUnboundedBaseChangeIso.{u, r} Λ sq j).inv.app K))

end Map

section Iso

variable (Λ : Type) [CommRing Λ] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
  (j : CompactificationOf (Over.mk f))

include hΛ in
/-- **The base change map for `Rf_!` is invertible on `D(X_étale, Λ)` for a torsion ring `Λ`**
([Stacks, Tag 0F7L], the unbounded case): its first factor is the unbounded proper base change
for `f̄` ([Stacks, Tag 0F0C],
`Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isProper`) at
`Rj_! K`, and its second factor is `Rf̄'_*` of an isomorphism. -/
theorem isIso_derivedLowerShriekUnboundedBaseChange_app
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    IsIso ((derivedLowerShriekUnboundedBaseChange.{u, 0} Λ sq j).app K) :=
  isIso_derivedLowerShriekUnboundedBaseChange_app_of_isIso Λ sq j K
    (isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isProper Λ hΛ j.toBase
      (IsPullback.of_hasPullback j.toBase g) _)

/-- **The isomorphism `g⁻¹ ∘ Rf_! ≅ Rf'_! ∘ (g')⁻¹` on `D(X_étale, Λ)` for a torsion ring `Λ`**
([Stacks, Tag 0F7L], the unbounded case), for a cartesian square of schemes and a
compactification `j` of `X` over `Y`, `Rf'_!` being computed with the base change of `j`. Its
components are `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChange`. -/
def derivedLowerShriekUnboundedBaseChangeIso :
    derivedLowerShriekUnbounded.{u, 0} f j Λ ⋙ etaleModuleDerivedInverseImage.{u, 0} Λ g ≅
      etaleModuleDerivedInverseImage.{u, 0} Λ g' ⋙
        derivedLowerShriekUnbounded.{u, 0} f' (j.baseChange sq) Λ :=
  haveI : ∀ K, IsIso ((derivedLowerShriekUnboundedBaseChange.{u, 0} Λ sq j).app K) :=
    isIso_derivedLowerShriekUnboundedBaseChange_app Λ hΛ sq j
  haveI := NatIso.isIso_of_isIso_app (derivedLowerShriekUnboundedBaseChange.{u, 0} Λ sq j)
  asIso (derivedLowerShriekUnboundedBaseChange.{u, 0} Λ sq j)

/-- The components of `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChangeIso` are the
base change maps `Stacks.EtaleCohomology.derivedLowerShriekUnboundedBaseChange`. -/
@[simp]
theorem derivedLowerShriekUnboundedBaseChangeIso_hom_app
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedBaseChangeIso Λ hΛ sq j).hom.app K =
      (derivedLowerShriekUnboundedBaseChange.{u, 0} Λ sq j).app K :=
  rfl

end Iso

end Stacks.EtaleCohomology

end
