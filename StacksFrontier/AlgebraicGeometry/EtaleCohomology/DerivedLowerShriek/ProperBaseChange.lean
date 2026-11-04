module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BoundednessTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ExtensionByZeroTorsion
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedProperBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for `Rf_!`

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
`ḡ' : X̄' ⟶ X̄`. Following [Stacks, Tag 0F7L], the base change map for `Rf_! = Rf̄_* ∘ j_!` is the
composite
```
g⁻¹ ∘ Rf̄_* ∘ j_! ⟶ Rf̄'_* ∘ (ḡ')⁻¹ ∘ j_! ≅ Rf̄'_* ∘ j'_! ∘ (g')⁻¹
```
of the base change map of the square `f̄', ḡ', f̄, g` and the inverse of the isomorphism
`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroBaseChangeIso` exchanging extension by
zero and inverse image.

## Main definitions

* `Stacks.EtaleCohomology.derivedLowerShriekBaseChange`: the base change map
  `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹`.
* `Stacks.EtaleCohomology.derivedLowerShriekBaseChangeIso`: [Stacks, Tag 0F7L], the isomorphism
  `g⁻¹ ∘ Rf_! ≅ Rf'_! ∘ (g')⁻¹` on `D⁺_tors`.
* `Stacks.EtaleCohomology.compactlySupportedCohomologyBaseChangeIso`: [Stacks, Tag 0GK0], for a
  base change to a field `Spec k ⟶ Y`, `RΓ(Spec k, g⁻¹ Rf_! K) ≅ RΓ_c(X_k, (g')⁻¹ K)`.

## Main results

* `Stacks.EtaleCohomology.isIso_derivedLowerShriekBaseChange_app`: the base change map is
  invertible on `D⁺_tors`, by proper base change for sheaves of modules ([Stacks, Tag 0DDE]).
* `Stacks.EtaleCohomology.isTorsionPlus_etaleModuleDerivedExtensionByZero_obj`: derived extension
  by zero preserves `D⁺_tors`.

## References

* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
* [Stacks Project, Tag 0GK0](https://stacks.math.columbia.edu/tag/0GK0)
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

/-- **The base change map for `Rf_!`** ([Stacks, Tag 0F7L]): for a cartesian square
`f' ≫ g = g' ≫ f` and a compactification `j` of `X` over `Y`, the map
`g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹`, where `Rf'_!` is computed with the base change of `j`. It is
`g⁻¹ Rf̄_* j_! ⟶ Rf̄'_* (ḡ')⁻¹ j_!`, the base change map of the square of the compactifications,
followed by the inverse of `Rf̄'_*` applied to `j'_! (g')⁻¹ ≅ (ḡ')⁻¹ j_!`. -/
def derivedLowerShriekBaseChange :
    derivedLowerShriek.{u, r} f j Λ ⋙ etaleModuleDerivedInverseImagePlus.{u, r} Λ g ⟶
      etaleModuleDerivedInverseImagePlus.{u, r} Λ g' ⋙
        derivedLowerShriek.{u, r} f' (j.baseChange sq) Λ :=
  Functor.whiskerLeft (etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion)
      (etaleModuleDerivedBaseChange.{u, r} Λ j.toBase (pullback.snd j.toBase g) g
        (pullback.fst j.toBase g) pullback.condition.symm) ≫
    Functor.whiskerRight (etaleModuleDerivedExtensionByZeroBaseChangeIso.{u, r} Λ sq j).inv
      (etaleModuleDerivedDirectImage.{u, r} Λ (pullback.snd j.toBase g))

/-- **Derived extension by zero preserves `D⁺_tors`.** For an étale `j : U ⟶ X` and `K` in
`D⁺(U_étale, Λ)` with torsion cohomology sheaves, `Rj_! K` has torsion cohomology sheaves:
extension by zero is exact, so `H^q(Rj_! K) = j_! H^q(K)`, and `j_!` of a torsion sheaf is
torsion (`Stacks.EtaleCohomology.isTorsionEtaleModule_etaleModuleExtensionByZero_obj`). -/
theorem isTorsionPlus_etaleModuleDerivedExtensionByZero_obj (Λ : Type) [Ring Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ U))
    (hK : isTorsionPlus.{u, 0} Λ U K) :
    isTorsionPlus.{u, 0} Λ X ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j).obj K) := by
  intro q
  let E := etaleModuleExtensionByZero.{u, 0} Λ j
  let e₁ := (DerivedCategory.Plus.homologyFunctor _ q).mapIso
    ((Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus E).app K)
  let e₂ : (DerivedCategory.Plus.homologyFunctor _ q).obj (E.mapDerivedCategoryPlus.obj K) ≅
      E.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K) :=
    (Stacks.Homology.derivedHomologyIso E q).app (DerivedCategory.Plus.ι.obj K)
  exact IsTorsionEtaleModule.of_iso Λ X (e₁ ≪≫ e₂).symm
    (isTorsionEtaleModule_etaleModuleExtensionByZero_obj Λ j _ (hK q))

section Iso

variable (Λ : Type) [Ring Λ] {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X}
  {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g) (j : CompactificationOf (Over.mk f))

/-- **The base change map for `Rf_!` is invertible on `D⁺_tors`** ([Stacks, Tag 0F7L]). For a
cartesian square and `K ∈ D⁺(X_étale, Λ)` with torsion cohomology sheaves, the base change map
`g⁻¹ Rf_! K ⟶ Rf'_! (g')⁻¹ K` is an isomorphism: its first factor is proper base change for
`f̄` ([Stacks, Tag 0DDE], `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_of_isProper`)
at `Rj_! K`, which has torsion cohomology sheaves, and its second factor is `Rf̄'_*` of an
isomorphism. -/
theorem isIso_derivedLowerShriekBaseChange_app (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : isTorsionPlus.{u, 0} Λ X K) :
    IsIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K) :=
  IsIso.comp_isIso' (isIso_etaleModuleDerivedBaseChange_of_isProper Λ j.toBase
      (IsPullback.of_hasPullback j.toBase g) _
      (isTorsionPlus_etaleModuleDerivedExtensionByZero_obj Λ j.immersion K hK))
    (Functor.map_isIso (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd j.toBase g))
      ((etaleModuleDerivedExtensionByZeroBaseChangeIso.{u, 0} Λ sq j).inv.app K))

/-- **Stacks Project, Tag 0F7L.** For a cartesian square of schemes `f' ≫ g = g' ≫ f` and a
compactification `j` of `X` over `Y`, the canonical isomorphism `g⁻¹ ∘ Rf_! ≅ Rf'_! ∘ (g')⁻¹` of
functors on `D⁺_tors(X_étale, Λ)`, the bounded below complexes with torsion cohomology sheaves,
`Rf'_!` being computed with the base change of `j`
(`AlgebraicGeometry.CompactificationOf.baseChange`). Its components are
`Stacks.EtaleCohomology.derivedLowerShriekBaseChange`. -/
@[stacks 0F7L "the isomorphism g⁻¹ ∘ Rf_! ≅ Rf'_! ∘ (g')⁻¹ on D⁺_tors"]
def derivedLowerShriekBaseChangeIso :
    (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} f j Λ ⋙
        etaleModuleDerivedInverseImagePlus.{u, 0} Λ g ≅
      (isTorsionPlus.{u, 0} Λ X).ι ⋙ etaleModuleDerivedInverseImagePlus.{u, 0} Λ g' ⋙
        derivedLowerShriek.{u, 0} f' (j.baseChange sq) Λ :=
  haveI : ∀ K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory,
      IsIso ((Functor.whiskerLeft (isTorsionPlus.{u, 0} Λ X).ι
        (derivedLowerShriekBaseChange.{u, 0} Λ sq j)).app K) :=
    fun K => isIso_derivedLowerShriekBaseChange_app Λ sq j K.obj K.property
  haveI := NatIso.isIso_of_isIso_app
    (Functor.whiskerLeft (isTorsionPlus.{u, 0} Λ X).ι (derivedLowerShriekBaseChange.{u, 0} Λ sq j))
  asIso (Functor.whiskerLeft (isTorsionPlus.{u, 0} Λ X).ι
    (derivedLowerShriekBaseChange.{u, 0} Λ sq j))

/-- The components of `Stacks.EtaleCohomology.derivedLowerShriekBaseChangeIso` are the base change
maps `Stacks.EtaleCohomology.derivedLowerShriekBaseChange`. -/
@[simp]
theorem derivedLowerShriekBaseChangeIso_hom_app (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekBaseChangeIso Λ sq j).hom.app K =
      (derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K.obj :=
  rfl

/-- **Stacks Project, Tag 0GK0**, the cohomology form, for a base change to a field. For a
cartesian square of schemes with `Y' = Spec k` (for instance a geometric point
`ȳ : Spec k ⟶ Y`, `k` separably closed), a compactification `j` of `X` over `Y` and
`K ∈ D⁺_tors(X_étale, Λ)`: `RΓ(Spec k, g⁻¹ Rf_! K)`, which for `k` separably closed is the stalk
`(Rf_! K)_ȳ`, is the compactly supported cohomology `RΓ_c(X', (g')⁻¹ K)` of the fibre
`X' = X ×_Y Spec k`, computed with the base change of `j`. -/
@[stacks 0GK0 "(Rf_! K)_ȳ ≅ RΓ_c(X_ȳ, K|_{X_ȳ}), with (Rf_! K)_ȳ = RΓ(Spec k, ȳ⁻¹ Rf_! K)",
  sga "4 XVIII 0.1" "special case",
  sga "4½ Arcata 4.5.4" "more general"]
def compactlySupportedCohomologyBaseChangeIso {k : Type u} [Field k] {X Y X' : Scheme.{u}}
    {f : X ⟶ Y} {g : Spec (.of k) ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of k)}
    [LocallyOfFiniteType f'] [QuasiCompact f'] [IsSeparated f'] (sq : IsPullback g' f' f g)
    (j : CompactificationOf (Over.mk f)) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : isTorsionPlus.{u, 0} Λ X K) :
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of k))).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).obj
          ((derivedLowerShriek.{u, 0} f j Λ).obj K)) ≅
      (compactlySupportedCohomology.{u, 0} k f' (j.baseChange sq) Λ).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g').obj K) :=
  (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of k))).mapIso
    (haveI := isIso_derivedLowerShriekBaseChange_app Λ sq j K hK
     asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K))

/-- **Stacks Project, Tag 0GK0, on cohomology modules.** Under the hypotheses of
`Stacks.EtaleCohomology.compactlySupportedCohomologyBaseChangeIso`, for every `q`,
`H^q(RΓ(Spec k, g⁻¹ Rf_! K)) ≅ H^q_c(X', (g')⁻¹ K)`. -/
def compactlySupportedCohomologyGroupBaseChangeIso {k : Type u} [Field k] {X Y X' : Scheme.{u}}
    {f : X ⟶ Y} {g : Spec (.of k) ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of k)}
    [LocallyOfFiniteType f'] [QuasiCompact f'] [IsSeparated f'] (sq : IsPullback g' f' f g)
    (j : CompactificationOf (Over.mk f)) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : isTorsionPlus.{u, 0} Λ X K) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).obj
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of k))).obj
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).obj
            ((derivedLowerShriek.{u, 0} f j Λ).obj K))) ≅
      (compactlySupportedCohomologyGroup.{u, 0} k f' (j.baseChange sq) Λ q).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g').obj K) :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) q).mapIso
    (compactlySupportedCohomologyBaseChangeIso Λ sq j K hK)

end Iso

end Stacks.EtaleCohomology

end
