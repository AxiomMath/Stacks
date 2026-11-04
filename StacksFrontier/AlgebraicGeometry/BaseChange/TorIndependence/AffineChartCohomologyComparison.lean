module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartComparisonMap
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkLocalizationCriterion
public import StacksCore.Tactic.StacksAttribute

/-!
# The chart comparison of a base-change square, degree by degree

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes and let `ch` be a Cartesian affine-open chart for it, with
coordinate rings `R = 𝒪_S(V)`, `A = 𝒪_X(U)`, `R' = 𝒪_{S'}(V')` and
`A' = 𝒪_{X'}(U') = A ⊗_R R'`.  Given `K ∈ D(𝒪_X)`, `K' ∈ D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`,
`AlgebraicGeometry.BaseChangeChart.comparison` is the morphism

```
RΓ(U,K) ⊗ᴸ_R R' ⟶ RΓ(U',K')
```

of `D(R')` whose invertibility is condition (2) of Stacks 0DJ8.  This module reads that one
morphism of the derived category as a family of maps of modules, one in each degree: the
degree-`n` member is the `A'`-linear map

```
A' ⊗_{A ⊗_R R'} H^n(RΓ(U,K) ⊗ᴸ_R R') ⟶ H^n(RΓ(U',K'))
```

of Stacks 0DJ7's ring form, `RingTheory.TorIndependence.exists_unique_ringBaseChangeCohomologyMap`
for the chart's pushout square of rings, and condition (2) at the chart is exactly invertibility
of all of them — equivalently, of all of their localizations at the primes of `A'`, that is, of
their germs at the points of `U'`.

## Main definitions

* `RingTheory.TorIndependence.ringDerivedBaseChangeComparison`: the derived base-change
  comparison of Stacks 065Z for a commutative square of rings, followed by the given morphism —
  the shape of which `AlgebraicGeometry.BaseChangeChart.comparison` is an instance.
* `RingTheory.TorIndependence.ringCohomologyComparison`: the degree-`n` `A'`-linear map of
  Stacks 0DJ7's ring form attached to `ringDerivedBaseChangeComparison`.
* `AlgebraicGeometry.BaseChangeChart.cohomologyComparison`: the same for a chart, the degree-`n`
  reading of the chart comparison.

## Main results

* `RingTheory.TorIndependence.ringCohomologyComparison_tmul_one`: the defining formula, that
  the degree-`n` map sends `1 ⊗ m` to `H^n(ringDerivedBaseChangeComparison)` of `m`.
* `RingTheory.TorIndependence.isIso_ringDerivedBaseChangeComparison_iff`: over a pushout square
  of rings the comparison is invertible exactly when all of its degree-`n` maps are.
* `AlgebraicGeometry.BaseChangeChart.comparison_eq_ringDerivedBaseChangeComparison`: the chart
  comparison is an instance of `ringDerivedBaseChangeComparison`, for the chart's pushout square
  of rings.
* `AlgebraicGeometry.BaseChangeChart.cohomologyComparison_tmul_one`: the degree-`n` map of a
  chart sends `1 ⊗ m` to `H^n` of the chart comparison.
* `AlgebraicGeometry.BaseChangeChart.isIso_comparison_iff_forall_isIso_cohomologyComparison`:
  **condition (2) of Stacks 0DJ8 at a chart, degree by degree.**
* `AlgebraicGeometry.BaseChangeChart.isIso_comparison_iff_forall_localized`: the same condition
  read at the primes of `A'`, one localization of one degree-`n` map at a time.

## Implementation notes

The square of rings of a chart is a square of `CommRingCat` morphisms, while the ring-level
statements are stated for `Algebra` structures and `algebraMap`s. The chart's algebra and
scalar-tower instances are given by `RingHom.toAlgebra`, which makes `algebraMap R A` the
chart's `a` by definition, and are spelled out locally at each declaration.

The ring-level statements take `[HasDerivedCategory.{w} ·]` for the four rings as binders.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)
open scoped TensorProduct
open scoped ChangeOfRings

universe u w

namespace RingTheory.TorIndependence

/-! ### The comparison of a square of rings, and its degreewise reading -/

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]

/-- The base-change comparison of a commutative square of rings, followed by a morphism:
for `K ∈ D(A)`, `K' ∈ D(A')` and `φ : K ⊗ᴸ_A A' ⟶ K'`, the composition

`K ⊗ᴸ_R R' ⟶ (K ⊗ᴸ_A A')|_{R'} ⟶ K'|_{R'}`

in `D(R')`, whose first arrow is `derivedBaseChangeComparison`. -/
public abbrev ringDerivedBaseChangeComparison
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj K ⟶ K') :
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.obj
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) ⟶
      (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.obj K' :=
  let Tg := totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')
  let Th := totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')
  let sq : (algebraMap A A').comp (algebraMap R A) = (algebraMap R' A').comp (algebraMap R R') :=
    (IsScalarTower.algebraMap_eq R A A').symm.trans (IsScalarTower.algebraMap_eq R R' A')
  let τ := (@derivedBaseChangeComparison.{u, u, u, u, u, w, w, w, w} R A R' A' _ _ _ _ _ _ _ _
    (algebraMap R A) (algebraMap R R') (algebraMap A A') (algebraMap R' A') sq
    Tg.functor Th.functor Tg.comparison Th.comparison Tg.isLeftDerived Th.isLeftDerived).2.1
  τ.app K ≫ (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map φ

/-- The degree-`n` reading of `ringDerivedBaseChangeComparison`: the unique `A'`-linear map
`A' ⊗_{A ⊗_R R'} H^n(K ⊗ᴸ_R R') ⟶ H^n(K')` whose value on `1 ⊗ m` is
`H^n(ringDerivedBaseChangeComparison)` of `m`. -/
public abbrev ringCohomologyComparison
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj K ⟶ K')
    (n : ℤ) :=
  Classical.choose
    (exists_unique_ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n).exists

/-- The defining formula of `ringCohomologyComparison`: on `1 ⊗ m` it is `H^n` of
`ringDerivedBaseChangeComparison`, read through the identification of the cohomology of a complex
of `A'`-modules with the cohomology of its restriction to `R'`. -/
public theorem ringCohomologyComparison_tmul_one
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj K ⟶ K')
    (n : ℤ) (m : baseChangeCohomology (R := R) (R' := R') K n) :
    let B := A ⊗[R] R'
    let k : B →+* A' :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R A A')
        (IsScalarTower.toAlgHom R R' A') (fun _ _ => Commute.all _ _)).toRingHom
    (ringCohomologyComparison (R := R) (R' := R') K K' φ n).hom
        ((1 : A') ⊗ₜ[B, k] m) =
      (((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryHomologyIso
          n).app K').hom.hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
          (ringDerivedBaseChangeComparison (R := R) (R' := R') K K' φ)).hom m) :=
  Classical.choose_spec
    (exists_unique_ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n).exists m

/-- A morphism out of an extension of scalars along a ring isomorphism is invertible exactly
when its adjoint is bijective on the pure tensors `1 ⊗ m`. -/
private theorem isIso_iff_bijective_tmul_one {Rr Ss : Type u} [CommRing Rr] [CommRing Ss]
    (e : Rr ≃+* Ss) {M : ModuleCat.{u} Rr} {N : ModuleCat.{u} Ss}
    (α : (ModuleCat.extendScalars e.toRingHom).obj M ⟶ N) :
    IsIso α ↔ Function.Bijective (fun m : M =>
      ((ModuleCat.extendRestrictScalarsAdj e.toRingHom).homEquiv M N α).hom m) := by
  let adj := ModuleCat.extendRestrictScalarsAdj e.toRingHom
  have : (ModuleCat.restrictScalars e.toRingHom).IsEquivalence := inferInstance
  have : IsIso (adj.unit.app M) := inferInstance
  rw [← isIso_iff_of_reflects_iso α (ModuleCat.restrictScalars e.toRingHom),
    ← isIso_comp_left_iff (adj.unit.app M)]
  show IsIso (adj.unit.app M ≫ (ModuleCat.restrictScalars e.toRingHom).map α) ↔ _
  exact ConcreteCategory.isIso_iff_bijective _

/-- A morphism of modules is invertible exactly when all of its localizations at primes, by
`ModuleCat.localizedModuleFunctor`, are. -/
private theorem isIso_iff_forall_isIso_localized {Rr : Type u} [CommRing Rr]
    {M N : ModuleCat.{u} Rr} (ψ : M ⟶ N) :
    IsIso ψ ↔ ∀ p : PrimeSpectrum Rr,
      IsIso ((ModuleCat.localizedModuleFunctor.{u} p.asIdeal.primeCompl).map ψ) := by
  rw [ConcreteCategory.isIso_iff_bijective,
    Stacks.StalkLocalization.bijective_iff_forall_bijective_localizedMap' ψ.hom]
  refine forall_congr' fun p => ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact Stacks.StalkLocalization.bijective_localizedModule_map_iff _ ψ.hom
    (M.localizedModuleMkLinearMap p.asIdeal.primeCompl)
    (N.localizedModuleMkLinearMap p.asIdeal.primeCompl)

/-- Over a pushout square of rings, `ringDerivedBaseChangeComparison` is invertible exactly
when the `A'`-linear map `ringCohomologyComparison` is invertible in every degree `n`. -/
public theorem isIso_ringDerivedBaseChangeComparison_iff [Algebra.IsPushout R A R' A']
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj K ⟶ K') :
    IsIso (ringDerivedBaseChangeComparison (R := R) (R' := R') K K' φ) ↔
      ∀ n : ℤ, IsIso (ringCohomologyComparison (R := R) (R' := R') K K' φ n) := by
  rw [DerivedCategory.isIso_iff]
  refine forall_congr' fun n => ?_
  let k : A ⊗[R] R' →+* A' :=
    (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R A A')
      (IsScalarTower.toAlgHom R R' A') (fun _ _ => Commute.all _ _)).toRingHom
  have hk : Function.Bijective k := by
    have he : k = (Algebra.IsPushout.equiv R A R' A').toRingEquiv.toRingHom := by
      ext a <;> simp [k, Algebra.IsPushout.equiv_tmul]
    rw [he]
    exact (Algebra.IsPushout.equiv R A R' A').bijective
  let e : A ⊗[R] R' ≃+* A' := RingEquiv.ofBijective k hk
  let H := baseChangeCohomology (R := R) (R' := R') K n
  let H' := (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K'
  let b : (ModuleCat.extendScalars k).obj H ⟶ H' :=
    ringCohomologyComparison (R := R) (R' := R') K K' φ n
  let α := (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
    (ringDerivedBaseChangeComparison (R := R) (R' := R') K K' φ)
  let e' := ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryHomologyIso
    n).app K'
  have hval : (fun m : H =>
      ((ModuleCat.extendRestrictScalarsAdj e.toRingHom).homEquiv H H' b).hom m) =
      fun m : H => e'.hom.hom (α.hom m) :=
    funext fun m => ringCohomologyComparison_tmul_one (R := R) (R' := R') K K' φ n m
  show IsIso α ↔ IsIso b
  refine Iff.trans ?_ (isIso_iff_bijective_tmul_one e b).symm
  rw [hval]
  have he' : Function.Bijective e'.hom.hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp (inferInstance : IsIso e'.hom)
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (he'.of_comp_iff' α.hom).symm

end RingTheory.TorIndependence

namespace AlgebraicGeometry.BaseChangeChart

/-! ### The chart comparison, degree by degree -/

open RingTheory.TorIndependence

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- The chart comparison in degree `n`: on a chart with coordinate rings `R`, `A`, `R'`, `A'`,
the `A'`-linear map

`A' ⊗_{A ⊗_R R'} H^n(RΓ(U,K) ⊗ᴸ_R R') ⟶ H^n(RΓ(U',K'))`

given by `ringCohomologyComparison` for the chart's pushout square of rings. -/
@[stacks 0DJ8 "the comparison map of (2) on a Cartesian affine-open chart, in degree n: the \
A'-linear map of Tag 0DJ7's ring form for the chart's pushout square of rings"]
public def cohomologyComparison (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') (n : ℤ) :=
  letI : Algebra ch.R ch.A := ch.a.hom.toAlgebra
  letI : Algebra ch.R ch.R' := ch.b.hom.toAlgebra
  letI : Algebra ch.R ch.A' := (ch.c.hom.comp ch.a.hom).toAlgebra
  letI : Algebra ch.A ch.A' := ch.c.hom.toAlgebra
  letI : Algebra ch.R' ch.A' := ch.d.hom.toAlgebra
  letI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower ch.R ch.R' ch.A' := IsScalarTower.of_algebraMap_eq' ch.isPushout_hom
  ringCohomologyComparison (R := ch.R) (R' := ch.R')
    ((affineDerivedSections ch.incU).obj K) ((affineDerivedSections ch.incU').obj K')
    (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) n

/-- The chart comparison is `ringDerivedBaseChangeComparison` for the chart's pushout square
of rings, with the given morphism `φ` folded into the second arrow. -/
public theorem comparison_eq_ringDerivedBaseChangeComparison (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') :
    letI : Algebra ch.R ch.A := ch.a.hom.toAlgebra
    letI : Algebra ch.R ch.R' := ch.b.hom.toAlgebra
    letI : Algebra ch.R ch.A' := (ch.c.hom.comp ch.a.hom).toAlgebra
    letI : Algebra ch.A ch.A' := ch.c.hom.toAlgebra
    letI : Algebra ch.R' ch.A' := ch.d.hom.toAlgebra
    letI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower ch.R ch.R' ch.A' := IsScalarTower.of_algebraMap_eq' ch.isPushout_hom
    ch.comparison K K' φ =
      ringDerivedBaseChangeComparison (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K) ((affineDerivedSections ch.incU').obj K')
        (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) := by
  dsimp only [comparison, pullbackComparison, ringDerivedBaseChangeComparison]
  rw [Functor.map_comp]
  exact Category.assoc _ _ _

/-- The degree-`n` map of a chart is `H^n` of the chart comparison: its value on `1 ⊗ m` is
`H^n(comparison)` of `m`, read through the identification of the cohomology of a complex of
`A'`-modules with the cohomology of its restriction to `R'`. -/
@[stacks 0DJ8 "the degree-n map of a chart is H^n of the comparison map of (2)"]
public theorem cohomologyComparison_tmul_one (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') (n : ℤ) :
    letI : Algebra ch.R ch.A := ch.a.hom.toAlgebra
    letI : Algebra ch.R ch.R' := ch.b.hom.toAlgebra
    letI : Algebra ch.R ch.A' := (ch.c.hom.comp ch.a.hom).toAlgebra
    letI : Algebra ch.A ch.A' := ch.c.hom.toAlgebra
    letI : Algebra ch.R' ch.A' := ch.d.hom.toAlgebra
    letI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower ch.R ch.R' ch.A' := IsScalarTower.of_algebraMap_eq' ch.isPushout_hom
    ∀ m : baseChangeCohomology (R := ch.R) (R' := ch.R')
      ((affineDerivedSections ch.incU).obj K) n,
      let B := ch.A ⊗[ch.R] ch.R'
      let k : B →+* ch.A' :=
        (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom ch.R ch.A ch.A')
          (IsScalarTower.toAlgHom ch.R ch.R' ch.A') (fun _ _ => Commute.all _ _)).toRingHom
      (ch.cohomologyComparison K K' φ n).hom ((1 : ch.A') ⊗ₜ[B, k] m) =
        (((ModuleCat.restrictScalars ch.d.hom).mapDerivedCategoryHomologyIso n).app
            ((affineDerivedSections ch.incU').obj K')).hom.hom
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} ch.R') n).map
            (ch.comparison K K' φ)).hom m) := by
  let : Algebra ch.R ch.A := ch.a.hom.toAlgebra
  let : Algebra ch.R ch.R' := ch.b.hom.toAlgebra
  let : Algebra ch.R ch.A' := (ch.c.hom.comp ch.a.hom).toAlgebra
  let : Algebra ch.A ch.A' := ch.c.hom.toAlgebra
  let : Algebra ch.R' ch.A' := ch.d.hom.toAlgebra
  let : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower ch.R ch.R' ch.A' := IsScalarTower.of_algebraMap_eq' ch.isPushout_hom
  intro m
  rw [ch.comparison_eq_ringDerivedBaseChangeComparison K K' φ]
  exact ringCohomologyComparison_tmul_one (R := ch.R) (R' := ch.R')
    ((affineDerivedSections ch.incU).obj K) ((affineDerivedSections ch.incU').obj K')
    (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) n m

/-- The chart comparison

`RΓ(U,K) ⊗ᴸ_{𝒪_S(V)} 𝒪_{S'}(V') ⟶ RΓ(U',K')`

is an isomorphism exactly when, in every degree `n`, the `A'`-linear map

`A' ⊗_{A ⊗_R R'} H^n(RΓ(U,K) ⊗ᴸ_R R') ⟶ H^n(RΓ(U',K'))`

of the chart's pushout square of rings is. -/
@[stacks 0DJ8 "condition (2) at a Cartesian affine-open chart, read degree by degree: the chart \
comparison is invertible exactly when the A'-linear base-change maps on cohomology of the \
chart's pushout square of rings are invertible in every degree"]
public theorem isIso_comparison_iff_forall_isIso_cohomologyComparison
    (ch : BaseChangeChart f g f' g') (K : DerivedCategory X.Modules)
    (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') :
    IsIso (ch.comparison K K' φ) ↔
      ∀ n : ℤ, IsIso (ch.cohomologyComparison K K' φ n) := by
  let : Algebra ch.R ch.A := ch.a.hom.toAlgebra
  let : Algebra ch.R ch.R' := ch.b.hom.toAlgebra
  let : Algebra ch.R ch.A' := (ch.c.hom.comp ch.a.hom).toAlgebra
  let : Algebra ch.A ch.A' := ch.c.hom.toAlgebra
  let : Algebra ch.R' ch.A' := ch.d.hom.toAlgebra
  let : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower ch.R ch.R' ch.A' := IsScalarTower.of_algebraMap_eq' ch.isPushout_hom
  let : Algebra.IsPushout ch.R ch.A ch.R' ch.A' :=
    CommRingCat.isPushout_iff_isPushout.mp ch.isPushout
  rw [ch.comparison_eq_ringDerivedBaseChangeComparison K K' φ,
    isIso_ringDerivedBaseChangeComparison_iff]
  rfl

/-- The chart comparison is an isomorphism exactly when, at every prime `y` of
`A' = 𝒪_{X'}(U')` (that is, at every point of `U'`) and in every degree `n`, the localization at
`y` of the degree-`n` map of the chart is an isomorphism. -/
@[stacks 0DJ8 "condition (2) at a Cartesian affine-open chart is a pointwise condition on the \
points of U': invertibility of the localization at each prime of A' of each degree-n map"]
public theorem isIso_comparison_iff_forall_localized (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') :
    IsIso (ch.comparison K K' φ) ↔
      ∀ (y : PrimeSpectrum ch.A') (n : ℤ),
        IsIso ((ModuleCat.localizedModuleFunctor.{u} y.asIdeal.primeCompl).map
          (ch.cohomologyComparison K K' φ n)) :=
  ((ch.isIso_comparison_iff_forall_isIso_cohomologyComparison K K' φ).trans
    (forall_congr' fun _ => isIso_iff_forall_isIso_localized _)).trans forall_comm

end AlgebraicGeometry.BaseChangeChart

end
