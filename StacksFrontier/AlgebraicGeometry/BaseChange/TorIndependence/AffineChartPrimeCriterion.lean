module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartComparisonMap
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapConstructionGeneral
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkLocalizationCriterion

/-!
# The prime-local form of the chart comparison of Stacks 0DJ8

For a commutative square of rings `R → A`, `R → R'`, `A → A'`, `R' → A'`, an object `K` of
`D(A)`, an object `K'` of `D(A')` and `φ : K ⊗ᴸ_A A' ⟶ K'`, the composition

`K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A A' ⟶ K'`

is a morphism of `D(R')`. It is an isomorphism exactly when each of its cohomology maps is
bijective, and each of those is a map of `A ⊗_R R'`-modules, so bijectivity is detected at the
primes of `A ⊗_R R'` by the local criterion [Stacks, Tag 00HN]. Applied to a Cartesian
affine-open chart, this turns invertibility of the chart comparison into a condition at the
primes of the chart's coordinate ring.

## Main results

* `RingTheory.TorIndependence.bijective_cohomologyComparisonLinearMap_iff`: the cohomology map is
  bijective exactly when `H^n` of the comparison is invertible.
* `RingTheory.TorIndependence.isIso_ringComparison_iff`: the comparison is invertible exactly
  when every cohomology map is bijective after localizing at every prime of `A ⊗_R R'`.
* `RingTheory.TorIndependence.isIso_ringComparison_iff_forall_isIso`: over a pushout square the
  comparison is invertible exactly when the ring-level map of Stacks 0DJ7 is invertible in every
  degree.
* `BaseChangeChart.comparison_eq_ringComparison`: the chart comparison of Stacks 0DJ8 (2) is the
  ring-level comparison of the chart's square of coordinate rings.
* `BaseChangeChart.isIso_comparison_iff`: condition (2) at a chart, read at the primes of
  `𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V')`.
* `BaseChangeChart.isIso_comparison_iff_forall_isIso_ringBaseChangeCohomologyMap`: condition (2) at
  a chart is invertibility, in every degree, of the ring-level map of Stacks 0DJ7 for the chart's
  rings.

## References

* [Stacks Project, Tag 00HN](https://stacks.math.columbia.edu/tag/00HN)
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
open scoped TensorProduct
open scoped ChangeOfRings

universe u w

namespace RingTheory.TorIndependence

section Ring

variable {R A R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]

omit [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')] in
/-- **The canonical map `A ⊗_R R' → A'` is bijective when the square of rings is a pushout.**
It agrees with `Algebra.IsPushout.equiv` on pure tensors. -/
theorem bijective_baseChangeTensorRingMap [Algebra.IsPushout R A R' A'] :
    Function.Bijective
      (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')) := by
  have he : ∀ x : A ⊗[R] R',
      baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A') x =
        Algebra.IsPushout.equiv R A R' A' x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b =>
      rw [Algebra.IsPushout.equiv_tmul]
      change (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R A A')
        (IsScalarTower.toAlgHom R R' A') (fun _ _ => Commute.all _ _)) (a ⊗ₜ b) = _
      rw [Algebra.TensorProduct.lift_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact funext he ▸ (Algebra.IsPushout.equiv R A R' A').bijective

/-- **The unit `m ↦ 1 ⊗ m` of the extension-restriction adjunction along a bijective ring map is
bijective.** Its inverse sends `c ⊗ m` to `k⁻¹(c) • m`. -/
private lemma bijective_one_tmul {B C : Type u} [CommRing B] [CommRing C] (k : B →+* C)
    (hk : Function.Bijective k) (H : ModuleCat.{u} B) :
    Function.Bijective (fun m : H =>
      ((1 : C) ⊗ₜ[B, k] m : (ModuleCat.extendScalars k).obj H)) := by
  let : Module B C := Module.compHom C k
  let e : B ≃+* C := RingEquiv.ofBijective k hk
  let esl : C →ₗ[B] B :=
    { toFun := fun c => e.symm c
      map_add' := fun c₁ c₂ => map_add e.symm c₁ c₂
      map_smul' := fun b c => by
        change e.symm (k b * c) = b * e.symm c
        rw [map_mul]
        congr 1
        exact e.symm_apply_apply b }
  let ψ : TensorProduct B C H →ₗ[B] H := TensorProduct.lift (LinearMap.lsmul B H ∘ₗ esl)
  have hψ1 : ∀ m : H, ψ ((1 : C) ⊗ₜ[B, k] m) = m := by
    intro m
    change ψ ((1 : C) ⊗ₜ m) = m
    rw [TensorProduct.lift.tmul]
    change (e.symm (1 : C)) • m = m
    rw [map_one, one_smul]
  have h2 : ∀ t : TensorProduct B C H, ((1 : C) ⊗ₜ[B, k] (ψ t)) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, TensorProduct.tmul_zero]
    | tmul c m =>
      rw [TensorProduct.lift.tmul]
      change ((1 : C) ⊗ₜ[B, k] (e.symm c • m)) = c ⊗ₜ m
      rw [← TensorProduct.smul_tmul]
      congr 1
      change k (e.symm c) * (1 : C) = c
      rw [mul_one]
      exact e.apply_symm_apply c
    | add x y hx hy => rw [map_add, TensorProduct.tmul_add, hx, hy]
  exact ⟨Function.LeftInverse.injective hψ1, fun t => ⟨ψ t, h2 t⟩⟩

/-- A map that factors through a bijection is bijective exactly when its other factor is. -/
private lemma bijective_iff_outer_of_bijective_inner {M N P : Type*}
    (fm : M → P) (gm : M → N) (en : N → P) (hg : Function.Bijective gm)
    (h : ∀ m, fm m = en (gm m)) :
    Function.Bijective fm ↔ Function.Bijective en := by
  rw [show fm = en ∘ gm from funext h]
  exact Function.Bijective.of_comp_iff en hg

/-- A map that factors as a bijection after a second map is bijective exactly when that second
map is. -/
private lemma bijective_iff_inner_of_bijective_outer {M N P : Type*}
    (fm : M → P) (gm : M → N) (em : N → P) (he : Function.Bijective em)
    (h : ∀ m, fm m = em (gm m)) :
    Function.Bijective fm ↔ Function.Bijective gm := by
  rw [show fm = em ∘ gm from funext h]
  exact Function.Bijective.of_comp_iff' he gm

/-- **The cohomology map is bijective exactly when the cohomology of the comparison is
invertible.** The two differ by the isomorphism identifying the cohomology of a restriction of
scalars with the restriction of scalars of the cohomology. -/
theorem bijective_cohomologyComparisonLinearMap_iff (K : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ) :
    Function.Bijective (cohomologyComparisonLinearMapGeneral (R := R) (R' := R') K K' φ n).hom ↔
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        (ringComparison (R := R) (R' := R') K K' φ)) := by
  refine Iff.trans (bijective_iff_inner_of_bijective_outer
    (fm := ⇑(cohomologyComparisonLinearMapGeneral (R := R) (R' := R') K K' φ n).hom)
    (gm := ⇑((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
      (ringComparison (R := R) (R' := R') K K' φ)).hom)
    (em := ⇑(((ModuleCat.restrictScalars (algebraMap R' A')
      ).mapDerivedCategoryHomologyIso n).hom.app K').hom)
    ((ConcreteCategory.isIso_iff_bijective
      (f := ((ModuleCat.restrictScalars (algebraMap R' A')
        ).mapDerivedCategoryHomologyIso n).hom.app K')).mp inferInstance)
    (cohomologyComparisonLinearMapGeneral_apply (R := R) (R' := R') K K' φ n))
    (ConcreteCategory.isIso_iff_bijective
      (f := (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        (ringComparison (R := R) (R' := R') K K' φ))).symm

/-- **The ring-level comparison is invertible exactly when its cohomology maps are bijective at
every prime of `A ⊗_R R'`.** -/
theorem isIso_ringComparison_iff (K : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') :
    IsIso (ringComparison (R := R) (R' := R') K K' φ) ↔
      ∀ (n : ℤ) (q : Ideal (A ⊗[R] R')) (_ : q.IsPrime),
        Function.Bijective (LocalizedModule.map q.primeCompl
          (cohomologyComparisonLinearMapGeneral (R := R) (R' := R') K K' φ n).hom) := by
  rw [DerivedCategory.isIso_iff]
  refine forall_congr' fun n => ?_
  rw [← bijective_cohomologyComparisonLinearMap_iff (R := R) (R' := R') K K' φ n,
    Stacks.StalkLocalization.bijective_iff_forall_bijective_localizedMap
      (cohomologyComparisonLinearMapGeneral (R := R) (R' := R') K K' φ n).hom]

/-- When the square of rings is a pushout, so that `A' = A ⊗_R R'`, the comparison
`K ⊗ᴸ_R R' ⟶ K'` is invertible in `D(R')` exactly when the ring-level map of Stacks 0DJ7 is
invertible in every degree. -/
theorem isIso_ringComparison_iff_forall_isIso [Algebra.IsPushout R A R' A']
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') :
    IsIso (ringComparison (R := R) (R' := R') K K' φ) ↔
      ∀ n : ℤ, IsIso (ringBaseChangeCohomologyMapGeneral (R := R) (R' := R') K K' φ n) := by
  rw [DerivedCategory.isIso_iff]
  refine forall_congr' fun n => ?_
  rw [← bijective_cohomologyComparisonLinearMap_iff (R := R) (R' := R') K K' φ n]
  refine Iff.trans (bijective_iff_outer_of_bijective_inner
      (fm := ⇑(cohomologyComparisonLinearMapGeneral (R := R) (R' := R') K K' φ n).hom)
      (gm := fun m => ((1 : A') ⊗ₜ[A ⊗[R] R',
          baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')] m :
        (ModuleCat.extendScalars
            (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A'))).obj
          (baseChangeCohomologyCatGeneral (R := R) (R' := R') K n)))
      (en := ⇑(ringBaseChangeCohomologyMapGeneral (R := R) (R' := R') K K' φ n).hom)
      (bijective_one_tmul (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A'))
        bijective_baseChangeTensorRingMap _)
      (fun m => (ringBaseChangeCohomologyMapGeneral_one_tmul (R := R) (R' := R') K K' φ n m).symm))
    (ConcreteCategory.isIso_iff_bijective
      (f := ringBaseChangeCohomologyMapGeneral (R := R) (R' := R') K K' φ n)).symm

end Ring

end RingTheory.TorIndependence

namespace AlgebraicGeometry

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- The algebra structures on the coordinate rings of a chart, given by its four ring maps. -/
private instance (ch : BaseChangeChart f g f' g') : Algebra ch.R ch.A := ch.a.hom.toAlgebra
private instance (ch : BaseChangeChart f g f' g') : Algebra ch.R ch.R' := ch.b.hom.toAlgebra
private instance (ch : BaseChangeChart f g f' g') : Algebra ch.A ch.A' := ch.c.hom.toAlgebra
private instance (ch : BaseChangeChart f g f' g') : Algebra ch.R' ch.A' := ch.d.hom.toAlgebra
private instance (ch : BaseChangeChart f g f' g') : Algebra ch.R ch.A' :=
  (ch.c.hom.comp ch.a.hom).toAlgebra
private instance (ch : BaseChangeChart f g f' g') : IsScalarTower ch.R ch.A ch.A' :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
private instance (ch : BaseChangeChart f g f' g') : IsScalarTower ch.R ch.R' ch.A' :=
  IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r

/-- The comparison map of a chart is the ring-level comparison of the chart's square of
coordinate rings, applied to the morphism `RΓ(U,K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{X'}(U') ⟶ RΓ(U',K')` assembled
from the identification `sectionsBaseChangeMap` and `RΓ(U', φ)`. -/
@[stacks 0DJ8 "the comparison map of (2) is the ring-level comparison of the chart's square"]
theorem comparison_eq_ringComparison (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := ch.c.hom.toAlgebra
    letI := ch.d.hom.toAlgebra
    letI := (ch.c.hom.comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower ch.R ch.R' ch.A' :=
      IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
    ch.comparison K K' φ =
      RingTheory.TorIndependence.ringComparison
        (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K)
        ((affineDerivedSections ch.incU').obj K')
        (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) := by
  dsimp only [comparison, pullbackComparison, RingTheory.TorIndependence.ringComparison]
  rw [Functor.map_comp, Category.assoc]
  rfl

/-- The comparison map of a Cartesian affine-open chart is an isomorphism exactly when, in
every degree, the induced map on cohomology is bijective after localizing at every prime of
`𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V')`. -/
@[stacks 0DJ8 "(2) at one chart, reduced to the primes of the chart's coordinate ring"]
theorem isIso_comparison_iff (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := ch.c.hom.toAlgebra
    letI := ch.d.hom.toAlgebra
    letI := (ch.c.hom.comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower ch.R ch.R' ch.A' :=
      IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
    (IsIso (ch.comparison K K' φ) ↔
      ∀ (n : ℤ) (q : Ideal (ch.A ⊗[ch.R] ch.R')) (_ : q.IsPrime),
        Function.Bijective (LocalizedModule.map q.primeCompl
          (RingTheory.TorIndependence.cohomologyComparisonLinearMapGeneral
            (R := ch.R) (R' := ch.R')
            ((affineDerivedSections ch.incU).obj K)
            ((affineDerivedSections ch.incU').obj K')
            (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) n).hom)) := by
  rw [ch.comparison_eq_ringComparison K K' φ]
  exact RingTheory.TorIndependence.isIso_ringComparison_iff _ _ _

/-- The comparison map of a Cartesian affine-open chart is an isomorphism exactly when the
ring-level map `RingTheory.TorIndependence.ringBaseChangeCohomologyMapGeneral` of Stacks 0DJ7 for
the chart's square of coordinate rings is invertible in every degree. -/
@[stacks 0DJ8 "(2) at one chart is the invertibility, in every degree, of the ring-level map of \
Stacks 0DJ7 for the chart's rings: the affine reduction of the source proof"]
theorem isIso_comparison_iff_forall_isIso_ringBaseChangeCohomologyMap
    (ch : BaseChangeChart f g f' g')
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := ch.c.hom.toAlgebra
    letI := ch.d.hom.toAlgebra
    letI := (ch.c.hom.comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A ch.A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower ch.R ch.R' ch.A' :=
      IsScalarTower.of_algebraMap_eq fun r => DFunLike.congr_fun ch.isPushout_hom r
    (IsIso (ch.comparison K K' φ) ↔
      ∀ n : ℤ, IsIso (RingTheory.TorIndependence.ringBaseChangeCohomologyMapGeneral
        (R := ch.R) (R' := ch.R')
        ((affineDerivedSections ch.incU).obj K)
        ((affineDerivedSections ch.incU').obj K')
        (ch.sectionsBaseChangeMap K ≫ (affineDerivedSections ch.incU').map φ) n)) := by
  have : Algebra.IsPushout ch.R ch.A ch.R' ch.A' :=
    CommRingCat.isPushout_iff_isPushout.mp ch.isPushout
  rw [ch.comparison_eq_ringComparison K K' φ]
  exact RingTheory.TorIndependence.isIso_ringComparison_iff_forall_isIso _ _ _

end BaseChangeChart

end AlgebraicGeometry

end
