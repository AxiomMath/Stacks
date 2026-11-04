module

public import Mathlib.Data.List.TFAE
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-coherent cohomology of a complex is étale-local on an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `E` be
an object of `D(𝒪_X)`.  Then `E` has quasi-coherent cohomology if and only if it has so after
pullback to one, or to every, étale chart of `X`, or after pullback along one surjective étale
morphism of algebraic spaces.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback`: quasi-coherence of an
  `𝒪_X`-module is inherited by every étale pullback.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_forall_affine_chart`: an `𝒪_X`-module whose
  pullback to every affine étale chart is quasi-coherent is quasi-coherent.
* `AlgebraicGeometry.Space.derivedQuasicoherent_tfae`: **Stacks 08F2**, the five equivalent
  tests for membership in `D_QCoh(𝒪_X)`.

## Implementation notes

`D_QCoh(𝒪_X)` is `AlgebraicGeometry.Space.QuasicoherentDerivedCategory` of Stacks 071X, the full
subcategory of `D(𝒪_X)` cut out by `DerivedCategoryB.derivedCategoryB` for quasi-coherence, so
membership in it is that object property and no new predicate is introduced.

A scheme chart `φ : U → X` is read as the morphism of algebraic spaces
`AlgebraicGeometry.Space.chartToSpace`, and `Lφ^*` is
`AlgebraicGeometry.Space.etaleModulePullback` on derived categories.  That is legitimate because
an étale pullback of modules is restriction of sections along
`AlgebraicGeometry.Space.smallEtalePostcomp` and so is exact — the content of
`AlgebraicGeometry.Space.preservesFiniteLimits_etaleModulePullback` and
`AlgebraicGeometry.Space.preservesFiniteColimits_etaleModulePullback` — hence its induced
functor on derived categories is already the total left derived functor.  No separate
`Lf^*` is constructed, and the comparison `Hⁿ(Lf^*E) ≅ f^*(HⁿE)` is
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`.

## References

* [Stacks Project, Tag 08F2](https://stacks.math.columbia.edu/tag/08F2)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-! ### Quasi-coherence and étale pullback of modules -/

/-- **Quasi-coherence is inherited by every étale pullback.**  If an `𝒪_X`-module `M` is
quasi-coherent and `f : Y ⟶ X` is étale, then `f^*M` is quasi-coherent.

This is the half of `AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback_iff` which
needs no surjectivity: a covering of the composite chart of `X` lifts to a covering of the chart
of `Y` by `AlgebraicGeometry.Space.SmallEtale.smallEtalePostcomp_cover_lift`, and global
presentations transfer by
`AlgebraicGeometry.Space.hasGlobalPresentation_over_postcomp_iff`. -/
theorem isQuasicoherentOnSite_etaleModulePullback (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) :
    ((etaleModulePullback B S hS f hf).obj M).IsQuasicoherentOnSite := by
  refine ⟨fun V => ?_⟩
  obtain ⟨I, Z, h, hcov, hpres⟩ :=
    hM.locally_hasGlobalPresentation ((ringedSitePostcomp B S hS f hf).obj V)
  have hlift : (Sieve.ofArrows Z h).functorPullback (ringedSitePostcomp B S hS f hf) ∈
      (smallEtaleRingedSite B S hS Y.1 Y.2).J V :=
    SmallEtale.smallEtalePostcomp_cover_lift B S hS f hf V _ hcov
  let Ar := {A : Over V //
    ((Sieve.ofArrows Z h).functorPullback (ringedSitePostcomp B S hS f hf)).arrows A.hom}
  have hEq : Sieve.ofArrows (fun A : Ar => A.1.left) (fun A : Ar => A.1.hom) =
      (Sieve.ofArrows Z h).functorPullback (ringedSitePostcomp B S hS f hf) := by
    refine le_antisymm ?_ ?_
    · intro T g hg
      obtain ⟨A, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
      exact ((Sieve.ofArrows Z h).functorPullback
        (ringedSitePostcomp B S hS f hf)).downward_closed A.2 b
    · intro T g hg
      exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨Over.mk g, hg⟩, 𝟙 T, by simp⟩
  refine ⟨Ar, fun A => A.1.left, fun A => A.1.hom, ?_, fun A => ?_⟩
  · rw [hEq]
    exact hlift
  · obtain ⟨j, b, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp A.2
    rw [hasGlobalPresentation_over_postcomp_iff B S hS f hf M A.1.left]
    exact Stacks.SheafOfModules.hasGlobalPresentation_overMap M b (hpres j)

/-- **Quasi-coherence is detected on the affine étale charts.**  An `𝒪_X`-module whose pullback
along the structure morphism of every étale scheme chart with affine underlying scheme is
quasi-coherent is itself quasi-coherent.

This is condition (4) of Stacks 03M0 read through the pullback `φ^*` of Stacks 03LU rather than
through restriction to a slice.  The affine charts cover the final object of the small étale site
(`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts`); over an affine chart `A` the
hypothesis produces, on each étale chart of `A`, a covering on whose members the pullback has a
global presentation, and
`AlgebraicGeometry.Space.hasGlobalPresentation_over_postcomp_iff` turns those into global
presentations of `M` itself over the composite charts of `X`. -/
theorem isQuasicoherentOnSite_of_forall_affine_chart (M : Modules.{u, u} B S hS X.1 X.2)
    (h : ∀ A : SmallEtale B S hS X.1,
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
        ((etaleModulePullback B S hS (chartToSpace B S hS X A)
          (isEtale_chartToSpace B S hS X A)).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  refine (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation
    M).2 ⟨{Z : (smallEtaleRingedSite B S hS X.1 X.2).C // (M.over Z).HasGlobalPresentation},
      fun z => z.1, fun W => ?_, fun z => z.2⟩
  refine (smallEtaleRingedSite B S hS X.1 X.2).J.transitive
    (SmallEtale.coversTop_affineCharts B S hS X.1 W) _ ?_
  intro W' p hp
  obtain ⟨A, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff _ p).mp hp
  set f := chartToSpace B S hS X A.1
  set hf := isEtale_chartToSpace B S hS X A.1
  set Va := (SmallEtale.chartLocalizationInverse B S hS X.1 A.1).obj (Over.mk a)
  obtain ⟨I₁, V₁, q₁, hcov₁, hpres₁⟩ := (h A.1 A.2).locally_hasGlobalPresentation Va
  have hpush := (SmallEtale.coverPreserving_smallEtalePostcomp B S hS f hf).cover_preserve hcov₁
  have hle : Sieve.functorPushforward (ringedSitePostcomp B S hS f hf)
      (Sieve.ofArrows V₁ q₁) ≤
      Sieve.ofObjects (fun z : {Z : (smallEtaleRingedSite B S hS X.1 X.2).C //
        (M.over Z).HasGlobalPresentation} => z.1)
        ((ringedSitePostcomp B S hS f hf).obj Va) := by
    rintro T r ⟨Z₀, r₀, q, hr₀, rfl⟩
    obtain ⟨i, b, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hr₀
    exact ⟨⟨_, (hasGlobalPresentation_over_postcomp_iff B S hS f hf M (V₁ i)).1 (hpres₁ i)⟩,
      ⟨q ≫ (ringedSitePostcomp B S hS f hf).map b⟩⟩
  have hobj := (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering hle hpush
  have hα := (smallEtaleRingedSite B S hS X.1 X.2).J.pullback_stable
    ((Over.forget A.1).mapIso
      ((SmallEtale.chartLocalizationCounitIso B S hS X.1 A.1).app (Over.mk a))).inv hobj
  exact (smallEtaleRingedSite B S hS X.1 X.2).J.superset_covering (fun _ _ hb => hb) hα

/-! ### The derived category -/

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

/-- For an étale morphism `f : Y ⟶ X` of algebraic spaces, the condition that `Lf^*E` lie in
`D_QCoh(𝒪_Y)`.

An étale pullback of modules is exact, so the functor it induces on derived categories is
already its total left derived functor; `Lf^*` is therefore
`CategoryTheory.Functor.mapDerivedCategory` of
`AlgebraicGeometry.Space.etaleModulePullback`. -/
def DerivedQuasicoherentPullback (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) : Prop :=
  DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
    ((etaleModulePullback B S hS f hf).mapDerivedCategory.obj E)

/-- `Lf^*E` lies in `D_QCoh(𝒪_Y)` exactly when every étale pullback `f^*(HⁿE)` of a cohomology
sheaf of `E` is quasi-coherent.

An étale pullback is exact, so it commutes with the cohomology of the derived category by
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`: `Hⁿ(Lf^*E) ≅ f^*(HⁿE)`. -/
theorem derivedQuasicoherentPullback_iff (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    DerivedQuasicoherentPullback B S hS f hf E ↔
      ∀ n : ℤ, ((etaleModulePullback B S hS f hf).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj
          E)).IsQuasicoherentOnSite :=
  ⟨fun h n => SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((Functor.mapDerivedCategoryHomologyIso (etaleModulePullback B S hS f hf) n).app E) (h n),
    fun h n => SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((Functor.mapDerivedCategoryHomologyIso (etaleModulePullback B S hS f hf) n).app E).symm
      (h n)⟩

/-- The structure morphism of an étale scheme chart, read as a morphism of algebraic spaces, has
the same underlying morphism of presheaves as the chart itself. -/
theorem chartToSpace_hom (A : SmallEtale B S hS X.1) :
    (chartToSpace B S hS X A).hom = A.1.hom := rfl

/-- **Stacks 08F2.**  Let `E` be an object of `D(𝒪_X)` on an algebraic space `X`.  The following
are equivalent: `E` lies in `D_QCoh(𝒪_X)`; `Lφ^*E` lies in `D_QCoh(𝒪_U)` for every étale scheme
chart `φ : U → X` with `U` affine; the same for every étale scheme chart; the same for one étale
scheme chart surjective on points; and `Lf^*E` lies in `D_QCoh(𝒪_Y)` for one étale morphism
`f : Y ⟶ X` of algebraic spaces surjective on points.

All five are the corresponding conditions of Stacks 03M0 applied to the cohomology sheaves of
`E`, the passage between `Hⁿ(Lf^*E)` and `f^*(HⁿE)` being
`AlgebraicGeometry.Space.derivedQuasicoherentPullback_iff`. -/
@[stacks 08F2]
theorem derivedQuasicoherent_tfae (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    List.TFAE
      [DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) E,
        ∀ A : SmallEtale B S hS X.1,
          IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
          DerivedQuasicoherentPullback B S hS (chartToSpace B S hS X A)
            (isEtale_chartToSpace B S hS X A) E,
        ∀ A : SmallEtale B S hS X.1,
          DerivedQuasicoherentPullback B S hS (chartToSpace B S hS X A)
            (isEtale_chartToSpace B S hS X A) E,
        ∃ A : SmallEtale B S hS X.1, IsSurjective B S hS A.1.hom ∧
          DerivedQuasicoherentPullback B S hS (chartToSpace B S hS X A)
            (isEtale_chartToSpace B S hS X A) E,
        ∃ (Z : AlgebraicSpaces B S hS) (g : Z ⟶ X) (hg : IsEtale B S hS g.hom),
          IsSurjective B S hS g.hom ∧ DerivedQuasicoherentPullback B S hS g hg E] := by
  tfae_have 1 → 3 := fun h A => (derivedQuasicoherentPullback_iff B S hS _ _ E).2 fun n =>
    isQuasicoherentOnSite_etaleModulePullback B S hS _ _ _ (h n)
  tfae_have 3 → 2 := fun h A _ => h A
  tfae_have 2 → 1 := fun h n =>
    isQuasicoherentOnSite_of_forall_affine_chart B S hS _ fun A hA =>
      (derivedQuasicoherentPullback_iff B S hS _ _ E).1 (h A hA) n
  tfae_have 1 → 4 := fun h => by
    obtain ⟨A, hA⟩ := exists_surjective_smallEtale_chart B S hS X.1 X.2
    exact ⟨A, hA, tfae_1_to_3 h A⟩
  tfae_have 4 → 5 := by
    rintro ⟨A, hA, hE⟩
    exact ⟨chartSpace B S hS X A, chartToSpace B S hS X A, isEtale_chartToSpace B S hS X A,
      hA, hE⟩
  tfae_have 5 → 1 := by
    rintro ⟨Z, g, hg, hgs, hE⟩ n
    exact (isQuasicoherentOnSite_etaleModulePullback_iff B S hS g hg hgs _).2
      ((derivedQuasicoherentPullback_iff B S hS g hg E).1 hE n)
  tfae_finish

end AlgebraicGeometry.Space

end
