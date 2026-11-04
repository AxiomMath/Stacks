module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FinitePresentationSlice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleStructureSheaf

/-!
# Finiteness of a module on an algebraic space is tested on its étale charts

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  An
`𝒪_F`-module on the small étale site of `F` is of finite type, respectively of finite
presentation, exactly when its restriction to the slice at one surjective étale chart is, and
exactly when its restriction to the slice at every étale chart is, and exactly when its
restriction to the slice at every étale chart whose underlying scheme is affine is.

This is the clause of Stacks 03DN for finite type and for finite presentation, applied to the
covering families of the small étale site supplied by
`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective` and
`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts`.  It is the finiteness counterpart
of `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_over_of_isSurjective` and of
`AlgebraicGeometry.Space.isCoherentOnSite_iff_over_of_isSurjective`.

## Main results

* `AlgebraicGeometry.Space.isFiniteType_iff_over_of_isSurjective`,
  `AlgebraicGeometry.Space.isFiniteType_iff_forall_over` and
  `AlgebraicGeometry.Space.isFiniteType_iff_forall_affine_over`: finite type is tested on one
  surjective étale chart, on every étale chart, and on every affine étale chart.
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_iff_over_of_isSurjective`: the first of those in
  the `SheafOfModules.IsFiniteTypeOnSite` reading of clause (5) of Stacks 03DL, which is the
  reading every statement about ideal sheaves in this development uses.
* `AlgebraicGeometry.Space.isFinitePresentation_iff_over_of_isSurjective`,
  `AlgebraicGeometry.Space.isFinitePresentation_iff_forall_over` and
  `AlgebraicGeometry.Space.isFinitePresentation_iff_forall_affine_over`: the same three
  equivalences for finite presentation.
* `AlgebraicGeometry.Space.smallEtaleRingedSite_hasPullbacks` and the four sheafification
  instances: the iterated-slice data that the clause of Stacks 03DN for these two conditions
  consumes.

## Implementation notes

The restriction to a chart is restriction to the slice of the small étale site at that chart,
`SheafOfModules.over`, as in
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_over_of_isSurjective` and
`AlgebraicGeometry.Space.isCoherentOnSite_iff_over_of_isSurjective`.  The slice of `F_étale` at
a chart is the small étale site of the chart, which is Stacks 04M0, proved as
`AlgebraicGeometry.Space.smallEtaleEquivalenceOverChart`; transporting a module across that
equivalence of *sites* additionally requires matching the two structure sheaves.  The statements
below are in the slice reading on both sides, which needs no such matching.

The clause of Stacks 03DN for finite type and for finite presentation quantifies over the
slices of the *slices* of the site, so it needs sheafification of presheaves of abelian groups,
and the agreement of local equivalences with locally bijective morphisms, on the iterated
slices too.  Those follow, exactly as the one-step versions of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSite` do, from essential smallness: a slice of
an essentially small category is essentially small, hence so is a slice of `Over U`.  As in
`StacksFrontier.AlgebraicGeometry.Spaces.RingedSite` the instances are restated for the
projections of `AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does not
unfold.

Fibre products of the site are needed by
`Stacks.SheafOfModules.Site.isFiniteType_over_of_isFiniteType`; they are
`AlgebraicGeometry.Space.SmallEtale.hasPullbacks`, which depends on the algebraicity of `F` and
so cannot be a global instance.  The finite-presentation half of the heredity is
`Stacks.SheafOfModules.isFinitePresentation_over`, which needs no fibre products.

The module universe is the universe `u` of the schemes, as it is for
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_over_of_isSurjective`: both
`SheafOfModules.IsFiniteType` and `SheafOfModules.IsFinitePresentation` take the module
sections in the universe of the coefficient rings.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- A slice of a slice of the small étale site is essentially small, because a slice of an
essentially small category is. -/
instance SmallEtale.instEssentiallySmallOverOver (U : SmallEtale B S hS F) (V : Over U) :
    EssentiallySmall.{u} (Over V) :=
  inferInstanceAs (EssentiallySmall.{u} (CostructuredArrow (𝟭 (Over U)) V))

section ConcreteSheafification

variable (A : Type v) [Category.{u} A]
  {FA : A → A → Type*} {CA : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)] [HasColimits A] [HasLimits A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

/-- Sheafification with concrete coefficients on each slice of each slice of the small étale
site. -/
instance (priority := low) SmallEtale.instHasSheafifyOverOver
    (U : SmallEtale B S hS F) (V : Over U) :
    HasSheafify (((SmallEtale.topology B S hS F).over U).over V) A :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- The local equivalences of concrete presheaves on a slice of a slice of the small étale site
are exactly the locally bijective morphisms. -/
instance (priority := low) SmallEtale.instWEqualsLocallyBijectiveOverOver
    (U : SmallEtale B S hS F) (V : Over U) :
    (((SmallEtale.topology B S hS F).over U).over V).WEqualsLocallyBijective A :=
  .ofEssentiallySmall.{u} _

end ConcreteSheafification

variable (hF : IsAlgebraicSpace B S hS F)

/-- Every slice of every slice of the small étale ringed site of `F` admits sheafification of
presheaves of abelian groups. -/
instance smallEtaleRingedSite_hasSheafify_over_over :
    ∀ (U : (smallEtaleRingedSite B S hS F hF).C) (V : Over U),
      HasSheafify (((smallEtaleRingedSite B S hS F hF).J.over U).over V)
        AddCommGrpCat.{u} := by
  change ∀ (U : SmallEtale B S hS F) (V : Over U),
    HasSheafify (((SmallEtale.topology B S hS F).over U).over V) AddCommGrpCat.{u}
  infer_instance

/-- The same sheafification, in the weak form that the sheaves-of-modules API consumes. -/
instance smallEtaleRingedSite_hasWeakSheafify_over_over :
    ∀ (U : (smallEtaleRingedSite B S hS F hF).C) (V : Over U),
      HasWeakSheafify (((smallEtaleRingedSite B S hS F hF).J.over U).over V)
        AddCommGrpCat.{u} :=
  fun U V => (smallEtaleRingedSite_hasSheafify_over_over B S hS F hF U V).isRightAdjoint

/-- On every slice of every slice of the small étale ringed site of `F`, the local equivalences
of presheaves of abelian groups are exactly the locally bijective morphisms. -/
instance smallEtaleRingedSite_wEqualsLocallyBijective_over_over :
    ∀ (U : (smallEtaleRingedSite B S hS F hF).C) (V : Over U),
      (((smallEtaleRingedSite B S hS F hF).J.over U).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} := by
  change ∀ (U : SmallEtale B S hS F) (V : Over U),
    (((SmallEtale.topology B S hS F).over U).over V).WEqualsLocallyBijective AddCommGrpCat.{u}
  infer_instance

/-- The weak sheafification of the previous instance, in the spelling that reads the slice of
the small étale ringed site as a ringed site in its own right
(`AlgebraicGeometry.RingedSite.over`), which is the shape
`SheafOfModules.IsFiniteType` and `SheafOfModules.IsFinitePresentation` ask for on a slice. -/
instance smallEtaleRingedSite_over_hasWeakSheafify_over :
    ∀ (U : (smallEtaleRingedSite B S hS F hF).C)
      (V : ((smallEtaleRingedSite B S hS F hF).over U).C),
      HasWeakSheafify (((smallEtaleRingedSite B S hS F hF).over U).J.over V)
        AddCommGrpCat.{u} := by
  change ∀ (U : SmallEtale B S hS F) (V : Over U),
    HasWeakSheafify (((SmallEtale.topology B S hS F).over U).over V) AddCommGrpCat.{u}
  infer_instance

/-- The agreement of local equivalences with locally bijective morphisms, in the same
slice-as-a-ringed-site spelling. -/
instance smallEtaleRingedSite_over_wEqualsLocallyBijective_over :
    ∀ (U : (smallEtaleRingedSite B S hS F hF).C)
      (V : ((smallEtaleRingedSite B S hS F hF).over U).C),
      (((smallEtaleRingedSite B S hS F hF).over U).J.over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} := by
  change ∀ (U : SmallEtale B S hS F) (V : Over U),
    (((SmallEtale.topology B S hS F).over U).over V).WEqualsLocallyBijective AddCommGrpCat.{u}
  infer_instance

/-- The small étale ringed site of `F` has fibre products: this is
`AlgebraicGeometry.Space.SmallEtale.hasPullbacks`, restated for the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does not unfold. -/
theorem smallEtaleRingedSite_hasPullbacks :
    HasPullbacks (smallEtaleRingedSite B S hS F hF).C :=
  SmallEtale.hasPullbacks B S hS F hF

/-- The family of all objects of a site covers the final object. -/
private theorem coversTop_id {C : Type*} [Category C] (J : GrothendieckTopology C) :
    J.CoversTop (fun U : C => U) := fun W =>
  J.superset_covering (fun _ _ _ => ⟨_, ⟨𝟙 _⟩⟩) (J.top_mem W)

/-- **Finite type on the small étale site is tested on one surjective étale chart.**  An
`𝒪_F`-module is of finite type if and only if its restriction to the slice at one étale chart
whose structure morphism is surjective on points is of finite type. -/
theorem isFiniteType_iff_over_of_isSurjective (M : Modules.{u, u} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) (hsurj : IsSurjective B S hS U.1.hom) :
    M.IsFiniteType ↔
      SheafOfModules.IsFiniteType
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U) := by
  have _ := smallEtaleRingedSite_hasPullbacks B S hS F hF
  refine ⟨fun hM => Stacks.SheafOfModules.Site.isFiniteType_over_of_isFiniteType U hM,
    fun h => ?_⟩
  exact (Stacks.SheafOfModules.isFiniteType_iff_exists_cover_isFiniteType M).2
    ⟨PUnit.{u + 2}, fun _ => U,
      SmallEtale.coversTop_of_isSurjective B S hS F hF U hsurj, fun _ => h⟩

/-- **Finite type on a site is tested on one surjective étale chart**, in the
`SheafOfModules.IsFiniteTypeOnSite` reading of clause (5) of Stacks 03DL. -/
theorem isFiniteTypeOnSite_iff_over_of_isSurjective (M : Modules.{u, u} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) (hsurj : IsSurjective B S hS U.1.hom) :
    SheafOfModules.IsFiniteTypeOnSite M ↔
      SheafOfModules.IsFiniteTypeOnSite
        (R := Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS F hF).over U).O) (M.over U) := by
  have : ∀ V : ((smallEtaleRingedSite B S hS F hF).over U).C,
      HasSheafify (((smallEtaleRingedSite B S hS F hF).over U).J.over V) AddCommGrpCat.{u} :=
    smallEtaleRingedSite_hasSheafify_over_over B S hS F hF U
  exact ⟨fun h => Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _
      ((isFiniteType_iff_over_of_isSurjective B S hS F hF M U hsurj).1
        (Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite M h)),
    fun h => Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _
      ((isFiniteType_iff_over_of_isSurjective B S hS F hF M U hsurj).2
        (Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _ h))⟩

/-- **Finite type on the small étale site is tested on every étale chart.**  Unlike
`AlgebraicGeometry.Space.isFiniteType_iff_over_of_isSurjective` this needs no geometry: the
family of all objects of a site covers the final object. -/
theorem isFiniteType_iff_forall_over (M : Modules.{u, u} B S hS F hF) :
    M.IsFiniteType ↔
      ∀ U : (smallEtaleRingedSite B S hS F hF).C,
        SheafOfModules.IsFiniteType
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U) := by
  have _ := smallEtaleRingedSite_hasPullbacks B S hS F hF
  refine ⟨fun hM U => Stacks.SheafOfModules.Site.isFiniteType_over_of_isFiniteType U hM,
    fun h => ?_⟩
  exact (Stacks.SheafOfModules.isFiniteType_iff_exists_cover_isFiniteType M).2
    ⟨(smallEtaleRingedSite B S hS F hF).C, fun U => U, coversTop_id _, h⟩

/-- **Finite type on the small étale site is tested on every affine étale chart.**  An
`𝒪_F`-module is of finite type if and only if its restriction to the slice at every étale chart
whose underlying scheme is affine is of finite type. -/
theorem isFiniteType_iff_forall_affine_over (M : Modules.{u, u} B S hS F hF) :
    M.IsFiniteType ↔
      ∀ U : (smallEtaleRingedSite B S hS F hF).C,
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)) →
        SheafOfModules.IsFiniteType
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U) := by
  have _ := smallEtaleRingedSite_hasPullbacks B S hS F hF
  refine ⟨fun hM U _ => Stacks.SheafOfModules.Site.isFiniteType_over_of_isFiniteType U hM,
    fun h => ?_⟩
  exact (Stacks.SheafOfModules.isFiniteType_iff_exists_cover_isFiniteType M).2
    ⟨{U : SmallEtale B S hS F //
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U))},
      fun U => U.1, SmallEtale.coversTop_affineCharts B S hS F, fun U => h U.1 U.2⟩

/-- **Finite presentation on the small étale site is tested on one surjective étale chart.**
An `𝒪_F`-module is of finite presentation if and only if its restriction to the slice at one
étale chart whose structure morphism is surjective on points is of finite presentation. -/
theorem isFinitePresentation_iff_over_of_isSurjective (M : Modules.{u, u} B S hS F hF)
    (U : (smallEtaleRingedSite B S hS F hF).C) (hsurj : IsSurjective B S hS U.1.hom) :
    M.IsFinitePresentation ↔
      SheafOfModules.IsFinitePresentation
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U) := by
  refine ⟨fun hM => Stacks.SheafOfModules.isFinitePresentation_over M hM U, fun h => ?_⟩
  exact (Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_isFinitePresentation M).2
    ⟨PUnit.{u + 2}, fun _ => U,
      SmallEtale.coversTop_of_isSurjective B S hS F hF U hsurj, fun _ => h⟩

/-- **Finite presentation on the small étale site is tested on every étale chart.** -/
theorem isFinitePresentation_iff_forall_over (M : Modules.{u, u} B S hS F hF) :
    M.IsFinitePresentation ↔
      ∀ U : (smallEtaleRingedSite B S hS F hF).C,
        SheafOfModules.IsFinitePresentation
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U) := by
  refine ⟨fun hM U => Stacks.SheafOfModules.isFinitePresentation_over M hM U, fun h => ?_⟩
  exact (Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_isFinitePresentation M).2
    ⟨(smallEtaleRingedSite B S hS F hF).C, fun U => U, coversTop_id _, h⟩

/-- **Finite presentation on the small étale site is tested on every affine étale chart.** -/
theorem isFinitePresentation_iff_forall_affine_over (M : Modules.{u, u} B S hS F hF) :
    M.IsFinitePresentation ↔
      ∀ U : (smallEtaleRingedSite B S hS F hF).C,
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U)) →
        SheafOfModules.IsFinitePresentation
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            ((smallEtaleRingedSite B S hS F hF).over U).O)) (M.over U) := by
  refine ⟨fun hM U _ => Stacks.SheafOfModules.isFinitePresentation_over M hM U, fun h => ?_⟩
  exact (Stacks.SheafOfModules.isFinitePresentation_iff_exists_cover_isFinitePresentation M).2
    ⟨{U : SmallEtale B S hS F //
        IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj U))},
      fun U => U.1, SmallEtale.coversTop_affineCharts B S hS F, fun U => h U.1 U.2⟩

end AlgebraicGeometry.Space

end
