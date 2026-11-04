module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.QuotToCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback

/-!
# The locus where a quotient is supported in an open subspace

Let `f : Y ⟶ B` be the morphism of a Quot situation of Stacks 09TR, with module `G` on `Y`, and
let `π : X ⟶ Y` be an open immersion of algebraic spaces over `B`.  For a quotient `G_T ⟶ Q` in
`Quot_{G/Y/B}(T)` over a scheme `T` of the site, the condition `Supp(Q_t) ⊆ |X_t|` on a point
`t ∈ T` is open in `t`, as used in Stacks 0DP2 and Stacks 0DP3.

Here the locus is the factorization locus of Stacks 0DNA for the object `(T, Q)` of `Coh_{Y/B}`
underlying the quotient: the complement in `|T|` of the image of the points of `Supp(Q)` not
lying in `X_T`, which is open because `Supp(Q)` is proper over `T`.  Its points are those `t`
with `Supp(Q_t) ⊆ |X_t|`, and a morphism `g : U ⟶ T` of schemes of the site factors through it
exactly when the base change of `Q` to `U` is supported in `X_U`: the support of the pullback of
`Q` is the inverse image of `Supp(Q)` by Stacks 07TZ, and the points of `Y_U` are the pairs of
points of `Y_T` and of `U` over a common point of `T` by Stacks 03H4.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.IsSupportedIn`: the condition `Supp(Q) ⊆ |X_T|` on a
  quotient `G_T ⟶ Q`.
* `AlgebraicGeometry.Space.QuotSituation.supportLocus`: the locus in a scheme of the site above
  which a quotient classified by the Quot functor is supported in `X`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.isOpenSubspace_supportLocus`: the locus is an open
  subspace.
* `AlgebraicGeometry.Space.QuotSituation.mem_supportLocus_iff`: a morphism of schemes of the site
  lies in the locus exactly when the base change of the quotient along it is supported in `X`.

## References

* [Stacks Project, Tag 0DP2](https://stacks.math.columbia.edu/tag/0DP2)
* [Stacks Project, Tag 0DP3](https://stacks.math.columbia.edu/tag/0DP3)
* [Stacks Project, Tag 0DNA](https://stacks.math.columbia.edu/tag/0DNA)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotSituation

variable (D : QuotSituation B S hS) {X : AlgebraicSpaces B S hS} {π : X ⟶ D.X} {bX : X ⟶ D.Y}

/-- **The condition `Supp(Q) ⊆ |X_T|`** on the quotient of `G_T` by a subobject `K`: its support
lies in the image of the base change `π_T : X_T ⟶ Y_T` of the open immersion. -/
def IsSupportedIn (hπ : π ≫ D.f = bX) (T : SchemesOver D.Y)
    (K : Subobject (D.baseChangeModule T)) : Prop :=
  D.support T (D.quotientModule T K) ⊆
    Set.range (pointsMap B S hS (baseChangeSpace bX T).1
      (D.toCoherentSituation.baseChangeOfMap hπ T).hom)

/-- A point of `Y_T` lies in the image of `X_T` exactly when its image in `Y` lies in the image of
`X`, the square of `π_T` and `π` being cartesian (Stacks 03H4). -/
theorem mem_range_baseChangeOfMap_iff (hπ : π ≫ D.f = bX) (T : SchemesOver D.Y)
    (y : points B S hS (D.space T).1) :
    y ∈ Set.range (pointsMap B S hS (baseChangeSpace bX T).1
        (D.toCoherentSituation.baseChangeOfMap hπ T).hom) ↔
      pointsMap B S hS (D.space T).1 (baseChangeProjection D.f T).hom y ∈
        Set.range (pointsMap B S hS X.1 π.hom) := by
  have sq := D.toCoherentSituation.isPullback_baseChangeOfMap hπ T
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨pointsMap B S hS _ (baseChangeProjection bX T).hom x, ?_⟩
    exact (pointsMap_apply_comm B S hS sq.w x).symm
  · rintro ⟨x, hx⟩
    obtain ⟨w, hw, -⟩ := exists_point_of_isPullback_presheaf B S hS sq y x hx.symm
    exact ⟨w, hw⟩

/-- The object `(T, Q)` of `Coh_{Y/B}` underlying a quotient `G_T ⟶ Q` classified by the Quot
functor over a scheme `T` of the site (Stacks 0DP6). -/
abbrev quotFamilyCohObject {T : BigFppfOver B S hS} (y : QuotFamilyOver D T) :
    CoherentObject D.toCoherentSituation :=
  D.cohObject (CostructuredArrow.mk y.toBase) y.subobject y.mem

/-- The support of the quotient underlying a quotient classified by the Quot functor is closed,
by Stacks 07TZ. -/
theorem isClosed_support_quotFamilyCohObject {T : BigFppfOver B S hS} (y : QuotFamilyOver D T) :
    IsClosed (D.toCoherentSituation.support (D.quotFamilyCohObject y).T
      (D.quotFamilyCohObject y).F) :=
  D.isClosed_support_of_mem y.mem.1

/-- The reduced induced closed subspace on the support of the quotient underlying a quotient
classified by the Quot functor. -/
abbrev quotFamilySupportSubspace {T : BigFppfOver B S hS} (y : QuotFamilyOver D T) :
    Subfunctor (D.space (CostructuredArrow.mk y.toBase)).1 :=
  D.toCoherentSituation.supportSubspace (D.quotFamilyCohObject y)
    (D.isClosed_support_quotFamilyCohObject y)

/-- **The locus above which a quotient is supported in `X`.**  For a quotient classified by the
Quot functor over a scheme `T` of the site, this is the factorization locus of Stacks 0DNA for the
underlying object of `Coh_{Y/B}`: the complement in `|T|` of the image of the points of the support
not lying in `X_T`. -/
def supportLocus (hπ : π ≫ D.f = bX) {T : BigFppfOver B S hS} (y : QuotFamilyOver D T) :
    Subfunctor (yoneda.obj T) :=
  D.toCoherentSituation.supportFactorizationLocus hπ (D.quotFamilyCohObject y)
    (D.isClosed_support_quotFamilyCohObject y)

/-- **The locus above which a quotient is supported in `X` is an open subspace**, the support
being proper over the test scheme (Stacks 0DNA, the open locus). -/
theorem isOpenSubspace_supportLocus (hπ : π ≫ D.f = bX) (hopen : IsOpenImmersion B S hS π.hom)
    {T : BigFppfOver B S hS} (y : QuotFamilyOver D T) :
    IsOpenSubspace B S hS (D.supportLocus hπ y) :=
  D.toCoherentSituation.isOpenSubspace_supportFactorizationLocus hπ hopen _ _

/-- **A morphism of schemes of the site lies in the support locus exactly when the base change of
the quotient along it is supported in `X`.** -/
theorem mem_supportLocus_iff (hπ : π ≫ D.f = bX) (hopen : IsOpenImmersion B S hS π.hom)
    {T U : BigFppfOver B S hS} (y : QuotFamilyOver D T) (g : U ⟶ T) :
    g ∈ (D.supportLocus hπ y).obj (Opposite.op U) ↔
      D.IsSupportedIn hπ (CostructuredArrow.mk (y.baseChange g).toBase)
        (y.baseChange g).subobject := by
  have hTalg : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hU := D.isClosed_support_quotFamilyCohObject y
  have hL : g ∈ (D.supportLocus hπ y).obj (Opposite.op U) ↔
      ∀ u : points B S hS (yoneda.obj U),
        ∀ z : points B S hS (D.quotFamilySupportSubspace y).toFunctor,
        pointsMap B S hS _ ((D.quotFamilySupportSubspace y).ι ≫
            (D.projection (CostructuredArrow.mk y.toBase)).hom) z =
            pointsMap B S hS _ (yoneda.map g) u →
          pointsMap B S hS _ (baseChangeProjection D.f (CostructuredArrow.mk y.toBase)).hom
              (pointsMap B S hS _ (D.quotFamilySupportSubspace y).ι z) ∈
            Set.range (pointsMap B S hS X.1 π.hom) := by
    rw [Subfunctor.mem_yoneda_iff,
      factorsThrough_openSubspace_iff_points B S hS hTalg hUalg (D.supportLocus hπ y)
        (D.isOpenSubspace_supportLocus hπ hopen y)]
    constructor
    · rintro hsub u z hz
      obtain ⟨w, hw⟩ := hsub ⟨u, rfl⟩
      have hmem := (D.toCoherentSituation.mem_supportFactorizationLocus_iff hπ _ hU _).1
        ⟨w, hw⟩ z hz
      exact (D.mem_range_baseChangeOfMap_iff hπ _ _).1 hmem
    · rintro hgood _ ⟨u, rfl⟩
      refine (D.toCoherentSituation.mem_supportFactorizationLocus_iff hπ _ hU _).2
        fun z hz => ?_
      exact (D.mem_range_baseChangeOfMap_iff hπ _ _).2 (hgood u z hz)
  have : (D.quotientModule (CostructuredArrow.mk y.toBase)
      y.subobject).IsFinitePresentationOnSite :=
    y.mem.1.2
  have hsupp : D.support (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ y.toBase))
      (D.quotientModule _ (D.quotientPullback (QuotFamilyOver.restrict g y.toBase) y.subobject)) =
        pointsMap B S hS _ (D.relativeMap (QuotFamilyOver.restrict g y.toBase)).hom ⁻¹'
          D.support (CostructuredArrow.mk y.toBase)
            (D.quotientModule (CostructuredArrow.mk y.toBase) y.subobject) :=
    (supportOfSheaf_eq_of_iso B S hS _
      (D.quotientPullbackCokernelIso (QuotFamilyOver.restrict g y.toBase) y.subobject)).trans
      (supportOfSheaf_modulePullback_eq B S hS _ _ y.mem.1.1.1 inferInstance)
  have hZrange : Set.range (pointsMap B S hS _ (D.quotFamilySupportSubspace y).ι) =
      D.support (CostructuredArrow.mk y.toBase)
        (D.quotientModule (CostructuredArrow.mk y.toBase) y.subobject) :=
    range_pointsMap_ι_reducedClosedSubspace B S hS _ _ _ hU
  have sqY := isPullback_baseChangeMap D.f (QuotFamilyOver.restrict g y.toBase)
  have hprojY : (baseChangeMap D.f (QuotFamilyOver.restrict g y.toBase)).hom ≫
      (baseChangeProjection D.f (CostructuredArrow.mk y.toBase)).hom =
        (baseChangeProjection D.f
          (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ y.toBase))).hom :=
    congrArg (fun k => k.hom) (AlgebraicGeometry.Space.baseChangeMap_comp_projection D.f
      (QuotFamilyOver.restrict g y.toBase))
  show _ ↔ D.IsSupportedIn hπ
    (CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g ≫ y.toBase))
    (D.quotientPullback (QuotFamilyOver.restrict g y.toBase) y.subobject)
  rw [hL, IsSupportedIn, hsupp]
  constructor
  · intro hgood y' hy'
    refine (D.mem_range_baseChangeOfMap_iff hπ _ y').2 ?_
    obtain ⟨z, hz⟩ : pointsMap B S hS _
        (D.relativeMap (QuotFamilyOver.restrict g y.toBase)).hom y' ∈
          Set.range (pointsMap B S hS _ (D.quotFamilySupportSubspace y).ι) := by
      rwa [hZrange]
    have h1 := hgood (pointsMap B S hS _ (baseChangeInclusion D.f _).hom y') z (by
      rw [pointsMap_comp_apply, hz]
      exact pointsMap_apply_comm B S hS (congrArg (·.hom) sqY.w) y')
    rw [hz, ← pointsMap_comp_apply] at h1
    rwa [← hprojY]
  · intro hsub u z hz
    obtain ⟨y', hy', hu⟩ := exists_point_of_isPullback B S hS sqY
      (pointsMap B S hS _ (D.quotFamilySupportSubspace y).ι z) u
      (by rw [← pointsMap_comp_apply]; exact hz)
    have hmem : y' ∈ pointsMap B S hS _
        (D.relativeMap (QuotFamilyOver.restrict g y.toBase)).hom ⁻¹'
          D.support (CostructuredArrow.mk y.toBase)
            (D.quotientModule (CostructuredArrow.mk y.toBase) y.subobject) := by
      rw [Set.mem_preimage, show D.relativeMap (QuotFamilyOver.restrict g y.toBase) =
        baseChangeMap D.f (QuotFamilyOver.restrict g y.toBase) from rfl, hy', ← hZrange]
      exact ⟨z, rfl⟩
    have h1 := (D.mem_range_baseChangeOfMap_iff hπ _ y').1 (hsub hmem)
    rwa [← hprojY, pointsMap_comp_apply, hy'] at h1

end QuotSituation

end AlgebraicGeometry.Space

end
