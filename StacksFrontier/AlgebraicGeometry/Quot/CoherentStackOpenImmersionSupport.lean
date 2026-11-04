module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSurjectiveOnPointsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetOpenPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence

/-!
# Supports along an open immersion, for the stacks of coherent sheaves

Let `B` be an algebraic space and let `π : X ⟶ Y` be an open immersion of algebraic spaces over
`B`, with `Y ⟶ B` the standing datum of Stacks 08KB.  For a test scheme `T` over `B` write
`π_T : X_T ⟶ Y_T` for the base change, again an open immersion.  This file proves the facts about
supports that identify the image of `Coh_{X/B} ⟶ Coh_{Y/B}`, the morphism of Stacks 0DN9, with
the objects of `Coh_{Y/B}` whose module is supported in `X_T`, and that make that condition open
on the base.

* **Direct images land in `X_T`.**  For a quasi-coherent `𝒪_{X_T}`-module `F` whose support is
  proper over `T`, the support of `π_{T,*}F` lies in `|X_T|`, provided `Y ⟶ B` is separated: the
  image of `Supp(F)` in `|Y_T|` is then closed (Stacks 0CZG) and the support of a direct image lies
  in any closed set containing the image of the support.
* **Restrictions are objects of `Coh_{X/B}`.**  For an object `(T, G)` of `Coh_{Y/B}` with
  `Supp(G) ⊆ |X_T|`, the restriction `π_T^*G` is quasi-coherent, of finite presentation, flat
  over `T` — `π_T` being flat — and its support `π_T⁻¹(Supp G)` is proper over `T`: the base
  change of the reduced induced subspace on `Supp(G)` along `π_T` is an open immersion surjective
  on points, hence an isomorphism, so it is proper over `T`.  The unit `G ⟶ π_{T,*}π_T^*G` is an
  isomorphism.
* **The locus is read on points.**  For a morphism `h : T' ⟶ T` of test schemes, `|T'|` maps into
  the locus `{t ∈ |T| : Supp(G) ∩ |Y_t| ⊆ |X_t|}` exactly when the support of the inverse image
  of `G` on `Y_{T'}` lies in `|X_{T'}|`.  This is Stacks 07TZ for the support of an inverse image
  and Stacks 03H4 for the points of the two cartesian squares involved.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.supportOfSheaf_modulePushforward_subset_range`: the
  support of a direct image lies in `|X_T|`.
* `AlgebraicGeometry.Space.CoherentSituation.isFlatOver_modulePullback_baseChangeOfMap`,
  `CoherentSituation.isProperOver_supportOfSheaf_modulePullback_baseChangeOfMap`,
  `CoherentSituation.isIso_unit_baseChangeOfMap`: the restriction of a module supported in `X_T`
  is flat over `T` with support proper over `T`, and the module is the direct image of its
  restriction.
* `AlgebraicGeometry.Space.CoherentSituation.range_subset_supportLocus_iff`: the locus read on
  points along a morphism of test schemes.
* `AlgebraicGeometry.Space.CoherentSituation.isOpen_supportLocus`: the locus is open.

## References

* [Stacks Project, Tag 0DNA](https://stacks.math.columbia.edu/tag/0DNA)
* [Stacks Project, Tag 0DN9](https://stacks.math.columbia.edu/tag/0DN9)
* [Stacks Project, Tag 0CZG](https://stacks.math.columbia.edu/tag/0CZG)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

variable (D : CoherentSituation B S hS) {X : AlgebraicSpaces B S hS}
    {π : X ⟶ D.X} {bX : X ⟶ D.Y}

/-! ### The base change of a separated morphism -/

/-- The projection `Y_T ⟶ T` is separated when `Y ⟶ B` is (Stacks 03KL). -/
theorem isSeparated_projection (hsep : IsSeparated B S hS D.f.hom) (T : SchemesOver D.Y) :
    IsSeparated B S hS (D.projection T).hom :=
  isSeparated_pullback B S hS D.f.hom T.hom.hom hsep

/-- The map on points of a composite of morphisms of algebraic spaces, for a given composite. -/
private theorem pointsMap_hom_comp_apply {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y ⟶ Z}
    {k : X ⟶ Z} (hfg : f ≫ g = k) (w : points B S hS X.1) :
    pointsMap B S hS Y.1 g.hom (pointsMap B S hS X.1 f.hom w) = pointsMap B S hS X.1 k.hom w := by
  subst hfg
  exact (pointsMap_comp_apply B S hS _ _ w).symm

/-! ### The support of a direct image -/

/-- **The support of a direct image along `π_T` lies in `|X_T|`.**  For an `𝒪_{X_T}`-module `F`
whose support is closed and proper over `T`, and `Y ⟶ B` separated, the support of `π_{T,*}F` is
contained in the image of `|X_T|`. -/
theorem supportOfSheaf_modulePushforward_subset_range (hπ : π ≫ D.f = bX)
    (hsep : IsSeparated B S hS D.f.hom) (T : SchemesOver D.Y)
    (F : Modules.{u, u} B S hS (baseChangeSpace bX T).1 (baseChangeSpace bX T).2)
    (hpX : IsLocallyOfFiniteType B S hS (baseChangeInclusion bX T).hom)
    (hpY : IsLocallyOfFiniteType B S hS (D.projection T).hom)
    (hU : IsClosed (supportOfSheaf B S hS (baseChangeSpace bX T).1
      ((SheafOfModules.toSheaf _).obj F)))
    (hproper : IsProperOver B S hS (baseChangeSpace bX T).2
      ((schemeSpaceFunctor B S hS).obj T.left).2 (baseChangeInclusion bX T).hom hpX
      (supportOfSheaf B S hS (baseChangeSpace bX T).1 ((SheafOfModules.toSheaf _).obj F)) hU) :
    supportOfSheaf B S hS (D.space T).1 ((SheafOfModules.toSheaf _).obj
        ((modulePushforward B S hS (baseChangeOfMap D hπ T)).obj F)) ⊆
      Set.range (pointsMap B S hS (baseChangeSpace bX T).1 (baseChangeOfMap D hπ T).hom) :=
  supportOfSheaf_modulePushforward_subset_range_of_isClosed_image B S hS _ F
    (isClosed_image_of_isProperOver B S hS (baseChangeSpace bX T).2 (D.space T).2
      ((schemeSpaceFunctor B S hS).obj T.left).2 (baseChangeOfMap D hπ T).hom
      (baseChangeInclusion bX T).hom (D.projection T).hom
      (congrArg (fun m => m.hom) (baseChangeOfMap_comp_inclusion D hπ T))
      hpX hpY (isSeparated_projection D hsep T) _ hU hproper)

/-! ### The restriction of a module supported in `X_T` -/

section Restriction

variable (hπ : π ≫ D.f = bX) (hopen : IsOpenImmersion B S hS π.hom) (T : SchemesOver D.Y)
  (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)

include hopen in
/-- **The restriction of a module flat over `T` is flat over `T`**, the open immersion `π_T`
being flat. -/
theorem isFlatOver_modulePullback_baseChangeOfMap [G.IsQuasicoherentOnSite]
    (hflat : IsFlatOver B S hS (D.space T).2 (D.projection T).hom G) :
    IsFlatOver B S hS (baseChangeSpace bX T).2 (baseChangeInclusion bX T).hom
      ((modulePullback B S hS (baseChangeOfMap D hπ T)).obj G) := by
  have : ((modulePullback B S hS (baseChangeOfMap D hπ T)).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ G inferInstance
  rw [isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS (D.projection T) G] at hflat
  rw [← baseChangeOfMap_comp_inclusion D hπ T, isFlatOver_iff_forall_isFlatOverAtGeometricPoint
    B S hS (baseChangeOfMap D hπ T ≫ D.projection T)]
  exact fun xbar ↦ (isFlatOverAtGeometricPoint_modulePullback_iff_of_isFlatAt B S hS
    (baseChangeOfMap D hπ T) (D.projection T) G xbar (isFlatAt_of_isFlat B S hS _
      (isFlat_of_isEtale B S hS (isEtale_of_isOpenImmersion B S hS
        (isOpenImmersion_baseChangeOfMap D hπ hopen T))) xbar.image)).mp (hflat _)

/-- **The support of the restriction is the inverse image of the support** (Stacks 07TZ), for a
quasi-coherent module of finite type. -/
theorem supportOfSheaf_modulePullback_baseChangeOfMap [G.IsQuasicoherentOnSite]
    [SheafOfModules.IsFiniteTypeOnSite G] :
    supportOfSheaf B S hS (baseChangeSpace bX T).1 ((SheafOfModules.toSheaf _).obj
        ((modulePullback B S hS (baseChangeOfMap D hπ T)).obj G)) =
      pointsMap B S hS (baseChangeSpace bX T).1 (baseChangeOfMap D hπ T).hom ⁻¹'
        supportOfSheaf B S hS (D.space T).1 ((SheafOfModules.toSheaf _).obj G) :=
  supportOfSheaf_modulePullback_eq B S hS _ G inferInstance inferInstance

include hopen in
/-- **The support of the restriction of a module supported in `X_T` is proper over `T`.**  If the
support of `G` is closed, proper over `T` and contained in `|X_T|`, then the support of `π_T^*G`
— its inverse image in `|X_T|` — is proper over `T`. -/
theorem isProperOver_supportOfSheaf_modulePullback_baseChangeOfMap [G.IsQuasicoherentOnSite]
    [SheafOfModules.IsFiniteTypeOnSite G]
    (hpY : IsLocallyOfFiniteType B S hS (D.projection T).hom)
    (hpX : IsLocallyOfFiniteType B S hS (baseChangeInclusion bX T).hom)
    (hU : IsClosed (supportOfSheaf B S hS (D.space T).1 ((SheafOfModules.toSheaf _).obj G)))
    (hproper : IsProperOver B S hS (D.space T).2 ((schemeSpaceFunctor B S hS).obj T.left).2
      (D.projection T).hom hpY
      (supportOfSheaf B S hS (D.space T).1 ((SheafOfModules.toSheaf _).obj G)) hU)
    (hsupp : supportOfSheaf B S hS (D.space T).1 ((SheafOfModules.toSheaf _).obj G) ⊆
      Set.range (pointsMap B S hS (baseChangeSpace bX T).1 (baseChangeOfMap D hπ T).hom))
    (hU' : IsClosed (supportOfSheaf B S hS (baseChangeSpace bX T).1
      ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS (baseChangeOfMap D hπ T)).obj G)))) :
    IsProperOver B S hS (baseChangeSpace bX T).2 ((schemeSpaceFunctor B S hS).obj T.left).2
      (baseChangeInclusion bX T).hom hpX
      (supportOfSheaf B S hS (baseChangeSpace bX T).1 ((SheafOfModules.toSheaf _).obj
        ((modulePullback B S hS (baseChangeOfMap D hπ T)).obj G))) hU' := by
  have hcomp : (baseChangeOfMap D hπ T).hom ≫ (D.projection T).hom =
      (baseChangeInclusion bX T).hom :=
    congrArg (fun m => m.hom) (baseChangeOfMap_comp_inclusion D hπ T)
  have key := isProperOver_preimage_of_isOpenImmersion B S hS (baseChangeSpace bX T).2
    (D.space T).2 ((schemeSpaceFunctor B S hS).obj T.left).2 (baseChangeOfMap D hπ T).hom
    (D.projection T).hom (isOpenImmersion_baseChangeOfMap D hπ hopen T) (hcomp ▸ hpX) hpY _ hU
    hsupp hproper
  have transport : ∀ (q : (baseChangeSpace bX T).1 ⟶ ((schemeSpaceFunctor B S hS).obj T.left).1)
      (hq : IsLocallyOfFiniteType B S hS q)
      (Z : Set (points B S hS (baseChangeSpace bX T).1)) (hZ : IsClosed Z),
      q = (baseChangeOfMap D hπ T).hom ≫ (D.projection T).hom →
      Z = pointsMap B S hS (baseChangeSpace bX T).1 (baseChangeOfMap D hπ T).hom ⁻¹'
        supportOfSheaf B S hS (D.space T).1 ((SheafOfModules.toSheaf _).obj G) →
      IsProperOver B S hS (baseChangeSpace bX T).2 ((schemeSpaceFunctor B S hS).obj T.left).2
        q hq Z hZ := by
    rintro _ _ _ _ rfl rfl
    exact key
  exact transport _ hpX _ hU' hcomp.symm
    (supportOfSheaf_modulePullback_baseChangeOfMap D hπ T G)

include hopen in
/-- **A module supported in `X_T` is the direct image of its restriction.**  If the support of
`G` is closed and contained in `|X_T|`, the unit `G ⟶ π_{T,*}π_T^*G` is an isomorphism. -/
theorem isIso_unit_baseChangeOfMap
    (hU : IsClosed (supportOfSheaf B S hS (D.space T).1 ((SheafOfModules.toSheaf _).obj G)))
    (hsupp : supportOfSheaf B S hS (D.space T).1 ((SheafOfModules.toSheaf _).obj G) ⊆
      Set.range (pointsMap B S hS (baseChangeSpace bX T).1 (baseChangeOfMap D hπ T).hom)) :
    IsIso ((modulePullbackAdjunction B S hS (baseChangeOfMap D hπ T)).unit.app G) :=
  isIso_modulePullbackAdjunction_unit_of_supportOfSheaf_subset B S hS _
    (isOpenImmersion_baseChangeOfMap D hπ hopen T) G hU hsupp

end Restriction

/-! ### The locus above which a module is supported in `X_T` -/

/-- The base change of `π` commutes with the morphisms of base changes induced by a morphism of
test schemes: `π_{T'} ≫ Y_h = X_h ≫ π_T`. -/
@[reassoc]
theorem baseChangeOfMap_comp_relativeMap (hπ : π ≫ D.f = bX) {T' T : SchemesOver D.Y}
    (h : T' ⟶ T) :
    baseChangeOfMap D hπ T' ≫ D.relativeMap h = baseChangeMap bX h ≫ baseChangeOfMap D hπ T := by
  refine baseChange_hom_ext D.f ?_ ?_
  · simp [Category.assoc]
  · simp only [Category.assoc, baseChangeMap_comp_inclusion, baseChangeOfMap_comp_inclusion_assoc,
      baseChangeOfMap_comp_inclusion]

/-- **The locus `{t ∈ |T| : Supp(G) ∩ |Y_t| ⊆ |X_t|}`**: the points of `T` above which every point
of the support of the `𝒪_{Y_T}`-module `G` lies in `|X_T|`. -/
def supportLocus (hπ : π ≫ D.f = bX) (T : SchemesOver D.Y)
    (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :
    Set (points B S hS ((schemeSpaceFunctor B S hS).obj T.left).1) :=
  {t | ∀ y ∈ supportOfSheaf B S hS (D.space T).1 ((SheafOfModules.toSheaf _).obj G),
    pointsMap B S hS (D.space T).1 (D.projection T).hom y = t →
      y ∈ Set.range (pointsMap B S hS (baseChangeSpace bX T).1 (baseChangeOfMap D hπ T).hom)}

/-- The locus is the whole of `|T|` when the support lies in `|X_T|`. -/
theorem supportLocus_eq_univ (hπ : π ≫ D.f = bX) (T : SchemesOver D.Y)
    (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (hsupp : supportOfSheaf B S hS (D.space T).1 ((SheafOfModules.toSheaf _).obj G) ⊆
      Set.range (pointsMap B S hS (baseChangeSpace bX T).1 (baseChangeOfMap D hπ T).hom)) :
    supportLocus D hπ T G = Set.univ :=
  Set.eq_univ_of_forall fun _ _ hy _ ↦ hsupp hy

/-- The locus is the set of points of the open subspace
`AlgebraicGeometry.Space.CoherentSituation.supportFactorizationLocus`. -/
theorem range_pointsMap_ι_supportFactorizationLocus (hπ : π ≫ D.f = bX)
    (A : CoherentObject D) (hU : IsClosed (D.support A.T A.F)) :
    Set.range (pointsMap B S hS (supportFactorizationLocus D hπ A hU).toFunctor
        (supportFactorizationLocus D hπ A hU).ι) = supportLocus D hπ A.T A.F := by
  ext t
  rw [mem_supportFactorizationLocus_iff]
  constructor
  · intro h y hy hyt
    obtain ⟨z, rfl⟩ : y ∈ Set.range (pointsMap B S hS (supportSubspace D A hU).toFunctor
        (supportSubspace D A hU).ι) := by
      rwa [range_pointsMap_ι_reducedClosedSubspace]
    exact h z (by rwa [pointsMap_comp])
  · intro h z hz
    exact h _ ((range_pointsMap_ι_reducedClosedSubspace B S hS (D.space A.T).1 (D.space A.T).2 _
      hU).subset ⟨z, rfl⟩) (by rwa [pointsMap_comp] at hz)

/-- **The locus is open** (the hint of Stacks 0DNA): it is the set of points of an open
subspace of `T`. -/
theorem isOpen_supportLocus (hπ : π ≫ D.f = bX) (hopen : IsOpenImmersion B S hS π.hom)
    (A : CoherentObject D) : IsOpen (supportLocus D hπ A.T A.F) := by
  rw [← range_pointsMap_ι_supportFactorizationLocus D hπ A (isClosed_support D A)]
  exact isOpen_range_pointsMap_of_isOpenImmersion B S hS _
    (isOpenSubspace_supportFactorizationLocus D hπ hopen A (isClosed_support D A)).2

/-- **`X_{T'}` is the inverse image of `X_T` in `Y_{T'}`, on points.**  For a morphism
`h : T' ⟶ T` of test schemes over `B`, a point of `Y_{T'}` whose image in `Y_T` lies in `|X_T|`
lies in `|X_{T'}|`: `X_{T'}` is the fibre product of `Y_{T'}` and `X` over `Y`, so Stacks 03H4
applies. -/
theorem preimage_range_baseChangeOfMap_subset (hπ : π ≫ D.f = bX) {T' T : SchemesOver D.Y}
    (h : T' ⟶ T) :
    pointsMap B S hS (D.space T').1 (D.relativeMap h).hom ⁻¹'
        Set.range (pointsMap B S hS (baseChangeSpace bX T).1 (baseChangeOfMap D hπ T).hom) ⊆
      Set.range (pointsMap B S hS (baseChangeSpace bX T').1 (baseChangeOfMap D hπ T').hom) := by
  rintro w ⟨x₀, hx₀⟩
  have hpt : pointsMap B S hS (D.space T').1 (baseChangeProjection D.f T').hom w =
      pointsMap B S hS X.1 π.hom
        (pointsMap B S hS (baseChangeSpace bX T).1 (baseChangeProjection bX T).hom x₀) := by
    have e1 : pointsMap B S hS (D.space T').1 (baseChangeProjection D.f T').hom w =
        pointsMap B S hS (D.space T).1 (baseChangeProjection D.f T).hom
          (pointsMap B S hS (D.space T').1 (D.relativeMap h).hom w) := by
      rw [pointsMap_hom_comp_apply (baseChangeMap_comp_projection D.f h)]
    rw [e1, ← hx₀, pointsMap_hom_comp_apply (baseChangeOfMap_comp_projection D hπ T)]
    exact (pointsMap_hom_comp_apply rfl x₀).symm
  obtain ⟨x, hx, -⟩ :=
    exists_point_of_isPullback_presheaf B S hS (isPullback_baseChangeOfMap D hπ T') w _ hpt
  exact ⟨x, hx⟩

/-- **The locus read on points along a morphism of test schemes.**  For a morphism
`h : T' ⟶ T` of test schemes over `B` and an `𝒪_{Y_T}`-module `G`, the image of `|T'|` lies in
the locus of `G` exactly when the inverse image under `Y_h : Y_{T'} ⟶ Y_T` of the support of `G`
lies in `|X_{T'}|`. -/
theorem range_subset_supportLocus_iff (hπ : π ≫ D.f = bX) {T' T : SchemesOver D.Y}
    (h : T' ⟶ T) (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :
    Set.range (pointsMap B S hS ((schemeSpaceFunctor B S hS).obj T'.left).1
        ((schemeSpaceFunctor B S hS).map h.left).hom) ⊆ supportLocus D hπ T G ↔
      pointsMap B S hS (D.space T').1 (D.relativeMap h).hom ⁻¹'
          supportOfSheaf B S hS (D.space T).1 ((SheafOfModules.toSheaf _).obj G) ⊆
        Set.range (pointsMap B S hS (baseChangeSpace bX T').1
          (baseChangeOfMap D hπ T').hom) := by
  have hproj : ∀ w, pointsMap B S hS (D.space T).1 (D.projection T).hom
      (pointsMap B S hS (D.space T').1 (D.relativeMap h).hom w) =
        pointsMap B S hS _ ((schemeSpaceFunctor B S hS).map h.left).hom
          (pointsMap B S hS (D.space T').1 (D.projection T').hom w) := by
    intro w
    rw [pointsMap_hom_comp_apply (f := D.projection T')
      (g := (schemeSpaceFunctor B S hS).map h.left) rfl]
    exact pointsMap_hom_comp_apply (f := D.relativeMap h) (g := D.projection T)
      (baseChangeMap_comp_inclusion D.f h) w
  have hcompat : ∀ x, pointsMap B S hS (D.space T').1 (D.relativeMap h).hom
      (pointsMap B S hS (baseChangeSpace bX T').1 (baseChangeOfMap D hπ T').hom x) =
        pointsMap B S hS (baseChangeSpace bX T).1 (baseChangeOfMap D hπ T).hom
          (pointsMap B S hS (baseChangeSpace bX T').1 (baseChangeMap bX h).hom x) := by
    intro x
    rw [pointsMap_hom_comp_apply (baseChangeOfMap_comp_relativeMap D hπ h),
      pointsMap_hom_comp_apply rfl]
  constructor
  · intro hsub w hw
    exact preimage_range_baseChangeOfMap_subset D hπ h
      (hsub ⟨pointsMap B S hS (D.space T').1 (D.projection T').hom w, rfl⟩ _ hw (hproj w))
  · rintro hsub _ ⟨t', rfl⟩ y hy hyt
    obtain ⟨w, hw, hwt⟩ :=
      exists_point_of_isPullback B S hS (isPullback_baseChangeMap D.f h) y t' hyt
    obtain ⟨x, rfl⟩ := hsub (show w ∈ _ by rwa [Set.mem_preimage, hw])
    exact ⟨_, (hcompat x).symm.trans hw⟩

end CoherentSituation

end AlgebraicGeometry.Space

end
