module

public import StacksFrontier.AlgebraicGeometry.Quot.C1764Prereq.DualizingSheafOfComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveLocusOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperMorphismSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeHFace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.C1764Prereq.CounitBaseChange

/-!
# The locus where `f^*f_*𝓛 ⟶ 𝓛` fails to be surjective

Let `f : X ⟶ S` be a family of curves and `𝓛` a quasi-coherent `𝒪_X`-module of finite type. The
counit `u : f^*f_*𝓛 ⟶ 𝓛` is a map of quasi-coherent modules (`f_*𝓛` is quasi-coherent by
Stacks 03M9, its pullback by Stacks 03GA), so its cokernel `C` is quasi-coherent of finite type,
with closed support (Stacks 07TZ). Pullback being right exact, the pullback of `u` along
`a : P ⟶ X` is surjective exactly when no point of `P` maps into `Supp(C)`. The image
`Z = f(Supp(C))` is closed in `S` (Stacks 0CZG, `f` being proper), and:

* `u` is surjective over `f⁻¹(U)` exactly when `U ∩ Z = ∅`;
* `u` is surjective on a presentation of the fibre `X_s` exactly when `s ∉ Z`;
* so condition (2) of Stacks 0E6Y holds at `s` exactly when `s ∉ Z`.

Finally the support of `C` is compatible with a morphism of families over an étale morphism of
bases, the base change map being invertible in that case.

## Main definitions

* `AlgebraicGeometry.C1764Prereq.counitSituation`: the counit, as a situation of Stacks 083F.
* `AlgebraicGeometry.C1764Prereq.counitNonSurjectiveLocus`: the closed set `Z` above.

## Main results

* `AlgebraicGeometry.C1764Prereq.epi_modulePullback_map_iff_of_isPullback`.
* `AlgebraicGeometry.C1764Prereq.isClosed_counitNonSurjectiveLocus`.
* `AlgebraicGeometry.C1764Prereq.epi_fibre_iff_notMem`.
* `AlgebraicGeometry.C1764Prereq.isCounitSurjectiveAbove_iff_notMem`.
* `AlgebraicGeometry.C1764Prereq.mem_cokernelSupport_of_hom`.

## References

* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 0CZG](https://stacks.math.columbia.edu/tag/0CZG)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1764Prereq

open Space

attribute [local instance] Space.pointTopology

section Situation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : ModuleMapSituation.{u, u} B S hS)

/-- The support `Supp(Coker u)` of the cokernel of the map of a situation of Stacks 083F, as a
set of points of the source space. -/
abbrev cokernelSupport : Set (points B S hS D.X.1) :=
  supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj D.cokernelModule)

/-- **The pullback of `u` along `a : P ⟶ X` is surjective exactly when no point of `P` maps into
`Supp(Coker u)`.** Pullback is right exact, a module vanishes exactly when its support is empty,
and the support of the pullback of the quasi-coherent module of finite type `Coker u` is the
inverse image of its support (Stacks 07TZ, part (3)). -/
theorem epi_modulePullback_map_iff_forall_notMem (hG : SheafOfModules.IsFiniteTypeOnSite D.G)
    {P : AlgebraicSpaces B S hS} (a : P ⟶ D.X) :
    Epi ((modulePullback B S hS a).map D.u) ↔
      ∀ w, pointsMap B S hS P.1 a.hom w ∉ cokernelSupport D := by
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS a) :=
    (modulePullbackAdjunction B S hS a).leftAdjoint_preservesColimits
  rw [Preadditive.epi_iff_isZero_cokernel,
    (PreservesCokernel.iso (modulePullback B S hS a) D.u).symm.isZero_iff,
    ← supportOfSheaf_eq_empty_iff_isZero,
    supportOfSheaf_modulePullback_eq B S hS a D.cokernelModule D.isQuasicoherentOnSite_cokernel_u
      (D.isFiniteTypeOnSite_cokernelModule hG), Set.eq_empty_iff_forall_notMem]
  rfl

/-- **The pullback of `u` to a fibre product is surjective exactly when no point of
`Supp(Coker u)` lies over the image of the other factor** (Stacks 03H4). -/
theorem epi_modulePullback_map_iff_of_isPullback (hG : SheafOfModules.IsFiniteTypeOnSite D.G)
    {P : AlgebraicSpaces B S hS} {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : P ⟶ D.X}
    {b : P.1 ⟶ Z} {g : Z ⟶ D.Y.1} (sq : IsPullback a.hom b D.f.hom g) :
    Epi ((modulePullback B S hS a).map D.u) ↔
      ∀ x ∈ cokernelSupport D,
        pointsMap B S hS D.X.1 D.f.hom x ∉ Set.range (pointsMap B S hS Z g) := by
  rw [epi_modulePullback_map_iff_forall_notMem D hG a]
  constructor
  · rintro h x hx ⟨z, hz⟩
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS sq x z hz.symm
    exact h w (hw ▸ hx)
  · intro h w hw
    exact h _ hw ⟨pointsMap B S hS P.1 b w, (pointsMap_apply_comm B S hS sq.w w).symm⟩

/-- The points of the spectrum of the residue field at `t` map onto the single point `t`. -/
theorem range_pointsMap_yoneda_residueFieldMap (T : BigFppfOver B S hS)
    (t : (BigFppfOver.toScheme B S hS).obj T) :
    Set.range (pointsMap B S hS _ (yoneda.map (residueFieldMap B S hS T t
        (B.residueField_spec_contains T.left.property t)))) =
      pointsToScheme B S hS T ⁻¹' {t} := by
  ext w
  refine ⟨?_, fun hw => ?_⟩
  · rintro ⟨z, rfl⟩
    rw [Set.mem_preimage, pointsToScheme_pointsMap_yoneda, Set.mem_singleton_iff]
    exact Scheme.fromSpecResidueField_apply t _
  · obtain ⟨z, -⟩ := surjective_pointsToScheme B S hS (residueFieldObject B S hS T t
      (B.residueField_spec_contains T.left.property t))
      (Classical.arbitrary (Spec (.of (((BigFppfOver.toScheme B S hS).obj T).residueField t))))
    refine ⟨z, injective_pointsToScheme B S hS T ?_⟩
    rw [pointsToScheme_pointsMap_yoneda]
    exact (Scheme.fromSpecResidueField_apply t _).trans hw.symm

end Situation

section Family

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- For a family of curves `f : X ⟶ S` and a quasi-coherent `𝓛`, the module `f^*f_*𝓛` is
quasi-coherent: `f_*𝓛` is by Stacks 03M9 (`f` is quasi-compact and quasi-separated) and
pullback preserves quasi-coherence by Stacks 03GA. -/
theorem isQuasicoherentOnSite_pullback_pushforward (X : CurveFamily B hZ)
    (L : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (hL : L.IsQuasicoherentOnSite) :
    ((modulePullback B integerBase hZ X.toBase).obj
      ((modulePushforward B integerBase hZ X.toBase).obj L)).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase hZ X.toBase _
    (isQuasicoherentOnSite_modulePushforward_of_qcqs B integerBase hZ X.toBase
      X.finitePresentation.2.1 X.finitePresentation.2.2 L hL)

/-- The counit `f^*f_*𝓛 ⟶ 𝓛` of a family of curves, as a situation of Stacks 083F. -/
abbrev counitSituation (X : CurveFamily B hZ)
    (L : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (hL : L.IsQuasicoherentOnSite) : ModuleMapSituation.{u, u} B integerBase hZ :=
  ⟨X.total, schemeSpace X.base, X.toBase, _, L, isQuasicoherentOnSite_pullback_pushforward X L hL,
    hL, X.pushforwardCounit L⟩

/-- The set of points `s` of the base of a family of curves over which `f^*f_*𝓛 ⟶ 𝓛` fails to be
surjective: the image `f(Supp(Coker))` of the support of the cokernel, as a set of points of the
base scheme. -/
def counitNonSurjectiveLocus (X : CurveFamily B hZ)
    (L : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (hL : L.IsQuasicoherentOnSite) : Set ((BigFppfOver.toScheme B integerBase hZ).obj X.base) :=
  pointsToScheme B integerBase hZ X.base '' (counitSituation X L hL).cokernelSupportImage

/-- **The locus where `f^*f_*𝓛 ⟶ 𝓛` is not surjective is closed** (Stacks 0CZG): the support of
the cokernel is closed (Stacks 07TZ), hence proper over the base since `f` is proper, and its
image is closed. -/
theorem isClosed_counitNonSurjectiveLocus (X : CurveFamily B hZ)
    (L : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (hL : L.IsQuasicoherentOnSite) (hLft : SheafOfModules.IsFiniteTypeOnSite L) :
    IsClosed (counitNonSurjectiveLocus X L hL) := by
  have hf := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
    X.finitePresentation.1
  exact (isClosed_pointTopology_yoneda_iff_isClosed_image B integerBase hZ X.base _).1
    ((counitSituation X L hL).isClosed_cokernelSupportImage hf hLft
      (@hasProperSupport_toSheaf_of_isProper B integerBase hZ _ _ X.total.2 (schemeSpace X.base).2
        X.toBase.hom hf X.proper L hLft))

/-- The counit is surjective over `f⁻¹(U)` exactly when `U` misses the non-surjectivity locus. -/
theorem epi_preimageOpens_iff (X : CurveFamily B hZ)
    (L : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (hL : L.IsQuasicoherentOnSite) (hLft : SheafOfModules.IsFiniteTypeOnSite L)
    (U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens) :
    Epi ((modulePullback B integerBase hZ
      (openSubspaceHom B integerBase hZ (X.preimageOpens U)
        (X.isOpenSubspace_preimageOpens U))).map (X.pushforwardCounit L)) ↔
      ∀ z ∈ counitNonSurjectiveLocus X L hL, z ∉ U := by
  refine (epi_modulePullback_map_iff_of_isPullback (counitSituation X L hL) hLft
    (a := openSubspaceHom B integerBase hZ (X.preimageOpens U) (X.isOpenSubspace_preimageOpens U))
    (Subfunctor.isPullback_preimage X.toBase.hom
      (subspaceOfOpens B integerBase hZ X.base U)).flip).trans ?_
  have hr := Set.ext_iff.1 (range_pointsMap_subspaceOfOpens B integerBase hZ X.base U)
  constructor
  · rintro h _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ hU
    exact h x hx ((hr _).2 hU)
  · intro h x hx hU
    exact h _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ ((hr _).1 hU)

/-- The counit is surjective on a presentation of the fibre `X_s` exactly when `s` is not in the
non-surjectivity locus. -/
theorem epi_fibre_iff_notMem (X : CurveFamily B hZ)
    (L : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (hL : L.IsQuasicoherentOnSite) (hLft : SheafOfModules.IsFiniteTypeOnSite L)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) {V : BigFppfOver B integerBase hZ}
    {v : V ⟶ CurveFamily.residuePoint B hZ X s} {q : yoneda.obj V ⟶ X.total.obj}
    (hq : CurveFamily.IsFibrePresentation B hZ X s v q) :
    Epi ((modulePullback B integerBase hZ
        (ObjectProperty.homMk q : schemeSpace V ⟶ X.total)).map (X.pushforwardCounit L)) ↔
      s ∉ counitNonSurjectiveLocus X L hL := by
  refine (epi_modulePullback_map_iff_of_isPullback (counitSituation X L hL) hLft
    (a := (ObjectProperty.homMk q : schemeSpace V ⟶ X.total)) hq).trans ?_
  have hr := Set.ext_iff.1 (range_pointsMap_yoneda_residueFieldMap X.base s)
  constructor
  · rintro h ⟨_, ⟨x, hx, rfl⟩, hxs⟩
    exact h x hx ((hr _).2 hxs)
  · intro h x hx hxs
    exact h ⟨_, ⟨x, hx, rfl⟩, (hr _).1 hxs⟩

/-- **Condition (2) of Stacks 0E6Y at `s` is `s ∉ f(Supp(Coker))`**: the locus is closed, so its
complement is an open neighbourhood of `s` over which the counit is surjective. -/
theorem isCounitSurjectiveAbove_iff_notMem (X : CurveFamily B hZ)
    (L : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (hL : L.IsQuasicoherentOnSite) (hLft : SheafOfModules.IsFiniteTypeOnSite L)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) :
    X.IsCounitSurjectiveAbove L s ↔ s ∉ counitNonSurjectiveLocus X L hL := by
  constructor
  · rintro ⟨U, hsU, hU⟩ hs
    exact (epi_preimageOpens_iff X L hL hLft U).1 hU s hs hsU
  · intro hs
    refine ⟨⟨_, (isClosed_counitNonSurjectiveLocus X L hL hLft).isOpen_compl⟩, hs,
      (epi_preimageOpens_iff X L hL hLft _).2 fun z hz hzU => hzU hz⟩

/-- **The support of the cokernel of the counit is compatible with étale base change.** For a
morphism `φ : X' ⟶ X` of families of curves over an étale morphism of bases, a point of `X'`
whose image in `X` lies in the support of `Coker(f^*f_*𝓛 ⟶ 𝓛)` lies in the support of
`Coker(f'^*f'_*φ^*𝓛 ⟶ φ^*𝓛)`: the base change map `g^*f_*𝓛 ⟶ f'_*φ^*𝓛` is invertible (Stacks
03LX, étale case), so the pullback of the counit of `X` is, up to an isomorphism of sources, the
counit of `X'`, and the cokernel of the former is the pullback of the cokernel. -/
theorem mem_cokernelSupport_of_hom {X X' : CurveFamily B hZ} (φ : X' ⟶ X)
    (hφ : Etale ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap))
    (L : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (hL : L.IsQuasicoherentOnSite) (hLft : SheafOfModules.IsFiniteTypeOnSite L)
    (hL' : ((modulePullback B integerBase hZ φ.totalMap).obj L).IsQuasicoherentOnSite)
    (x' : points B integerBase hZ X'.total.1)
    (hx : pointsMap B integerBase hZ X'.total.1 φ.totalMap.hom x' ∈
      cokernelSupport (counitSituation X L hL)) :
    x' ∈ cokernelSupport (counitSituation X' ((modulePullback B integerBase hZ φ.totalMap).obj L)
      hL') := by
  have hg : IsEtale B integerBase hZ (schemeSpaceMap φ.baseMap).hom :=
    isEtale_of_presheaf_etale B integerBase hZ
      ((presheaf_yoneda_map_etale_iff B integerBase hZ φ.baseMap).2 hφ)
  have hβ := isIso_moduleBaseChangeMap_of_isEtale B integerBase hZ φ.totalMap X'.toBase X.toBase
    (schemeSpaceMap φ.baseMap) φ.cartesian hg
  have h := modulePullback_map_counit_eq X.toBase (schemeSpaceMap φ.baseMap) X'.toBase φ.totalMap
    φ.cartesian.w L
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B integerBase hZ φ.totalMap) :=
    (modulePullbackAdjunction B integerBase hZ φ.totalMap).leftAdjoint_preservesColimits
  have ha : Epi ((modulePullbackSquareComparison X.toBase (schemeSpaceMap φ.baseMap) X'.toBase
      φ.totalMap φ.cartesian.w).hom.app ((modulePushforward B integerBase hZ X.toBase).obj L)) :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom ((modulePullbackSquareComparison X.toBase
      (schemeSpaceMap φ.baseMap) X'.toBase φ.totalMap φ.cartesian.w).app _))
  have hb : Epi ((modulePullback B integerBase hZ X'.toBase).map ((moduleBaseChangeMap X.toBase
      (schemeSpaceMap φ.baseMap) X'.toBase φ.totalMap φ.cartesian.w).app L)) :=
    @IsIso.epi_of_iso _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _
      (@NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hβ L))
  have e := PreservesCokernel.iso (modulePullback B integerBase hZ φ.totalMap)
      (X.pushforwardCounit L) ≪≫ cokernelIsoOfEq h ≪≫ @cokernelEpiComp _ _ _ _ _ _ _ _ ha _ ≪≫
    @cokernelEpiComp _ _ _ _ _ _ _ _ hb _
  have h₁ := supportOfSheaf_eq_of_iso B integerBase hZ X'.total e
  have h₂ := supportOfSheaf_modulePullback_eq B integerBase hZ φ.totalMap _
    (counitSituation X L hL).isQuasicoherentOnSite_cokernel_u
    ((counitSituation X L hL).isFiniteTypeOnSite_cokernelModule hLft)
  have hx' : x' ∈ supportOfSheaf B integerBase hZ X'.total.1 ((SheafOfModules.toSheaf _).obj
      ((modulePullback B integerBase hZ φ.totalMap).obj
        (counitSituation X L hL).cokernelModule)) := h₂.symm ▸ hx
  exact h₁.subst (motive := fun T => x' ∈ T) hx'

end Family

end AlgebraicGeometry.C1764Prereq
