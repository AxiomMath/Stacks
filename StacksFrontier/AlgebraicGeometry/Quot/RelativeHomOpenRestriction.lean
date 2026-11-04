module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHomOpenSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectDirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitFlatProperSupport
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionLiftAndCompactNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperClosedSubsetOpenPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModuleConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# Shrinking the source of the relative Hom functor to a neighbourhood of the support

In Situation 08JT let `j : U ⟶ X` be an open immersion whose image contains the support of `G`
(of finite type).  Then `Hom(F, G) = Hom(F|_U, G|_U)` as functors on the test schemes over the
base: for every test scheme `T`, the base change `U_T ⟶ X_T` is an open immersion whose image
contains the support of `G_T`, and homomorphisms into `G_T` are determined by, and glue from,
their restrictions to `U_T`.

This is the first sentence of the proof of Stacks 08JY: "We may replace `X` by a quasi-compact
open neighbourhood of the support of `𝒢`".

## Main definitions

* `AlgebraicGeometry.Space.HomSituation.restrictSource`: the situation `(U ⟶ base, j^*F, j^*G)`.
* `AlgebraicGeometry.Space.HomSituation.restrictSourceMap`: restriction of homomorphisms, as a
  morphism of relative Hom functors, natural in the test scheme by construction.

## Main results

* `AlgebraicGeometry.Space.HomSituation.isIso_restrictSourceMap`: restriction to an open
  subspace containing the support of `G` is an isomorphism of relative Hom functors.
* `AlgebraicGeometry.Space.HomSituation.restrictSourceIso`: the same as an isomorphism.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.HomSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (s : HomSituation B S hS)

/-- **The situation restricted along `j : U ⟶ X`**: the morphism `j ≫ f : U ⟶ base` and the two
pulled-back modules, quasi-coherent by Stacks 03GA. -/
def restrictSource {U : AlgebraicSpaces B S hS} (j : U ⟶ s.X) : HomSituation B S hS where
  X := U
  base := s.base
  f := j ≫ s.f
  F := (modulePullback B S hS j).obj s.F
  G := (modulePullback B S hS j).obj s.G
  quasicoherent_F :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS j s.F s.quasicoherent_F
  quasicoherent_G :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS j s.G s.quasicoherent_G

/-- **Restriction of homomorphisms along `j : U ⟶ X`**, as a morphism of relative Hom functors:
pullback along the base changes `U_T ⟶ X_T`, read through the comparison of Stacks 03LU of the
iterated pullbacks.  Its naturality in the test scheme is that of
`AlgebraicGeometry.Space.baseChangeSourceOver` and of
`AlgebraicGeometry.Space.moduleHomOverPullback`. -/
def restrictSourceMap (hc : ModulePushforwardCoherence B S hS) {U : AlgebraicSpaces B S hS}
    (j : U ⟶ s.X) : s.homFunctor hc ⟶ (s.restrictSource j).homFunctor hc :=
  Functor.whiskerRight (NatTrans.op (baseChangeSourceOver s.f j)) (moduleHomOver hc s.F s.G) ≫
    Functor.whiskerLeft (baseChangeOver (j ≫ s.f)).op (moduleHomOverPullback hc j s.F s.G).inv

/-- The base change `U_T ⟶ X_T` of an open immersion `j` is an open immersion. -/
theorem isOpenImmersion_baseChangeSourceMap {U : AlgebraicSpaces B S hS} (j : U ⟶ s.X)
    (hj : IsOpenImmersion B S hS j.hom) (T : s.SchemesOver) :
    IsOpenImmersion B S hS (baseChangeSourceMap s.f j T).hom :=
  isOpenImmersion_of_isPullback B S hS (isPullback_baseChangeSourceMap s.f j T).flip hj

/-- The support of `G_T` lies in the image of `U_T ⟶ X_T` when the support of `G` lies in the
image of `j`. -/
theorem supportOfSheaf_baseChange_subset_range {U : AlgebraicSpaces B S hS} (j : U ⟶ s.X)
    (hGft : SheafOfModules.IsFiniteTypeOnSite s.G)
    (hsupp : supportOfSheaf B S hS s.X.1 ((SheafOfModules.toSheaf _).obj s.G) ⊆
      Set.range (pointsMap B S hS U.1 j.hom)) (T : s.SchemesOver) :
    supportOfSheaf B S hS (s.baseChange T).1
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS (s.projection T)).obj s.G)) ⊆
      Set.range (pointsMap B S hS (baseChangeSpace (j ≫ s.f) T).1
        (baseChangeSourceMap s.f j T).hom) := by
  intro x hx
  obtain ⟨y, hy⟩ := hsupp (supportOfSheaf_modulePullback_subset B S hS (s.projection T) s.G hGft hx)
  obtain ⟨w, hw, -⟩ := exists_point_of_isPullback B S hS (isPullback_baseChangeSourceMap s.f j T)
    x y hy.symm
  exact ⟨w, hw⟩

/-- **Restriction to an open subspace containing the support of `G` is an isomorphism of
relative Hom functors.** -/
theorem isIso_restrictSourceMap (hc : ModulePushforwardCoherence B S hS)
    {U : AlgebraicSpaces B S hS} (j : U ⟶ s.X) (hj : IsOpenImmersion B S hS j.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite s.G)
    (hsupp : supportOfSheaf B S hS s.X.1 ((SheafOfModules.toSheaf _).obj s.G) ⊆
      Set.range (pointsMap B S hS U.1 j.hom)) :
    IsIso (s.restrictSourceMap hc j) := by
  have h1 : IsIso (Functor.whiskerRight (NatTrans.op (baseChangeSourceOver s.f j))
      (moduleHomOver hc s.F s.G)) := by
    have (T : s.SchemesOverᵒᵖ) : IsIso ((Functor.whiskerRight
        (NatTrans.op (baseChangeSourceOver s.f j)) (moduleHomOver hc s.F s.G)).app T) := by
      refine isIso_moduleHomOver_map hc s.F s.G _ ?_
      apply bijective_modulePullback_map_of_supportOfSheaf_subset_range
      · exact s.isOpenImmersion_baseChangeSourceMap j hj T.unop
      · exact isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ s.F
          s.quasicoherent_F
      · exact isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ s.G
          s.quasicoherent_G
      · exact isFiniteTypeOnSite_modulePullback B S hS _ s.G hGft
      · exact s.supportOfSheaf_baseChange_subset_range j hGft hsupp T.unop
    exact NatIso.isIso_of_isIso_app _
  exact IsIso.comp_isIso' h1
    (Functor.isoWhiskerLeft (baseChangeOver (j ≫ s.f)).op
      (moduleHomOverPullback hc j s.F s.G).symm).isIso_hom

/-- **Stacks 08JY, first step**: the relative Hom functor is unchanged by restricting the source
to an open subspace containing the support of `G`. -/
def restrictSourceIso (hc : ModulePushforwardCoherence B S hS)
    {U : AlgebraicSpaces B S hS} (j : U ⟶ s.X) (hj : IsOpenImmersion B S hS j.hom)
    (hGft : SheafOfModules.IsFiniteTypeOnSite s.G)
    (hsupp : supportOfSheaf B S hS s.X.1 ((SheafOfModules.toSheaf _).obj s.G) ⊆
      Set.range (pointsMap B S hS U.1 j.hom)) :
    s.homFunctor hc ≅ (s.restrictSource j).homFunctor hc :=
  have := s.isIso_restrictSourceMap hc j hj hGft hsupp
  asIso (s.restrictSourceMap hc j)

open CoherentSituation in
/-- **A quasi-compact open neighbourhood of the support of `G`**: if the base is quasi-compact
and the support of `G` is proper over it, the support is compact, hence contained in a
quasi-compact open subspace of the source (Stacks 08JY, the first sentence of the proof). -/
theorem exists_isOpenImmersion_isQuasiCompactSpace_supportOfSheaf_subset
    (hB : IsQuasiCompactSpace B S hS s.base.1) (hproper : HasProperSupportOver s.f s.G) :
    ∃ (U : AlgebraicSpaces B S hS) (j : U ⟶ s.X), IsOpenImmersion B S hS j.hom ∧
      IsQuasiCompactSpace B S hS U.1 ∧
      supportOfSheaf B S hS s.X.1 ((SheafOfModules.toSheaf _).obj s.G) ⊆
        Set.range (pointsMap B S hS U.1 j.hom) := by
  obtain ⟨hp, hcl, hpr⟩ := hproper
  have hc := isCompact_of_isProperOver B S hS s.X.2 s.base.2 hB s.f.hom hp _ hcl hpr
  obtain ⟨V, hV, hVqc, hsub⟩ :=
    exists_isQuasiCompactSpace_openSubspace_of_isCompact B S hS s.X.2 _ hc
  exact ⟨⟨V.toFunctor, hV.1⟩, ObjectProperty.homMk V.ι, hV.2, hVqc, hsub⟩

/-- The restricted morphism `j ≫ f : U ⟶ B` is locally of finite type when `f` is and `j` is an
open immersion (Stacks 03XG, an open immersion being étale, hence locally of finite type). -/
theorem isLocallyOfFiniteType_restrictSource {U : AlgebraicSpaces B S hS} (j : U ⟶ s.X)
    (hj : IsOpenImmersion B S hS j.hom) (hf : IsLocallyOfFiniteType B S hS s.f.hom) :
    IsLocallyOfFiniteType B S hS (s.restrictSource j).f.hom :=
  isLocallyOfFiniteType_comp B S hS U.2 s.X.2 s.base.2 j.hom s.f.hom
    (isLocallyOfFiniteType_of_isEtale' B S hS j.hom (isEtale_of_isOpenImmersion B S hS hj)) hf

/-- The restricted morphism `j ≫ f : U ⟶ B` is quasi-separated when `f` is and `j` is an open
immersion (Stacks 03KQ, an open immersion being a monomorphism, hence quasi-separated). -/
theorem isQuasiSeparated_restrictSource {U : AlgebraicSpaces B S hS} (j : U ⟶ s.X)
    (hj : IsOpenImmersion B S hS j.hom) (hf : IsQuasiSeparated B S hS s.f.hom) :
    IsQuasiSeparated B S hS (s.restrictSource j).f.hom :=
  isQuasiSeparated_comp B S hS U.2 s.X.2 j.hom s.f.hom
    (isQuasiSeparated_of_mono B S hS j.hom (mono_of_isOpenImmersion B S hS j.hom hj)) hf

/-- **A quasi-compact open subspace of a source locally of finite type and quasi-separated over a
Noetherian base is Noetherian** (Stacks 08JY, the first sentence of the proof): it is
quasi-compact by assumption, quasi-separated by Stacks 04ZH (2) and locally Noetherian by
Stacks 04ZK. -/
theorem isNoetherian_restrictSource (hZ : B.Contains (⊤_ Scheme.{u}))
    (hB : IsNoetherian B S hS hZ s.base.1) (hf : IsLocallyOfFiniteType B S hS s.f.hom)
    (hfqs : IsQuasiSeparated B S hS s.f.hom) {U : AlgebraicSpaces B S hS} (j : U ⟶ s.X)
    (hj : IsOpenImmersion B S hS j.hom) (hU : IsQuasiCompactSpace B S hS U.1) :
    IsNoetherian B S hS hZ U.1 :=
  ⟨hU, isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ U.2 hB.2.1
      (s.isQuasiSeparated_restrictSource j hj hfqs),
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS U.2 s.base.2 _
      (s.isLocallyOfFiniteType_restrictSource j hj hf) hB.2.2⟩

open CoherentSituation in
/-- **Proper support survives restriction to an open neighbourhood of the support.** If `G` is of
finite type with support proper over the base and contained in the image of the open immersion
`j : U ⟶ X`, then `j^*G` has support proper over the base along `j ≫ f`.

The support of `j^*G` lies in the preimage of the support of `G`, which is proper over the base
by `AlgebraicGeometry.Space.isProperOver_preimage_of_isOpenImmersion`; Stacks 0CZE concludes. -/
theorem hasProperSupportOver_restrictSource {U : AlgebraicSpaces B S hS} (j : U ⟶ s.X)
    (hj : IsOpenImmersion B S hS j.hom) (hGft : SheafOfModules.IsFiniteTypeOnSite s.G)
    (hsupp : supportOfSheaf B S hS s.X.1 ((SheafOfModules.toSheaf _).obj s.G) ⊆
      Set.range (pointsMap B S hS U.1 j.hom))
    (hproper : HasProperSupportOver s.f s.G) :
    HasProperSupportOver (s.restrictSource j).f (s.restrictSource j).G := by
  obtain ⟨hp, hcl, hpr⟩ := hproper
  have hjf := s.isLocallyOfFiniteType_restrictSource j hj hp
  exact ⟨hjf, isClosed_supportOfSheaf_modulePullback B S hS j s.G hGft,
    isProperOver_of_subset B S hS U.2 s.base.2 _ hjf _ _ _ _
      (supportOfSheaf_modulePullback_subset B S hS j s.G hGft)
      (isProperOver_preimage_of_isOpenImmersion B S hS U.2 s.X.2 s.base.2 j.hom s.f.hom hj hjf
        hp _ hcl hsupp hpr)⟩

/-- **Flatness over the base survives restriction along an étale morphism**: if `G` is flat over
the base, so is `j^*G` along `j ≫ f` (Stacks 05VY, as `j` is flat by Stacks 0467). -/
theorem isFlatOver_restrictSource {U : AlgebraicSpaces B S hS} (j : U ⟶ s.X)
    (hj : IsEtale B S hS j.hom) (hflat : IsFlatOver B S hS s.X.2 s.f.hom s.G) :
    IsFlatOver B S hS (s.restrictSource j).X.2 (s.restrictSource j).f.hom
      (s.restrictSource j).G :=
  isFlatOver_comp_modulePullback_of_isFlat B S hS j s.f s.G s.quasicoherent_G
    (isFlat_of_isEtale B S hS hj) hflat

open CoherentSituation in
/-- **Stacks 08JY reduces to a quasi-compact source**: if the relative Hom functor of every
restriction of the situation to a quasi-compact open subspace containing the support of `G` is an
algebraic space affine and of finite presentation over the base, so is the relative Hom functor of
the situation, the base being quasi-compact and the support of `G` proper over it. -/
theorem isAffineFinitePresentationAlgebraicSpaceOverBase_of_restrictSource
    (hc : ModulePushforwardCoherence B S hS) (hB : IsQuasiCompactSpace B S hS s.base.1)
    (hGft : SheafOfModules.IsFiniteTypeOnSite s.G) (hproper : HasProperSupportOver s.f s.G)
    (h : ∀ (U : AlgebraicSpaces B S hS) (j : U ⟶ s.X), IsOpenImmersion B S hS j.hom →
      IsQuasiCompactSpace B S hS U.1 →
      supportOfSheaf B S hS s.X.1 ((SheafOfModules.toSheaf _).obj s.G) ⊆
        Set.range (pointsMap B S hS U.1 j.hom) →
      (s.restrictSource j).IsAffineFinitePresentationAlgebraicSpaceOverBase hc) :
    s.IsAffineFinitePresentationAlgebraicSpaceOverBase hc := by
  obtain ⟨U, j, hj, hU, hsupp⟩ :=
    s.exists_isOpenImmersion_isQuasiCompactSpace_supportOfSheaf_subset hB hproper
  exact IsAffineFinitePresentationAlgebraicSpaceOver.of_iso
    (s.restrictSourceIso hc j hj hGft hsupp).symm (h U j hj hU hsupp)

end AlgebraicGeometry.Space.HomSituation

end
