module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativelyPerfectDirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCartesianPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedEtaleBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectLocalOnSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteTypeSubalgebraModelUnbounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperDescentOverPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FlatDescentOverPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentOfAffineSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseRelativeDirectImage

/-!
# The reduction step of Stacks 0DKX

Test file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section EtaleLocal

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

/-- **Perfectness of `Rf_*E` is étale local on `Y`.** Let `f : X ⟶ Y` be proper, flat and of finite
presentation and `E` a `Y`-perfect object of `D(𝒪_X)`. If the derived direct image is perfect for
every proper, flat, finitely presented morphism to an affine object of the site and every
relatively perfect object, then `Rf_*E` is perfect.

Every point of `Y` lies in the image of an affine étale chart `W ⟶ Y`
(`AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`), perfectness descends along such a
jointly surjective family (`AlgebraicGeometry.Space.isPerfect_of_isPerfect_etaleModulePullback`),
the restriction of `Rf_*E` to `W` is `R(f_W)_*` of the pullback of `E` (Stacks 08GE,
`AlgebraicGeometry.Space.spaceDerivedPushforwardPullBaseChangeIso`), the base change `f_W` is
again proper, flat and finitely presented, and the pullback of `E` is `W`-perfect (Stacks 0DKT,
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_pull_of_isPullback`), the projection
`X ×_Y W ⟶ X` being representable. -/
theorem isPerfect_spaceDerivedPushforward_of_affineCharts
    (H : ∀ (W : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
      ∀ {X' : AlgebraicSpaces B S hS}
        (f' : X' ⟶ (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS)),
        IsProper B S hS f'.hom → ∀ (hflat : IsFlat B S hS f'.hom)
        (hfp : IsFinitePresentation B S hS f'.hom) (E' : derivedModules B S hS X'),
        RelativeDescentSituation.IsPerfectAlong f' hflat hfp.1 E' →
        (smallEtaleRingedSite B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)).IsPerfect
          ((spaceDerivedPushforward B S hS f').obj E'))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hproper : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (E : derivedModules B S hS X) (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect ((spaceDerivedPushforward B S hS f).obj E) := by
  choose W b hWaff hbet w hw using
    fun x : points B S hS Y.1 => exists_affine_etale_chart_at_point B S hS Y.1 Y.2 x
  let Yx : points B S hS Y.1 → AlgebraicSpaces B S hS :=
    fun x => ⟨yoneda.obj (W x), isAlgebraicSpace_yoneda B S hS (W x)⟩
  let g : ∀ x, Yx x ⟶ Y := fun x => ObjectProperty.homMk (b x)
  have hg : ∀ x, IsEtale B S hS (g x).hom := fun x =>
    (isEtale_iff_presheaf_of_yoneda B S hS (b x)).2 (hbet x)
  refine isPerfect_of_isPerfect_etaleModulePullback B S hS g hg (fun x => ⟨x, w x, hw x⟩) _
    fun x => ?_
  have sq := IsPullback.of_hasPullback f (g x)
  have sq' := AlgebraicSpaces.isPullback_hom B S hS sq
  have hrep : yoneda.relativelyRepresentable (pullback.fst f (g x)).hom :=
    MorphismProperty.of_isPullback sq'.flip
      (relativelyRepresentable_of_isAlgebraicSpace B S hS Y.2 (b x))
  have hprop' : IsProper B S hS (pullback.snd f (g x)).hom :=
    MorphismProperty.of_isPullback (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
      IsProper B S hS f.hom) sq hproper
  have hflat' : IsFlat B S hS (pullback.snd f (g x)).hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hflat
  have hfp' : IsFinitePresentation B S hS (pullback.snd f (g x)).hom :=
    MorphismProperty.of_isPullback (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
      IsFinitePresentation B S hS f.hom) sq hfp
  have hE' := isPerfectRelativeToCanonical_pull_of_isPullback sq hrep hflat' hfp'.1 hflat hfp.1 E hE
  have hperf := H (W x) (hWaff x) (pullback.snd f (g x)) hprop' hflat' hfp' _ hE'
  refine RingedSite.isPerfect_of_iso _ hperf ?_
  exact ((spaceDerivedPushforwardPullBaseChangeIso B S hS sq (hg x)).app E).symm ≪≫
    (smallEtaleDerivedModulePullbackIsoEtale B S hS (g x) (hg x)).app _

end EtaleLocal

/-! ### The affine case over the final scheme -/

section Affine

attribute [local instance] uliftIntAlgebra

variable {B}

/-- The stages `Spec Λ_t` of the system of the finitely generated subrings of a ring are
Noetherian algebraic spaces over the final scheme, `Λ_t` being of finite type over `ℤ`. -/
theorem isNoetherian_yoneda_adjoinSiteDiagram (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u)
    [CommRing A] (hA : B.Contains (Spec (.of A))) (t : (Finset A)ᵒᵖ) :
    IsNoetherian B (⊤_ Scheme.{u}) hZ hZ (yoneda.obj ((adjoinSiteDiagram B hZ A hA).obj t)) :=
  have : IsNoetherianRing (adjoinRing A t.unop) := Algebra.FiniteType.isNoetherianRing ℤ _
  ⟨isQuasiCompactSpace_yoneda_of_isAffine B _ hZ _
      (inferInstanceAs (IsAffine (Spec (.of (adjoinRing A t.unop))))),
    isAbsolutelyQuasiSeparated_yoneda_obj B _ hZ hZ _
      (inferInstanceAs (QuasiSeparatedSpace (Spec (.of (adjoinRing A t.unop))))),
    hasEtaleLocalProperty_of_representable B _ hZ _
      (fun T : Scheme.{u} => IsLocallyNoetherian T) ((adjoinSiteDiagram B hZ A hA).obj t)
      (Iso.refl _) (inferInstanceAs (IsLocallyNoetherian (Spec (.of (adjoinRing A t.unop)))))⟩

/-- The spectrum of the global sections of an affine object of the site lies in the site. -/
theorem contains_spec_globalSections_of_isAffine {T : Scheme.{u}} {hT : B.Contains T}
    (W : BigFppfOver B T hT) [IsAffine ((BigFppfOver.toScheme B T hT).obj W)] :
    B.Contains (Spec (.of Γ((BigFppfOver.toScheme B T hT).obj W, ⊤))) :=
  (Scheme.size_congr ((BigFppfOver.toScheme B T hT).obj W).isoSpec).symm.trans_lt W.left.2

/-- An affine object `W` of the big fppf site of the final scheme is the spectrum of its global
sections, as an object of that site. -/
def isoOverMkToTerminalSite (hZ : B.Contains (⊤_ Scheme.{u})) (W : BigFppfOver B _ hZ)
    [IsAffine ((BigFppfOver.toScheme B _ hZ).obj W)] :
    W ≅ Over.mk (toTerminalSite B hZ (contains_spec_globalSections_of_isAffine W)) :=
  Over.isoMk (ObjectProperty.isoMk _ ((BigFppfOver.toScheme B _ hZ).obj W).isoSpec)
    (B.inclusion.map_injective (terminal.hom_ext _ _))

end Affine

section AffineDescent

attribute [local instance] uliftIntAlgebra
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {B}

/-- The underlying schemes of the cone of the `Spec Λ_s` with vertex `Spec A` form a limit. -/
def isLimitToSchemeAdjoinSiteCone (hZ : B.Contains (⊤_ Scheme.{u})) (A : Type u) [CommRing A]
    (hA : B.Contains (Spec (.of A))) :
    IsLimit ((BigFppfOver.toScheme B _ hZ).mapCone (adjoinSiteCone B hZ A hA)) :=
  AdjoinFinset.isLimitSpecCone (ULift.{u} ℤ) A


/-- A cone extended along an isomorphism stays a limit after applying a functor. -/
def isLimitMapConeExtendOfIsIso {J C D : Type*} [Category* J] [Category* C] [Category* D]
    (F : C ⥤ D) {K : J ⥤ C} (c : Cone K) {X : C} (e : X ≅ c.pt)
    (h : IsLimit (F.mapCone c)) : IsLimit (F.mapCone (c.extend e.hom)) :=
  (IsLimit.extendIso (F.map e.hom) h).ofIsoLimit (Cone.ext (Iso.refl _) fun j => by simp)

/-- A cartesian square whose top morphism ends with an isomorphism `i` stays cartesian when `i` is
moved to the bottom-left morphism. -/
theorem isPullback_comp_iso_left {C : Type*} [Category* C] {P X X' Y Z : C} {f : P ⟶ X'}
    {g : P ⟶ Y} {h : X ⟶ Z} {k : Y ⟶ Z} (i : X' ≅ X) (sq : IsPullback (f ≫ i.hom) g h k) :
    IsPullback f g (i.hom ≫ h) k :=
  sq.of_iso (Iso.refl _) i.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

/-- **The perfectness half of Stacks 0DKX over an affine target, over the final scheme, from the
limit theorem.** Let `W` be an affine object of the big fppf site of `Spec ℤ`, `f : X ⟶ W` proper,
flat and of finite presentation and `E` a `W`-perfect object of `D(𝒪_X)`. If perfectness of the
direct image holds at the limit of every Situation 0DKU over `Spec ℤ` whose limit is a limit of
schemes, with Noetherian stages and proper base changes, then `Rf_*E` is perfect.

Write `W = Spec A`. By Stacks 07SK, 08K0 and 08K1
(`exists_adjoinRing_model_unbounded_of_adjoinDescent`) `X ⟶ Spec A` is the base change of a proper,
flat, finitely presented `X₁ ⟶ Spec Λ_s` along `Spec A ⟶ Spec Λ_s`, for a finite subset `s` of
`A`. The system of the `Spec Λ_t`, `t` a finite subset of `A`, with this model at `s` and with
`X ⟶ W` at the limit, is a Situation 0DKU
(`AlgebraicGeometry.Space.RelativeDescentSituation.ofAffineSystem`) whose limit is a limit of
schemes, whose stages are Noetherian and whose base changes are proper.

* `h08K1`: Stacks 08K1, not yet proved here
  `MorphismDescentSituation.exists_isProper_mapAt_of_siteContainsBaseChangeLimits`: for a situation
  of Stacks 084W whose system of bases satisfies the convention 07SD, if the base change of `f₀` to
  the limit is proper and `f₀` is locally of finite type, its base change to some stage is
  proper. -/
theorem isPerfect_spaceDerivedPushforward_of_isAffine_terminal
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : MorphismDescentSituation B S hS hZ I),
      SiteContainsBaseChangeLimits B S hS D.base → IsProper B S hS D.mapLimit →
      IsLocallyOfFiniteType B S hS D.map₀ →
      ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi))
    (H : ∀ (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)]
        (D : RelativeDescentSituation B (⊤_ Scheme.{u}) B.contains_terminal B.contains_terminal I),
        D.IsSchemeLimit →
        (∀ i : D.LaterIndex,
          IsNoetherian B _ B.contains_terminal B.contains_terminal (D.stageTarget i).1) →
        (∀ i : D.LaterIndex, IsProper B _ B.contains_terminal (D.stageStructure i).hom) →
        ∀ E' : derivedModules B _ B.contains_terminal D.limitSource, D.IsLimitPerfect E' →
          (smallEtaleRingedSite B _ B.contains_terminal D.limitTarget.1
            D.limitTarget.2).IsPerfect
            ((derivedModulePushforward B _ B.contains_terminal D.limitStructure).obj E'))
    (W : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal)
    (hW : IsAffine ((BigFppfOver.toScheme B _ B.contains_terminal).obj W))
    {X : AlgebraicSpaces B _ B.contains_terminal}
    (f : X ⟶ (⟨yoneda.obj W, isAlgebraicSpace_yoneda B _ B.contains_terminal W⟩ :
      AlgebraicSpaces B _ B.contains_terminal))
    (hproper : IsProper B _ B.contains_terminal f.hom)
    (hflat : IsFlat B _ B.contains_terminal f.hom)
    (hfp : IsFinitePresentation B _ B.contains_terminal f.hom)
    (E : derivedModules B _ B.contains_terminal X)
    (hE : RelativeDescentSituation.IsPerfectAlong f hflat hfp.1 E) :
    (smallEtaleRingedSite B _ B.contains_terminal (yoneda.obj W)
        (isAlgebraicSpace_yoneda B _ B.contains_terminal W)).IsPerfect
      ((spaceDerivedPushforward B _ B.contains_terminal f).obj E) := by
  classical
  let hZ := B.contains_terminal
  let A : Type u := Γ((BigFppfOver.toScheme B _ hZ).obj W, ⊤)
  have hA : B.Contains (Spec (.of A)) := contains_spec_globalSections_of_isAffine W
  let e : W ≅ Over.mk (toTerminalSite B hZ hA) := isoOverMkToTerminalSite hZ W
  let p : X.1 ⟶ yoneda.obj (Over.mk (toTerminalSite B hZ hA)) := f.hom ≫ yoneda.map e.hom
  have hp : IsProper B _ hZ p ∧ IsFlat B _ hZ p ∧ IsFinitePresentation B _ hZ p :=
    (isProper_isFlat_isFinitePresentation_comp_isIso_iff B _ hZ f.hom (yoneda.map e.hom)).2
      ⟨hproper, hflat, hfp⟩
  have hq := adjoinSiteDiagram_isAlgebraicSpace_isAffineHom_qcqs B hZ A hA
  obtain ⟨s, X₁, hX₁, f₁, ⟨hp₁, hfl₁, hfp₁⟩, π, hπ⟩ :=
    exists_adjoinRing_model_unbounded_of_adjoinDescent B hZ A hA
      (fun i _ _ g => exists_isProper_overPullback_map_of_chartLimitsInSite B _ hZ hZ
        (fun D => h08K1 hZ hZ D) _ (adjoinSiteDiagram_chartLimitsInSite B hZ A hA) hq.1 hq.2.1 i g)
      (fun i _ _ g => exists_isFlat_overPullback_map_of_chartLimitsInSite B _ hZ hZ _
        (adjoinSiteDiagram_chartLimitsInSite B hZ A hA) hq.1 hq.2.1 i g)
      X.2 p hp
  -- the cone of the `Spec Λ_t` with vertex `W`
  let d : Cone (adjoinSiteDiagram B hZ A hA) := (adjoinSiteCone B hZ A hA).extend e.hom
  have hd : IsLimit ((BigFppfOver.toScheme B _ hZ).mapCone d) :=
    isLimitMapConeExtendOfIsIso (BigFppfOver.toScheme B _ hZ) (adjoinSiteCone B hZ A hA) e
      (isLimitToSchemeAdjoinSiteCone hZ A hA)
  have hT :
      ∀ t, IsAffine ((BigFppfOver.toScheme B _ hZ).obj ((adjoinSiteDiagram B hZ A hA).obj t)) :=
    fun t => inferInstanceAs (IsAffine (Spec (.of (adjoinRing A t.unop))))
  have hpb : IsPullback f.hom π (yoneda.map (d.π.app (op s))) f₁ := by
    have := isPullback_comp_iso_left (yoneda.mapIso e) hπ.flip
    have e₂ : yoneda.map (d.π.app (op s)) =
        (yoneda.mapIso e).hom ≫ yoneda.map ((adjoinSiteCone B hZ A hA).π.app (op s)) :=
      (yoneda.map_comp _ _)
    rw [e₂]
    exact this
  let D := RelativeDescentSituation.ofAffineSystem hd hT s hX₁ f₁ hfl₁ hfp₁ X.2 π f.hom hpb hZ
  have hperf := H (Finset A) D (RelativeDescentSituation.isSchemeLimit_ofAffineSystem hZ)
    (fun i => isNoetherian_yoneda_adjoinSiteDiagram hZ A hA (op i.1))
    (RelativeDescentSituation.isProper_stageStructure_of_isProper D hp₁) E hE
  exact RingedSite.isPerfect_of_iso _ hperf
    ((derivedModulePushforwardIsoSpaceDerivedPushforward B _ hZ f).app E)

/-- **The étale localisation and the limit argument of Stacks 0DKX, over the final scheme**
(unregistered): `AlgebraicGeometry.Space.PerfectnessReducesToNoetherianDescent` for algebraic
spaces over `Spec ℤ`. Perfectness of `Rf_*E` is étale local on `Y`
(`AlgebraicGeometry.Space.isPerfect_spaceDerivedPushforward_of_affineCharts`), and over an affine
target it is perfectness at the limit of a Situation 0DKU of the spectra of the finitely generated
subrings (`AlgebraicGeometry.Space.isPerfect_spaceDerivedPushforward_of_isAffine_terminal`).

* `h08K1`: Stacks 08K1, not yet proved here
  `MorphismDescentSituation.exists_isProper_mapAt_of_siteContainsBaseChangeLimits`. -/
theorem perfectnessReducesToNoetherianDescent_terminal
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : MorphismDescentSituation B S hS hZ I),
      SiteContainsBaseChangeLimits B S hS D.base → IsProper B S hS D.mapLimit →
      IsLocallyOfFiniteType B S hS D.map₀ →
      ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi)) :
    PerfectnessReducesToNoetherianDescent B (⊤_ Scheme.{u}) B.contains_terminal := by
  intro X Y f hproper hflat hfp E hE H
  refine RingedSite.isPerfect_of_iso _ ?_
    ((derivedModulePushforwardIsoSpaceDerivedPushforward B _ _ f).app E).symm
  exact isPerfect_spaceDerivedPushforward_of_affineCharts B _ _
    (fun W hW _ f' hp' hfl' hfp' E' hE' =>
      isPerfect_spaceDerivedPushforward_of_isAffine_terminal h08K1 H W hW f' hp' hfl' hfp' E' hE')
    f hproper hflat hfp E hE

end AffineDescent

/-! ### The change of base to the final scheme -/

section ChangeOfBase

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {W T : Scheme.{u}} {hW : B.Contains W} {hT : B.Contains T} (h : B.obj hW ⟶ B.obj hT)

/-- **Relative perfectness over the smaller base** (internal, pending; Stacks 0DKN read through
Stacks 04SG), as a proposition: for flat, locally finitely presented morphisms `f : Z₁ ⟶ Z₂` over
`W` and `g : Y₁ ⟶ Y₂` over `T` matched by `εᵢ : Λ_h Zᵢ ≅ Yᵢ`, an object of `D(𝒪_{Y₁})` is
`Y₂`-perfect exactly when the corresponding object of `D(𝒪_{Z₁})` is `Z₂`-perfect.

The pseudo-coherence clause is
`AlgebraicGeometry.Space.isPseudoCoherent_smallerBaseDerivedEquivalence_iff`. The Tor clause
needs the change of base to identify the inverse images `g⁻¹𝒪_{Y₂}` and `f⁻¹𝒪_{Z₂}` along the
equivalence of small étale sites, compatibly with the structure maps to `𝒪_{Y₁}` and `𝒪_{Z₁}`,
and then the canonical derived tensor products on the slices (Stacks 06YU) and Tor amplitude
along that equivalence of ringed sites. -/
def SmallerBaseRelativelyPerfectComparison : Prop :=
  ∀ {Z₁ Z₂ : AlgebraicSpaces B W hW} {Y₁ Y₂ : AlgebraicSpaces B T hT}
    (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
    (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1)
    {f : Z₁ ⟶ Z₂} {g : Y₁ ⟶ Y₂},
    ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom →
    ∀ (hgfl : IsFlat B T hT g.hom) (hglfp : IsLocallyOfFinitePresentation B T hT g.hom)
      (hffl : IsFlat B W hW f.hom) (hflfp : IsLocallyOfFinitePresentation B W hW f.hom)
      (K : DerivedCategory (Modules.{u, u} B T hT Y₁.1 Y₁.2)),
      IsPerfectRelativeToCanonical B T hT g hgfl hglfp K ↔
        IsPerfectRelativeToCanonical B W hW f hffl hflfp
          ((smallerBaseDerivedEquivalence B h ε₁).functor.obj K)

variable {B}

/-- **The reduction of Stacks 0DKX to the final scheme** (unregistered): the proposition
`AlgebraicGeometry.Space.PerfectnessReducesToNoetherianDescent` over `S` follows from the same
over `Spec ℤ`, by the change of base `S ⟶ Spec ℤ` of Stacks 04SG. The morphism `f` is carried to
`Λ f`, which is again proper, flat and of finite presentation
(`AlgebraicGeometry.Space.isProper_relocalizeSpaceMap_iff` and its companions), and `E` to the
corresponding object of `D(𝒪_{Λ X})`, which is `Λ Y`-perfect.

* `hpush`, `hperf`, `hrel`: internal, pending: the change of base commutes with `Rf_*`
  (`AlgebraicGeometry.Space.SmallerBaseDerivedPushforwardComparison`), preserves and reflects
  perfectness (`AlgebraicGeometry.Space.SmallerBasePerfectComparison`) and relative perfectness
  (`AlgebraicGeometry.Space.SmallerBaseRelativelyPerfectComparison`), all at
  `S ⟶ Spec ℤ`. -/
theorem perfectnessReducesToNoetherianDescent_of_terminal
    (hpush : SmallerBaseDerivedPushforwardComparison B (toTerminalSite B B.contains_terminal hS))
    (hperf : SmallerBasePerfectComparison B (toTerminalSite B B.contains_terminal hS))
    (hrel : SmallerBaseRelativelyPerfectComparison B (toTerminalSite B B.contains_terminal hS))
    (htop : PerfectnessReducesToNoetherianDescent B (⊤_ Scheme.{u}) B.contains_terminal) :
    PerfectnessReducesToNoetherianDescent B S hS := by
  intro X Y f hproper hflat hfp E hE H
  have hproper' := (isProper_relocalizeSpaceMap_iff
    (h := toTerminalSite B B.contains_terminal hS) f).2 hproper
  have hflat' := (isFlat_relocalizeSpaceMap_iff
    (h := toTerminalSite B B.contains_terminal hS) f).2 hflat
  have hfp' := (isFinitePresentation_relocalizeSpaceMap_iff
    (h := toTerminalSite B B.contains_terminal hS) f).2 hfp
  have := isClosedUnderIsomorphisms_isPerfectRelativeToCanonical B S hS f hflat hfp.1
  have hfg : (Iso.refl ((OverShriek.relocalizePresheafFunctor
        (toTerminalSite B B.contains_terminal hS)).obj X.1)).hom ≫
      (relocalizeSpaceMap (toTerminalSite B B.contains_terminal hS) f).hom =
        (OverShriek.relocalizePresheafFunctor (toTerminalSite B B.contains_terminal hS)).map f.hom ≫
          (Iso.refl ((OverShriek.relocalizePresheafFunctor
            (toTerminalSite B B.contains_terminal hS)).obj Y.1)).hom :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have t2 : IsPerfectRelativeToCanonical B S hS f hflat hfp.1
      ((smallerBaseDerivedEquivalence B (toTerminalSite B B.contains_terminal hS)
        (Iso.refl ((OverShriek.relocalizePresheafFunctor
          (toTerminalSite B B.contains_terminal hS)).obj X.1))).functor.obj
        ((relocalizeSpaceDerivedEquivalence B (toTerminalSite B B.contains_terminal hS)
          X).inverse.obj E)) :=
    (isPerfectRelativeToCanonical B S hS f hflat hfp.1).prop_of_iso
      ((relocalizeSpaceDerivedEquivalence B (toTerminalSite B B.contains_terminal hS)
        X).counitIso.app E).symm hE
  have hrel' := hrel (Iso.refl _) (Iso.refl _) hfg hflat' hfp'.1 hflat hfp.1
  have hE' := (hrel' ((relocalizeSpaceDerivedEquivalence B (toTerminalSite B B.contains_terminal hS)
    X).inverse.obj E)).2 t2
  have hp := htop (relocalizeSpaceMap (toTerminalSite B B.contains_terminal hS) f) hproper' hflat'
    hfp' ((relocalizeSpaceDerivedEquivalence B (toTerminalSite B B.contains_terminal hS)
      X).inverse.obj E) hE' H
  exact isPerfect_derivedModulePushforward_of_relocalize hpush hperf f E hp

end ChangeOfBase

/-! ### Stacks 0DKX with the reduction discharged -/

section Discharged

/-- **The étale localisation and the limit argument of Stacks 0DKX** (unregistered):
`AlgebraicGeometry.Space.PerfectnessReducesToNoetherianDescent` over any base scheme `S`, from
the case of the final scheme
(`AlgebraicGeometry.Space.perfectnessReducesToNoetherianDescent_terminal`) and the change of base
`S ⟶ Spec ℤ`
(`AlgebraicGeometry.Space.perfectnessReducesToNoetherianDescent_of_terminal`).

* `h08K1`: Stacks 08K1, not yet proved here
  `MorphismDescentSituation.exists_isProper_mapAt_of_siteContainsBaseChangeLimits`.
* `hpush`, `hperf`, `hrel`: internal, pending: the change of base `S ⟶ Spec ℤ` commutes with
  `Rf_*` (`AlgebraicGeometry.Space.SmallerBaseDerivedPushforwardComparison`), preserves and
  reflects perfectness (`AlgebraicGeometry.Space.SmallerBasePerfectComparison`) and relative
  perfectness (`AlgebraicGeometry.Space.SmallerBaseRelativelyPerfectComparison`). -/
theorem perfectnessReducesToNoetherianDescent_of_changeOfBase
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : MorphismDescentSituation B S hS hZ I),
      SiteContainsBaseChangeLimits B S hS D.base → IsProper B S hS D.mapLimit →
      IsLocallyOfFiniteType B S hS D.map₀ →
      ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi))
    (hpush : SmallerBaseDerivedPushforwardComparison B (toTerminalSite B B.contains_terminal hS))
    (hperf : SmallerBasePerfectComparison B (toTerminalSite B B.contains_terminal hS))
    (hrel : SmallerBaseRelativelyPerfectComparison B (toTerminalSite B B.contains_terminal hS)) :
    PerfectnessReducesToNoetherianDescent B S hS :=
  perfectnessReducesToNoetherianDescent_of_terminal S hS hpush hperf hrel
    (perfectnessReducesToNoetherianDescent_terminal h08K1)

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

/-- **Stacks 0DKX** (unregistered), with the reduction to Noetherian stages proved: the form of
`AlgebraicGeometry.Space.isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_reduction`
whose hypothesis `hred` is discharged by
`AlgebraicGeometry.Space.perfectnessReducesToNoetherianDescent_of_changeOfBase`. For a flat,
proper, finitely presented `f : X ⟶ Y` and a `Y`-perfect `E`, `Rf_*E` is perfect and its formation
commutes with arbitrary base change.

* `h0A1K`: Stacks 0A1K at every base scheme, not yet proved here.
* `h08IS`: Stacks 08IS at every base scheme, not yet proved here.
* `h0DKW`: Stacks 0DKW at every base scheme, not yet proved here.
* `h08K1`: Stacks 08K1, not yet proved here.
* `hpush`, `hperf`, `hrel`: internal, pending (the change of base `S ⟶ Spec ℤ`, see
  `AlgebraicGeometry.Space.perfectnessReducesToNoetherianDescent_of_changeOfBase`). -/
theorem isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_changeOfBase
    (h0A1K : ∀ {T : Scheme.{u}} (hT : B.Contains T), FlatDerivedBaseChange B T hT)
    (h08IS : ∀ {T : Scheme.{u}} (hT : B.Contains T), ProperSupportPerfectDirectImage B T hT)
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT)
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : MorphismDescentSituation B S hS hZ I),
      SiteContainsBaseChangeLimits B S hS D.base → IsProper B S hS D.mapLimit →
      IsLocallyOfFiniteType B S hS D.map₀ →
      ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi))
    (hpush : SmallerBaseDerivedPushforwardComparison B (toTerminalSite B B.contains_terminal hS))
    (hperf : SmallerBasePerfectComparison B (toTerminalSite B B.contains_terminal hS))
    (hrel : SmallerBaseRelativelyPerfectComparison B (toTerminalSite B B.contains_terminal hS))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hproper : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (E : derivedModules B S hS X) (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect ((spaceDerivedPushforward B S hS f).obj E) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
        (hpb : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' hpb.w E) :=
  isPerfect_and_isIso_baseChange_of_isPerfectRelativeTo_of_reduction B S hS h0A1K h08IS h0DKW
    (perfectnessReducesToNoetherianDescent_of_changeOfBase B S hS h08K1 hpush hperf hrel)
    f hproper hflat hfp E hE

/-- **The 0DKX input of the proof of Stacks 0DKY**,
`AlgebraicGeometry.Space.RelativelyPerfectPushforwardBaseChange`, with the reduction to Noetherian
stages proved (`AlgebraicGeometry.Space.perfectnessReducesToNoetherianDescent_of_changeOfBase`).
Pending: `h0A1K`, `h08IS`, `h0DKW`, `h08K1` (not yet proved here) and `hpush`, `hperf`, `hrel`
(internal). -/
theorem relativelyPerfectPushforwardBaseChange_of_changeOfBase
    (h0A1K : ∀ {T : Scheme.{u}} (hT : B.Contains T), FlatDerivedBaseChange B T hT)
    (h08IS : ∀ {T : Scheme.{u}} (hT : B.Contains T), ProperSupportPerfectDirectImage B T hT)
    (h0DKW : ∀ {T : Scheme.{u}} (hT : B.Contains T), RelativelyPerfectColimitHolds B T hT)
    (h08K1 : ∀ {S : Scheme.{u}} (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
      {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : MorphismDescentSituation B S hS hZ I),
      SiteContainsBaseChangeLimits B S hS D.base → IsProper B S hS D.mapLimit →
      IsLocallyOfFiniteType B S hS D.map₀ →
      ∃ (i : I) (hi : D.initial ≤ i), IsProper B S hS (D.mapAt i hi))
    (hpush : SmallerBaseDerivedPushforwardComparison B (toTerminalSite B B.contains_terminal hS))
    (hperf : SmallerBasePerfectComparison B (toTerminalSite B B.contains_terminal hS))
    (hrel : SmallerBaseRelativelyPerfectComparison B (toTerminalSite B B.contains_terminal hS)) :
    RelativelyPerfectPushforwardBaseChange B S hS :=
  relativelyPerfectPushforwardBaseChange_of_reduction B S hS h0A1K h08IS h0DKW
    (perfectnessReducesToNoetherianDescent_of_changeOfBase B S hS h08K1 hpush hperf hrel)

end Discharged

end AlgebraicGeometry.Space

end
