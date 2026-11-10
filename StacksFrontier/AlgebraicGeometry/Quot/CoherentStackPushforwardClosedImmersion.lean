module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorClosedImmersionPushforwardUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionUnitBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedProperSupportUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyClosedLocus

/-!
# The direct image along a closed immersion is a closed immersion of stacks (Stacks 0DNB)

Let `B` be an algebraic space and let `π : X ⟶ Y` be a closed immersion of algebraic spaces which
are separated and of finite presentation over `B`.  Stacks 0DNB asserts that the morphism
`Coh_{X/B} ⟶ Coh_{Y/B}` of Stacks 0DN9, `(T, F) ↦ (T, π_{T,*}F)`, is a closed immersion.  This
file proves it along the lines of the source's proof.

* **Full faithfulness.**  `π_{T,*}` is fully faithful for every test scheme `T`, the base change
  `π_T` being a closed immersion (Stacks 04CJ), so the morphism is fully faithful by
  `CoherentPushforwardSituation.fullyFaithfulPushforwardFunctorOfFullyFaithful`.
* **The essential image.**  An object `(T, G)` of `Coh_{Y/B}` is isomorphic over `T` to the image
  of an object of `Coh_{X/B}` exactly when `G` is a direct image along `π_T`: then the restriction
  `π_T^*G` is an object of `Coh_{X/B}` (quasi-coherence, finite presentation, flatness and proper
  support descend along `π_{T,*}`) and the unit `G ⟶ π_{T,*}π_T^*G` is an isomorphism.
* **The closed locus.**  Over a scheme-valued point `(T₀, G)`, the condition at `T ⟶ T₀` is the
  vanishing of the base change of the inclusion `ker η ⟶ G` of the kernel of the unit
  `η : G ⟶ π_{T₀,*}π_{T₀}^*G` (the source writes the same map as `G ⊗ 𝓘 ⟶ G`, whose image is
  `ker η`), and that vanishing is represented by a closed subspace of `T₀` by Stacks 083M.

## Main definitions

* `AlgebraicGeometry.Space.CoherentPushforwardSituation.ofIsClosedImmersion`: the standing data of
  Stacks 0DN9 for a closed immersion, whose quasi-finiteness is proved rather than assumed.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.restrictObjectOfIsClosedImmersion`: the
  restriction `(T, π_T^*G)` of an object of `Coh_{Y/B}` whose module is a direct image.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.kernelUnitSituation`: the situation of
  Stacks 083F given by the inclusion of the kernel of the unit.

## Main results

* `CoherentPushforwardSituation.exists_twoFibreProductFst_pushforwardBased_iff_essImage`:
  the essential image is the objects whose module is a direct image.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.essImage_iff_isZeroAt`: that condition is
  the vanishing condition of Stacks 083F.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.hasClosedLocus_pushforwardBased`: the
  essential image is cut out by a closed subscheme on every scheme-valued point.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_and_isClosedImmersion_cohPushforward`:
  **Stacks 0DNB.**

## Implementation notes

As for Stacks 0DNA, the morphism of Stacks 0DN9 is the 1-morphism of categories fibred in
groupoids `AlgebraicGeometry.Space.CoherentPushforwardSituation.cohPushforward`, and the
closed-immersion predicate of Stacks 04XB is read at it; the structure morphism of `X` is `π`
followed by that of `Y`.

## References

* [Stacks Project, Tag 0DNB](https://stacks.math.columbia.edu/tag/0DNB)
* [Stacks Project, Tag 0DN9](https://stacks.math.columbia.edu/tag/0DN9)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 083M](https://stacks.math.columbia.edu/tag/083M)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/- The global instances `Abelian (SheafOfModules.{max u v r w} O)` and its Grothendieck
counterpart leave a stuck universe constraint against the modules of the small étale site; the
abelian structure used here is the one of `StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`.
-/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Factorizations through a closed subscheme of the base of a point -/

/-- A morphism `T ⟶ V` of the big fppf site of `U`, for `V` given by a morphism `s` to `U` read
over `S`, is a factorization of `T ⟶ U` through `s`, read over `S`. -/
theorem nonempty_hom_overMk_iff {U : BigFppfOver B S hS} {W : BigFppfOver B S hS}
    (s : W ⟶ (Over.map U.hom).obj (Over.mk (𝟙 (B.obj U.left.2))))
    (T : BigFppfOver B U.left.1 U.left.2) :
    Nonempty (T ⟶ (Over.mk s.left : BigFppfOver B U.left.1 U.left.2)) ↔
      ∃ l : (Over.map U.hom).obj T ⟶ W,
        l ≫ s = (Over.map U.hom).map (Over.homMk T.hom (Category.comp_id _)) := by
  constructor
  · rintro ⟨c⟩
    have hc : c.left ≫ s.left = T.hom := Over.w c
    refine ⟨Over.homMk c.left ?_, ?_⟩
    · change c.left ≫ W.hom = T.hom ≫ U.hom
      rw [← Over.w s, ← Category.assoc, hc]
      simp
    · exact Over.OverMorphism.ext hc
  · rintro ⟨l, hl⟩
    exact ⟨Over.homMk l.left (congrArg (fun k => k.left) hl)⟩

/-- Factorizations through `s` are unchanged by composing the target with an isomorphism on the
right and the morphism being factored with isomorphisms on both sides. -/
theorem exists_comp_eq_iff_of_iso {C : Type*} [Category C] {X X' W Y Y' : C} (a : X ≅ X')
    (b : Y ≅ Y') (s : W ⟶ Y') (q : X' ⟶ Y) :
    (∃ l : X ⟶ W, l ≫ s = a.hom ≫ q ≫ b.hom) ↔ ∃ l : X' ⟶ W, l ≫ (s ≫ b.inv) = q := by
  constructor
  · rintro ⟨l, hl⟩
    refine ⟨a.inv ≫ l, ?_⟩
    rw [Category.assoc, ← Category.assoc l, hl]
    simp
  · rintro ⟨l, hl⟩
    refine ⟨a.hom ≫ l, ?_⟩
    rw [← hl]
    simp

namespace CoherentPushforwardSituation

variable {D : CoherentPushforwardSituation B S hS}

/-- The base change `π_T` of a closed immersion is a closed immersion (Stacks 03M4). -/
theorem isClosedImmersion_mapAt (hclosed : IsClosedImmersion B S hS D.π.hom)
    (T : SchemesOver D.base) : IsClosedImmersion B S hS (D.mapAt T).hom := by
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (D.isPullback_mapAt T).flip hclosed

/-- The direct image `π_{T,*}` along the base change of a closed immersion is fully faithful
(Stacks 04CJ). -/
def fullyFaithfulPushforwardAtOfIsClosedImmersion (hclosed : IsClosedImmersion B S hS D.π.hom)
    (T : SchemesOver D.base) : (modulePushforward B S hS (D.mapAt T)).FullyFaithful :=
  fullyFaithfulModulePushforward B S hS (D.mapAt T) (isClosedImmersion_mapAt hclosed T)

variable (hclosed : IsClosedImmersion B S hS D.π.hom)

/-! ### The restriction of an object which is a direct image -/

/-- **The restriction `(T, π_T^*G)` of an object `(T, G)` of `Coh_{Y/B}` whose module is a direct
image along `π_T`**, an object of `Coh_{X/B}`. -/
def restrictObjectOfIsClosedImmersion (A : CoherentObject D.target)
    (hA : (modulePushforward B S hS (D.mapAt A.T)).essImage A.F) :
    CoherentObject D.source where
  T := A.T
  F := (modulePullback B S hS (D.mapAt A.T)).obj A.F
  quasicoherent :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ A.F A.quasicoherent
  finitePresentation :=
    isFinitePresentationOnSite_modulePullback B S hS (D.mapAt A.T) A.F A.finitePresentation
  flat := by
    have hi := isClosedImmersion_mapAt hclosed A.T
    have hu : IsIso ((modulePullbackAdjunction B S hS (D.mapAt A.T)).unit.app A.F) :=
      (essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS _ hi A.F).1 hA
    let e := asIso ((modulePullbackAdjunction B S hS (D.mapAt A.T)).unit.app A.F)
    have : ((modulePullback B S hS (D.mapAt A.T)).obj A.F).IsQuasicoherentOnSite :=
      isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ A.F A.quasicoherent
    have h := isFlatOver_of_isFlatOver_modulePushforward B S hS (D.mapAt A.T) hi
      (D.target.projection A.T) ((modulePullback B S hS (D.mapAt A.T)).obj A.F)
      (SheafOfModules.IsQuasicoherentOnSite.of_iso e A.quasicoherent)
      (IsFlatOver.of_iso B S hS _ e A.flat)
    rwa [D.mapAt_comp_projection] at h
  properSupport := by
    have hi := isClosedImmersion_mapAt hclosed A.T
    have hu : IsIso ((modulePullbackAdjunction B S hS (D.mapAt A.T)).unit.app A.F) :=
      (essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS _ hi A.F).1 hA
    let e := asIso ((modulePullbackAdjunction B S hS (D.mapAt A.T)).unit.app A.F)
    obtain ⟨hp, hU, hproper⟩ := A.properSupport
    have := isFinitePresentationOnSite_modulePullback B S hS (D.mapAt A.T) A.F
      A.finitePresentation
    have hpX : IsLocallyOfFiniteType B S hS (D.source.projection A.T).hom :=
      isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
        (D.source.isFinitePresentation_projection A.T).1
    have hsupp : supportOfSheaf B S hS (D.target.space A.T).1
        ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS (D.mapAt A.T)).obj
          ((modulePullback B S hS (D.mapAt A.T)).obj A.F))) = D.target.support A.T A.F :=
      (supportOfSheaf_eq_of_iso B S hS _ e).symm
    have hP : HasProperSupport B S hS (D.target.space A.T).2
        ((schemeSpaceFunctor B S hS).obj A.T.left).2 (D.target.projection A.T).hom hp
        ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS (D.mapAt A.T)).obj
          ((modulePullback B S hS (D.mapAt A.T)).obj A.F))) :=
      ⟨hsupp ▸ hU, isProperOver_congr rfl hsupp.symm hproper⟩
    obtain ⟨hcl, hpr⟩ := hasProperSupport_of_hasProperSupport_modulePushforward B S hS
      ((schemeSpaceFunctor B S hS).obj A.T.left).2 (D.mapAt A.T) hi
      (D.target.projection A.T).hom hp hpX (D.mapAt_hom_comp_projection_hom A.T) _ hP
    exact ⟨hpX, hcl, hpr⟩

include hclosed in
/-- The unit `G ⟶ π_{T,*}π_T^*G` is an isomorphism when `G` is a direct image. -/
theorem isIso_unit_mapAt_of_isClosedImmersion (A : CoherentObject D.target)
    (hA : (modulePushforward B S hS (D.mapAt A.T)).essImage A.F) :
    IsIso ((modulePullbackAdjunction B S hS (D.mapAt A.T)).unit.app A.F) :=
  (essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS _
    (isClosedImmersion_mapAt hclosed A.T) A.F).1 hA

/-- **A module which is a direct image is the direct image of its restriction**: the unit
`G ⟶ π_{T,*}π_T^*G` as an isomorphism. -/
def restrictUnitIsoOfIsClosedImmersion (A : CoherentObject D.target)
    (hA : (modulePushforward B S hS (D.mapAt A.T)).essImage A.F) :
    A.F ≅ (modulePushforward B S hS (D.mapAt A.T)).obj
      ((modulePullback B S hS (D.mapAt A.T)).obj A.F) :=
  haveI := isIso_unit_mapAt_of_isClosedImmersion hclosed A hA
  asIso ((modulePullbackAdjunction B S hS (D.mapAt A.T)).unit.app A.F)

/-! ### The vanishing condition -/

/-- **The situation of Stacks 083F cutting out the essential image** over an object `(T, G)` of
`Coh_{Y/B}`: the inclusion `ker η ⟶ G` of the kernel of the unit `η : G ⟶ π_{T,*}π_T^*G`, a map
of quasi-coherent modules on `Y_T`, over the projection `Y_T ⟶ T`. -/
def kernelUnitSituation (A : CoherentObject D.target) : ModuleMapSituation.{u, u} B S hS where
  X := D.target.space A.T
  Y := (schemeSpaceFunctor B S hS).obj A.T.left
  f := D.target.projection A.T
  F := kernel ((modulePullbackAdjunction B S hS (D.mapAt A.T)).unit.app A.F)
  G := A.F
  quasicoherent_F := by
    have : ((𝟭 _).obj A.F).IsQuasicoherentOnSite := A.quasicoherent
    have : ((modulePullback B S hS (D.mapAt A.T) ⋙ modulePushforward B S hS (D.mapAt A.T)).obj
        A.F).IsQuasicoherentOnSite :=
      isQuasicoherentOnSite_modulePushforward_isAffineHom B S hS (D.mapAt A.T)
        (isAffineHom_of_isClosedImmersion B S hS _ (isClosedImmersion_mapAt hclosed A.T)) _
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ A.F
          A.quasicoherent)
    exact isQuasicoherentOnSite_kernel_of_quasicoherent B S hS _ _ _
  quasicoherent_G := A.quasicoherent
  u := kernel.ι ((modulePullbackAdjunction B S hS (D.mapAt A.T)).unit.app A.F)

/-- The test scheme over `T'` of the situation of
`AlgebraicGeometry.Space.CoherentPushforwardSituation.kernelUnitSituation` given by a morphism
`T ⟶ T'` of test schemes over `B`. -/
abbrev kernelUnitTestScheme (A : CoherentObject D.target) {T : SchemesOver D.base}
    (h : T ⟶ A.T) : (kernelUnitSituation hclosed A).SchemesOver :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map h.left)

/-- **The base change of `Y_{T'} ⟶ T'` along `T ⟶ T'` is `Y_T`**, compatibly with the
projections to `Y_{T'}`. -/
def kernelUnitBaseChangeIso (A : CoherentObject D.target) {T : SchemesOver D.base}
    (h : T ⟶ A.T) :
    D.target.space T ≅ (kernelUnitSituation hclosed A).baseChangeSpace
      (kernelUnitTestScheme hclosed A h) :=
  (Space.isPullback_baseChangeMap D.f h).isoIsPullback _ _
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (D.target.projection A.T)
      ((schemeSpaceFunctor B S hS).map h.left))

/-- The comparison `Y_T ≅ Y_{T'} ×_{T'} T` lies over `Y_{T'}`. -/
theorem kernelUnitBaseChangeIso_hom_comp (A : CoherentObject D.target) {T : SchemesOver D.base}
    (h : T ⟶ A.T) :
    (kernelUnitBaseChangeIso hclosed A h).hom ≫
        (kernelUnitSituation hclosed A).baseChangeProjection (kernelUnitTestScheme hclosed A h) =
      D.target.relativeMap h :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- **The essential image is the vanishing condition.**  For a morphism `(h, ψ) : (T, E) ⟶
(T', G)` of `Coh_{Y/B}`, the module `E` is a direct image along `π_T` exactly when the base change
to `T` of the inclusion `ker η ⟶ G` vanishes, `η : G ⟶ π_{T',*}π_{T'}^*G` being the unit. -/
theorem essImage_iff_isZeroAt (A E : CoherentObject D.target) (m : CoherentHom E A) :
    (modulePushforward B S hS (D.mapAt E.T)).essImage E.F ↔
      (kernelUnitSituation hclosed A).IsZeroAt (modulePullbackSystem B S hS)
        (kernelUnitTestScheme hclosed A m.base) := by
  let e := @asIso _ _ _ _ m.fibre m.isIso_fibre
  have h1 : (modulePushforward B S hS (D.mapAt E.T)).essImage E.F ↔
      (modulePushforward B S hS (D.mapAt E.T)).essImage
        ((modulePullback B S hS (D.target.relativeMap m.base)).obj A.F) :=
    ⟨(modulePushforward B S hS (D.mapAt E.T)).essImage.prop_of_iso e.symm,
      (modulePushforward B S hS (D.mapAt E.T)).essImage.prop_of_iso e⟩
  rw [h1, essImage_modulePushforward_modulePullback_iff (D.mapAt A.T)
    (D.target.relativeMap m.base) (D.mapAt E.T) (D.source.relativeMap m.base)
    (D.isPullback_relativeMap m.base) (isClosedImmersion_mapAt hclosed A.T)
    (isClosedImmersion_mapAt hclosed E.T) A.F A.quasicoherent]
  exact modulePullback_map_eq_zero_iff_of_iso_comp (kernelUnitBaseChangeIso hclosed A m.base)
    _ (kernelUnitBaseChangeIso_hom_comp hclosed A m.base) _

variable (H : D.PreservesCoherence)

/-- **The comparison `(T, G) ⟶ (T, π_{T,*}π_T^*G)`**, lying over the identity of `T`, for a
module `G` which is a direct image along `π_T`. -/
def toPushforwardRestrictOfIsClosedImmersion (A : CoherentObject D.target)
    (hA : (modulePushforward B S hS (D.mapAt A.T)).essImage A.F) :
    CoherentHom A (pushforwardObject H (restrictObjectOfIsClosedImmersion hclosed A hA)) where
  base := 𝟙 A.T
  fibre := ((D.target.idComparison (modulePushforwardCoherence B S hS) A.T).app
      ((modulePushforward B S hS (D.mapAt A.T)).obj
        ((modulePullback B S hS (D.mapAt A.T)).obj A.F)) ≪≫
    (restrictUnitIsoOfIsClosedImmersion hclosed A hA).symm).hom
  isIso_fibre := Iso.isIso_hom _

omit hclosed in
/-- **An object of `Coh_{Y/B}` receiving a morphism to a direct image has module a direct
image.**  If `(h, ψ) : (T, G) ⟶ (T', π_{T',*}F)` is a morphism of `Coh_{Y/B}` then
`G ≅ Y_h^*π_{T',*}F ≅ π_{T,*}X_h^*F`, by `ψ` and the base change isomorphism of claim (b) of the
proof of Stacks 0DN9. -/
theorem essImage_modulePushforward_of_hom (E : CoherentObject D.target)
    (A₀ : CoherentObject D.source) (m : CoherentHom E (pushforwardObject H A₀)) :
    (modulePushforward B S hS (D.mapAt E.T)).essImage E.F :=
  ⟨_, ⟨(baseChangeIso H A₀ m.base).symm ≪≫ @asIso _ _ _ _ m.fibre m.isIso_fibre⟩⟩

include hclosed in
/-- **The essential image of the morphism of Stacks 0DN9 along a closed immersion.**  An object
`T` of the big fppf site of `U` is in the image of the first projection of the 2-fibre product of
`Coh_{X/B} ⟶ Coh_{Y/B}` with a scheme-valued point `y` exactly when the module of `y(T)` is a
direct image along the base change of `π`. -/
theorem exists_twoFibreProductFst_pushforwardBased_iff_essImage (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ (coherentBasedCategory D.target.categoryData).obj)
    (hy : y ⋙ (coherentBasedCategory D.target.categoryData).p = Over.map U.hom)
    (T : BigFppfOver B U.left.1 U.left.2) :
    (∃ a, (TwoFibreProductOver.fst (Over.map U.hom)
        (coherentBasedCategory D.source.categoryData).p
        (coherentBasedCategory D.target.categoryData).p y
        (pushforwardBased H).toFunctor).obj a = T) ↔
      (modulePushforward B S hS (D.mapAt (CoherentObject.T (D := D.target) (y.obj T)))).essImage
        (CoherentObject.F (D := D.target) (y.obj T)) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact essImage_modulePushforward_of_hom H (y.obj a.x) a.y a.iso.hom
  · intro hA
    let R := restrictObjectOfIsClosedImmersion hclosed (y.obj T) hA
    let : Category.{u + 1} (CoherentObject D.target) := D.target.categoryData.category
    let φ : y.obj T ⟶ pushforwardObject H R :=
      toPushforwardRestrictOfIsClosedImmersion hclosed H (y.obj T) hA
    have hlift' : (D.target.categoryData.projection ⋙
        CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.target.Y).IsHomLift
          (𝟙 (CoherentObject.T (D := D.target) (y.obj T)).left) φ := by
      have : (D.target.categoryData.projection ⋙
          CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.target.Y).map φ =
            𝟙 (CoherentObject.T (D := D.target) (y.obj T)).left := rfl
      rw [← this]
      exact Functor.IsHomLift.map (p := D.target.categoryData.projection ⋙
        CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.target.Y) φ
    have hiso : IsIso φ := Functor.isIso_of_isHomLift_id' _
      D.target.projection_isFiberedInGroupoids φ hlift'
    have hp : (D.target.categoryData.projection ⋙
        CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.target.Y) =
          (coherentBasedCategory D.target.categoryData).p :=
      coherentSiteProjection_eq D.target.categoryData
    have hlift : (coherentBasedCategory D.target.categoryData).p.IsHomLift
        (𝟙 ((coherentBasedCategory D.target.categoryData).p.obj (y.obj T))) φ := by
      rw [← hp]
      exact hlift'
    exact ⟨{ base := (coherentBasedCategory D.target.categoryData).p.obj (y.obj T)
             x := T
             y := R
             hx := (Functor.congr_obj hy T).symm
             hy := rfl
             iso := @asIso _ _ _ _ φ hiso
             vertical := hlift }, rfl⟩

/-! ### The closed locus -/

include hclosed in
/-- **Stacks 0DNB, the closed locus.**  For every scheme-valued point `y` of `Coh_{Y/B}` over an
object `U` of the big fppf site of `S`, there is a closed subscheme `V ⊆ U` through which an
object `T` of the big fppf site of `U` factors exactly when `y(T)` comes from `Coh_{X/B}`.

With `(T₀, G) = y(U)`, an object `T` comes from `Coh_{X/B}` exactly when the base change to `T` of
`ker η ⟶ G` vanishes, `η : G ⟶ π_{T₀,*}π_{T₀}^*G` being the unit, and that is cut out by a closed
subspace of `T₀` by Stacks 083M, the module `G` being of finite presentation, flat over `T₀` and
with support proper over `T₀`. -/
theorem hasClosedLocus_pushforwardBased :
    Stack.HasClosedLocus B S hS (pushforwardBased H) := by
  intro U y hy
  let U₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 _)
  let A : CoherentObject D.target := y.obj U₀
  let M := kernelUnitSituation hclosed A
  have hf : IsLocallyOfFinitePresentation B S hS M.f.hom :=
    (D.target.isFinitePresentation_projection A.T).1
  obtain ⟨hp, hU, hproper⟩ := A.properSupport
  obtain ⟨Z, hZ, -, hZiff⟩ :=
    M.zeroLocusRepresentation_of_hasProperSupport hf A.finitePresentation A.flat ⟨hU, hproper⟩
  obtain ⟨V₀, s, hs, hfac⟩ :=
    Space.exists_isClosedImmersion_factors_iff_of_isClosedSubspace B S hS A.T.left Z hZ
  have hA : A.T.left = (Over.map U.hom).obj U₀ := Functor.congr_obj hy U₀
  let s' : V₀ ⟶ (Over.map U.hom).obj U₀ := s ≫ eqToHom hA
  refine ⟨Over.mk s'.left, ?_, fun T => ?_⟩
  · change _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map s')
    rw [Functor.map_comp]
    infer_instance
  · rw [nonempty_hom_overMk_iff s' T,
      exists_twoFibreProductFst_pushforwardBased_iff_essImage hclosed H U y hy T]
    let t : T ⟶ U₀ := Over.homMk T.hom (Category.comp_id _)
    let m : CoherentHom (D := D.target) (y.obj T) A := y.map t
    rw [essImage_iff_isZeroAt hclosed A (y.obj T) m, hZiff]
    refine Iff.trans ?_ (hfac m.base.left).symm
    have hT : (CoherentObject.T (D := D.target) (y.obj T)).left = (Over.map U.hom).obj T :=
      Functor.congr_obj hy T
    have hm : m.base.left = eqToHom hT ≫ (Over.map U.hom).map t ≫ eqToHom hA.symm :=
      Functor.congr_hom hy t
    rw [hm]
    exact (exists_comp_eq_iff_of_iso (eqToIso hT) (eqToIso hA.symm) s _).symm

/-! ### Stacks 0DNB -/

include hclosed in
/-- **The morphism of Stacks 0DN9 along a closed immersion is representable by algebraic spaces
and a closed immersion**, for any claims (a) and (b) of the proof of Stacks 0DN9: it is fully
faithful and its essential image is cut out by a closed subscheme on every scheme-valued
point. -/
theorem isClosedImmersion_mkHom_pushforwardBased :
    Stack.IsRepresentableByAlgebraicSpaces B S hS
        (Bicategory.InducedBicategory.mkHom (pushforwardBased H) :
          coherentCFG D.source ⟶ coherentCFG D.target).hom ∧
      Stack.IsClosedImmersion B S hS
        (Bicategory.InducedBicategory.mkHom (pushforwardBased H) :
          coherentCFG D.source ⟶ coherentCFG D.target) := by
  let := D.source.categoryData.category
  let := D.target.categoryData.category
  have hff := fullyFaithfulPushforwardFunctorOfFullyFaithful H
    (fullyFaithfulPushforwardAtOfIsClosedImmersion hclosed)
  exact (Stack.isClosedImmersion_and_isRepresentableByAlgebraicSpaces_of_hasClosedLocus B S hS
    (Bicategory.InducedBicategory.mkHom (pushforwardBased H) :
      coherentCFG D.source ⟶ coherentCFG D.target) hff.full hff.faithful
    (hasClosedLocus_pushforwardBased hclosed H)).symm

end CoherentPushforwardSituation

/-- **The standing data of Stacks 0DN9 for a closed immersion** `π : X ⟶ Y` of algebraic spaces
which are separated and of finite presentation over `B`.  A closed immersion is finite
(Stacks 081Y), hence quasi-finite (Stacks 04NY). -/
def CoherentPushforwardSituation.ofIsClosedImmersion {A X Y : AlgebraicSpaces B S hS}
    (π : X ⟶ Y) (f : Y ⟶ A) (hclosed : IsClosedImmersion B S hS π.hom)
    (hsepX : IsSeparated B S hS (π ≫ f).hom) (hfpX : IsFinitePresentation B S hS (π ≫ f).hom)
    (hsepY : IsSeparated B S hS f.hom) (hfpY : IsFinitePresentation B S hS f.hom) :
    CoherentPushforwardSituation B S hS where
  base := A
  X := X
  Y := Y
  π := π
  f := f
  quasiFinite := isQuasiFinite_of_isFinite B S hS π.hom X.2 Y.2
    (isFinite_of_isClosedImmersion B S hS π.hom hclosed)
  separated_source := hsepX
  finitePresentation_source := hfpX
  separated_target := hsepY
  finitePresentation_target := hfpY

/-- **Stacks 0DNB.**  Let `B` be an algebraic space and let `π : X ⟶ Y` be a closed immersion of
algebraic spaces which are separated and of finite presentation over `B`, the structure morphism
of `X` being `π ≫ f` for the structure morphism `f : Y ⟶ B`.  Then the morphism
`Coh_{X/B} ⟶ Coh_{Y/B}` of Stacks 0DN9,
`AlgebraicGeometry.Space.CoherentPushforwardSituation.cohPushforward`, is a closed immersion: it
is representable by algebraic spaces, and every algebraic space representing its base change
along a scheme-valued point of `Coh_{Y/B}` is a closed subspace of that scheme (Stacks 04XB at
closed immersions), which together are Stacks 04YL (2).

The proof is the source's.  The morphism is fully faithful because `π_{T,*}` is, `π_T` being a
closed immersion (Stacks 04CJ); its essential image over a test scheme `T` is the objects
`(T, G)` with `G` a direct image along `π_T`, which is the vanishing of the inclusion
`ker(G ⟶ π_{T,*}π_T^*G) ⟶ G`, and that vanishing after base change is cut out by a closed
subspace of `T` by Stacks 083M. -/
@[stacks 0DNB "the whole statement: for a closed immersion π : X → Y of algebraic spaces \
separated and of finite presentation over B, the morphism Cohstack_{X/B} → Cohstack_{Y/B} of \
Tag 0DN9 is representable by algebraic spaces and a closed immersion in the sense of Tag 04XB, \
which together are representability by closed immersions (Tag 04YL (2))"]
theorem isRepresentableByAlgebraicSpaces_and_isClosedImmersion_cohPushforward
    {A X Y : AlgebraicSpaces B S hS} (π : X ⟶ Y) (f : Y ⟶ A)
    (hclosed : IsClosedImmersion B S hS π.hom)
    (hsepX : IsSeparated B S hS (π ≫ f).hom) (hfpX : IsFinitePresentation B S hS (π ≫ f).hom)
    (hsepY : IsSeparated B S hS f.hom) (hfpY : IsFinitePresentation B S hS f.hom) :
    let D := CoherentPushforwardSituation.ofIsClosedImmersion π f hclosed hsepX hfpX hsepY hfpY
    Stack.IsRepresentableByAlgebraicSpaces B S hS
        (Bicategory.InducedBicategory.mkHom D.cohPushforward :
          coherentCFG D.source ⟶ coherentCFG D.target).hom ∧
      Stack.IsClosedImmersion B S hS
        (Bicategory.InducedBicategory.mkHom D.cohPushforward :
          coherentCFG D.source ⟶ coherentCFG D.target) :=
  CoherentPushforwardSituation.isClosedImmersion_mkHom_pushforwardBased
    (D := CoherentPushforwardSituation.ofIsClosedImmersion π f hclosed hsepX hfpX hsepY hfpY)
    hclosed (CoherentPushforwardSituation.preservesCoherence _)

end AlgebraicGeometry.Space

end
