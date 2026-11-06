module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ReadingBundleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcChartFullness
public import
  StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianAtlasDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModulePullback

/-!
# The projective bundle of an inverse image

Let `f : Y ⟶ X` be a morphism of algebraic spaces and `ℰ` a finite locally free `𝒪_X`-module. The
reading of `f^*ℰ` on a scheme `T` over `Y` is the reading of `ℰ` on `T` viewed over `X`, through
the comparison `ψ^* f^* ℰ ≅ (ψ ≫ f)^* ℰ` of inverse images (Stacks 03LU), and these
identifications are compatible with the base-change comparisons of the readings. Hence the
projective bundles of the readings are identified, compatibly with base change, and the
identifications over the presenting chart of `Y` descend to a morphism
`φ : 𝐏(f^*ℰ) ⟶ 𝐏(ℰ)` over `f`. The square of `φ` over `f` is cartesian, since it is after the base
change to the presenting chart (Stacks 01OB, base change of the projective bundle).

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.readingPullbackIso`: the identification
  `(f^*ℰ)_ψ ≅ ℰ_{ψ ≫ f}`.
* `AlgebraicGeometry.Space.PrivateChern.readingBundlePullback`: the induced comparison of the
  projective bundles of the readings.
* `AlgebraicGeometry.Space.PrivateChern.projectiveBundleSpacePullback`: the comparison
  `φ : 𝐏(f^*ℰ) ⟶ 𝐏(ℰ)`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.readingPullbackIso_comp`: compatibility of the
  identifications with the base-change comparisons.
* `AlgebraicGeometry.Space.PrivateChern.readingBundleMap_comp_readingBundlePullback`: the
  comparisons of the bundles commute with the base-change morphisms.
* `AlgebraicGeometry.Space.PrivateChern.isPullback_projectiveBundleSpacePullback`:
  `𝐏(f^*ℰ) = Y ×_X 𝐏(ℰ)`.

## References

* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : Y ⟶ X) (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]

/-- The inverse image `f^*ℰ`. -/
abbrev pullbackModule : Modules.{u, u} B S hS Y.1 Y.2 := (modulePullback B S hS f).obj E

/-- The inverse image `f^*ℰ` of a quasi-coherent module is quasi-coherent. -/
instance isQuasicoherentOnSite_pullbackModule : (pullbackModule f E).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f E hE

/-- **The reading of `f^*ℰ` along `ψ` is the reading of `ℰ` along `ψ ≫ f`.** -/
def readingPullbackIso {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ Y) :
    schemeReading (pullbackModule f E) ψ ≅ schemeReading E (ψ ≫ f) :=
  (SmallEtale.restrictModule (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T)
      T.left.property).mapIso
    ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso
      (QuasiCoherentDescent.pullbackComparison B S hS ψ f (ψ ≫ f) rfl E).symm)

/-- **The identifications of the readings are compatible with the base-change comparisons**:
for `g : T' ⟶ T` with `g ≫ ψ = ψ'`, pulling back the identification at `ψ` and comparing is the
comparison of `f^*ℰ` followed by the identification at `ψ'`. -/
theorem readingPullbackIso_comp {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ Y} {ψ' : representedAlgebraicSpace B S hS T' ⟶ Y}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ')
    (w' : representedSpaceMap B S hS g ≫ (ψ ≫ f) = ψ' ≫ f) :
    (Scheme.Modules.pullback (siteSchemeHom g)).mapIso (readingPullbackIso f E ψ) ≪≫
        schemeReadingPullbackIso E hE g w' =
      schemeReadingPullbackIso (pullbackModule f E) inferInstance g w ≪≫
        readingPullbackIso f E ψ' := by
  rw [schemeReadingPullbackIso_eq, schemeReadingPullbackIso_eq, readingPullbackIso,
    readingPullbackIso, ← Iso.trans_assoc]
  refine (congrArg (· ≪≫ _) (representedZariskiModulePullbackIso_naturality_iso B S hS g
    (relativelyRepresentable_yoneda_map B S hS g)
    (isQuasicoherentOnSite_modulePullback_schemeReading (pullbackModule f E) inferInstance ψ)
    (isQuasicoherentOnSite_modulePullback_schemeReading E hE (ψ ≫ f))
    (QuasiCoherentDescent.pullbackComparison B S hS ψ f (ψ ≫ f) rfl E).symm)).trans ?_
  have key := QuasiCoherentDescent.pullbackComparison_trans B S hS
    (representedSpaceMap B S hS g) ψ f (ψ ≫ f) rfl ψ' w (ψ' ≫ f) w' rfl E
  have inner₀ : (modulePullback B S hS (representedSpaceMap B S hS g)).mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS ψ f (ψ ≫ f) rfl E).symm ≪≫
      (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) (ψ ≫ f)
        (ψ' ≫ f) w' E).symm =
      (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) ψ ψ' w
        (pullbackModule f E)).symm ≪≫
      (QuasiCoherentDescent.pullbackComparison B S hS ψ' f (ψ' ≫ f) rfl E).symm := by
    rw [Functor.mapIso_symm, ← Iso.trans_symm, ← Iso.trans_symm, key]
  have inner : (representedSmallEtaleModuleEquivalence B S hS T').inverse.mapIso
        ((modulePullback B S hS (representedSpaceMap B S hS g)).mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS ψ f (ψ ≫ f) rfl E).symm) ≪≫
      (representedSmallEtaleModuleEquivalence B S hS T').inverse.mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) (ψ ≫ f)
          (ψ' ≫ f) w' E).symm =
      (representedSmallEtaleModuleEquivalence B S hS T').inverse.mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) ψ ψ' w
          (pullbackModule f E)).symm ≪≫
      (representedSmallEtaleModuleEquivalence B S hS T').inverse.mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS ψ' f (ψ' ≫ f) rfl E).symm := by
    refine Iso.ext ?_
    have := congrArg (fun i => (representedSmallEtaleModuleEquivalence B S hS T').inverse.map i.hom)
      inner₀
    simp only [Iso.trans_hom] at this
    simp only [Iso.trans_hom]
    exact (Functor.map_comp _ _ _).symm.trans (this.trans (Functor.map_comp _ _ _))
  rw [Iso.trans_assoc, Iso.trans_assoc, ← Functor.mapIso_trans, ← Functor.mapIso_trans, inner]

/-! ### Unitality of the inverse images of modules on schemes -/

section Unitality

variable {X₀ Y₀ : Scheme.{u}} (q : X₀ ⟶ Y₀) (M : Y₀.Modules)

/-- The comparison `q^* 𝟙^* M ≅ (q ≫ 𝟙)^* M ≅ q^* M` is `q^*` of the unit `𝟙^* M ≅ M`. -/
theorem pullbackComp_id_hom_app :
    (Scheme.Modules.pullbackComp q (𝟙 Y₀)).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.comp_id q)).hom.app M =
      (Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackId Y₀).hom.app M) := by
  have h := congrArg (fun φ => φ.app M) (Scheme.Modules.pseudofunctor_left_unitality q)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    eqToHom_app] at h
  have : Epi ((Scheme.Modules.pullbackComp q (𝟙 Y₀)).inv.app M) :=
    ⟨fun _ _ e => by simpa using congrArg ((Scheme.Modules.pullbackComp q (𝟙 Y₀)).hom.app M ≫ ·) e⟩
  rw [← cancel_epi ((Scheme.Modules.pullbackComp q (𝟙 Y₀)).inv.app M), ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp]
  refine (?_ : _ = eqToHom _).trans (h.symm.trans (congrArg (_ ≫ ·) (Category.comp_id _)))
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app]

/-- The comparison `𝟙^* q^* M ≅ (𝟙 ≫ q)^* M ≅ q^* M` is the unit `𝟙^* (q^* M) ≅ q^* M`. -/
theorem pullbackComp_id_left_hom_app :
    (Scheme.Modules.pullbackComp (𝟙 X₀) q).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.id_comp q)).hom.app M =
      (Scheme.Modules.pullbackId X₀).hom.app ((Scheme.Modules.pullback q).obj M) := by
  have h := congrArg (fun φ => φ.app M) (Scheme.Modules.pseudofunctor_right_unitality q)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at h
  have : Epi ((Scheme.Modules.pullbackComp (𝟙 X₀) q).inv.app M) :=
    ⟨fun _ _ e => by simpa using congrArg ((Scheme.Modules.pullbackComp (𝟙 X₀) q).hom.app M ≫ ·) e⟩
  rw [← cancel_epi ((Scheme.Modules.pullbackComp (𝟙 X₀) q).inv.app M), ← Category.assoc,
    Iso.inv_hom_id_app]
  refine (Category.id_comp _).trans ((?_ : _ = eqToHom _).trans
    (h.symm.trans (congrArg (_ ≫ ·) (Category.comp_id _))))
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app]

end Unitality

/-! ### The comparison of the projective bundles of the readings -/

/-- The base-change morphism only depends on the morphism, up to `pullbackCongr`. -/
theorem projectiveBundleBaseChange_congr {X₀ Y₀ : Scheme.{u}} {g₁ g₂ : X₀ ⟶ Y₀} (h : g₁ = g₂)
    (M : Y₀.Modules) [M.IsQuasicoherent] (M' : X₀.Modules) [M'.IsQuasicoherent]
    (c : M' ≅ (Scheme.Modules.pullback g₁).obj M) :
    Stacks.RelativeProj.projectiveBundleBaseChange g₁ M M' c =
      Stacks.RelativeProj.projectiveBundleBaseChange g₂ M M'
        (c ≪≫ (Scheme.Modules.pullbackCongr h).app M) := by
  subst h
  congr 1

/-- The identification `(f^*ℰ)_ψ ≅ 𝟙^*ℰ_{ψ ≫ f}` along which the projective bundles of the readings
are compared. -/
def readingBundlePullbackIso {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ Y) :
    schemeReading (pullbackModule f E) ψ ≅
      (Scheme.Modules.pullback (𝟙 ((BigFppfOver.toScheme B S hS).obj T))).obj
        (schemeReading E (ψ ≫ f)) :=
  readingPullbackIso f E ψ ≪≫ ((Scheme.Modules.pullbackId _).app (schemeReading E (ψ ≫ f))).symm

omit hE in
/-- The inverse of `readingBundlePullbackIso` is the unit `𝟙^* ℰ_{ψ ≫ f} ≅ ℰ_{ψ ≫ f}` followed by
the inverse of `readingPullbackIso`. -/
theorem readingBundlePullbackIso_inv {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ Y) :
    (readingBundlePullbackIso f E ψ).inv =
      (Scheme.Modules.pullbackId _).hom.app (schemeReading E (ψ ≫ f)) ≫
        (readingPullbackIso f E ψ).inv :=
  rfl

/-- **The comparison `𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f})`** over `T`. -/
def readingBundlePullback {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ Y) :
    readingBundle (pullbackModule f E) ψ ⟶ readingBundle E (ψ ≫ f) :=
  Stacks.RelativeProj.projectiveBundleBaseChange (𝟙 _) (schemeReading E (ψ ≫ f))
    (schemeReading (pullbackModule f E) ψ) (readingBundlePullbackIso f E ψ)

/-- **The comparisons commute with the base-change morphisms.** -/
theorem readingBundleMap_comp_readingBundlePullback {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ Y} {ψ' : representedAlgebraicSpace B S hS T' ⟶ Y}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ')
    (w' : representedSpaceMap B S hS g ≫ (ψ ≫ f) = ψ' ≫ f) :
    readingBundleMap (pullbackModule f E) g w ≫ readingBundlePullback f E ψ =
      readingBundlePullback f E ψ' ≫ readingBundleMap E g w' := by
  have hcomp := readingPullbackIso_comp f E g w w'
  have hθ : (schemeReadingPullbackIso (pullbackModule f E) inferInstance g w).symm ≪≫
      (Scheme.Modules.pullback (siteSchemeHom g)).mapIso (readingPullbackIso f E ψ) =
      readingPullbackIso f E ψ' ≪≫ (schemeReadingPullbackIso E hE g w').symm := by
    have key : ∀ {C : Type _} [Category C] {a b c d : C} (A : a ≅ b) (P : a ≅ c) (Q : c ≅ d)
        (R : b ≅ d), P ≪≫ Q = A ≪≫ R → A.symm ≪≫ P = R ≪≫ Q.symm := by
      intro C _ a b c d A P Q R h
      calc A.symm ≪≫ P = A.symm ≪≫ (P ≪≫ Q) ≪≫ Q.symm := by
            rw [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
        _ = R ≪≫ Q.symm := by rw [h, Iso.trans_assoc, Iso.symm_self_id_assoc]
    exact key _ _ _ _ hcomp
  rw [readingBundleMap, readingBundleMap, readingBundlePullback, readingBundlePullback,
    Stacks.RelativeProj.projectiveBundleBaseChange_comp (siteSchemeHom g) (𝟙 _) _ _ _ _ _
      (((schemeReadingPullbackIso (pullbackModule f E) inferInstance g w).symm ≪≫
        (Scheme.Modules.pullback (siteSchemeHom g)).mapIso (readingPullbackIso f E ψ)) ≪≫
          (Scheme.Modules.pullbackCongr (Category.comp_id _)).symm.app _) ?_,
    Stacks.RelativeProj.projectiveBundleBaseChange_comp (𝟙 _) (siteSchemeHom g) _ _ _ _ _
      ((readingPullbackIso f E ψ' ≪≫ (schemeReadingPullbackIso E hE g w').symm) ≪≫
          (Scheme.Modules.pullbackCongr (Category.id_comp _)).symm.app _) ?_,
    projectiveBundleBaseChange_congr (Category.comp_id _),
    projectiveBundleBaseChange_congr (Category.id_comp _), hθ]
  · congr 1
  · simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv, readingBundlePullbackIso_inv]
    rw [← Category.assoc, pullbackComp_id_left_hom_app]
    have hn := (Scheme.Modules.pullbackId _).hom.naturality
      (schemeReadingPullbackIso E hE g w').hom
    exact ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (readingPullbackIso f E ψ').inv)
      hn).trans (Category.assoc _ _ _))).symm
  · simp only [Iso.trans_inv, Iso.symm_inv, Iso.app_inv,
      Functor.mapIso_inv, Functor.map_comp, Category.assoc, readingBundlePullbackIso_inv]
    rw [← Category.assoc, ← Category.assoc, pullbackComp_id_hom_app]
    exact Category.assoc _ _ _

/-- The comparison `𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f})` commutes with the projections to `T`. -/
@[reassoc]
theorem readingBundlePullback_toBase {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ Y) :
    readingBundlePullback f E ψ ≫ readingBundleToBase E (ψ ≫ f) =
      readingBundleToBase (pullbackModule f E) ψ :=
  (Stacks.RelativeProj.isPullback_projectiveBundleBaseChange (𝟙 _) (schemeReading E (ψ ≫ f))
    (schemeReading (pullbackModule f E) ψ)
    (readingBundlePullbackIso f E ψ)).w.trans
    (Category.comp_id _)

/-- The square formed by the comparison `𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f})` and the projections to `T`
is cartesian. -/
theorem isPullback_readingBundlePullback {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ Y) :
    IsPullback (readingBundlePullback f E ψ) (readingBundleToBase (pullbackModule f E) ψ)
      (readingBundleToBase E (ψ ≫ f)) (𝟙 _) :=
  Stacks.RelativeProj.isPullback_projectiveBundleBaseChange (𝟙 _) (schemeReading E (ψ ≫ f))
    (schemeReading (pullbackModule f E) ψ)
    (readingBundlePullbackIso f E ψ)

/-! ### The comparison of the projective bundles -/

section Space

variable (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

include hfree in
/-- The inverse image `f^*ℰ` of a finite locally free module is finite locally free. -/
theorem isFiniteLocallyFreeOnSite_pullbackModule :
    SheafOfModules.IsFiniteLocallyFreeOnSite (pullbackModule f E) :=
  isFiniteLocallyFreeOnSite_modulePullback B S hS f E hE hfree

/-- The comparison `𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ_{ψ ≫ f})`, as a morphism of the site. -/
def readingBundleSitePullback {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ Y) :
    readingBundleSite (pullbackModule f E) (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ ⟶
      readingBundleSite E hfree (ψ ≫ f) :=
  Over.homMk (ObjectProperty.homMk (readingBundlePullback f E ψ)) (by
    apply ObjectProperty.hom_ext
    change readingBundlePullback f E ψ ≫ readingBundleToBase E (ψ ≫ f) ≫ T.hom.hom =
      readingBundleToBase (pullbackModule f E) ψ ≫ T.hom.hom
    rw [readingBundlePullback_toBase_assoc])

/-- The square formed by `readingBundleSitePullback` and the projections to `T` in the site is
cartesian. -/
theorem isPullback_readingBundleSitePullback {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ Y) :
    IsPullback (readingBundleSitePullback f E hfree ψ)
      (readingBundleSiteToBase (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ)
      (readingBundleSiteToBase E hfree (ψ ≫ f)) (𝟙 T) :=
  IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) (by
    rw [CategoryTheory.Functor.map_id]
    exact isPullback_readingBundlePullback f E ψ)

/-- The comparisons `readingBundleSitePullback` commute with the base-change morphisms of the
site. -/
theorem readingBundleSiteMap_comp_readingBundleSitePullback {T' T : BigFppfOver B S hS}
    (g : T' ⟶ T) {ψ : representedAlgebraicSpace B S hS T ⟶ Y}
    {ψ' : representedAlgebraicSpace B S hS T' ⟶ Y}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ')
    (w' : representedSpaceMap B S hS g ≫ (ψ ≫ f) = ψ' ≫ f) :
    readingBundleSiteMap (pullbackModule f E) (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)
        g w ≫ readingBundleSitePullback f E hfree ψ =
      readingBundleSitePullback f E hfree ψ' ≫ readingBundleSiteMap E hfree g w' :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _
    (readingBundleMap_comp_readingBundlePullback f E g w w'))

/-- The comparison `𝐏((f^*ℰ)_ψ) ⟶ 𝐏(ℰ)`, over `ψ ≫ f`. -/
abbrev readingBundlePullbackToSpace {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ Y) :
    yoneda.obj (readingBundleSite (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ψ) ⟶
      (projectiveBundle E hfree).1 :=
  yoneda.map (readingBundleSitePullback f E hfree ψ) ≫ readingBundleToSpace (ψ ≫ f) E hfree

/-- For `g : T' ⟶ T` with `g ≫ ψ = ψ'`, the base-change morphism followed by the comparison at `ψ`
is the comparison at `ψ'`. -/
theorem readingBundleSiteMap_comp_readingBundlePullbackToSpace {T' T : BigFppfOver B S hS}
    (g : T' ⟶ T) {ψ : representedAlgebraicSpace B S hS T ⟶ Y}
    {ψ' : representedAlgebraicSpace B S hS T' ⟶ Y}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') :
    yoneda.map (readingBundleSiteMap (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) g w) ≫
        readingBundlePullbackToSpace f E hfree ψ =
      readingBundlePullbackToSpace f E hfree ψ' := by
  have w' : representedSpaceMap B S hS g ≫ (ψ ≫ f) = ψ' ≫ f := by
    rw [← Category.assoc, w]
  rw [readingBundlePullbackToSpace, ← Category.assoc, ← Functor.map_comp,
    readingBundleSiteMap_comp_readingBundleSitePullback f E hfree g w w', Functor.map_comp,
    Category.assoc, readingBundleSiteMap_comp_readingBundleToSpace E hfree g w']

/-- Over a morphism of étale charts `h : V' ⟶ V` of `Y`, the morphism of chart bundles of `f^*ℰ`
is compatible with the morphisms of the chart bundles to `𝐏(ℰ)`. -/
theorem chartSiteMap_comp_readingBundlePullbackToSpace {V V' : SmallEtale B S hS Y.1}
    (h : V' ⟶ V) :
    yoneda.map ((projectiveBundleChartFamily (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).siteMap h) ≫
        readingBundlePullbackToSpace f E hfree (chartToSpace B S hS Y V) =
      readingBundlePullbackToSpace f E hfree (chartToSpace B S hS Y V') :=
  readingBundleSiteMap_comp_readingBundlePullbackToSpace f E hfree _
    (representedSpaceMap_toOver_map_comp_chartToSpace h)

/-- The two projections of the relation of the presentation of `Y`, followed by the comparison
over the presenting chart, agree. -/
theorem chartRelation_comp_readingBundlePullbackToSpace :
    yoneda.map ((projectiveBundleChartFamily (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E
            hfree)).siteMap (presentationRelationTargetHom (projectiveBundlePresentation Y))) ≫
        readingBundlePullbackToSpace f E hfree (chartToSpace B S hS Y (bundleBaseChart Y)) =
      yoneda.map ((projectiveBundleChartFamily (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E
            hfree)).siteMap (presentationRelationSourceHom (projectiveBundlePresentation Y))) ≫
        readingBundlePullbackToSpace f E hfree (chartToSpace B S hS Y (bundleBaseChart Y)) := by
  rw [chartSiteMap_comp_readingBundlePullbackToSpace,
      chartSiteMap_comp_readingBundlePullbackToSpace]

/-- **The comparison `φ : 𝐏(f^*ℰ) ⟶ 𝐏(ℰ)`**, descended from the chart `𝐏((f^*ℰ)_U) ⟶ 𝐏(ℰ)` over the
presenting chart `U` of `Y`. -/
def projectiveBundleSpacePullback :
    (projectiveBundle (pullbackModule f E)
      (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).1 ⟶
      (projectiveBundle E hfree).1 :=
  (existsUnique_desc_of_surjective_etale_atlas B S hS
    (projectiveBundle _ (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).property.isSheaf
    _ (isPullback_projectiveBundleSpaceChart_relation _ _)
    ((projectiveBundleChartPresentation _ _).surjective) ((projectiveBundleChartPresentation _
        _).etale)
    (projectiveBundle E hfree).property.isSheaf
    (readingBundlePullbackToSpace f E hfree (chartToSpace B S hS Y (bundleBaseChart Y)))
    (chartRelation_comp_readingBundlePullbackToSpace f E hfree)).exists.choose

/-- The chart of `𝐏(f^*ℰ)` followed by `φ` is the comparison `𝐏((f^*ℰ)_U) ⟶ 𝐏(ℰ)` over the
presenting chart `U` of `Y`. -/
theorem projectiveBundleSpaceChart_comp_projectiveBundleSpacePullback :
    projectiveBundleChart (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ≫
        projectiveBundleSpacePullback f E hfree =
      readingBundlePullbackToSpace f E hfree (chartToSpace B S hS Y (bundleBaseChart Y)) := by
  unfold projectiveBundleSpacePullback
  exact Exists.choose_spec (p := fun d => _ ≫ d = _) _

/-- The chart of `𝐏(f^*ℰ)`, followed by `φ`, is the base change of `𝐏(ℰ)` along `U ⟶ X`. -/
theorem isPullback_projectiveBundleSpaceChart_comp_projectiveBundleSpacePullback :
    IsPullback (projectiveBundleChart (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree) ≫
        projectiveBundleSpacePullback f E hfree)
      (yoneda.map ((projectiveBundleChartFamily (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).siteToChart (bundleBaseChart Y)))
      (projectiveBundleProj E hfree).hom ((bundleBaseChart Y).obj.hom ≫ f.hom) := by
  rw [projectiveBundleSpaceChart_comp_projectiveBundleSpacePullback]
  have h := ((isPullback_readingBundleSitePullback f E hfree
    (chartToSpace B S hS Y (bundleBaseChart Y))).map yoneda).paste_horiz
      (isPullback_readingBundleToSpace (chartToSpace B S hS Y (bundleBaseChart Y) ≫ f) E hfree)
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

/-- **`φ` lies over `f`.** -/
theorem projectiveBundleSpacePullback_comp_proj :
    projectiveBundleSpacePullback f E hfree ≫ (projectiveBundleProj E hfree).hom =
      (projectiveBundleProj (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).hom ≫ f.hom := by
  refine hom_ext_of_etale_atlas B S hS
    (projectiveBundle _ (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).property.isSheaf
    X.property.isSheaf _ ((projectiveBundleChartPresentation _ _).surjective)
    ((projectiveBundleChartPresentation _ _).etale) ?_
  rw [← Category.assoc,
    (isPullback_projectiveBundleSpaceChart_comp_projectiveBundleSpacePullback f E hfree).w,
    ← Category.assoc]
  exact (congrArg (· ≫ f.hom) (isPullback_projectiveBundleProj _ _).w.symm).trans
    (Category.assoc _ _ _)

/-- **`𝐏(f^*ℰ) = Y ×_X 𝐏(ℰ)`** (Stacks 01OB, base change of the projective bundle): the comparison
`φ` over `f` is cartesian. -/
theorem isPullback_projectiveBundleSpacePullback :
    IsPullback (projectiveBundleSpacePullback f E hfree)
      (projectiveBundleProj (pullbackModule f E)
        (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).hom
      (projectiveBundleProj E hfree).hom f.hom :=
  isPullback_of_isPullback_atlas B S hS
    (projectiveBundle _ (isFiniteLocallyFreeOnSite_pullbackModule f E hfree)).property.isSheaf
    (projectiveBundle E hfree).property.isSheaf Y.property.isSheaf X.property.isSheaf
    (projectiveBundleSpacePullback_comp_proj f E hfree) (projectiveBundlePresentation Y).surjective
    (projectiveBundlePresentation Y).etale (isPullback_projectiveBundlePresentation Y)
    (isPullback_projectiveBundleProj _ _)
    (isPullback_projectiveBundleSpaceChart_comp_projectiveBundleSpacePullback f E hfree)
    (((projectiveBundleChartFamily _ _).isPullback_siteMap (presentationRelationTargetHom
        (projectiveBundlePresentation Y))).map yoneda)
    ((projectiveBundleChartFamily _ _).isPullback_siteMap (presentationRelationSourceHom
        (projectiveBundlePresentation Y))).w
    (isPullback_projectiveBundleSpaceChart_relation _ _).w

end Space

end AlgebraicGeometry.Space.PrivateChern

end
