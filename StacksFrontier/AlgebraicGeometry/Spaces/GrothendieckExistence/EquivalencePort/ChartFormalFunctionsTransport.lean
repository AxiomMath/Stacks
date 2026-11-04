module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartAdicQuotientTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.CompletionQuotientCommute
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.CoherentAdicLimitFactorization

namespace CategoryTheory.C1573
end CategoryTheory.C1573
namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The theorem on formal functions over an affine chart, for the comparison of Stacks 08BD

Let `f : X ⟶ Y` be a representable proper morphism of algebraic spaces with `Y` locally
Noetherian, `𝒥 ⊆ 𝒪_Y` a quasi-coherent sheaf of ideals, `𝓘 = f⁻¹𝒥 · 𝒪_X` and `𝓕` a coherent
`𝒪_X`-module.  Over every affine étale chart `V` of `Y` the comparison
`c : (f_*𝓕)^ ⟶ (f_*(𝓕/𝓘ⁿ⁺¹𝓕))_n` induces a bijection on the inverse limits of the sections over
`V` (`AlgebraicGeometry.Space.bijective_adicSectionLimitMap_directImageCompletionComparison`).

Over `V` both towers are identified with the corresponding towers of global sections for the
proper morphism of schemes `f_V : V ×_Y X ⟶ V`
(`AlgebraicGeometry.Space.C1573.chartPushforwardAdicQuotientEquiv`,
`AlgebraicGeometry.Space.C1573.chartDirectImageAdicQuotientIso`), compatibly with the transition
maps and with the comparisons, and the scheme statement is the theorem on formal functions,
`Stacks.Coherent.isIso_limMap_affineSections_pushforwardCompletionComparison_affineOpen`.

## References

* [Stacks Project, Tag 08BD](https://stacks.math.columbia.edu/tag/08BD)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

open _root_.CategoryTheory.C1573
attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- Two composites out of a common first factor agree, given the three squares they are built
from.  Stated in an arbitrary category, so that it can be instantiated where the category of
modules carries two spellings. -/
theorem CategoryTheory.C1573.comp_comp_eq_of_three_squares {C : Type*} [Category C]
    {A B B' D E : C}
    {p : A ⟶ B} {Φ : B ⟶ D} {t : D ⟶ E} {m : B ⟶ B'} {Φ' : B' ⟶ E} {a : A ⟶ D} {p' : A ⟶ B'}
    (h1 : p ≫ Φ = a) (h2 : p ≫ m = p') (h3 : a ≫ t = p' ≫ Φ') :
    p ≫ Φ ≫ t = p ≫ m ≫ Φ' := by
  rw [← Category.assoc, h1, h3, ← h2, Category.assoc]

/-- Conjugating a commutative square of isomorphisms. -/
theorem CategoryTheory.C1573.comp_inv_eq_inv_comp_of_square {C : Type*} [Category C]
    {A A' B B' : C}
    (e₁ : A ≅ A') (e₂ : B ≅ B') (t : A' ⟶ B') (m : A ⟶ B) (h : e₁.hom ≫ t = m ≫ e₂.hom) :
    t ≫ e₂.inv = e₁.inv ≫ m := by
  rw [Iso.eq_inv_comp, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- An element of a limit of a tower of modules is determined by its projections. -/
private theorem Stacks.Coherent.C1573.moduleLimit_ext {A : Type u} [CommRing A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{u} A) {x y : (limit F : ModuleCat.{u} A)}
    (h : ∀ n, (limit.π F (op n)).hom x = (limit.π F (op n)).hom y) : x = y :=
  Concrete.limit_ext F x y fun j => by
    cases j with
    | op n => exact h n

/-- The projections of the element attached to a compatible family are its members. -/
private theorem Stacks.Coherent.C1573.limit_π_moduleLimitTowerEquiv_symm {A : Type u} [CommRing A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (y : Stacks.Coherent.moduleTowerLimit (fun n => F.obj (op n))
      (fun n => (F.map (homOfLE (Nat.le_succ n)).op).hom)) (n : ℕ) :
    (limit.π F (op n)).hom ((Stacks.Coherent.moduleLimitTowerEquiv F).symm y) = y.1 n := by
  rw [← Stacks.Coherent.moduleLimitTowerEquiv_apply_coe, LinearEquiv.apply_symm_apply]

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573

/-- A compatible family of sections over a chart is determined by its members in positive
degree. -/
private theorem C1573.adicSectionLimit_ext {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S}
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hZ : IsAlgebraicSpace B S hS Z}
    {W : (smallEtaleRingedSite B S hS Z hZ).C} {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS Z hZ}
    {x x' : adicSectionLimit B S hS Z hZ W E} (h : ∀ n, x.1 (n + 1) = x'.1 (n + 1)) : x = x' := by
  refine Subtype.ext (funext fun k => ?_)
  cases k with
  | zero => exact funext fun i => Fin.elim0 i
  | succ n => exact h n

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
  (V : SmallEtale B S hS Y.1) [IsAffine (chartScheme V)]
  (J : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
  [IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))]
  (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)

/-- The comparison `𝓕|_U / ℐⁿ⁺¹ ⟶ (𝓕/𝓘ⁿ⁺¹𝓕)|_U` is compatible with the transition maps. -/
theorem C1573.chartAdicQuotientHom_transition (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
    (n : ℕ) :
    chartAdicQuotientHom B S hS f hf V J F hF hJ (n + 1) ≫
        (chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).map
          (smallEtaleAdicQuotientTransition B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J)
            (n + 1) F) =
      ((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
          (chartCoherentModule B S hS f hf V F hF)).obj.map (homOfLE (Nat.le_succ n)).op ≫
        chartAdicQuotientHom B S hS f hf V J F hF hJ n := by
  have := Stacks.Algebraization.epi_completionProjection _ (chartBaseChangeIdeal B S hS f hf V J)
    (chartCoherentModule B S hS f hf V F hF) (n + 1)
  refine (cancel_epi (C := (chartScheme ((smallBaseChange B S hS f hf).obj V)).Modules)
    (Stacks.Algebraization.completionProjection _ (chartBaseChangeIdeal B S hS f hf V J)
      (chartCoherentModule B S hS f hf V F hF) (n + 1))).1 ?_
  refine CategoryTheory.C1573.comp_comp_eq_of_three_squares
    (completionProjection_comp_chartAdicQuotientHom B S hS f hf V J F hF hJ (n + 1))
    (Stacks.Algebraization.completionProjection_transition _ _ _ n) ?_
  refine (Functor.map_comp _ _ _).symm.trans ?_
  exact (congrArg (chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).map
    (smallEtaleAdicQuotientProjection_comp_transition B S hS X.1 X.2
      (inverseImageIdeal B S hS f hf J) (n + 1) F)).trans
    (completionProjection_comp_chartAdicQuotientHom B S hS f hf V J F hF hJ n).symm

/-- **The identification of the sections of `f_*(𝓕/𝓘ⁿ⁺¹𝓕)` over `V` is compatible with the
transition maps.** -/
theorem C1573.chartDirectImageAdicQuotientIso_transition
    (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
    (hJfg : ∀ Q : SmallEtale B S hS Y.1, IsAffine (chartScheme Q) →
      (chartSectionsIdeal B S hS Y J Q).FG) (n : ℕ)
    (y : ((modulePushforward B S hS f).obj (smallEtaleAdicQuotient B S hS X.1 X.2
      (inverseImageIdeal B S hS f hf J) (n + 1 + 1) F)).val.obj (op V)) :
    (chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).hom
        (((modulePushforward B S hS f).map (smallEtaleAdicQuotientTransition B S hS X.1 X.2
          (inverseImageIdeal B S hS f hf J) (n + 1) F)).val.app (op V) y) =
      Scheme.Modules.Hom.app
        ((Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)).map
          (((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
            (chartCoherentModule B S hS f hf V F hF)).obj.map (homOfLE (Nat.le_succ n)).op)) ⊤
        ((chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg (n + 1)).hom y) := by
  rw [chartDirectImageAdicQuotientIso_hom_apply, chartDirectImageAdicQuotientIso_hom_apply,
    chartBaseChangeSectionsMap_naturality]
  have h := CategoryTheory.C1573.comp_inv_eq_inv_comp_of_square
    (chartAdicQuotientIso B S hS f hf V J F hF hJ hJfg (n + 1))
    (chartAdicQuotientIso B S hS f hf V J F hF hJ hJfg n) _ _
    (chartAdicQuotientHom_transition B S hS f hf V J F hF hJ n)
  exact ConcreteCategory.congr_hom (congrArg (fun k => Scheme.Modules.Hom.app k _) h)
    (chartBaseChangeSectionsMap B S hS f hf V _ y)

section Pushforward

variable [IsNoetherianRing Γ(chartScheme V, ⊤)] (hfp : IsProper B S hS f.hom)
  (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
  (hM : IsCartesianOnAffineCharts ((modulePushforward B S hS f).obj F))

/-- **The identification of the sections of `(f_*𝓕)/𝒥ⁿ⁺¹` over `V` is compatible with the
transition maps.** -/
theorem C1573.chartPushforwardAdicQuotientEquiv_transition (n : ℕ)
    (y : (smallEtaleAdicQuotient B S hS Y.1 Y.2 J (n + 1 + 1)
      ((modulePushforward B S hS f).obj F)).val.obj (op V)) :
    chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n
        ((smallEtaleAdicQuotientTransition B S hS Y.1 Y.2 J (n + 1)
          ((modulePushforward B S hS f).obj F)).val.app (op V) y) =
      Scheme.Modules.Hom.app (((Stacks.Algebraization.completionFunctor _
          (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))).obj
            (chartPushforwardCoherent B S hS f hf V F hF hfp)).obj.map
              (homOfLE (Nat.le_succ n)).op) ⊤
        (chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM (n + 1) y) := by
  obtain ⟨x, rfl⟩ : ∃ x, (smallEtaleAdicQuotientProjection B S hS Y.1 Y.2 J (n + 1 + 1)
      ((modulePushforward B S hS f).obj F)).val.app (op V) x = y :=
    surjective_val_app_idealPowerQuotient_π B S hS Y.1 Y.2 J hJ _ hM (n + 1 + 1)
      ‹IsAffine (chartScheme V)› y
  have h1 := congrArg (fun k => k.val.app (op V) x)
    (smallEtaleAdicQuotientProjection_comp_transition B S hS Y.1 Y.2 J (n + 1)
      ((modulePushforward B S hS f).obj F))
  refine (congrArg (chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n)
    h1).trans ?_
  rw [chartPushforwardAdicQuotientEquiv_projection, chartPushforwardAdicQuotientEquiv_projection,
    chartPushforwardProjection_apply, chartPushforwardProjection_apply]
  exact (ConcreteCategory.congr_hom (congrArg (fun k => Scheme.Modules.Hom.app k ⊤)
    (Stacks.Algebraization.completionProjection_transition _ _
      (chartPushforwardCoherent B S hS f hf V F hF hfp) n)) _).symm

variable (hJfg : ∀ Q : SmallEtale B S hS Y.1, IsAffine (chartScheme Q) →
  (chartSectionsIdeal B S hS Y J Q).FG)

/-- The families of a compatible family of sections of `(f_*𝓕)^` over `V`, read on the scheme
side, are compatible. -/
theorem C1573.chartPushforwardAdicQuotientEquiv_family
    (x : adicSectionLimit B S hS Y.1 Y.2 V
      (adicQuotientSystem B S hS Y.1 Y.2 J ((modulePushforward B S hS f).obj F))) (n : ℕ) :
    Scheme.Modules.Hom.app (((Stacks.Algebraization.completionFunctor _
        (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))).obj
          (chartPushforwardCoherent B S hS f hf V F hF hfp)).obj.map
            (homOfLE (Nat.le_succ n)).op) ⊤
        (chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM (n + 1)
          (x.1 (n + 1 + 1))) =
      chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n (x.1 (n + 1)) := by
  refine (chartPushforwardAdicQuotientEquiv_transition B S hS f hf V J F hF hfp hJ hM n
    (x.1 (n + 1 + 1))).symm.trans ?_
  refine congrArg (chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n) ?_
  refine Eq.trans ?_ (x.2 (n + 1))
  exact (congrArg (fun k => k.val.app (op V) (x.1 (n + 1 + 1)))
    (adicQuotientSystem_map_succ B S hS Y.1 Y.2 J ((modulePushforward B S hS f).obj F) n)).symm

include hJfg in
omit [IsNoetherianRing Γ(chartScheme V, ⊤)] in
/-- The families of a compatible family of sections of `(f_*(𝓕/𝓘ⁿ⁺¹𝓕))_n` over `V`, read on the
scheme side, are compatible. -/
theorem C1573.chartDirectImageAdicQuotientIso_family
    (z : adicSectionLimit B S hS Y.1 Y.2 V
      (adicQuotientSystem B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) F ⋙
        modulePushforward B S hS f)) (n : ℕ) :
    Scheme.Modules.Hom.app
        ((Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)).map
          (((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
            (chartCoherentModule B S hS f hf V F hF)).obj.map (homOfLE (Nat.le_succ n)).op)) ⊤
        ((chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg (n + 1)).hom
          (z.1 (n + 1 + 1))) =
      (chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).hom (z.1 (n + 1)) := by
  refine (chartDirectImageAdicQuotientIso_transition B S hS f hf V J F hF hJ hJfg n
    (z.1 (n + 1 + 1))).symm.trans ?_
  refine congrArg (chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).hom ?_
  refine Eq.trans ?_ (z.2 (n + 1))
  exact (congrArg
    (fun k => ((modulePushforward B S hS f).map k).val.app (op V) (z.1 (n + 1 + 1)))
    (adicQuotientSystem_map_succ B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) F n)).symm

/-- The tower of sections over `V` of the completion of the pushforward along the chart. -/
private abbrev C1573.chartPushforwardCompletionSections :=
  ((Stacks.Algebraization.completionFunctor _
    (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))).obj
      (chartPushforwardCoherent B S hS f hf V F hF hfp)).obj ⋙
    Stacks.Algebraization.affineSectionFunctor ⟨⊤, isAffineOpen_top (chartScheme V)⟩

/-- The element of the limit of the scheme-side tower attached to a compatible family of sections
of `(f_*𝓕)/𝒥ⁿ⁺¹` over `V`. -/
private def C1573.chartPushforwardLimitOfAdicSection
    (x : adicSectionLimit B S hS Y.1 Y.2 V
      (adicQuotientSystem B S hS Y.1 Y.2 J ((modulePushforward B S hS f).obj F))) :
    (limit (chartPushforwardCompletionSections B S hS f hf V J F hF hfp) :
      ModuleCat Γ(chartScheme V, ⊤)) :=
  (Stacks.Coherent.moduleLimitTowerEquiv _).symm
    ⟨fun n => chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n (x.1 (n + 1)),
      fun n => chartPushforwardAdicQuotientEquiv_family B S hS f hf V J F hF hfp hJ hM x n⟩

/-- The projections of `chartPushforwardLimitOfAdicSection` are the members of the family, read on
the scheme side. -/
private theorem C1573.π_chartPushforwardLimitOfAdicSection
    (x : adicSectionLimit B S hS Y.1 Y.2 V
      (adicQuotientSystem B S hS Y.1 Y.2 J ((modulePushforward B S hS f).obj F))) (n : ℕ) :
    (limit.π (chartPushforwardCompletionSections B S hS f hf V J F hF hfp) (op n)).hom
        (chartPushforwardLimitOfAdicSection B S hS f hf V J F hF hfp hJ hM x) =
      chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n (x.1 (n + 1)) :=
  Stacks.Coherent.C1573.limit_π_moduleLimitTowerEquiv_symm _ _ n

/-- The compatible family of sections of `(f_*𝓕)/𝒥ⁿ⁺¹` over `V` attached to an element of the
limit of the scheme-side tower. -/
private def C1573.chartPushforwardAdicSectionOfLimit
    (v : (limit (chartPushforwardCompletionSections B S hS f hf V J F hF hfp) :
      ModuleCat Γ(chartScheme V, ⊤))) :
    adicSectionLimit B S hS Y.1 Y.2 V
      (adicQuotientSystem B S hS Y.1 Y.2 J ((modulePushforward B S hS f).obj F)) :=
  let D1 := chartPushforwardCompletionSections B S hS f hf V J F hF hfp
  let e := chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM
  let xs : ∀ k, adicSectionTower B S hS Y.1 Y.2
      (adicQuotientSystem B S hS Y.1 Y.2 J ((modulePushforward B S hS f).obj F)) V k := fun k =>
    match k with
    | 0 => (0 : Fin 0 → chartRing B S hS Y.1 Y.2 V)
    | n + 1 => (e n).symm ((limit.π D1 (op n)).hom v)
  have hxs : ∀ k, adicSectionTransition B S hS Y.1 Y.2
      (adicQuotientSystem B S hS Y.1 Y.2 J ((modulePushforward B S hS f).obj F)) V k
        (xs (k + 1)) = xs k := by
    intro k
    cases k with
    | zero => exact funext fun i => Fin.elim0 i
    | succ n =>
      refine (e n).injective ?_
      have h1 := congrArg (fun k => k.val.app (op V) ((e (n + 1)).symm
          ((limit.π D1 (op (n + 1))).hom v)))
        (adicQuotientSystem_map_succ B S hS Y.1 Y.2 J ((modulePushforward B S hS f).obj F) n)
      refine (congrArg (e n) h1).trans ?_
      refine (chartPushforwardAdicQuotientEquiv_transition B S hS f hf V J F hF hfp hJ hM n
        _).trans ?_
      refine (congrArg (fun t => Scheme.Modules.Hom.app (((Stacks.Algebraization.completionFunctor _
        (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))).obj
          (chartPushforwardCoherent B S hS f hf V F hF hfp)).obj.map
            (homOfLE (Nat.le_succ n)).op) ⊤ t)
        (LinearEquiv.apply_symm_apply (e (n + 1)) _)).trans ?_
      refine Eq.trans ?_ (LinearEquiv.apply_symm_apply (e n) _).symm
      exact ConcreteCategory.congr_hom (limit.w D1 (homOfLE (Nat.le_succ n)).op) v
  ⟨xs, hxs⟩

/-- The members of `chartPushforwardAdicSectionOfLimit v`, read on the scheme side, are the
projections of `v`. -/
private theorem C1573.chartPushforwardAdicQuotientEquiv_adicSectionOfLimit
    (v : (limit (chartPushforwardCompletionSections B S hS f hf V J F hF hfp) :
      ModuleCat Γ(chartScheme V, ⊤))) (n : ℕ) :
    chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n
        ((chartPushforwardAdicSectionOfLimit B S hS f hf V J F hF hfp hJ hM v).1 (n + 1)) =
      (limit.π (chartPushforwardCompletionSections B S hS f hf V J F hF hfp) (op n)).hom v :=
  LinearEquiv.apply_symm_apply
    (chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n) _

include hJfg hF hfp hJ hM in
/-- **The theorem on formal functions over an affine chart, for the comparison of Stacks 08BD.**
Over an affine étale chart `V` of `Y`, the comparison `c : (f_*𝓕)^ ⟶ (f_*(𝓕/𝓘ⁿ⁺¹𝓕))_n` induces a
bijection `lim_n ((f_*𝓕)/𝒥ⁿ⁺¹)(V) ⟶ lim_n (f_*(𝓕/𝓘ⁿ⁺¹𝓕))(V)`. -/
theorem C1573.bijective_adicSectionLimitMap_chart :
    Function.Bijective (adicSectionLimitMap B S hS Y.1 Y.2 V
      (directImageCompletionComparison B S hS f hf J F)) := by
  have := isCoherent_chartZariskiModule B S hS X F hF ((smallBaseChange B S hS f hf).obj V)
    inferInstance
  have := isCoherent_pushforward_chartZariskiModule B S hS f hf V F hF hfp
  have := isProper_chartBaseChangeSchemeHom B S hS f hf V hfp
  let ΓT := Stacks.Algebraization.affineSectionFunctor ⟨⊤, isAffineOpen_top (chartScheme V)⟩
  let c' := Stacks.Coherent.pushforwardCompletionComparison (chartBaseChangeSchemeHom B S hS f hf V)
    (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))
    ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj F)
  have hiso : IsIso (limMap (Functor.whiskerRight c' ΓT)) :=
    Stacks.Coherent.isIso_limMap_affineSections_pushforwardCompletionComparison_affineOpen _ _
      ⟨⊤, isAffineOpen_top (chartScheme V)⟩ _
  let D2 := (((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
      (chartCoherentModule B S hS f hf V F hF)).obj ⋙
        Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)) ⋙ ΓT
  let e := fun n => (chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).toLinearEquiv
  let e' := chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM
  let ℓ1 := chartPushforwardLimitOfAdicSection B S hS f hf V J F hF hfp hJ hM
  have hℓ1 := π_chartPushforwardLimitOfAdicSection B S hS f hf V J F hF hfp hJ hM
  have hcomp : ∀ (x : adicSectionLimit B S hS Y.1 Y.2 V
      (adicQuotientSystem B S hS Y.1 Y.2 J ((modulePushforward B S hS f).obj F))) (n : ℕ),
      e n ((adicSectionLimitMap B S hS Y.1 Y.2 V
        (directImageCompletionComparison B S hS f hf J F) x).1 (n + 1)) =
      (limit.π D2 (op n)).hom (limMap (Functor.whiskerRight c' ΓT) |>.hom (ℓ1 x)) := by
    intro x n
    refine (congrArg (e n) (adicSectionLimitMap_apply B S hS Y.1 Y.2 V
      (directImageCompletionComparison B S hS f hf J F) x n)).trans ?_
    refine (chartDirectImageAdicQuotientIso_comparison B S hS f hf V J F hF hfp hJ hM hJfg n
      (x.1 (n + 1))).trans ?_
    exact (congrArg _ (hℓ1 x n)).symm.trans (ConcreteCategory.congr_hom
      (limMap_π (Functor.whiskerRight c' ΓT) (op n)) (ℓ1 x)).symm
  have hbij := ConcreteCategory.bijective_of_isIso (limMap (Functor.whiskerRight c' ΓT))
  refine ⟨fun x x' h => ?_, fun z => ?_⟩
  · have h2 : ∀ n, (limit.π D2 (op n)).hom (limMap (Functor.whiskerRight c' ΓT) |>.hom (ℓ1 x)) =
        (limit.π D2 (op n)).hom (limMap (Functor.whiskerRight c' ΓT) |>.hom (ℓ1 x')) := fun n =>
      (hcomp x n).symm.trans ((congrArg (fun (y : adicSectionLimit B S hS Y.1 Y.2 V
        (adicQuotientSystem B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) F ⋙
          modulePushforward B S hS f)) => e n (y.1 (n + 1))) h).trans (hcomp x' n))
    have hlim : ℓ1 x = ℓ1 x' := hbij.1 (Stacks.Coherent.C1573.moduleLimit_ext D2 h2)
    exact adicSectionLimit_ext fun n => (e' n).injective ((hℓ1 x n).symm.trans
      ((congrArg (fun a => (limit.π (chartPushforwardCompletionSections B S hS f hf V J F hF hfp)
        (op n)).hom a) hlim).trans (hℓ1 x' n)))
  · let w : (limit D2 : ModuleCat Γ(chartScheme V, ⊤)) :=
      (Stacks.Coherent.moduleLimitTowerEquiv D2).symm ⟨fun n => e n (z.1 (n + 1)), fun n =>
        chartDirectImageAdicQuotientIso_family B S hS f hf V J F hF hJ hJfg z n⟩
    obtain ⟨v, hv⟩ := hbij.2 w
    let x := chartPushforwardAdicSectionOfLimit B S hS f hf V J F hF hfp hJ hM v
    have hxv : ℓ1 x = v := Stacks.Coherent.C1573.moduleLimit_ext _ fun n => (hℓ1 x n).trans
      (chartPushforwardAdicQuotientEquiv_adicSectionOfLimit B S hS f hf V J F hF hfp hJ hM v n)
    refine ⟨x, adicSectionLimit_ext fun n => (e n).injective ?_⟩
    exact (hcomp x n).trans ((congrArg (fun a => (limit.π D2 (op n)).hom
      ((limMap (Functor.whiskerRight c' ΓT)).hom a)) hxv).trans
        ((congrArg (fun a => (limit.π D2 (op n)).hom a) hv).trans
          (Stacks.Coherent.C1573.limit_π_moduleLimitTowerEquiv_symm D2 _ n)))

end Pushforward

end AlgebraicGeometry.Space

end
