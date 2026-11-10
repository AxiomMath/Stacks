module

public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.BundleSectionMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FamilyPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapLociFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularSectionEffectiveCartierUnique
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeReadingOfModule
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# The section `(0, 1)` of the projective completion is a regular section

Let `X` be an algebraic space, `ℰ` a finite locally free `𝒪_X`-module of rank `r`, and
`π : P = 𝐏(ℰ ⊕ 𝒪_X) ⟶ X` the projective completion of its vector bundle, with the section
`s ∈ Γ(P, 𝒪_P(1))` of `(0, 1)`. This file proves that `s` is a regular section: the map
`𝒪_P ⟶ 𝒪_P(1)` it defines is a monomorphism. By Stacks 0847 its zero scheme `D = Z(s)` is then
an effective Cartier divisor with `𝒪_P(D) ≅ 𝒪_P(1)`, the divisor at infinity of the proof of
Stacks 0ERW.

Injectivity descends along the flat atlas `P_U ⟶ P` of the projective bundle
(`AlgebraicGeometry.Space.mono_of_forall_mono_modulePullback_map_of_isFlat`), and on `P_U` it is
read on the scheme `P_U = 𝐏((ℰ ⊕ 𝒪_X)|_U)`. There the reading of the inverse image of `s` is,
up to isomorphisms, the map `ρ^*𝒪_U ⟶ ρ^*((ℰ ⊕ 𝒪_X)|_U) ⟶ 𝒪_{P_U}(1)` of the split section
`𝒪_U ⟶ (ℰ ⊕ 𝒪_X)|_U`, which is a monomorphism by
`Stacks.RelativeProj.mono_pullback_map_comp_tautologicalDatumUniv`.

## Main results

* `AlgebraicGeometry.Space.mono_of_mono_representedZariski_map`: a map of quasi-coherent modules
  on a representable algebraic space whose reading on the scheme is a monomorphism is a
  monomorphism.
* `AlgebraicGeometry.Space.schemeReadingPullbackIso_hom_naturality`: the comparison of readings
  along a morphism of the site is natural in the module.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Cancellation of a monomorphism after a functor, in an abstract form that sees through any
spelling of the categories involved. -/
theorem _root_.CategoryTheory.Functor.map_eq_map_of_mono_map {C₀ D₀ : Type*} [Category C₀]
    [Category D₀] (R : C₀ ⥤ D₀) {x y z : C₀} (f : x ⟶ y) [Mono (R.map f)] (g h : z ⟶ x)
    (e : g ≫ f = h ≫ f) : R.map g = R.map h := by
  rw [← cancel_mono (R.map f), ← R.map_comp, ← R.map_comp, e]

/-- Composing two naturality squares through a functor, in an abstract form that sees through
any spelling of the categories involved. -/
theorem _root_.CategoryTheory.Functor.comp_map_naturality_shape {C₀ C₁ D₀ : Type*}
    [Category C₀] [Category C₁] [Category D₀] (F₁ : C₀ ⥤ C₁) (F₂ : C₁ ⥤ D₀)
    {x1 x2 x3 x4 : C₀} {a : x1 ⟶ x2} {e' : x4 ≅ x2} {e : x3 ≅ x1} {c : x3 ⟶ x4}
    (nat2 : a ≫ e'.inv = e.inv ≫ c) :
    F₂.map (F₁.map a) ≫ (F₂.mapIso (F₁.mapIso e'.symm)).hom =
      (F₂.mapIso (F₁.mapIso e.symm)).hom ≫ F₂.map (F₁.map c) := by
  simp only [Functor.mapIso_hom, Iso.symm_hom]
  rw [← F₂.map_comp, ← F₁.map_comp, nat2, F₁.map_comp, F₂.map_comp]

/-- Peeling an isomorphism off the front of a composite after three functors. -/
theorem _root_.CategoryTheory.Functor.mono_map_map_map_comp_of_isIso {C₀ C₁ C₂ D₀ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category D₀] (G₁ : C₀ ⥤ C₁) (G₂ : C₁ ⥤ C₂)
    (G₃ : C₂ ⥤ D₀) {x y z w : C₀} (a : x ≅ y) (b : y ⟶ z) (c : z ⟶ w)
    (h : Mono (G₃.map (G₂.map (G₁.map b)) ≫ G₃.map (G₂.map (G₁.map c)))) :
    Mono (G₃.map (G₂.map (G₁.map (a.hom ≫ b ≫ c)))) := by
  rw [G₁.map_comp, G₁.map_comp, G₂.map_comp, G₂.map_comp, G₃.map_comp, G₃.map_comp]
  exact mono_comp _ _

/-- Replacing the second factor of a composite after two functors by a map it agrees with up to
an isomorphism on the target. -/
theorem _root_.CategoryTheory.Functor.mono_map_map_comp_of_comp_iso {C₁ C₂ D₀ : Type*}
    [Category C₁] [Category C₂] [Category D₀] (G₂ : C₁ ⥤ C₂) (G₃ : C₂ ⥤ D₀) {x y z z' : C₁}
    (b : x ⟶ y) (c : y ⟶ z) (e : z ≅ z') (q : y ⟶ z') (hq : c ≫ e.hom = q)
    (Q : G₃.obj (G₂.obj y) ⟶ G₃.obj (G₂.obj z')) (hQ : G₃.map (G₂.map q) = Q)
    (h : Mono (G₃.map (G₂.map b) ≫ Q)) :
    Mono (G₃.map (G₂.map b) ≫ G₃.map (G₂.map c)) := by
  have hc : c = q ≫ e.inv := by rw [← hq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  subst hc
  rw [G₂.map_comp, G₃.map_comp, ← Category.assoc, hQ]
  exact mono_comp _ _

/-- Moving a map past an isomorphism, after two functors, along a naturality square. -/
theorem _root_.CategoryTheory.Functor.mono_map_map_comp_mapIso_of_naturality {C₁ C₂ D₀ : Type*}
    [Category C₁] [Category C₂] [Category D₀] (G₂ : C₁ ⥤ C₂) (G₃ : C₂ ⥤ D₀) {x y x' y' : C₁}
    {o1 o2 o3 : D₀} (b : x ⟶ y) (κ : y' ≅ y) (κx : x' ≅ x) (b₂ : x' ⟶ y')
    (nat : b ≫ κ.inv = κx.inv ≫ b₂) (s1 : G₃.obj (G₂.obj y') ⟶ o1) (s2 : o1 ⟶ o2) (ε : o3 ≅ o2)
    (h : Mono (G₃.map (G₂.map b₂) ≫ s1 ≫ s2)) :
    Mono (G₃.map (G₂.map b) ≫ (G₃.mapIso (G₂.mapIso κ.symm)).hom ≫ s1 ≫ s2 ≫ ε.inv) := by
  have e := Functor.comp_map_naturality_shape G₂ G₃ nat
  have := mono_comp (G₃.mapIso (G₂.mapIso κx.symm)).hom
    ((G₃.map (G₂.map b₂) ≫ s1 ≫ s2) ≫ ε.inv)
  rw [← Category.assoc, e]
  simpa only [Category.assoc] using this

/-- Moving a map past an isomorphism along a naturality square. -/
theorem _root_.CategoryTheory.mono_comp_inv_comp_of_naturality {D₀ : Type*} [Category D₀]
    {q0 q1 p1 p2 o2 : D₀} (B₂ : p1 ⟶ p2) (K' : q1 ≅ p2) (K : q0 ≅ p1) (M : q0 ⟶ q1)
    (nat3 : M ≫ K'.hom = K.hom ≫ B₂) (s2 : q1 ⟶ o2) (h : Mono (M ≫ s2)) :
    Mono (B₂ ≫ K'.inv ≫ s2) := by
  have hB : B₂ = K.inv ≫ M ≫ K'.hom := (Iso.eq_inv_comp K).mpr nat3.symm
  have e : B₂ ≫ K'.inv ≫ s2 = K.inv ≫ M ≫ s2 := by
    rw [hB]
    simp
  rw [e]
  exact mono_comp _ _

/-- Replacing the source of a map by an isomorphic one, after a functor, in front of a map. -/
theorem _root_.CategoryTheory.Functor.mono_map_comp_of_iso {C₀ D₀ : Type*} [Category C₀]
    [Category D₀] (G : C₀ ⥤ D₀) {x x' z : C₀} {w : D₀} (u : x ≅ x') (m : x ⟶ z)
    (t : G.obj z ⟶ w) (h : Mono (G.map (u.inv ≫ m) ≫ t)) : Mono (G.map m ≫ t) := by
  have he : G.map m ≫ t = G.map u.hom ≫ (G.map (u.inv ≫ m) ≫ t) := by
    simp
  rw [he]
  exact mono_comp _ _

/-- A retraction after three functors, conjugated by an isomorphism, in an abstract form that
sees through any spelling of the categories involved. -/
theorem _root_.CategoryTheory.Functor.iso_inv_comp_map_map_map_comp_eq_id {C₀ C₁ C₂ D₀ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category D₀] (G₁ : C₀ ⥤ C₁) (G₂ : C₁ ⥤ C₂)
    (G₃ : C₂ ⥤ D₀) {x y : C₀} {w : D₀} (u : G₃.obj (G₂.obj (G₁.obj x)) ≅ w) (a : x ⟶ y)
    (b : y ⟶ x) (h : a ≫ b = 𝟙 x) :
    (u.inv ≫ G₃.map (G₂.map (G₁.map a))) ≫ (G₃.map (G₂.map (G₁.map b)) ≫ u.hom) = 𝟙 w := by
  simp only [Category.assoc]
  rw [← G₃.map_comp_assoc, ← G₂.map_comp, ← G₁.map_comp, h]
  simp

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **A map of quasi-coherent modules on a representable algebraic space whose reading on the
scheme is a monomorphism is a monomorphism**: its kernel is quasi-coherent, and the reading is
injective on the morphisms out of a quasi-coherent module (Stacks 03DX (2)), so the inclusion of
the kernel vanishes. -/
theorem mono_of_mono_representedZariski_map {T : BigFppfOver B S hS}
    {M N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite) (f : M ⟶ N)
    (hf : Mono ((SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map f))) :
    Mono f := by
  have := hM
  have := hN
  let : Abelian (Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) :=
    SheafOfModules.instAbelian.{u, u, u, u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O))
  have hK : (kernel f).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_kernel_of_quasicoherent B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T) f
  refine Abelian.mono_of_kernel_ι_eq_zero _ ?_
  refine (QuasiCoherentDescent.bijective_representedZariski_map B S hS (kernel f) M hK).1 ?_
  have : Mono (((representedSmallEtaleModuleEquivalence B S hS T).inverse ⋙
      SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map f) := hf
  exact ((representedSmallEtaleModuleEquivalence B S hS T).inverse ⋙
      SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map_eq_map_of_mono_map f _ _
    ((kernel.condition f).trans (zero_comp (f := f)).symm)

variable {X : AlgebraicSpaces B S hS}

/-- The reading on the scheme of `T` of the inverse image along `ψ : T ⟶ X` of a morphism of
`𝒪_X`-modules. -/
abbrev schemeReadingMap {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X)
    {E E' : Modules.{u, u} B S hS X.1 X.2} (u : E ⟶ E') :
    schemeReading E ψ ⟶ schemeReading E' ψ :=
  (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).map
    ((representedSmallEtaleModuleEquivalence B S hS T).inverse.map
      ((modulePullback B S hS ψ).map u))

/-- **The comparison `g^* ℰ_T ≅ ℰ_{T'}` of readings is natural in the module.** -/
theorem schemeReadingPullbackIso_hom_naturality {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') {E E' : Modules.{u, u} B S hS X.1 X.2}
    (hE : E.IsQuasicoherentOnSite) (hE' : E'.IsQuasicoherentOnSite) (u : E ⟶ E') :
    (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).map
        (schemeReadingMap ψ u) ≫ (schemeReadingPullbackIso E' hE' g w).hom =
      (schemeReadingPullbackIso E hE g w).hom ≫ schemeReadingMap ψ' u := by
  rw [schemeReadingPullbackIso_eq, schemeReadingPullbackIso_eq]
  simp only [Iso.trans_hom]
  have nat1 := representedZariskiModulePullbackIso_naturality B S hS g
    (relativelyRepresentable_yoneda_map B S hS g) (F := (modulePullback B S hS ψ).obj E)
    (F' := (modulePullback B S hS ψ).obj E')
    (isQuasicoherentOnSite_modulePullback_schemeReading E hE ψ)
    (isQuasicoherentOnSite_modulePullback_schemeReading E' hE' ψ)
    ((modulePullback B S hS ψ).map u)
  have nat2 := QuasiCoherentDescent.pullbackComparison_inv_naturality B S hS
    (representedSpaceMap B S hS g) ψ ψ' w u
  rw [← Category.assoc, nat1, Category.assoc, Category.assoc,
    Functor.comp_map_naturality_shape _ _ nat2]

section Regular

variable (E : Modules.{u, u} B S hS X.1 X.2) [hE : E.IsQuasicoherentOnSite]
    (hfree : SheafOfModules.IsFiniteLocallyFreeOnSite E)

/-- The reading on the presenting chart bundle of the inverse image along `P_U ⟶ P ⟶ X`, with the
inverse image written along the atlas of the groupoid. -/
theorem schemeReadingMap_projectiveBundleAtlas_comp_eq {E' : Modules.{u, u} B S hS X.1 X.2}
    (u : E' ⟶ E) :
    schemeReadingMap (T := (projectiveBundleChartPresentation E hfree).U)
      (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree) u =
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
      (projectiveBundleChartPresentation E hfree).U.left.property).map
      ((representedSmallEtaleModuleEquivalence B S hS
        (projectiveBundleChartPresentation E hfree).U).inverse.map
        ((modulePullback B S hS (projectiveBundleAtlas E hfree ≫ projectiveBundleProj E hfree)).map
          u)) := by
  with_reducible rfl

/-- The reading of the tautological quotient on the presenting chart bundle is the reading
`AlgebraicGeometry.Space.quotientReadingOf` of the tautological quotient of `𝐏(ℰ|_U)`. -/
theorem projectiveBundleChartQuotientReading_eq_quotientReadingOf :
    projectiveBundleChartQuotientReading E hfree =
      quotientReadingOf E hE (representedSpaceMap_projectiveBundleChartProj_comp E hfree)
        (chartBundleTautological E (bundleBaseChart X))
        (projectiveBundleChartTwistReadingIso E hfree)
        (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
          (projectiveBundleProj E hfree) _ rfl E).symm :=
  rfl

/-- The reading `AlgebraicGeometry.Space.quotientReadingOf` of the tautological quotient of
`𝐏(ℰ|_U)`, written out: the reading of `φ^*π^*ℰ ≅ (φ ≫ π)^*ℰ`, the comparison of readings along
`P_U ⟶ U`, the tautological quotient and the reading of the twist. -/
theorem quotientReadingOf_chartBundleTautological_eq :
    quotientReadingOf E hE (representedSpaceMap_projectiveBundleChartProj_comp E hfree)
        (chartBundleTautological E (bundleBaseChart X))
        (projectiveBundleChartTwistReadingIso E hfree)
        (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
          (projectiveBundleProj E hfree) _ rfl E).symm =
      ((SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
          (projectiveBundleChartPresentation E hfree).U.left.property).mapIso
        ((representedSmallEtaleModuleEquivalence B S hS
          (projectiveBundleChartPresentation E hfree).U).inverse.mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
            (projectiveBundleProj E hfree) _ rfl E).symm)).hom ≫
        (schemeReadingPullbackIso E hE (projectiveBundleChartProj E hfree)
          (representedSpaceMap_projectiveBundleChartProj_comp E hfree)).inv ≫
        chartBundleTautological E (bundleBaseChart X) ≫
        (projectiveBundleChartTwistReadingIso E hfree).inv :=
  rfl

/-- The projection `P_U ⟶ U` of the presenting chart bundle, on schemes, is the projection of
`𝐏(ℰ|_U)`. -/
theorem schemeHom_projectiveBundleChartProj_left :
    SmallEtale.schemeHom (associatedBigEtaleSite B) (projectiveBundleChartProj E hfree).left =
      chartBundleToChart E (bundleBaseChart X) :=
  rfl

/-- **The hyperplane section of a split section is regular, on the projective bundle of a module
on an algebraic space.** For `σ : 𝒪_X ⟶ ℰ` with a retraction, the map
`𝒪_P ≅ π^*𝒪_X ⟶ π^*ℰ ⟶ 𝒪_P(1)` on `π : P = 𝐏(ℰ) ⟶ X` is a monomorphism. -/
theorem mono_projectiveBundleSectionHom_of_comp_eq_id
    (σ : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)) ⟶ E)
    (τ : E ⟶ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O))) (hστ : σ ≫ τ = 𝟙 _) :
    Mono ((modulePullbackUnitIso B S hS (projectiveBundleProj E hfree)).inv ≫
      (modulePullback B S hS (projectiveBundleProj E hfree)).map σ ≫
        (projectiveBundleTautological E hfree).hom) := by
  -- descend along the atlas of the projective bundle
  refine mono_of_forall_mono_modulePullback_map_of_isFlat B S hS
    (fun _ : PUnit.{u + 1} => projectiveBundleAtlas E hfree)
    (fun _ => isFlat_of_isEtale B S hS (presentationAtlas_isEtale _))
    ((isJointlySurjective_iff B S hS _ _).2 fun y =>
      ⟨PUnit.unit, surjective_pointsMap_projectiveBundleAtlas E hfree y⟩)
    _ fun _ => ?_
  refine mono_of_mono_representedZariski_map
    (T := (projectiveBundleChartPresentation E hfree).U)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
      (SheafOfModules.isQuasicoherentOnSite_unit _))
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
      (projectiveBundleTwist E hfree).property) _ ?_
  refine Functor.mono_map_map_map_comp_of_isIso
    (modulePullback B S hS (projectiveBundleAtlas E hfree))
    (representedSmallEtaleModuleEquivalence B S hS
      (projectiveBundleChartPresentation E hfree).U).inverse
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj (projectiveBundleChartPresentation E hfree).U)
      (projectiveBundleChartPresentation E hfree).U.left.property)
    (modulePullbackUnitIso B S hS (projectiveBundleProj E hfree)).symm _ _ ?_
  -- the tautological map on the atlas is the chart quotient
  refine Functor.mono_map_map_comp_of_comp_iso _ _ _ _ (projectiveBundleTwistAtlasIso E hfree)
    (projectiveBundleChartQuotient E hfree)
    (modulePullback_map_projectiveBundleTautological E hfree)
    _ (representedZariski_map_projectiveBundleChartQuotient E hfree) ?_
  rw [projectiveBundleChartQuotientReading_eq_quotientReadingOf,
    quotientReadingOf_chartBundleTautological_eq]
  -- move `σ` past the comparison of iterated inverse images
  have nat := QuasiCoherentDescent.pullbackComparison_inv_naturality B S hS
    (projectiveBundleAtlas E hfree) (projectiveBundleProj E hfree) _ rfl σ
  refine Functor.mono_map_map_comp_mapIso_of_naturality _ _ _ _
    (QuasiCoherentDescent.pullbackComparison B S hS (projectiveBundleAtlas E hfree)
      (projectiveBundleProj E hfree) _ rfl
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))))
    ((modulePullback B S hS (projectiveBundleAtlas E hfree ≫
      projectiveBundleProj E hfree)).map σ) ?nat _ _ _ ?_
  case nat => exact nat
  -- move `σ` past the comparison of readings
  have nat3 := schemeReadingPullbackIso_hom_naturality (projectiveBundleChartProj E hfree)
    (representedSpaceMap_projectiveBundleChartProj_comp E hfree)
    (SheafOfModules.isQuasicoherentOnSite_unit _) hE σ
  rw [schemeReadingMap_projectiveBundleAtlas_comp_eq] at nat3
  refine mono_comp_inv_comp_of_naturality _ _
    (schemeReadingPullbackIso (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O))) (SheafOfModules.isQuasicoherentOnSite_unit _)
      (projectiveBundleChartProj E hfree)
      (representedSpaceMap_projectiveBundleChartProj_comp E hfree))
    ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B) (projectiveBundleChartProj E hfree).left)).map
      (schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) σ)) ?nat3 _ ?_
  case nat3 => exact nat3
  -- the reading on the chart bundle `𝐏(ℰ|_U) ⟶ U`
  have := isFiniteLocallyFree_chartBundleModule E hfree (bundleBaseChart X)
  let uU : schemeReading (T := (SmallEtale.toOver B S hS X.1).obj (bundleBaseChart X))
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O))) (chartToSpace B S hS X (bundleBaseChart X)) ≅
      Scheme.unitModule (chartScheme (bundleBaseChart X)) :=
    schemeReadingChartIso _ _ ≪≫ restrictToChartSchemeUnitIso B S hS X.1 X.2 _
  refine Functor.mono_map_comp_of_iso
    (Scheme.Modules.pullback (chartBundleToChart E (bundleBaseChart X))) uU _ _ ?_
  refine Stacks.RelativeProj.mono_pullback_map_comp_tautologicalDatumUniv
    (chartBundleModule E (bundleBaseChart X)) _
    (schemeReadingMap (chartToSpace B S hS X (bundleBaseChart X)) τ ≫ uU.hom) ?_
  refine Functor.iso_inv_comp_map_map_map_comp_eq_id _ _ _ _ _ _ ?_
  exact hστ

end Regular

section Completion

variable (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)

/-- **The section `s` of `(0, 1)` of the projective completion `P = 𝐏(ℰ ⊕ 𝒪_X)` is regular**:
the map `𝒪_P ⟶ 𝒪_P(1)` it defines is a monomorphism. -/
theorem mono_projectiveCompletionSectionHom : Mono (projectiveCompletionSectionHom E hr) := by
  unfold projectiveCompletionSectionHom
  with_reducible
    exact @mono_projectiveBundleSectionHom_of_comp_eq_id B S hS X (addUnit X.2 E)
      (isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr) (addUnitInr X.2 E)
      (addUnitSnd X.2 E) (addUnitInr_addUnitSnd X.2 E)

/-- **The section `s` of `(0, 1)` of the projective completion is a regular section of
`𝒪_P(1)`.** -/
theorem isRegularSection_projectiveCompletionSection :
    AlgebraicGeometry.IsRegularSection (structureCommRings B S hS (projectiveCompletion E hr))
      (structureRingSheaf B S hS (projectiveCompletion E hr)).property
      (projectiveCompletionSection E hr) := by
  change Mono ((projectiveCompletionTwist E hr).obj.unitHomEquiv.symm
    (projectiveCompletionSection E hr))
  rw [unitHomEquiv_symm_projectiveCompletionSection]
  exact mono_projectiveCompletionSectionHom E hr

/-- **The divisor at infinity of the projective completion** (Stacks 0847 for the regular section
`s`): the zero scheme `D = Z(s)` of `s` is an effective Cartier divisor of `P = 𝐏(ℰ ⊕ 𝒪_X)`, with
an isomorphism `𝒪_P(D) ≅ 𝒪_P(1)` taking the canonical section of `𝒪_P(D)` to `s`. -/
theorem exists_isEffectiveCartierDivisor_zeroScheme_projectiveCompletionSection :
    ∃ (hD : IsEffectiveCartierDivisor B S hS (projectiveCompletion E hr)
        (zeroScheme B S hS (projectiveCompletion E hr) (projectiveCompletionTwist E hr).obj
          (projectiveCompletionSection E hr)))
      (i : associatedInvertibleSheaf B S hS (projectiveCompletion E hr) _ hD ≅
        (projectiveCompletionTwist E hr).obj),
      canonicalSectionHom B S hS (projectiveCompletion E hr) _ hD ≫ i.hom =
        projectiveCompletionSectionHom E hr := by
  obtain ⟨D, hD, i, hDz, hi, -, -⟩ :=
    exists_unique_isEffectiveCartierDivisor_iso_canonicalSectionHom_comp B S hS
      (projectiveCompletion E hr) (projectiveCompletionTwist E hr).obj
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
        (isInvertibleModule_projectiveCompletionTwist E hr))
      (projectiveCompletionSection E hr) (isRegularSection_projectiveCompletionSection E hr)
  subst hDz
  exact ⟨hD, i, hi.trans (unitHomEquiv_symm_projectiveCompletionSection E hr)⟩

end Completion

end AlgebraicGeometry.Space

end
