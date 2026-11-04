module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsReadingModulePullbackValue
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackUnitIsoCompValue
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBundleModuleSectionsBasis
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionChartQuotientReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionChartCoordinate
public import StacksFrontier.AlgebraicGeometry.Modules.FreeSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.AdditiveSheafAssociatedStructure

/-!
# The coordinates of `U ×_X V` in two ways

Let `X` be an algebraic space, `ℰ` a finite locally free `𝒪_X`-module, `P = 𝐏(ℰ ⊕ 𝒪_X)` with
affine part `ι : U ⟶ P`, `u : U ⟶ X`, `q : u^*ℰ ⟶ 𝒪_U` the map `m ↦ (m, 0) / s`, and `V` an affine
étale chart of `X` with a morphism `m` to the presenting chart, on which `ℰ` is free by
`e : ℰ|_V ≅ 𝒪_V^{⊕ n}`. The object `A = U ×_X V` is the open complement of `𝐏(ℰ|_V)` in
`𝐏((ℰ ⊕ 𝒪)|_V)`, an affine space over `V` with coordinates `λ(σ'(k_j)) / λ(σ)`
(`Stacks.RelativeProj.UnitSplitting.splitCoordVector`). This file shows that the `j`-th
coordinate is the value of `q` on the inverse image of the `j`-th basis section of `ℰ(V)` at the
chart `U_V = A` of `U` (Stacks 0ERW, proof): the reading of `q` on the scheme of `A` is the ratio
of the readings of `ι^*(π^*(inl) ≫ λ)` and `ι^*(π^*(inr) ≫ λ)`, which are read through
`AlgebraicGeometry.Space.exists_quotientReadingHyp_comp_projectiveBundleTautological` with a
common identification of the targets, which cancels.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

attribute [-instance] CategoryTheory.catToReflQuiver

/-! ### Abstract shapes -/

namespace CategoryTheory

/-- The ratio of two read quotients with a common identification of the targets. -/
theorem reading_ratio_shape {C : Type*} [Category C]
    {PE PO BE BO RE RO RL TU RU OA : C}
    (SE : PE ≅ BE) (KE : RE ≅ BE) (YE : PE ⟶ TU) (ε : RL ≅ TU) (ZE : RE ⟶ RL)
    (SO : PO ≅ BO) (KO : RO ≅ BO) (YO : PO ⟶ TU) (ZO : RO ⟶ RL) [IsIso ZO] [IsIso YO]
    (Zw : RO ⟶ RU) (UA : RU ≅ OA)
    (hE : ZE = KE.hom ≫ SE.inv ≫ YE ≫ ε.inv) (hO : ZO = KO.hom ≫ SO.inv ≫ YO ≫ ε.inv) :
    SE.hom ≫ KE.inv ≫ (ZE ≫ inv ZO ≫ Zw) ≫ UA.hom =
      YE ≫ inv YO ≫ SO.hom ≫ KO.inv ≫ Zw ≫ UA.hom := by
  subst hE hO
  simp only [IsIso.inv_comp, IsIso.Iso.inv_hom, IsIso.Iso.inv_inv, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]

/-- `CategoryTheory.reading_ratio_shape` without the final identification. -/
theorem reading_ratio_shape' {C : Type*} [Category C]
    {PE PO BE BO RE RO RL TU RU : C}
    (SE : PE ≅ BE) (KE : RE ≅ BE) (YE : PE ⟶ TU) (ε : RL ≅ TU) (ZE : RE ⟶ RL)
    (SO : PO ≅ BO) (KO : RO ≅ BO) (YO : PO ⟶ TU) (ZO : RO ⟶ RL) [IsIso ZO] [IsIso YO]
    (Zw : RO ⟶ RU)
    (hE : ZE = KE.hom ≫ SE.inv ≫ YE ≫ ε.inv) (hO : ZO = KO.hom ≫ SO.inv ≫ YO ≫ ε.inv) :
    SE.hom ≫ KE.inv ≫ ZE ≫ inv ZO ≫ Zw = YE ≫ inv YO ≫ SO.hom ≫ KO.inv ≫ Zw := by
  simpa using reading_ratio_shape SE KE YE ε ZE SO KO YO ZO Zw (Iso.refl _) hE hO

/-- The inverse of an isomorphism `m ≫ y`. -/
theorem iso_inv_eq_of_hom_eq_comp {C : Type*} [Category C] {a b t : C} (μ : a ≅ t) (m : a ≅ b)
    (y : b ⟶ t) [IsIso y] (h : μ.hom = m.hom ≫ y) : μ.inv = inv y ≫ m.inv := by
  rw [← cancel_epi μ.hom, Iso.hom_inv_id, h, Category.assoc, IsIso.hom_inv_id_assoc,
    Iso.hom_inv_id]

/-- If `g ≫ y = 𝟙 b`, then `f ≫ x = (f ≫ g) ≫ (y ≫ x)`. -/
theorem comp_eq_comp_comp_of_comp_eq_id {C : Type*} [Category C]
    {a b c d : C} (f : a ⟶ b) (g : b ⟶ c) (x : b ⟶ d) (y : c ⟶ b) (h : g ≫ y = 𝟙 b) :
    f ≫ x = (f ≫ g) ≫ (y ≫ x) := by
  rw [Category.assoc, reassoc_of% h]

/-- If an isomorphism `s` factors as `I.hom ≫ y` with `I` an isomorphism, then `y` is an
isomorphism. -/
theorem isIso_of_eq_iso_hom_comp {C : Type*} [Category C] {o z t : C}
    (s : o ⟶ t) [IsIso s] (I : o ≅ z) (y : z ⟶ t) (hs : s = I.hom ≫ y) : IsIso y := by
  have : IsIso (I.hom ≫ y) := hs ▸ inferInstance
  exact IsIso.of_isIso_comp_left I.hom y

/-- If `s = I.hom ≫ y` with `s` and `y` isomorphisms, then
`c ≫ x ≫ inv s ≫ w = (c ≫ x) ≫ inv y ≫ I.inv ≫ w`. -/
theorem ratio_shape {C : Type*} [Category C] {a b o z t w' : C}
    (c : a ⟶ b) (x : b ⟶ t) (s : o ⟶ t) [IsIso s] (I : o ≅ z) (y : z ⟶ t) [IsIso y]
    (w : o ⟶ w') (hs : s = I.hom ≫ y) :
    c ≫ x ≫ inv s ≫ w = (c ≫ x) ≫ inv y ≫ I.inv ≫ w := by
  subst hs
  simp only [IsIso.inv_comp, IsIso.Iso.inv_hom, Category.assoc]

/-- The image of `x ≫ inv y ≫ w` under the composite of three functors `F₁`, `F₂`, `F₃` is the
image of `x`, followed by the inverse of the image of `y` and the image of `w`. -/
theorem Functor.map_map_map_comp_inv_comp {C₁ C₂ C₃ C₄ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [Category C₄] (F₁ : C₁ ⥤ C₂) (F₂ : C₂ ⥤ C₃)
    (F₃ : C₃ ⥤ C₄) {a b c d : C₁} (x : a ⟶ b) (y : c ⟶ b) [IsIso y] (w : c ⟶ d) :
    F₃.map (F₂.map (F₁.map (x ≫ CategoryTheory.inv y ≫ w))) =
      F₃.map (F₂.map (F₁.map x)) ≫ CategoryTheory.inv (F₃.map (F₂.map (F₁.map y))) ≫
        F₃.map (F₂.map (F₁.map w)) := by
  simp only [Functor.map_comp, Functor.map_inv]

end CategoryTheory

/-! ### Pulling back a global section along a morphism of schemes -/

namespace Stacks.RelativeProj

open _root_.AlgebraicGeometry

/-- The morphism out of `g^*𝒪_X` of a morphism `φ : 𝒪_X ⟶ M` sends `1` to the pullback of the
section `φ(1)`. -/
theorem pullbackUnitIso_inv_comp_map_app_top_one {X Y : Scheme.{u}} (g : Y ⟶ X) {M : X.Modules}
    (φ : Scheme.unitModule X ⟶ M) :
    ((Scheme.Modules.pullbackUnitIso g).inv ≫ (Scheme.Modules.pullback g).map φ).app ⊤
        (1 : Γ(Y, ⊤)) =
      pullbackSectionHom g M ⊤ ⊤ le_top (φ.app ⊤ (1 : Γ(X, ⊤))) := by
  have h1 := pullbackUnitIso_hom_app_top_pullbackSectionHom g le_top (1 : Γ(X, ⊤))
  rw [map_one] at h1
  have h2 : (Scheme.Modules.pullbackUnitIso g).inv.app ⊤ (1 : Γ(Y, ⊤)) =
      pullbackSectionHom g (Scheme.unitModule X) ⊤ ⊤ le_top (1 : Γ(X, ⊤)) :=
    (congrArg ((Scheme.Modules.pullbackUnitIso g).inv.app ⊤) h1).symm.trans
      (congrArg (fun k : (Scheme.Modules.pullback g).obj (Scheme.unitModule X) ⟶
        (Scheme.Modules.pullback g).obj (Scheme.unitModule X) => k.app ⊤
          (pullbackSectionHom g (Scheme.unitModule X) ⊤ ⊤ le_top (1 : Γ(X, ⊤))))
        (Scheme.Modules.pullbackUnitIso g).hom_inv_id)
  show ((Scheme.Modules.pullback g).map φ).app ⊤
    ((Scheme.Modules.pullbackUnitIso g).inv.app ⊤ (1 : Γ(Y, ⊤))) = _
  rw [h2]
  exact pullbackSectionHom_naturality_apply g φ ⊤ ⊤ le_top _

/-- Two morphisms to `𝒪_T` agreeing on the image of `1` under an isomorphism `𝒪_T ≅ P` are
equal. -/
theorem eq_of_iso_hom_comp_app_top_one {T : Scheme.{u}} {P : T.Modules}
    (ζ : Scheme.unitModule T ≅ P) (γ γ' : P ⟶ Scheme.unitModule T)
    (h : (ζ.hom ≫ γ).app ⊤ (1 : Γ(T, ⊤)) = (ζ.hom ≫ γ').app ⊤ (1 : Γ(T, ⊤))) : γ = γ' := by
  rw [← cancel_epi ζ.hom, ← UnitSplitting.unitHomEquivTop_app_top_eq_self (ζ.hom ≫ γ),
    ← UnitSplitting.unitHomEquivTop_app_top_eq_self (ζ.hom ≫ γ'), h]

namespace UnitSplitting

variable {X : Scheme.{u}} {F G : X.Modules} {u : F ⟶ G} (S : UnitSplitting u)
  [F.IsQuasicoherent] [G.IsQuasicoherent] [Epi u] {T : Scheme.{u}} {g : T ⟶ X}
  {R : X.Modules} (UV : R ≅ Scheme.unitModule X) (σr : R ⟶ F) (hσ : S.σ = UV.inv ≫ σr)
  (f : T ⟶ projectiveBundle X F) (hg : f ≫ projectiveBundleToBase X F = g)
  (hf : Set.range f.base ⊆ splitQuotientComplement u)

omit [G.IsQuasicoherent] [Epi u] in
include hσ in
/-- If `S.σ = UV.inv ≫ σr`, then `S.splitHyperplaneMap f hg` is `g^*(UV.inv)` followed by
`g^*σr` and the quotient `(tautologicalDatum F).overQuotientMap f hg`. -/
theorem splitHyperplaneMap_eq_comp :
    S.splitHyperplaneMap f hg = (Scheme.Modules.pullback g).map UV.inv ≫
      ((Scheme.Modules.pullback g).map σr ≫ (tautologicalDatum F).overQuotientMap f hg) := by
  rw [splitHyperplaneMap, hσ, Functor.map_comp, Category.assoc]

include hσ hf in
/-- If `S.σ = UV.inv ≫ σr` and `f` lands in `splitQuotientComplement u`, then
`g^*σr ≫ (tautologicalDatum F).overQuotientMap f hg` is an isomorphism. -/
theorem isIso_map_comp_overQuotientMap :
    IsIso ((Scheme.Modules.pullback g).map σr ≫ (tautologicalDatum F).overQuotientMap f hg) :=
  CategoryTheory.isIso_of_eq_iso_hom_comp (S.splitHyperplaneIso f hg hf).hom
    ((Scheme.Modules.pullback g).mapIso UV.symm) _ (S.splitHyperplaneMap_eq_comp UV σr hσ f hg)

include hσ in
/-- **The coordinate morphism as a ratio** of `q_f ∘ g^*σ'` and `q_f ∘ g^*σ_r`, for `σ` written as
`σ_r` precomposed with an identification `𝒪_X ≅ R`. -/
theorem splitCoordMap_eq_ratio
    [IsIso ((Scheme.Modules.pullback g).map σr ≫ (tautologicalDatum F).overQuotientMap f hg)] :
    S.splitCoordMap f hg hf =
      ((Scheme.Modules.pullback g).map S.σ' ≫ (tautologicalDatum F).overQuotientMap f hg) ≫
        inv ((Scheme.Modules.pullback g).map σr ≫ (tautologicalDatum F).overQuotientMap f hg) ≫
        (Scheme.Modules.pullback g).map UV.hom ≫ (Scheme.Modules.pullbackUnitIso g).hom := by
  have h := CategoryTheory.iso_inv_eq_of_hom_eq_comp (S.splitHyperplaneIso f hg hf)
    ((Scheme.Modules.pullback g).mapIso UV.symm) _ (S.splitHyperplaneMap_eq_comp UV σr hσ f hg)
  rw [splitCoordMap, h]
  simp only [Functor.mapIso_inv, Iso.symm_inv, Category.assoc]

end UnitSplitting

end Stacks.RelativeProj

/-! ### The quotient `q` as a ratio -/

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {U P X : AlgebraicSpaces B S hS} (ι : U ⟶ P) (π : P ⟶ X)
    {F : Modules.{u, u} B S hS X.1 X.2} {L : Modules.{u, u} B S hS P.1 P.2}
    (τ : (modulePullback B S hS π).obj F ⟶ L)

/-- The map `(π ∘ ι)^*𝓜 ⟶ ι^*π^*𝓜 ⟶ ι^*𝓛` of `σ : 𝓜 ⟶ 𝓕`. -/
abbrev compPullbackQuotient {M : Modules.{u, u} B S hS X.1 X.2} (σ : M ⟶ F) :
    (modulePullback B S hS (ι ≫ π)).obj M ⟶ (modulePullback B S hS ι).obj L :=
  (QuasiCoherentDescent.pullbackComparison B S hS ι π (ι ≫ π) rfl M).hom ≫
    (modulePullback B S hS ι).map ((modulePullback B S hS π).map σ ≫ τ)

/-- The component at `M` of `modulePullbackCompIso ι π` followed by the comparison
`QuasiCoherentDescent.pullbackComparison ι π (ι ≫ π) rfl M` is the identity. -/
theorem modulePullbackCompIso_hom_app_comp_pullbackComparison_hom
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackCompIso B S hS ι π).hom.app M ≫
      (QuasiCoherentDescent.pullbackComparison B S hS ι π (ι ≫ π) rfl M).hom = 𝟙 _ := by
  rw [QuasiCoherentDescent.pullbackComparison_rfl, Iso.symm_hom, Iso.app_inv, Iso.hom_inv_id_app]

/-- The image under `ι^*` of `𝒪_P ⟶ π^*𝒪_X ⟶ π^*𝓕 ⟶ 𝓛`, built from `σO` and `τ`, is the
identification `modulePullbackUnitCompIso ι π` followed by `compPullbackQuotient ι π τ σO`. -/
theorem modulePullback_map_unitIso_comp_eq
    (σO : (SheafOfModules.unit (structureRingSheaf B S hS X) : Modules.{u, u} B S hS X.1 X.2) ⟶ F) :
    (modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
      (modulePullback B S hS π).map σO ≫ τ) =
      (modulePullbackUnitCompIso ι π).hom ≫ compPullbackQuotient ι π τ σO :=
  (Functor.map_comp _ _ _).trans
    (CategoryTheory.comp_eq_comp_comp_of_comp_eq_id _ _ _ _
      (modulePullbackCompIso_hom_app_comp_pullbackComparison_hom ι π _))

/-- If the image under `ι^*` of `𝒪_P ⟶ π^*𝒪_X ⟶ π^*𝓕 ⟶ 𝓛`, built from `σO` and `τ`, is an
isomorphism, then so is `compPullbackQuotient ι π τ σO`. -/
theorem isIso_compPullbackQuotient
    (σO : (SheafOfModules.unit (structureRingSheaf B S hS X) : Modules.{u, u} B S hS X.1 X.2) ⟶ F)
    [hs : IsIso ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
      (modulePullback B S hS π).map σO ≫ τ))] :
    IsIso (compPullbackQuotient ι π τ σO) :=
  @CategoryTheory.isIso_of_eq_iso_hom_comp _ _ _ _ _
    ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
      (modulePullback B S hS π).map σO ≫ τ)) hs (modulePullbackUnitCompIso ι π)
    (compPullbackQuotient ι π τ σO) (modulePullback_map_unitIso_comp_eq ι π τ σO)

/-- The comparison `(π ∘ ι)^*ℰ ⟶ ι^*π^*ℰ` at the composite is the inverse of the comparison of
Stacks 03LU. -/
theorem modulePullbackCompIso_inv_app_comp_eq {E : Modules.{u, u} B S hS X.1 X.2} (σE : E ⟶ F) :
    (modulePullbackCompIso B S hS ι π).inv.app E ≫
        (modulePullback B S hS ι).map ((modulePullback B S hS π).map σE ≫ τ) =
      compPullbackQuotient ι π τ σE := by
  rw [compPullbackQuotient, QuasiCoherentDescent.pullbackComparison_rfl, Iso.symm_hom, Iso.app_inv]

/-- **`q` as a ratio**: for `ι : U ⟶ P`, `π : P ⟶ X` and `τ : π^*𝓕 ⟶ 𝓛`, the composite
`u^*ℰ ⟶ ι^*π^*ℰ ⟶ ι^*𝓛 ⟶ ι^*𝒪_P ⟶ 𝒪_U` of `ι^*(π^*σ_E ≫ τ)` and the inverse of
`ι^*(π^*σ_O ≫ τ)` is the ratio of the two maps `compPullbackQuotient`, followed by the
identification `(π ∘ ι)^*𝒪_X ≅ 𝒪_U`. -/
theorem modulePullback_comp_inv_eq_ratio {E : Modules.{u, u} B S hS X.1 X.2} (σE : E ⟶ F)
    (σO : (SheafOfModules.unit (structureRingSheaf B S hS X) : Modules.{u, u} B S hS X.1 X.2) ⟶ F)
    [IsIso ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
      (modulePullback B S hS π).map σO ≫ τ))]
    [IsIso (compPullbackQuotient ι π τ σO)] :
    (modulePullbackCompIso B S hS ι π).inv.app E ≫
        (modulePullback B S hS ι).map ((modulePullback B S hS π).map σE ≫ τ) ≫
        inv ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
          (modulePullback B S hS π).map σO ≫ τ)) ≫
        (modulePullbackUnitIso B S hS ι).hom =
      compPullbackQuotient ι π τ σE ≫ inv (compPullbackQuotient ι π τ σO) ≫
        (modulePullbackUnitCompIso ι π).inv ≫ (modulePullbackUnitIso B S hS ι).hom :=
  (CategoryTheory.ratio_shape _ _ _ _ _ _ (modulePullback_map_unitIso_comp_eq ι π τ σO)).trans
    (congrArg (· ≫ _) (modulePullbackCompIso_inv_app_comp_eq ι π τ σE))

/-- The comparison of the reading of an inverse image with the reading along the composite,
written out. -/
theorem schemeReadingModulePullbackIso_eq {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ Y) :
    schemeReadingModulePullbackIso g M ψ =
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso
          (QuasiCoherentDescent.pullbackComparison B S hS ψ g (ψ ≫ g) rfl M).symm) :=
  rfl

variable {E : Modules.{u, u} B S hS X.1 X.2} (hEq : E.IsQuasicoherentOnSite)
  (hOq : (SheafOfModules.unit (structureRingSheaf B S hS X) :
    Modules.{u, u} B S hS X.1 X.2).IsQuasicoherentOnSite)
  (σE : E ⟶ F)
  (σO : (SheafOfModules.unit (structureRingSheaf B S hS X) : Modules.{u, u} B S hS X.1 X.2) ⟶ F)
  {A Y : BigFppfOver B S hS} {ρ : A ⟶ Y} {ψY : representedAlgebraicSpace B S hS Y ⟶ X}
  (c : representedAlgebraicSpace B S hS A ⟶ U)
  (wρ : representedSpaceMap B S hS ρ ≫ ψY = c ≫ (ι ≫ π))
  {TU : ((BigFppfOver.toScheme B S hS).obj A).Modules}
  (ε : representedZariskiModule B S hS A
    ((modulePullback B S hS c).obj ((modulePullback B S hS ι).obj L)) ≅ TU)
  (univE : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).obj
        (schemeReading E ψY) ⟶ TU)
  (univO : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).obj
        (schemeReading (SheafOfModules.unit (structureRingSheaf B S hS X) :
          Modules.{u, u} B S hS X.1 X.2) ψY) ⟶ TU)

/-- **The reading of `q` is the ratio of the readings.** If the readings of the two maps
`(π ∘ ι)^*𝓜 ⟶ ι^*𝓛` of `σ_E` and `σ_O` are `univ_E` and `univ_O` with a common identification
`ε` of the targets, the reading of `q = ι^*(π^*σ_E ≫ τ) ∘ ι^*(π^*σ_O ≫ τ)⁻¹`, through the canonical
identifications of the sources, is `univ_E ∘ univ_O⁻¹` followed by the reading of the
identification `(π ∘ ι)^*𝒪_X ≅ 𝒪_U`. -/
theorem reading_modulePullback_comp_inv_eq
    [hs : IsIso ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
      (modulePullback B S hS π).map σO ≫ τ))] [hU : IsIso univO]
    (hE : QuotientReadingHyp E hEq wρ univE ε
      ((modulePullback B S hS c).map (compPullbackQuotient ι π τ σE))
      (QuasiCoherentDescent.pullbackComparison B S hS c (ι ≫ π) (c ≫ (ι ≫ π)) rfl E).symm)
    (hO : QuotientReadingHyp _ hOq wρ univO ε
      ((modulePullback B S hS c).map (compPullbackQuotient ι π τ σO))
      (QuasiCoherentDescent.pullbackComparison B S hS c (ι ≫ π) (c ≫ (ι ≫ π)) rfl _).symm) :
    (schemeReadingPullbackIso E hEq ρ wρ).hom ≫ (schemeReadingModulePullbackIso (ι ≫ π) E c).inv ≫
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj A) A.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS A).inverse.map
          ((modulePullback B S hS c).map
            ((modulePullbackCompIso B S hS ι π).inv.app E ≫
              (modulePullback B S hS ι).map ((modulePullback B S hS π).map σE ≫ τ) ≫
              inv ((modulePullback B S hS ι).map ((modulePullbackUnitIso B S hS π).inv ≫
                (modulePullback B S hS π).map σO ≫ τ)) ≫
              (modulePullbackUnitIso B S hS ι).hom))) =
    univE ≫ inv univO ≫ (schemeReadingPullbackIso _ hOq ρ wρ).hom ≫
      (schemeReadingModulePullbackIso (ι ≫ π) _ c).inv ≫
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj A) A.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS A).inverse.map
          ((modulePullback B S hS c).map
            ((modulePullbackUnitCompIso ι π).inv ≫ (modulePullbackUnitIso B S hS ι).hom))) := by
  have h0 : IsIso (compPullbackQuotient ι π τ σO) := isIso_compPullbackQuotient ι π τ σO
  have h1 : IsIso ((modulePullback B S hS c).map (compPullbackQuotient ι π τ σO)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ h0
  have h2 : IsIso ((representedSmallEtaleModuleEquivalence B S hS A).inverse.map
      ((modulePullback B S hS c).map (compPullbackQuotient ι π τ σO))) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ h1
  have h3 : IsIso ((SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj A) A.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS A).inverse.map
          ((modulePullback B S hS c).map (compPullbackQuotient ι π τ σO)))) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ h2
  unfold QuotientReadingHyp quotientReadingOf at hE hO
  rw [modulePullback_comp_inv_eq_ratio ι π τ σE σO]
  refine (congrArg (fun k => (schemeReadingPullbackIso E hEq ρ wρ).hom ≫
    (schemeReadingModulePullbackIso (ι ≫ π) E c).inv ≫ k)
    (CategoryTheory.Functor.map_map_map_comp_inv_comp (modulePullback B S hS c)
      (representedSmallEtaleModuleEquivalence B S hS A).inverse
      (SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj A) A.left.property)
      (compPullbackQuotient ι π τ σE) (compPullbackQuotient ι π τ σO)
      ((modulePullbackUnitCompIso ι π).inv ≫ (modulePullbackUnitIso B S hS ι).hom))).trans ?_
  exact CategoryTheory.reading_ratio_shape' (schemeReadingPullbackIso E hEq ρ wρ)
    (schemeReadingModulePullbackIso (ι ≫ π) E c) univE ε _
    (schemeReadingPullbackIso _ hOq ρ wρ) (schemeReadingModulePullbackIso (ι ≫ π) _ c) univO _
    ((SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj A) A.left.property).map
        ((representedSmallEtaleModuleEquivalence B S hS A).inverse.map
          ((modulePullback B S hS c).map
            ((modulePullbackUnitCompIso ι π).inv ≫ (modulePullbackUnitIso B S hS ι).hom))))
    hE hO

end AlgebraicGeometry.Space

end
