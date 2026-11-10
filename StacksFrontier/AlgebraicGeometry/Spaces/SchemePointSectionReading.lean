module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsPullbackRepresentedComp
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartRestrictionQuotient

/-!
# Reading a module and its global sections at the scheme points of an algebraic space

Let `X` be an algebraic space over a scheme `S` of a big fppf site, `M` an `𝒪_X`-module and `σ` a
global section of `M`. At a scheme point `t : h_T ⟶ X` the inverse image `t^*M` of Stacks 03LU
restricts to a module on the scheme `T` (its restriction to the identity chart of `h_T`), and `σ`
to a global section of it. These readings are compatible with base change along a morphism
`h : T' ⟶ T` of the site: the canonical comparison of chart restrictions carries the pullback
along `h` of the reading at `t` to the reading at `h ≫ t`, section by section, and it is an
isomorphism when `M` is quasi-coherent.

## Main definitions

* `AlgebraicGeometry.Space.chartRestrictionSheafMapIso`: the chart restriction of an isomorphism
  of modules, given by `AlgebraicGeometry.Space.chartRestrictionSheafMap` on both directions.
* `AlgebraicGeometry.Space.pointModule`: the reading of `t^*M` on `T`.
* `AlgebraicGeometry.Space.pointGlobalSection`: the reading of `t^*σ`, a global section of
  `AlgebraicGeometry.Space.pointModule`.
* `AlgebraicGeometry.Space.pointModuleComparison`: the comparison
  `h^*(t^*M)|_T ⟶ ((h ≫ t)^*M)|_{T'}`.

## Main results

* `AlgebraicGeometry.Space.pointModuleComparison_pullbackGlobalSections`: the comparison carries
  the pullback of the reading of a global section to the reading of the global section at the
  composite.
* `AlgebraicGeometry.Space.isIso_pointModuleComparison`: the comparison is an isomorphism for a
  quasi-coherent module.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A composite of morphisms of sheaves of modules, on a section. -/
theorem sheafOfModules_comp_val_app_apply {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {P Q W : SheafOfModules.{u} R} (f : P ⟶ Q) (g : Q ⟶ W) (U : Cᵒᵖ)
    (x : P.val.obj U) : (f ≫ g).val.app U x = g.val.app U (f.val.app U x) :=
  rfl

/-- A composite of morphisms of `𝒪`-modules on an algebraic space, on a section. -/
theorem modules_comp_val_app_apply_eq {Y : AlgebraicSpaces B S hS}
    {N₁ N₂ N₃ : Modules.{u, u} B S hS Y.1 Y.2} (κ : N₁ ⟶ N₂) (ε : N₂ ⟶ N₃)
    (U : (SmallEtale B S hS Y.1)ᵒᵖ) (w : N₁.val.obj U) (z : N₃.val.obj U)
    (h : ε.val.app U (κ.val.app U w) = z) : (κ ≫ ε).val.app U w = z :=
  h

/-! ### The chart restriction is functorial in the module -/

section Functorial

variable {X : AlgebraicSpaces B S hS} {G G' : Modules.{u, u} B S hS X.1 X.2}

/-- Two morphisms of modules on a chart scheme agree if they agree on every section. -/
theorem chartRestrictionSheaf_hom_ext {A : SmallEtale B S hS X.1}
    {P Q : (chartScheme A).Modules} {φ ψ : P ⟶ Q}
    (h : ∀ (O : (chartScheme A).Opens) (x : P.val.obj (op O)),
      φ.val.app (op O) x = ψ.val.app (op O) x) : φ = ψ := by
  ext O x
  exact h O x

/-- **The chart restriction of an isomorphism of `𝒪_X`-modules.** -/
def chartRestrictionSheafMapIso (κ : G ≅ G') (A : SmallEtale B S hS X.1) :
    chartRestrictionSheaf B S hS X G A ≅ chartRestrictionSheaf B S hS X G' A where
  hom := chartRestrictionSheafMap B S hS X κ.hom A
  inv := chartRestrictionSheafMap B S hS X κ.inv A
  hom_inv_id := chartRestrictionSheaf_hom_ext B S hS fun O x ↦ congrArg ULift.up
    (congrArg (fun k ↦ k.val.app (op ((chartOpens B S hS A).obj O)) x.down) κ.hom_inv_id |>.trans
      rfl)
  inv_hom_id := chartRestrictionSheaf_hom_ext B S hS fun O x ↦ congrArg ULift.up
    (congrArg (fun k ↦ k.val.app (op ((chartOpens B S hS A).obj O)) x.down) κ.inv_hom_id |>.trans
      rfl)

end Functorial

/-! ### The readings at a scheme point -/

section Points

variable {X : AlgebraicSpaces B S hS} (M : Modules.{u, u} B S hS X.1 X.2)

/-- **The reading of `M` along a morphism `k : h_T ⟶ X`** from the algebraic space represented by
an object `T` of the site: the inverse image `k^*M` of Stacks 03LU, restricted to the Zariski site
of `T` along the identity chart of `h_T`. -/
def pointModule (T : BigFppfOver B S hS) (k : representedAlgebraicSpace B S hS T ⟶ X) :
    ((BigFppfOver.toScheme B S hS).obj T).Modules :=
  chartRestrictionSheaf B S hS (representedAlgebraicSpace B S hS T)
    ((modulePullback B S hS k).obj M) (idEtaleChart B S hS T)

/-- **The reading of a global section of `M` along `k : h_T ⟶ X`**: the value of the pulled back
global section `k^*σ` on the identity chart of `h_T`, read as a global section of
`AlgebraicGeometry.Space.pointModule`. -/
def pointGlobalSection (T : BigFppfOver B S hS) (k : representedAlgebraicSpace B S hS T ⟶ X)
    (σ : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M) :
    Γ(pointModule B S hS M T k, ⊤) :=
  chartRestrictionSheafTopEquiv B S hS (representedAlgebraicSpace B S hS T)
    ((modulePullback B S hS k).obj M) (idEtaleChart B S hS T)
    (((globalSectionsPullbackMap B S hS k M).hom σ).1 (op (idEtaleChart B S hS T)))

variable {T T' : BigFppfOver B S hS}

/-- The square of identity charts over a morphism of the site commutes. -/
theorem representedMap_idEtaleChart_comm (h : T' ⟶ T) :
    yoneda.map h ≫ (idEtaleChart B S hS T).obj.hom =
      (idEtaleChart B S hS T').obj.hom ≫ (representedMap B S hS h).hom := by
  change yoneda.map h ≫ 𝟙 _ = 𝟙 _ ≫ yoneda.map h
  rw [Category.comp_id, Category.id_comp]

/-- The diagram of identity charts over a morphism of the site. -/
abbrev representedIdChartDiagram (h : T' ⟶ T) :
    ChartDiagram B S hS (yoneda.obj T') (yoneda.obj T) (representedMap B S hS h).hom :=
  ⟨idEtaleChart B S hS T', idEtaleChart B S hS T, h,
    (representedMap_idEtaleChart_comm B S hS h).symm⟩

/-- **The comparison of the readings along `k` and along `k' = h ≫ k`**: the canonical comparison
of chart restrictions along the diagram of identity charts over `h`, followed by the comparison of
iterated inverse images of Stacks 03LU. -/
def pointModuleComparison (h : T' ⟶ T) (k : representedAlgebraicSpace B S hS T ⟶ X)
    (k' : representedAlgebraicSpace B S hS T' ⟶ X) (e : representedMap B S hS h ≫ k = k') :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
        (pointModule B S hS M T k) ⟶
      pointModule B S hS M T' k' :=
  chartRestrictionPullbackComparison B S hS (representedMap B S hS h) (idEtaleChart B S hS T)
      (idEtaleChart B S hS T') h (representedMap_idEtaleChart_comm B S hS h)
      ((modulePullback B S hS k).obj M) ≫
    chartRestrictionSheafMap B S hS _
      ((modulePullbackCompIso B S hS (representedMap B S hS h) k).hom.app M ≫
        eqToHom (congrArg (fun k ↦ (modulePullback B S hS k).obj M) e)) (idEtaleChart B S hS T')

/-- **For a quasi-coherent module the comparison of the readings is an isomorphism.** -/
theorem isIso_pointModuleComparison (hM : M.IsQuasicoherentOnSite) (h : T' ⟶ T)
    (k : representedAlgebraicSpace B S hS T ⟶ X)
    (k' : representedAlgebraicSpace B S hS T' ⟶ X) (e : representedMap B S hS h ≫ k = k') :
    IsIso (pointModuleComparison B S hS M h k k' e) := by
  subst e
  rw [pointModuleComparison, eqToHom_refl, Category.comp_id]
  have h1 := isIso_chartRestrictionPullbackComparison B S hS (representedMap B S hS h)
    (idEtaleChart B S hS T) (idEtaleChart B S hS T') h (representedMap_idEtaleChart_comm B S hS h)
    ((modulePullback B S hS k).obj M)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ M hM)
  have h2 := (chartRestrictionSheafMapIso B S hS
    ((modulePullbackCompIso B S hS (representedMap B S hS h) k).app M)
    (idEtaleChart B S hS T')).isIso_hom
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

/-- The global section `pullbackGlobalSections` is the pullback of the section over `⊤`. -/
theorem pullbackGlobalSections_eq_pullbackSection {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (F : Z.Modules) (x : Γ(F, ⊤)) :
    pullbackGlobalSections f F x = Scheme.Modules.pullbackSection f F ⊤ ⊤ le_top x := by
  change ((Scheme.Modules.pullback f).obj F).presheaf.map (eqToHom (by simp)).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).app ⊤ x) =
    ((Scheme.Modules.pullback f).obj F).val.map (homOfLE le_top).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F).val.app (op ⊤) x)
  rfl

/-- The value of `AlgebraicGeometry.Space.chartRestrictionSheafTopEquiv`: restriction of sections
from the chart to the chart cut out by `⊤`. -/
theorem chartRestrictionSheafTopEquiv_down {Y : AlgebraicSpaces B S hS}
    (N : Modules.{u, u} B S hS Y.1 Y.2) (A : SmallEtale B S hS Y.1) (m : N.val.obj (op A)) :
    (chartRestrictionSheafTopEquiv B S hS Y N A m).down =
      N.val.map (chartOpensTopHom B S hS Y A).op m :=
  rfl

/-- **The comparison of readings carries the pullback of the reading of a global section along `k`
to its reading along `k' = h ≫ k`.** -/
theorem pointModuleComparison_pullbackGlobalSections (h : T' ⟶ T)
    (k : representedAlgebraicSpace B S hS T ⟶ X)
    (k' : representedAlgebraicSpace B S hS T' ⟶ X) (e : representedMap B S hS h ≫ k = k')
    (σ : (globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M) :
    (pointModuleComparison B S hS M h k k' e).val.app (op ⊤)
        (pullbackGlobalSections ((BigFppfOver.toScheme B S hS).map h)
          (pointModule B S hS M T k) (pointGlobalSection B S hS M T k σ)) =
      pointGlobalSection B S hS M T' k' σ := by
  subst e
  have hc := chartRestrictionPullbackComparison_pullbackSection B S hS (representedMap B S hS h)
    (idEtaleChart B S hS T) (idEtaleChart B S hS T') h (representedMap_idEtaleChart_comm B S hS h)
    ((modulePullback B S hS k).obj M) ⊤ ⊤ le_top (pointGlobalSection B S hS M T k σ)
  have hnat := modulePullbackChartSection_naturality B S hS (representedMap B S hS h)
    ((modulePullback B S hS k).obj M) (representedIdChartDiagram B S hS h)
    (chartOpenDiagramOfLE B S hS (representedMap B S hS h) (idEtaleChart B S hS T)
      (idEtaleChart B S hS T') h (representedMap_idEtaleChart_comm B S hS h) ⊤ ⊤ le_top)
    (chartOpensTopHom B S hS (representedAlgebraicSpace B S hS T') (idEtaleChart B S hS T'))
    (chartOpensTopHom B S hS (representedAlgebraicSpace B S hS T) (idEtaleChart B S hS T)) (by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact (Scheme.Hom.resLE_comp_ι ((BigFppfOver.toScheme B S hS).map h) le_top).symm)
    (((globalSectionsPullbackMap B S hS k M).hom σ).1 (op (idEtaleChart B S hS T)))
  have hval : ((globalSectionsPullbackMap B S hS (representedMap B S hS h)
      ((modulePullback B S hS k).obj M)).hom
      ((globalSectionsPullbackMap B S hS k M).hom σ)).1 (op (idEtaleChart B S hS T')) =
      modulePullbackChartSection B S hS (representedMap B S hS h)
        ((modulePullback B S hS k).obj M) (representedIdChartDiagram B S hS h)
        (((globalSectionsPullbackMap B S hS k M).hom σ).1 (op (idEtaleChart B S hS T))) :=
    globalSectionsPullbackMap_val_chartDiagram B S hS (representedMap B S hS h)
      ((modulePullback B S hS k).obj M) ((globalSectionsPullbackMap B S hS k M).hom σ)
      (representedIdChartDiagram B S hS h)
  have hcomp := modulePullbackCompIso_globalSectionsPullbackMap_represented B S hS h k M σ
    (idEtaleChart B S hS T')
  rw [pointModuleComparison, eqToHom_refl, Category.comp_id,
    pullbackGlobalSections_eq_pullbackSection]
  refine ULift.ext ?_
  change ((modulePullbackCompIso B S hS (representedMap B S hS h) k).hom.app M).val.app
      (op ((chartOpens B S hS (idEtaleChart B S hS T')).obj ⊤))
      ((chartRestrictionPullbackComparison B S hS (representedMap B S hS h) (idEtaleChart B S hS T)
        (idEtaleChart B S hS T') h (representedMap_idEtaleChart_comm B S hS h)
        ((modulePullback B S hS k).obj M)).val.app (op ⊤)
        (Scheme.Modules.pullbackSection _ _ ⊤ ⊤ le_top
          (pointGlobalSection B S hS M T k σ))).down = _
  rw [hc, show (pointGlobalSection B S hS M T k σ).down = _ from
    chartRestrictionSheafTopEquiv_down B S hS _ _ _,
    show (pointGlobalSection B S hS M T' (representedMap B S hS h ≫ k) σ).down = _ from
    chartRestrictionSheafTopEquiv_down B S hS _ _ _]
  refine (congrArg (fun z ↦ ((modulePullbackCompIso B S hS (representedMap B S hS h) k).hom.app
      M).val.app (op ((chartOpens B S hS (idEtaleChart B S hS T')).obj ⊤)) z) (hnat.trans
        (congrArg _ hval.symm))).trans ?_
  refine (PresheafOfModules.naturality_apply ((modulePullbackCompIso B S hS
      (representedMap B S hS h) k).hom.app M).val
    (chartOpensTopHom B S hS (representedAlgebraicSpace B S hS T') (idEtaleChart B S hS T')).op
      _).trans ?_
  exact congrArg (fun z ↦ (((modulePullback B S hS (representedMap B S hS h ≫ k)).obj M).val.map
    (chartOpensTopHom B S hS (representedAlgebraicSpace B S hS T') (idEtaleChart B S hS T')).op) z)
    hcomp

end Points

end AlgebraicGeometry.Space

end
