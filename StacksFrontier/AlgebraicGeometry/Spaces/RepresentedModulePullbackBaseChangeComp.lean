module

public meta import StacksFrontier.Tactic.HEqCongr
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SectionsComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutModuleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompUnitChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompUnitEq
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChangeComposition
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqSquareComp

/-!
# The inverse image along represented morphisms is compatible with composition

For morphisms `p : X ⟶ Y` and `q : Y ⟶ Z` of the big fppf site over `S`, the identification
`AlgebraicGeometry.Space.representedModulePullbackIso` of the inverse image of modules of
Stacks 03LU along a represented morphism with the pullback along the morphism of small étale
ringed sites of Stacks 070R (2) composes: the identification along `p ≫ q` is the pasting of those
along `q` and `p`, read through the composition law of Stacks 03LU and the composition law
`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` of the small étale pullbacks.

By uniqueness of left adjoints it is enough to compose the squares of direct images
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso`.  Read through the chart
comparison `AlgebraicGeometry.Space.modulePushforwardChartIso`, each square is restriction of
sections along the comparison of the two base changes, and the composition comparison of direct
images is the iterated chart projection
(`AlgebraicGeometry.Space.chartModProj_modulePushforwardCompIso`); so the composition law becomes
an identity of morphisms of the small étale site of the scheme underlying `X` into a fibre product
(`AlgebraicGeometry.Space.representedBaseChange_comp_mor`).

## Main results

* `AlgebraicGeometry.Space.pushforwardSquare_comp_generic`: the composition law of the squares of
  direct images, for squares whose chart readings compose on sections, and
  `AlgebraicGeometry.Space.representedModulePushforwardSquare_chartComp`: they do.
* `AlgebraicGeometry.Space.representedModulePullbackIso_hom_comp_of_eq`: the composition law of the
  identifications of inverse images.

## Implementation notes

Every computation on sections is done in a lemma whose data are variables
(`AlgebraicGeometry.Space.pushforwardSquare_comp_generic`), instantiated once: the sections of
the concrete modules admit two spellings of their site (`SmallEtale` and the site of the small
étale ringed site), and comparing them under a projection makes elaborator and kernel evaluate
the modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange



namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Square

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- The square of direct images `representedModulePushforwardSquareIso` is the composite of the
composition isomorphisms of pushforwards, the comparison of the two base changes, and the inverse
of the chart comparison `modulePushforwardChartIso`. -/
theorem representedModulePushforwardSquareIso_eq_pushforwardComp :
    representedModulePushforwardSquareIso B S hS g hg =
    (SheafOfModules.pushforwardComp.{u} (representedEquivSharp B S hS T)
      (representedSchemeStructureMapRing B S hS g)) ≪≫
      (SheafOfModules.pushforwardCongr₂.{u} _ (representedSmallEtaleBaseChangeIso B S hS g hg)
      (representedStructureMapRing_square B S hS g hg)) ≪≫ (SheafOfModules.pushforwardComp.{u}
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g) hg)
      (representedEquivSharp B S hS T')).symm ≪≫
      (Functor.isoWhiskerLeft ((representedSmallEtaleModuleEquivalence B S hS T').functor)
      (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg).symm) := rfl

/-- The square of direct images read through the chart comparison: restriction along the
comparison of the two base changes. -/
noncomputable def representedModulePushforwardSquareChartIso :
    SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS g) ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor ≅
      (representedSmallEtaleModuleEquivalence B S hS T').functor ⋙
        smallBaseChangeModulePushforward.{u, u} B S hS (representedSpaceMap B S hS g) hg :=
  ((SheafOfModules.pushforwardComp.{u} (representedEquivSharp B S hS T)
      (representedSchemeStructureMapRing B S hS g)) ≪≫
      (SheafOfModules.pushforwardCongr₂.{u} _
      (representedSmallEtaleBaseChangeIso B S hS g (relativelyRepresentable_yoneda_map B S hS g))
      (representedStructureMapRing_square B S hS g (relativelyRepresentable_yoneda_map B S hS g)))
      ≪≫ (SheafOfModules.pushforwardComp.{u}
      (smallBaseChangeSharp B S hS (representedSpaceMap B S hS g)
          (relativelyRepresentable_yoneda_map B S hS g))
      (representedEquivSharp B S hS T')).symm)

/-- The square of direct images followed by the chart comparison `modulePushforwardChartIso` is
`representedModulePushforwardSquareChartIso`. -/
theorem representedModulePushforwardSquareIso_trans_chartIso :
    representedModulePushforwardSquareIso B S hS g hg ≪≫
    Functor.isoWhiskerLeft ((representedSmallEtaleModuleEquivalence B S hS T').functor)
      (modulePushforwardChartIso B S hS (representedSpaceMap B S hS g) hg) =
    representedModulePushforwardSquareChartIso B S hS g hg := by
  rw [representedModulePushforwardSquareIso_eq_pushforwardComp]
  exact Stacks.CategoryTheory.SquareComposition.trans_isoWhiskerLeft_symm_trans _ _ _ _

/-- The chart projection of a section of `σ`, for `σ` followed by the chart comparison equal to
`τ`, is the section of `τ`. -/
theorem chartModProj_hom_app_of_trans_chartIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom) {A : Type*} [Category A]
    {F : A ⥤ Modules.{u, u} B S hS Y.1 Y.2} {G : A ⥤ Modules.{u, u} B S hS X.1 X.2}
    (σ : F ≅ G ⋙ modulePushforward B S hS f)
    (τ : F ≅ G ⋙ smallBaseChangeModulePushforward.{u, u} B S hS f hrep)
    (h : σ ≪≫ Functor.isoWhiskerLeft G (modulePushforwardChartIso B S hS f hrep) = τ)
    (N : A) (V : SmallEtale B S hS Y.1) (n : (F.obj N).val.obj (op V)) :
    chartModProj B S hS f hrep (G.obj N) V ((σ.hom.app N).val.app (op V) n) =
      (τ.hom.app N).val.app (op V) n := by
  subst h
  exact (modulePushforwardChartIso_hom_app_val_app B S hS f hrep (G.obj N) V _).symm

end Square

section SquareComp

variable {X Y Z : BigFppfOver B S hS} (p : X ⟶ Y) (q : Y ⟶ Z)

/-- The comparison of pushforwards along the base-change structure maps, from the composite to
the two successive ones. -/
abbrev schemePushforwardCompHom :
    SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS (p ≫ q)) ⟶
      SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS p) ⋙
        SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS q) :=
  (SmallEtale.smallEtalePushforwardCompIso (associatedBigEtaleSite B) p.left q.left).hom ≫
    (SheafOfModules.pushforwardComp.{u}
      (SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B) q.left)
      (SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B) p.left)).inv

/-- The diagram chase behind `representedBaseChange_comp_mor`, on first projections. -/
theorem representedBaseChange_comp_chase {C : Type*} [Category C] {P0 P0' P1 P2 P3 P4 A2 A3 W0 : C}
    (a : P0 ⟶ P1) (b : P1 ⟶ P2) (c : P2 ⟶ P3) (d : P3 ⟶ P4) (e : P0 ⟶ P0') (r : P0' ⟶ P4)
    (fst : P4 ⟶ W0) (f2 : P3 ⟶ A3) (f3 : A3 ⟶ W0) (f4 : P2 ⟶ A2) (k : A2 ⟶ A3)
    (sp : P1 ⟶ A2) (sq : A2 ⟶ W0) (spq : P0' ⟶ W0) (spq' : P0 ⟶ W0)
    (hd : d ≫ fst = f2 ≫ f3) (hc : c ≫ f2 = f4 ≫ k) (hk : k ≫ f3 = sq) (hb : b ≫ f4 = sp)
    (ha : a ≫ sp ≫ sq = spq') (hr : r ≫ fst = spq) (he : e ≫ spq = spq') :
    (a ≫ b ≫ c ≫ d) ≫ fst = (e ≫ r) ≫ fst := by
  simp only [Category.assoc, hd, reassoc_of% hc, hk, reassoc_of% hb, ha, hr, he]

/-- The comparison of the two base changes at a chart, on first projections. -/
theorem representedSmallEtaleBaseChangeIso_hom_app_fst {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    (hg : yoneda.relativelyRepresentable (yoneda.map g)) (V : SmallEtale B S hS (yoneda.obj T)) :
    ((representedSmallEtaleBaseChangeIso B S hS g hg).hom.app V).hom.left ≫
        pullback.fst (yonedaEquiv V.1.hom).left g.left = (hg.snd V.1.hom).left := by
  rw [show ((representedSmallEtaleBaseChangeIso B S hS g hg).hom.app V).hom.left =
    (representedSmallEtaleBaseChangeComponent B S hS g hg V).hom.hom.left from rfl,
    representedSmallEtaleBaseChangeComponent_hom]
  exact (isPullback_representedChart_schemes B S hS g hg V).isoIsPullback_hom_fst _ _ _

/-- Base change along equal morphisms of algebraic spaces: the transport between the two base
changed charts is compatible with the cartesian projections. -/
theorem eqToHom_left_comp_snd {X' Y' : AlgebraicSpaces B S hS} {f f' : X' ⟶ Y'} (hff : f = f')
    (hrep : yoneda.relativelyRepresentable f.hom) (hrep' : yoneda.relativelyRepresentable f'.hom)
    (V : SmallEtale B S hS Y'.1)
    (hV : (smallBaseChange B S hS f hrep).obj V = (smallBaseChange B S hS f' hrep').obj V) :
    (eqToHom hV).hom.left ≫ hrep'.snd V.1.hom = hrep.snd V.1.hom := by
  subst hff
  obtain rfl : hrep = hrep' := rfl
  simp only [eqToHom_refl]
  exact Category.id_comp _

/-- Peeling a fourfold composite under a chart projection. -/
theorem chartModProj_comp4_apply {X' Y' : AlgebraicSpaces B S hS} (f : X' ⟶ Y')
    (hrep : yoneda.relativelyRepresentable f.hom)
    {Q R₁ R₂ R₃ : Modules.{u, u} B S hS Y'.1 Y'.2} {N : Modules.{u, u} B S hS X'.1 X'.2}
    (a : Q ⟶ R₁) (b : R₁ ⟶ R₂) (c : R₂ ⟶ R₃) (d : R₃ ⟶ (modulePushforward B S hS f).obj N)
    (V : SmallEtale B S hS Y'.1) (x : Q.val.obj (op V)) :
    chartModProj B S hS f hrep N V ((a ≫ b ≫ c ≫ d).val.app (op V) x) =
      chartModProj B S hS f hrep N V
        (d.val.app (op V) (c.val.app (op V) (b.val.app (op V) (a.val.app (op V) x)))) := rfl

/-- Restriction along equal morphisms. -/
theorem sheafOfModules_val_map_congr {CC : Type*} [Category CC] {J : GrothendieckTopology CC}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) {A A' : CC} {a b : A ⟶ A'} (h : a = b)
    (x : M.val.obj (op A')) : M.val.map a.op x = M.val.map b.op x := by
  rw [h]

/-- Restriction along a twofold composite. -/
theorem sheafOfModules_val_map_comp2 {CC : Type*} [Category CC] {J : GrothendieckTopology CC}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) {A₀ A₁ A₂ : CC} (a : A₀ ⟶ A₁)
    (b : A₁ ⟶ A₂) (x : M.val.obj (op A₂)) :
    M.val.map (a ≫ b).op x = M.val.map a.op (M.val.map b.op x) := by
  simp only [Stacks.SectionsComponents.val_map_map]

/-- Restriction along a fourfold composite. -/
theorem sheafOfModules_val_map_comp4 {CC : Type*} [Category CC] {J : GrothendieckTopology CC}
    {R : Sheaf J RingCat.{u}} (M : SheafOfModules.{u} R) {A₀ A₁ A₂ A₃ A₄ : CC} (a : A₀ ⟶ A₁)
    (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄) (x : M.val.obj (op A₄)) :
    M.val.map (a ≫ b ≫ c ≫ d).op x =
      M.val.map a.op (M.val.map b.op (M.val.map c.op (M.val.map d.op x))) := by
  simp only [Stacks.SectionsComponents.val_map_map]

/-- A morphism of `𝒪`-modules on the small étale site of an algebraic space is determined by its
action on sections, with the sections spelled as those of `AlgebraicGeometry.Space.Modules`. -/
theorem modules_hom_ext {Y' : AlgebraicSpaces B S hS}
    {M M' : Modules.{u, u} B S hS Y'.1 Y'.2} {f g : M ⟶ M'}
    (hfg : ∀ (V : SmallEtale B S hS Y'.1) (x : M.val.obj (op V)),
      f.val.app (op V) x = g.val.app (op V) x) : f = g :=
  Stacks.ChartUnitEq.hom_ext_val_app_unop hfg

/-- **The reindexing identity of the composition law**, on underlying schemes: both routes from
the base-changed chart of the composite to the base change of the scheme chart are the same
morphism of the small étale site of the scheme underlying `X`. -/
theorem representedBaseChange_comp_mor (V : SmallEtale B S hS (yoneda.obj Z))
    (h : representedSpaceMap B S hS p ≫ representedSpaceMap B S hS q =
      representedSpaceMap B S hS (p ≫ q))
    (hpq : yoneda.relativelyRepresentable
      (representedSpaceMap B S hS p ≫ representedSpaceMap B S hS q).hom)
    (hV : (smallBaseChange B S hS (representedSpaceMap B S hS p ≫ representedSpaceMap B S hS q)
        hpq).obj V = (smallBaseChange B S hS (representedSpaceMap B S hS (p ≫ q))
          (relativelyRepresentable_yoneda_map B S hS (p ≫ q))).obj V) :
    (representedSmallEtaleEquivalence B S hS X).functor.map
          (chartBaseChangeCompComparison B S hS (representedSpaceMap B S hS p)
            (representedSpaceMap B S hS q) (relativelyRepresentable_yoneda_map B S hS p)
            (relativelyRepresentable_yoneda_map B S hS q) hpq V) ≫
        (representedSmallEtaleBaseChangeIso B S hS p
            (relativelyRepresentable_yoneda_map B S hS p)).hom.app
          ((smallBaseChange B S hS (representedSpaceMap B S hS q)
            (relativelyRepresentable_yoneda_map B S hS q)).obj V) ≫
        (_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) p.left).map
          ((representedSmallEtaleBaseChangeIso B S hS q
            (relativelyRepresentable_yoneda_map B S hS q)).hom.app V) ≫
        (smallEtaleBaseChange_factoredCompIso (associatedBigEtaleSite B) _ _ _ p.left q.left
          (p.left ≫ q.left) rfl).hom.app
          ((representedSmallEtaleEquivalence B S hS Z).functor.obj V) =
      (representedSmallEtaleEquivalence B S hS X).functor.map (eqToHom hV) ≫
        (representedSmallEtaleBaseChangeIso B S hS (p ≫ q)
          (relativelyRepresentable_yoneda_map B S hS (p ≫ q))).hom.app V := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (pullback.hom_ext ?_ ?_))
  · simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left]
    exact representedBaseChange_comp_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (smallEtaleBaseChange_factoredCompIso_hom_app_fst
          (associatedBigEtaleSite B) _ _ _ p.left q.left
        (p.left ≫ q.left) rfl ((representedSmallEtaleEquivalence B S hS Z).functor.obj V))
      (pullback.lift_fst _ _ _)
      (representedSmallEtaleBaseChangeIso_hom_app_fst B S hS q _ V)
      (representedSmallEtaleBaseChangeIso_hom_app_fst B S hS p _ _)
      (congrArg Over.Hom.left (toOver_map_chartBaseChangeCompComparison_comp_snd B S hS
        (representedSpaceMap B S hS p) (representedSpaceMap B S hS q) _ _ hpq V))
      (representedSmallEtaleBaseChangeIso_hom_app_fst B S hS (p ≫ q) _ V)
      (congrArg Over.Hom.left (eqToHom_left_comp_snd B S hS h hpq _ V hV))
  · exact (Over.w _).trans (Over.w _).symm

/-- Peeling the last factor off a composite under a chart projection, the target written as the
value of a composite functor. -/
theorem chartModProj_comp_apply' {X' Y' : AlgebraicSpaces B S hS} (f : X' ⟶ Y')
    (hrep : yoneda.relativelyRepresentable f.hom) {A : Type*} [Category A]
    (G : A ⥤ Modules.{u, u} B S hS X'.1 X'.2) (N₀ : A) {Q R : Modules.{u, u} B S hS Y'.1 Y'.2}
    (p : Q ⟶ R) (q : R ⟶ (G ⋙ modulePushforward B S hS f).obj N₀)
    (V : SmallEtale B S hS Y'.1) (x : Q.val.obj (op V)) :
    chartModProj B S hS f hrep (G.obj N₀) V ((p ≫ q).val.app (op V) x) =
      chartModProj B S hS f hrep (G.obj N₀) V (q.val.app (op V) (p.val.app (op V) x)) := rfl

/-- Rewriting the section under a chart projection of a component. -/
theorem chartModProj_val_app_congr {X' Y' : AlgebraicSpaces B S hS} (f : X' ⟶ Y')
    (hrep : yoneda.relativelyRepresentable f.hom) {M : Modules.{u, u} B S hS Y'.1 Y'.2}
    {N : Modules.{u, u} B S hS X'.1 X'.2} (φ : M ⟶ (modulePushforward B S hS f).obj N)
    (W : SmallEtale B S hS Y'.1) {y y' : M.val.obj (op W)} (h : y = y') :
    chartModProj B S hS f hrep N W (φ.val.app (op W) y) =
      chartModProj B S hS f hrep N W (φ.val.app (op W) y') := by
  rw [h]

/-- Transport of the chart projection along an equality of morphisms of algebraic spaces,
whiskered by a functor. -/
theorem chartModProj_whiskerLeft_eqToHom_app {X' Y' Z' : AlgebraicSpaces B S hS} (fp : X' ⟶ Y')
    (fq : Y' ⟶ Z') {f' : X' ⟶ Z'} (hff : fp ≫ fq = f')
    (hrep : yoneda.relativelyRepresentable (fp ≫ fq).hom)
    (hrep' : yoneda.relativelyRepresentable f'.hom) {A : Type*} [Category A]
    (G : A ⥤ Modules.{u, u} B S hS X'.1 X'.2) (N : A) (V : SmallEtale B S hS Z'.1)
    (z : ((G ⋙ modulePushforward B S hS f').obj N).val.obj (op V)) :
    chartModProj B S hS (fp ≫ fq) hrep (G.obj N) V
        (((Functor.whiskerLeft G (eqToHom (congrArg (modulePushforward B S hS) hff.symm))).app
          N).val.app (op V) z) =
      (G.obj N).val.map (eqToHom (smallBaseChange_obj_congr hff hrep hrep' V)).op
        (chartModProj B S hS f' hrep' (G.obj N) V z) := by
  subst hff
  obtain rfl : hrep = hrep' := rfl
  rw [eqToHom_refl, eqToHom_refl]
  exact (Stacks.SectionsComponents.val_map_id (G.obj N) _).symm

/-- The chart readings of three squares of direct images compose on sections. -/
structure PushforwardSquareChartComp {X' Y' Z' : AlgebraicSpaces B S hS} (fp : X' ⟶ Y')
    (fq : Y' ⟶ Z') (f' : X' ⟶ Z') (hf : fp ≫ fq = f')
    (hp : yoneda.relativelyRepresentable fp.hom) (hq : yoneda.relativelyRepresentable fq.hom)
    (hpq : yoneda.relativelyRepresentable (fp ≫ fq).hom)
    (hf' : yoneda.relativelyRepresentable f'.hom)
    {AX AY AZ : Type*} [Category AX] [Category AY] [Category AZ]
    (ΦX : AX ⥤ Modules.{u, u} B S hS X'.1 X'.2) (ΦY : AY ⥤ Modules.{u, u} B S hS Y'.1 Y'.2)
    (ΦZ : AZ ⥤ Modules.{u, u} B S hS Z'.1 Z'.2)
    (Ep : AX ⥤ AY) (Eqq : AY ⥤ AZ) (Epq : AX ⥤ AZ) (cE : Epq ⟶ Ep ⋙ Eqq)
    (τp : Ep ⋙ ΦY ≅ ΦX ⋙ smallBaseChangeModulePushforward.{u, u} B S hS fp hp)
    (τq : Eqq ⋙ ΦZ ≅ ΦY ⋙ smallBaseChangeModulePushforward.{u, u} B S hS fq hq)
    (τpq : Epq ⋙ ΦZ ≅ ΦX ⋙ smallBaseChangeModulePushforward.{u, u} B S hS f' hf') : Prop where
  comp : ∀ (N : AX) (V : SmallEtale B S hS Z'.1) (x : ((Epq ⋙ ΦZ).obj N).val.obj (op V)),
      (ΦX.obj N).val.map (chartBaseChangeCompComparison B S hS fp fq hp hq hpq V).op
          ((τp.hom.app N).val.app (op ((smallBaseChange B S hS fq hq).obj V))
            ((τq.hom.app (Ep.obj N)).val.app (op V) ((ΦZ.map (cE.app N)).val.app (op V) x))) =
        (ΦX.obj N).val.map (eqToHom (smallBaseChange_obj_congr hf hpq hf' V)).op
          ((τpq.hom.app N).val.app (op V) x)

/-- **The composition law of a family of squares of direct images**, at variable data: three
squares `σ` of direct images whose chart readings `τ` compose on sections (`H`) compose. -/
theorem pushforwardSquare_comp_generic {X' Y' Z' : AlgebraicSpaces B S hS} (fp : X' ⟶ Y')
    (fq : Y' ⟶ Z') (f' : X' ⟶ Z') (hf : fp ≫ fq = f')
    (hp : yoneda.relativelyRepresentable fp.hom) (hq : yoneda.relativelyRepresentable fq.hom)
    (hpq : yoneda.relativelyRepresentable (fp ≫ fq).hom)
    (hf' : yoneda.relativelyRepresentable f'.hom)
    {AX AY AZ : Type*} [Category AX] [Category AY] [Category AZ]
    (ΦX : AX ⥤ Modules.{u, u} B S hS X'.1 X'.2) (ΦY : AY ⥤ Modules.{u, u} B S hS Y'.1 Y'.2)
    (ΦZ : AZ ⥤ Modules.{u, u} B S hS Z'.1 Z'.2)
    (Ep : AX ⥤ AY) (Eqq : AY ⥤ AZ) (Epq : AX ⥤ AZ) (cE : Epq ⟶ Ep ⋙ Eqq)
    (σp : Ep ⋙ ΦY ≅ ΦX ⋙ modulePushforward B S hS fp)
    (σq : Eqq ⋙ ΦZ ≅ ΦY ⋙ modulePushforward B S hS fq)
    (σpq : Epq ⋙ ΦZ ≅ ΦX ⋙ modulePushforward B S hS f')
    (τp : Ep ⋙ ΦY ≅ ΦX ⋙ smallBaseChangeModulePushforward.{u, u} B S hS fp hp)
    (τq : Eqq ⋙ ΦZ ≅ ΦY ⋙ smallBaseChangeModulePushforward.{u, u} B S hS fq hq)
    (τpq : Epq ⋙ ΦZ ≅ ΦX ⋙ smallBaseChangeModulePushforward.{u, u} B S hS f' hf')
    (hσp : σp ≪≫ Functor.isoWhiskerLeft ΦX (modulePushforwardChartIso B S hS fp hp) = τp)
    (hσq : σq ≪≫ Functor.isoWhiskerLeft ΦY (modulePushforwardChartIso B S hS fq hq) = τq)
    (hσpq : σpq ≪≫ Functor.isoWhiskerLeft ΦX (modulePushforwardChartIso B S hS f' hf') = τpq)
    (H : PushforwardSquareChartComp B S hS fp fq f' hf hp hq hpq hf' ΦX ΦY ΦZ Ep Eqq
        Epq cE τp τq τpq)
    (N : AX) :
    ΦZ.map (cE.app N) ≫ σq.hom.app (Ep.obj N) ≫ (modulePushforward B S hS fq).map (σp.hom.app N) ≫
        (modulePushforwardCompIso B S hS fp fq).hom.app (ΦX.obj N) =
      σpq.hom.app N ≫
        (Functor.whiskerLeft ΦX (eqToHom (congrArg (modulePushforward B S hS) hf.symm))).app N := by
  refine modules_hom_ext B S hS fun V x ↦ chartModProj_injective B S hS _ hpq (ΦX.obj N) V ?_
  have hb := chartModProj_hom_app_of_trans_chartIso B S hS fq hq σq τq hσq (Ep.obj N) V
  have hal := chartModProj_hom_app_of_trans_chartIso B S hS fp hp σp τp hσp N
    ((smallBaseChange B S hS fq hq).obj V)
  refine (chartModProj_comp4_apply B S hS _ hpq _ _ _ _ V x).trans ?_
  refine (chartModProj_modulePushforwardCompIso B S hS fp fq hp hq hpq (ΦX.obj N) V _).trans ?_
  refine Eq.trans ?_ ((H.comp N V x).trans ?_)
  · refine congrArg
        ((ΦX.obj N).val.map (chartBaseChangeCompComparison B S hS fp fq hp hq hpq V).op) ?_
    refine (congrArg (chartModProj B S hS fp hp (ΦX.obj N) ((smallBaseChange B S hS fq hq).obj V))
      (chartModProj_map B S hS fq hq (σp.hom.app N) V _)).trans ?_
    exact (chartModProj_val_app_congr B S hS fp hp (σp.hom.app N) _ (hb _)).trans (hal _)
  · refine Eq.symm ((chartModProj_comp_apply' B S hS (fp ≫ fq) hpq ΦX N (σpq.hom.app N)
      ((Functor.whiskerLeft ΦX (eqToHom (congrArg (modulePushforward B S hS) hf.symm))).app N)
      V x).trans ?_)
    refine (chartModProj_whiskerLeft_eqToHom_app B S hS fp fq hf hpq hf' ΦX N V
      ((σpq.hom.app N).val.app (op V) x)).trans ?_
    exact congrArg _ (chartModProj_hom_app_of_trans_chartIso B S hS f' hf' σpq τpq hσpq N V x)

/-- The chart readings of the squares of direct images along `q`, `p` and `p ≫ q` compose on
sections: on underlying schemes, this is the reindexing identity
`representedBaseChange_comp_mor`. -/
theorem representedModulePushforwardSquare_chartComp
    (h : representedSpaceMap B S hS p ≫ representedSpaceMap B S hS q =
      representedSpaceMap B S hS (p ≫ q))
    (hpq : yoneda.relativelyRepresentable
      (representedSpaceMap B S hS p ≫ representedSpaceMap B S hS q).hom) :
    PushforwardSquareChartComp B S hS (representedSpaceMap B S hS p) (representedSpaceMap B S hS q)
        (representedSpaceMap B S hS (p ≫ q)) h
      (relativelyRepresentable_yoneda_map B S hS p)
      (relativelyRepresentable_yoneda_map B S hS q) hpq
      (relativelyRepresentable_yoneda_map B S hS (p ≫ q))
      (representedSmallEtaleModuleEquivalence B S hS X).functor
      (representedSmallEtaleModuleEquivalence B S hS Y).functor
      (representedSmallEtaleModuleEquivalence B S hS Z).functor
      (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS p))
      (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS q))
      (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS (p ≫ q)))
      (schemePushforwardCompHom B S hS p q)
      (representedModulePushforwardSquareChartIso B S hS p
          (relativelyRepresentable_yoneda_map B S hS p))
      (representedModulePushforwardSquareChartIso B S hS q
          (relativelyRepresentable_yoneda_map B S hS q))
      (representedModulePushforwardSquareChartIso B S hS (p ≫ q)
          (relativelyRepresentable_yoneda_map B S hS (p ≫ q))) := by
  refine ⟨fun N V x => ?_⟩
  have hV := smallBaseChange_obj_congr h hpq (relativelyRepresentable_yoneda_map B S hS (p ≫ q)) V
  have hmor := representedBaseChange_comp_mor B S hS p q V h hpq hV
  refine Eq.trans ?l ((sheafOfModules_val_map_congr N hmor x).trans ?r)
  case l =>
    refine Eq.trans ?_ (sheafOfModules_val_map_comp4 N
      ((representedSmallEtaleEquivalence B S hS X).functor.map
        (chartBaseChangeCompComparison B S hS (representedSpaceMap B S hS p)
          (representedSpaceMap B S hS q) (relativelyRepresentable_yoneda_map B S hS p)
          (relativelyRepresentable_yoneda_map B S hS q) hpq V))
      ((representedSmallEtaleBaseChangeIso B S hS p
          (relativelyRepresentable_yoneda_map B S hS p)).hom.app
        ((smallBaseChange B S hS (representedSpaceMap B S hS q)
          (relativelyRepresentable_yoneda_map B S hS q)).obj V))
      ((_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) p.left).map
        ((representedSmallEtaleBaseChangeIso B S hS q
          (relativelyRepresentable_yoneda_map B S hS q)).hom.app V))
      ((smallEtaleBaseChange_factoredCompIso (associatedBigEtaleSite B) _ _ _ p.left q.left
        (p.left ≫ q.left) rfl).hom.app ((representedSmallEtaleEquivalence B S hS Z).functor.obj V))
      x).symm
    rfl
  case r =>
    refine (sheafOfModules_val_map_comp2 N
      ((representedSmallEtaleEquivalence B S hS X).functor.map
          (eqToHom hV))
      ((representedSmallEtaleBaseChangeIso B S hS (p ≫ q)
        (relativelyRepresentable_yoneda_map B S hS (p ≫ q))).hom.app V) x).trans ?_
    rfl

/-- **The composition law of the comparison of inverse images along represented morphisms**
(`representedModulePullbackIso`), read through the composition laws of Stacks 03LU and of the
pullbacks along the morphisms of small étale ringed sites. -/
theorem representedModulePullbackIso_hom_comp_of_eq
    (h : representedSpaceMap B S hS p ≫ representedSpaceMap B S hS q =
      representedSpaceMap B S hS (p ≫ q)) :
    Functor.whiskerLeft (modulePullback B S hS (representedSpaceMap B S hS q))
        (representedModulePullbackIso B S hS p (relativelyRepresentable_yoneda_map B S hS p)).hom ≫
        Functor.whiskerRight
            (representedModulePullbackIso B S hS q
            (relativelyRepresentable_yoneda_map B S hS q)).hom
            (SheafOfModules.pullback.{u} (representedSchemeStructureMapRing B S hS p)) ≫
        Functor.whiskerLeft (representedSmallEtaleModuleEquivalence B S hS Z).inverse
            (SmallEtale.smallEtalePullbackCompIso (associatedBigEtaleSite B) p.left q.left).hom =
      Functor.whiskerRight
          ((modulePullbackCompIso B S hS (representedSpaceMap B S hS p)
              (representedSpaceMap B S hS q)).hom ≫
          eqToHom (congrArg (modulePullback B S hS) h))
              (representedSmallEtaleModuleEquivalence B S hS X).inverse ≫
              (representedModulePullbackIso B S hS (p ≫ q)
              (relativelyRepresentable_yoneda_map B S hS (p ≫ q))).hom := by
  have hpq : yoneda.relativelyRepresentable
      (representedSpaceMap B S hS p ≫ representedSpaceMap B S hS q).hom := by
    rw [h]; exact relativelyRepresentable_yoneda_map B S hS (p ≫ q)
  have hL : conjugateEquiv (modulePullbackAdjunction B S hS (representedSpaceMap B S hS (p ≫ q)))
      ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS q)).comp
        (modulePullbackAdjunction B S hS (representedSpaceMap B S hS p)))
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS p)
          (representedSpaceMap B S hS q)).hom ≫ eqToHom (congrArg (modulePullback B S hS) h)) =
        eqToHom (congrArg (modulePushforward B S hS) h.symm) ≫
          (modulePushforwardCompIso B S hS (representedSpaceMap B S hS p)
              (representedSpaceMap B S hS q)).inv := by
    rw [← conjugateEquiv_comp _
        (modulePullbackAdjunction B S hS
            ((representedSpaceMap B S hS p) ≫ (representedSpaceMap B S hS q))) _,
      conjugateEquiv_eqToHom_modulePullback h.symm]
    exact congrArg _ (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _)
  have hE : conjugateEquiv
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (representedSchemeStructureMapRing B S hS (p ≫ q)))
      ((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (representedSchemeStructureMapRing B S hS q)).comp
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (representedSchemeStructureMapRing B S hS p)))
      (SmallEtale.smallEtalePullbackCompIso (associatedBigEtaleSite B) p.left q.left).hom =
      schemePushforwardCompHom B S hS p q := by
    have h0 := SmallEtale.conjugateEquiv_smallEtalePullbackCompIso_inv
        (associatedBigEtaleSite B) p.left q.left
    have h1 := conjugateEquiv_comm
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (representedSchemeStructureMapRing B S hS (p ≫ q)))
      ((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (representedSchemeStructureMapRing B S hS q)).comp
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
            (representedSchemeStructureMapRing B S hS p)))
      (SmallEtale.smallEtalePullbackCompIso (associatedBigEtaleSite B) p.left q.left).inv_hom_id
    simp only [representedSchemeStructureMapRing, Over.comp_left] at h1 ⊢
    rw [h0] at h1
    have h2 : ((SheafOfModules.pushforwardComp.{u}
        (SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B) q.left)
        (SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B) p.left)).hom ≫
        (SmallEtale.smallEtalePushforwardCompIso (associatedBigEtaleSite B) p.left q.left).inv) ≫
        ((SmallEtale.smallEtalePushforwardCompIso (associatedBigEtaleSite B) p.left q.left).hom ≫
        (SheafOfModules.pushforwardComp.{u}
        (SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B) q.left)
        (SmallEtale.smallEtaleStructureMapRing (associatedBigEtaleSite B) p.left)).inv)
        = 𝟙 _ := by simp
    rw [← Category.comp_id (conjugateEquiv _ _ _), ← h2, ← Category.assoc, h1, Category.id_comp]
  refine Stacks.CategoryTheory.SquareComposition.leftAdjointUniq_comp_of_app
      (MX := (Modules.{u, u} B S hS
          (⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩ : AlgebraicSpaces B S hS).1
          (⟨yoneda.obj X, isAlgebraicSpace_yoneda B S hS X⟩ : AlgebraicSpaces B S hS).2))
      (MY := (Modules.{u, u} B S hS
          (⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ : AlgebraicSpaces B S hS).1
          (⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ : AlgebraicSpaces B S hS).2))
      (MZ := (Modules.{u, u} B S hS
          (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ : AlgebraicSpaces B S hS).1
          (⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ : AlgebraicSpaces B S hS).2))
      (representedSmallEtaleModuleEquivalence B S hS X)
      (representedSmallEtaleModuleEquivalence B S hS Y)
      (representedSmallEtaleModuleEquivalence B S hS Z)
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS p))
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS q))
    (modulePullbackAdjunction B S hS (representedSpaceMap B S hS (p ≫ q)))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (representedSchemeStructureMapRing B S hS p))
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (representedSchemeStructureMapRing B S hS q))
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
        (representedSchemeStructureMapRing B S hS (p ≫ q)))
    (representedModulePushforwardSquareIso B S hS p (relativelyRepresentable_yoneda_map B S hS p))
    (representedModulePushforwardSquareIso B S hS q (relativelyRepresentable_yoneda_map B S hS q))
    (representedModulePushforwardSquareIso B S hS (p ≫ q)
        (relativelyRepresentable_yoneda_map B S hS (p ≫ q)))
    (modulePushforwardCompIso B S hS (representedSpaceMap B S hS p) (representedSpaceMap B S hS q))
    _ _ hL _ _ hE
      ?happ
  case happ =>
    intro N
    refine eq_of_heq
        (HEq.trans (by heq_congr)
        (HEq.trans (heq_of_eq
            (pushforwardSquare_comp_generic B S hS (representedSpaceMap B S hS p)
            (representedSpaceMap B S hS q) (representedSpaceMap B S hS (p ≫ q)) h
        (relativelyRepresentable_yoneda_map B S hS p)
        (relativelyRepresentable_yoneda_map B S hS q) hpq
        (relativelyRepresentable_yoneda_map B S hS (p ≫ q))
        (representedSmallEtaleModuleEquivalence B S hS X).functor
        (representedSmallEtaleModuleEquivalence B S hS Y).functor
        (representedSmallEtaleModuleEquivalence B S hS Z).functor
        (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS p))
        (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS q))
        (SheafOfModules.pushforward.{u} (representedSchemeStructureMapRing B S hS (p ≫ q)))
        (schemePushforwardCompHom B S hS p q)
        (representedModulePushforwardSquareIso B S hS p
            (relativelyRepresentable_yoneda_map B S hS p))
        (representedModulePushforwardSquareIso B S hS q
            (relativelyRepresentable_yoneda_map B S hS q))
        (representedModulePushforwardSquareIso B S hS (p ≫ q)
            (relativelyRepresentable_yoneda_map B S hS (p ≫ q)))
        (representedModulePushforwardSquareChartIso B S hS p
            (relativelyRepresentable_yoneda_map B S hS p))
        (representedModulePushforwardSquareChartIso B S hS q
            (relativelyRepresentable_yoneda_map B S hS q))
        (representedModulePushforwardSquareChartIso B S hS (p ≫ q)
            (relativelyRepresentable_yoneda_map B S hS (p ≫ q)))
        (representedModulePushforwardSquareIso_trans_chartIso B S hS p _)
        (representedModulePushforwardSquareIso_trans_chartIso B S hS q _)
        (representedModulePushforwardSquareIso_trans_chartIso B S hS (p ≫ q) _)
        (representedModulePushforwardSquare_chartComp B S hS p q h hpq) N)) (by heq_congr)))

end SquareComp

end AlgebraicGeometry.Space
