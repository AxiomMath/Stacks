module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaLocal
public import StacksFrontier.AlgebraicGeometry.ProjMapCard.RestrictionComparison

/-!
# The target comparison of the relative `θ` of Stacks Tag 01O9, on sections

`…GradedPowerMap.chartTargetHom` compares the target of [Stacks, Tag 01NK]'s `θ` for the datum
induced over an affine open `V` of the base — sections of `(ℒ|_{f^{-1}(V)})^{⊗ n}` on the open
subscheme `f^{-1}(V)` — with the target of the relative `θ` over the chart of `V` — sections of
`ℒ^{⊗ n}` on `T`. This file computes it on sections: it is the inverse of `pullPow`, the passage of
a section of `ℒ^{⊗ n}` over an open of `T` to the open subscheme `f^{-1}(V)` by the pullback unit
and [Stacks, Tag 01CD]'s comparison of the integer powers.

## Main definitions

* `…GradedPowerMap.pullPow`: a section of `ℒ^{⊗ n}` over `O`, read on `f^{-1}(V)`.
* `…GradedPowerMap.targetOpen`, `…GradedPowerMap.sourceOpen`: the two opens the target
  comparison over a chart open `W₁` relates.

## Main results

* `…GradedPowerMap.chartTargetHom_app_pullPow`: **the target comparison undoes `pullPow`.**
* `…GradedPowerMap.pullPow_localMul`, `pullPow_map`, `pullPow_bijective`: `pullPow` is
  multiplicative, natural and bijective over the opens inside `f^{-1}(V)`.
* `…GradedPowerMap.sourceOpen_eq`: the two opens correspond under `f^{-1}(V) ↪ T`; this uses that
  `r_{ℒ,ψ}` lies over `S`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

/-! ### Generic section formulas, with every object a variable -/

section Generic

variable {X : Scheme.{u}}

/-- Two successive restriction maps of a module compose to the restriction map. -/
theorem map_map (M : X.Modules) {U V W : X.Opensᵒᵖ} (a : U ⟶ V) (b : V ⟶ W)
    (c : U ⟶ W) (x : M.presheaf.obj U) :
    M.presheaf.map b (M.presheaf.map a x) = M.presheaf.map c x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact congrArg (fun k => M.presheaf.map k x) (Subsingleton.elim _ _)

/-- Three successive restriction maps of a module compose to the restriction map. -/
theorem map_map3 (M : X.Modules) {U V W Z : X.Opensᵒᵖ} (a : U ⟶ V) (b : V ⟶ W) (c : W ⟶ Z)
    (d : U ⟶ Z) (x : M.presheaf.obj U) :
    M.presheaf.map c (M.presheaf.map b (M.presheaf.map a x)) = M.presheaf.map d x := by
  rw [map_map M a b (a ≫ b), map_map M _ c d]

/-- A restriction map of a module from an open to itself is the identity. -/
theorem map_id_apply (M : X.Modules) {U : X.Opensᵒᵖ} (a : U ⟶ U) (x : M.presheaf.obj U) :
    M.presheaf.map a x = x := by
  rw [Subsingleton.elim a (𝟙 U), M.presheaf.map_id]
  rfl

/-- A morphism of modules commutes with restriction maps, on sections. -/
theorem app_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opensᵒᵖ} (a : U ⟶ V)
    (x : M.presheaf.obj U) :
    φ.app V.unop (M.presheaf.map a x) = N.presheaf.map a (φ.app U.unop x) :=
  congr($(φ.mapPresheaf.naturality a) x)

/-- The adjoint transpose along an open immersion `j`, pushed forward along `g`, on sections. -/
theorem pushforward_homEquiv_app {Y' Y Z : Scheme.{u}} (j : Y' ⟶ Y) [IsOpenImmersion j]
    (g : Y ⟶ Z) {M : Y.Modules} {N : Y'.Modules} (φ : M.restrict j ⟶ N) (W : Z.Opens)
    (x : Γ(M, g ⁻¹ᵁ W)) :
    ((Scheme.Modules.pushforward g).map ((Scheme.Modules.restrictAdjunction j).homEquiv _ _ φ) ≫
        (Scheme.Modules.pushforwardComp j g).hom.app N).app W x =
      φ.app (j ⁻¹ᵁ g ⁻¹ᵁ W) (M.presheaf.map (homOfLE (j.image_preimage_le _)).op x) := by
  simp only [Adjunction.homEquiv_unit, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.pushforwardComp_hom_app_app]
  rfl

/-- The five-factor comparison of restrictions, on sections. -/
theorem restrictComparison_app {P C F T U' : Scheme.{u}} (a : P ⟶ C) (b : C ⟶ F) (c : F ⟶ T)
    (d : P ⟶ U') (e : U' ⟶ T) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    [IsOpenImmersion d] [IsOpenImmersion e] (h : (a ≫ b) ≫ c = d ≫ e)
    {M : F.Modules} {K : T.Modules} (ψ : M ⟶ K.restrict c) (O : P.Opens)
    (x : Γ(M, b ''ᵁ (a ''ᵁ O))) :
    (((Scheme.Modules.restrictFunctorComp a b).app M).inv ≫
        (Scheme.Modules.restrictFunctor (a ≫ b)).map ψ ≫
        ((Scheme.Modules.restrictFunctorComp (a ≫ b) c).app K).inv ≫
        ((Scheme.Modules.restrictFunctorCongr h).app K).hom ≫
        ((Scheme.Modules.restrictFunctorComp d e).app K).hom).app O x =
      K.presheaf.map (eqToHom (show e ''ᵁ (d ''ᵁ O) = c ''ᵁ ((a ≫ b) ''ᵁ O) by
          simp only [← Scheme.Hom.comp_image, h])).op
        (ψ.app ((a ≫ b) ''ᵁ O) (M.presheaf.map (eqToHom (show (a ≫ b) ''ᵁ O = b ''ᵁ (a ''ᵁ O) by
          rw [Scheme.Hom.comp_image])).op x)) := by
  simp only [Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app, Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app, restrictFunctor_map_app', Iso.app_hom,
    Iso.app_inv]
  exact map_map3 K _ _ _ _ _

/-- The restriction maps of a direct image of a restriction are restriction maps. -/
theorem pushforward_restrict_map {Y' Y Z : Scheme.{u}} (j : Y' ⟶ Y) [IsOpenImmersion j]
    (g : Y' ⟶ Z) (M : Y.Modules) {W W' : Z.Opens} (i : W' ⟶ W) (x : Γ(M, j ''ᵁ (g ⁻¹ᵁ W))) :
    ((Scheme.Modules.pushforward g).obj (M.restrict j)).presheaf.map i.op x =
      M.presheaf.map (homOfLE (j.image_mono (g.preimage_mono (leOfHom i)))).op x := rfl

/-- A restriction along an equality of opens is bijective. -/
theorem map_bijective_of_eq (M : X.Modules) {U V : X.Opens} (h : V ≤ U) (e : U = V) :
    Function.Bijective (M.presheaf.map (homOfLE h).op) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨M.presheaf.map (homOfLE (le_of_eq e)).op, fun x => ?_, fun x => ?_⟩
  · exact (map_map M _ _ (𝟙 _) x).trans (map_id_apply M _ x)
  · exact (map_map M _ _ (𝟙 _) x).trans (map_id_apply M _ x)

/-- A round trip through an identification of a restriction, on sections. -/
theorem restrict_iso_round_trip {Y' Y : Scheme.{u}} (j : Y' ⟶ Y) [IsOpenImmersion j]
    {M : Y.Modules} {N : Y'.Modules} (E : M.restrict j ≅ N) {O₀ : Y.Opens} {Oa Ob : Y'.Opens}
    {O₁ O₂ : Y'.Opens} {O' : Y.Opens}
    (d : j ''ᵁ Ob ⟶ O₀) (c : O₁ ⟶ Ob) (b : O₂ ⟶ O₁) (a : Oa ⟶ O₂) (e : O' ⟶ j ''ᵁ Oa)
    (d' : O' ⟶ O₀) (t : Γ(M, O₀)) :
    M.presheaf.map e.op (E.inv.app Oa (N.presheaf.map a.op (N.presheaf.map b.op
      (N.presheaf.map c.op (E.hom.app Ob (M.presheaf.map d.op t)))))) = M.presheaf.map d'.op t := by
  rw [map_map3 N c.op b.op a.op (a ≫ b ≫ c).op]
  rw [show N.presheaf.map (a ≫ b ≫ c).op (E.hom.app Ob (M.presheaf.map d.op t)) =
      E.hom.app Oa ((M.restrict j).presheaf.map (a ≫ b ≫ c).op (M.presheaf.map d.op t)) from
    (app_map E.hom (a ≫ b ≫ c).op _).symm]
  rw [show E.inv.app Oa (E.hom.app Oa ((M.restrict j).presheaf.map (a ≫ b ≫ c).op
      (M.presheaf.map d.op t))) = (M.restrict j).presheaf.map (a ≫ b ≫ c).op
        (M.presheaf.map d.op t) from
    (ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ Oa) E.hom_inv_id)
      _).trans rfl]
  exact map_map3 M d.op _ e.op d'.op t

/-- **The whole target comparison on sections**, with every object a variable: the adjoint
transpose along `a`, pushed forward along `g`, of the five-factor comparison built on an
identification `E` of a restriction, applied to a section that is itself `E` of a restriction,
is a restriction. -/
theorem targetComparison_app {Pc C F T U' Z : Scheme.{u}} (a : Pc ⟶ C) (b : C ⟶ F) (c : F ⟶ T)
    (d : Pc ⟶ U') (e : U' ⟶ T) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    [IsOpenImmersion d] [IsOpenImmersion e] (h : (a ≫ b) ≫ c = d ≫ e) (g : C ⟶ Z)
    {K : T.Modules} {M : F.Modules} (E : K.restrict c ≅ M) (W₁ : Z.Opens)
    {O₀ : T.Opens} {Ob : F.Opens} (k' : c ''ᵁ Ob ⟶ O₀) (k : b ''ᵁ (g ⁻¹ᵁ W₁) ⟶ Ob)
    (k'' : e ''ᵁ (d ''ᵁ (a ⁻¹ᵁ g ⁻¹ᵁ W₁)) ⟶ O₀) (t : Γ(K, O₀)) :
    ((Scheme.Modules.pushforward g).map ((Scheme.Modules.restrictAdjunction a).homEquiv
        (M.restrict b) ((K.restrict e).restrict d)
        (((Scheme.Modules.restrictFunctorComp a b).app M).inv ≫
          (Scheme.Modules.restrictFunctor (a ≫ b)).map E.inv ≫
          ((Scheme.Modules.restrictFunctorComp (a ≫ b) c).app K).inv ≫
          ((Scheme.Modules.restrictFunctorCongr h).app K).hom ≫
          ((Scheme.Modules.restrictFunctorComp d e).app K).hom)) ≫
        (Scheme.Modules.pushforwardComp a g).hom.app ((K.restrict e).restrict d)).app W₁
      (M.presheaf.map k.op (E.hom.app Ob (K.presheaf.map k'.op t))) =
      K.presheaf.map k''.op t := by
  refine (pushforward_homEquiv_app a g _ W₁ _).trans ?_
  refine (restrictComparison_app a b c d e h E.inv _ _).trans ?_
  exact restrict_iso_round_trip c E _ _ _ _ _ _ t

end Generic

namespace GradedPowerMap

attribute [local irreducible] GradedPowerMap.globalMorphism
  Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

/-- A section of `ℒ^{⊗ n}` over an open `O` of `T`, read on the open subscheme `f^{-1}(V)` as a
section of `(ℒ|_{f^{-1}(V)})^{⊗ n}` over `O ∩ f^{-1}(V)`. -/
def pullPow (V : S.Opens) (n : ℤ) (O : T.Opens) (t : Γ(tensorPowerModule T P.L n, O)) :
    Γ(tensorPowerModule (f ⁻¹ᵁ V).toScheme ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L) n,
      (f ⁻¹ᵁ V).ι ⁻¹ᵁ O) :=
  (P.restrictPowIso V n).hom.app ((f ⁻¹ᵁ V).ι ⁻¹ᵁ O)
    ((tensorPowerModule T P.L n).presheaf.map
      (homOfLE ((f ⁻¹ᵁ V).ι.image_preimage_le O)).op t)

/-- If `φ.app W y = e.hom.app W x`, then `(φ ≫ e.inv).app W y = x`. -/
theorem comp_iso_inv_app_eq {X : Scheme.{u}} {M N K : X.Modules} (φ : M ⟶ K) (e : N ≅ K)
    (W : X.Opens) (y : Γ(M, W)) (x : Γ(N, W)) (h : φ.app W y = e.hom.app W x) :
    (φ ≫ e.inv).app W y = x := by
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, h, ← ConcreteCategory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]
  rfl

/-- The open of `T` on which the target comparison over a chart open `W₁` lands. -/
abbrev targetOpen (V : S.Opens) (hV : IsAffineOpen V)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) :
    T.Opens :=
  P.coveringOpen.ι ''ᵁ (P.globalMorphism (relativeProj A) ⁻¹ᵁ
    ((relativeProj A).chart V hV ''ᵁ W₁))

/-- The open of `f^{-1}(V)` on which the source of the target comparison over `W₁` lives. -/
abbrev sourceOpen (V : S.Opens) (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) :
    (f ⁻¹ᵁ V).toScheme.Opens :=
  ((P.affineDatum V).coveringOpen).ι ''ᵁ ((P.affineDatum V).glued ⁻¹ᵁ W₁)

/-- The leg of the piece over `V` followed by the chart is the global morphism on the piece. -/
private theorem chart_pieceLeg_base_eq (V : S.Opens) (hV : IsAffineOpen V)
    (y : (P.toBase ⁻¹ᵁ V).toScheme) :
    ((relativeProj A).chart V hV).base ((P.pieceLeg V hV).base y) =
      (P.globalMorphism (relativeProj A)).base ((P.toBase ⁻¹ᵁ V).ι.base y) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    P.pieceLeg_comp_chart (relativeProj A) ⟨V, hV⟩]

/-- A point of the piece over `V` whose leg lands in `W₁` lies over the target open. -/
theorem mem_targetOpen (V : S.Opens) (hV : IsAffineOpen V)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) (y : (P.toBase ⁻¹ᵁ V).toScheme)
    (hy : (P.pieceLeg V hV).base y ∈ W₁) :
    P.coveringOpen.ι.base ((P.toBase ⁻¹ᵁ V).ι.base y) ∈ P.targetOpen V hV W₁ := by
  refine ⟨(P.toBase ⁻¹ᵁ V).ι.base y, ?_, rfl⟩
  show (P.globalMorphism (relativeProj A)).base ((P.toBase ⁻¹ᵁ V).ι.base y) ∈
    ((relativeProj A).chart V hV ''ᵁ W₁)
  rw [← P.chart_pieceLeg_base_eq V hV y]
  exact ⟨_, hy, rfl⟩

/-- The source open over `W₁` lies in the preimage of the target open in `f^{-1}(V)`. -/
theorem sourceOpen_le (V : S.Opens) (hV : IsAffineOpen V)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) :
    P.sourceOpen V W₁ ≤ (f ⁻¹ᵁ V).ι ⁻¹ᵁ P.targetOpen V hV W₁ := by
  rintro _ ⟨z, hz, rfl⟩
  have hz' : (P.pieceIso V hV).hom.base ((P.pieceIso V hV).inv.base z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
  have h : (f ⁻¹ᵁ V).ι.base (((P.affineDatum V).coveringOpen).ι.base z) =
      P.coveringOpen.ι.base ((P.toBase ⁻¹ᵁ V).ι.base ((P.pieceIso V hV).inv.base z)) := by
    have key := congrArg (fun φ => φ.base ((P.pieceIso V hV).inv.base z))
      (P.pieceIso_comp_ι V hV)
    simp only [Scheme.Hom.comp_apply, hz'] at key
    exact key
  show (f ⁻¹ᵁ V).ι.base (((P.affineDatum V).coveringOpen).ι.base z) ∈ P.targetOpen V hV W₁
  rw [h]
  refine P.mem_targetOpen V hV W₁ _ ?_
  show (P.affineDatum V).glued.base ((P.pieceIso V hV).hom.base _) ∈ W₁
  rw [hz']
  exact hz

/-- The image in `T` of the part of the piece over `V` whose leg lands in `W₁` lies in the target
open. -/
theorem pieceImage_le_targetOpen (V : S.Opens) (hV : IsAffineOpen V)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) :
    P.coveringOpen.ι ''ᵁ ((P.toBase ⁻¹ᵁ V).ι ''ᵁ
      ((P.pieceIso V hV).hom ⁻¹ᵁ (P.affineDatum V).glued ⁻¹ᵁ W₁)) ≤ P.targetOpen V hV W₁ := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact P.mem_targetOpen V hV W₁ y hy

/-- **The target comparison undoes `pullPow`**: on the restriction of `pullPow` of a section `t`
over the target open to the source open, the target comparison over `W₁` returns `t`. -/
theorem chartTargetHom_app_pullPow (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens)
    (t : Γ(tensorPowerModule T P.L n, P.targetOpen V hV W₁)) :
    (P.chartTargetHom V hV n).app W₁
      ((tensorPowerModule (f ⁻¹ᵁ V).toScheme
          ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L) n).presheaf.map
        (homOfLE (P.sourceOpen_le V hV W₁)).op (P.pullPow V n _ t)) = t := by
  have key := comp_iso_inv_app_eq
    ((Scheme.Modules.pushforward (P.affineDatum V).glued).map (P.pieceTargetAdj V hV n) ≫
      (Scheme.Modules.pushforwardComp (P.pieceIso V hV).hom (P.affineDatum V).glued).hom.app
        ((P.powK n).restrict (P.toBase ⁻¹ᵁ V).ι))
    (P.chartBaseChangeIso V hV n) W₁ ((tensorPowerModule (f ⁻¹ᵁ V).toScheme
          ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L) n).presheaf.map
        (homOfLE (P.sourceOpen_le V hV W₁)).op (P.pullPow V n _ t)) t
  rw [Category.assoc] at key
  refine key (Eq.trans ?_ (ConcreteCategory.congr_hom (baseChange_app ((relativeProj A).chart V hV)
    (P.globalMorphism (relativeProj A)) (P.toBase ⁻¹ᵁ V).ι (P.pieceLeg V hV)
    (P.pieceLeg_comp_chart (relativeProj A) ⟨V, hV⟩) (P.powK n) W₁) t).symm)
  unfold pieceTargetAdj pieceTargetHom
  exact targetComparison_app (P.pieceIso V hV).hom ((P.affineDatum V).coveringOpen).ι
    (f ⁻¹ᵁ V).ι (P.toBase ⁻¹ᵁ V).ι P.coveringOpen.ι (P.pieceIso_ι_ι V hV)
    (P.affineDatum V).glued (P.restrictPowIso V n) W₁ (O₀ := P.targetOpen V hV W₁)
    (Ob := (f ⁻¹ᵁ V).ι ⁻¹ᵁ P.targetOpen V hV W₁)
    (homOfLE ((f ⁻¹ᵁ V).ι.image_preimage_le _)) (homOfLE (P.sourceOpen_le V hV W₁))
    (homOfLE (P.pieceImage_le_targetOpen V hV W₁)) t

/-! ### `pullPow`: restriction to the open subscheme `f^{-1}(V)` on sections -/

/-- `pullPow` is the pullback unit followed by [Stacks, Tag 01CD]'s comparison of the integer
powers. -/
theorem pullPow_eq (V : S.Opens) (n : ℤ) (O : T.Opens) (t : Γ(tensorPowerModule T P.L n, O)) :
    P.pullPow V n O t =
      PresheafOfModules.Hom.app (Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.intPullIso
          (f ⁻¹ᵁ V).ι P.L n).hom.val
        ((RingedSpaceModuleAdjunction.opensMap (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).op.obj (op O))
        (Stacks.RingedSpace.pullbackUnit (f ⁻¹ᵁ V).ι.toLRSHom.toShHom
          (tensorPowerModule T P.L n) (op O) t) := by
  refine Eq.trans ?_ (congrArg (fun z => PresheafOfModules.Hom.app
    (Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.intPullIso (f ⁻¹ᵁ V).ι P.L n).hom.val
      ((RingedSpaceModuleAdjunction.opensMap (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).op.obj (op O)) z)
    (Stacks.AlgebraicGeometry.ProjMapCard.pullbackUnit_eq_restrictFunctorIsoPullback
      (f ⁻¹ᵁ V).ι (tensorPowerModule T P.L n) O t)).symm
  rfl

/-- **`pullPow` is multiplicative.** -/
theorem pullPow_localMul (V : S.Opens) (i j : ℤ) (O : T.Opens)
    (a : Γ(tensorPowerModule T P.L i, O)) (b : Γ(tensorPowerModule T P.L j, O)) :
    P.pullPow V (i + j) O (Stacks.TensorPowerDivision.localMul P.L a b) =
      Stacks.TensorPowerDivision.localMul ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L)
        (P.pullPow V i O a) (P.pullPow V j O b) :=
  (P.pullPow_eq V (i + j) O _).trans
    ((ProjChartRatioPullbackLocalMul.pullbackIntPowIso_pullbackUnit_localMul
      (f ⁻¹ᵁ V).ι P.L i j O a b).trans
      (congrArg₂ (Stacks.TensorPowerDivision.localMul
          ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L))
        (P.pullPow_eq V i O a).symm (P.pullPow_eq V j O b).symm))

/-- **`pullPow` commutes with restriction.** -/
theorem pullPow_map (V : S.Opens) (n : ℤ) {O O' : T.Opens} (hO : O' ≤ O)
    (t : Γ(tensorPowerModule T P.L n, O)) :
    P.pullPow V n O' ((tensorPowerModule T P.L n).presheaf.map (homOfLE hO).op t) =
      (tensorPowerModule (f ⁻¹ᵁ V).toScheme ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L)
          n).presheaf.map (homOfLE ((f ⁻¹ᵁ V).ι.preimage_mono hO)).op (P.pullPow V n O t) := by
  have hle : (f ⁻¹ᵁ V).ι ''ᵁ ((f ⁻¹ᵁ V).ι ⁻¹ᵁ O') ≤ O :=
    ((f ⁻¹ᵁ V).ι.image_preimage_le O').trans hO
  have h1 : (tensorPowerModule T P.L n).presheaf.map
      ((f ⁻¹ᵁ V).ι.opensFunctor.map (homOfLE ((f ⁻¹ᵁ V).ι.preimage_mono hO))).op
      ((tensorPowerModule T P.L n).presheaf.map
        (homOfLE ((f ⁻¹ᵁ V).ι.image_preimage_le O)).op t) =
      (tensorPowerModule T P.L n).presheaf.map (homOfLE hle).op t :=
    map_map _ _ _ _ t
  have h2 : (tensorPowerModule T P.L n).presheaf.map
      (homOfLE ((f ⁻¹ᵁ V).ι.image_preimage_le O')).op
      ((tensorPowerModule T P.L n).presheaf.map (homOfLE hO).op t) =
      (tensorPowerModule T P.L n).presheaf.map (homOfLE hle).op t :=
    map_map _ _ _ _ t
  have h3 := app_map (P.restrictPowIso V n).hom (homOfLE ((f ⁻¹ᵁ V).ι.preimage_mono hO)).op
    ((tensorPowerModule T P.L n).presheaf.map (homOfLE ((f ⁻¹ᵁ V).ι.image_preimage_le O)).op t)
  refine Eq.trans ?_ h3
  exact congrArg (fun z => (P.restrictPowIso V n).hom.app ((f ⁻¹ᵁ V).ι ⁻¹ᵁ O') z)
    (h2.trans h1.symm)

/-- `pullPow` is bijective on the opens inside `f^{-1}(V)`. -/
private theorem pullPow_bijective_of_le (V : S.Opens) (n : ℤ) {O : T.Opens} (hO : O ≤ f ⁻¹ᵁ V) :
    Function.Bijective (P.pullPow V n O) := by
  have e : O = (f ⁻¹ᵁ V).ι ''ᵁ ((f ⁻¹ᵁ V).ι ⁻¹ᵁ O) :=
    ((f ⁻¹ᵁ V).ι.image_preimage_eq_opensRange_inf O |>.trans
      (by rw [Scheme.Opens.opensRange_ι]; exact inf_eq_right.mpr hO)).symm
  exact (ConcreteCategory.bijective_of_isIso
    ((P.restrictPowIso V n).hom.app ((f ⁻¹ᵁ V).ι ⁻¹ᵁ O))).comp
      (map_bijective_of_eq _ _ e)

/-- **`pullPow` is injective on the opens inside `f^{-1}(V)`.** -/
theorem pullPow_injective (V : S.Opens) (n : ℤ) {O : T.Opens} (hO : O ≤ f ⁻¹ᵁ V) :
    Function.Injective (P.pullPow V n O) :=
  (P.pullPow_bijective_of_le V n hO).injective

/-! ### The target open is the piece's chart open -/

/-- A point of `U(ψ)` whose image under `r_{ℒ,ψ}` lies over `V` lies in the piece over `V`. -/
theorem exists_piece_of_mem (V : S.Opens) (hV : IsAffineOpen V) (y : P.coveringOpen.toScheme)
    (hy : (P.globalMorphism (relativeProj A)).base y ∈ ((relativeProj A).chart V hV).opensRange) :
    ∃ p : (P.toBase ⁻¹ᵁ V).toScheme, (P.toBase ⁻¹ᵁ V).ι.base p = y :=
  P.preimage_chart_opensRange_le V hV hy

/-- The target open over a chart open `W₁` lies in `f^{-1}(V)`. -/
theorem targetOpen_le (V : S.Opens) (hV : IsAffineOpen V)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) :
    P.targetOpen V hV W₁ ≤ f ⁻¹ᵁ V := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨p, rfl⟩ := P.exists_piece_of_mem V hV y (by
    obtain ⟨w, -, hw⟩ := hy
    exact ⟨w, hw⟩)
  show (P.coveringOpen.ι ≫ f).base ((P.toBase ⁻¹ᵁ V).ι.base p) ∈ V
  exact p.2

/-- The preimage of the target open in `f^{-1}(V)` lies in the source open. -/
theorem preimage_targetOpen_le (V : S.Opens) (hV : IsAffineOpen V)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) :
    (f ⁻¹ᵁ V).ι ⁻¹ᵁ P.targetOpen V hV W₁ ≤ P.sourceOpen V W₁ := by
  rintro x ⟨y, hy, hxy⟩
  obtain ⟨p, rfl⟩ := P.exists_piece_of_mem V hV y (by
    obtain ⟨w, -, hw⟩ := hy
    exact ⟨w, hw⟩)
  have hleg : (P.pieceLeg V hV).base p ∈ W₁ := by
    obtain ⟨w, hw, hw'⟩ := hy
    rw [← (relativeProj A).chart V hV |>.isOpenEmbedding.injective
      (hw'.trans (P.chart_pieceLeg_base_eq V hV p).symm)]
    exact hw
  refine ⟨(P.pieceIso V hV).hom.base p, hleg, ?_⟩
  apply (f ⁻¹ᵁ V).ι.isOpenEmbedding.injective
  have key := congrArg (fun φ => φ.base p) (P.pieceIso_comp_ι V hV)
  simp only [Scheme.Hom.comp_apply] at key
  exact key.trans hxy

/-- The source open is the preimage of the target open under `f^{-1}(V) ↪ T`. -/
theorem sourceOpen_eq (V : S.Opens) (hV : IsAffineOpen V)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) :
    P.sourceOpen V W₁ = (f ⁻¹ᵁ V).ι ⁻¹ᵁ P.targetOpen V hV W₁ :=
  le_antisymm (P.sourceOpen_le V hV W₁) (P.preimage_targetOpen_le V hV W₁)

/-- **`pullPow` is bijective on the opens inside `f^{-1}(V)`.** -/
theorem pullPow_bijective (V : S.Opens) (n : ℤ) {O : T.Opens} (hO : O ≤ f ⁻¹ᵁ V) :
    Function.Bijective (P.pullPow V n O) :=
  P.pullPow_bijective_of_le V n hO

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
