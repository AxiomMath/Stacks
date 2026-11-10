module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiChartClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiClosedSubspaceIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiKernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiKernelRepresented

/-!
# Reading kernels along represented morphisms (Stacks 085L)

The kernel of an adjoint along a morphism `τ` of representable algebraic spaces, at the self-open
of a Zariski open, is read on the pulled-back sections of the scheme: the reading of the map
applied to the pulled-back section vanishes.  For the unit of `τ^* ⊣ τ_*` this says that the unit
kills a section exactly when its pullback along the morphism of schemes vanishes.  These are the
represented steps of the chart dictionary of Stacks 085L for the kernel of
`𝒜_n ⟶ π_*i_*i^*𝒪_P(n)`, together with the chart square of a closed subspace of `P` over the
atlas.

## Main results

* `AlgebraicGeometry.Space.C1359Bridge.homEquiv_val_app_selfOpens_eq_zero_iff_pullbackSection`.
* `AlgebraicGeometry.Space.C1359Bridge.unit_val_app_selfOpens_eq_zero_iff_pullbackSection`.
* `AlgebraicGeometry.Space.C1359Bridge.pullback_map_comp_pullbackReadingHom_comp`.
* `AlgebraicGeometry.Space.C1359Bridge.unit_reading_val_app_eq_zero_iff_pullbackSection`.
* `AlgebraicGeometry.Space.C1359Bridge.isPullback_closedSubspaceChart`.
* `AlgebraicGeometry.Space.C1359Bridge.homEquiv_comp_unit_val_app_etalePointChart_eq_zero_iff`:
  the chart dictionary on representables, for any `c : P_U ⟶ P` over the atlas along which `ψ`
  has the chart property: the adjoint of `ψ ≫ η_i` kills the reading of a section over a chart
  `W ⟶ U ⟶ X` exactly when the scheme map `Ψ` kills its pullback on `Z ×_P P_U`.

## References

* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space.C1359Bridge

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T T' : BigFppfOver B S hS}
  (τ : T' ⟶ T)

/-- `AlgebraicGeometry.Space.C1359Bridge.homEquiv_comp_unit_val_app_etaleChart_eq_zero_iff` with
the commutativity of the square passed separately. -/
theorem homEquiv_comp_unit_val_app_etaleChart_eq_zero_iff_of_comm
    {X P Z U P' Z' : AlgebraicSpaces B S hS}
    (π : P ⟶ X) (i : Z ⟶ P) (g : U ⟶ X) (c : P' ⟶ P) (f' : P' ⟶ U) (cZ : Z' ⟶ Z) (j : Z' ⟶ P')
    (sq : IsPullback c f' π g) (comm : c ≫ π = f' ≫ g) (sqZ : IsPullback cZ j i c)
    (hg : IsEtale B S hS g.hom)
    (hc : IsEtale B S hS c.hom) {F : Modules.{u, u} B S hS X.1 X.2}
    {K : Modules.{u, u} B S hS P.1 P.2} (ψ : (modulePullback B S hS π).obj F ⟶ K)
    (V : SmallEtale B S hS U.1) (x : ((modulePullback B S hS g).obj F).val.obj (op V)) :
    ((modulePullbackAdjunction B S hS π).homEquiv F _
        (ψ ≫ (modulePullbackAdjunction B S hS i).unit.app K)).val.app
        (op ((smallEtalePostcomp B S hS g hg).obj V))
        (((modulePullbackIsoEtaleModulePullback B S hS g hg).app F).hom.val.app (op V) x) = 0 ↔
      ((modulePullbackAdjunction B S hS f').homEquiv ((modulePullback B S hS g).obj F)
        ((modulePushforward B S hS j).obj ((modulePullback B S hS j).obj
          ((modulePullback B S hS c).obj K)))
        ((modulePullbackSquareComparison π g f' c comm).inv.app F ≫
          (modulePullback B S hS c).map ψ ≫
            (modulePullbackAdjunction B S hS j).unit.app
              ((modulePullback B S hS c).obj K))).val.app (op V) x = 0 := by
  rw [show comm = sq.w from rfl]
  exact homEquiv_comp_unit_val_app_etaleChart_eq_zero_iff π i g c f' cZ j sq sqZ hg hc ψ V x

/-- **The reading of the inverse image along a morphism of representable algebraic spaces**: the
pullback along the morphism of schemes of the Zariski reading of `N`, identified with the Zariski
reading of `τ^*N` through the base identifications and the comparison of Stacks 03LU. -/
def pullbackReadingHom
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    (Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).obj
        ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N) ⟶
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).obj
        ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N) :=
  (Stacks.RingedSpace.pullbackFunctor
      (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
      ((zariskiReadingIso T).app N).inv ≫
    ((_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso
        (associatedBigEtaleSite B) τ.left
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj N)
        (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T N hN)).hom ≫
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).map
        ((representedModulePullbackIso B S hS τ
          (relativelyRepresentable_yoneda_map B S hS τ)).inv.app N) ≫
      (zariskiReadingIso T').hom.app
        ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N))

/-- **The kernel of an adjoint along a morphism of representable algebraic spaces, on
pulled-back sections.**  A section `x` of `N` over the self-open of a Zariski open `W` is killed
by the adjoint of `v : τ^*N ⟶ H` exactly when the reading of `v` kills the pullback of `x` along
the morphism of schemes, read through `pullbackReadingHom`. -/
theorem homEquiv_val_app_selfOpens_eq_zero_iff_pullbackSection
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite)
    {H : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')}
    (v : (modulePullback B S hS (representedSpaceMap B S hS τ)).obj N ⟶ H)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (x : N.val.obj (op ((selfOpensFunctor B S hS T).obj W))) :
    ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS τ)).homEquiv N H v).val.app
        (op ((selfOpensFunctor B S hS T).obj W)) x = 0 ↔
      (pullbackReadingHom τ N hN ≫
        (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map v).val.app
          (op ((BigFppfOver.toScheme B S hS).map τ ⁻¹ᵁ W))
          (Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map τ)
            ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N) W
            ((BigFppfOver.toScheme B S hS).map τ ⁻¹ᵁ W) le_rfl x) = 0 := by
  refine (homEquiv_val_app_selfOpens_eq_zero_iff τ N hN v W x).trans ?_
  exact homEquiv_val_app_eq_zero_iff_pullbackSection ((BigFppfOver.toScheme B S hS).map τ) _ _
    (pullbackReadingHom τ N hN ≫
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map v) W x


/-- `AlgebraicGeometry.Space.C1359Bridge.homEquiv_val_app_selfOpens_eq_zero_iff_pullbackSection`
with the pulled-back section taken over any open `V` equal to `τ⁻¹(W)`. -/
theorem homEquiv_val_app_selfOpens_eq_zero_iff_pullbackSection'
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite)
    {H : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')}
    (v : (modulePullback B S hS (representedSpaceMap B S hS τ)).obj N ⟶ H)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (V : ((BigFppfOver.toScheme B S hS).obj T').Opens)
    (hV : V = (BigFppfOver.toScheme B S hS).map τ ⁻¹ᵁ W)
    (hV' : V ≤ (BigFppfOver.toScheme B S hS).map τ ⁻¹ᵁ W)
    (x : N.val.obj (op ((selfOpensFunctor B S hS T).obj W))) :
    ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS τ)).homEquiv N H v).val.app
        (op ((selfOpensFunctor B S hS T).obj W)) x = 0 ↔
      (pullbackReadingHom τ N hN ≫
        (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map v).val.app (op V)
          (Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map τ)
            ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N) W V hV' x) =
        0 := by
  subst hV
  exact homEquiv_val_app_selfOpens_eq_zero_iff_pullbackSection τ N hN v W x

/-- A composite of four isomorphisms of sheaves of modules kills a section exactly when the section
is zero. -/
theorem sheafOfModules_iso_comp4_val_app_eq_zero_iff {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M₀ M₁ M₂ M₃ M₄ : SheafOfModules.{u} R}
    (e₁ : M₀ ≅ M₁) (e₂ : M₁ ≅ M₂) (e₃ : M₂ ≅ M₃) (e₄ : M₃ ≅ M₄) (W : Cᵒᵖ) (x : M₀.val.obj W) :
    (e₁.hom ≫ e₂.hom ≫ e₃.hom ≫ e₄.hom).val.app W x = 0 ↔ x = 0 := by
  rw [← Iso.trans_hom, ← Iso.trans_hom, ← Iso.trans_hom]
  exact sheafOfModules_comp_iso_hom_val_app_eq_zero_iff (𝟙 M₀) (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄) W x

/-- The reading of the inverse image kills a section exactly when the section is zero. -/
theorem pullbackReadingHom_val_app_eq_zero_iff
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) (V : ((BigFppfOver.toScheme B S hS).obj T').Opens)
    (y : ((Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).obj
        ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N)).val.obj
          (op V)) :
    (pullbackReadingHom τ N hN).val.app (op V) y = 0 ↔ y = 0 :=
  sheafOfModules_iso_comp4_val_app_eq_zero_iff
    ((Stacks.RingedSpace.pullbackFunctor
      (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).mapIso
      ((zariskiReadingIso T).app N).symm)
    (_root_.AlgebraicGeometry.SmallEtale.restrictModulePullbackObjIso
        (associatedBigEtaleSite B) τ.left
        ((representedSmallEtaleModuleEquivalence B S hS T).inverse.obj N)
        (isQuasicoherentOnSite_representedSmallEtaleInverse B S hS T N hN))
    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).mapIso
        ((representedModulePullbackIso B S hS τ
          (relativelyRepresentable_yoneda_map B S hS τ)).app N).symm)
    ((zariskiReadingIso T').app
        ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N)) (op V) y

/-- An isomorphism of sheaves of modules kills a section exactly when the section is zero. -/
theorem sheafOfModules_isIso_val_app_eq_zero_iff {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M H : SheafOfModules.{u} R}
    (e : M ⟶ H) [IsIso e] (W : Cᵒᵖ) (x : M.val.obj W) : e.val.app W x = 0 ↔ x = 0 :=
  sheafOfModules_comp_isIso_val_app_eq_zero_iff (𝟙 M) e W x

/-- **The unit of `τ^* ⊣ τ_*` on sections over a self-open.**  The unit kills a section `x` of `N`
over the self-open of `W` exactly when the pullback of `x` along the morphism of schemes vanishes,
over any open `V` equal to `τ⁻¹(W)`. -/
theorem unit_val_app_selfOpens_eq_zero_iff_pullbackSection
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (V : ((BigFppfOver.toScheme B S hS).obj T').Opens)
    (hV : V = (BigFppfOver.toScheme B S hS).map τ ⁻¹ᵁ W)
    (hV' : V ≤ (BigFppfOver.toScheme B S hS).map τ ⁻¹ᵁ W)
    (x : N.val.obj (op ((selfOpensFunctor B S hS T).obj W))) :
    ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS τ)).unit.app N).val.app
        (op ((selfOpensFunctor B S hS T).obj W)) x = 0 ↔
      Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map τ)
            ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N) W V hV' x =
        0 := by
  have h := homEquiv_val_app_selfOpens_eq_zero_iff_pullbackSection' τ N hN (𝟙 _) W V hV hV' x
  rw [Adjunction.homEquiv_id] at h
  exact h.trans (pullbackReadingHom_val_app_eq_zero_iff τ N hN V _)


/-- In any category, given the factorizations `hP`, `hM` and the commutativity relations `hB`,
`h5`, `hN`, the composite `a ≫ Pr ≫ Mv` equals `Ψ ≫ ρ'' ≫ z₃ ≫ U`. -/
private theorem paste_reading {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ Y₁ Y₂ Y₃ : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (R : X₂ ⟶ X₃)
    (z : X₃ ⟶ X₄) (Pr : X₁ ⟶ X₄) (hP : Pr = b ≫ R ≫ z) (Mv : X₄ ⟶ X₇) (M : X₄ ⟶ X₅)
    (E : X₅ ⟶ X₆) (U : X₆ ⟶ X₇) (hM : Mv = M ≫ E ≫ U) (r : X₂ ⟶ X₀) (ρ' : X₀ ⟶ Y₁)
    (z₂ : Y₁ ⟶ X₅) (Ψ : X₀ ⟶ Y₂) (ρ'' : Y₂ ⟶ Y₃) (z₃ : Y₃ ⟶ X₆)
    (hB : R ≫ z ≫ M = r ≫ ρ' ≫ z₂) (h5 : a ≫ b ≫ r = 𝟙 X₀) (hN : ρ' ≫ z₂ ≫ E = Ψ ≫ ρ'' ≫ z₃) :
    a ≫ Pr ≫ Mv = Ψ ≫ ρ'' ≫ z₃ ≫ U := by
  subst hP hM
  calc a ≫ (b ≫ R ≫ z) ≫ M ≫ E ≫ U = a ≫ b ≫ (R ≫ z ≫ M) ≫ E ≫ U := by
        simp only [Category.assoc]
    _ = (a ≫ b ≫ r) ≫ (ρ' ≫ z₂ ≫ E) ≫ U := by rw [hB]; simp only [Category.assoc]
    _ = Ψ ≫ ρ'' ≫ z₃ ≫ U := by rw [h5, hN]; simp only [Category.id_comp, Category.assoc]

variable {T'' : BigFppfOver B S hS} (j : T'' ⟶ T')

/-- **The reading of `τ^*(N) ⟶ (N_Zar)^a`-transported maps.**  For `N` quasi-coherent on
`yoneda.obj T`, `M₁ = N_{Zar}`, a map `Ψ : τ^*M₁ ⟶ M₂` of modules on the scheme of `T'` and
`j : T'' ⟶ T'`, the pullback of the Zariski reading of `N ≅ (M₁)^a`, followed by the reading of the
inverse image and the reading of `τ^*(M₁^a) ≅ (τ^*M₁)^a ⟶ M₂^a ⟶ j_*j^*(M₂^a)`, is `Ψ` followed by
the base identification of `M₂` and the reading of the unit of `j`. -/
theorem pullback_map_comp_pullbackReadingHom_comp
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite)
    (M₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf).FullSubcategory)
    (Ψ : quasicoherentPullbackObj B S hS τ (zariskiReadingQcoh T N hN) ⟶ M₂) :
    (Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
        ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
          (zariskiReadingQuasicoherentIso T N hN).hom) ≫
      pullbackReadingHom τ
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
          (zariskiReadingQcoh T N hN)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
          (zariskiReadingQcoh T N hN)).property ≫
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map
        ((modulePullbackRepresentedQuasicoherentIso B S hS τ (zariskiReadingQcoh T N hN)).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS T').functor.map Ψ).hom ≫
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS j)).unit.app
            ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj) =
    Ψ.hom ≫ (representedZariskiModuleQuasicoherentSchemeIso B S hS T' M₂).inv ≫
      (zariskiReadingIso T').hom.app
        ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj ≫
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map
        ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS j)).unit.app
          ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj) := by
  have hB := congrArg Iso.hom
    (representedZariskiModulePullbackIso_trans_zariskiReadingIso_trans_mapIso τ
      (zariskiReadingQcoh T N hN))
  simp only [Iso.trans_hom, Iso.symm_hom] at hB
  have h5 := pushforward_map_zariskiReadingQuasicoherentIso_hom_comp T N hN
  have h5' := ((congrArg (_ ≫ ·) ((Stacks.RingedSpace.pullbackFunctor
      (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map_comp _ _).symm).trans
    ((Stacks.RingedSpace.pullbackFunctor
      (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map_comp _ _).symm).trans
    ((congrArg (Stacks.RingedSpace.pullbackFunctor
      (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map h5).trans
    ((Stacks.RingedSpace.pullbackFunctor
      (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map_id _))
  have hN₁ := representedZariskiModuleQuasicoherentSchemeIso_naturality B S hS Ψ
  have hN₂ := (zariskiReadingIso T').hom.naturality
    ((representedQuasicoherentSchemeEquivalence B S hS T').functor.map Ψ).hom
  refine paste_reading _ _ _ _ _ rfl _ _ _ _
    (((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map_comp _ _).trans
      (congrArg (_ ≫ ·) ((SheafOfModules.pushforward.{u}
        (selfOpensStructureMap B S hS T')).map_comp _ _))) _ _ _ _ _ _
    hB h5' ?_
  exact (congrArg (_ ≫ ·) hN₂.symm).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hN₁.symm).trans (Category.assoc _ _ _)))


/-- `AlgebraicGeometry.Space.C1359Bridge.pullback_map_comp_pullbackReadingHom_comp` on the
pullback of a section `x` of `N` over the self-open of `W`: the reading of `τ^*(M₁^a) ⟶ j_*j^*M₂^a`
applied to the pullback of the image of `x` in `M₁^a` is the reading of `Ψ` followed by the unit of
`j`, applied to the pullback of `x`. -/
theorem pullbackReadingHom_comp_val_app_pullbackSection
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite)
    (M₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf).FullSubcategory)
    (Ψ : quasicoherentPullbackObj B S hS τ (zariskiReadingQcoh T N hN) ⟶ M₂)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (V : ((BigFppfOver.toScheme B S hS).obj T').Opens)
    (hV' : V ≤ (BigFppfOver.toScheme B S hS).map τ ⁻¹ᵁ W)
    (x : N.val.obj (op ((selfOpensFunctor B S hS T).obj W))) :
    (pullbackReadingHom τ
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
          (zariskiReadingQcoh T N hN)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
          (zariskiReadingQcoh T N hN)).property ≫
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map
        ((modulePullbackRepresentedQuasicoherentIso B S hS τ (zariskiReadingQcoh T N hN)).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS T').functor.map Ψ).hom ≫
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS j)).unit.app
            ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj)).val.app
        (op V)
        (Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map τ)
          ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj
            ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
              (zariskiReadingQcoh T N hN)).obj) W V hV'
          ((zariskiReadingQuasicoherentIso T N hN).hom.val.app
            (op ((selfOpensFunctor B S hS T).obj W)) x)) =
    (Ψ.hom ≫ (representedZariskiModuleQuasicoherentSchemeIso B S hS T' M₂).inv ≫
      (zariskiReadingIso T').hom.app
        ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj ≫
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map
        ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS j)).unit.app
          ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj)).val.app
        (op V)
        (Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map τ)
          ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N) W V hV' x) :=
  (congrArg (fun y => (pullbackReadingHom τ
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
          (zariskiReadingQcoh T N hN)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
          (zariskiReadingQcoh T N hN)).property ≫
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map
        ((modulePullbackRepresentedQuasicoherentIso B S hS τ (zariskiReadingQcoh T N hN)).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS T').functor.map Ψ).hom ≫
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS j)).unit.app
            ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj)).val.app
        (op V) y)
    (Scheme.Modules.pullbackSection_naturality ((BigFppfOver.toScheme B S hS).map τ)
      ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).map
        (zariskiReadingQuasicoherentIso T N hN).hom) W V hV' x).symm).trans
    (congrArg (fun φ => φ.val.app (op V)
        (Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map τ)
          ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N) W V hV' x))
      (pullback_map_comp_pullbackReadingHom_comp τ j N hN M₂ Ψ))

/-- `AlgebraicGeometry.Space.C1359Bridge.pullbackReadingHom_comp_val_app_pullbackSection`, as
an equivalence of vanishing statements. -/
theorem pullbackReadingHom_comp_val_app_pullbackSection_eq_zero_iff
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite)
    (M₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf).FullSubcategory)
    (Ψ : quasicoherentPullbackObj B S hS τ (zariskiReadingQcoh T N hN) ⟶ M₂)
    (W : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (V : ((BigFppfOver.toScheme B S hS).obj T').Opens)
    (hV' : V ≤ (BigFppfOver.toScheme B S hS).map τ ⁻¹ᵁ W)
    (x : N.val.obj (op ((selfOpensFunctor B S hS T).obj W))) :
    (pullbackReadingHom τ
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
          (zariskiReadingQcoh T N hN)).obj
        ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
          (zariskiReadingQcoh T N hN)).property ≫
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map
        ((modulePullbackRepresentedQuasicoherentIso B S hS τ (zariskiReadingQcoh T N hN)).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS T').functor.map Ψ).hom ≫
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS j)).unit.app
            ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj)).val.app
        (op V)
        (Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map τ)
          ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj
            ((representedQuasicoherentSchemeEquivalence B S hS T).functor.obj
              (zariskiReadingQcoh T N hN)).obj) W V hV'
          ((zariskiReadingQuasicoherentIso T N hN).hom.val.app
            (op ((selfOpensFunctor B S hS T).obj W)) x)) = 0 ↔
    (Ψ.hom ≫ (representedZariskiModuleQuasicoherentSchemeIso B S hS T' M₂).inv ≫
      (zariskiReadingIso T').hom.app
        ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj ≫
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map
        ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS j)).unit.app
          ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj)).val.app
        (op V)
        (Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map τ)
          ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T)).obj N) W V hV' x) =
      0 :=
  Eq.to_iff (congrArg (· = 0)
    (pullbackReadingHom_comp_val_app_pullbackSection τ j N hN M₂ Ψ W V hV' x))

/-- An isomorphism of sheaves of modules kills a section exactly when the section is zero. -/
theorem sheafOfModules_iso_hom_val_app_eq_zero_iff {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M H : SheafOfModules.{u} R}
    (e : M ≅ H) (W : Cᵒᵖ) (x : M.val.obj W) : e.hom.val.app W x = 0 ↔ x = 0 :=
  sheafOfModules_comp_iso_hom_val_app_eq_zero_iff (𝟙 M) e W x

/-- **The unit of `j^* ⊣ j_*` read on a module on the scheme.**  For `M₂` quasi-coherent on the
scheme of `T'` and `j : T'' ⟶ T'`, the base identification of `M₂` followed by the reading of the
unit of `j` at `M₂^a` kills a section `z` of `M₂` over `V` exactly when the pullback of `z` along
the morphism of schemes vanishes. -/
theorem unit_reading_val_app_eq_zero_iff_pullbackSection
    (M₂ : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf).FullSubcategory)
    (V : ((BigFppfOver.toScheme B S hS).obj T').Opens)
    (V'' : ((BigFppfOver.toScheme B S hS).obj T'').Opens)
    (hV : V'' = (BigFppfOver.toScheme B S hS).map j ⁻¹ᵁ V)
    (hV' : V'' ≤ (BigFppfOver.toScheme B S hS).map j ⁻¹ᵁ V) (z : M₂.obj.val.obj (op V)) :
    ((representedZariskiModuleQuasicoherentSchemeIso B S hS T' M₂).inv ≫
      (zariskiReadingIso T').hom.app
        ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj ≫
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS T')).map
        ((modulePullbackAdjunction B S hS (representedSpaceMap B S hS j)).unit.app
          ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj)).val.app
        (op V) z = 0 ↔
      Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map j) M₂.obj V V'' hV' z =
        0 := by
  refine (unit_val_app_selfOpens_eq_zero_iff_pullbackSection j
    ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj
    ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).property V V'' hV hV'
    (((representedZariskiModuleQuasicoherentSchemeIso B S hS T' M₂).inv ≫
      (zariskiReadingIso T').hom.app
        ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj).val.app
        (op V) z)).trans ?_
  exact (Eq.to_iff (congrArg (· = 0) (Scheme.Modules.pullbackSection_naturality
    ((BigFppfOver.toScheme B S hS).map j)
    ((representedZariskiModuleQuasicoherentSchemeIso B S hS T' M₂).inv ≫
      (zariskiReadingIso T').hom.app
        ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj)
    V V'' hV' z))).symm.trans
    (sheafOfModules_iso_hom_val_app_eq_zero_iff ((Scheme.Modules.pullback
      ((BigFppfOver.toScheme B S hS).map j)).mapIso
      ((representedZariskiModuleQuasicoherentSchemeIso B S hS T' M₂).symm ≪≫
        (zariskiReadingIso T').app
          ((representedQuasicoherentSchemeEquivalence B S hS T').functor.obj M₂).obj)) _ _)


/-- The adjoint along a morphism into a represented algebraic space kills the same sections
whichever spelling of the represented algebraic space is used. -/
theorem homEquiv_val_app_eq_zero_iff_yonedaSpace {T₀ : BigFppfOver B S hS}
    {Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ (⟨yoneda.obj T₀, isAlgebraicSpace_yoneda B S hS T₀⟩ : AlgebraicSpaces B S hS))
    {M : Modules.{u, u} B S hS (yoneda.obj T₀) (isAlgebraicSpace_yoneda B S hS T₀)}
    {H : Modules.{u, u} B S hS Y.1 Y.2} (v : (modulePullback B S hS f).obj M ⟶ H)
    (V : (SmallEtale B S hS (yoneda.obj T₀))ᵒᵖ) (x : M.val.obj V) :
    ((modulePullbackAdjunction B S hS (Y := yonedaSpace B S hS T₀) f).homEquiv M H v).val.app V
        x = 0 ↔
      ((modulePullbackAdjunction B S hS f).homEquiv M H v).val.app V x = 0 :=
  Iff.rfl

/-- **Removing an inverse image and a trailing isomorphism from an adjoint.**  The adjoint of
`f^*z ≫ w ≫ k`, with `k` invertible, kills `x` exactly when the adjoint of `w` kills `z(x)`. -/
theorem homEquiv_map_comp_comp_val_app_eq_zero_iff {Y U : AlgebraicSpaces B S hS} (f : Y ⟶ U)
    {N N' : Modules.{u, u} B S hS U.1 U.2} (z : N ⟶ N') {G G' : Modules.{u, u} B S hS Y.1 Y.2}
    (w : (modulePullback B S hS f).obj N' ⟶ G) (k : G ⟶ G') (hk : IsIso k)
    (V : (SmallEtale B S hS U.1)ᵒᵖ) (x : N.val.obj V) :
    ((modulePullbackAdjunction B S hS f).homEquiv N G'
        ((modulePullback B S hS f).map z ≫ w ≫ k)).val.app V x = 0 ↔
      ((modulePullbackAdjunction B S hS f).homEquiv N' G w).val.app V (z.val.app V x) = 0 := by
  have := hk
  have : IsIso ((modulePushforward B S hS f).map k) := Functor.map_isIso _ _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  exact comp_isIso_val_app_eq_zero_iff (((modulePullbackAdjunction B S hS f).homEquiv N' G) w)
    ((modulePushforward B S hS f).map k) V (z.val.app V x)

section Points

variable {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) {U₀ : BigFppfOver B S hS} (u₀ : yoneda.obj U₀ ⟶ X.1)
  (hP : IsAlgebraicSpace B S hS P)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)


/-- The paste behind
`AlgebraicGeometry.Space.C1359Bridge.squareComparison_inv_comp_pullback_map_comp_unit`, in an
arbitrary category. -/
private theorem paste_chart {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ Y₁ : C} (a : X₀ ⟶ X₁) (ψ : X₁ ⟶ X₄) (χ : X₄ ≅ X₅) (Zr : X₀ ⟶ X₂)
    (R : X₂ ⟶ X₃) (E : X₃ ⟶ X₅) (hψ : a ≫ ψ ≫ χ.hom = Zr ≫ R ≫ E) (U : X₄ ⟶ X₆)
    (U' : X₅ ⟶ Y₁) (k : Y₁ ⟶ X₆) (hU : χ.inv ≫ U = U' ≫ k) :
    a ≫ ψ ≫ U = Zr ≫ (R ≫ E ≫ U') ≫ k := by
  have h1 : a ≫ ψ ≫ U = (a ≫ ψ ≫ χ.hom) ≫ χ.inv ≫ U := by simp
  rw [h1, hψ, hU]
  simp

variable {c : (⟨yoneda.obj (d.fibre U₀ u₀), isAlgebraicSpace_yoneda B S hS _⟩ :
    AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩}
  (hsq : IsPullback c (representedSpaceMap B S hS (d.fibreHom U₀ u₀))
    (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) (pointHom u₀))
  (comm : c ≫ (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) =
    representedSpaceMap B S hS (d.fibreHom U₀ u₀) ≫ pointHom u₀)

/-- **`c^*ψ` through the square comparison, followed by a unit.**  Let `c : P_U ⟶ P` lie over the
atlas `u : U ⟶ X` and let `ψ : π^*𝒜_n ⟶ 𝒦` be such that the comparison `π_U^*u^* ≅ c^*π^*`
followed by `c^*ψ` and an identification `χ : c^*𝒦 ≅ M₂^a` is the inverse image of
`u^*𝒜_n ≅ ((u^*𝒜_n)_{Zar})^a` followed by the attached module of `Ψ : π_U^*(u^*𝒜_n)_{Zar} ⟶ M₂`.
Then for any `j : Z' ⟶ P_U` the same holds with the unit of `j` composed on, up to
`j_*j^*(χ⁻¹)`. -/
theorem squareComparison_inv_comp_pullback_map_comp_unit (n : ℤ)
    {K : Modules.{u, u} B S hS P hP}
    (M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (d.fibre U₀ u₀)).ringCatSheaf).FullSubcategory)
    (χ : (modulePullback B S hS c).obj K ≅
      ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre U₀ u₀)).functor.obj
        M₂).obj)
    (Ψ : quasicoherentPullbackObj B S hS (d.fibreHom U₀ u₀)
      (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))) ⟶ M₂)
    (ψ : (modulePullback B S hS
      (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n) ⟶ K)
    (hψ : (modulePullbackSquareComparison
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (pointHom u₀) (representedSpaceMap B S hS (d.fibreHom U₀ u₀)) c
        comm).inv.app (A.piece n) ≫ (modulePullback B S hS c).map ψ ≫ χ.hom =
      (modulePullback B S hS (representedSpaceMap B S hS (d.fibreHom U₀ u₀))).map
        (zariskiReadingQuasicoherentIso U₀
          ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS (d.fibreHom U₀ u₀)
          (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n)))).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS
          (d.fibre U₀ u₀)).functor.map Ψ).hom)
    {Z' : AlgebraicSpaces B S hS}
    (j : Z' ⟶ ⟨yoneda.obj (d.fibre U₀ u₀), isAlgebraicSpace_yoneda B S hS _⟩) :
    (modulePullbackSquareComparison
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (pointHom u₀) (representedSpaceMap B S hS (d.fibreHom U₀ u₀)) c
        comm).inv.app (A.piece n) ≫
      (modulePullback B S hS c).map ψ ≫
      (modulePullbackAdjunction B S hS j).unit.app ((modulePullback B S hS c).obj K) =
    (modulePullback B S hS (representedSpaceMap B S hS (d.fibreHom U₀ u₀))).map
        (zariskiReadingQuasicoherentIso U₀
          ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))).hom ≫
      ((modulePullbackRepresentedQuasicoherentIso B S hS (d.fibreHom U₀ u₀)
          (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n)))).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS
          (d.fibre U₀ u₀)).functor.map Ψ).hom ≫
        (modulePullbackAdjunction B S hS j).unit.app
          ((representedQuasicoherentSchemeEquivalence B S hS
            (d.fibre U₀ u₀)).functor.obj M₂).obj) ≫
      (modulePushforward B S hS j).map ((modulePullback B S hS j).map χ.inv) := by
  have hU : χ.inv ≫ (modulePullbackAdjunction B S hS j).unit.app
        ((modulePullback B S hS c).obj K) =
      (modulePullbackAdjunction B S hS j).unit.app
          ((representedQuasicoherentSchemeEquivalence B S hS
            (d.fibre U₀ u₀)).functor.obj M₂).obj ≫
        (modulePushforward B S hS j).map ((modulePullback B S hS j).map χ.inv) :=
    (modulePullbackAdjunction B S hS j).unit.naturality χ.inv
  exact paste_chart _ _ χ _ _ _ hψ _ _ _ hU


include hsq in
/-- **The kernel over an étale chart of the atlas, on the base change to `P_U`**: the étale base
change step of the chart dictionary, for `c : P_U ⟶ P` over the atlas `u : U ⟶ X`. -/
theorem homEquiv_comp_unit_val_app_atlasChart_eq_zero_iff (hc : IsEtale B S hS c.hom) (n : ℤ)
    {K : Modules.{u, u} B S hS P hP}
    (ψ : (modulePullback B S hS
      (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n) ⟶ K)
    {Z : AlgebraicSpaces B S hS} (i : Z ⟶ ⟨P, hP⟩) {T'' : BigFppfOver B S hS}
    (cZ : (⟨yoneda.obj T'', isAlgebraicSpace_yoneda B S hS T''⟩ : AlgebraicSpaces B S hS) ⟶ Z)
    (τZ : T'' ⟶ d.fibre U₀ u₀)
    (sqZ : IsPullback cZ (representedSpaceMap B S hS τZ) i c)
    (hg : IsEtale B S hS (pointHom u₀).hom)
    (W : ((BigFppfOver.toScheme B S hS).obj U₀).Opens)
    (x : ((modulePullback B S hS (pointHom u₀)).obj (A.piece n)).val.obj
      (op ((selfOpensFunctor B S hS U₀).obj W))) :
    ((modulePullbackAdjunction B S hS
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).homEquiv _ _
        (ψ ≫ (modulePullbackAdjunction B S hS i).unit.app K)).val.app
        (op ((smallEtalePostcomp B S hS (pointHom u₀) hg).obj
          ((selfOpensFunctor B S hS U₀).obj W)))
        (((modulePullbackIsoEtaleModulePullback B S hS (pointHom u₀) hg).app
          (A.piece n)).hom.val.app (op ((selfOpensFunctor B S hS U₀).obj W)) x) = 0 ↔
      ((modulePullbackAdjunction B S hS (Y := yonedaSpace B S hS U₀)
        (representedSpaceMap B S hS (d.fibreHom U₀ u₀))).homEquiv
        ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        ((modulePushforward B S hS (representedSpaceMap B S hS τZ)).obj
          ((modulePullback B S hS (representedSpaceMap B S hS τZ)).obj
            ((modulePullback B S hS c).obj K)))
        ((modulePullbackSquareComparison
            (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
            (pointHom u₀) (representedSpaceMap B S hS (d.fibreHom U₀ u₀)) c
            comm).inv.app (A.piece n) ≫
          (modulePullback B S hS c).map ψ ≫
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS τZ)).unit.app
            ((modulePullback B S hS c).obj K))).val.app
        (op ((selfOpensFunctor B S hS U₀).obj W)) x = 0 := by
  exact homEquiv_comp_unit_val_app_etaleChart_eq_zero_iff_of_comm
    (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X) i (pointHom u₀) c
    (representedSpaceMap B S hS (d.fibreHom U₀ u₀)) cZ
    (representedSpaceMap B S hS τZ) hsq comm sqZ hg hc ψ ((selfOpensFunctor B S hS U₀).obj W) x

/-- An adjoint of equal morphisms kills the same sections. -/
theorem homEquiv_val_app_eq_zero_iff_of_eq {Y Y' : AlgebraicSpaces B S hS} (f : Y ⟶ Y')
    {M : Modules.{u, u} B S hS Y'.1 Y'.2} {H : Modules.{u, u} B S hS Y.1 Y.2}
    {v v' : (modulePullback B S hS f).obj M ⟶ H} (h : v = v')
    (V : (SmallEtale B S hS Y'.1)ᵒᵖ) (x : M.val.obj V) :
    ((modulePullbackAdjunction B S hS f).homEquiv M H v).val.app V x = 0 ↔
      ((modulePullbackAdjunction B S hS f).homEquiv M H v').val.app V x = 0 := by
  rw [h]

/-- **The base-changed kernel through the chart property of `ψ`**: on `P_U`, the adjoint of
`c^*ψ ≫ η_j` (after the square comparison) kills `x` exactly when the adjoint of the attached
module of `Ψ` followed by the unit of `j` kills the Zariski reading of `x`. -/
theorem homEquiv_squareComparison_val_app_eq_zero_iff (n : ℤ)
    {K : Modules.{u, u} B S hS P hP}
    (M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (d.fibre U₀ u₀)).ringCatSheaf).FullSubcategory)
    (χ : (modulePullback B S hS c).obj K ≅
      ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre U₀ u₀)).functor.obj
        M₂).obj)
    (Ψ : quasicoherentPullbackObj B S hS (d.fibreHom U₀ u₀)
      (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))) ⟶ M₂)
    (ψ : (modulePullback B S hS
      (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n) ⟶ K)
    (hψ : (modulePullbackSquareComparison
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (pointHom u₀) (representedSpaceMap B S hS (d.fibreHom U₀ u₀)) c
        comm).inv.app (A.piece n) ≫ (modulePullback B S hS c).map ψ ≫ χ.hom =
      (modulePullback B S hS (representedSpaceMap B S hS (d.fibreHom U₀ u₀))).map
        (zariskiReadingQuasicoherentIso U₀
          ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS (d.fibreHom U₀ u₀)
          (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n)))).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS
          (d.fibre U₀ u₀)).functor.map Ψ).hom)
    {T'' : BigFppfOver B S hS} (τZ : T'' ⟶ d.fibre U₀ u₀)
    (W : ((BigFppfOver.toScheme B S hS).obj U₀).Opens)
    (x : ((modulePullback B S hS (pointHom u₀)).obj (A.piece n)).val.obj
      (op ((selfOpensFunctor B S hS U₀).obj W))) :
    ((modulePullbackAdjunction B S hS (Y := yonedaSpace B S hS U₀)
        (representedSpaceMap B S hS (d.fibreHom U₀ u₀))).homEquiv
        ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        ((modulePushforward B S hS (representedSpaceMap B S hS τZ)).obj
          ((modulePullback B S hS (representedSpaceMap B S hS τZ)).obj
            ((modulePullback B S hS c).obj K)))
        ((modulePullbackSquareComparison
            (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
            (pointHom u₀) (representedSpaceMap B S hS (d.fibreHom U₀ u₀)) c
            comm).inv.app (A.piece n) ≫
          (modulePullback B S hS c).map ψ ≫
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS τZ)).unit.app
            ((modulePullback B S hS c).obj K))).val.app
        (op ((selfOpensFunctor B S hS U₀).obj W)) x = 0 ↔
      ((modulePullbackAdjunction B S hS
        (representedSpaceMap B S hS (d.fibreHom U₀ u₀))).homEquiv _ _
        ((modulePullbackRepresentedQuasicoherentIso B S hS (d.fibreHom U₀ u₀)
            (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n)))).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS
            (d.fibre U₀ u₀)).functor.map Ψ).hom ≫
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS τZ)).unit.app
            ((representedQuasicoherentSchemeEquivalence B S hS
              (d.fibre U₀ u₀)).functor.obj M₂).obj)).val.app
        (op ((selfOpensFunctor B S hS U₀).obj W))
        ((zariskiReadingQuasicoherentIso U₀
          ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))).hom.val.app _
          x) = 0 := by
  refine (homEquiv_val_app_eq_zero_iff_yonedaSpace
    (representedSpaceMap B S hS (d.fibreHom U₀ u₀)) _ _ x).trans ?_
  have h3 := squareComparison_inv_comp_pullback_map_comp_unit d u₀ hP A hA comm n M₂ χ Ψ ψ hψ
    (representedSpaceMap B S hS τZ)
  refine (homEquiv_val_app_eq_zero_iff_of_eq
    (representedSpaceMap B S hS (d.fibreHom U₀ u₀))
    (M := (modulePullback B S hS (pointHom u₀)).obj (A.piece n))
    (H := (modulePushforward B S hS (representedSpaceMap B S hS τZ)).obj
      ((modulePullback B S hS (representedSpaceMap B S hS τZ)).obj
        ((modulePullback B S hS c).obj K))) h3 _ x).trans ?_
  exact homEquiv_map_comp_comp_val_app_eq_zero_iff
    (representedSpaceMap B S hS (d.fibreHom U₀ u₀)) _ _ _
    ((modulePushforward B S hS (representedSpaceMap B S hS τZ)).mapIso
      ((modulePullback B S hS (representedSpaceMap B S hS τZ)).mapIso χ.symm)).isIso_hom _ x

/-- **The represented end of the chart dictionary**: the adjoint along `π_U` of the attached module
of `Ψ` followed by the unit of `j = τ_Z` kills the Zariski reading of `x` exactly when the pullback
along `τ_Z` of `Ψ` applied to the pullback of `x` vanishes. -/
theorem homEquiv_attached_comp_unit_val_app_eq_zero_iff (n : ℤ)
    (M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (d.fibre U₀ u₀)).ringCatSheaf).FullSubcategory)
    (Ψ : quasicoherentPullbackObj B S hS (d.fibreHom U₀ u₀)
      (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))) ⟶ M₂)
    {T'' : BigFppfOver B S hS} (τZ : T'' ⟶ d.fibre U₀ u₀)
    (W : ((BigFppfOver.toScheme B S hS).obj U₀).Opens)
    (V : ((BigFppfOver.toScheme B S hS).obj (d.fibre U₀ u₀)).Opens)
    (hV : V = (BigFppfOver.toScheme B S hS).map (d.fibreHom U₀ u₀) ⁻¹ᵁ W)
    (hV' : V ≤ (BigFppfOver.toScheme B S hS).map (d.fibreHom U₀ u₀) ⁻¹ᵁ W)
    (V'' : ((BigFppfOver.toScheme B S hS).obj T'').Opens)
    (hV'' : V'' = (BigFppfOver.toScheme B S hS).map τZ ⁻¹ᵁ V)
    (hV''' : V'' ≤ (BigFppfOver.toScheme B S hS).map τZ ⁻¹ᵁ V)
    (x : ((modulePullback B S hS (pointHom u₀)).obj (A.piece n)).val.obj
      (op ((selfOpensFunctor B S hS U₀).obj W))) :
    ((modulePullbackAdjunction B S hS
        (representedSpaceMap B S hS (d.fibreHom U₀ u₀))).homEquiv _ _
        ((modulePullbackRepresentedQuasicoherentIso B S hS (d.fibreHom U₀ u₀)
            (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n)))).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS
            (d.fibre U₀ u₀)).functor.map Ψ).hom ≫
          (modulePullbackAdjunction B S hS (representedSpaceMap B S hS τZ)).unit.app
            ((representedQuasicoherentSchemeEquivalence B S hS
              (d.fibre U₀ u₀)).functor.obj M₂).obj)).val.app
        (op ((selfOpensFunctor B S hS U₀).obj W))
        ((zariskiReadingQuasicoherentIso U₀
          ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))).hom.val.app _
          x) = 0 ↔
      Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map τZ) M₂.obj V V'' hV'''
        (Ψ.hom.val.app (op V)
          (Scheme.Modules.pullbackSection
            ((BigFppfOver.toScheme B S hS).map (d.fibreHom U₀ u₀))
            ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U₀)).obj
              ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))) W V hV' x)) = 0 := by
  refine (homEquiv_val_app_selfOpens_eq_zero_iff_pullbackSection'
    (d.fibreHom U₀ u₀)
    ((representedQuasicoherentSchemeEquivalence B S hS U₀).functor.obj
      (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n)))).obj
    ((representedQuasicoherentSchemeEquivalence B S hS U₀).functor.obj
      (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n)))).property
    _ W V hV hV'
    ((zariskiReadingQuasicoherentIso U₀
      ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))).hom.val.app _
      x)).trans
    ((pullbackReadingHom_comp_val_app_pullbackSection_eq_zero_iff
      (d.fibreHom U₀ u₀) τZ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
        (pointHom u₀) _ (hA n)) M₂ Ψ W V hV' x).trans
      (unit_reading_val_app_eq_zero_iff_pullbackSection τZ M₂ V V'' hV'' hV'''
        (Ψ.hom.val.app (op V)
          (Scheme.Modules.pullbackSection
            ((BigFppfOver.toScheme B S hS).map (d.fibreHom U₀ u₀))
            ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U₀)).obj
              ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))) W V hV' x))))


include hsq in
/-- **The chart dictionary for the kernel of `𝒜_n ⟶ π_*i_*i^*𝒦`, on representables.**  With
`ψ`, `χ`, `Ψ` as in `squareComparison_inv_comp_pullback_map_comp_unit`, a closed-subspace-type
square `c_Z ≫ i = j ≫ c` with `j` represented by `τ_Z : T'' ⟶ U ×_X P`, the adjoint of
`ψ ≫ η_i` kills the 03LW-reading of a section `x` of `u^*𝒜_n` over the chart `W ⟶ U ⟶ X`
exactly when the pullback along `τ_Z` of `Ψ` applied to the pullback of `x` vanishes. -/
theorem homEquiv_comp_unit_val_app_etalePointChart_eq_zero_iff (hc : IsEtale B S hS c.hom)
    (n : ℤ)
    {K : Modules.{u, u} B S hS P hP}
    (M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
      (d.fibre U₀ u₀)).ringCatSheaf).FullSubcategory)
    (χ : (modulePullback B S hS c).obj K ≅
      ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre U₀ u₀)).functor.obj
        M₂).obj)
    (Ψ : quasicoherentPullbackObj B S hS (d.fibreHom U₀ u₀)
      (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))) ⟶ M₂)
    (ψ : (modulePullback B S hS
      (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).obj (A.piece n) ⟶ K)
    (hψ : (modulePullbackSquareComparison
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (pointHom u₀) (representedSpaceMap B S hS (d.fibreHom U₀ u₀)) c
        comm).inv.app (A.piece n) ≫ (modulePullback B S hS c).map ψ ≫ χ.hom =
      (modulePullback B S hS (representedSpaceMap B S hS (d.fibreHom U₀ u₀))).map
        (zariskiReadingQuasicoherentIso U₀
          ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n))).hom ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS (d.fibreHom U₀ u₀)
          (zariskiReadingQcoh U₀ ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (pointHom u₀) _ (hA n)))).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS
          (d.fibre U₀ u₀)).functor.map Ψ).hom)
    {Z : AlgebraicSpaces B S hS} (i : Z ⟶ ⟨P, hP⟩) {T'' : BigFppfOver B S hS}
    (cZ : (⟨yoneda.obj T'', isAlgebraicSpace_yoneda B S hS T''⟩ : AlgebraicSpaces B S hS) ⟶ Z)
    (τZ : T'' ⟶ d.fibre U₀ u₀)
    (sqZ : IsPullback cZ (representedSpaceMap B S hS τZ) i c)
    (hg : IsEtale B S hS (pointHom u₀).hom)
    (W : ((BigFppfOver.toScheme B S hS).obj U₀).Opens)
    (V : ((BigFppfOver.toScheme B S hS).obj (d.fibre U₀ u₀)).Opens)
    (hV : V = (BigFppfOver.toScheme B S hS).map (d.fibreHom U₀ u₀) ⁻¹ᵁ W)
    (hV' : V ≤ (BigFppfOver.toScheme B S hS).map (d.fibreHom U₀ u₀) ⁻¹ᵁ W)
    (V'' : ((BigFppfOver.toScheme B S hS).obj T'').Opens)
    (hV'' : V'' = (BigFppfOver.toScheme B S hS).map τZ ⁻¹ᵁ V)
    (hV''' : V'' ≤ (BigFppfOver.toScheme B S hS).map τZ ⁻¹ᵁ V)
    (x : ((modulePullback B S hS (pointHom u₀)).obj (A.piece n)).val.obj
      (op ((selfOpensFunctor B S hS U₀).obj W))) :
    ((modulePullbackAdjunction B S hS
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)).homEquiv _ _
        (ψ ≫ (modulePullbackAdjunction B S hS i).unit.app K)).val.app
        (op ((smallEtalePostcomp B S hS (pointHom u₀) hg).obj
          ((selfOpensFunctor B S hS U₀).obj W)))
        (((modulePullbackIsoEtaleModulePullback B S hS (pointHom u₀) hg).app
          (A.piece n)).hom.val.app (op ((selfOpensFunctor B S hS U₀).obj W)) x) = 0 ↔
      Scheme.Modules.pullbackSection ((BigFppfOver.toScheme B S hS).map τZ) M₂.obj V V'' hV'''
        (Ψ.hom.val.app (op V)
          (Scheme.Modules.pullbackSection
            ((BigFppfOver.toScheme B S hS).map (d.fibreHom U₀ u₀))
            ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U₀)).obj
              ((modulePullback B S hS (pointHom u₀)).obj (A.piece n))) W V hV' x)) = 0 :=
  (homEquiv_comp_unit_val_app_atlasChart_eq_zero_iff d u₀ hP A hsq comm hc n ψ i cZ τZ sqZ hg W
    x).trans
    ((homEquiv_squareComparison_val_app_eq_zero_iff d u₀ hP A hA comm n M₂ χ Ψ ψ hψ τZ W x).trans
      (homEquiv_attached_comp_unit_val_app_eq_zero_iff d u₀ A hA n M₂ Ψ τZ W V hV hV' V''
        hV'' hV''' x))

end Points

section PointsAtlas

variable {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)

/-- The cartesian square `c ≫ π = π_U ≫ u` of the atlas of `P` over the atlas of `X`, as a
square of algebraic spaces. -/
theorem isPullback_presentationAtlas_homMk :
    IsPullback (presentationAtlas (d.spacePresentation Px hP))
      (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
      (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (pointHom Px.toSpace) :=
  isPullback_homMk B S hS hP (isAlgebraicSpace_yoneda _ _ _ _) X.2
    (isAlgebraicSpace_yoneda _ _ _ _) (d.isPullback Px.U Px.toSpace)

/-- The atlas `c : P_U ⟶ P` of the presentation of `P`, with its source spelled as the algebraic
space represented by `U ×_X P`. -/
abbrev presentationFibreAtlas :
    (⟨yoneda.obj (d.fibre Px.U Px.toSpace), isAlgebraicSpace_yoneda B S hS _⟩ :
      AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩ :=
  presentationAtlas (d.spacePresentation Px hP)

/-- The square `c ≫ π = π_U ≫ u` of the atlas of `P`, for the atlas spelled through `U ×_X P`. -/
theorem isPullback_presentationFibreAtlas :
    IsPullback (presentationFibreAtlas d Px hP)
      (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
      (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
      (pointHom Px.toSpace) :=
  isPullback_presentationAtlas_homMk d Px hP

end PointsAtlas

section Situation

variable (s : RelativeProjSituation.{u, u})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)

variable {Z : AlgebraicSpaces s.site s.base s.containsBase} (i : Z ⟶ s.Proj)
  (hi : IsClosedImmersion s.site s.base s.containsBase i.hom)

/-- The projection `Z ×_P (T ×_X P) ⟶ Z` of the chart of a closed subspace over a scheme point
`f : T ⟶ X` of the base. -/
def closedSubspaceChartFst (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) :
    (⟨yoneda.obj ((closedSubspaceOfIsClosedImmersion s.site s.base s.containsBase i
        hi).2.2.rep.pullback (s.relativeProjPoints.fibreToSpace T f)),
      isAlgebraicSpace_yoneda _ _ _ _⟩ : AlgebraicSpaces s.site s.base s.containsBase) ⟶ Z := by
  haveI := mono_of_isClosedImmersion s.site s.base s.containsBase i.hom hi
  exact ObjectProperty.homMk
    ((closedSubspaceOfIsClosedImmersion s.site s.base s.containsBase i hi).2.2.rep.fst
      (s.relativeProjPoints.fibreToSpace T f) ≫ (asIso (Subfunctor.toRange i.hom)).inv)

/-- **The chart of a closed subspace over a scheme point of the base.**  For `i : Z ⟶ P` a closed
immersion and `f : T ⟶ X`, the base change `Z ×_P (T ×_X P)` of `i` along `T ×_X P ⟶ P`, spelled
through the representability of the range of `i`, is a fibre product of algebraic spaces. -/
theorem isPullback_closedSubspaceChartPoint (T : BigFppfOver s.site s.base s.containsBase)
    (f : yoneda.obj T ⟶ s.space.1) :
    IsPullback (closedSubspaceChartFst s i hi T f)
      (representedSpaceMap s.site s.base s.containsBase
        ((closedSubspaceOfIsClosedImmersion s.site s.base s.containsBase i hi).2.2.rep.snd
          (s.relativeProjPoints.fibreToSpace T f)))
      i (ObjectProperty.homMk (s.relativeProjPoints.fibreToSpace T f) :
        (⟨yoneda.obj (s.relativeProjPoints.fibre T f), isAlgebraicSpace_yoneda _ _ _ _⟩ :
          AlgebraicSpaces s.site s.base s.containsBase) ⟶ s.Proj) := by
  have := mono_of_isClosedImmersion s.site s.base s.containsBase i.hom hi
  have h := (closedSubspaceOfIsClosedImmersion s.site s.base s.containsBase i hi).2.2.rep.isPullback
    (s.relativeProjPoints.fibreToSpace T f)
  have hι : inv (Subfunctor.toRange i.hom) ≫ i.hom = (Subfunctor.range i.hom).ι := by
    rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]
  have h' := h.of_iso (Iso.refl _) (asIso (Subfunctor.toRange i.hom)).symm (Iso.refl _)
    (Iso.refl _) (fst' := _ ≫ inv (Subfunctor.toRange i.hom))
    (snd' := yoneda.map ((closedSubspaceOfIsClosedImmersion s.site s.base s.containsBase i
      hi).2.2.rep.snd (s.relativeProjPoints.fibreToSpace T f))) (f' := i.hom)
    (g' := s.relativeProjPoints.fibreToSpace T f)
    (Category.id_comp _).symm ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans hι.symm) ((Category.comp_id _).trans (Category.id_comp _).symm)
  exact isPullback_homMk s.site s.base s.containsBase Z.2 (isAlgebraicSpace_yoneda _ _ _ _)
    s.Proj.2 (isAlgebraicSpace_yoneda _ _ _ _) h'

/-- **The chart of a closed subspace over the atlas of `P`**: the case of
`AlgebraicGeometry.Space.C1359Bridge.isPullback_closedSubspaceChartPoint` at the atlas of a
presentation. -/
theorem isPullback_closedSubspaceChart :
    IsPullback (closedSubspaceChartFst s i hi Px.U Px.toSpace)
      (representedSpaceMap s.site s.base s.containsBase
        ((closedSubspaceOfIsClosedImmersion s.site s.base s.containsBase i hi).2.2.rep.snd
          (s.relativeProjPoints.fibreToSpace Px.U Px.toSpace)))
      i (presentationAtlas
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)) :=
  isPullback_closedSubspaceChartPoint s i hi Px.U Px.toSpace

/-- The identification of the re-presented algebra, inverted on a section. -/
theorem smallAlgebraPieceIso_inv_smallPieceEquiv (n : ℤ)
    (V : (SmallEtale s.site s.base s.containsBase s.space.1)ᵒᵖ)
    (y : (s.smallAlgebra.piece n).val.obj V) :
    (s.smallAlgebraPieceIso n).inv.val.app V
      (SheafOfModules.GradedAlgebra.smallPieceEquiv s.algebra n V y) = y := by
  change ((s.smallAlgebraPieceIso n).hom ≫ (s.smallAlgebraPieceIso n).inv).val.app V y = y
  rw [Iso.hom_inv_id]
  rfl

/-- The reading of a section on a chart, unfolded. -/
theorem etalePointReading_eq_mk {T₀ : BigFppfOver s.site s.base s.containsBase}
    (t₀ : yoneda.obj T₀ ⟶ s.space.1)
    (hf : IsEtale s.site s.base s.containsBase (pointHom (X := s.space) t₀).hom) (n : ℤ)
    (W : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T₀).Opens)
    (a : Γ((s.relativeProjPoints.algebra T₀ t₀).piece n, W)) :
    s.etalePointReading t₀ hf n W a =
      (RelativeProjSituation.mk s.site s.base s.containsBase s.space s.algebra s.mul_comm
        s.negative_isZero s.isQuasicoherent s.sections_hasCardinalLT).etalePointSectionsEquiv
          t₀ hf n W a :=
  rfl

end Situation

end AlgebraicGeometry.Space.C1359Bridge

end
