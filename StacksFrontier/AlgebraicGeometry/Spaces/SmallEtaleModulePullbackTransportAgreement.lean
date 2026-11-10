module

public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleDerivedPullbackCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareMates
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackTensorSections

/-!
# The two compositors of the inverse image of modules on algebraic spaces agree

The inverse image of `𝒪`-modules along a composite `f ≫ g` of morphisms of algebraic spaces is
compared with the composite of the inverse images in two ways: through the composition comparison
of Stacks 03LU, `AlgebraicGeometry.Space.modulePullbackCompIso`, carried by the pullback datum
`AlgebraicGeometry.Space.toposPullbackData`; and through the compositor of the morphisms of small
étale ringed topoi followed by the transport `AlgebraicGeometry.Space.pullbackModulesCompTransport`
along the 2-isomorphism comparing their composite with the morphism of ringed topoi of `f ≫ g`.
This file shows the two agree, and deduces that the two compositors of the derived pullback built
from them agree as well.

## Main results

* `AlgebraicGeometry.Space.pullbackModulesCompIso_inv_comp_pullbackModulesCompTransport_hom`: the
  underived compositors agree.
* `Space.toposDerivedPullbackData_compIso_eq_smallEtaleDerivedModulePullbackCompIso_symm`: the
  composition comparison of `AlgebraicGeometry.Space.toposDerivedPullbackData` is the inverse of
  the comparison `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso` of Stacks 0D6D.
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-! ### Comparing two compositors of left adjoints through their conjugates -/

namespace Stacks.CategoryTheory

/-- Two compositors of left adjoints agree once their conjugates do. Let `L_f ⊣ P_f`, `L_g ⊣ P_g`,
`L_c ⊣ P_c` and `L_{fg} ⊣ P_{fg}` be adjunctions, compared with a second family `L'_f ⊣ R_f`,
`L'_g ⊣ R_g`, `L'_{fg} ⊣ R_{fg}` along isomorphisms `ε` of the left adjoints whose conjugates are
the transports along equations `P = R` of the right adjoints. Let `γ : L_c ≅ L_g ⋙ L_f` and
`T : L_c ≅ L_{fg}` have conjugates `δ` and `τ`. If the comparison `μ : R_f ⋙ R_g ≅ R_{fg}` of the
second family is `δ⁻¹` followed by `τ` up to the transports, then the comparison `γ⁻¹ ≫ T` of the
first family is any comparison `M` of the second family whose conjugate is `μ⁻¹`, read through the
`ε`. -/
theorem inv_comp_hom_eq_whisker_comp_comp_inv_of_conjugateEquiv
    {CX CY CZ : Type*} [Category CX] [Category CY] [Category CZ]
    {Lf Lf' : CY ⥤ CX} {Pf Rf : CX ⥤ CY} {Lg Lg' : CZ ⥤ CY} {Pg Rg : CY ⥤ CZ}
    {Lc Lfg Lfg' : CZ ⥤ CX} {Pc Pfg Rfg : CX ⥤ CZ}
    (Af : Lf ⊣ Pf) (Ag : Lg ⊣ Pg) (Ac : Lc ⊣ Pc) (Afg : Lfg ⊣ Pfg)
    (Af' : Lf' ⊣ Rf) (Ag' : Lg' ⊣ Rg) (Afg' : Lfg' ⊣ Rfg)
    (pf : Pf = Rf) (pg : Pg = Rg) (pfg : Pfg = Rfg)
    (εf : Lf ≅ Lf') (εg : Lg ≅ Lg') (εfg : Lfg ≅ Lfg')
    (hεf : conjugateEquiv Af' Af εf.hom = eqToHom pf.symm)
    (hεg : conjugateEquiv Ag' Ag εg.hom = eqToHom pg.symm)
    (hεfg : conjugateEquiv Afg' Afg εfg.hom = eqToHom pfg.symm)
    (γ : Lc ≅ Lg ⋙ Lf) (δ : Pc ≅ Pf ⋙ Pg) (hγ : conjugateEquiv Ac (Ag.comp Af) γ.inv = δ.hom)
    (T : Lc ≅ Lfg) (τ : Pc ≅ Pfg) (hT : conjugateEquiv Afg Ac T.hom = τ.inv)
    (m : Rf ⋙ Rg = Pf ⋙ Pg) (μ : Rf ⋙ Rg ≅ Rfg)
    (hμ : μ = eqToIso m ≪≫ δ.symm ≪≫ τ ≪≫ eqToIso pfg)
    (M : Lg' ⋙ Lf' ⟶ Lfg') (hM : conjugateEquiv Afg' (Ag'.comp Af') M = μ.inv) :
    γ.inv ≫ T.hom =
      ((Functor.whiskerLeft Lg εf.hom ≫ Functor.whiskerRight εg.hom Lf') ≫ M) ≫ εfg.inv := by
  subst hμ pf pg pfg
  have hL : conjugateEquiv Afg (Ag.comp Af) (γ.inv ≫ T.hom) = τ.inv ≫ δ.hom := by
    rw [← conjugateEquiv_comp Afg Ac (Ag.comp Af), hT, hγ]
  have hεfg' : conjugateEquiv Afg Afg' εfg.inv = 𝟙 _ := by
    have h := conjugateEquiv_comp Afg Afg' Afg εfg.inv εfg.hom
    rwa [hεfg, eqToHom_refl, Category.comp_id, Iso.hom_inv_id, conjugateEquiv_id] at h
  have hR : conjugateEquiv Afg (Ag.comp Af)
      (((Functor.whiskerLeft Lg εf.hom ≫ Functor.whiskerRight εg.hom Lf') ≫ M) ≫ εfg.inv) =
      τ.inv ≫ δ.hom := by
    rw [← conjugateEquiv_comp Afg Afg' (Ag.comp Af),
      ← conjugateEquiv_comp Afg' (Ag'.comp Af') (Ag.comp Af),
      ← conjugateEquiv_comp (Ag'.comp Af') (Ag.comp Af') (Ag.comp Af),
      conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft, hεf, hεg,
      hM, hεfg']
    simp
  exact (conjugateEquiv Afg (Ag.comp Af)).injective (hL.trans hR.symm)

/-- Two natural transformations `L ⋙ G ⟶ F` of the shape `whiskerLeft L γ ≫ α` agree as soon as
they agree at every object, read as `γ.app (L.obj K) ≫ α.app K`. -/
theorem whiskerLeft_comp_eq_of_app {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {G G' : D ⥤ E} {F : C ⥤ E} (γ₁ γ₂ : G ⟶ G') (α : L ⋙ G' ⟶ F)
    (h : ∀ K, γ₁.app (L.obj K) ≫ α.app K = γ₂.app (L.obj K) ≫ α.app K) :
    Functor.whiskerLeft L γ₁ ≫ α = Functor.whiskerLeft L γ₂ ≫ α :=
  NatTrans.ext (funext h)

end Stacks.CategoryTheory

namespace CategoryTheory.PullbackData

/-- The inverse of the composition comparison of a transported pullback pseudofunctor datum,
written out. -/
theorem transport_compIso_inv {A : Type*} [Category A] {M : A → Type*} [∀ a, Category (M a)]
    (P' : PullbackData A M) (pull' : ∀ {a b : A}, (a ⟶ b) → (M b ⥤ M a))
    (ε : ∀ {a b : A} (f : a ⟶ b), pull' f ≅ P'.pull f) {a b d : A} (f : a ⟶ b) (g : b ⟶ d) :
    ((transport P' pull' ε).compIso f g).inv =
      ((Functor.whiskerLeft (pull' g) (ε f).hom ≫ Functor.whiskerRight (ε g).hom (P'.pull f)) ≫
        (P'.compIso f g).inv) ≫ (ε (f ≫ g)).inv :=
  rfl

/-- On the homotopy categories of cochain complexes, the inverse of the composition comparison
`c` read through `CategoryTheory.PullbackData.homotopyIso` and
`CategoryTheory.PullbackData.homotopyCompIso` is the comparison induced by `e` followed by the one
induced by `T`, as soon as `e ≫ T` is the inverse of `c`. -/
theorem homotopyIso_trans_homotopyCompIso_inv {V₁ V₂ V₃ : Type*} [Category V₁] [Preadditive V₁]
    [Category V₂] [Preadditive V₂] [Category V₃] [Preadditive V₃]
    (F₁ : V₃ ⥤ V₂) (F₂ : V₂ ⥤ V₁) {Lc Lfg : V₃ ⥤ V₁} [F₁.Additive] [F₂.Additive] [Lc.Additive]
    [Lfg.Additive] (e : F₁ ⋙ F₂ ≅ Lc) (T : Lc ≅ Lfg) (c : Lfg ≅ F₁ ⋙ F₂)
    (h : e.hom ≫ T.hom = c.inv) :
    (homotopyIso c ≪≫ homotopyCompIso F₁ F₂).inv =
      (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso T (ComplexShape.up ℤ)).hom := by
  refine NatTrans.ext (funext fun Y => ?_)
  change (HomotopyCategory.quotient V₁ _).map
        ((NatTrans.mapHomologicalComplex (Iso.refl (F₁ ⋙ F₂)).hom _).app Y.as) ≫
      (HomotopyCategory.quotient V₁ _).map ((NatTrans.mapHomologicalComplex c.inv _).app Y.as) =
    (HomotopyCategory.quotient V₁ _).map ((NatTrans.mapHomologicalComplex e.hom _).app Y.as) ≫
      (HomotopyCategory.quotient V₁ _).map ((NatTrans.mapHomologicalComplex T.hom _).app Y.as)
  rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.comp_app,
    ← NatTrans.mapHomologicalComplex_comp, ← NatTrans.mapHomologicalComplex_comp, ← h,
    Iso.refl_hom, Category.id_comp]

end CategoryTheory.PullbackData

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y Z : AlgebraicSpaces B S hS}
  (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The adjunction of the inverse image and the direct image of modules of the morphism of small
étale ringed topoi of `f`. -/
abbrev toposModulesAdj (h : X ⟶ Y) :=
  RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS h)

/-- The conjugate of the transport `pullbackModulesCompTransport` is the inverse of the transport
of the direct images. -/
theorem conjugateEquiv_pullbackModulesCompTransport_hom :
    conjugateEquiv (toposModulesAdj B S hS (f ≫ g))
        (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHomComp B S hS f g))
        (pullbackModulesCompTransport B S hS f g).hom =
      (pushforwardModulesCompTransport B S hS f g).inv :=
  Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom' _ _ _

/-- The conjugate of the identification of the two spellings of the inverse image of modules
along `h` is the transport along the equation of the two spellings of the direct image. -/
theorem conjugateEquiv_toposPullbackModulesIso_hom (h : X ⟶ Y) :
    conjugateEquiv (modulePullbackAdjunction B S hS h) (toposModulesAdj B S hS h)
        (toposPullbackModulesIso h).hom =
      eqToHom (pushforwardModules_eq_modulePushforward B S hS h).symm := by
  have e : toposPullbackModulesIso h = pullbackModulesIsoModulePullback B S hS h :=
    (pullbackModulesIsoModulePullback_eq_eqToIso h).symm
  rw [e]
  exact (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom' _ _ _).trans
    (congrArg Iso.inv (pushforwardModulesIsoModulePushforward_eq_eqToIso B S hS h))

/-- The two compositors of the inverse image of modules agree: the inverse of the compositor of the
morphisms of small étale ringed topoi of `f` and `g`, followed by the transport
`AlgebraicGeometry.Space.pullbackModulesCompTransport` along the 2-isomorphism comparing their
composite with the morphism of ringed topoi of `f ≫ g`, is the composition comparison of the
pullback datum `AlgebraicGeometry.Space.toposPullbackData`, that is, the composition comparison of
Stacks 03LU read in the spelling the derived pullback is built from. -/
theorem pullbackModulesCompIso_inv_comp_pullbackModulesCompTransport_hom :
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS g)).inv ≫ (pullbackModulesCompTransport B S hS f g).hom =
      ((toposPullbackData B S hS).compIso f g).inv := by
  have hμ : modulePushforwardCompIso B S hS f g =
      eqToIso (modulePushforward_comp_eq B S hS f g) ≪≫
        (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
          (smallEtaleRingedToposHom B S hS g)).symm ≪≫
        pushforwardModulesCompTransport B S hS f g ≪≫
        eqToIso (pushforwardModules_eq_modulePushforward B S hS (f ≫ g)) := rfl
  have key := Stacks.CategoryTheory.inv_comp_hom_eq_whisker_comp_comp_inv_of_conjugateEquiv
    (toposModulesAdj B S hS f) (toposModulesAdj B S hS g)
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHomComp B S hS f g))
    (toposModulesAdj B S hS (f ≫ g))
    (Lf' := (toposModulePullbackData B S hS).pull f)
    (Lg' := (toposModulePullbackData B S hS).pull g)
    (Lfg' := (toposModulePullbackData B S hS).pull (f ≫ g))
    (modulePullbackAdjunction B S hS f) (modulePullbackAdjunction B S hS g)
    (modulePullbackAdjunction B S hS (f ≫ g))
    (pushforwardModules_eq_modulePushforward B S hS f)
    (pushforwardModules_eq_modulePushforward B S hS g)
    (pushforwardModules_eq_modulePushforward B S hS (f ≫ g))
    (toposPullbackModulesIso f) (toposPullbackModulesIso g) (toposPullbackModulesIso (f ≫ g))
    (conjugateEquiv_toposPullbackModulesIso_hom B S hS f)
    (conjugateEquiv_toposPullbackModulesIso_hom B S hS g)
    (conjugateEquiv_toposPullbackModulesIso_hom B S hS (f ≫ g))
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g))
    (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g))
    (RingedToposHom.conjugateEquiv_pullbackModulesCompIso_inv (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g))
    (pullbackModulesCompTransport B S hS f g) (pushforwardModulesCompTransport B S hS f g)
    (conjugateEquiv_pullbackModulesCompTransport_hom B S hS f g)
    (modulePushforward_comp_eq B S hS f g) (modulePushforwardCompIso B S hS f g) hμ
    ((toposModulePullbackData B S hS).compIso f g).inv
    (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _)
  exact key.trans (PullbackData.transport_compIso_inv _ _ _ f g).symm

/-- The inverse image of modules along the composite of the morphisms of small étale ringed topoi
of `f` and `g` is additive. -/
instance pullbackModules_smallEtaleRingedToposHomComp_additive :
    (smallEtaleRingedToposHomComp B S hS f g).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.pullbackModules_additive (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHomComp B S hS f g)

/-- The underived compositor equality on the homotopy categories of complexes: the inverse of the
composition comparison of `AlgebraicGeometry.Space.homotopyPullbackData` is the degreewise
compositor of the morphisms of small étale ringed topoi followed by the degreewise transport
`AlgebraicGeometry.Space.pullbackModulesCompTransport`. -/
theorem homotopyPullbackData_compIso_inv :
    ((homotopyPullbackData B S hS).compIso f g).inv =
      (Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.pullbackMapHomotopyCompIso
          (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g) ≪≫
        Stacks.Homology.mapHomotopyCategoryIso (pullbackModulesCompTransport B S hS f g)
          (ComplexShape.up ℤ)).hom :=
  PullbackData.homotopyIso_trans_homotopyCompIso_inv _ _
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g)).symm
    (pullbackModulesCompTransport B S hS f g) ((toposPullbackData B S hS).compIso f g)
    (pullbackModulesCompIso_inv_comp_pullbackModulesCompTransport_hom B S hS f g)

/-- The composition comparison `L g ⋙ L f ⟶ L (f ≫ g)` of the derived pullbacks induced by the
universal property of `L (f ≫ g)` is the comparison
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso` of Stacks 0D6D for algebraic
spaces. -/
theorem smallEtaleDerivedComp_eq_smallEtaleDerivedModulePullbackCompIso_hom :
    smallEtaleDerivedComp B S hS f g = (smallEtaleDerivedModulePullbackCompIso B S hS f g).hom := by
  refine Functor.leftDerived_ext (smallEtaleDerivedModulePullback B S hS (f ≫ g))
    (smallEtaleDerivedModulePullbackComparison B S hS (f ≫ g)) (smallEtaleModuleQuasiIso B S hS Z)
    _ _ _ (Stacks.CategoryTheory.whiskerLeft_comp_eq_of_app _ _ _ fun K => ?_)
  have h1 := smallEtaleDerivedComp_fac f g K
  open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
  have h2 := derivedPullbackCompComparison_app_comp_isoOfPullbackModulesIso_comparison_app
    (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g)
    (pullbackModulesCompTransport B S hS f g) K
  have h3 := congrArg (fun t => t.app K) (homotopyPullbackData_compIso_inv B S hS f g)
  have e := Stacks.Cohomology.DerivedPullbackCompositionOfToposHom.derivedPullbackCompIso_hom
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    (Z := smallEtaleRingedTopos B S hS Z) (smallEtaleRingedToposHom B S hS f)
    (smallEtaleRingedToposHom B S hS g)
  rw [h1, smallEtaleDerivedModulePullbackCompIso, Iso.trans_hom, NatTrans.comp_app,
    Category.assoc, e]
  refine Eq.trans ?_ h2.symm
  exact congrArg (fun t => (smallEtaleDerivedModulePullback B S hS f).map
      ((smallEtaleDerivedModulePullbackComparison B S hS g).app K) ≫
    (smallEtaleDerivedModulePullbackComparison B S hS f).app
      (((homotopyPullbackData B S hS).pull g).obj K) ≫ (toposQh X).map t) h3

/-- The two compositors of the derived pullback on algebraic spaces agree: the composition
comparison of the pullback pseudofunctor datum `AlgebraicGeometry.Space.toposDerivedPullbackData`,
induced by the universal property of the derived pullbacks from the composition comparison of
Stacks 03LU, is the inverse of the comparison
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso` of Stacks 0D6D, built from the
compositor of the morphisms of small étale ringed topoi and the transport
`AlgebraicGeometry.Space.pullbackModulesCompTransport`. -/
theorem toposDerivedPullbackData_compIso_eq_smallEtaleDerivedModulePullbackCompIso_symm :
    (toposDerivedPullbackData B S hS).compIso f g =
      (smallEtaleDerivedModulePullbackCompIso B S hS f g).symm :=
  congrArg Iso.symm
    (Iso.ext (smallEtaleDerivedComp_eq_smallEtaleDerivedModulePullbackCompIso_hom B S hS f g))

end AlgebraicGeometry.Space

end
