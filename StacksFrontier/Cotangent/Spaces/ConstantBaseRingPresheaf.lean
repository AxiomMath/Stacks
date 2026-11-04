module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionComp
public import StacksFrontier.Cotangent.Spaces.ConstantBaseRing

/-!
# The canonical map `Λ̲ ⟶ 𝒪_X` of an algebraic space over `Λ`, chart by chart

Let `X` be an algebraic space over `Spec Λ`. Stacks 08VG
(`AlgebraicGeometry.Space.cotangentComplexOverConstantSheafIso`) is stated for the canonical map
`Λ̲ ⟶ 𝒪_X` from the constant sheaf on `X_et`, the map adjoint to the structure map
`Λ → Γ(X, 𝒪_X)` (`AlgebraicGeometry.Space.constantStructureMapOfSpace`). This file proves that
on each étale scheme chart `U ⟶ X` that map is the chart's own `Λ`-algebra structure
`Γ(U ⟶ Spec Λ)`, so that it is the sheafification of the chartwise structure maps
`AlgebraicGeometry.Space.etaleConstantStructurePresheafMap`.

## Main results

* `AlgebraicGeometry.Space.toSheafify_comp_constantStructureMapOfSpace`: precomposed with the
  sheafification map of the constant presheaf, the canonical map `Λ̲ ⟶ 𝒪_X` is
  `U ↦ Γ(U ⟶ Spec Λ)`;
* `AlgebraicGeometry.Space.constantStructureMapOfSpace_eq`: the canonical map is
  `AlgebraicGeometry.Space.etaleConstantStructureMap`;
* `AlgebraicGeometry.Space.globalStructureMap_comp_res`: the structure map `Λ → Γ(X, 𝒪_X)`,
  restricted to a chart `U`, is `Γ(U ⟶ Spec Λ)`.

## The computation

Global sections are the sections over the final object of the spaces-étale site; their
restriction to a chart is `AlgebraicGeometry.Space.ringGlobalSectionsRes`. The adjunction between
the constant sheaf and global sections is computed on charts
(`AlgebraicGeometry.Space.toSheafify_comp_constantSheafGlobalSectionsAdj_homEquiv_symm_app`),
which needs the compatibility of the dense-subsite comparison of sheafifications with the
sheafification maps (`toSheafify_comp_sheafEquivSheafificationCompatibility_hom_app`, in the
namespace `CategoryTheory.Functor.IsDenseSubsite`).
The identification `Γ(Spec Λ, p_*𝒪_X) = Γ(X, 𝒪_X)` is read on charts through the comparison of the
direct image with spaces-étale base change
(`AlgebraicGeometry.Space.globalSectionsPushforwardIso_hom_app_comp_res`), and `p♯` on a
commutative diagram of charts is the pullback of regular functions
(`AlgebraicGeometry.Space.fSharp_app_pushforwardRing_chartRes`, from the chart projections of
Stacks 03G8).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Functor.IsDenseSubsite

variable {C D : Type*} [Category* C] [Category* D] (J : GrothendieckTopology C)
  (K : GrothendieckTopology D) (G : C ⥤ D) [G.IsDenseSubsite J K] (A : Type*) [Category* A]
  [(G.sheafPushforwardContinuous A J K).IsEquivalence] [HasWeakSheafify J A]
  [HasWeakSheafify K A]

/-- **The dense-subsite comparison of sheafifications respects the sheafification maps**: for a
presheaf `P` on `D`, the sheafification map of `G.op ⋙ P` followed by the comparison
`sheafify_J(G.op ⋙ P) ⟶ (sheafify_K P)|_C` of
`CategoryTheory.Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility` is the restriction
to `C` of the sheafification map of `P`. -/
theorem toSheafify_comp_sheafEquivSheafificationCompatibility_hom_app (P : Dᵒᵖ ⥤ A) :
    toSheafify J (G.op ⋙ P) ≫ ((sheafEquivSheafificationCompatibility J K G A).hom.app P).hom =
      Functor.whiskerLeft G.op (toSheafify K P) := by
  have h3 : Functor.whiskerLeft G.op ((sheafifyAdjunctionOfIsEquivalence J K G A).unit.app P) =
      toSheafify J (G.op ⋙ P) ≫
        ((G.sheafPushforwardContinuous A J K).asEquivalence.counitInv.app _).hom := by
    have := IsDenseSubsite.isLocallyFull J K G
    have := IsDenseSubsite.isCoverDense J K G
    rw [← Adjunction.homEquiv_id, sheafifyAdjunctionOfIsEquivalence,
      Adjunction.mkOfHomEquiv_homEquiv]
    show Functor.whiskerLeft G.op (IsCoverDense.restrictHomEquivHom
      (((sheafificationAdjunction J A).homEquiv _ _)
        (((G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction.homEquiv _ _)
          (𝟙 _)))) = _
    refine (IsCoverDense.restrictHomEquivHom.symm_apply_apply _).trans ?_
    rw [Adjunction.homEquiv_id, Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app]
    rfl
  have hα : (sheafifyOfIsEquivalenceCompIso J K G A).inv.app P =
      (G.sheafPushforwardContinuous A J K).asEquivalence.counitInv.app _ := by
    have h : (sheafifyOfIsEquivalenceCompIso J K G A).inv.app P =
        ((𝟙 _ ≫ (G.sheafPushforwardContinuous A J K).asEquivalence.counitInv.app
          ((presheafToSheaf J A).obj (G.op ⋙ P))) ≫ 𝟙 _) ≫ 𝟙 _ := rfl
    refine h.trans ?_
    simp only [Category.id_comp, Category.comp_id]
    rfl
  have hc : (sheafEquivSheafificationCompatibility J K G A).hom.app P =
      (sheafifyOfIsEquivalenceCompIso J K G A).inv.app P ≫
        (G.sheafPushforwardContinuous A J K).map
          (((sheafifyAdjunctionOfIsEquivalence J K G A).leftAdjointUniq
            (sheafificationAdjunction K A)).hom.app P) := rfl
  rw [hc, hα]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h3.symm).trans ?_
  exact (Functor.whiskerLeft_comp _ _ _).symm.trans (congrArg (Functor.whiskerLeft G.op)
    (Adjunction.unit_leftAdjointUniq_hom_app (sheafifyAdjunctionOfIsEquivalence J K G A)
      (sheafificationAdjunction K A) P))

/-- **The restriction of a constant sheaf to a dense subsite, on the constant presheaf**: the
identification of the constant sheaf on `C` with the restriction of the constant sheaf on `D`
(`CategoryTheory.Functor.IsDenseSubsite.constantSheafCompSheafPushforwardContinuousIso`) sends
the sheafification map of the constant presheaf on `C` to the restriction of that on `D`. -/
theorem toSheafify_comp_constantSheafCompSheafPushforwardContinuousIso_inv_app (M : A) :
    toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
        ((constantSheafCompSheafPushforwardContinuousIso J K G A).inv.app M).hom =
      Functor.whiskerLeft G.op (toSheafify K ((Functor.const Dᵒᵖ).obj M)) := by
  let n : (Functor.const Cᵒᵖ).obj M ⟶ G.op ⋙ (Functor.const Dᵒᵖ).obj M :=
    { app := fun _ => 𝟙 M }
  have hι : (constantSheafCompSheafPushforwardContinuousIso J K G A).inv.app M =
      ((presheafToSheaf J A).map n ≫ 𝟙 _) ≫
        (sheafEquivSheafificationCompatibility J K G A).hom.app ((Functor.const Dᵒᵖ).obj M) := rfl
  rw [hι, Category.comp_id]
  show toSheafify J _ ≫ sheafifyMap J n ≫ _ = _
  refine ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (toSheafify_naturality J n).symm)).trans ?_
  refine (Category.assoc _ _ _).trans ((congrArg (n ≫ ·)
    (toSheafify_comp_sheafEquivSheafificationCompatibility_hom_app J K G A _)).trans ?_)
  exact NatTrans.ext (funext fun _ => Category.id_comp _)

end CategoryTheory.Functor.IsDenseSubsite

namespace AlgebraicGeometry.Space

section General

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Sheafification of presheaves of commutative rings on the spaces-étale site, as the existence
of a left adjoint, at high priority: instance search otherwise tries an instance whose universes
it does not settle at this coefficient category. -/
private theorem hasWeakSheafify_spacesEtale_commRingCat' (X : AlgebraicSpaces B S hS) :
    HasWeakSheafify (SpacesEtale.topology B S hS X) CommRingCat.{u} :=
  (hasSheafify_spacesEtale_commRingCat B S hS X).isRightAdjoint

attribute [local instance high] hasWeakSheafify_spacesEtale_commRingCat'

/-- **The restriction of global sections to an étale scheme chart**, `Γ(Z, F) ⟶ F(U)`:
restriction along `U ⟶ Z` on the spaces-étale site, read through the counit of the comparison
equivalence of Stacks 03G1. -/
abbrev ringGlobalSectionsRes (Z : AlgebraicSpaces B S hS)
    (F : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}) (U : SmallEtale B S hS Z.1) :
    (ringGlobalSections Z).obj F ⟶ F.obj.obj (op U) :=
  ((ringRestrictionEquiv Z).inverse.obj F).obj.map
      ((SpacesEtale.isTerminal_idObj B S hS Z).from ((comparisonFunctor B S hS Z).obj U)).op ≫
    ((ringRestrictionEquiv Z).counitIso.hom.app F).hom.app (op U)

/-- The restriction of global sections to a chart is natural in the sheaf. -/
@[reassoc]
theorem ringGlobalSections_map_comp_res (Z : AlgebraicSpaces B S hS)
    {F F' : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}} (g : F ⟶ F')
    (U : SmallEtale B S hS Z.1) :
    (ringGlobalSections Z).map g ≫ ringGlobalSectionsRes Z F' U =
      ringGlobalSectionsRes Z F U ≫ g.hom.app (op U) := by
  have h₁ := ((ringRestrictionEquiv Z).inverse.map g).hom.naturality
    ((SpacesEtale.isTerminal_idObj B S hS Z).from ((comparisonFunctor B S hS Z).obj U)).op
  have h₂ := congrArg (fun m => m.hom.app (op U))
    ((ringRestrictionEquiv Z).counitIso.hom.naturality g)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁.symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

/-- **The adjoint of a map into global sections, on a chart**: for `g : M ⟶ Γ(Z, F)`, the map
of sheaves `M̲ ⟶ F` adjoint to `g` (`AlgebraicGeometry.Space.constantSheafGlobalSectionsAdj`),
precomposed with the sheafification map of the constant presheaf and evaluated at an étale scheme
chart `U`, is `g` followed by restriction to `U`. -/
theorem toSheafify_comp_constantSheafGlobalSectionsAdj_homEquiv_symm_app
    (Z : AlgebraicSpaces B S hS) {M : CommRingCat.{u}}
    {F : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}}
    (g : M ⟶ (ringGlobalSections Z).obj F) (U : SmallEtale B S hS Z.1) :
    (toSheafify (SmallEtale.topology B S hS Z.1) ((Functor.const _).obj M)).app (op U) ≫
        (((constantSheafGlobalSectionsAdj Z).homEquiv M F).symm g).hom.app (op U) =
      g ≫ ringGlobalSectionsRes Z F U := by
  let x := ((constantSheafAdj (SpacesEtale.topology B S hS Z) CommRingCat.{u}
    (SpacesEtale.isTerminal_idObj B S hS Z)).homEquiv M
      ((ringRestrictionEquiv Z).inverse.obj F)).symm g
  have e1 : ((constantSheafGlobalSectionsAdj Z).homEquiv M F).symm g =
      (constantSheafRestrictionIso Z).inv.app M ≫
        ((ringRestriction Z).map x ≫ (ringRestrictionEquiv Z).counitIso.hom.app F) := by
    refine (Adjunction.homEquiv_ofNatIsoLeft_symm_apply _ _ g).trans (congrArg (_ ≫ ·) ?_)
    rw [Adjunction.comp_homEquiv]
    exact (ringRestrictionEquiv Z).toAdjunction.homEquiv_counit _ _ x
  have e2 : toSheafify (SpacesEtale.topology B S hS Z)
        ((Functor.const (SpacesEtale B S hS Z)ᵒᵖ).obj M :
          (SpacesEtale B S hS Z)ᵒᵖ ⥤ CommRingCat.{u}) ≫ x.hom =
      (Functor.const _).map g ≫ (constantPresheafAdj CommRingCat.{u}
        (SpacesEtale.isTerminal_idObj B S hS Z)).counit.app
          ((ringRestrictionEquiv Z).inverse.obj F).obj := by
    have h := ((sheafificationAdjunction (SpacesEtale.topology B S hS Z) CommRingCat.{u}).homEquiv
      _ _).apply_symm_apply (((constantPresheafAdj CommRingCat.{u}
        (SpacesEtale.isTerminal_idObj B S hS Z)).homEquiv _ _).symm g)
    rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
    have hx : x = ((sheafificationAdjunction (SpacesEtale.topology B S hS Z)
        CommRingCat.{u}).homEquiv _ _).symm (((constantPresheafAdj CommRingCat.{u}
          (SpacesEtale.isTerminal_idObj B S hS Z)).homEquiv _ _).symm g) := by
      show ((((constantPresheafAdj CommRingCat.{u} (SpacesEtale.isTerminal_idObj B S hS Z)).comp
        (sheafificationAdjunction (SpacesEtale.topology B S hS Z) CommRingCat.{u})).homEquiv
          _ _).symm g) = _
      rw [Adjunction.comp_homEquiv]
      rfl
    rw [hx]
    exact h.trans ((constantPresheafAdj CommRingCat.{u}
      (SpacesEtale.isTerminal_idObj B S hS Z)).homEquiv_counit _ _ g)
  have e3 := congrArg (fun m => m.app (op U))
    (Functor.IsDenseSubsite.toSheafify_comp_constantSheafCompSheafPushforwardContinuousIso_inv_app
      (SmallEtale.topology B S hS Z.1) (SpacesEtale.topology B S hS Z) (comparisonFunctor B S hS Z)
      CommRingCat.{u} M)
  have e4 := congrArg (fun m => m.app (op ((comparisonFunctor B S hS Z).obj U))) e2
  rw [e1]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e3).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e4).trans (Category.assoc _ _ _))))

section Pushforward

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- Spaces-étale base change along `f` is continuous (Stacks 03G2), as a local instance. -/
private abbrev spacesBaseChangeIsContinuous :
    (spacesBaseChange B S hS f).functor.IsContinuous (SpacesEtale.topology B S hS Y)
      (SpacesEtale.topology B S hS X) :=
  (spacesBaseChange_isMorphismOfSites B S hS f).isContinuous

attribute [local instance] spacesBaseChangeIsContinuous

/-- The comparison `(f_*F)^♮ ⟶ (F^♮)` restricted along `X ×_Y (-)`, of sheaves on the
spaces-étale site of `Y`, from which `AlgebraicGeometry.Space.globalSectionsPushforwardIso` is
built, written as it is built. -/
private abbrev pushforwardInverseHom (F : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) :
    (ringRestrictionEquiv Y).inverse.obj
        ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.obj F) ⟶
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous CommRingCat.{u}
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj
          ((ringRestrictionEquiv X).inverse.obj F) :=
  (ringRestrictionEquiv Y).inverse.map (𝟙 _) ≫
    ((ringRestrictionEquiv Y).inverse.map
      ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map
        ((ringRestrictionEquiv X).counitIso.inv.app F)) ≫
      ((ringRestrictionEquiv Y).inverse.map (𝟙 _) ≫
        ((ringRestrictionEquiv Y).inverse.map
          ((smallEtaleRingedToposHom_pushforwardRing B S hS f).hom.app
            ((ringRestrictionEquiv X).inverse.obj F)) ≫
          (𝟙 _ ≫ (𝟙 _ ≫ ((ringRestrictionEquiv Y).unitIso.inv.app
            (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous
              CommRingCat.{u} (SpacesEtale.topology B S hS Y)
                (SpacesEtale.topology B S hS X)).obj
              ((ringRestrictionEquiv X).inverse.obj F)) ≫ 𝟙 _))))))

/-- The components of `AlgebraicGeometry.Space.globalSectionsPushforwardIso`, as they are built:
the comparison with base change at the final object of `Y`, then restriction along the
identification of `X` with `X ×_Y Y`. -/
private theorem globalSectionsPushforwardIso_hom_app
    (F : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) :
    (globalSectionsPushforwardIso f).hom.app F =
      𝟙 _ ≫ (((sheafSections (SpacesEtale.topology B S hS Y) CommRingCat.{u}).obj
          (op (SpacesEtale.idObj B S hS Y))).map (pushforwardInverseHom f F) ≫
        (𝟙 _ ≫ ((sheafSections (SpacesEtale.topology B S hS X) CommRingCat.{u}).map
          ((isTerminal_spacesBaseChange_idObj B S hS f).uniqueUpToIso
            (SpacesEtale.isTerminal_idObj B S hS X)).inv.op).app
          ((ringRestrictionEquiv X).inverse.obj F))) :=
  rfl

/-- The comparison from which `AlgebraicGeometry.Space.globalSectionsPushforwardIso` is built, read
back on the small étale site of `Y`:
the counit of the comparison equivalence of `Y`, followed by the direct image of the inverse
counit of `X` and the comparison of the direct image with base change. -/
private theorem ringRestriction_map_pushforwardInverseHom
    (F : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) :
    (ringRestriction Y).map (pushforwardInverseHom f F) =
      (ringRestrictionEquiv Y).counitIso.hom.app
          ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.obj F) ≫
        (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map
          ((ringRestrictionEquiv X).counitIso.inv.app F) ≫
        (smallEtaleRingedToposHom_pushforwardRing B S hS f).hom.app
          ((ringRestrictionEquiv X).inverse.obj F) := by
  have he : pushforwardInverseHom f F =
      (ringRestrictionEquiv Y).inverse.map
          ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map
            ((ringRestrictionEquiv X).counitIso.inv.app F) ≫
          (smallEtaleRingedToposHom_pushforwardRing B S hS f).hom.app
            ((ringRestrictionEquiv X).inverse.obj F)) ≫
        (ringRestrictionEquiv Y).unitIso.inv.app
          (((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous CommRingCat.{u}
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)).obj
              ((ringRestrictionEquiv X).inverse.obj F)) := by
    unfold pushforwardInverseHom
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    refine (congrArg (fun t => _ ≫ _ ≫ t) (Category.comp_id _)).trans ?_
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) ((ringRestrictionEquiv Y).inverse.map_comp _ _).symm)
  refine (congrArg (ringRestriction Y).map he).trans ?_
  refine ((ringRestrictionEquiv Y).functor.map_comp _ _).trans ?_
  refine (congrArg₂ (· ≫ ·) ((ringRestrictionEquiv Y).fun_inv_map _ _ _)
    ((ringRestrictionEquiv Y).counit_app_functor _).symm).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Iso.inv_hom_id_app (ringRestrictionEquiv Y).counitIso _)).trans
      (Category.comp_id _))))

/-- **Global sections of a direct image, restricted to a chart.** For an étale scheme chart `V` of
`Y`, an étale scheme chart `U` of `X` and a morphism `j` from `U` to `X ×_Y V` on the
spaces-étale site of `X`, the identification `Γ(Y, f_*F) = Γ(X, F)` followed by restriction to
`U` is restriction to `V`, followed by the comparison of the direct image with base change
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforwardRing`) and restriction along `j`. -/
theorem globalSectionsPushforwardIso_hom_app_comp_res
    (F : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (V : SmallEtale B S hS Y.1) (U : SmallEtale B S hS X.1)
    (j : (comparisonFunctor B S hS X).obj U ⟶
      (spacesBaseChange B S hS f).functor.obj ((comparisonFunctor B S hS Y).obj V)) :
    (globalSectionsPushforwardIso f).hom.app F ≫ ringGlobalSectionsRes X F U =
      ringGlobalSectionsRes Y
          ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.obj F) V ≫
        ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map
          ((ringRestrictionEquiv X).counitIso.inv.app F)).hom.app (op V) ≫
        ((smallEtaleRingedToposHom_pushforwardRing B S hS f).hom.app
          ((ringRestrictionEquiv X).inverse.obj F)).hom.app (op V) ≫
        ((ringRestrictionEquiv X).inverse.obj F).obj.map j.op ≫
        ((ringRestrictionEquiv X).counitIso.hom.app F).hom.app (op U) := by
  let G := (ringRestrictionEquiv X).inverse.obj F
  let tX := (SpacesEtale.isTerminal_idObj B S hS X).from ((comparisonFunctor B S hS X).obj U)
  let tY := (SpacesEtale.isTerminal_idObj B S hS Y).from ((comparisonFunctor B S hS Y).obj V)
  let uI := ((isTerminal_spacesBaseChange_idObj B S hS f).uniqueUpToIso
    (SpacesEtale.isTerminal_idObj B S hS X)).inv
  let E := pushforwardInverseHom f F
  let L := ((ringRestrictionEquiv Y).inverse.obj
    ((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.obj F)).obj.map tY.op
  have h1 : tX ≫ uI = j ≫ (spacesBaseChange B S hS f).functor.map tY :=
    (isTerminal_spacesBaseChange_idObj B S hS f).hom_ext _ _
  have h2 : G.obj.map uI.op ≫ G.obj.map tX.op =
      G.obj.map ((spacesBaseChange B S hS f).functor.map tY).op ≫ G.obj.map j.op :=
    (G.obj.map_comp _ _).symm.trans
      ((congrArg (fun m => G.obj.map (Quiver.Hom.op m)) h1).trans (G.obj.map_comp _ _))
  have h3 : E.hom.app (op (SpacesEtale.idObj B S hS Y)) ≫
        G.obj.map ((spacesBaseChange B S hS f).functor.map tY).op =
      L ≫ E.hom.app (op ((comparisonFunctor B S hS Y).obj V)) :=
    (E.hom.naturality tY.op).symm
  have h4 := congrArg (fun m => m.hom.app (op V))
    (ringRestriction_map_pushforwardInverseHom f F)
  refine (congrArg (· ≫ ringGlobalSectionsRes X F U)
    (globalSectionsPushforwardIso_hom_app f F)).trans ?_
  refine (congrArg (· ≫ _)
    ((Category.id_comp _).trans (congrArg (_ ≫ ·) (Category.id_comp _)))).trans ?_
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)).trans ?_
  refine (congrArg (fun m => E.hom.app (op (SpacesEtale.idObj B S hS Y)) ≫ (m ≫ _)) h2).trans ?_
  refine ((congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg (· ≫ _) h3).trans ?_
  refine (congrArg (fun m => (L ≫ m) ≫ _) h4).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _)))).trans (Category.assoc _ _ _).symm)

end Pushforward

end General

section PushforwardChart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y)

attribute [local instance] spacesBaseChangeIsContinuous

/-- **The structure map, read on a chart diagram through the base-change comparison.** For a
commutative diagram `d` of étale scheme charts over `f : X ⟶ Y`, with vertical morphism
`d.g : d.U ⟶ d.V`, and a regular function `b` on `d.V`: the image of `b` under `f♯`, read through
the comparison of the direct image with spaces-étale base change
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforwardRing`) and restricted to `d.U`, is
the pullback of `b` along `d.g`. -/
theorem fSharp_app_pushforwardRing_chartRes (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (b : (smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)) :
    ((ringRestrictionEquiv X).counitIso.hom.app (smallEtaleRingedTopos B S hS X).O).hom.app
        (op d.U)
      (((ringRestrictionEquiv X).inverse.obj (smallEtaleRingedTopos B S hS X).O).obj.map
        (baseChangeArrowOfChartDiagram B S hS f d).op
        (((smallEtaleRingedToposHom_pushforwardRing B S hS f).hom.app
          ((ringRestrictionEquiv X).inverse.obj (smallEtaleRingedTopos B S hS X).O)).hom.app
            (op d.V)
          (((smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing.map
            ((ringRestrictionEquiv X).counitIso.inv.app (smallEtaleRingedTopos B S hS X).O)).hom.app
              (op d.V)
            ((smallEtaleRingedToposHom B S hS f).fSharp.hom.app (op d.V) b)))) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map d.g).op b := by
  let O := (smallEtaleRingedTopos B S hS X).O
  let G := (ringRestrictionEquiv X).inverse.obj O
  let pf := (smallEtaleRingedToposHom B S hS f).toToposHom.pushforwardRing
  let ε := (ringRestrictionEquiv X).counitIso
  let y := (smallEtaleRingedToposHom B S hS f).fSharp.hom.app (op d.V) b
  let c := (pf.map (ε.inv.app O)).hom.app (op d.V) y
  let j : StructuredArrow (op (chartBaseChange B S hS f d.V)) (comparisonFunctor B S hS X).op :=
    StructuredArrow.mk (Y := op d.U) (baseChangeArrowOfChartDiagram B S hS f d).op
  let π := directImageChartProjection B S hS f d.V j
  have s1 := congrArg (fun m => m.hom.app (op d.V) c)
    (smallEtaleRingedToposHom_pushforwardRing_forget B S hS f G)
  have s2 := directImageChartProjection_comparison B S hS f d.V j
    ((sheafCompose (SpacesEtale.topology B S hS X) (forget CommRingCat.{u})).obj G) c
  have s3 := directImageChartProjection_map B S hS f d.V j
    ((sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map (ε.hom.app O)) c
  have s4 := congrArg (fun m => m.hom.app (op d.V) c)
    (MorphismOfTopoi.pushforwardRing_map_forget (smallEtaleRingedToposHom B S hS f).toToposHom
      (ε.hom.app O))
  have s5 : (pf.map (ε.hom.app O)).hom.app (op d.V) c = y := by
    have e : pf.map (ε.inv.app O) ≫ pf.map (ε.hom.app O) = 𝟙 _ :=
      (pf.map_comp _ _).symm.trans ((congrArg pf.map (Iso.inv_hom_id_app _ _)).trans (pf.map_id _))
    have h := congrArg (fun m => m.hom.app (op d.V) y) e
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
    exact h
  have s6 := congrArg (fun m => m.hom.app (op d.V) b) (forgetRing_map_fSharp B S hS f)
  have s7 := directImageChartProjection_structureSharpSet_chartDiagram B S hS f d b
  exact (congrArg (fun x => (ε.hom.app O).hom.app (op d.U)
      (G.obj.map (baseChangeArrowOfChartDiagram B S hS f d).op x)) s1).trans
    ((congrArg (fun x => (ε.hom.app O).hom.app (op d.U) x) s2).symm.trans (s3.symm.trans
      ((congrArg (fun x => π.app ((sheafCompose (SmallEtale.topology B S hS X.1)
          (forget CommRingCat.{u})).obj O) x) (s4.symm.trans s5)).trans
        ((congrArg (fun x => π.app (structureSetSheaf B S hS X) x) s6).trans s7))))

end PushforwardChart

section Canonical

open PolynomialChart

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ))) (X : AlgebraicSpaces B (Spec (CommRingCat.of Λ)) hS)

/-- An étale scheme chart `U` of `X` over the identity chart of `Spec Λ`: the commutative
diagram of charts over `p : X ⟶ Spec Λ` whose vertical morphism is the structure morphism
`U ⟶ Spec Λ`. -/
def specChartDiagram (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X.1) :
    ChartDiagram B (Spec (CommRingCat.of Λ)) hS X.1 (specSpace Λ B hS).1
      (structureToSpec Λ B hS X).hom where
  U := U
  V := idEtaleChart B (Spec (CommRingCat.of Λ)) hS
    (BigFppfOver.terminalObj B (Spec (CommRingCat.of Λ)) hS)
  g := (Over.mkIdTerminal (X := B.obj hS)).from _
  comm := ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).hom_ext _ _

/-- **The structure map `Λ → Γ(X, 𝒪_X)`, restricted to a chart**, is the chart's own
`Λ`-algebra structure `Γ(U ⟶ Spec Λ)`. -/
theorem globalStructureMap_comp_res (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X.1) :
    globalStructureMap Λ B hS X ≫
        ringGlobalSectionsRes X (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).O U =
      (etaleConstantStructurePresheafMap Λ B hS X.1).app (op U) := by
  let d := specChartDiagram Λ B hS X U
  let O := (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).O
  let G := (ringRestrictionEquiv X).inverse.obj O
  let p := smallEtaleRingedToposHom B (Spec (CommRingCat.of Λ)) hS (structureToSpec Λ B hS X)
  let P := smallEtaleRingedToposHom_pushforwardRing B (Spec (CommRingCat.of Λ)) hS
    (structureToSpec Λ B hS X)
  let st := etaleConstantStructurePresheafMap Λ B hS (specSpace Λ B hS).1
  let Q : (p.toToposHom.pushforwardRing.obj O).obj.obj (op d.V) → _ := fun y =>
    ((ringRestrictionEquiv X).counitIso.hom.app O).hom.app (op U)
      (G.obj.map (baseChangeArrowOfChartDiagram B _ hS _ d).op ((P.hom.app G).hom.app (op d.V)
        ((p.toToposHom.pushforwardRing.map ((ringRestrictionEquiv X).counitIso.inv.app O)).hom.app
          (op d.V) y)))
  have hB := globalSectionsPushforwardIso_hom_app_comp_res (structureToSpec Λ B hS X) O d.V U
    (baseChangeArrowOfChartDiagram B _ hS _ d)
  have hN := ringGlobalSections_map_comp_res (specSpace Λ B hS) p.fSharp d.V
  have hA : specGlobalStructureMap Λ B hS ≫ ringGlobalSectionsRes (specSpace Λ B hS)
        (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS (specSpace Λ B hS)).O d.V =
      st.app (op d.V) := by
    have e := ((constantSheafGlobalSectionsAdj (specSpace Λ B hS)).homEquiv _ _).symm_apply_apply
      (etaleConstantStructureMap Λ B hS (specSpace Λ B hS).1 (specSpace Λ B hS).2)
    exact (toSheafify_comp_constantSheafGlobalSectionsAdj_homEquiv_symm_app _
      (specGlobalStructureMap Λ B hS) d.V).symm.trans
        ((congrArg (fun m => (toSheafify _ _).app (op d.V) ≫ m.hom.app (op d.V)) e).trans
          (congrArg (fun m => m.app (op d.V))
            (toSheafify_comp_etaleConstantStructureMap Λ B hS _ (specSpace Λ B hS).2)))
  have hO : (BigFppfOver.toScheme B (Spec (CommRingCat.of Λ)) hS).map d.g ≫
      openPartToBase Λ B hS (specSpace Λ B hS).1 d.V = openPartToBase Λ B hS X.1 U :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w d.g))
  ext a
  have hC := fSharp_app_pushforwardRing_chartRes B (Spec (CommRingCat.of Λ)) hS
    (structureToSpec Λ B hS X) d (st.app (op d.V) a)
  refine (ConcreteCategory.congr_hom hB (((ringGlobalSections (specSpace Λ B hS)).map p.fSharp)
    (specGlobalStructureMap Λ B hS a))).trans ?_
  refine (congrArg Q (ConcreteCategory.congr_hom hN (specGlobalStructureMap Λ B hS a))).trans ?_
  refine (congrArg (fun y => Q (p.fSharp.hom.app (op d.V) y))
    (ConcreteCategory.congr_hom hA a)).trans (hC.trans ?_)
  show Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (CommRingCat.of Λ)) hS).map d.g).op
    (Scheme.Γ.map (openPartToBase Λ B hS (specSpace Λ B hS).1 d.V).op
      ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv a)) =
    Scheme.Γ.map (openPartToBase Λ B hS X.1 U).op ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv a)
  refine Eq.trans ?_ (congrArg (fun (m : _ ⟶ Spec (CommRingCat.of Λ)) => Scheme.Γ.map m.op
    ((Scheme.ΓSpecIso (CommRingCat.of Λ)).inv a)) hO)
  exact (ConcreteCategory.congr_hom (Scheme.Γ.map_comp _ _) _).symm

/-- **The canonical map `Λ̲ ⟶ 𝒪_X` on sections of the constant presheaf**: precomposed with the
sheafification map of the constant presheaf, `AlgebraicGeometry.Space.constantStructureMapOfSpace`
is, on each étale scheme chart `U` of `X`, the chart's own `Λ`-algebra structure
`Γ(U ⟶ Spec Λ)` (`AlgebraicGeometry.Space.etaleConstantStructurePresheafMap`). -/
theorem toSheafify_comp_constantStructureMapOfSpace :
    toSheafify (SmallEtale.topology B (Spec (CommRingCat.of Λ)) hS X.1)
        ((Functor.const (SmallEtale B (Spec (CommRingCat.of Λ)) hS X.1)ᵒᵖ).obj
          (CommRingCat.of Λ)) ≫ (constantStructureMapOfSpace Λ B hS X).hom =
      etaleConstantStructurePresheafMap Λ B hS X.1 :=
  NatTrans.ext (funext fun U =>
    (toSheafify_comp_constantSheafGlobalSectionsAdj_homEquiv_symm_app X
      (globalStructureMap Λ B hS X) U.unop).trans (globalStructureMap_comp_res Λ B hS X U.unop))

/-- **The canonical map `Λ̲ ⟶ 𝒪_X` is the sheafification of the chartwise structure map**: the
map adjoint to the structure map `Λ → Γ(X, 𝒪_X)` is
`AlgebraicGeometry.Space.etaleConstantStructureMap`. -/
theorem constantStructureMapOfSpace_eq :
    constantStructureMapOfSpace Λ B hS X = etaleConstantStructureMap Λ B hS X.1 X.2 :=
  ObjectProperty.hom_ext _ (sheafify_hom_ext _ _ _
    (smallEtaleRingedTopos B (Spec (CommRingCat.of Λ)) hS X).O.property
    ((toSheafify_comp_constantStructureMapOfSpace Λ B hS X).trans
      (toSheafify_comp_etaleConstantStructureMap Λ B hS X.1 X.2).symm))

end Canonical

end AlgebraicGeometry.Space
