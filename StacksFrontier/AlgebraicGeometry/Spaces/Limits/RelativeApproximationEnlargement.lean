module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ArrowLimitComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteLimits
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteAffineReflects
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation

/-!
# Relative approximations descend along an enlargement of the big fppf site

Let `B ⊆ B'` be big fppf sites. A relative approximation (the conclusion of Stacks 0GS3) of the
inverse image on `B'` of a morphism `f` of algebraic spaces over `Spec ℤ` on `B` descends to a
relative approximation of `f`: its stages are quasi-separated algebraic spaces of finite type over
`Spec ℤ`, hence in the essential image of the inverse image functor (Stacks 04W1), which is fully
faithful; affineness of the transition morphisms and the limit property descend.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Finite type over `Spec ℤ` is invariant under isomorphism.** -/
theorem isFiniteType_terminal_of_iso {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
    {F G : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (h : IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from F)) :
    IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from G) :=
  ⟨(isLocallyOfFiniteType_terminal_iff_of_iso B _ hZ e).mp h.1,
    isQuasiCompact_of_isPullback B (⊤_ Scheme.{u}) hZ
      (IsPullback.of_horiz_isIso (fst := e.inv) (snd := terminal.from G)
        (f := terminal.from F) (g := 𝟙 _) ⟨terminal.hom_ext _ _⟩) h.2⟩

/-- The view over `Spec ℤ` of an algebraic space over `Spec ℤ` being of finite type is invariant
under isomorphism. -/
theorem isFiniteType_viewOverIntegers_of_iso {B : BigFppfSite.{u}}
    {hZ : B.Contains (⊤_ Scheme.{u})}
    {F G : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (h : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ F))) :
    IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ G)) :=
  isFiniteType_terminal_of_iso ((OverShriek.relocalizePresheafFunctor _).mapIso e) h

/-- Affineness of a morphism is invariant under conjugation by isomorphisms. -/
theorem isAffineHom_of_arrowIso {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G) (e₁ : F' ≅ F) (e₂ : G ≅ G')
    (hg : IsAffineHom B S hS g) : IsAffineHom B S hS (e₁.hom ≫ g ≫ e₂.hom) :=
  isAffineHom_comp B S hS _ _ (isAffineHom_of_isIso e₁.hom)
    (isAffineHom_comp B S hS _ _ hg (isAffineHom_of_isIso e₂.hom))

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B')
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Relative approximations descend along an enlargement of the big fppf site.** -/
theorem hasRelativeApproximation_of_changeBigSite {X Y : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
    (f : X ⟶ Y)
    (hR : HasRelativeApproximation B' (largerContains h hZ)
      ((changeBigSite B B' h (⊤_ Scheme.{u}) hZ).map f).hom) :
    HasRelativeApproximation B hZ f.hom := by
  classical
  obtain ⟨R⟩ := hR
  let _ := R.preorder
  let _ := R.nonempty
  let _ := R.isDirected
  let F := changeBigSite B B' h (⊤_ Scheme.{u}) hZ
  obtain ⟨hF⟩ := changeBigSite_fullyFaithful B B' h (⊤_ Scheme.{u}) hZ
  have _ := hF.full
  have _ := hF.faithful
  let hZ' := largerContains h hZ
  let P' := fun F : (BigFppfOver B' (⊤_ Scheme.{u}) hZ')ᵒᵖ ⥤ Type u =>
    IsAlgebraicSpace B' (⊤_ Scheme.{u}) hZ' F
  let ι' : AlgebraicSpaces B' (⊤_ Scheme.{u}) hZ' ⥤ _ := ObjectProperty.ι P'
  -- the two systems of stages, as algebraic spaces on the larger site
  let G : R.Iᵒᵖ ⥤ AlgebraicSpaces B' (⊤_ Scheme.{u}) hZ' :=
    ObjectProperty.lift _ (R.diagram ⋙ Arrow.leftFunc) R.isAlgebraicSpace_left
  let H : R.Iᵒᵖ ⥤ AlgebraicSpaces B' (⊤_ Scheme.{u}) hZ' :=
    ObjectProperty.lift _ (R.diagram ⋙ Arrow.rightFunc) R.isAlgebraicSpace_right
  have hG : ∀ j, F.essImage (G.obj j) := fun j =>
    mem_essImage_changeBigSite_of_isFiniteType B B' h hZ (G.obj j)
      (R.isAbsolutelyQuasiSeparated_left j) (R.isFiniteTypeOverIntegers_left j)
  have hH : ∀ j, F.essImage (H.obj j) := fun j =>
    mem_essImage_changeBigSite_of_isFiniteType B B' h hZ (H.obj j)
      (R.isAbsolutelyQuasiSeparated_right j) (R.isFiniteTypeOverIntegers_right j)
  -- descend them through the equivalence onto the essential image
  let E := F.toEssImage
  have _ : E.IsEquivalence := { }
  let L : R.Iᵒᵖ ⥤ AlgebraicSpaces B (⊤_ Scheme.{u}) hZ := ObjectProperty.lift _ G hG ⋙ E.inv
  let M : R.Iᵒᵖ ⥤ AlgebraicSpaces B (⊤_ Scheme.{u}) hZ := ObjectProperty.lift _ H hH ⋙ E.inv
  let eL : L ⋙ F ≅ G :=
    Functor.isoWhiskerLeft L F.toEssImageCompι.symm ≪≫
      Functor.isoWhiskerLeft (ObjectProperty.lift _ G hG)
        (Functor.isoWhiskerRight E.asEquivalence.counitIso F.essImage.ι)
  let eM : M ⋙ F ≅ H :=
    Functor.isoWhiskerLeft M F.toEssImageCompι.symm ≪≫
      Functor.isoWhiskerLeft (ObjectProperty.lift _ H hH)
        (Functor.isoWhiskerRight E.asEquivalence.counitIso F.essImage.ι)
  have nL {a b : R.Iᵒᵖ} (g : a ⟶ b) : F.map (L.map g) ≫ eL.hom.app b = eL.hom.app a ≫ G.map g :=
    eL.hom.naturality g
  have nM {a b : R.Iᵒᵖ} (g : a ⟶ b) : H.map g ≫ eM.inv.app b = eM.inv.app a ≫ F.map (M.map g) :=
    eM.inv.naturality g
  -- the arrows of the stages
  let α (j : R.Iᵒᵖ) : G.obj j ⟶ H.obj j := ObjectProperty.homMk (R.diagram.obj j).hom
  have hα {a b : R.Iᵒᵖ} (g : a ⟶ b) : G.map g ≫ α b = α a ≫ H.map g :=
    ObjectProperty.hom_ext _ (R.diagram.map g).w
  let β (j : R.Iᵒᵖ) : L.obj j ⟶ M.obj j := F.preimage (eL.hom.app j ≫ α j ≫ eM.inv.app j)
  have hFβ (j : R.Iᵒᵖ) : F.map (β j) = eL.hom.app j ≫ α j ≫ eM.inv.app j := F.map_preimage _
  have hβ {a b : R.Iᵒᵖ} (g : a ⟶ b) : L.map g ≫ β b = β a ≫ M.map g := F.map_injective (by
    simp only [F.map_comp, hFβ, Category.assoc, reassoc_of% (nL g), reassoc_of% (hα g), nM])
  -- the descended system of arrows
  let D : R.Iᵒᵖ ⥤ Arrow ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) :=
    { obj := fun j => Arrow.mk (β j).hom
      map := fun g => Arrow.homMk' (L.map g).hom (M.map g).hom
        (congrArg InducedCategory.Hom.hom (hβ g))
      map_id := fun j => Arrow.hom_ext _ _
        (by change (L.map (𝟙 j)).hom = 𝟙 _; rw [L.map_id]; rfl)
        (by change (M.map (𝟙 j)).hom = 𝟙 _; rw [M.map_id]; rfl)
      map_comp := fun f g => Arrow.hom_ext _ _
        (by change (L.map (f ≫ g)).hom = (L.map f).hom ≫ (L.map g).hom; rw [L.map_comp]; rfl)
        (by change (M.map (f ≫ g)).hom = (M.map f).hom ≫ (M.map g).hom; rw [M.map_comp]; rfl) }
  -- the legs of the cone of `f`
  let πL (j : R.Iᵒᵖ) : X ⟶ L.obj j :=
    F.preimage ((ObjectProperty.homMk (R.π.app j).left : F.obj X ⟶ G.obj j) ≫ eL.inv.app j)
  let πM (j : R.Iᵒᵖ) : Y ⟶ M.obj j :=
    F.preimage ((ObjectProperty.homMk (R.π.app j).right : F.obj Y ⟶ H.obj j) ≫ eM.inv.app j)
  have hFπL (j : R.Iᵒᵖ) : F.map (πL j) =
      (ObjectProperty.homMk (R.π.app j).left : F.obj X ⟶ G.obj j) ≫ eL.inv.app j :=
    F.map_preimage _
  have hFπM (j : R.Iᵒᵖ) : F.map (πM j) =
      (ObjectProperty.homMk (R.π.app j).right : F.obj Y ⟶ H.obj j) ≫ eM.inv.app j :=
    F.map_preimage _
  have nL' {a b : R.Iᵒᵖ} (g : a ⟶ b) : G.map g ≫ eL.inv.app b = eL.inv.app a ≫ F.map (L.map g) :=
    eL.inv.naturality g
  have hπLnat {a b : R.Iᵒᵖ} (g : a ⟶ b) : πL a ≫ L.map g = πL b := F.map_injective (by
    rw [F.map_comp, hFπL, hFπL, Category.assoc, ← nL', ← Category.assoc]
    congr 1
    exact ObjectProperty.hom_ext _
      ((congrArg CommaMorphism.left (R.π.naturality g)).symm.trans (Category.id_comp _)))
  have hπMnat {a b : R.Iᵒᵖ} (g : a ⟶ b) : πM a ≫ M.map g = πM b := F.map_injective (by
    rw [F.map_comp, hFπM, hFπM, Category.assoc, ← nM, ← Category.assoc]
    congr 1
    exact ObjectProperty.hom_ext _
      ((congrArg CommaMorphism.right (R.π.naturality g)).symm.trans (Category.id_comp _)))
  have hπw (j : R.Iᵒᵖ) : πL j ≫ β j = f ≫ πM j := F.map_injective (by
    rw [F.map_comp, F.map_comp, hFπL, hFπM, hFβ, Category.assoc, Iso.inv_hom_id_app_assoc,
      ← Category.assoc, ← Category.assoc]
    congr 1
    exact ObjectProperty.hom_ext _ (R.π.app j).w)
  -- the two cones of algebraic spaces, and their limit property
  let cL : Cone L :=
    Cone.mk X (NatTrans.mk πL fun _ _ g => (Category.id_comp _).trans (hπLnat g).symm)
  let cM : Cone M :=
    Cone.mk Y (NatTrans.mk πM fun _ _ g => (Category.id_comp _).trans (hπMnat g).symm)
  have hlimL : IsLimit ((ObjectProperty.ι _).mapCone cL) := by
    refine isLimitOfIsLimitChangeBigSite B B' h (⊤_ Scheme.{u}) hZ _ ?_
    refine (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerRight eL ι') _)
      ((Arrow.isLimitLeftOfIsLimit R.isLimit).ofIsoLimit (Cone.ext (Iso.refl _) fun j => ?_))
    change (R.π.app j).left = 𝟙 _ ≫ (F.map (πL j)).hom ≫ (eL.hom.app j).hom
    rw [Category.id_comp, hFπL]
    change (R.π.app j).left = ((ObjectProperty.homMk (R.π.app j).left : F.obj X ⟶ G.obj j) ≫
      eL.inv.app j ≫ eL.hom.app j).hom
    rw [Iso.inv_hom_id_app, Category.comp_id]
    rfl
  have hlimM : IsLimit ((ObjectProperty.ι _).mapCone cM) := by
    refine isLimitOfIsLimitChangeBigSite B B' h (⊤_ Scheme.{u}) hZ _ ?_
    refine (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerRight eM ι') _)
      ((Arrow.isLimitRightOfIsLimit initialIsInitial R.isLimit).ofIsoLimit
        (Cone.ext (Iso.refl _) fun j => ?_))
    change (R.π.app j).right = 𝟙 _ ≫ (F.map (πM j)).hom ≫ (eM.hom.app j).hom
    rw [Category.id_comp, hFπM]
    change (R.π.app j).right = ((ObjectProperty.homMk (R.π.app j).right : F.obj Y ⟶ H.obj j) ≫
      eM.inv.app j ≫ eM.hom.app j).hom
    rw [Iso.inv_hom_id_app, Category.comp_id]
    rfl
  -- the cone of `f` over the descended system of arrows
  let π : (Functor.const R.Iᵒᵖ).obj (Arrow.mk f.hom) ⟶ D :=
    { app := fun j => Arrow.homMk' (πL j).hom (πM j).hom (congrArg InducedCategory.Hom.hom (hπw j))
      naturality := fun a b g => Arrow.hom_ext _ _
        (by
          change 𝟙 _ ≫ (πL b).hom = (πL a).hom ≫ (L.map g).hom
          rw [Category.id_comp, ← hπLnat g]
          rfl)
        (by
          change 𝟙 _ ≫ (πM b).hom = (πM a).hom ≫ (M.map g).hom
          rw [Category.id_comp, ← hπMnat g]
          rfl) }
  have hlim : IsLimit (Cone.mk (Arrow.mk f.hom) π) :=
    Comma.fstSndJointlyReflectLimit hlimL hlimM
  -- the properties of the stages descend
  have hpropL (j : R.Iᵒᵖ) :=
    isAbsolutelyQuasiSeparated_and_isFiniteType_of_changeBigSite B B' h hZ (L.obj j)
      (isQuasiSeparatedOver_of_iso B' (⊤_ Scheme.{u}) hZ'
        ((OverShriek.relocalizePresheafFunctor _).mapIso (ι'.mapIso (eL.app j)).symm)
        (R.isAbsolutelyQuasiSeparated_left j))
      (isFiniteType_viewOverIntegers_of_iso (ι'.mapIso (eL.app j)).symm
        (R.isFiniteTypeOverIntegers_left j))
  have hpropM (j : R.Iᵒᵖ) :=
    isAbsolutelyQuasiSeparated_and_isFiniteType_of_changeBigSite B B' h hZ (M.obj j)
      (isQuasiSeparatedOver_of_iso B' (⊤_ Scheme.{u}) hZ'
        ((OverShriek.relocalizePresheafFunctor _).mapIso (ι'.mapIso (eM.app j)).symm)
        (R.isAbsolutelyQuasiSeparated_right j))
      (isFiniteType_viewOverIntegers_of_iso (ι'.mapIso (eM.app j)).symm
        (R.isFiniteTypeOverIntegers_right j))
  have haffL {a b : R.Iᵒᵖ} (g : a ⟶ b) : IsAffineHom B (⊤_ Scheme.{u}) hZ (L.map g).hom := by
    refine isAffineHom_of_isAffineHom_changeBigSite B B' h (⊤_ Scheme.{u}) hZ (L.map g) ?_
    have e : F.map (L.map g) = eL.hom.app a ≫ G.map g ≫ eL.inv.app b := by
      rw [nL', Iso.hom_inv_id_app_assoc]
    rw [e]
    exact isAffineHom_of_arrowIso (G.map g).hom (ι'.mapIso (eL.app a)) (ι'.mapIso (eL.app b)).symm
      (R.isAffineHom_left g)
  have haffM {a b : R.Iᵒᵖ} (g : a ⟶ b) : IsAffineHom B (⊤_ Scheme.{u}) hZ (M.map g).hom := by
    refine isAffineHom_of_isAffineHom_changeBigSite B B' h (⊤_ Scheme.{u}) hZ (M.map g) ?_
    have e : F.map (M.map g) = eM.hom.app a ≫ H.map g ≫ eM.inv.app b := by
      rw [nM, Iso.hom_inv_id_app_assoc]
    rw [e]
    exact isAffineHom_of_arrowIso (H.map g).hom (ι'.mapIso (eM.app a)) (ι'.mapIso (eM.app b)).symm
      (R.isAffineHom_right g)
  exact ⟨RelativeApproximation.mk (I := R.I) (diagram := D)
    (isAlgebraicSpace_left := fun j => (L.obj j).property)
    (isAlgebraicSpace_right := fun j => (M.obj j).property)
    (isAffineHom_left := haffL) (isAffineHom_right := haffM)
    (isAbsolutelyQuasiSeparated_left := fun j => (hpropL j).1)
    (isAbsolutelyQuasiSeparated_right := fun j => (hpropM j).1)
    (isFiniteTypeOverIntegers_left := fun j => (hpropL j).2)
    (isFiniteTypeOverIntegers_right := fun j => (hpropM j).2)
    (π := π) (isLimit := hlim)⟩

end AlgebraicGeometry.Space

end
