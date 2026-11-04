module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Algebra
public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Transpose
public import StacksFrontier.CategoryTheory.Sites.RightAdjointSections

/-!
# Sections of a direct image along a morphism of test objects, on Zariski opens

Let `τ : T' ⟶ T` be a morphism of the big fppf category over `S` and let `φ` be the morphism of
represented algebraic spaces it induces.  For a Zariski open `O` of the scheme underlying `T`
the base change along `φ` of the étale chart cut out by `O` is the étale chart cut out by the
preimage open `τ⁻¹(O)`.  Consequently the sections over `O` of the direct image `φ_* F` of a
sheaf of sets on the small étale site of `yoneda.obj T'` are the sections of `F` over `τ⁻¹(O)`,
naturally in `F`.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeSelfOpensIso`: the base change along `φ` of the chart of
  `O` is the chart of `τ⁻¹(O)`.
* `AlgebraicGeometry.Space.directImageSelfOpensSection`: the identification
  `(φ_* F)(O) ⟶ F(τ⁻¹(O))`.

## Main results

* `AlgebraicGeometry.Space.directImageSelfOpensSection_map`: it is natural in the sheaf.
* `AlgebraicGeometry.Space.subsingleton_inverseImage_selfOpens`: the sheaf corepresenting the
  sections over `O` of a direct image has at most one section anywhere, so any two natural maps
  out of those sections agree (`Stacks.Sites.SheafSection.natural_family_ext`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites.SheafSection
open scoped Stacks.Sites.SheafSection.OfEssentiallySmall

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The preimage of a Zariski open of the scheme underlying `T` along the scheme morphism of
`τ : T' ⟶ T`. -/
abbrev preimageOpens {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens) :
    (chartScheme (idEtaleChart B S hS T')).Opens :=
  ((BigFppfOver.toScheme B S hS).map τ) ⁻¹ᵁ O

/-- **The base change of the chart of a Zariski open is the chart of the preimage open.** -/
def baseChangeSelfOpensIso {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens) :
    (smallBaseChange B S hS (representedSpaceMap B S hS τ)
        (relativelyRepresentable_yoneda_map B S hS τ)).obj
        ((selfOpensFunctor B S hS T).obj O) ≅
      (selfOpensFunctor B S hS T').obj (preimageOpens τ O) :=
  (representedSmallEtaleEquivalence B S hS T').unitIso.app _ ≪≫
    (representedSmallEtaleEquivalence B S hS T').inverse.mapIso
      ((representedSmallEtaleBaseChangeIso B S hS τ
          (relativelyRepresentable_yoneda_map B S hS τ)).app _ ≪≫
        (smallEtaleBaseChange (associatedBigEtaleSite B) τ.left).mapIso
          ((representedSmallEtaleEquivalence B S hS T).counitIso.app _) ≪≫
        (SmallEtale.baseChangeOpensObjIso (associatedBigEtaleSite B) τ.left O).symm)

/-- The morphism of small étale ringed topoi of a morphism of test objects. -/
abbrev testToposHom {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) :=
  smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ)

/-- **Sections over a Zariski open of a direct image along a morphism of test objects.** The
sections over `O` of `φ_* F` are the sections of `F` over the base change of the chart of `O`,
which is the chart of `τ⁻¹(O)`. -/
def directImageSelfOpensSection {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (F : Sheaf (SmallEtale.topology B S hS (yoneda.obj T')) (Type u))
    (x : ((testToposHom τ).toToposHom.pushforward.obj F).obj.obj
      (op ((selfOpensFunctor B S hS T).obj O))) :
    F.obj.obj (op ((selfOpensFunctor B S hS T').obj (preimageOpens τ O))) :=
  F.obj.map (baseChangeSelfOpensIso τ O).inv.op
    (((smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS τ) ≪≫
      chartRanIso B S hS (representedSpaceMap B S hS τ)
        (relativelyRepresentable_yoneda_map B S hS τ)).hom.app F).hom.app _ x)

/-- The identification of sections is natural in the sheaf. -/
theorem directImageSelfOpensSection_map {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    {F F' : Sheaf (SmallEtale.topology B S hS (yoneda.obj T')) (Type u)} (g : F ⟶ F')
    (x : ((testToposHom τ).toToposHom.pushforward.obj F).obj.obj
      (op ((selfOpensFunctor B S hS T).obj O))) :
    directImageSelfOpensSection τ O F'
        (((testToposHom τ).toToposHom.pushforward.map g).hom.app _ x) =
      g.hom.app _ (directImageSelfOpensSection τ O F x) := by
  have h1 := congrArg (fun k => k.hom.app (op ((selfOpensFunctor B S hS T).obj O)) x)
    ((smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS τ) ≪≫
      chartRanIso B S hS (representedSpaceMap B S hS τ)
        (relativelyRepresentable_yoneda_map B S hS τ)).hom.naturality g)
  exact (congrArg (F'.obj.map (baseChangeSelfOpensIso τ O).inv.op) h1).trans
    (NatTrans.naturality_apply g.hom _ _).symm

/-- **The sheaf corepresenting the sections over a Zariski open of a direct image is
subterminal.** It is the inverse image of the sheafified representable of the chart of the open,
which is a subobject of the terminal sheaf, morphisms into the chart of an open being unique;
inverse images are left exact. -/
theorem subsingleton_inverseImage_selfOpens {T : BigFppfOver B S hS}
    {P : AlgebraicSpaces B S hS} (φ : P ⟶ yonedaSpace B S hS T)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens) (Q : (SmallEtale B S hS P.1)ᵒᵖ) :
    Subsingleton (((smallEtaleRingedToposHom B S hS φ).toToposHom.inverseImage.obj
      ((presheafToSheaf (SmallEtale.topology B S hS (yoneda.obj T)) (Type u)).obj
        (smallYoneda.{u} ((selfOpensFunctor B S hS T).obj O)))).obj.obj Q) := by
  have := (smallEtaleRingedToposHom B S hS φ).toToposHom.preservesFiniteLimits
  exact subsingleton_obj_of_subsingleton_hom
    (L := (smallEtaleRingedToposHom B S hS φ).toToposHom.inverseImage)
    (op ((selfOpensFunctor B S hS T).obj O))
    (fun W => subsingleton_hom_selfOpensFunctor B S hS T W O) Q

/-- The identification of sections, as a natural transformation of section functors. -/
def directImageSelfOpensNatTrans {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens) :
    (testToposHom τ).toToposHom.pushforward ⋙
        Sheaf.sectionsFunctor (SmallEtale.topology B S hS (yoneda.obj T))
          (op ((selfOpensFunctor B S hS T).obj O)) ⟶
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS (yoneda.obj T'))
        (op ((selfOpensFunctor B S hS T').obj (preimageOpens τ O))) where
  app F := TypeCat.ofHom (directImageSelfOpensSection τ O F)
  naturality _ _ g := by
    ext x
    exact directImageSelfOpensSection_map τ O g x

/-- The component of `directImageSelfOpensNatTrans` at a sheaf `F` sends a section `x` to
`directImageSelfOpensSection τ O F x`. -/
theorem directImageSelfOpensNatTrans_app {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (F : Sheaf (SmallEtale.topology B S hS (yoneda.obj T')) (Type u)) (x) :
    (directImageSelfOpensNatTrans τ O).app F x = directImageSelfOpensSection τ O F x := rfl

/-- The structure map of the chart of a Zariski open, on sections: a function on the open,
read as a global function on the open subscheme and transported to the chart. -/
theorem selfOpensStructureMap_hom_app (T : BigFppfOver B S hS)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (r : Γ((BigFppfOver.toScheme B S hS).obj T, O)) :
    (selfOpensStructureMap B S hS T).hom.app (op O) r =
      (representedSchemeStructureSheaf B S hS T).obj.map
        ((representedSmallEtaleEquivalence B S hS T).counit.app
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property O)).op
        ((forget₂ CommRingCat RingCat).map (Scheme.Opens.topIso O).inv r) :=
  rfl

/-- The base change of the chart of an open, read on schemes, lies over the restriction of
the scheme morphism to the open. -/
theorem baseChangeSelfOpensIso_inv_snd_counit {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
  (O : ((BigFppfOver.toScheme B S hS).obj T).Opens) :
    (BigFppfOver.toScheme B S hS).map (baseChangeSelfOpensIso τ O).inv.hom.left ≫
    (BigFppfOver.toScheme B S hS).map ((relativelyRepresentable_yoneda_map B S hS τ).snd
        ((selfOpensFunctor B S hS T).obj O).1.hom) ≫
      (associatedBigEtaleSite B).inclusion.map
        ((representedSmallEtaleEquivalence B S hS T).counit.app
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property O)).hom.left =
    (associatedBigEtaleSite B).inclusion.map
        ((representedSmallEtaleEquivalence B S hS T').counit.app
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property
            (preimageOpens τ O))).hom.left ≫
      ((BigFppfOver.toScheme B S hS).map τ).resLE O (preimageOpens τ O) le_rfl := by
  refine (cancel_mono O.ι).1 ?_
  have ha : ∀ (U : BigFppfOver B S hS) (W : ((BigFppfOver.toScheme B S hS).obj U).Opens),
      (associatedBigEtaleSite B).inclusion.map
          ((representedSmallEtaleEquivalence B S hS U).counit.app
            (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj U) U.left.property W)).hom.left ≫ W.ι =
        (BigFppfOver.toScheme B S hS).map
          (yonedaEquiv ((selfOpensFunctor B S hS U).obj W).1.hom) := by
    intro U W
    exact ((associatedBigEtaleSite B).inclusion.map_comp _ _).symm.trans
      (congrArg (associatedBigEtaleSite B).inclusion.map
        (Over.w ((representedSmallEtaleEquivalence B S hS U).counit.app
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property W)).hom))
  have hsq : yonedaEquiv ((relativelyRepresentable_yoneda_map B S hS τ).fst
        ((selfOpensFunctor B S hS T).obj O).1.hom) ≫ τ =
      (relativelyRepresentable_yoneda_map B S hS τ).snd
        ((selfOpensFunctor B S hS T).obj O).1.hom ≫
        yonedaEquiv ((selfOpensFunctor B S hS T).obj O).1.hom := by
    have := congrArg yonedaEquiv
      ((relativelyRepresentable_yoneda_map B S hS τ).w ((selfOpensFunctor B S hS T).obj O).1.hom)
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map] at this
    exact this
  have hκ : (baseChangeSelfOpensIso τ O).inv.hom.left ≫
      yonedaEquiv ((relativelyRepresentable_yoneda_map B S hS τ).fst
        ((selfOpensFunctor B S hS T).obj O).1.hom) =
      yonedaEquiv ((selfOpensFunctor B S hS T').obj (preimageOpens τ O)).1.hom :=
    (yonedaEquiv_naturality _ _).trans
      (congrArg yonedaEquiv (CostructuredArrow.w (baseChangeSelfOpensIso τ O).inv.hom))
  have h1 := ha T O
  have h2 := ha T' (preimageOpens τ O)
  have e1 : ((BigFppfOver.toScheme B S hS).map (baseChangeSelfOpensIso τ O).inv.hom.left ≫
      (BigFppfOver.toScheme B S hS).map ((relativelyRepresentable_yoneda_map B S hS τ).snd
        ((selfOpensFunctor B S hS T).obj O).1.hom) ≫
      (associatedBigEtaleSite B).inclusion.map
        ((representedSmallEtaleEquivalence B S hS T).counit.app
          (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property O)).hom.left) ≫ O.ι =
      (BigFppfOver.toScheme B S hS).map
        (yonedaEquiv ((selfOpensFunctor B S hS T').obj (preimageOpens τ O)).1.hom ≫ τ) := by
    refine (Category.assoc _ _ _).trans ((congrArg _ ((Category.assoc _ _ _).trans
      (congrArg _ h1))).trans ?_)
    refine ((congrArg _ ((BigFppfOver.toScheme B S hS).map_comp _ _).symm).trans
      ((BigFppfOver.toScheme B S hS).map_comp _ _).symm).trans (congrArg _ ?_)
    exact (congrArg _ hsq.symm).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ τ) hκ))
  refine e1.trans ?_
  refine ((BigFppfOver.toScheme B S hS).map_comp _ _).trans ?_
  refine (congrArg (· ≫ (BigFppfOver.toScheme B S hS).map τ) h2.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg _ (Scheme.Hom.resLE_comp_ι _ _).symm

/-- **The structure map, on sections over a Zariski open.** -/
theorem directImageSelfOpensSection_structureSharp {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (r : Γ((BigFppfOver.toScheme B S hS).obj T, O)) :
    directImageSelfOpensSection τ O
        (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS (yonedaSpace B S hS T')).O))
        ((structureSharp B S hS (representedSpaceMap B S hS τ)).hom.app _
          ((selfOpensStructureMap B S hS T).hom.app (op O) r)) =
      (selfOpensStructureMap B S hS T').hom.app (op (preimageOpens τ O))
        (((BigFppfOver.toScheme B S hS).map τ).app O r) := by
  have h := congrArg (fun k => (k.hom.app (op ((selfOpensFunctor B S hS T).obj O)))
      ((selfOpensStructureMap B S hS T).hom.app (op O) r))
    (structureSharp_comp_chartRanIso B S hS (representedSpaceMap B S hS τ)
      (relativelyRepresentable_yoneda_map B S hS τ))
  change _ = (ConcreteCategory.hom ((smallBaseChangeSharp B S hS (representedSpaceMap B S hS τ)
      (relativelyRepresentable_yoneda_map B S hS τ)).hom.app _)) _ at h
  refine (congrArg ((Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedTopos B S hS (yonedaSpace B S hS T')).O)).obj.map
        (baseChangeSelfOpensIso τ O).inv.op) h).trans ?_
  show Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (baseChangeSelfOpensIso τ O).inv.hom.left).op
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        ((relativelyRepresentable_yoneda_map B S hS τ).snd
          ((selfOpensFunctor B S hS T).obj O).1.hom)).op
        (Scheme.Γ.map ((associatedBigEtaleSite B).inclusion.map
          ((representedSmallEtaleEquivalence B S hS T).counit.app
            (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T) T.left.property O)).hom.left).op
          ((Scheme.Opens.topIso O).inv r))) =
    Scheme.Γ.map ((associatedBigEtaleSite B).inclusion.map
          ((representedSmallEtaleEquivalence B S hS T').counit.app
            (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
              ((BigFppfOver.toScheme B S hS).obj T') T'.left.property
              (preimageOpens τ O))).hom.left).op
      ((Scheme.Opens.topIso (preimageOpens τ O)).inv
        (((BigFppfOver.toScheme B S hS).map τ).app O r))
  have hl := Scheme.Opens.topIso_inv_appTop_of_comp ((BigFppfOver.toScheme B S hS).map τ) O
    (((BigFppfOver.toScheme B S hS).map τ).resLE O (preimageOpens τ O) le_rfl)
    (Scheme.Hom.resLE_comp_ι _ _)
  have hkey := baseChangeSelfOpensIso_inv_snd_counit τ O
  have hr := congrArg (fun g => g.appTop ((Scheme.Opens.topIso O).inv r)) hkey
  simp only [Scheme.Hom.comp_appTop] at hr
  refine hr.trans ?_
  have hl' := congrArg (fun g => (ConcreteCategory.hom g) r) hl
  simp only [CommRingCat.comp_apply] at hl'
  exact congrArg (ConcreteCategory.hom (Scheme.Hom.appTop ((associatedBigEtaleSite B).inclusion.map
    ((representedSmallEtaleEquivalence B S hS T').counit.app
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property
        (preimageOpens τ O))).hom.left))) hl'

/-- A natural transformation to a sections functor carries the transported scalar action to the
scalar action on sections. -/
theorem _root_.CategoryTheory.Sheaf.natTrans_moduleSMulObj {C : Type*} [Category C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget RingCat.{u})]
    [J.HasSheafCompose (forget AddCommGrpCat.{u})] (R : Sheaf J RingCat.{u})
    (M : SheafOfModules.{u} R) {P : Sheaf J (Type u) ⥤ Type u} [Limits.PreservesFiniteProducts P]
    {X : Cᵒᵖ} (θ : P ⟶ Sheaf.sectionsFunctor J X) (a : P.obj (Sheaf.ringSheaf R))
    (x : P.obj (Sheaf.moduleSheaf R M)) (b : R.obj.obj X) (hab : θ.app _ a = b) :
    θ.app _ (Sheaf.moduleSMulObj R M P a x) =
      (b • (show M.val.obj X from θ.app _ x) : M.val.obj X) := by
  rw [Sheaf.moduleSMulObj_naturality, hab]
  exact Sheaf.sectionsFunctor_map_moduleSMulHom _ _ _ _ _


end AlgebraicGeometry.Space
