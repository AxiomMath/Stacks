module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompIso
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekComposition
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Etale.OpenCovarianceSeparated

/-!
# The composition isomorphism of direct images with compact support for separated morphisms

For a separated locally quasi-finite morphism `f` the two models of `f_!` agree
(Stacks 0F6N, `AlgebraicGeometry.SmallEtale.fShriekFunctorIsoProperSupport`). This file computes
that identification on stalks: a section of `f_!F` with proper support has, at a point of a
geometric fibre, the germ of the section itself. From this, the composition isomorphism of
Stacks 0F6T is compared with the identification of Stacks 0F50 when both morphisms are
separated, which is part (1) of Stacks 0F6T, and with the construction of Stacks 0F79 when the
second morphism is separated, which is part (2).

## Main results

* `AlgebraicGeometry.SmallEtale.fShriekStalkIso_germ_fShriekFunctorIsoProperSupport_inv` — the
  stalk decomposition of a section with proper support.
* `AlgebraicGeometry.SmallEtale.fShriekCompIso_eq_of_isSeparated` — part (1) of Stacks 0F6T.
* `AlgebraicGeometry.SmallEtale.fShriekCompIso_generator_of_isSeparated` — part (2) of
  Stacks 0F6T: on the local generators the isomorphism is the map `c` of Stacks 0F79.
* `AlgebraicGeometry.SmallEtale.etaleSection_ext` — sections of an abelian étale sheaf are
  determined by their germs at the geometric points.

## References

* [Stacks Project, Tag 0F6T](https://stacks.math.columbia.edu/tag/0F6T)
* [Stacks Project, Tag 0F6N](https://stacks.math.columbia.edu/tag/0F6N)
* [Stacks Project, Tag 0F50](https://stacks.math.columbia.edu/tag/0F50)
* [Stacks Project, Tag 0F79](https://stacks.math.columbia.edu/tag/0F79)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped DirectSum

universe u v

namespace AlgebraicGeometry.SmallEtale

section SheafIso

variable {C : Type*} [Category C] {J : GrothendieckTopology C}

/-- An isomorphism of functors to abelian sheaves undoes its inverse on sections. -/
public theorem natIso_inv_hom_app_apply {D : Type*} [Category D]
    {Φ Ψ : D ⥤ Sheaf J AddCommGrpCat.{v}} (e : Φ ≅ Ψ) (X : D) (U : Cᵒᵖ)
    (x : (Ψ.obj X).obj.obj U) : (e.hom.app X).hom.app U ((e.inv.app X).hom.app U x) = x :=
  ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app U) (e.inv_hom_id_app X)) x

/-- A presheaf of abelian groups carries an isomorphism and its inverse to inverse maps. -/
public theorem presheaf_map_hom_inv_apply {P : Cᵒᵖ ⥤ AddCommGrpCat.{v}} {A A' : C} (i : A ≅ A')
    (a : P.obj (op A)) : P.map i.hom.op (P.map i.inv.op a) = a := by
  rw [← ConcreteCategory.comp_apply, ← P.map_comp, ← op_comp, i.hom_inv_id, op_id, P.map_id]
  rfl

/-- An isomorphism of functors to abelian sheaves undoes itself on sections. -/
private theorem natIso_hom_inv_app_apply {D : Type*} [Category D]
    {Φ Ψ : D ⥤ Sheaf J AddCommGrpCat.{v}} (e : Φ ≅ Ψ) (X : D) (U : Cᵒᵖ)
    (x : (Φ.obj X).obj.obj U) : (e.inv.app X).hom.app U ((e.hom.app X).hom.app U x) = x :=
  ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app U) (e.hom_inv_id_app X)) x

/-- A functor carries an equality of composites to an equality of the composites of images. -/
private theorem functor_map_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Z} {c : W ⟶ Y} {d : Y ⟶ Z} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, ← F.map_comp, h]

end SheafIso

section Arrow

variable (B : BigEtaleSite.{u}) {Y Z : B.Scheme} (g : Y ⟶ Z)
  [LocallyOfFiniteType (B.inclusion.map g)]

/-- A section of the proper-support direct image `g_!G` over `W`, as a section of `G` over
`W ×_Z Y`. -/
public def properSupportSection (G : Sheaf (SmallEtale.topology B Y.obj Y.property)
    AddCommGrpCat.{v}) (W : SmallEtale B Z.obj Z.property) :
    ((properSupportFunctor.{u, v} B g).obj G).obj.obj (op W) →+
      G.obj.obj (op (baseChange B g W)) :=
  ((fShriekSubsheaf B g G).val.arrow.hom.app (op W)).hom

/-- A section of the proper-support direct image of a morphism of sheaves, read in the ordinary
direct image. -/
public theorem properSupportSection_map
    {G H : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{v}} (φ : G ⟶ H)
    (W : SmallEtale B Z.obj Z.property)
    (ρ : ((properSupportFunctor.{u, v} B g).obj G).obj.obj (op W)) :
    properSupportSection B g H W (((properSupportFunctor.{u, v} B g).map φ).hom.app (op W) ρ) =
      φ.hom.app (op (baseChange B g W)) (properSupportSection B g G W ρ) :=
  ConcreteCategory.congr_hom (congrArg (fun ψ => ψ.hom.app (op W))
    ((properSupportToPushforward.{u, v} B g).naturality φ)) ρ

end Arrow

section Germ

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [IsSeparated (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The identification of Stacks 0F6N restricts, along the sheafification unit, to the
identification of the finite-support direct image presheaf with the proper-support direct
image. -/
public theorem toSheafify_fShriekFunctorIsoProperSupport_hom :
    toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).val.obj F) ≫
      ((fShriekFunctorIsoProperSupport.{u, v} B f).hom.app F).hom =
    (finiteSupportPushforwardIso.{u, max (u + 1) v} B f).val.hom.app F := by
  simp [fShriekFunctorIsoProperSupport]

/-- The inverse of the identification of Stacks 0F6N carries the image of a section of the
finite-support direct image presheaf to its image under the sheafification unit. -/
public theorem fShriekFunctorIsoProperSupport_inv_app_apply (W : SmallEtale B Y.obj Y.property)
    (x : ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).val.obj
      F).obj (op W)) :
    ((fShriekFunctorIsoProperSupport.{u, v} B f).inv.app F).hom.app (op W)
        (((finiteSupportPushforwardIso.{u, max (u + 1) v} B f).val.hom.app F).app (op W) x) =
      (toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).val.obj
          F)).app (op W) x := by
  rw [← toSheafify_fShriekFunctorIsoProperSupport_hom.{u, v} B f F]
  change ((((fShriekFunctorIsoProperSupport.{u, v} B f).hom.app F) ≫
    ((fShriekFunctorIsoProperSupport.{u, v} B f).inv.app F)).hom.app (op W)) _ = _
  rw [Iso.hom_inv_id_app]
  rfl

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- For a separated morphism every point of the geometric fibre lifts into the canonical open of
a support, which is everything; the germ of a supported section there is the germ of its
extension by zero. -/
public theorem fiberStalkComponent_eq_etaleGerm_finiteSupportExtension (s : GeometricPoint Y.obj)
    (V : SmallEtale B Y.obj Y.property) (w : (geometricPointFiber B Y.obj Y.property s).obj V)
    (E : FiniteSupport B f V)
    (a : supportedSections B X.obj X.property F (baseChange B f V) E.1
      (finiteSupport_isLocallyClosed B f V E)) (x : GeometricFiberPoint B f s) :
    fiberStalkComponent.{u, max (u + 1) v} B f s F V w E a x =
      etaleGerm B X.obj X.property (x.toGeometricPoint B f s) F.obj (baseChange B f V)
        (fiberPointElement B f s V w x)
        (finiteSupportExtension.{u, max (u + 1) v} B f F V E a) := by
  have h : HasFiberLift B f s V w E x := by
    unfold HasFiberLift
    rw [finiteSupportOpen_eq_top]
    trivial
  rw [fiberStalkComponent_of_hasFiberLift B f s F V w E a x h, ← etaleGerm_openObjectLift B
    X.obj X.property (x.toGeometricPoint B f s) F.obj (baseChange B f V)
    (fiberPointElement B f s V w x) (finiteSupportOpen B f V E) h,
    finiteSupportExtension_restrict]

/-- **The stalk decomposition of a section with proper support.** For a separated locally
quasi-finite morphism `f`, a section `ρ` of `f_!F` with proper support over `W`, read in the
sheafified model of `f_!` through Stacks 0F6N, has at a point `x` of the geometric fibre over a
geometric point `s` with a lift to `W` the germ of `ρ` itself at the corresponding lift of `x`. -/
public theorem fShriekStalkIso_germ_fShriekFunctorIsoProperSupport_inv (s : GeometricPoint Y.obj)
    (W : SmallEtale B Y.obj Y.property) (w : (geometricPointFiber B Y.obj Y.property s).obj W)
    (ρ : ((properSupportFunctor.{u, max (u + 1) v} B f).obj F).obj.obj (op W))
    (x : GeometricFiberPoint B f s) :
    ((fShriekStalkIso.{u, v} B f s F).hom
        (etaleGerm B Y.obj Y.property s ((fShriekFunctor.{u, v} B f).obj F).obj W w
          (((fShriekFunctorIsoProperSupport.{u, v} B f).inv.app F).hom.app (op W) ρ)) :
        fiberStalks.{u, max (u + 1) v} B f s F) x =
      etaleGerm B X.obj X.property (x.toGeometricPoint B f s) F.obj (baseChange B f W)
        (fiberPointElement B f s W w x) (properSupportSection B f F W ρ) := by
  obtain ⟨y, rfl⟩ : ∃ y, ((finiteSupportPushforwardIso.{u, max (u + 1) v} B f).val.hom.app F).app
      (op W) y = ρ :=
    ⟨_, Iso.inv_hom_id_apply (((finiteSupportPushforwardIso.{u, max (u + 1) v} B f).val.app F).app
      (op W)) ρ⟩
  let ev : AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B f s F) ⟶
      AddCommGrpCat.of ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) F.obj) :=
    AddCommGrpCat.ofHom (DFinsupp.evalAddMonoidHom x)
  have key : ((finiteSupportPushforwardIso.{u, max (u + 1) v} B f).val.hom.app F).app (op W) ≫
      ((fShriekFunctorIsoProperSupport.{u, v} B f).inv.app F).hom.app (op W) ≫
      colimit.ι (etaleStalkDiagram B Y.obj Y.property s ((fShriekFunctor.{u, v} B f).obj F).obj)
        (op (Functor.elementsMk _ W w)) ≫ (fShriekStalkIso.{u, v} B f s F).hom ≫ ev =
    ((finiteSupportPushforwardIso.{u, max (u + 1) v} B f).val.hom.app F).app (op W) ≫
      (fShriekSubsheaf B f F).val.arrow.hom.app (op W) ≫
      colimit.ι (etaleStalkDiagram B X.obj X.property (x.toGeometricPoint B f s) F.obj)
        (op (Functor.elementsMk _ (baseChange B f W) (fiberPointElement B f s W w x))) := by
    refine finiteSupportPushforwardGenerator_hom_ext B f F W fun E => ?_
    refine ConcreteCategory.hom_ext _ _ fun a => ?_
    simp only [ConcreteCategory.comp_apply]
    rw [fShriekFunctorIsoProperSupport_inv_app_apply]
    have h1 := fShriekStalkIso_hom_germ_generator.{u, v} B f F s W w E a
    refine (congrArg (fun m => (m : fiberStalks.{u, max (u + 1) v} B f s F) x) h1).trans ?_
    refine (fiberStalkComponent_eq_etaleGerm_finiteSupportExtension B f F s W w E a x).trans ?_
    exact congrArg (etaleGerm B X.obj X.property (x.toGeometricPoint B f s) F.obj
      (baseChange B f W) (fiberPointElement B f s W w x))
      (finiteSupportPushforwardIso_generator.{u, v} B f F W E a).symm
  exact ConcreteCategory.congr_hom key y

end Germ

section Lift

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The identification `(W ×_Z Y) ×_Y X = W ×_Z X` of Stacks 021J carries the projection to `W`
to the composite of the two projections. -/
public theorem smallEtaleBaseChange_compIso_hom_app_left_fst (W : SmallEtale B Z.obj Z.property) :
    ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W).hom.left ≫
        pullback.fst W.obj.hom (f ≫ g) =
      pullback.fst ((smallEtaleBaseChange B g).obj W).obj.hom f ≫ pullback.fst W.obj.hom g := by
  have hl : ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W).hom.left =
      ((Over.pullbackComp f g).inv.app W.obj).left :=
    congrArg Over.Hom.left (smallEtaleBaseChange_compIso_app B X Y Z f g W)
  rw [hl]
  exact Over.pullbackComp_inv_app_left_fst f g W.obj

/-- The lift of a point of the geometric fibre of `f ≫ g` to `W ×_Z X`, read through the
identification `(W ×_Z Y) ×_Y X = W ×_Z X` of Stacks 021J, is the lift of the point through the
lift of its image to `W ×_Z Y`. -/
public theorem fiberPointElement_compIso (s : GeometricPoint Z.obj)
    (W : SmallEtale B Z.obj Z.property) (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (y : GeometricFiberPoint B g s) (x : GeometricFiberPoint B f (y.toGeometricPoint B g s)) :
    (geometricPointFiber B X.obj X.property ((compFiberPointOf B f g s y x).toGeometricPoint B
        (f ≫ g) s)).map ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W)
      (fiberPointElement B f (y.toGeometricPoint B g s) (baseChange B g W)
        (fiberPointElement B g s W w y) x) =
      fiberPointElement B (f ≫ g) s W w (compFiberPointOf B f g s y x) := by
  refine Subtype.ext ?_
  change fiberPointLift B f (y.toGeometricPoint B g s) (baseChange B g W)
      (fiberPointElement B g s W w y) x ≫ B.inclusion.map
        ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W).hom.left =
    fiberPointLift B (f ≫ g) s W w (compFiberPointOf B f g s y x)
  refine ((IsPullback.of_hasPullback W.obj.hom (f ≫ g)).map B.inclusion).hom_ext ?_ ?_
  · have h := functor_map_comp_eq_map_comp B.inclusion
      (smallEtaleBaseChange_compIso_hom_app_left_fst B f g W)
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (fiberPointLift_comp_fst B f _ _ _ x)).trans ?_
    exact (fiberPointLift_comp_fst B g s W w y).trans
      (fiberPointLift_comp_fst B (f ≫ g) s W w (compFiberPointOf B f g s y x)).symm
  · have h := congrArg B.inclusion.map
      (Over.w ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W).hom)
    simp only [Functor.map_comp] at h
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h).trans ?_)
    exact (fiberPointLift_comp_snd B f _ _ _ x).trans
      (fiberPointLift_comp_snd B (f ≫ g) s W w (compFiberPointOf B f g s y x)).symm

end Lift


section Composition

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated (B.inclusion.map f)] [IsSeparated (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyOfFiniteType (B.inclusion.map g)]

/-- **Stacks 0F50 on sections.** The identification `g_!f_!F = (g ∘ f)_!F` of proper-support
direct images carries a section to the same section of `F`, read on `W ×_Z X` through the
identification `(W ×_Z Y) ×_Y X = W ×_Z X`. -/
public theorem properSupportSection_properSupportFunctor_compIso
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (W : SmallEtale B Z.obj Z.property)
    (ρ : ((properSupportFunctor.{u, v} B f ⋙ properSupportFunctor.{u, v} B g).obj F).obj.obj
      (op W)) :
    properSupportSection B (f ≫ g) F W
        (((properSupportFunctor_compIso B f g).val.hom.app F).hom.app (op W) ρ) =
      F.obj.map ((smallEtaleBaseChange_compIso B X Y Z f g).val.inv.app W).op
        (properSupportSection B f F (baseChange B g W)
          (properSupportSection B g ((properSupportFunctor.{u, v} B f).obj F) W ρ)) := by
  have h := ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app (op W))
    (properSupportSheaf_compIso B f g F).property) ρ
  rwa [← (properSupportFunctor_compIso B f g).property F] at h

/-- **Stacks 0F50 on sections**, read from the other side. -/
public theorem properSupportSection_properSupportFunctor_compIso_inv
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (W : SmallEtale B Z.obj Z.property)
    (ρ : ((properSupportFunctor.{u, v} B (f ≫ g)).obj F).obj.obj (op W)) :
    properSupportSection B (f ≫ g) F W ρ =
      F.obj.map ((smallEtaleBaseChange_compIso B X Y Z f g).val.inv.app W).op
        (properSupportSection B f F (baseChange B g W)
          (properSupportSection B g ((properSupportFunctor.{u, v} B f).obj F) W
            (((properSupportFunctor_compIso B f g).val.inv.app F).hom.app (op W) ρ))) := by
  have h := properSupportSection_properSupportFunctor_compIso B f g F W
    (((properSupportFunctor_compIso B f g).val.inv.app F).hom.app (op W) ρ)
  rwa [natIso_inv_hom_app_apply] at h

/-- **Stacks 0F50 on sections**, read on `(W ×_Z Y) ×_Y X`. -/
public theorem properSupportSection_properSupportFunctor_compIso_inv'
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{v})
    (W : SmallEtale B Z.obj Z.property)
    (ρ : ((properSupportFunctor.{u, v} B (f ≫ g)).obj F).obj.obj (op W)) :
    properSupportSection B f F (baseChange B g W)
        (properSupportSection B g ((properSupportFunctor.{u, v} B f).obj F) W
          (((properSupportFunctor_compIso B f g).val.inv.app F).hom.app (op W) ρ)) =
      F.obj.map ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W).op
        (properSupportSection B (f ≫ g) F W ρ) := by
  refine Eq.trans ?_ (congrArg (F.obj.map ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app
    W).op) (properSupportSection_properSupportFunctor_compIso_inv B f g F W ρ)).symm
  exact (presheaf_map_hom_inv_apply (P := F.obj)
    ((smallEtaleBaseChange_compIso B X Y Z f g).val.app W) _).symm

end Composition

section Separated

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated (B.inclusion.map f)] [IsSeparated (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]

/-- The comparison `(g ∘ f)_! ⟶ g_! ∘ f_!` read off the identification of Stacks 0F50 of the
proper-support direct images, through the identifications of Stacks 0F6N of the two models. -/
public abbrev separatedCompShriekMap
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    (fShriekFunctor.{u, v} B (f ≫ g)).obj F ⟶
      (fShriekFunctor.{u, v} B g).obj ((fShriekFunctor.{u, v} B f).obj F) :=
  (fShriekFunctorIsoProperSupport.{u, v} B (f ≫ g)).hom.app F ≫
    (properSupportFunctor_compIso B f g).val.inv.app F ≫
    (properSupportFunctor.{u, max (u + 1) v} B g).map
      ((fShriekFunctorIsoProperSupport.{u, v} B f).inv.app F) ≫
    (fShriekFunctorIsoProperSupport.{u, v} B g).inv.app ((fShriekFunctor.{u, v} B f).obj F)

/-- The comparison read off Stacks 0F50 on the germ of a section. -/
public theorem separatedCompShriekMap_germ
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (s : GeometricPoint Z.obj) (W : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (ρ : ((properSupportFunctor.{u, max (u + 1) v} B (f ≫ g)).obj F).obj.obj (op W)) :
    ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map (separatedCompShriekMap B f g F)
        (etaleGerm B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj W w
          (((fShriekFunctorIsoProperSupport.{u, v} B (f ≫ g)).inv.app F).hom.app (op W) ρ)) =
      etaleGerm B Z.obj Z.property s
        ((fShriekFunctor.{u, v} B g).obj ((fShriekFunctor.{u, v} B f).obj F)).obj W w
        (((fShriekFunctorIsoProperSupport.{u, v} B g).inv.app
          ((fShriekFunctor.{u, v} B f).obj F)).hom.app (op W)
          (((properSupportFunctor.{u, max (u + 1) v} B g).map
            ((fShriekFunctorIsoProperSupport.{u, v} B f).inv.app F)).hom.app (op W)
            (((properSupportFunctor_compIso B f g).val.inv.app F).hom.app (op W) ρ))) := by
  refine (colim_map_etaleGerm.{u, v} B s (separatedCompShriekMap B f g F).hom W w _).trans ?_
  refine congrArg (etaleGerm B Z.obj Z.property s _ W w) ?_
  change ((fShriekFunctorIsoProperSupport.{u, v} B g).inv.app
        ((fShriekFunctor.{u, v} B f).obj F)).hom.app (op W)
      (((properSupportFunctor.{u, max (u + 1) v} B g).map
        ((fShriekFunctorIsoProperSupport.{u, v} B f).inv.app F)).hom.app (op W)
        (((properSupportFunctor_compIso B f g).val.inv.app F).hom.app (op W)
          (((fShriekFunctorIsoProperSupport.{u, v} B (f ≫ g)).hom.app F).hom.app (op W)
            (((fShriekFunctorIsoProperSupport.{u, v} B (f ≫ g)).inv.app F).hom.app (op W)
              ρ)))) = _
  have hA : ((fShriekFunctorIsoProperSupport.{u, v} B (f ≫ g)).hom.app F).hom.app (op W)
      (((fShriekFunctorIsoProperSupport.{u, v} B (f ≫ g)).inv.app F).hom.app (op W) ρ) = ρ :=
    natIso_inv_hom_app_apply _ F (op W) ρ
  exact congrArg (fun z => ((fShriekFunctorIsoProperSupport.{u, v} B g).inv.app
        ((fShriekFunctor.{u, v} B f).obj F)).hom.app (op W)
      (((properSupportFunctor.{u, max (u + 1) v} B g).map
        ((fShriekFunctorIsoProperSupport.{u, v} B f).inv.app F)).hom.app (op W)
        (((properSupportFunctor_compIso B f g).val.inv.app F).hom.app (op W) z))) hA

/-- The left side of the stalk computation of the comparison read off Stacks 0F50: the
component at a point of the geometric fibre is the germ of the section itself. -/
public theorem separatedCompShriekMap_component
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (s : GeometricPoint Z.obj) (W : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (ρ₂ : ((properSupportFunctor.{u, max (u + 1) v} B f ⋙
      properSupportFunctor.{u, max (u + 1) v} B g).obj F).obj.obj (op W))
    (y : GeometricFiberPoint B g s) (x : GeometricFiberPoint B f (y.toGeometricPoint B g s)) :
    ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
        (((fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F)).hom
          (etaleGerm B Z.obj Z.property s
            ((fShriekFunctor.{u, v} B g).obj ((fShriekFunctor.{u, v} B f).obj F)).obj W w
            (((fShriekFunctorIsoProperSupport.{u, v} B g).inv.app
              ((fShriekFunctor.{u, v} B f).obj F)).hom.app (op W)
              (((properSupportFunctor.{u, max (u + 1) v} B g).map
                ((fShriekFunctorIsoProperSupport.{u, v} B f).inv.app F)).hom.app (op W) ρ₂))) :
          fiberStalks.{u, max (u + 1) v} B g s _) y) : fiberStalks.{u, max (u + 1) v} B f _ F) x =
      etaleGerm B X.obj X.property (x.toGeometricPoint B f (y.toGeometricPoint B g s)) F.obj
        (baseChange B f (baseChange B g W))
        (fiberPointElement B f (y.toGeometricPoint B g s) (baseChange B g W)
          (fiberPointElement B g s W w y) x)
        (properSupportSection B f F (baseChange B g W)
          (properSupportSection B g ((properSupportFunctor.{u, max (u + 1) v} B f).obj F) W
            ρ₂)) := by
  have hK1 := fShriekStalkIso_germ_fShriekFunctorIsoProperSupport_inv.{u, v} B g
    ((fShriekFunctor.{u, v} B f).obj F) s W w
    (((properSupportFunctor.{u, max (u + 1) v} B g).map
      ((fShriekFunctorIsoProperSupport.{u, v} B f).inv.app F)).hom.app (op W) ρ₂) y
  refine (congrArg (fun m => ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom m :
    fiberStalks.{u, max (u + 1) v} B f _ F) x) hK1).trans ?_
  have harr' := properSupportSection_map.{u, max (u + 1) v} B g
    ((fShriekFunctorIsoProperSupport.{u, v} B f).inv.app F) W ρ₂
  have hc := congrArg (fun m => ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
    (etaleGerm B Y.obj Y.property (y.toGeometricPoint B g s)
      ((fShriekFunctor.{u, v} B f).obj F).obj (baseChange B g W)
      (fiberPointElement B g s W w y) m) : fiberStalks.{u, max (u + 1) v} B f _ F) x) harr'
  refine hc.trans ?_
  exact fShriekStalkIso_germ_fShriekFunctorIsoProperSupport_inv.{u, v} B f F
    (y.toGeometricPoint B g s) (baseChange B g W) (fiberPointElement B g s W w y)
    (properSupportSection.{u, max (u + 1) v} B g _ W ρ₂) x

omit [LocallyQuasiFinite (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map g)] in
/-- The two germs of the stalk computation of the comparison read off Stacks 0F50 agree. -/
public theorem separatedCompShriekMap_germ_eq
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (s : GeometricPoint Z.obj) (W : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (ρ : ((properSupportFunctor.{u, max (u + 1) v} B (f ≫ g)).obj F).obj.obj (op W))
    (y : GeometricFiberPoint B g s) (x : GeometricFiberPoint B f (y.toGeometricPoint B g s)) :
    etaleGerm B X.obj X.property (x.toGeometricPoint B f (y.toGeometricPoint B g s)) F.obj
        (baseChange B f (baseChange B g W))
        (fiberPointElement B f (y.toGeometricPoint B g s) (baseChange B g W)
          (fiberPointElement B g s W w y) x)
        (properSupportSection B f F (baseChange B g W)
          (properSupportSection B g ((properSupportFunctor.{u, max (u + 1) v} B f).obj F) W
            (((properSupportFunctor_compIso B f g).val.inv.app F).hom.app (op W) ρ))) =
      etaleGerm B X.obj X.property ((compFiberPointOf B f g s y x).toGeometricPoint B (f ≫ g) s)
        F.obj (baseChange B (f ≫ g) W)
        (fiberPointElement B (f ≫ g) s W w (compFiberPointOf B f g s y x))
        (properSupportSection B (f ≫ g) F W ρ) :=
  (congrArg (etaleGerm B X.obj X.property _ F.obj _ _)
    (properSupportSection_properSupportFunctor_compIso_inv'.{u, max (u + 1) v} B f g F W ρ)).trans
    (etaleGerm_map B X.obj X.property
      ((compFiberPointOf B f g s y x).toGeometricPoint B (f ≫ g) s) F.obj
      ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W) _ _
      (fiberPointElement_compIso B f g s W w y x) (properSupportSection B (f ≫ g) F W ρ))

/-- The comparison read off Stacks 0F50 is the regrouping of the geometric fibre on stalks. -/
public theorem hasCompShriekStalks_separatedCompShriekMap
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    HasCompShriekStalks B f g F (separatedCompShriekMap B f g F) := by
  intro s
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine (Iso.eq_comp_inv _).2 (ConcreteCategory.hom_ext _ _ fun e => ?_)
  obtain ⟨W, w, σ, rfl⟩ := exists_etaleGerm_eq B Z.obj Z.property s
    ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj e
  obtain ⟨ρ, rfl⟩ : ∃ ρ, ((fShriekFunctorIsoProperSupport.{u, v} B (f ≫ g)).inv.app F).hom.app
      (op W) ρ = σ :=
    ⟨_, natIso_hom_inv_app_apply _ F (op W) σ⟩
  refine DFinsupp.ext fun y => ?_
  refine (AddCommGrpCat.mono_iff_injective (fShriekStalkIso.{u, v} B f
    (y.toGeometricPoint B g s) F).hom).1 inferInstance ?_
  refine DFinsupp.ext fun x => ?_
  refine (congrArg (fun m => ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
    ((m : fiberStalks.{u, max (u + 1) v} B g s _) y) : fiberStalks.{u, max (u + 1) v} B f _ F) x)
    (congrArg (fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F)).hom
      (separatedCompShriekMap_germ B f g F s W w ρ))).trans ?_
  refine (separatedCompShriekMap_component B f g F s W w _ y x).trans ?_
  refine (separatedCompShriekMap_germ_eq B f g F s W w ρ y x).trans ?_
  exact ((fShriekStalkIso_germ_fShriekFunctorIsoProperSupport_inv.{u, v} B (f ≫ g) F s W w ρ
    (compFiberPointOf B f g s y x)).symm.trans (compFiberStalksMap_apply B f g s F
      ((fShriekStalkIso.{u, v} B (f ≫ g) s F).hom (etaleGerm B Z.obj Z.property s
        ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj W w
        (((fShriekFunctorIsoProperSupport.{u, v} B (f ≫ g)).inv.app F).hom.app (op W) ρ))) y
      x).symm)


/-- **Stacks 0F6T, part (1).** If `f` and `g` are separated, the isomorphism
`(g ∘ f)_! ≅ g_! ∘ f_!` agrees with the identification `g_! f_! = (g ∘ f)_!` of proper-support
direct images of Stacks 0F50, read through the identifications of Stacks 0F6N of the
finite-support model of `f_!`, `g_!` and `(g ∘ f)_!` with the proper-support model. -/
@[stacks 0F6T "part (1)"]
public theorem fShriekCompIso_eq_of_isSeparated :
    fShriekCompIso B f g =
      fShriekFunctorIsoProperSupport.{u, v} B (f ≫ g) ≪≫
        (properSupportFunctor_compIso B f g).val.symm ≪≫
        Functor.isoWhiskerRight (fShriekFunctorIsoProperSupport.{u, v} B f).symm
          (properSupportFunctor.{u, max (u + 1) v} B g) ≪≫
        Functor.isoWhiskerLeft (fShriekFunctor.{u, v} B f)
          (fShriekFunctorIsoProperSupport.{u, v} B g).symm := by
  refine Iso.ext (eq_fShriekCompIso B f g fun s F => ?_).symm
  exact (Iso.eq_comp_inv _).1 ((hasCompShriekStalks_separatedCompShriekMap B f g F s).trans
    (Category.assoc _ _ _).symm)
end Separated

section SectionExt

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Sections of an abelian étale sheaf are determined by their germs** at the geometric
points: two sections with the same germ at every lift of every geometric point agree, because
the arrows along which they agree form a covering sieve. -/
public theorem etaleSection_ext
    {G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) v}}
    {U : SmallEtale B S hS} (a b : G.obj.obj (op U))
    (h : ∀ (t : GeometricPoint S) (q : (geometricPointFiber B S hS t).obj U),
      etaleGerm B S hS t G.obj U q a = etaleGerm B S hS t G.obj U q b) : a = b := by
  have hcov : Presheaf.equalizerSieve a b ∈ SmallEtale.topology B S hS U := by
    refine SmallEtale.mem_topology_of_jointlySurjective fun x => ?_
    have h0 : etaleGerm B S hS (geometricPointOfEtalePoint B S hS U x) G.obj U
        (geometricPointOfEtalePointLift B S hS U x) (a - b) = 0 := by
      have ha := h (geometricPointOfEtalePoint B S hS U x)
        (geometricPointOfEtalePointLift B S hS U x)
      have hs : etaleGerm B S hS (geometricPointOfEtalePoint B S hS U x) G.obj U
          (geometricPointOfEtalePointLift B S hS U x) (a - b) =
          etaleGerm B S hS (geometricPointOfEtalePoint B S hS U x) G.obj U
            (geometricPointOfEtalePointLift B S hS U x) a -
          etaleGerm B S hS (geometricPointOfEtalePoint B S hS U x) G.obj U
            (geometricPointOfEtalePointLift B S hS U x) b :=
        map_sub (ConcreteCategory.hom (colimit.ι (etaleStalkDiagram B S hS
          (geometricPointOfEtalePoint B S hS U x) G.obj) (op (Functor.elementsMk _ U _)))) a b
      rw [hs, ha, sub_self]
    obtain ⟨W', j, q', hq', hz⟩ := (etaleGerm_eq_zero_iff B S hS _ G.obj U _ (a - b)).1 h0
    refine ⟨W', j, ?_, q'.1.base default, ?_⟩
    · change G.obj.map j.op a = G.obj.map j.op b
      rw [map_sub] at hz
      exact sub_eq_zero.1 hz
    · have h1 : q'.1 ≫ (SmallEtale.toScheme B S hS).map j =
          (geometricPointOfEtalePointLift B S hS U x).1 := congrArg Subtype.val hq'
      have h2 : ((SmallEtale.toScheme B S hS).map j).base (q'.1.base default) =
          (geometricPointOfEtalePointLift B S hS U x).1.base default :=
        congrArg (fun m : (geometricPointOfEtalePoint B S hS U x).source ⟶ _ =>
          m.base (default : ↥(geometricPointOfEtalePoint B S hS U x).source)) h1
      exact h2.trans (geometricPointOfEtalePointLift_base B S hS U x)
  exact G.property.isSeparated _ _ hcov _ _ fun _ _ hf => hf

end SectionExt

section SeparatedOuter

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The identification `(W ×_Z Y) ×_Y X = W ×_Z X` of Stacks 021J, on underlying schemes. -/
public abbrev sepCompMap (W : SmallEtale B Z.obj Z.property) :
    (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f (baseChange B g W)) ⟶
      (SmallEtale.toScheme B X.obj X.property).obj (baseChange B (f ≫ g) W) :=
  (SmallEtale.toScheme B X.obj X.property).map
    ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W)

/-- The inverse of `AlgebraicGeometry.SmallEtale.sepCompMap`. -/
public abbrev sepCompInv (W : SmallEtale B Z.obj Z.property) :
    (SmallEtale.toScheme B X.obj X.property).obj (baseChange B (f ≫ g) W) ⟶
      (SmallEtale.toScheme B X.obj X.property).obj (baseChange B f (baseChange B g W)) :=
  (SmallEtale.toScheme B X.obj X.property).map
    ((smallEtaleBaseChange_compIso B X Y Z f g).val.inv.app W)

/-- `AlgebraicGeometry.SmallEtale.sepCompInv` is a left inverse of
`AlgebraicGeometry.SmallEtale.sepCompMap`. -/
public theorem sepCompInv_sepCompMap (W : SmallEtale B Z.obj Z.property) :
    sepCompInv B f g W ≫ sepCompMap B f g W = 𝟙 _ :=
  ((SmallEtale.toScheme B X.obj X.property).mapIso
    ((smallEtaleBaseChange_compIso B X Y Z f g).val.app W)).inv_hom_id

/-- `AlgebraicGeometry.SmallEtale.sepCompInv` is a right inverse of
`AlgebraicGeometry.SmallEtale.sepCompMap`. -/
public theorem sepCompMap_sepCompInv (W : SmallEtale B Z.obj Z.property) :
    sepCompMap B f g W ≫ sepCompInv B f g W = 𝟙 _ :=
  ((SmallEtale.toScheme B X.obj X.property).mapIso
    ((smallEtaleBaseChange_compIso B X Y Z f g).val.app W)).hom_inv_id

/-- `AlgebraicGeometry.SmallEtale.sepCompMap` carries the projection to `W` to the composite of
the two projections. -/
public theorem sepCompMap_fst (W : SmallEtale B Z.obj Z.property) :
    sepCompMap B f g W ≫ B.inclusion.map (pullback.fst W.obj.hom (f ≫ g)) =
      B.inclusion.map (pullback.fst (baseChange B g W).obj.hom f) ≫
        B.inclusion.map (pullback.fst W.obj.hom g) :=
  functor_map_comp_eq_map_comp B.inclusion (smallEtaleBaseChange_compIso_hom_app_left_fst B f g W)

variable [IsSeparated (B.inclusion.map g)]

/-- The support of `X_{W ×_Z Y}` corresponding to a support of `X_W` finite over `W` is finite
over `W ×_Z Y`: it is finite over `W`, and `W ×_Z Y ⟶ W` is separated. -/
public theorem isFiniteSupport_sepCompSupport (W : SmallEtale B Z.obj Z.property)
    (E : FiniteSupport B (f ≫ g) W) :
    IsFiniteSupport B f (baseChange B g W) ((sepCompMap B f g W).base ⁻¹' E.1) := by
  obtain ⟨Zs, i, hi, hfin, hrange⟩ := E.property
  have : IsImmersion i := hi
  have : IsIso (sepCompInv B f g W) :=
    ((SmallEtale.toScheme B X.obj X.property).mapIso
      ((smallEtaleBaseChange_compIso B X Y Z f g).val.app W).symm).isIso_hom
  refine ⟨Zs, i ≫ sepCompInv B f g W, inferInstance, ?_, ?_⟩
  · have hsep : IsSeparated (B.inclusion.map (pullback.fst W.obj.hom g)) :=
      MorphismProperty.of_isPullback
        ((IsPullback.of_hasPullback W.obj.hom g).map B.inclusion).flip inferInstance
    have hc : ((i ≫ sepCompInv B f g W) ≫
        B.inclusion.map (pullback.fst (baseChange B g W).obj.hom f)) ≫
          B.inclusion.map (pullback.fst W.obj.hom g) =
        i ≫ B.inclusion.map (pullback.fst W.obj.hom (f ≫ g)) := by
      refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
        (congrArg (i ≫ ·) ?_))
      refine (congrArg (sepCompInv B f g W ≫ ·) (sepCompMap_fst B f g W).symm).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (· ≫ _) (sepCompInv_sepCompMap B f g W)).trans (Category.id_comp _)
    have hfin' : IsFinite (((i ≫ sepCompInv B f g W) ≫
        B.inclusion.map (pullback.fst (baseChange B g W).obj.hom f)) ≫
          B.inclusion.map (pullback.fst W.obj.hom g)) := by
      rwa [hc]
    exact @IsFinite.of_comp _ _ _ _ (B.inclusion.map (pullback.fst W.obj.hom g)) hfin' hsep
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change (sepCompMap B f g W).base ((sepCompInv B f g W).base y) ∈ E.1
      rw [← Scheme.Hom.comp_apply, sepCompInv_sepCompMap]
      exact hy
    · intro hx
      refine ⟨_, hx, ?_⟩
      change (sepCompInv B f g W).base ((sepCompMap B f g W).base x) = x
      rw [← Scheme.Hom.comp_apply, sepCompMap_sepCompInv]
      rfl

/-- The support of `X_{W ×_Z Y}` finite over `W ×_Z Y` corresponding to a support of `X_W` finite
over `W`. -/
public def sepCompSupport (W : SmallEtale B Z.obj Z.property) (E : FiniteSupport B (f ≫ g) W) :
    FiniteSupport B f (baseChange B g W) :=
  ⟨_, isFiniteSupport_sepCompSupport B f g W E⟩

variable (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- A section of `F` over `X_W` supported on a support finite over `W`, read on
`X_{W ×_Z Y} = X_W`: the construction `c` of Stacks 0F79 on a generator. -/
public def sepCompSection (W : SmallEtale B Z.obj Z.property) (E : FiniteSupport B (f ≫ g) W) :
    supportedSections B X.obj X.property F (baseChange B (f ≫ g) W) E.1
        (finiteSupport_isLocallyClosed B _ W E) →+
      supportedSections B X.obj X.property F (baseChange B f (baseChange B g W))
        (sepCompSupport B f g W E).1 (finiteSupport_isLocallyClosed B f _ _) :=
  supportedSectionsPullback B X.obj X.property F
    ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W) E.1
    (finiteSupport_isLocallyClosed B _ W E) (sepCompSupport B f g W E).1
    (finiteSupport_isLocallyClosed B f _ _) rfl

/-- The construction `c` of Stacks 0F79 on a generator does not change its germs: the germ of
the transported section at a point of the geometric fibre of `f` over a point of the geometric
fibre of `g` is the germ of the section at the corresponding point of the geometric fibre of
`f ≫ g`. -/
public theorem fiberStalkComponent_sepCompSection (s : GeometricPoint Z.obj)
    (W : SmallEtale B Z.obj Z.property) (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (E : FiniteSupport B (f ≫ g) W)
    (a : supportedSections B X.obj X.property F (baseChange B (f ≫ g) W) E.1
      (finiteSupport_isLocallyClosed B _ W E))
    (y : GeometricFiberPoint B g s) (x : GeometricFiberPoint B f (y.toGeometricPoint B g s)) :
    fiberStalkComponent.{u, max (u + 1) v} B f (y.toGeometricPoint B g s) F (baseChange B g W)
        (fiberPointElement B g s W w y) (sepCompSupport B f g W E) (sepCompSection B f g F W E a)
        x =
      fiberStalkComponent.{u, max (u + 1) v} B (f ≫ g) s F W w E a
        (compFiberPointOf B f g s y x) := by
  let k := sepCompMap B f g W
  let lf := fiberPointLift B f (y.toGeometricPoint B g s) (baseChange B g W)
    (fiberPointElement B g s W w y) x
  let lh := fiberPointLift B (f ≫ g) s W w (compFiberPointOf B f g s y x)
  have hl : lf ≫ k = lh := congrArg Subtype.val (fiberPointElement_compIso B f g s W w y x)
  have hk : Topology.IsOpenEmbedding k.base := k.isOpenEmbedding
  have hcob : (finiteSupportOpen B f _ (sepCompSupport B f g W E) : Set _) =
      k.base ⁻¹' (finiteSupportOpen B (f ≫ g) W E : Set _) := by
    change coborder ((sepCompMap B f g W).base ⁻¹' E.1) = k.base ⁻¹' coborder E.1
    exact hk.coborder_preimage _
  have hpt : k.base (lf.base default) = lh.base default := by
    rw [← hl]
    rfl
  have hiff : HasFiberLift B f _ (baseChange B g W) (fiberPointElement B g s W w y)
      (sepCompSupport B f g W E) x ↔
      HasFiberLift B (f ≫ g) s W w E (compFiberPointOf B f g s y x) := by
    change lf.base default ∈ (finiteSupportOpen B f _ (sepCompSupport B f g W E) : Set _) ↔
      lh.base default ∈ (finiteSupportOpen B (f ≫ g) W E : Set _)
    rw [hcob, Set.mem_preimage, hpt]
  by_cases h : HasFiberLift B (f ≫ g) s W w E (compFiberPointOf B f g s y x)
  · have h' := hiff.2 h
    rw [fiberStalkComponent_of_hasFiberLift _ _ _ _ _ _ _ _ _ h',
      fiberStalkComponent_of_hasFiberLift _ _ _ _ _ _ _ _ _ h]
    refine etaleGerm_map B X.obj X.property _ F.obj
      (supportOpenMap B X.obj X.property ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W)
        E.1 (finiteSupport_isLocallyClosed B _ W E) (sepCompSupport B f g W E).1
        (finiteSupport_isLocallyClosed B f _ _) rfl) _ _ ?_ a.val
    apply openObjectLift_ext
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (supportOpenMap_map B X.obj X.property
      ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W) E.1
      (finiteSupport_isLocallyClosed B _ W E) (sepCompSupport B f g W E).1
      (finiteSupport_isLocallyClosed B f _ _) rfl)).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ k) (openObjectLift_comp_ι _ _ _ _ _ _ _ _)).trans ?_
    exact hl.trans (openObjectLift_comp_ι B X.obj X.property
      ((compFiberPointOf B f g s y x).toGeometricPoint B (f ≫ g) s) (baseChange B (f ≫ g) W)
      (fiberPointElement B (f ≫ g) s W w (compFiberPointOf B f g s y x))
      (finiteSupportOpen B (f ≫ g) W E) h).symm
  · rw [fiberStalkComponent_of_not_hasFiberLift _ _ _ _ _ _ _ _ _ (fun h' => h (hiff.1 h')),
      fiberStalkComponent_of_not_hasFiberLift _ _ _ _ _ _ _ _ _ h]
    rfl

end SeparatedOuter

section SeparatedOuterGerm

variable (B : BigEtaleSite.{u}) {Y Z : B.Scheme} (g : Y ⟶ Z)

/-- Sections of an abelian étale sheaf on `Y` over `W ×_Z Y` are determined by their germs at
the lifts of the points of the geometric fibres of `g` over the geometric points of `W`. -/
public theorem etaleSection_ext_baseChange
    {G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}}
    (W : SmallEtale B Z.obj Z.property) (a b : G.obj.obj (op (baseChange B g W)))
    (h : ∀ (s : GeometricPoint Z.obj) (w : (geometricPointFiber B Z.obj Z.property s).obj W)
      (y : GeometricFiberPoint B g s),
      etaleGerm B Y.obj Y.property (y.toGeometricPoint B g s) G.obj (baseChange B g W)
          (fiberPointElement B g s W w y) a =
        etaleGerm B Y.obj Y.property (y.toGeometricPoint B g s) G.obj (baseChange B g W)
          (fiberPointElement B g s W w y) b) : a = b := by
  refine etaleSection_ext.{u, v} B Y.obj Y.property a b fun t ℓ => ?_
  let s : GeometricPoint Z.obj := t.map (B.inclusion.map g)
  have hw : (ℓ.1 ≫ B.inclusion.map (pullback.fst W.obj.hom g)) ≫ B.inclusion.map W.obj.hom =
      s.hom := by
    have hc : B.inclusion.map (pullback.fst W.obj.hom g) ≫ B.inclusion.map W.obj.hom =
        B.inclusion.map (pullback.snd W.obj.hom g) ≫ B.inclusion.map g :=
      functor_map_comp_eq_map_comp B.inclusion pullback.condition
    refine (Category.assoc _ _ _).trans ((congrArg (ℓ.1 ≫ ·) hc).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (· ≫ B.inclusion.map g) ℓ.2
  let w : (geometricPointFiber B Z.obj Z.property s).obj W :=
    ⟨ℓ.1 ≫ B.inclusion.map (pullback.fst W.obj.hom g), hw⟩
  let y : GeometricFiberPoint B g s := ⟨t.hom, rfl⟩
  have hℓ : fiberPointElement B g s W w y = ℓ := by
    refine Subtype.ext (((IsPullback.of_hasPullback W.obj.hom g).map B.inclusion).hom_ext ?_ ?_)
    · exact fiberPointLift_comp_fst B g s W w y
    · exact (fiberPointLift_comp_snd B g s W w y).trans ℓ.2.symm
  have hy := h s w y
  rw [hℓ] at hy
  exact hy

variable [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)]
  [LocallyQuasiFinite (B.inclusion.map g)]

/-- The germ at a point of a geometric fibre of a section of `g_!G`, read in the proper-support
model through Stacks 0F6N, is the component of the stalk decomposition of Stacks 0F5F. -/
public theorem etaleGerm_properSupportSection_fShriekFunctorIsoProperSupport_hom
    (G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (s : GeometricPoint Z.obj) (W : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj W) (y : GeometricFiberPoint B g s)
    (τ : ((fShriekFunctor.{u, v} B g).obj G).obj.obj (op W)) :
    etaleGerm B Y.obj Y.property (y.toGeometricPoint B g s) G.obj (baseChange B g W)
        (fiberPointElement B g s W w y)
        (properSupportSection B g G W
          (((fShriekFunctorIsoProperSupport.{u, v} B g).hom.app G).hom.app (op W) τ)) =
      ((fShriekStalkIso.{u, v} B g s G).hom
        (etaleGerm B Z.obj Z.property s ((fShriekFunctor.{u, v} B g).obj G).obj W w τ) :
          fiberStalks.{u, max (u + 1) v} B g s G) y := by
  refine (fShriekStalkIso_germ_fShriekFunctorIsoProperSupport_inv.{u, v} B g G s W w _ y).symm.trans
    ?_
  exact congrArg (fun z => ((fShriekStalkIso.{u, v} B g s G).hom
    (etaleGerm B Z.obj Z.property s ((fShriekFunctor.{u, v} B g).obj G).obj W w z) :
      fiberStalks.{u, max (u + 1) v} B g s G) y) (natIso_hom_inv_app_apply _ G (op W) τ)

end SeparatedOuterGerm

section SeparatedOuterMain

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The components of the stalk decomposition of the image of a section under the composition
isomorphism. -/
public theorem fShriekStalkIso_germ_fShriekCompIso (s : GeometricPoint Z.obj)
    (W : SmallEtale B Z.obj Z.property) (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (σ : ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj.obj (op W))
    (y : GeometricFiberPoint B g s) (x : GeometricFiberPoint B f (y.toGeometricPoint B g s)) :
    ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
        (((fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F)).hom
          (etaleGerm B Z.obj Z.property s
            ((fShriekFunctor.{u, v} B g).obj ((fShriekFunctor.{u, v} B f).obj F)).obj W w
            (((fShriekCompIso B f g).hom.app F).hom.app (op W) σ)) :
          fiberStalks.{u, max (u + 1) v} B g s _) y) : fiberStalks.{u, max (u + 1) v} B f _ F) x =
      ((fShriekStalkIso.{u, v} B (f ≫ g) s F).hom
        (etaleGerm B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj W w σ) :
          fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F) (compFiberPointOf B f g s y x) := by
  have h1 := colim_map_etaleGerm.{u, v} B s ((fShriekCompIso B f g).hom.app F).hom W w σ
  have h2 := ConcreteCategory.congr_hom (fShriekCompIso_stalk B f g s F)
    (etaleGerm B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj W w σ)
  refine (congrArg (fun m => ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
    (((fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F)).hom m :
      fiberStalks.{u, max (u + 1) v} B g s _) y) : fiberStalks.{u, max (u + 1) v} B f _ F) x)
    h1.symm).trans ?_
  refine (congrArg (fun m => ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
    ((m : fiberStalks.{u, max (u + 1) v} B g s _) y) : fiberStalks.{u, max (u + 1) v} B f _ F) x)
    h2).trans ?_
  exact compFiberStalksMap_apply B f g s F _ y x

variable [IsSeparated (B.inclusion.map g)]

/-- **Stacks 0F6T, part (2).** If `g` is separated, the isomorphism `(g ∘ f)_! ≅ g_! ∘ f_!`
agrees with the isomorphism of Stacks 0F79: read in the proper-support model of `g_!` through
Stacks 0F6N, it is the sheafification of the map `c` of the proof of Stacks 0F79, which sends a
local generator `(Z, s)` of `(g ∘ f)_{p!}F` over `W` — a section `s` of `F` over `X_W` supported
on `Z ⊆ X_W` finite over `W` — to the generator `(Z, s)` of `f_{p!}F` over `W ×_Z Y`, through
`X_{W ×_Z Y} = X_W`. The generators generate `(g ∘ f)_{p!}F`, so this determines the
isomorphism. -/
@[stacks 0F6T "part (2)"]
public theorem fShriekCompIso_generator_of_isSeparated (W : SmallEtale B Z.obj Z.property)
    (E : FiniteSupport B (f ≫ g) W) (a : (finiteSupportDiagram B (f ≫ g) F W).obj E) :
    properSupportSection B g ((fShriekFunctor.{u, v} B f).obj F) W
        (((fShriekFunctorIsoProperSupport.{u, v} B g).hom.app
          ((fShriekFunctor.{u, v} B f).obj F)).hom.app (op W)
          (((fShriekCompIso B f g).hom.app F).hom.app (op W)
            ((finiteSupportPushforwardGenerator B (f ≫ g) F W E ≫
              (toSheafify (SmallEtale.topology B Z.obj Z.property)
                ((finiteSupportPushforward.{u, max (u + 1) v} B (f ≫ g)
                  (fun _ => inferInstance)).val.obj F)).app (op W)) a))) =
      (finiteSupportPushforwardGenerator B f F (baseChange B g W) (sepCompSupport B f g W E) ≫
        (toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).val.obj F)).app (op (baseChange B g W)))
        (sepCompSection B f g F W E a) := by
  refine etaleSection_ext_baseChange.{u, v} B g W _ _ fun s w y => ?_
  refine (etaleGerm_properSupportSection_fShriekFunctorIsoProperSupport_hom.{u, v} B g
    ((fShriekFunctor.{u, v} B f).obj F) s W w y _).trans ?_
  refine (AddCommGrpCat.mono_iff_injective (fShriekStalkIso.{u, v} B f
    (y.toGeometricPoint B g s) F).hom).1 inferInstance ?_
  refine DFinsupp.ext fun x => ?_
  refine (fShriekStalkIso_germ_fShriekCompIso B f g F s W w _ y x).trans ?_
  have hR := fShriekStalkIso_hom_germ_generator.{u, v} B f F (y.toGeometricPoint B g s)
    (baseChange B g W) (fiberPointElement B g s W w y) (sepCompSupport B f g W E)
    (sepCompSection B f g F W E a)
  have hL := fShriekStalkIso_hom_germ_generator.{u, v} B (f ≫ g) F s W w E a
  refine (congrArg (fun m => (m : fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F)
    (compFiberPointOf B f g s y x)) hL).trans ?_
  refine Eq.trans ?_ (congrArg (fun m => (m : fiberStalks.{u, max (u + 1) v} B f _ F) x) hR).symm
  exact (fiberStalkComponent_sepCompSection B f g F s W w E a y x).symm

end SeparatedOuterMain

end AlgebraicGeometry.SmallEtale

end
