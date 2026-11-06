module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalk
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CoefficientsGerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePullbackFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.EtaleStalkFunctor

/-!
# Germs and the composition law for inverse images on small étale sites

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of a big étale site and let `fg : X ⟶ Z` be a
chosen presentation of their composite, so `f ≫ g = fg`. Inverse image along `fg` is the
composite of the inverse images along `g` and along `f`, up to the canonical comparison of
Stacks 021J; this file computes that comparison on sections and on germs.

On sections the content is the composition law for
`AlgebraicGeometry.pullbackSectionAlongHom`: pulling a section over `V` back to the base change
of `V` along `g`, then pulling the result back along `f`, and finally comparing, is the same as
pulling the section back along `fg` and restricting along the comparison of base changes. It is
obtained from the characterisation of the comparison by the units of the three adjunctions,
which is exactly the formula for the mate of a natural isomorphism of right adjoints.

On germs, with abelian coefficients, the content is the compatibility of the comparison with the
identification of Stacks 03Q1 of the stalk of an inverse image with the stalk at the image
point: transporting a germ through the comparisons for `g` and then for `f` is the same as
transporting it through the comparison for `fg`. The two geometric points of `Z` involved,
`(x ∘ f) ∘ g` and `x ∘ fg`, are equal only up to the given factorisation, so the statement takes
a lift of each and the hypothesis that the two lifts agree as morphisms of schemes.

## Main definitions

* `AlgebraicGeometry.smallEtaleSheafPullbackFactoredCompIso` — the comparison of successive
  inverse images with the inverse image along a chosen presentation of the composite, for an
  arbitrary coefficient category.

## Main results

* `AlgebraicGeometry.unit_sheafPullbackFactoredCompIso` — the comparison is characterised by the
  units of the three adjunctions.
* `AlgebraicGeometry.pullbackSectionAlongHom_comp` — the composition law on sections.
* `AlgebraicGeometry.etaleGerm_pullbackSectionAlongHom` and
  `AlgebraicGeometry.etaleGerm_etaleStalkSmallEtalePullObjIso_inv` — **Stacks 03Q1** on germs
  with abelian coefficients, in both directions.
* `AlgebraicGeometry.compIso_lift_compat` — the composite of the two canonical lifts of a
  geometric point is the lift required by the germ formula for the composite.
* `AlgebraicGeometry.etaleGerm_smallEtaleSheafPullbackFactoredCompIso` — the germ formula for the
  composite comparison.

## References

* [Stacks Project, Tag 021J](https://stacks.math.columbia.edu/tag/021J)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v uA vA

namespace AlgebraicGeometry

/-- Two equal morphisms of sheaves have equal components. -/
public theorem sheaf_hom_app_congr {C : Type*} [Category C] {JJ : GrothendieckTopology C}
    {A' : Type*} [Category A'] {F G : Sheaf JJ A'} {a b : F ⟶ G} (h : a = b) (U : Cᵒᵖ) :
    a.hom.app U = b.hom.app U := by rw [h]

/-- The comparison of successive inverse images with the inverse image along a chosen
factorisation of the composite. -/
public def smallEtaleSheafPullbackFactoredCompIso (B : BigEtaleSite.{u}) (X Y Z : B.Scheme)
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg) (A : Type uA) [Category.{vA} A]
    [((smallEtaleBaseChange B g).sheafPushforwardContinuous A
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B Y.obj Y.property)).IsRightAdjoint]
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).IsRightAdjoint]
    [((smallEtaleBaseChange B fg).sheafPushforwardContinuous A
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B X.obj X.property)).IsRightAdjoint] :
    (smallEtaleBaseChange B g).sheafPullback A
        (SmallEtale.topology B Z.obj Z.property)
        (SmallEtale.topology B Y.obj Y.property) ⋙
      (smallEtaleBaseChange B f).sheafPullback A
        (SmallEtale.topology B Y.obj Y.property)
        (SmallEtale.topology B X.obj X.property) ≅
    (smallEtaleBaseChange B fg).sheafPullback A
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B X.obj X.property) :=
  Functor.sheafPullbackComp' (smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg) A _ _ _

/-- At the tautological presentation of the composite, the factored comparison is the
comparison of `AlgebraicGeometry.smallEtaleSheafPullbackCompIso`. -/
public theorem smallEtaleSheafPullbackFactoredCompIso_rfl (B : BigEtaleSite.{u})
    (X Y Z : B.Scheme) (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type uA) [Category.{vA} A]
    [((smallEtaleBaseChange B g).sheafPushforwardContinuous A
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B Y.obj Y.property)).IsRightAdjoint]
    [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).IsRightAdjoint]
    [((smallEtaleBaseChange B (f ≫ g)).sheafPushforwardContinuous A
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B X.obj X.property)).IsRightAdjoint] :
    smallEtaleSheafPullbackFactoredCompIso B X Y Z f g (f ≫ g) rfl A =
      smallEtaleSheafPullbackCompIso B X Y Z f g A :=
  congrArg
    (fun e => Functor.sheafPullbackComp' e A
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property))
    (by simp [smallEtaleBaseChange_factoredCompIso])

section Comp

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
  (hfg : f ≫ g = fg) (A : Type uA) [Category.{vA} A]
  [((smallEtaleBaseChange B g).sheafPushforwardContinuous A
    (SmallEtale.topology B Z.obj Z.property)
    (SmallEtale.topology B Y.obj Y.property)).IsRightAdjoint]
  [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
    (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X.obj X.property)).IsRightAdjoint]
  [((smallEtaleBaseChange B fg).sheafPushforwardContinuous A
    (SmallEtale.topology B Z.obj Z.property)
    (SmallEtale.topology B X.obj X.property)).IsRightAdjoint]

/-- The unit characterisation of the factored composite comparison. -/
public theorem unit_sheafPullbackFactoredCompIso
    (F : Sheaf (SmallEtale.topology B Z.obj Z.property) A) :
    ((smallEtaleBaseChange B fg).sheafAdjunctionContinuous A
          (SmallEtale.topology B Z.obj Z.property)
          (SmallEtale.topology B X.obj X.property)).unit.app F ≫
        (Functor.sheafPushforwardContinuousComp'
          (smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg) A
          (SmallEtale.topology B Z.obj Z.property)
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X.obj X.property)).inv.app
            (((smallEtaleBaseChange B fg).sheafPullback A
              (SmallEtale.topology B Z.obj Z.property)
              (SmallEtale.topology B X.obj X.property)).obj F) =
      (((smallEtaleBaseChange B g).sheafAdjunctionContinuous A
            (SmallEtale.topology B Z.obj Z.property)
            (SmallEtale.topology B Y.obj Y.property)).comp
          ((smallEtaleBaseChange B f).sheafAdjunctionContinuous A
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property))).unit.app F ≫
        ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
            (SmallEtale.topology B Y.obj Y.property)
            (SmallEtale.topology B X.obj X.property) ⋙
          (smallEtaleBaseChange B g).sheafPushforwardContinuous A
            (SmallEtale.topology B Z.obj Z.property)
            (SmallEtale.topology B Y.obj Y.property)).map
          ((smallEtaleSheafPullbackFactoredCompIso B X Y Z f g fg hfg A).hom.app F) :=
  unit_conjugateEquiv_symm _ _ _ F

omit [((smallEtaleBaseChange B g).sheafPushforwardContinuous A
    (SmallEtale.topology B Z.obj Z.property)
    (SmallEtale.topology B Y.obj Y.property)).IsRightAdjoint]
  [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
    (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X.obj X.property)).IsRightAdjoint]
  [((smallEtaleBaseChange B fg).sheafPushforwardContinuous A
    (SmallEtale.topology B Z.obj Z.property)
    (SmallEtale.topology B X.obj X.property)).IsRightAdjoint] in
/-- The composite pushforward comparison, on sections, is restriction along the site
comparison. -/
public theorem sheafPushforwardContinuousComp'_inv_app_hom_app
    (M : Sheaf (SmallEtale.topology B X.obj X.property) A)
    (V : SmallEtale B Z.obj Z.property) :
    ((Functor.sheafPushforwardContinuousComp'
          (smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg) A
          (SmallEtale.topology B Z.obj Z.property)
          (SmallEtale.topology B Y.obj Y.property)
          (SmallEtale.topology B X.obj X.property)).inv.app M).hom.app (op V) =
      M.obj.map ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app V).op :=
  Category.comp_id
    (M.obj.map ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app V).op)

end Comp

section Id

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (q : T ⟶ S) (A : Type uA) [Category.{vA} A]
  [((smallEtaleBaseChange B q).sheafPushforwardContinuous A
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

/-- Pulling a section back along the identity of its own base change is the unit. -/
public theorem pullbackSectionAlongHom_id
    (F : Sheaf (SmallEtale.topology B S.obj S.property) A)
    (V : SmallEtale B S.obj S.property) :
    pullbackSectionAlongHom B q A F V ((smallEtaleBaseChange B q).obj V) (𝟙 _) =
      (((smallEtaleBaseChange B q).sheafAdjunctionContinuous A
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).unit.app F).hom.app (op V) :=
  (congrArg (fun m => (((smallEtaleBaseChange B q).sheafAdjunctionContinuous A
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).unit.app F).hom.app (op V) ≫ m)
      (CategoryTheory.Functor.map_id
        ((((smallEtaleBaseChange B q).sheafPullback A
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj F).obj)
        (op ((smallEtaleBaseChange B q).obj V)))).trans (Category.comp_id _)

end Id

section CompSections

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
  (hfg : f ≫ g = fg) (A : Type uA) [Category.{vA} A]
  [((smallEtaleBaseChange B g).sheafPushforwardContinuous A
    (SmallEtale.topology B Z.obj Z.property)
    (SmallEtale.topology B Y.obj Y.property)).IsRightAdjoint]
  [((smallEtaleBaseChange B f).sheafPushforwardContinuous A
    (SmallEtale.topology B Y.obj Y.property)
    (SmallEtale.topology B X.obj X.property)).IsRightAdjoint]
  [((smallEtaleBaseChange B fg).sheafPushforwardContinuous A
    (SmallEtale.topology B Z.obj Z.property)
    (SmallEtale.topology B X.obj X.property)).IsRightAdjoint]

/-- The section-level composition law for the factored composite comparison. -/
public theorem pullbackSectionAlongHom_comp
    (F : Sheaf (SmallEtale.topology B Z.obj Z.property) A)
    (V : SmallEtale B Z.obj Z.property) :
    pullbackSectionAlongHom B g A F V ((smallEtaleBaseChange B g).obj V) (𝟙 _) ≫
        pullbackSectionAlongHom B f A
          (((smallEtaleBaseChange B g).sheafPullback A
            (SmallEtale.topology B Z.obj Z.property)
            (SmallEtale.topology B Y.obj Y.property)).obj F)
          ((smallEtaleBaseChange B g).obj V)
          ((smallEtaleBaseChange B f).obj ((smallEtaleBaseChange B g).obj V)) (𝟙 _) ≫
        ((smallEtaleSheafPullbackFactoredCompIso B X Y Z f g fg hfg A).hom.app F).hom.app
          (op ((smallEtaleBaseChange B f).obj ((smallEtaleBaseChange B g).obj V))) =
      pullbackSectionAlongHom B fg A F V
        ((smallEtaleBaseChange B f).obj ((smallEtaleBaseChange B g).obj V))
        ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app V) := by
  have h := sheaf_hom_app_congr (unit_sheafPullbackFactoredCompIso B f g fg hfg A F) (op V)
  rw [Adjunction.comp_unit_app] at h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    sheafPushforwardContinuousComp'_inv_app_hom_app B f g fg hfg A] at h
  rw [pullbackSectionAlongHom_id, pullbackSectionAlongHom_id]
  exact (Category.assoc _ _ _).symm.trans h.symm

end CompSections

section Lifts

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (q : T ⟶ S) (x : GeometricPoint T.obj)

/-- The lift of a point of the fibre to the base change composes with the projection back to
the point itself. -/
public theorem geometricPointFiberBaseChangeEquiv_comp_fst
    (V : SmallEtale B S.obj S.property)
    (w : (geometricPointFiber B S.obj S.property (x.map (B.inclusion.map q))).obj V) :
    (geometricPointFiberBaseChangeEquiv B q x V w).1 ≫
        B.inclusion.map (pullback.fst V.obj.hom q) = w.1 := by
  rw [geometricPointFiberBaseChangeEquiv_apply_val]
  exact (congrArg (fun k => k ≫ B.inclusion.map (pullback.fst V.obj.hom q))
      (Category.comp_id _)).trans
    (((IsPullback.of_hasPullback V.obj.hom q).map B.inclusion).lift_fst _ _ _)

/-- The lift of a point of the fibre to the base change satisfies the compatibility hypothesis
of the germ formula, with the identity as comparison morphism. -/
public theorem geometricPointFiberBaseChangeEquiv_ha
    (V : SmallEtale B S.obj S.property)
    (w : (geometricPointFiber B S.obj S.property (x.map (B.inclusion.map q))).obj V) :
    (geometricPointFiberBaseChangeEquiv B q x V w).1 ≫
        (SmallEtale.toScheme B T.obj T.property).map
          (𝟙 ((smallEtaleBaseChange B q).obj V)) ≫
        B.inclusion.map (pullback.fst V.obj.hom q) = w.1 := by
  have hid : (SmallEtale.toScheme B T.obj T.property).map
      (𝟙 ((smallEtaleBaseChange B q).obj V)) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  rw [hid, Category.id_comp]
  exact geometricPointFiberBaseChangeEquiv_comp_fst B q x V w

end Lifts

section AbelianGerm

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (q : T ⟶ S) (x : GeometricPoint T.obj)
  (F : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v})

/-- The comparison of the stalk of an inverse image with the stalk at the image point sends the
germ of a pulled-back section to the germ of the original section. -/
public theorem etaleGerm_pullbackSectionAlongHom
    (U : SmallEtale B T.obj T.property) (u : (geometricPointFiber B T.obj T.property x).obj U)
    (V : SmallEtale B S.obj S.property)
    (w : (geometricPointFiber B S.obj S.property (x.map (B.inclusion.map q))).obj V)
    (a : U ⟶ (smallEtaleBaseChange B q).obj V)
    (ha : u.1 ≫ (SmallEtale.toScheme B T.obj T.property).map a ≫
      B.inclusion.map (pullback.fst V.obj.hom q) = w.1)
    (τ : F.obj.obj (op V)) :
    (etaleStalkSmallEtalePullObjIso B q x AddCommGrpCat.{max (u + 1) v} F).hom
        (SmallEtale.etaleGerm B T.obj T.property x
          ((((smallEtaleBaseChange B q).sheafPullback AddCommGrpCat.{max (u + 1) v}
            (SmallEtale.topology B S.obj S.property)
            (SmallEtale.topology B T.obj T.property)).obj F).obj) U u
          (pullbackSectionAlongHom B q AddCommGrpCat.{max (u + 1) v} F V U a τ)) =
      SmallEtale.etaleGerm B S.obj S.property
        (x.map (B.inclusion.map q)) F.obj V w τ := by
  have h := ConcreteCategory.congr_hom
    (etaleStalkSmallEtalePullObjIso_germ B q x AddCommGrpCat.{max (u + 1) v} F
      ((geometricPointFiber B T.obj T.property x).elementsMk U u)
      ((geometricPointFiber B S.obj S.property
        (x.map (B.inclusion.map q))).elementsMk V w) a ha) τ
  simp only [ConcreteCategory.comp_apply] at h
  exact h

/-- The inverse form of `AlgebraicGeometry.etaleGerm_pullbackSectionAlongHom`: the comparison of
stalks carries the germ of a section to the germ of its pullback. -/
public theorem etaleGerm_etaleStalkSmallEtalePullObjIso_inv
    (U : SmallEtale B T.obj T.property) (u : (geometricPointFiber B T.obj T.property x).obj U)
    (V : SmallEtale B S.obj S.property)
    (w : (geometricPointFiber B S.obj S.property (x.map (B.inclusion.map q))).obj V)
    (a : U ⟶ (smallEtaleBaseChange B q).obj V)
    (ha : u.1 ≫ (SmallEtale.toScheme B T.obj T.property).map a ≫
      B.inclusion.map (pullback.fst V.obj.hom q) = w.1)
    (τ : F.obj.obj (op V)) :
    (etaleStalkSmallEtalePullObjIso B q x AddCommGrpCat.{max (u + 1) v} F).inv
        (SmallEtale.etaleGerm B S.obj S.property
          (x.map (B.inclusion.map q)) F.obj V w τ) =
      SmallEtale.etaleGerm B T.obj T.property x
        ((((smallEtaleBaseChange B q).sheafPullback AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj F).obj) U u
        (pullbackSectionAlongHom B q AddCommGrpCat.{max (u + 1) v} F V U a τ) := by
  have h2 := ConcreteCategory.congr_hom
    (etaleStalkSmallEtalePullObjIso B q x AddCommGrpCat.{max (u + 1) v} F).hom_inv_id
    (SmallEtale.etaleGerm B T.obj T.property x
      ((((smallEtaleBaseChange B q).sheafPullback AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).obj F).obj) U u
      (pullbackSectionAlongHom B q AddCommGrpCat.{max (u + 1) v} F V U a τ))
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h2
  rw [← etaleGerm_pullbackSectionAlongHom B q x F U u V w a ha τ]
  exact h2

/-- The inverse stalk comparison sends the germ of a section to the germ, at the canonical lift of
the point, of its pullback along the identity of the base change. -/
private theorem etaleGerm_etaleStalkSmallEtalePullObjIso_inv_lift
    (V : SmallEtale B S.obj S.property)
    (w : (geometricPointFiber B S.obj S.property (x.map (B.inclusion.map q))).obj V)
    (τ : F.obj.obj (op V)) :
    (etaleStalkSmallEtalePullObjIso B q x AddCommGrpCat.{max (u + 1) v} F).inv
        (SmallEtale.etaleGerm B S.obj S.property
          (x.map (B.inclusion.map q)) F.obj V w τ) =
      SmallEtale.etaleGerm B T.obj T.property x
        ((((smallEtaleBaseChange B q).sheafPullback AddCommGrpCat.{max (u + 1) v}
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj F).obj)
        ((smallEtaleBaseChange B q).obj V) (geometricPointFiberBaseChangeEquiv B q x V w)
        (pullbackSectionAlongHom B q AddCommGrpCat.{max (u + 1) v} F V
          ((smallEtaleBaseChange B q).obj V) (𝟙 _) τ) :=
  etaleGerm_etaleStalkSmallEtalePullObjIso_inv B q x F _ _ V w (𝟙 _)
    (geometricPointFiberBaseChangeEquiv_ha B q x V w) τ

end AbelianGerm

section StalkFunctor

/-- The stalk functor on presheaves sends the germ of a section to the germ of its image. -/
public theorem etaleStalkPresheafFunctor_map_etaleGerm (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (t : GeometricPoint S)
    {P Q : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}} (φ : P ⟶ Q)
    (W : SmallEtale B S hS) (p : (geometricPointFiber B S hS t).obj W) (σ : P.obj (op W)) :
    (etaleStalkPresheafFunctor B S hS t AddCommGrpCat.{max (u + 1) v}).map φ
        (SmallEtale.etaleGerm B S hS t P W p σ) =
      SmallEtale.etaleGerm B S hS t Q W p (φ.app (op W) σ) := by
  have h := ConcreteCategory.congr_hom
    (colimit.ι_map (Functor.whiskerLeft (CategoryOfElements.π (geometricPointFiber B S hS t)).op φ)
      (op ((geometricPointFiber B S hS t).elementsMk W p))) σ
  exact h

end StalkFunctor

section CompGerm

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
  (hfg : f ≫ g = fg) (x : GeometricPoint X.obj)

/-- The composite of the two canonical lifts satisfies the compatibility hypothesis of the germ
formula for the factored composite comparison. -/
public theorem compIso_lift_compat (V : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property
      ((x.map (B.inclusion.map f)).map (B.inclusion.map g))).obj V)
    (w' : (geometricPointFiber B Z.obj Z.property (x.map (B.inclusion.map fg))).obj V)
    (hw : w.1 = w'.1) :
    (geometricPointFiberBaseChangeEquiv B f x ((smallEtaleBaseChange B g).obj V)
        (geometricPointFiberBaseChangeEquiv B g (x.map (B.inclusion.map f)) V w)).1 ≫
      (SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app V) ≫
      B.inclusion.map (pullback.fst V.obj.hom fg) = w'.1 := by
  have hfst := smallEtaleBaseChange_factoredCompIso_hom_app_fst B X Y Z f g fg hfg V
  have h1 := geometricPointFiberBaseChangeEquiv_comp_fst B g (x.map (B.inclusion.map f)) V w
  have h2 := geometricPointFiberBaseChangeEquiv_comp_fst B f x
    ((smallEtaleBaseChange B g).obj V)
    (geometricPointFiberBaseChangeEquiv B g (x.map (B.inclusion.map f)) V w)
  have key : (SmallEtale.toScheme B X.obj X.property).map
        ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app V) ≫
      B.inclusion.map (pullback.fst V.obj.hom fg) =
    B.inclusion.map (pullback.fst ((smallEtaleBaseChange B g).obj V).obj.hom f) ≫
      B.inclusion.map (pullback.fst V.obj.hom g) :=
    (B.inclusion.map_comp _ _).symm.trans
      ((congrArg B.inclusion.map hfst).trans (B.inclusion.map_comp _ _))
  rw [← hw, key]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ B.inclusion.map (pullback.fst V.obj.hom g)) h2).trans h1)

/-- **Stacks 021J** and **Stacks 03Q1** on germs: the comparison of the composite inverse image
with the inverse image along the composite sends the germ of a section, transported through the
two stalk comparisons, to its germ transported through the comparison for the composite. -/
public theorem etaleGerm_smallEtaleSheafPullbackFactoredCompIso
    (F : Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{max (u + 1) v})
    (V : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property
      ((x.map (B.inclusion.map f)).map (B.inclusion.map g))).obj V)
    (w' : (geometricPointFiber B Z.obj Z.property (x.map (B.inclusion.map fg))).obj V)
    (hw : w.1 = w'.1) (τ : F.obj.obj (op V)) :
    ((etaleStalkPresheafFunctor B X.obj X.property x AddCommGrpCat.{max (u + 1) v}).map
        ((smallEtaleSheafPullbackFactoredCompIso B X Y Z f g fg hfg
          AddCommGrpCat.{max (u + 1) v}).hom.app F).hom)
      ((etaleStalkSmallEtalePullObjIso B f x AddCommGrpCat.{max (u + 1) v}
          (((smallEtaleBaseChange B g).sheafPullback AddCommGrpCat.{max (u + 1) v}
            (SmallEtale.topology B Z.obj Z.property)
            (SmallEtale.topology B Y.obj Y.property)).obj F)).inv
        ((etaleStalkSmallEtalePullObjIso B g (x.map (B.inclusion.map f))
            AddCommGrpCat.{max (u + 1) v} F).inv
          (SmallEtale.etaleGerm B Z.obj Z.property
            ((x.map (B.inclusion.map f)).map (B.inclusion.map g)) F.obj V w τ))) =
      (etaleStalkSmallEtalePullObjIso B fg x AddCommGrpCat.{max (u + 1) v} F).inv
        (SmallEtale.etaleGerm B Z.obj Z.property
          (x.map (B.inclusion.map fg)) F.obj V w' τ) := by
  have hg := etaleGerm_etaleStalkSmallEtalePullObjIso_inv_lift B g (x.map (B.inclusion.map f))
    F V w τ
  have hf := etaleGerm_etaleStalkSmallEtalePullObjIso_inv_lift B f x
    (((smallEtaleBaseChange B g).sheafPullback AddCommGrpCat.{max (u + 1) v}
      (SmallEtale.topology B Z.obj Z.property)
      (SmallEtale.topology B Y.obj Y.property)).obj F)
    ((smallEtaleBaseChange B g).obj V)
    (geometricPointFiberBaseChangeEquiv B g (x.map (B.inclusion.map f)) V w)
    (pullbackSectionAlongHom B g AddCommGrpCat.{max (u + 1) v} F V
      ((smallEtaleBaseChange B g).obj V) (𝟙 _) τ)
  have h3 := ConcreteCategory.congr_hom
    (pullbackSectionAlongHom_comp B f g fg hfg AddCommGrpCat.{max (u + 1) v} F V) τ
  simp only [ConcreteCategory.comp_apply] at h3
  have hc := etaleGerm_etaleStalkSmallEtalePullObjIso_inv B fg x F
    ((smallEtaleBaseChange B f).obj ((smallEtaleBaseChange B g).obj V))
    (geometricPointFiberBaseChangeEquiv B f x ((smallEtaleBaseChange B g).obj V)
      (geometricPointFiberBaseChangeEquiv B g (x.map (B.inclusion.map f)) V w))
    V w' ((smallEtaleBaseChange_factoredCompIso B X Y Z f g fg hfg).hom.app V)
    (compIso_lift_compat B f g fg hfg x V w w' hw) τ
  have h4 := etaleStalkPresheafFunctor_map_etaleGerm B X.obj X.property x
    ((smallEtaleSheafPullbackFactoredCompIso B X Y Z f g fg hfg
      AddCommGrpCat.{max (u + 1) v}).hom.app F).hom
    ((smallEtaleBaseChange B f).obj ((smallEtaleBaseChange B g).obj V))
    (geometricPointFiberBaseChangeEquiv B f x ((smallEtaleBaseChange B g).obj V)
      (geometricPointFiberBaseChangeEquiv B g (x.map (B.inclusion.map f)) V w))
    (pullbackSectionAlongHom B f AddCommGrpCat.{max (u + 1) v}
      (((smallEtaleBaseChange B g).sheafPullback AddCommGrpCat.{max (u + 1) v}
        (SmallEtale.topology B Z.obj Z.property)
        (SmallEtale.topology B Y.obj Y.property)).obj F)
      ((smallEtaleBaseChange B g).obj V)
      ((smallEtaleBaseChange B f).obj ((smallEtaleBaseChange B g).obj V)) (𝟙 _)
      (pullbackSectionAlongHom B g AddCommGrpCat.{max (u + 1) v} F V
        ((smallEtaleBaseChange B g).obj V) (𝟙 _) τ))
  rw [h3] at h4
  rw [hg, hf]
  exact h4.trans hc.symm

end CompGerm

end AlgebraicGeometry

end
