module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompPiece
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenCoverStalkCovariance
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompactification
public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupportProper

/-!
# The composition comparison on an open piece, on geometric stalks

This file computes the piece `(jX ≫ f ≫ g)_!(F|_{X'}) ⟶ g_!(f_! F)` of the comparison of
Stacks 0F6T (`AlgebraicGeometry.SmallEtale.compPieceMap`) on the stalk decompositions of
Stacks 0F5F: at a geometric point `z̄` of `Z`, the summand of a point `x̄` of `X'` over `z̄` goes to
the summand of `f(x̄)` in the decomposition of `g_!(f_! F)`, and inside it to the summand of `x̄` in
the decomposition of `(f_! F)_{f(x̄)}`.

## Main results

* `AlgebraicGeometry.SmallEtale.compPieceMap_stalk` — the stalk formula.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open scoped DirectSum

universe u v

namespace AlgebraicGeometry.SmallEtale

section Generic

variable (B : BigEtaleSite.{u})

/-- The comparison of the two descriptions of restriction to an open subscheme is restriction of
the unit of the inverse image along the unit of the post-composition adjunction. -/
public theorem openRestrictionIso_hom_app_eq {Y' Y : B.Scheme} (jY : Y' ⟶ Y)
    [IsOpenImmersion (B.inclusion.map jY)]
    (G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (Q : SmallEtale B Y'.obj Y'.property) (t : G.obj.obj (op ((openPostcompose B jY).obj Q))) :
    ((openRestrictionIso.{u, v} B jY).hom.app G).hom.app (op Q) t =
      pullbackSectionAlongHom B jY AddCommGrpCat.{max (u + 1) v} G
        ((openPostcompose B jY).obj Q) Q ((openPostcomposeAdjunction B jY).unit.app Q) t := by
  set c := (openPostcomposeAdjunction B jY).unit.app Q
  set k := (openPostcomposeAdjunction B jY).counit.app ((openPostcompose B jY).obj Q)
  have htri : (openPostcompose B jY).map c ≫ k = 𝟙 _ :=
    (openPostcomposeAdjunction B jY).left_triangle_components Q
  have hnat : ((openRestrictionIso.{u, v} B jY).hom.app G).hom.app (op Q)
        (G.obj.map ((openPostcompose B jY).map c).op (G.obj.map k.op t)) =
      ((openRestriction.{u, v} B jY).obj G).obj.map c.op
        (((openRestrictionIso.{u, v} B jY).hom.app G).hom.app
          (op ((smallEtaleBaseChange B jY).obj ((openPostcompose B jY).obj Q)))
            (G.obj.map k.op t)) :=
    ConcreteCategory.congr_hom
      (((openRestrictionIso.{u, v} B jY).hom.app G).hom.naturality c.op) _
  have hid : G.obj.map ((openPostcompose B jY).map c).op (G.obj.map k.op t) = t := by
    rw [← ConcreteCategory.comp_apply, ← G.obj.map_comp, ← op_comp, htri, op_id]
    simp
  rw [hid, openRestrictionIso_unit_app.{u, v} B jY G ((openPostcompose B jY).obj Q) t] at hnat
  exact hnat.trans (ConcreteCategory.comp_apply _ _ _).symm

/-- **Stacks 03Q1 for the restriction to an open subscheme, on germs**: the identification of the
stalk of `G|_{Y'}` at a geometric point of `Y'` with the stalk of `G` at its image sends the germ of
the restriction of a section to the germ of the section. -/
public theorem etaleStalkSmallEtalePullObjIso_germ_openRestrictionIso {Y' Y : B.Scheme}
    (jY : Y' ⟶ Y) [IsOpenImmersion (B.inclusion.map jY)]
    (G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (y : GeometricPoint Y'.obj) (Q : SmallEtale B Y'.obj Y'.property)
    (q : (geometricPointFiber B Y'.obj Y'.property y).obj Q)
    (q' : (geometricPointFiber B Y.obj Y.property (y.map (B.inclusion.map jY))).obj
      ((openPostcompose B jY).obj Q)) (hq : q'.1 = q.1)
    (t : G.obj.obj (op ((openPostcompose B jY).obj Q))) :
    (etaleStalkSmallEtalePullObjIso B jY y AddCommGrpCat.{max (u + 1) v} G).hom
        (etaleGerm B Y'.obj Y'.property y ((openRestriction.{u, v} B jY).obj G).obj Q q
          (((openRestrictionIso.{u, v} B jY).hom.app G).hom.app (op Q) t)) =
      etaleGerm B Y.obj Y.property (y.map (B.inclusion.map jY)) G.obj
        ((openPostcompose B jY).obj Q) q' t := by
  rw [openRestrictionIso_hom_app_eq]
  refine etaleGerm_pullbackSectionAlongHom B jY G y _ q' Q q _ ?_ t
  have h := (B.inclusion.map_comp _ _).symm.trans
    ((congrArg B.inclusion.map (openPostcomposeAdjunction_unit_left_fst B jY Q)).trans
      (B.inclusion.map_id _))
  exact (congrArg (fun m => q.1 ≫ m) h).trans ((Category.comp_id _).trans hq.symm)

/-- The stalk decomposition of Stacks 0F5F on the germ of the sheafification of a colimit
generator is the germ decomposition of the generator. -/
public theorem fShriekStalkIso_hom_germ_generator {X Y : B.Scheme} (f : X ⟶ Y)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (s : GeometricPoint Y.obj) (V : SmallEtale B Y.obj Y.property)
    (w : (geometricPointFiber B Y.obj Y.property s).obj V) (E : FiniteSupport B f V)
    (a : (finiteSupportDiagram B f F V).obj E) :
    (fShriekStalkIso.{u, v} B f s F).hom
        (etaleGerm B Y.obj Y.property s ((fShriekFunctor.{u, v} B f).obj F).obj V w
          ((finiteSupportPushforwardGenerator B f F V E ≫
            (toSheafify (SmallEtale.topology B Y.obj Y.property)
              ((finiteSupportPushforward.{u, max (u + 1) v} B f
                (fun _ => inferInstance)).val.obj F)).app (op V)) a)) =
      fiberStalkSum.{u, max (u + 1) v} B f s F V w E a := by
  have h1 := ConcreteCategory.congr_hom (colimit_ι_comp_etaleStalkSheafificationMap B Y.obj
    Y.property s ((finiteSupportPushforward.{u, max (u + 1) v} B f
      (fun _ => inferInstance)).val.obj F) (op (Functor.elementsMk _ V w)))
    ((finiteSupportPushforwardGenerator B f F V E) a)
  have h2 := ConcreteCategory.congr_hom (fShriekStalkIso_comp_sheafification.{u, v} B f s F)
    (finiteSupportStalkGenerator.{u, v} B f F s
      (Functor.elementsMk (geometricPointFiber B Y.obj Y.property s) V w) E a)
  have h3 := ConcreteCategory.congr_hom (finiteSupportStalkGenerator_comp_stalkIso.{u, v}
    B f F s V w E) a
  simp only [ConcreteCategory.comp_apply] at h1 h2 h3
  exact (congrArg (fShriekStalkIso.{u, v} B f s F).hom h1.symm).trans (h2.trans h3)

end Generic

section Lifts

variable (B : BigEtaleSite.{u}) {X Y Z X' Y' : B.Scheme}
  {f : X ⟶ Y} (g : Y ⟶ Z) {jX : X' ⟶ X} {jY : Y' ⟶ Y} {f' : X' ⟶ Y'}
  [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)]
  (sq : f' ≫ jY = jX ≫ f) (hsq : IsPullback f' jX jY f)

/-- The chart inclusion lies over the projections to the test object. -/
public theorem compChartInclusion_fiberProjection (W : SmallEtale B Z.obj Z.property) :
    (SmallEtale.toScheme B X.obj X.property).map (compChartInclusion B g sq hsq W) ≫
        B.inclusion.map (fiberProjection B (f ≫ g) W) =
      B.inclusion.map (baseChangeObjProjection B f (compChartBase B g jY W)) ≫
        B.inclusion.map (fiberProjection B (jY ≫ g) W) := by
  let e := (SmallEtale.toScheme B X.obj X.property).mapIso (compChartIso B g sq hsq W)
  have h1 : e.hom ≫ B.inclusion.map (baseChangeObjProjection B f (compChartBase B g jY W)) ≫
        B.inclusion.map (fiberProjection B (jY ≫ g) W) =
      B.inclusion.map (pullback.fst W.obj.hom (jX ≫ f ≫ g)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ B.inclusion.map (fiberProjection B (jY ≫ g) W))
        ((B.inclusion.map_comp _ _).symm.trans
          (congrArg B.inclusion.map (compChartHom_proj B g sq W)))).trans
      ((B.inclusion.map_comp _ _).symm.trans
        (congrArg B.inclusion.map (compChartMap_fst B g sq W))))
  calc (SmallEtale.toScheme B X.obj X.property).map (compChartInclusion B g sq hsq W) ≫
        B.inclusion.map (fiberProjection B (f ≫ g) W)
      = e.inv ≫ openBaseChangeHom B jX (f ≫ g) W ≫
          B.inclusion.map (fiberProjection B (f ≫ g) W) :=
        (congrArg (· ≫ B.inclusion.map (fiberProjection B (f ≫ g) W))
          (compChartInclusion_toScheme B g sq hsq W)).trans (Category.assoc _ _ _)
    _ = e.inv ≫ e.hom ≫ B.inclusion.map (baseChangeObjProjection B f (compChartBase B g jY W)) ≫
          B.inclusion.map (fiberProjection B (jY ≫ g) W) :=
        congrArg (e.inv ≫ ·) ((openBaseChangeHom_comp B jX (f ≫ g) W).trans h1.symm)
    _ = _ := e.inv_hom_id_assoc _

/-- The chart inclusion lies over `X`. -/
public theorem compChartInclusion_hom (W : SmallEtale B Z.obj Z.property) :
    (SmallEtale.toScheme B X.obj X.property).map (compChartInclusion B g sq hsq W) ≫
        B.inclusion.map (baseChange B (f ≫ g) W).obj.hom =
      B.inclusion.map (baseChange B f (compChartBase B g jY W)).obj.hom :=
  (B.inclusion.map_comp _ _).symm.trans
    (congrArg B.inclusion.map (Over.w (compChartInclusion B g sq hsq W).hom))

variable (s : GeometricPoint Z.obj)

/-- The lift into `W ×_Z Y'` of a point of the geometric fibre of `jY ≫ g`, as a lift of its
image in `Y` into the object `W ×_Z Y'` of the small étale site of `Y`. -/
public def compChartBaseLift (W : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (y : GeometricFiberPoint B (jY ≫ g) s) :
    (geometricPointFiber B Y.obj Y.property
      ((openFiberPoint B jY g s y).toGeometricPoint B g s)).obj (compChartBase B g jY W) :=
  ⟨fiberPointLift B (jY ≫ g) s W w y, (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ B.inclusion.map jY) (fiberPointLift_comp_snd B (jY ≫ g) s W w y))⟩

/-- The lift into `X ×_Y (W ×_Z Y')` of a point of `X` over the image of a point of the
geometric fibre of `jY ≫ g`, carried by the chart inclusion to the lift into `W ×_Z X`. -/
public theorem fiberPointLift_compChartInclusion (W : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (y : GeometricFiberPoint B (jY ≫ g) s)
    (x : GeometricFiberPoint B f ((openFiberPoint B jY g s y).toGeometricPoint B g s))
    (x' : GeometricFiberPoint B (f ≫ g) s) (hx : x'.1 = x.1) :
    fiberPointLift B f _ (compChartBase B g jY W) (compChartBaseLift B g s W w y) x ≫
        (SmallEtale.toScheme B X.obj X.property).map (compChartInclusion B g sq hsq W) =
      fiberPointLift B (f ≫ g) s W w x' := by
  let lf := fiberPointLift B f _ (compChartBase B g jY W) (compChartBaseLift B g s W w y) x
  let k := (SmallEtale.toScheme B X.obj X.property).map (compChartInclusion B g sq hsq W)
  refine ((IsPullback.of_hasPullback W.obj.hom (f ≫ g)).map B.inclusion).hom_ext ?_ ?_
  · calc (lf ≫ k) ≫ B.inclusion.map (pullback.fst W.obj.hom (f ≫ g))
        = lf ≫ (k ≫ B.inclusion.map (fiberProjection B (f ≫ g) W)) := Category.assoc _ _ _
      _ = lf ≫ (B.inclusion.map (baseChangeObjProjection B f (compChartBase B g jY W)) ≫
            B.inclusion.map (fiberProjection B (jY ≫ g) W)) :=
          congrArg (lf ≫ ·) (compChartInclusion_fiberProjection B g sq hsq W)
      _ = (lf ≫ B.inclusion.map (pullback.fst (compChartBase B g jY W).obj.hom f)) ≫
            B.inclusion.map (fiberProjection B (jY ≫ g) W) := (Category.assoc _ _ _).symm
      _ = fiberPointLift B (jY ≫ g) s W w y ≫
            B.inclusion.map (pullback.fst W.obj.hom (jY ≫ g)) :=
          congrArg (· ≫ B.inclusion.map (fiberProjection B (jY ≫ g) W))
            (fiberPointLift_comp_fst B f _ (compChartBase B g jY W)
              (compChartBaseLift B g s W w y) x)
      _ = w.1 := fiberPointLift_comp_fst B (jY ≫ g) s W w y
      _ = fiberPointLift B (f ≫ g) s W w x' ≫
            B.inclusion.map (pullback.fst W.obj.hom (f ≫ g)) :=
          (fiberPointLift_comp_fst B (f ≫ g) s W w x').symm
  · calc (lf ≫ k) ≫ B.inclusion.map (pullback.snd W.obj.hom (f ≫ g))
        = lf ≫ (k ≫ B.inclusion.map (baseChange B (f ≫ g) W).obj.hom) := Category.assoc _ _ _
      _ = lf ≫ B.inclusion.map (pullback.snd (compChartBase B g jY W).obj.hom f) :=
          congrArg (lf ≫ ·) (compChartInclusion_hom B g sq hsq W)
      _ = x.1 := fiberPointLift_comp_snd B f _ (compChartBase B g jY W)
            (compChartBaseLift B g s W w y) x
      _ = fiberPointLift B (f ≫ g) s W w x' ≫
            B.inclusion.map (pullback.snd W.obj.hom (f ≫ g)) :=
          hx.symm.trans (fiberPointLift_comp_snd B (f ≫ g) s W w x').symm

end Lifts

section Component

variable (B : BigEtaleSite.{u}) {X Y Z X' Y' : B.Scheme}
  {f : X ⟶ Y} (g : Y ⟶ Z) {jX : X' ⟶ X} {jY : Y' ⟶ Y} {f' : X' ⟶ Y'}
  [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)]
  [IsSeparated (B.inclusion.map (jY ≫ g))]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  (sq : f' ≫ jY = jX ≫ f) (hsq : IsPullback f' jX jY f)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
  (s : GeometricPoint Z.obj)

/-- The point of the geometric fibre of `jY ≫ g` below a point of the geometric fibre of
`jX ≫ f ≫ g`. -/
public def compFiberBase (x : GeometricFiberPoint B (jX ≫ f ≫ g) s) :
    GeometricFiberPoint B (jY ≫ g) s :=
  ⟨x.1 ≫ B.inclusion.map f', by
    have h : B.inclusion.map f' ≫ B.inclusion.map (jY ≫ g) =
        B.inclusion.map (jX ≫ f ≫ g) := by
      rw [← Functor.map_comp, ← Category.assoc, sq, Category.assoc]
    rw [Category.assoc, h]
    exact x.2⟩

/-- A point of the geometric fibre of `jX ≫ f ≫ g`, read in `X` as a point over the image of the
point of the geometric fibre of `jY ≫ g` below it. -/
public def compFiberTop (x : GeometricFiberPoint B (jX ≫ f ≫ g) s) :
    GeometricFiberPoint B f ((openFiberPoint B jY g s
      (compFiberBase B g sq s x)).toGeometricPoint B g s) :=
  ⟨x.1 ≫ B.inclusion.map jX, by
    change (x.1 ≫ B.inclusion.map jX) ≫ B.inclusion.map f =
      (x.1 ≫ B.inclusion.map f') ≫ B.inclusion.map jY
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, sq]⟩

/-- **The transported generator on a component.** At the point of `X` over the image of a point
of the geometric fibre of `jY ≫ g`, the germ of the transported section of `F` is the germ of the
original section of `F|_{X'}`, read through the identification of the two stalks. -/
public theorem fiberStalkComponent_compChartGenMap (W : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (T : FiniteSupport B (jX ≫ f ≫ g) W)
    (a : supportedSections B X'.obj X'.property ((openRestriction.{u, v} B jX).obj F)
      (baseChange B (jX ≫ f ≫ g) W) T.1 (finiteSupport_isLocallyClosed B _ W T))
    (x : GeometricFiberPoint B (jX ≫ f ≫ g) s) :
    fiberStalkComponent.{u, max (u + 1) v} B f _ F (compChartBase B g jY W)
        (compChartBaseLift B g s W w (compFiberBase B g sq s x))
        (compChartSupport B g sq hsq W T)
        (compChartGenMap B g sq hsq F W T _ (imageFiniteSupport_coe B jX (f ≫ g) W T)
          (compChartSupport B g sq hsq W T) (compChartSupport_coe B g sq hsq W T) a)
        (compFiberTop B g sq s x) =
      (openFiberStalkIso.{u, v} B jX (f ≫ g) F s x).hom
        (fiberStalkComponent.{u, max (u + 1) v} B (jX ≫ f ≫ g) s
          ((openRestriction.{u, v} B jX).obj F) W w T a x) := by
  rw [← fiberStalkComponent_covarianceSectionMap B jX (f ≫ g) F s W w T a x]
  let D := imageFiniteSupport B jX (f ≫ g) W T
  let E := compChartSupport B g sq hsq W T
  let c := covarianceSectionMap B jX (f ≫ g) F W T _ (imageFiniteSupport_coe B jX (f ≫ g) W T) a
  let k := (SmallEtale.toScheme B X.obj X.property).map (compChartInclusion B g sq hsq W)
  let lf := fiberPointLift B f _ (compChartBase B g jY W)
    (compChartBaseLift B g s W w (compFiberBase B g sq s x)) (compFiberTop B g sq s x)
  let lh := fiberPointLift B (f ≫ g) s W w (openFiberPoint B jX (f ≫ g) s x)
  have hl : lf ≫ k = lh := fiberPointLift_compChartInclusion B g sq hsq s W w _ _ _ rfl
  have hk : Topology.IsOpenEmbedding k := by
    have : IsOpenImmersion k := isOpenImmersion_compChartInclusion B g sq hsq W
    exact k.isOpenEmbedding
  have hcob : (finiteSupportOpen B f _ E : Set _) =
      k.base ⁻¹' (finiteSupportOpen B (f ≫ g) W D : Set _) := by
    change coborder E.1 = k.base ⁻¹' coborder D.1
    rw [compChartSupport_coe]
    exact hk.coborder_preimage _
  have hpt : k.base (lf.base default) = lh.base default := by
    rw [← hl]
    rfl
  have hiff : HasFiberLift B f _ (compChartBase B g jY W)
      (compChartBaseLift B g s W w (compFiberBase B g sq s x)) E (compFiberTop B g sq s x) ↔
      HasFiberLift B (f ≫ g) s W w D (openFiberPoint B jX (f ≫ g) s x) := by
    change lf.base default ∈ (finiteSupportOpen B f _ E : Set _) ↔
      lh.base default ∈ (finiteSupportOpen B (f ≫ g) W D : Set _)
    rw [hcob, Set.mem_preimage, hpt]
  by_cases h : HasFiberLift B (f ≫ g) s W w D (openFiberPoint B jX (f ≫ g) s x)
  · rw [fiberStalkComponent_of_hasFiberLift _ _ _ _ _ _ _ _ _ (hiff.2 h),
      fiberStalkComponent_of_hasFiberLift _ _ _ _ _ _ _ _ _ h]
    refine etaleGerm_map B X.obj X.property _ F.obj
      (supportOpenMap B X.obj X.property (compChartInclusion B g sq hsq W) D.1
        (finiteSupport_isLocallyClosed B _ W D) E.1 (finiteSupport_isLocallyClosed B f _ E)
        (compChartSupport_coe B g sq hsq W T)) _ _ ?_ c.val
    apply openObjectLift_ext
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (supportOpenMap_map B X.obj X.property
      (compChartInclusion B g sq hsq W) D.1 (finiteSupport_isLocallyClosed B _ W D) E.1
      (finiteSupport_isLocallyClosed B f _ E) (compChartSupport_coe B g sq hsq W T))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ k) (openObjectLift_comp_ι _ _ _ _ _ _ _ _)).trans ?_
    exact hl.trans (openObjectLift_comp_ι B X.obj X.property
      ((openFiberPoint B jX (f ≫ g) s x).toGeometricPoint B (f ≫ g) s) (baseChange B (f ≫ g) W)
      (fiberPointElement B (f ≫ g) s W w (openFiberPoint B jX (f ≫ g) s x))
      (finiteSupportOpen B (f ≫ g) W D) h).symm
  · rw [fiberStalkComponent_of_not_hasFiberLift _ _ _ _ _ _ _ _ _ (fun h' => h (hiff.1 h')),
      fiberStalkComponent_of_not_hasFiberLift _ _ _ _ _ _ _ _ _ h]
    rfl

end Component

section TopOpen

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (G : Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{v})

/-- Restriction to a Zariski open which is the whole object is injective. -/
public theorem map_openObjectι_injective_of_eq_univ (V : SmallEtale B S hS)
    (U : ((SmallEtale.toScheme B S hS).obj V).Opens)
    (hU : (U : Set ((SmallEtale.toScheme B S hS).obj V)) = Set.univ) :
    Function.Injective (G.obj.map (openObjectι B S hS V U).op) := by
  obtain rfl : U = ⊤ := SetLike.coe_injective (hU.trans (TopologicalSpace.Opens.coe_top).symm)
  have : IsIso ((SmallEtale.toScheme B S hS).map (openObjectι B S hS V ⊤)) := by
    rw [openObjectι_map, ← Scheme.topIso_hom]
    infer_instance
  have : IsIso (openObjectι B S hS V ⊤) :=
    isIso_of_reflects_iso _ (SmallEtale.toScheme B S hS)
  exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance

end TopOpen

section Generator

variable (B : BigEtaleSite.{u}) {X Y Z X' Y' : B.Scheme}
  {f : X ⟶ Y} (g : Y ⟶ Z) {jX : X' ⟶ X} {jY : Y' ⟶ Y} {f' : X' ⟶ Y'}
  [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)]
  [IsSeparated (B.inclusion.map (jY ≫ g))]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  (sq : f' ≫ jY = jX ≫ f) (hsq : IsPullback f' jX jY f)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The image of a support finite over `W`, as a support of `jY ≫ g` finite over `W`. -/
public def compChartImageSupport (W : SmallEtale B Z.obj Z.property)
    (T : FiniteSupport B (jX ≫ f ≫ g) W) : FiniteSupport B (jY ≫ g) W :=
  ⟨(compChartImage B g sq W T :
      Set ((SmallEtale.toScheme B Y'.obj Y'.property).obj (baseChange B (jY ≫ g) W))), by
    obtain ⟨hC, hP⟩ := exists_isProperOver_compChartImage B g sq W T
    let C : Closeds ((SmallEtale.toScheme B Y'.obj Y'.property).obj (baseChange B (jY ≫ g) W)) :=
      ⟨compChartImage B g sq W T, hC⟩
    refine isFiniteSupport_of_exists_isProper B (jY ≫ g) W
      ⟨_, (Scheme.IdealSheafData.vanishingIdeal C).subschemeι, inferInstance, hP, ?_⟩
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl⟩

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [IsOpenImmersion (B.inclusion.map jX)] in
/-- The underlying set of `compChartImageSupport` is the image `compChartImage`. -/
public theorem compChartImageSupport_coe (W : SmallEtale B Z.obj Z.property)
    (T : FiniteSupport B (jX ≫ f ≫ g) W) :
    (compChartImageSupport B g sq W T).1 = compChartImage B g sq W T := rfl

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [IsOpenImmersion (B.inclusion.map jX)] in
/-- The image support is closed. -/
public theorem isClosed_compChartImageSupport (W : SmallEtale B Z.obj Z.property)
    (T : FiniteSupport B (jX ≫ f ≫ g) W) :
    IsClosed (compChartImageSupport B g sq W T).1 :=
  (exists_isProperOver_compChartImage B g sq W T).1

/-- The transported generator, restricted to the canonical open of the image support. -/
public def compChartImageSection (W : SmallEtale B Z.obj Z.property)
    (T : FiniteSupport B (jX ≫ f ≫ g) W)
    (a : (finiteSupportDiagram B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F) W).obj T) :
    supportedSections B Y'.obj Y'.property
      ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F))
      (baseChange B (jY ≫ g) W) (compChartImageSupport B g sq W T).1
      (finiteSupport_isLocallyClosed B _ W _) :=
  ⟨((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)).obj.map
      (openObjectι B Y'.obj Y'.property (baseChange B (jY ≫ g) W)
        (supportOpen B Y'.obj Y'.property _ _
          (finiteSupport_isLocallyClosed B _ W (compChartImageSupport B g sq W T)))).op
      (compChartRestrict B g F W ((colimit.ι _ T ≫ compChartApp B g sq hsq F W) a)), by
    refine (supportSection_restrict_subset_preimage B Y'.obj Y'.property _ _ _ _ _).trans ?_
    rw [openObjectι_map]
    exact Set.preimage_mono (supportSection_compChartRestrict_subset B g sq hsq F W T a)⟩

/-- **The finite-support model of the transported generator.** Through the comparison of
Stacks 0F6N for the separated morphism `jY ≫ g`, the transported generator is the colimit
generator of the image support carrying the restricted section. -/
public theorem compPieceProperMap_finiteSupportPushforwardIso_inv
    (W : SmallEtale B Z.obj Z.property) (T : FiniteSupport B (jX ≫ f ≫ g) W)
    (a : (finiteSupportDiagram B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F) W).obj T) :
    ((finiteSupportPushforwardGenerator B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F)
        W T ≫ (compPieceProperMap B g sq hsq F).app (op W) ≫
        ((finiteSupportPushforwardIso.{u, max (u + 1) v} B (jY ≫ g)).val.inv.app
          ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F))).app (op W))
        a) =
      finiteSupportPushforwardGenerator B (jY ≫ g)
        ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)) W
        (compChartImageSupport B g sq W T) (compChartImageSection B g sq hsq F W T a) := by
  set e := (finiteSupportPushforwardIso.{u, max (u + 1) v} B (jY ≫ g))
  set H := (openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)
  have key : ((e.val.hom.app H).app (op W))
      (finiteSupportPushforwardGenerator B (jY ≫ g) H W
        (compChartImageSupport B g sq W T) (compChartImageSection B g sq hsq F W T a)) =
      ((compPieceProperMap B g sq hsq F).app (op W))
        ((finiteSupportPushforwardGenerator B (jX ≫ f ≫ g)
          ((openRestriction.{u, v} B jX).obj F) W T) a) := by
    apply Subtype.ext
    exact map_openObjectι_injective_of_eq_univ B Y'.obj Y'.property H
      (baseChange B (jY ≫ g) W) (supportOpen B Y'.obj Y'.property _ _
        (finiteSupport_isLocallyClosed B _ W (compChartImageSupport B g sq W T)))
      (coborder_eq_univ_iff.2 (isClosed_compChartImageSupport B g sq W T))
      (e.property H W (compChartImageSupport B g sq W T)
        (compChartImageSection B g sq hsq F W T a))
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  rw [← key]
  exact ConcreteCategory.congr_hom
    (congrArg (fun φ => NatTrans.app φ (op W)) (e.val.hom_inv_id_app H)) _

end Generator

section CovarianceComponents

variable (B : BigEtaleSite.{u}) {X' X Y : B.Scheme} (j : X' ⟶ X) (f : X ⟶ Y)
  [IsOpenImmersion (B.inclusion.map j)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
  (s : GeometricPoint Y.obj)

/-- The covariance map of Stacks 0F6S on the stalk decompositions of Stacks 0F5F. -/
public abbrev openCovarianceFiberStalksMap :
    AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B (j ≫ f) s
      ((openRestriction.{u, v} B j).obj F)) ⟶
      AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B f s F) :=
  (fShriekStalkIso.{u, v} B (j ≫ f) s ((openRestriction.{u, v} B j).obj F)).inv ≫
    ((geometricPointSitePoint B Y.obj Y.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map
      ((openCovarianceShriekMap.{u, v} B j f).app F) ≫
    (fShriekStalkIso.{u, v} B f s F).hom

/-- The covariance map carries a single summand to the summand at the image point. -/
private theorem openCovarianceFiberStalksMap_of
    [DecidableEq (GeometricFiberPoint B (j ≫ f) s)] [DecidableEq (GeometricFiberPoint B f s)]
    (y : GeometricFiberPoint B (j ≫ f) s)
    (c : ↑(etaleStalk B X'.obj X'.property (y.toGeometricPoint B (j ≫ f) s)
      ((openRestriction.{u, v} B j).obj F).obj)) :
    ((openCovarianceFiberStalksMap B j f F s) (DirectSum.of _ y c) :
        fiberStalks.{u, max (u + 1) v} B f s F) =
      DirectSum.of _ (openFiberPoint B j f s y) ((openFiberStalkIso.{u, v} B j f F s y).hom c) :=
  ConcreteCategory.congr_hom
    (ofHom_of_comp_fShriekStalkIso_openCovariance.{u, v} B j f F s y) c

/-- **Stacks 0F6S, part (1)**, componentwise: the covariance map carries the component at a point
of the geometric fibre of `j ≫ f` to the component at its image. -/
public theorem openCovarianceFiberStalksMap_apply
    (ζ : fiberStalks.{u, max (u + 1) v} B (j ≫ f) s ((openRestriction.{u, v} B j).obj F))
    (y : GeometricFiberPoint B (j ≫ f) s) :
    ((openCovarianceFiberStalksMap B j f F s) ζ : fiberStalks.{u, max (u + 1) v} B f s F)
        (openFiberPoint B j f s y) =
      (openFiberStalkIso.{u, v} B j f F s y).hom (ζ y) := by
  classical
  induction ζ using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, DirectSum.add_apply, ha, hb, DirectSum.add_apply, map_add]
  | of y' c =>
    rw [openCovarianceFiberStalksMap_of]
    by_cases hy : y' = y
    · subst hy
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (fun hc => hy (openFiberPoint_injective B j f s hc).symm),
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hy), map_zero]

/-- **Stacks 0F6S, part (1)**, componentwise: the covariance map has no component outside the
image of the geometric fibre of `j ≫ f`. -/
public theorem openCovarianceFiberStalksMap_apply_eq_zero
    (ζ : fiberStalks.{u, max (u + 1) v} B (j ≫ f) s ((openRestriction.{u, v} B j).obj F))
    (x : GeometricFiberPoint B f s)
    (hx : ∀ y : GeometricFiberPoint B (j ≫ f) s, openFiberPoint B j f s y ≠ x) :
    ((openCovarianceFiberStalksMap B j f F s) ζ : fiberStalks.{u, max (u + 1) v} B f s F) x =
      0 := by
  classical
  induction ζ using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, DirectSum.add_apply, ha, hb, add_zero]
  | of y' c =>
    rw [openCovarianceFiberStalksMap_of]
    exact DirectSum.of_eq_of_ne _ _ _ (hx y').symm

end CovarianceComponents

section ListSum

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (g : S ⟶ T)
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  (G : Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{max (u + 1) v})
  (t : GeometricPoint T.obj)

/-- Every element of the direct sum of the stalks over a geometric fibre is a finite sum of germ
decompositions of supported sections over one common pointed étale neighbourhood. -/
public theorem exists_listSum_fiberStalkSum
    (ξ : fiberStalks.{u, max (u + 1) v} B g t G) :
    ∃ (V : SmallEtale B T.obj T.property)
      (w : (geometricPointFiber B T.obj T.property t).obj V)
      (l : List ((E : FiniteSupport B g V) × ↑((finiteSupportDiagram B g G V).obj E))),
      (l.map (fun pr => fiberStalkSum.{u, max (u + 1) v} B g t G V w pr.1 pr.2)).sum = ξ := by
  obtain ⟨V, w, l, hl⟩ := exists_listSum_finiteSupportStalkGenerator.{u, v} B g G t
    ((finiteSupportStalkIso.{u, max (u + 1) v} B g t G (fun _ => inferInstance)).inv ξ)
  refine ⟨V, w, l, ?_⟩
  have h := congrArg (finiteSupportStalkIso.{u, max (u + 1) v} B g t G
    (fun _ => inferInstance)).hom hl
  rw [Iso.inv_hom_id_apply, map_list_sum, List.map_map] at h
  refine Eq.trans ?_ h
  congr 1
  refine List.map_congr_left fun pr _ => ?_
  exact (ConcreteCategory.congr_hom (finiteSupportStalkGenerator_comp_stalkIso.{u, v} B g G t V w
    pr.1) pr.2).symm

end ListSum

section PieceComponents

variable (B : BigEtaleSite.{u}) {X Y Z X' Y' : B.Scheme}
  {f : X ⟶ Y} (g : Y ⟶ Z) {jX : X' ⟶ X} {jY : Y' ⟶ Y} {f' : X' ⟶ Y'}
  [IsOpenImmersion (B.inclusion.map jX)] [IsOpenImmersion (B.inclusion.map jY)]
  [IsSeparated (B.inclusion.map (jY ≫ g))]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyOfFiniteType (B.inclusion.map g)] [LocallyQuasiFinite (B.inclusion.map g)]
  (sq : f' ≫ jY = jX ≫ f) (hsq : IsPullback f' jX jY f)
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
  (s : GeometricPoint Z.obj)

/-- The germ of a section is carried by a morphism of presheaves to the germ of its image. -/
public theorem colim_map_etaleGerm {S : Scheme.{u}} {hS : B.Contains S} (t : GeometricPoint S)
    {P Q : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}} (φ : P ⟶ Q)
    (W : SmallEtale B S hS) (q : (geometricPointFiber B S hS t).obj W) (a : P.obj (op W)) :
    (colim.map (Functor.whiskerLeft (Functor.Elements.π
        (geometricPointFiber B S hS t)).op φ)) (etaleGerm B S hS t P W q a) =
      etaleGerm B S hS t Q W q (φ.app (op W) a) :=
  ConcreteCategory.congr_hom (colimit.ι_map (Functor.whiskerLeft (Functor.Elements.π
    (geometricPointFiber B S hS t)).op φ) (op (Functor.elementsMk _ W q))) a

/-- The sheafified piece, before the covariance of Stacks 0F6S, on the germ of a generator: the
germ of the generator of the image support carrying the restricted section. -/
public theorem sheafFiber_map_compPieceLift_germ (W : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (T : FiniteSupport B (jX ≫ f ≫ g) W)
    (a : (finiteSupportDiagram B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F) W).obj T) :
    ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map
      (⟨sheafifyLift (SmallEtale.topology B Z.obj Z.property)
        (compPiecePresheafMap B g sq hsq F) (ObjectProperty.FullSubcategory.property _)⟩ :
        (openShriekPushforward.{u, v} B jX (f ≫ g)).obj F ⟶ _)
      (etaleGerm B Z.obj Z.property s
        ((fShriekFunctor.{u, v} B (jX ≫ f ≫ g)).obj ((openRestriction.{u, v} B jX).obj F)).obj
        W w ((finiteSupportPushforwardGenerator B (jX ≫ f ≫ g)
          ((openRestriction.{u, v} B jX).obj F) W T ≫
          (toSheafify (SmallEtale.topology B Z.obj Z.property)
            ((finiteSupportPushforward.{u, max (u + 1) v} B (jX ≫ f ≫ g)
              (fun _ => inferInstance)).val.obj ((openRestriction.{u, v} B jX).obj F))).app
            (op W)) a)) =
      etaleGerm B Z.obj Z.property s
        ((fShriekFunctor.{u, v} B (jY ≫ g)).obj
          ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F))).obj
        W w ((finiteSupportPushforwardGenerator B (jY ≫ g)
          ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)) W
          (compChartImageSupport B g sq W T) ≫
          (toSheafify (SmallEtale.topology B Z.obj Z.property)
            ((finiteSupportPushforward.{u, max (u + 1) v} B (jY ≫ g)
              (fun _ => inferInstance)).val.obj
                ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)))).app
            (op W)) (compChartImageSection B g sq hsq F W T a)) := by
  refine (colim_map_etaleGerm B s _ W w _).trans ?_
  refine congrArg (etaleGerm B Z.obj Z.property s _ W w) ?_
  have hL : toSheafify (SmallEtale.topology B Z.obj Z.property)
        ((finiteSupportPushforward.{u, max (u + 1) v} B (jX ≫ f ≫ g)
          (fun _ => inferInstance)).val.obj ((openRestriction.{u, v} B jX).obj F)) ≫
        sheafifyLift (SmallEtale.topology B Z.obj Z.property)
          (compPiecePresheafMap B g sq hsq F) (ObjectProperty.FullSubcategory.property _) =
      compPiecePresheafMap B g sq hsq F := by
    rw [toSheafify_sheafifyLift]
  refine (ConcreteCategory.congr_hom (NatTrans.congr_app hL (op W))
    ((finiteSupportPushforwardGenerator B (jX ≫ f ≫ g) _ W T) a)).trans ?_
  exact congrArg (ConcreteCategory.hom ((toSheafify (SmallEtale.topology B Z.obj Z.property)
    ((finiteSupportPushforward.{u, max (u + 1) v} B (jY ≫ g) (fun _ => inferInstance)).val.obj
      ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)))).app (op W)))
    (compPieceProperMap_finiteSupportPushforwardIso_inv B g sq hsq F W T a)

/-- The piece of the composition comparison on the stalk decompositions of Stacks 0F5F. -/
public abbrev compPieceFiberStalksMap :
    AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B (jX ≫ f ≫ g) s
      ((openRestriction.{u, v} B jX).obj F)) ⟶
      AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B g s ((fShriekFunctor.{u, v} B f).obj F)) :=
  (fShriekStalkIso.{u, v} B (jX ≫ f ≫ g) s ((openRestriction.{u, v} B jX).obj F)).inv ≫
    ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
        (A := AddCommGrpCat.{max (u + 1) v})).map (compPieceMap B g sq hsq F) ≫
    (fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F)).hom

/-- The piece on the germ decomposition of a generator, before the stalks of `f_! F` are
decomposed: the covariance of Stacks 0F6S applied to the germ decomposition of the generator of
the image support. -/
public theorem compPieceFiberStalksMap_fiberStalkSum (W : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (T : FiniteSupport B (jX ≫ f ≫ g) W)
    (a : (finiteSupportDiagram B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F) W).obj T) :
    compPieceFiberStalksMap B g sq hsq F s
        (fiberStalkSum.{u, max (u + 1) v} B (jX ≫ f ≫ g) s _ W w T a) =
      openCovarianceFiberStalksMap B jY g ((fShriekFunctor.{u, v} B f).obj F) s
        (fiberStalkSum.{u, max (u + 1) v} B (jY ≫ g) s _ W w (compChartImageSupport B g sq W T)
          (compChartImageSection B g sq hsq F W T a)) := by
  have h1 := fShriekStalkIso_hom_germ_generator B (jX ≫ f ≫ g)
    ((openRestriction.{u, v} B jX).obj F) s W w T a
  have h2 := fShriekStalkIso_hom_germ_generator B (jY ≫ g)
    ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)) s W w
    (compChartImageSupport B g sq W T) (compChartImageSection B g sq hsq F W T a)
  rw [← h1, ← h2]
  simp only [compPieceFiberStalksMap, openCovarianceFiberStalksMap, ConcreteCategory.comp_apply,
    Iso.hom_inv_id_apply]
  refine congrArg
    (fun z => (fShriekStalkIso.{u, v} B g s ((fShriekFunctor.{u, v} B f).obj F)).hom z) ?_
  have hc : compPieceMap B g sq hsq F = (⟨sheafifyLift (SmallEtale.topology B Z.obj Z.property)
        (compPiecePresheafMap B g sq hsq F) (ObjectProperty.FullSubcategory.property _)⟩ :
        (openShriekPushforward.{u, v} B jX (f ≫ g)).obj F ⟶ _) ≫
      (openCovarianceShriekMap.{u, v} B jY g).app ((fShriekFunctor.{u, v} B f).obj F) := rfl
  rw [hc, Functor.map_comp]
  exact congrArg (fun z => ((geometricPointSitePoint B Z.obj Z.property s).sheafFiber
      (A := AddCommGrpCat.{max (u + 1) v})).map
    ((openCovarianceShriekMap.{u, v} B jY g).app ((fShriekFunctor.{u, v} B f).obj F)) z)
    (sheafFiber_map_compPieceLift_germ B g sq hsq F s W w T a)

/-- **The piece of the composition comparison on a component.** At the point of the geometric
fibre of `g` below a point `x` of the geometric fibre of `jX ≫ f ≫ g`, and inside it at the point
of `X` over it given by `x`, the piece carries the germ decomposition of a generator to the
component at `x`, read through the identification of the stalks of `F|_{X'}` and `F`. -/
public theorem compPieceFiberStalksMap_fiberStalkSum_apply (W : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (T : FiniteSupport B (jX ≫ f ≫ g) W)
    (a : (finiteSupportDiagram B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F) W).obj T)
    (x : GeometricFiberPoint B (jX ≫ f ≫ g) s) :
    ((fShriekStalkIso.{u, v} B f ((openFiberPoint B jY g s
        (compFiberBase B g sq s x)).toGeometricPoint B g s) F).hom
      ((compPieceFiberStalksMap B g sq hsq F s
        (fiberStalkSum.{u, max (u + 1) v} B (jX ≫ f ≫ g) s _ W w T a) :
          fiberStalks.{u, max (u + 1) v} B g s _)
        (openFiberPoint B jY g s (compFiberBase B g sq s x))) :
          fiberStalks.{u, max (u + 1) v} B f _ F) (compFiberTop B g sq s x) =
      (openFiberStalkIso.{u, v} B jX (f ≫ g) F s x).hom
        (fiberStalkComponent.{u, max (u + 1) v} B (jX ≫ f ≫ g) s
          ((openRestriction.{u, v} B jX).obj F) W w T a x) := by
  rw [compPieceFiberStalksMap_fiberStalkSum, openCovarianceFiberStalksMap_apply,
    fiberStalkSum_apply]
  have hlift : HasFiberLift B (jY ≫ g) s W w (compChartImageSupport B g sq W T)
      (compFiberBase B g sq s x) := by
    change _ ∈ coborder _
    rw [coborder_eq_univ_iff.2 (isClosed_compChartImageSupport B g sq W T)]
    trivial
  rw [fiberStalkComponent_of_hasFiberLift _ _ _ _ _ _ _ _ _ hlift]
  change (fShriekStalkIso.{u, v} B f _ F).hom ((openFiberStalkIso.{u, v} B jY g
    ((fShriekFunctor.{u, v} B f).obj F) s (compFiberBase B g sq s x)).hom
    (etaleGerm B Y'.obj Y'.property _ _ _ _
      (((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)).obj.map
        (openObjectι B Y'.obj Y'.property (baseChange B (jY ≫ g) W) _).op
        (compChartRestrict B g F W ((colimit.ι _ T ≫ compChartApp B g sq hsq F W) a))))) _ = _
  have hg := etaleGerm_openObjectLift B Y'.obj Y'.property
    ((compFiberBase B g sq s x).toGeometricPoint B (jY ≫ g) s)
    (P := ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)).obj)
    (baseChange B (jY ≫ g) W) (fiberPointElement B (jY ≫ g) s W w (compFiberBase B g sq s x))
    (finiteSupportOpen B (jY ≫ g) W (compChartImageSupport B g sq W T)) hlift
    (compChartRestrict B g F W ((colimit.ι _ T ≫ compChartApp B g sq hsq F W) a))
  simp only [hg]
  have hA2 : (openFiberStalkIso.{u, v} B jY g ((fShriekFunctor.{u, v} B f).obj F) s
        (compFiberBase B g sq s x)).hom
        (etaleGerm B Y'.obj Y'.property ((compFiberBase B g sq s x).toGeometricPoint B _ s)
          ((openRestriction.{u, v} B jY).obj ((fShriekFunctor.{u, v} B f).obj F)).obj
          (baseChange B (jY ≫ g) W)
          (fiberPointElement B (jY ≫ g) s W w (compFiberBase B g sq s x))
          (((openRestrictionIso.{u, v} B jY).hom.app ((fShriekFunctor.{u, v} B f).obj F)).hom.app
            (op (baseChange B (jY ≫ g) W))
            ((colimit.ι (finiteSupportDiagram B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F)
              W) T ≫ compChartApp B g sq hsq F W) a))) =
      etaleGerm B Y.obj Y.property _ ((fShriekFunctor.{u, v} B f).obj F).obj
        (compChartBase B g jY W) (compChartBaseLift B g s W w (compFiberBase B g sq s x))
        ((colimit.ι (finiteSupportDiagram B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F)
          W) T ≫ compChartApp B g sq hsq F W) a) :=
    etaleStalkSmallEtalePullObjIso_germ_openRestrictionIso B jY
      ((fShriekFunctor.{u, v} B f).obj F)
      ((compFiberBase B g sq s x).toGeometricPoint B _ s) (baseChange B (jY ≫ g) W)
      (fiberPointElement B (jY ≫ g) s W w (compFiberBase B g sq s x))
      (compChartBaseLift B g s W w (compFiberBase B g sq s x)) rfl _
  refine (congrArg (fun z => ((fShriekStalkIso.{u, v} B f ((openFiberPoint B jY g s
      (compFiberBase B g sq s x)).toGeometricPoint B g s) F).hom z :
        fiberStalks.{u, max (u + 1) v} B f _ F) (compFiberTop B g sq s x)) hA2).trans ?_
  have ht : (colimit.ι (finiteSupportDiagram B (jX ≫ f ≫ g) ((openRestriction.{u, v} B jX).obj F)
        W) T ≫ compChartApp B g sq hsq F W) a =
      (finiteSupportPushforwardGenerator B f F _ (compChartSupport B g sq hsq W T) ≫
        (toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).val.obj F)).app (op (compChartBase B g jY W)))
        (compChartGenMap B g sq hsq F W T _ (imageFiniteSupport_coe B jX (f ≫ g) W T)
          (compChartSupport B g sq hsq W T) (compChartSupport_coe B g sq hsq W T) a) := by
    change (colimit.ι _ T ≫ colimit.desc _ (compChartCocone B g sq hsq F W)) a = _
    rw [colimit.ι_desc]
    rfl
  refine (congrArg (fun z => ((fShriekStalkIso.{u, v} B f ((openFiberPoint B jY g s
      (compFiberBase B g sq s x)).toGeometricPoint B g s) F).hom
        (etaleGerm B Y.obj Y.property _ ((fShriekFunctor.{u, v} B f).obj F).obj
          (compChartBase B g jY W) (compChartBaseLift B g s W w (compFiberBase B g sq s x)) z) :
        fiberStalks.{u, max (u + 1) v} B f _ F) (compFiberTop B g sq s x)) ht).trans ?_
  refine (congrArg (fun z => (z : fiberStalks.{u, max (u + 1) v} B f _ F)
    (compFiberTop B g sq s x)) (fShriekStalkIso_hom_germ_generator B f F _ _ _ _ _)).trans ?_
  exact fiberStalkComponent_compChartGenMap B g sq hsq F s W w T a x

/-- **The piece of the composition comparison on a component**, for an arbitrary element of the
stalk. -/
public theorem compPieceFiberStalksMap_apply
    (ξ : fiberStalks.{u, max (u + 1) v} B (jX ≫ f ≫ g) s ((openRestriction.{u, v} B jX).obj F))
    (x : GeometricFiberPoint B (jX ≫ f ≫ g) s) :
    ((fShriekStalkIso.{u, v} B f ((openFiberPoint B jY g s
        (compFiberBase B g sq s x)).toGeometricPoint B g s) F).hom
      ((compPieceFiberStalksMap B g sq hsq F s ξ : fiberStalks.{u, max (u + 1) v} B g s _)
        (openFiberPoint B jY g s (compFiberBase B g sq s x))) :
          fiberStalks.{u, max (u + 1) v} B f _ F) (compFiberTop B g sq s x) =
      (openFiberStalkIso.{u, v} B jX (f ≫ g) F s x).hom (ξ x) := by
  obtain ⟨V, w, l, rfl⟩ := exists_listSum_fiberStalkSum B (jX ≫ f ≫ g)
    ((openRestriction.{u, v} B jX).obj F) s ξ
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil, map_zero, DirectSum.zero_apply]
    rfl
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, map_add, DirectSum.add_apply] at ih ⊢
    rw [ih, compPieceFiberStalksMap_fiberStalkSum_apply]
    rfl

/-- The piece of the composition comparison has no component outside the image of `Y'`. -/
public theorem compPieceFiberStalksMap_apply_eq_zero
    (ξ : fiberStalks.{u, max (u + 1) v} B (jX ≫ f ≫ g) s ((openRestriction.{u, v} B jX).obj F))
    (y : GeometricFiberPoint B g s)
    (hy : ∀ y' : GeometricFiberPoint B (jY ≫ g) s, openFiberPoint B jY g s y' ≠ y) :
    (compPieceFiberStalksMap B g sq hsq F s ξ : fiberStalks.{u, max (u + 1) v} B g s _) y = 0 := by
  obtain ⟨V, w, l, rfl⟩ := exists_listSum_fiberStalkSum B (jX ≫ f ≫ g)
    ((openRestriction.{u, v} B jX).obj F) s ξ
  induction l with
  | nil =>
    simp only [List.map_nil, List.sum_nil, map_zero, DirectSum.zero_apply]
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, map_add, DirectSum.add_apply] at ih ⊢
    rw [ih, compPieceFiberStalksMap_fiberStalkSum,
      openCovarianceFiberStalksMap_apply_eq_zero _ _ _ _ _ _ y hy, add_zero]

end PieceComponents

end AlgebraicGeometry.SmallEtale

end
