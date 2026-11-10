module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompProperSupport

/-!
# The map `c'` of Stacks 0F79 on stalks

Let `g : Y ⟶ Z` be a morphism of a big étale site which is locally of finite type, let `G` be
an abelian sheaf on the small étale site of `Y`, let `s` be a geometric point of `Z` and let `ȳ`
be a point of the geometric fibre of `g` over `s`. A section of the proper-support direct image
`g_! G` over an étale neighbourhood `(W, w)` of `s` is a section of `G` over `W ×_Z Y`, and its
germ at the lift of `ȳ` to `W ×_Z Y` only depends on the germ of the section at `s`. This is the
map `(g_! G)_s ⟶ G_ȳ` of Stacks 0F78 (`AlgebraicGeometry.SmallEtale.properSupportStalkEval`).
Sections of `g_! G` are determined by these germs.

For `f : X ⟶ Y` with `f` and `f ≫ g` locally quasi-finite and `g` separated, the map
`c' : (f ≫ g)_! F ⟶ g_!(f_! F)` of Stacks 0F79 is computed on these germs: through the stalk
decompositions of Stacks 0F5F, the component at a point `x̄` of the geometric fibre of `f` over
`ȳ` of the germ of `c'(σ)` at `ȳ` is the component at `x̄` of the germ of `σ` at `s`. This
determines `c'`, and it gives the naturality of `c'` in the abelian sheaf.

## Main definitions

* `AlgebraicGeometry.SmallEtale.properSupportStalkEval` — the map `(g_! G)_s ⟶ G_ȳ`.
* `AlgebraicGeometry.SmallEtale.IsSepCompMap` — the germ formula characterizing `c'`.

## Main results

* `AlgebraicGeometry.SmallEtale.properSupportFunctor_hom_ext` — morphisms into `g_! G` are
  determined by the germs of the sections they produce at the points of the geometric fibres.
* `AlgebraicGeometry.SmallEtale.isSepCompMap_sepCompShriekMap` — `c'` satisfies the germ
  formula.
* `AlgebraicGeometry.SmallEtale.sepCompShriekMap_naturality` — `c'` is natural in the sheaf.

## References

* [Stacks Project, Tag 0F79](https://stacks.math.columbia.edu/tag/0F79)
* [Stacks Project, Tag 0F78](https://stacks.math.columbia.edu/tag/0F78)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open scoped DirectSum

universe u v

namespace AlgebraicGeometry.SmallEtale

section Eval

variable (B : BigEtaleSite.{u}) {Y Z : B.Scheme} (g : Y ⟶ Z)
  [LocallyOfFiniteType (B.inclusion.map g)]
  (G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
  (s : GeometricPoint Z.obj) (y : GeometricFiberPoint B g s)

/-- The germs at the lift of a point of the geometric fibre of the sections of the proper-support
direct image, as a cocone on the diagram of its stalk. -/
public def properSupportStalkCocone :
    Cocone (etaleStalkDiagram B Z.obj Z.property s
      ((properSupportFunctor.{u, max (u + 1) v} B g).obj G).obj) where
  pt := etaleStalk B Y.obj Y.property (y.toGeometricPoint B g s) G.obj
  ι :=
    { app U := (fShriekSubsheaf B g G).val.arrow.hom.app (op U.unop.1) ≫
        colimit.ι (etaleStalkDiagram B Y.obj Y.property (y.toGeometricPoint B g s) G.obj)
          (op (Functor.elementsMk _ (baseChange B g U.unop.1)
            (fiberPointElement B g s U.unop.1 U.unop.2 y)))
      naturality U U' m := by
        refine ConcreteCategory.hom_ext _ _ fun τ => ?_
        have hn := ConcreteCategory.congr_hom
          ((fShriekSubsheaf B g G).val.arrow.hom.naturality m.unop.1.op) τ
        have hg := etaleGerm_map B Y.obj Y.property (y.toGeometricPoint B g s) G.obj
          ((smallEtaleBaseChange B g).map m.unop.1) (fiberPointElement B g s U.unop.1 U.unop.2 y)
          (fiberPointElement B g s U'.unop.1 U'.unop.2 y)
          (Subtype.ext (fiberPointLift_comp_baseChange B g s U.unop.1 U'.unop.1 m.unop.1
            U.unop.2 U'.unop.2 m.unop.2 y))
          ((fShriekSubsheaf B g G).val.arrow.hom.app (op U.unop.1) τ)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          ConcreteCategory.comp_apply] at hn ⊢
        refine Eq.trans (congrArg (ConcreteCategory.hom (colimit.ι (etaleStalkDiagram B Y.obj
          Y.property (y.toGeometricPoint B g s) G.obj)
            (op (Functor.elementsMk _ (baseChange B g U'.unop.1)
              (fiberPointElement B g s U'.unop.1 U'.unop.2 y))))) hn) ?_
        exact hg }

/-- **The germ at a point of the geometric fibre** of a germ of a section of the proper-support
direct image `g_! G` at a geometric point `s` of `Z`: the map `(g_! G)_s ⟶ G_ȳ` of
Stacks 0F78 for a point `ȳ` of the geometric fibre of `g` over `s`. -/
public def properSupportStalkEval :
    etaleStalk B Z.obj Z.property s ((properSupportFunctor.{u, max (u + 1) v} B g).obj G).obj ⟶
      etaleStalk B Y.obj Y.property (y.toGeometricPoint B g s) G.obj :=
  colimit.desc _ (properSupportStalkCocone B g G s y)

/-- The map `(g_! G)_s ⟶ G_ȳ` on a germ: the germ of the section at the lift of `ȳ`. -/
public theorem properSupportStalkEval_germ (W : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (τ : ((properSupportFunctor.{u, max (u + 1) v} B g).obj G).obj.obj (op W)) :
    properSupportStalkEval B g G s y
        (etaleGerm B Z.obj Z.property s ((properSupportFunctor.{u, max (u + 1) v} B g).obj G).obj
          W w τ) =
      etaleGerm B Y.obj Y.property (y.toGeometricPoint B g s) G.obj (baseChange B g W)
        (fiberPointElement B g s W w y) (properSupportSection B g G W τ) :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (properSupportStalkCocone B g G s y) (op (Functor.elementsMk _ W w))) τ

/-- **Morphisms into the proper-support direct image are determined by germs.** Two morphisms
`A ⟶ g_! G` agree as soon as, for every section `σ` of `A` over an étale neighbourhood `(W, w)` of
a geometric point `s` of `Z`, the two sections of `G` over `W ×_Z Y` they produce have the same
germs at the lifts of the points of the geometric fibre of `g` over `s`. -/
public theorem properSupportFunctor_hom_ext
    {A : Sheaf (SmallEtale.topology B Z.obj Z.property) AddCommGrpCat.{max (u + 1) v}}
    {ψ₁ ψ₂ : A ⟶ (properSupportFunctor.{u, max (u + 1) v} B g).obj G}
    (h : ∀ (s : GeometricPoint Z.obj) (W : SmallEtale B Z.obj Z.property)
      (w : (geometricPointFiber B Z.obj Z.property s).obj W) (σ : A.obj.obj (op W))
      (y : GeometricFiberPoint B g s),
      etaleGerm B Y.obj Y.property (y.toGeometricPoint B g s) G.obj (baseChange B g W)
          (fiberPointElement B g s W w y) (properSupportSection B g G W (ψ₁.hom.app (op W) σ)) =
        etaleGerm B Y.obj Y.property (y.toGeometricPoint B g s) G.obj (baseChange B g W)
          (fiberPointElement B g s W w y) (properSupportSection B g G W (ψ₂.hom.app (op W) σ))) :
    ψ₁ = ψ₂ := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  exact ConcreteCategory.hom_ext _ _ fun σ => Subtype.ext <|
    etaleSection_ext_baseChange.{u, v} B g W.unop _ _ fun s w y => h s W.unop w σ y

end Eval

section Formula

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map (f ≫ g))]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- **The germ formula of Stacks 0F79** for a morphism `c : (f ≫ g)_! F ⟶ g_!(f_! F)`: for a
section `σ` of `(f ≫ g)_! F` over an étale neighbourhood `(W, w)` of a geometric point `s` of
`Z`, a point `ȳ` of the geometric fibre of `g` over `s` and a point `x̄` of the geometric fibre
of `f` over `ȳ`, the component at `x̄` of the germ of `c(σ)` at `ȳ` (Stacks 0F78, 0F5F) is the
component at `x̄` of the germ of `σ` at `s` (Stacks 0F5F). -/
public def IsSepCompMap
    (c : (fShriekFunctor.{u, v} B (f ≫ g)).obj F ⟶
      (properSupportFunctor.{u, max (u + 1) v} B g).obj ((fShriekFunctor.{u, v} B f).obj F)) :
    Prop :=
  ∀ (s : GeometricPoint Z.obj) (W : SmallEtale B Z.obj Z.property)
    (w : (geometricPointFiber B Z.obj Z.property s).obj W)
    (σ : ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj.obj (op W))
    (y : GeometricFiberPoint B g s) (x : GeometricFiberPoint B f (y.toGeometricPoint B g s)),
    ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
        (etaleGerm B Y.obj Y.property (y.toGeometricPoint B g s)
          ((fShriekFunctor.{u, v} B f).obj F).obj (baseChange B g W)
          (fiberPointElement B g s W w y)
          (properSupportSection B g ((fShriekFunctor.{u, v} B f).obj F) W
            (c.hom.app (op W) σ))) : fiberStalks.{u, max (u + 1) v} B f _ F) x =
      ((fShriekStalkIso.{u, v} B (f ≫ g) s F).hom
        (etaleGerm B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj W w σ) :
          fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F) (compFiberPointOf B f g s y x)

/-- Two elements of a stalk of `f'_! F'` are equal if all components of their images under the
stalk decomposition agree. -/
private theorem eq_of_fShriekStalkIso_hom_apply_eq {X' Y' : B.Scheme} (f' : X' ⟶ Y')
    [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]
    (t : GeometricPoint Y'.obj)
    {F' : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{max (u + 1) v}}
    {a b : ↑(etaleStalk B Y'.obj Y'.property t ((fShriekFunctor.{u, v} B f').obj F').obj)}
    (h : ∀ x, ((fShriekStalkIso.{u, v} B f' t F').hom a :
        fiberStalks.{u, max (u + 1) v} B f' t F') x =
      ((fShriekStalkIso.{u, v} B f' t F').hom b :
        fiberStalks.{u, max (u + 1) v} B f' t F') x) :
    a = b :=
  (AddCommGrpCat.mono_iff_injective (fShriekStalkIso.{u, v} B f' t F').hom).1 inferInstance
    (DFinsupp.ext h)

omit [IsSeparated (B.inclusion.map g)] in
/-- **Uniqueness.** A morphism `(f ≫ g)_! F ⟶ g_!(f_! F)` is determined by the germ formula. -/
public theorem eq_of_isSepCompMap
    {c₁ c₂ : (fShriekFunctor.{u, v} B (f ≫ g)).obj F ⟶
      (properSupportFunctor.{u, max (u + 1) v} B g).obj ((fShriekFunctor.{u, v} B f).obj F)}
    (h₁ : IsSepCompMap B f g F c₁) (h₂ : IsSepCompMap B f g F c₂) : c₁ = c₂ := by
  refine properSupportFunctor_hom_ext B g _ fun s W w σ y => ?_
  exact eq_of_fShriekStalkIso_hom_apply_eq B f _ fun x =>
    (h₁ s W w σ y x).trans (h₂ s W w σ y x).symm

/-- **The germ formula on stalks.** For an element `t` of the stalk of `(f ≫ g)_! F` at `s`, the
component at `x̄` of the image of `t` under `c'`, read at `ȳ`, is the component at `x̄` of the
stalk decomposition of `t`. -/
public theorem sepCompShriekMap_stalk (s : GeometricPoint Z.obj) (y : GeometricFiberPoint B g s)
    (x : GeometricFiberPoint B f (y.toGeometricPoint B g s))
    (t : ↑(etaleStalk B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj)) :
    ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
        (properSupportStalkEval B g ((fShriekFunctor.{u, v} B f).obj F) s y
          (colim.map (Functor.whiskerLeft (Functor.Elements.π
            (geometricPointFiber B Z.obj Z.property s)).op (sepCompShriekMap B f g F).hom) t)) :
        fiberStalks.{u, max (u + 1) v} B f _ F) x =
      ((fShriekStalkIso.{u, v} B (f ≫ g) s F).hom t :
        fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F) (compFiberPointOf B f g s y x) := by
  let P := (finiteSupportPushforward.{u, max (u + 1) v} B (f ≫ g) (fun _ => inferInstance)).val.obj
    F
  let L : ↑(etaleStalk B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj) →+
      ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f (y.toGeometricPoint B g s)) F.obj) :=
    (DFinsupp.evalAddMonoidHom x).comp
      ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom.hom.comp
        ((properSupportStalkEval B g ((fShriekFunctor.{u, v} B f).obj F) s y).hom.comp
          (colim.map (Functor.whiskerLeft (Functor.Elements.π
            (geometricPointFiber B Z.obj Z.property s)).op (sepCompShriekMap B f g F).hom)).hom))
  let R : ↑(etaleStalk B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj) →+
      ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f (y.toGeometricPoint B g s)) F.obj) :=
    (DFinsupp.evalAddMonoidHom (compFiberPointOf B f g s y x)).comp
      (fShriekStalkIso.{u, v} B (f ≫ g) s F).hom.hom
  change L t = R t
  have hgen : ∀ (W : SmallEtale B Z.obj Z.property)
      (w : (geometricPointFiber B Z.obj Z.property s).obj W)
      (E : FiniteSupport B (f ≫ g) W) (a : (finiteSupportDiagram B (f ≫ g) F W).obj E),
      L (etaleGerm B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj W w
        ((toSheafify (SmallEtale.topology B Z.obj Z.property) P).app (op W)
          (finiteSupportPushforwardGenerator B (f ≫ g) F W E a))) =
      R (etaleGerm B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj W w
        ((toSheafify (SmallEtale.topology B Z.obj Z.property) P).app (op W)
          (finiteSupportPushforwardGenerator B (f ≫ g) F W E a))) := by
    intro W w E a
    change ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
        (properSupportStalkEval B g ((fShriekFunctor.{u, v} B f).obj F) s y
          (colim.map (Functor.whiskerLeft (Functor.Elements.π
            (geometricPointFiber B Z.obj Z.property s)).op (sepCompShriekMap B f g F).hom)
            (etaleGerm B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj W w
              ((toSheafify (SmallEtale.topology B Z.obj Z.property) P).app (op W)
                (finiteSupportPushforwardGenerator B (f ≫ g) F W E a))))) :
          fiberStalks.{u, max (u + 1) v} B f _ F) x = ((fShriekStalkIso.{u, v} B (f ≫ g) s F).hom
        (etaleGerm B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj W w
          ((toSheafify (SmallEtale.topology B Z.obj Z.property) P).app (op W)
            (finiteSupportPushforwardGenerator B (f ≫ g) F W E a))) :
          fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F) (compFiberPointOf B f g s y x)
    rw [colim_map_etaleGerm, properSupportStalkEval_germ]
    have hc : properSupportSection B g ((fShriekFunctor.{u, v} B f).obj F) W
        ((sepCompShriekMap B f g F).hom.app (op W)
          ((toSheafify (SmallEtale.topology B Z.obj Z.property) P).app (op W)
            (finiteSupportPushforwardGenerator B (f ≫ g) F W E a))) =
        sepCompGenerator B f g F W E a :=
      properSupportSection_sepCompShriekMap_generator B f g F W E a
    rw [hc]
    have h1 := fShriekStalkIso_hom_germ_generator.{u, v} B f F (y.toGeometricPoint B g s)
      (baseChange B g W) (fiberPointElement B g s W w y) (sepCompSupport B f g W E)
      (sepCompSection B f g F W E a)
    have h2 := fShriekStalkIso_hom_germ_generator.{u, v} B (f ≫ g) F s W w E a
    refine (congrArg (fun m => (m : fiberStalks.{u, max (u + 1) v} B f _ F) x) h1).trans ?_
    refine Eq.trans ?_ (congrArg (fun m => (m : fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F)
      (compFiberPointOf B f g s y x)) h2).symm
    exact fiberStalkComponent_sepCompSection B f g F s W w E a y x
  obtain ⟨t', rfl⟩ : ∃ t', etaleStalkSheafificationMap B Z.obj Z.property s P t' = t :=
    ⟨(etaleStalkSheafificationIso B Z.obj Z.property s P).hom t,
      Iso.hom_inv_id_apply (etaleStalkSheafificationIso B Z.obj Z.property s P) t⟩
  obtain ⟨@⟨W, w⟩, l, rfl⟩ := exists_listSum_generators_eq_etaleStalk.{u, max (u + 1) v} B (f ≫ g)
    s F (fun _ => inferInstance) t'
  let L' := L.comp (etaleStalkSheafificationMap B Z.obj Z.property s P).hom
  let R' := R.comp (etaleStalkSheafificationMap B Z.obj Z.property s P).hom
  change L' _ = R' _
  refine (map_list_sum L' _).trans ((congrArg List.sum (List.map_congr_left fun t ht => ?_)).trans
    (map_list_sum R' _).symm)
  obtain ⟨pr, -, rfl⟩ := List.mem_map.1 ht
  have hι : etaleStalkSheafificationMap B Z.obj Z.property s P
        (colimit.ι (etaleStalkDiagram B Z.obj Z.property s P) (op (Functor.elementsMk _ W w))
          (finiteSupportPushforwardGenerator B (f ≫ g) F W pr.1 pr.2)) =
      etaleGerm B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj W w
        ((toSheafify (SmallEtale.topology B Z.obj Z.property) P).app (op W)
          (finiteSupportPushforwardGenerator B (f ≫ g) F W pr.1 pr.2)) :=
    ConcreteCategory.congr_hom
      (colimit_ι_comp_etaleStalkSheafificationMap B Z.obj Z.property s P
        (op (Functor.elementsMk _ W w))) _
  exact (congrArg L hι).trans ((hgen W w pr.1 pr.2).trans (congrArg R hι).symm)

/-- **Stacks 0F79, the germ formula for `c'`.** -/
public theorem isSepCompMap_sepCompShriekMap :
    IsSepCompMap B f g F (sepCompShriekMap B f g F) := by
  intro s W w σ y x
  have h := sepCompShriekMap_stalk B f g F s y x
    (etaleGerm B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj W w σ)
  rw [colim_map_etaleGerm, properSupportStalkEval_germ] at h
  exact h

/-- The stalk decomposition of Stacks 0F5F commutes with a morphism of sheaves, on germs. -/
public theorem fShriekStalkIso_hom_germ_map {X' Y' : B.Scheme} (f' : X' ⟶ Y')
    [LocallyOfFiniteType (B.inclusion.map f')] [LocallyQuasiFinite (B.inclusion.map f')]
    (t : GeometricPoint Y'.obj)
    {F₁ F₂ : Sheaf (SmallEtale.topology B X'.obj X'.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F₁ ⟶ F₂) (V : SmallEtale B Y'.obj Y'.property)
    (q : (geometricPointFiber B Y'.obj Y'.property t).obj V)
    (z : ((fShriekFunctor.{u, v} B f').obj F₁).obj.obj (op V)) :
    (fShriekStalkIso.{u, v} B f' t F₂).hom
        (etaleGerm B Y'.obj Y'.property t ((fShriekFunctor.{u, v} B f').obj F₂).obj V q
          (((fShriekFunctor.{u, v} B f').map φ).hom.app (op V) z)) =
      fiberStalksMap.{u, max (u + 1) v} B f' t φ
        ((fShriekStalkIso.{u, v} B f' t F₁).hom
          (etaleGerm B Y'.obj Y'.property t ((fShriekFunctor.{u, v} B f').obj F₁).obj V q z)) :=
  (congrArg (fShriekStalkIso.{u, v} B f' t F₂).hom.hom
    (colim_map_etaleGerm B t ((fShriekFunctor.{u, v} B f').map φ).hom V q z).symm).trans
    (ConcreteCategory.congr_hom (fShriekStalkIso_natural.{u, v} B f' t φ) _)

variable {F} in
/-- **The map `c'` of Stacks 0F79 is natural in the abelian sheaf.** -/
public theorem sepCompShriekMap_naturality
    {F' : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ F') :
    sepCompShriekMap B f g F ≫
        (properSupportFunctor.{u, max (u + 1) v} B g).map ((fShriekFunctor.{u, v} B f).map φ) =
      (fShriekFunctor.{u, v} B (f ≫ g)).map φ ≫ sepCompShriekMap B f g F' := by
  refine properSupportFunctor_hom_ext B g _ fun s W w σ y => ?_
  refine eq_of_fShriekStalkIso_hom_apply_eq B f _ fun x => ?_
  have hL := isSepCompMap_sepCompShriekMap B f g F s W w σ y x
  have hR := isSepCompMap_sepCompShriekMap B f g F' s W w
    (((fShriekFunctor.{u, v} B (f ≫ g)).map φ).hom.app (op W) σ) y x
  have n1 := fShriekStalkIso_hom_germ_map B f (y.toGeometricPoint B g s) φ (baseChange B g W)
    (fiberPointElement B g s W w y)
    (properSupportSection B g ((fShriekFunctor.{u, v} B f).obj F) W
      ((sepCompShriekMap B f g F).hom.app (op W) σ))
  have n2 := fShriekStalkIso_hom_germ_map B (f ≫ g) s φ W w σ
  have hm := properSupportSection_map B g ((fShriekFunctor.{u, v} B f).map φ) W
    ((sepCompShriekMap B f g F).hom.app (op W) σ)
  refine (congrArg (fun z => ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F').hom
    (etaleGerm B Y.obj Y.property (y.toGeometricPoint B g s)
      ((fShriekFunctor.{u, v} B f).obj F').obj (baseChange B g W)
      (fiberPointElement B g s W w y) z) : fiberStalks.{u, max (u + 1) v} B f _ F') x) hm).trans ?_
  refine (congrArg (fun m => (m : fiberStalks.{u, max (u + 1) v} B f _ F') x) n1).trans ?_
  refine Eq.trans ?_ hR.symm
  refine Eq.trans ?_ (congrArg (fun m => (m : fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F')
    (compFiberPointOf B f g s y x)) n2).symm
  change (colim.map (Functor.whiskerLeft (Functor.Elements.π (geometricPointFiber B X.obj
      X.property (x.toGeometricPoint B f (y.toGeometricPoint B g s)))).op φ.1)).hom
      (((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
        (etaleGerm B Y.obj Y.property (y.toGeometricPoint B g s)
          ((fShriekFunctor.{u, v} B f).obj F).obj (baseChange B g W)
          (fiberPointElement B g s W w y)
          (properSupportSection B g ((fShriekFunctor.{u, v} B f).obj F) W
            ((sepCompShriekMap B f g F).hom.app (op W) σ))) :
        fiberStalks.{u, max (u + 1) v} B f _ F) x) =
    (colim.map (Functor.whiskerLeft (Functor.Elements.π (geometricPointFiber B X.obj
      X.property ((compFiberPointOf B f g s y x).toGeometricPoint B (f ≫ g) s))).op φ.1)).hom
      (((fShriekStalkIso.{u, v} B (f ≫ g) s F).hom
        (etaleGerm B Z.obj Z.property s ((fShriekFunctor.{u, v} B (f ≫ g)).obj F).obj W w σ) :
          fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F) (compFiberPointOf B f g s y x))
  rw [hL]
  rfl

end Formula

end AlgebraicGeometry.SmallEtale

end
