module

public import StacksFrontier.Topology.Simplicial.Augmentation

/-!
# Sections of the direct image along an augmentation

Let `a : Y → X` be an augmentation of a simplicial topological space and let
`a : Sh(Y_Zar) → Sh(X)` be the morphism of topoi of Stacks 09W4. For a sheaf `F` on the site of
simplicial opens and an open `Ω ⊆ X`, the sections of the direct image are the limit, over the
simplex category, of the sections of `F` over the simplicial opens `a_n⁻¹(Ω) ⊆ Y_n`:

`(a_* F)(Ω) = lim_{[n] ∈ Δ} F(a_n⁻¹ Ω)`,

naturally in `F` and `Ω`. This is the description of `a_*` as the limit of the cosimplicial
sheaf `[n] ↦ a_{n,*} F_n` of the proof of Tag 09W4, read on sections.

## Main definitions

* `Stacks.Topology.Simplicial.augmentationOpen`: the simplicial open `a_n⁻¹(Ω)` in degree `n`.
* `Stacks.Topology.Simplicial.augmentationOpensDiagram`: the simplicial opens `a_n⁻¹(Ω)` as a
  cosimplicial diagram in the opposite of the site of simplicial opens, functorially in `Ω`.
* `Stacks.Topology.Simplicial.augmentationSections`: the presheaf `Ω ↦ lim_n F(a_n⁻¹ Ω)`,
  functorially in the presheaf `F`.

## Main results

* `Stacks.Topology.Simplicial.augmentationMorphism_pushforward_sectionsIso`: the presheaf
  underlying `a_* F` is `Ω ↦ lim_n F(a_n⁻¹ Ω)`, naturally in `F`.

## References

* [Stacks Project, Tag 09W4](https://stacks.math.columbia.edu/tag/09W4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Simplicial
open Stacks.Topology.Simplicial.Augmentation

universe u

namespace Stacks.Topology.Simplicial

variable (Y : SimplicialObject TopCat.{u}) (X : TopCat.{u})
  (a : Y ⟶ (SimplicialObject.const TopCat).obj X)

/-- The simplicial open `a_n⁻¹(Ω) ⊆ Y_n` in simplicial degree `n`. -/
abbrev augmentationOpen (Ω : Opens X) (n : SimplexCategoryᵒᵖ) : SimplicialOpen Y :=
  ⟨n, (Opens.map (a.app n)).obj Ω⟩

/-- The simplicial opens `a_n⁻¹(Ω)`, as a cosimplicial diagram in the opposite of the site of
simplicial opens, functorially in the open `Ω ⊆ X`. A simplex map `[m] → [n]` goes to the
inclusion `a_n⁻¹(Ω) ⊆ Y(φ)⁻¹ a_m⁻¹(Ω)` over `Y(φ) : Y_n → Y_m`, and an inclusion `Ω' ⊆ Ω` to
the inclusions `a_n⁻¹(Ω') ⊆ a_n⁻¹(Ω)`. -/
def augmentationOpensDiagram : (Opens X)ᵒᵖ ⥤ SimplexCategory ⥤ (SimplicialOpen Y)ᵒᵖ where
  obj Ω :=
    { obj n := op (augmentationOpen Y X a Ω.unop (op n))
      map {n m} φ := op
        { base := φ.op
          le := fun x hx => by
            change (Y.map φ.op ≫ a.app (op n)) x ∈ Ω.unop
            rw [augmentation_w]
            exact hx }
      map_id n := Quiver.Hom.unop_inj (SimplicialOpen.Hom.ext _ _ rfl)
      map_comp _ _ := Quiver.Hom.unop_inj (SimplicialOpen.Hom.ext _ _ rfl) }
  map {Ω Ω'} g :=
    { app n := op
        { base := 𝟙 _
          le := fun x hx => by
            change (Y.map (𝟙 _) ≫ a.app (op n)) x ∈ Ω.unop
            rw [CategoryTheory.Functor.map_id, Category.id_comp]
            exact leOfHom g.unop hx }
      naturality _ _ _ := Quiver.Hom.unop_inj (SimplicialOpen.Hom.ext _ _
        ((Category.id_comp _).trans (Category.comp_id _).symm)) }
  map_id _ := by
    ext n
    exact Quiver.Hom.unop_inj (SimplicialOpen.Hom.ext _ _ rfl)
  map_comp _ _ := by
    ext n
    exact Quiver.Hom.unop_inj (SimplicialOpen.Hom.ext _ _ (Category.id_comp _).symm)

/-- The presheaf `Ω ↦ lim_n F(a_n⁻¹ Ω)` on `X` attached to a presheaf `F` on the site of
simplicial opens, functorially in `F`. -/
def augmentationSections :
    ((SimplicialOpen Y)ᵒᵖ ⥤ Type u) ⥤ (Opens X)ᵒᵖ ⥤ Type u :=
  (Functor.whiskeringRight SimplexCategory _ (Type u)) ⋙
    (Functor.whiskeringLeft _ _ _).obj (augmentationOpensDiagram Y X a) ⋙
      (Functor.whiskeringRight _ _ _).obj lim

/-- On sections, the direct-image map attached to a triangle `f ≫ c = b` is the given `f`-map
followed by the identification of the two preimages. -/
theorem pushTransition_app {B C Z : TopCat.{u}} (f : B ⟶ C) (b : B ⟶ Z) (c : C ⟶ Z)
    (h : f ≫ c = b) {F : sh B} {G : sh C} (t : G ⟶ (pf f).obj F) (V : (Opens Z)ᵒᵖ) :
    (pushTransition f b c h t).hom.app V =
      t.hom.app (op ((Opens.map c).obj V.unop)) ≫
        F.obj.map (eqToHom (by rw [← h]; rfl)) := by
  subst h
  show ((pf c).map t ≫ 𝟙 _).hom.app V = _
  rw [Category.comp_id]
  exact (Category.comp_id _).symm.trans (congrArg _ (F.obj.map_id _).symm)

variable {Y} in
/-- The component of a sheaf on the site of simplicial opens in simplicial degree `n`, in the
sheaf-system description of Tag 09VM, is its restriction to the opens of `Y_n`, naturally in the
sheaf. -/
def componentSectionsIso (n : SimplexCategoryᵒᵖ) :
    (presentation Y).toEquivalence.functor ⋙ SimplicialSheafSystem.componentFunctor Y (Type u) n ⋙
        TopCat.Sheaf.forget (Type u) (Y.obj n) ≅
      sheafToPresheaf (SimplicialOpen.grothendieckTopology Y) (Type u) ⋙
        componentPresheafFunctor Y (Type u) n :=
  Functor.isoWhiskerLeft (presentation Y).toEquivalence.functor
      ((presentation Y).componentIso n).symm ≪≫
    Functor.isoWhiskerRight (presentation Y).underlyingPresheafIso
      (componentPresheafFunctor Y (Type u) n)

variable {Y} in
/-- The transition maps of the sheaf system of a sheaf `F` are, under `componentSectionsIso`,
the restriction maps of `F` along the simplicial structure maps. -/
theorem componentSectionsIso_transition
    (F : Sheaf (SimplicialOpen.grothendieckTopology Y) (Type u))
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (W : Opens (Y.obj m)) :
    (((presentation Y).toEquivalence.functor.obj F).transition φ).app (op W) ≫
        ((componentSectionsIso n).hom.app F).app (op ((Opens.map (Y.map φ)).obj W)) =
      ((componentSectionsIso m).hom.app F).app (op W) ≫
        F.obj.map (SimplicialSheafSystem.transitionHom φ W).op := by
  let E := presentation Y
  let S := E.toEquivalence.functor.obj F
  let en : ((TopCat.Sheaf.forget (Type u) (Y.obj n)).obj (S.component n)).obj
      (op ((Opens.map (Y.map φ)).obj W)) ≅
      ((E.toPresheaf ⋙ componentPresheafFunctor Y (Type u) n).obj S).obj
        (op ((Opens.map (Y.map φ)).obj W)) :=
    (((E.componentIso n).app S).app (op ((Opens.map (Y.map φ)).obj W))).symm
  let em : ((TopCat.Sheaf.forget (Type u) (Y.obj m)).obj (S.component m)).obj (op W) ≅
      ((E.toPresheaf ⋙ componentPresheafFunctor Y (Type u) m).obj S).obj (op W) :=
    (((E.componentIso m).app S).app (op W)).symm
  let T := (S.transition φ).app (op W)
  let tM := (SimplicialSheafSystem.transitionMap (E.toPresheaf.obj S) φ).app (op W)
  have hc : tM ≫ en.inv = em.inv ≫ T := E.transition_compatibility S φ (op W)
  have key : T ≫ en.hom = em.hom ≫ tM :=
    ((Iso.eq_inv_comp em).mp (((Iso.comp_inv_eq en).mp hc).trans (Category.assoc _ _ _))).symm
  let un := (E.underlyingPresheafIso.hom.app F).app (op ⟨n, (Opens.map (Y.map φ)).obj W⟩)
  let um := (E.underlyingPresheafIso.hom.app F).app (op ⟨m, W⟩)
  show T ≫ (en.hom ≫ un) = (em.hom ≫ um) ≫ F.obj.map (SimplicialSheafSystem.transitionHom φ W).op
  calc T ≫ (en.hom ≫ un) = (T ≫ en.hom) ≫ un := (Category.assoc _ _ _).symm
    _ = (em.hom ≫ tM) ≫ un := congrArg (fun k => k ≫ un) key
    _ = em.hom ≫ (tM ≫ un) := Category.assoc _ _ _
    _ = em.hom ≫ (um ≫ F.obj.map (SimplicialSheafSystem.transitionHom φ W).op) :=
        congrArg (fun k => em.hom ≫ k)
          ((E.underlyingPresheafIso.hom.app F).naturality
            (SimplicialSheafSystem.transitionHom φ W).op)
    _ = _ := (Category.assoc _ _ _).symm

variable {Y X a} in
/-- The cosimplicial diagram of direct images `[n] ↦ a_{n,*} F_n` of the proof of Tag 09W4,
read on presheaves, is the diagram `[n] ↦ (Ω ↦ F(a_n⁻¹ Ω))`. -/
def pushforwardDiagramIso (F : Sheaf (SimplicialOpen.grothendieckTopology Y) (Type u)) :
    pushforwardDiagram Y X a ((presentation Y).toEquivalence.functor.obj F) ⋙
        sheafToPresheaf (Opens.grothendieckTopology X) (Type u) ≅
      (augmentationOpensDiagram Y X a).flip ⋙ (Functor.whiskeringRight _ _ _).obj F.obj :=
  NatIso.ofComponents
    (fun n => NatIso.ofComponents
      (fun V => ((componentSectionsIso (op n)).app F).app
        (op ((Opens.map (a.app (op n))).obj V.unop)))
      (fun {V V'} g => ((componentSectionsIso (op n)).hom.app F).naturality
        ((Opens.map (a.app (op n))).op.map g)))
    (fun {n m} θ => by
      refine NatTrans.ext (funext fun V => ?_)
      let S := (presentation Y).toEquivalence.functor.obj F
      let Wn := (Opens.map (a.app (op n))).obj V.unop
      let Wm := (Opens.map (a.app (op m))).obj V.unop
      have p : op ((Opens.map (Y.map θ.op)).obj Wn) = op Wm := congrArg op (by
        change (Opens.map (Y.map θ.op ≫ a.app (op n))).obj V.unop = _
        rw [augmentation_w])
      have h1 : (pushTransition (Y.map θ.op) (a.app (op m)) (a.app (op n))
          (augmentation_w Y X a θ.op) (systemTransition Y S θ.op)).hom.app V =
          (S.transition θ.op).app (op Wn) ≫ (S.component (op m)).obj.map (eqToHom p) :=
        pushTransition_app _ _ _ _ _ V
      have h2 := ((componentSectionsIso (op m)).hom.app F).naturality (eqToHom p)
      have h3 := componentSectionsIso_transition F θ.op Wn
      have h4 : (SimplicialSheafSystem.transitionHom θ.op Wn).op ≫
          (levelFunctor Y (op m)).op.map (eqToHom p) =
            ((augmentationOpensDiagram Y X a).flip.map θ).app V :=
        Quiver.Hom.unop_inj (SimplicialOpen.Hom.ext _ _ (Category.id_comp _))
      change (pushTransition (Y.map θ.op) (a.app (op m)) (a.app (op n))
          (augmentation_w Y X a θ.op) (systemTransition Y S θ.op)).hom.app V ≫
          ((componentSectionsIso (op m)).hom.app F).app (op Wm) =
        ((componentSectionsIso (op n)).hom.app F).app (op Wn) ≫
          F.obj.map (((augmentationOpensDiagram Y X a).flip.map θ).app V)
      refine (congrArg (· ≫ _) h1).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) h2).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) h3).trans ?_))))
      exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
        ((F.obj.map_comp _ _).symm.trans (congrArg F.obj.map h4))))

/-- The functor taking a presheaf `F` on the site of simplicial opens to the diagram
`[n] ↦ (Ω ↦ F(a_n⁻¹ Ω))` of presheaves on `X`. -/
def sectionsDiagramFunctor :
    ((SimplicialOpen Y)ᵒᵖ ⥤ Type u) ⥤ SimplexCategory ⥤ (Opens X)ᵒᵖ ⥤ Type u :=
  Functor.whiskeringRight _ _ (Type u) ⋙
    (Functor.whiskeringLeft _ _ _).obj (augmentationOpensDiagram Y X a).flip

/-- The cosimplicial diagram of direct images of the proof of Tag 09W4, read on presheaves, is
the diagram `[n] ↦ (Ω ↦ F(a_n⁻¹ Ω))`, naturally in the sheaf `F`. -/
def pushforwardDiagramNatIso :
    (presentation Y).toEquivalence.functor ⋙ pushforwardDiagramFunctor Y X a ⋙
        (Functor.whiskeringRight SimplexCategory _ _).obj
          (sheafToPresheaf (Opens.grothendieckTopology X) (Type u)) ≅
      sheafToPresheaf (SimplicialOpen.grothendieckTopology Y) (Type u) ⋙
        sectionsDiagramFunctor Y X a :=
  NatIso.ofComponents (fun F => pushforwardDiagramIso F) (fun {F G} α => by
    refine NatTrans.ext (funext fun n => NatTrans.ext (funext fun V => ?_))
    exact congrArg (fun t => t.app (op ((Opens.map (a.app (op n))).obj V.unop)))
      ((componentSectionsIso (op n)).hom.naturality α))

/-- The limit of the diagram `[n] ↦ (Ω ↦ F(a_n⁻¹ Ω))` is the presheaf
`Ω ↦ lim_n F(a_n⁻¹ Ω)`, naturally in `F`. -/
def sectionsDiagramLimIso :
    sectionsDiagramFunctor Y X a ⋙ lim ≅ augmentationSections Y X a :=
  Functor.isoWhiskerLeft (sectionsDiagramFunctor Y X a) limIsoFlipCompWhiskerLim ≪≫
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
      simp only [Iso.refl_hom]
      rfl)

/-- **Stacks Tag 09W4, the direct image on sections.** For a sheaf `F` on the site of simplicial
opens of `Y` and an open `Ω ⊆ X`, the sections of the direct image of `F` along the augmentation
are `(a_* F)(Ω) = lim_{[n] ∈ Δ} F(a_n⁻¹ Ω)`, naturally in `F` and `Ω`. -/
def augmentationMorphism_pushforward_sectionsIso :
    (augmentationMorphism Y X a).pushforward ⋙
        sheafToPresheaf (Opens.grothendieckTopology X) (Type u) ≅
      sheafToPresheaf (SimplicialOpen.grothendieckTopology Y) (Type u) ⋙
        augmentationSections Y X a :=
  Functor.isoWhiskerLeft ((presentation Y).toEquivalence.functor ⋙ pushforwardDiagramFunctor Y X a)
      (preservesLimitNatIso (sheafToPresheaf (Opens.grothendieckTopology X) (Type u))) ≪≫
    Functor.isoWhiskerRight (pushforwardDiagramNatIso Y X a) lim ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf (SimplicialOpen.grothendieckTopology Y) (Type u))
      (sectionsDiagramLimIso Y X a)

end Stacks.Topology.Simplicial

end
