module

public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatStages

/-!
# Constructing a natural transformation out of a colimit of categories from stagewise data

`CategoryTheory.Cat.natTrans_ext_of_colimit` says that a `2`-cell between two functors out of a
filtered colimit in `Cat` is *determined* by its restrictions to the stages. This file provides
the matching *existence* statement: stagewise `2`-cells that agree along the transition functors
of the diagram assemble into a `2`-cell out of the colimit, and stagewise isomorphisms assemble
into an isomorphism.

The construction is the universal property of the colimit, applied not to `D` but to the arrow
category `CategoryTheory.Arrow D`. A colimit in `Cat` is a colimit in the `1`-category `Cat`, so
all it produces out of cocone data are *equalities* of functors -- never isomorphisms. But a
functor `H : C ⥤ Arrow D` together with two identifications `H ⋙ leftFunc = F` and
`H ⋙ rightFunc = G` *is* a natural transformation `F ⟶ G`, and a cocone of such functors is
exactly a compatible family of stagewise natural transformations. So the equalities the universal
property gives are the natural transformation one wants; nothing has to be known about the
presentation of the colimit, and no choice of representing stage and no well-definedness argument
are needed.

Filteredness is not used: the cocone argument works for any diagram in `Cat`. Even the
isomorphism statement only needs that every object of the colimit comes from a stage
(`CategoryTheory.Cat.exists_stage_obj_of_colimit`), which holds for any diagram, because being an
isomorphism is a condition on the components.

The target category is constrained, and this is the price of the route: the arrow category
`Arrow D` has to be an object of the same `Cat.{t, t}` as the diagram, so `D` must have its
morphisms in the colimit's universe.

## Main definitions

* `CategoryTheory.NatTrans.arrowFunctor`: the functor to the arrow category attached to a natural
  transformation.
* `CategoryTheory.Functor.natTransOfArrow`: the natural transformation read off a functor to the
  arrow category.
* `CategoryTheory.Cat.natTransOfStages`: a natural transformation out of a colimit in `Cat`,
  built from compatible stagewise natural transformations.
* `CategoryTheory.Cat.natIsoOfStages`: a natural isomorphism out of a colimit in `Cat`, built
  from compatible stagewise isomorphisms.

## Main results

* `CategoryTheory.Cat.natTransOfStages_app`,
  `CategoryTheory.Cat.natIsoOfStages_hom_app` and
  `CategoryTheory.Cat.natIsoOfStages_inv_app`: the restriction of the result to a stage is the
  given stagewise datum.

## References

* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

section Arrow

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {D : Type u₃} [Category.{v₃} D]

/-- **The functor to the arrow category attached to a natural transformation.** It sends an
object to the component of the transformation there and a morphism to the naturality square. -/
def NatTrans.arrowFunctor {F G : C ⥤ D} (σ : F ⟶ G) : C ⥤ Arrow D where
  obj x := Arrow.mk (σ.app x)
  map {_ _} f := Arrow.homMk (F.map f) (G.map f) (σ.naturality f)
  map_id _ := by apply Arrow.hom_ext <;> simp
  map_comp _ _ := by apply Arrow.hom_ext <;> simp

/-- `CategoryTheory.NatTrans.arrowFunctor` sends an object to the component of the
transformation there. -/
@[simp]
lemma NatTrans.arrowFunctor_obj {F G : C ⥤ D} (σ : F ⟶ G) (x : C) :
    σ.arrowFunctor.obj x = Arrow.mk (σ.app x) :=
  rfl

/-- The source of `CategoryTheory.NatTrans.arrowFunctor` is the source of the transformation. -/
lemma NatTrans.arrowFunctor_comp_leftFunc {F G : C ⥤ D} (σ : F ⟶ G) :
    σ.arrowFunctor ⋙ Arrow.leftFunc = F :=
  rfl

/-- The target of `CategoryTheory.NatTrans.arrowFunctor` is the target of the transformation. -/
lemma NatTrans.arrowFunctor_comp_rightFunc {F G : C ⥤ D} (σ : F ⟶ G) :
    σ.arrowFunctor ⋙ Arrow.rightFunc = G :=
  rfl

/-- **`CategoryTheory.NatTrans.arrowFunctor` turns a compatibility of components into an equality
of functors.** Precomposing the arrow functor of `σ` with `P` gives the arrow functor of `σ'`
as soon as the components match after transport along the identifications of the sources and the
targets. -/
lemma NatTrans.arrowFunctor_comp (P : C' ⥤ C) {F G : C ⥤ D} (σ : F ⟶ G)
    {F' G' : C' ⥤ D} (σ' : F' ⟶ G') (hF : P ⋙ F = F') (hG : P ⋙ G = G')
    (h : ∀ a : C', σ'.app a = eqToHom (Functor.congr_obj hF a).symm ≫ σ.app (P.obj a) ≫
      eqToHom (Functor.congr_obj hG a)) :
    P ⋙ σ.arrowFunctor = σ'.arrowFunctor := by
  subst hF hG
  obtain rfl : Functor.whiskerLeft P σ = σ' :=
    NatTrans.ext (funext fun a => by simpa using (h a).symm)
  rfl

/-- Equal arrows have, after transport, the same underlying morphism. -/
lemma Arrow.hom_eq_of_eq {A B : Arrow D} (h : A = B) :
    A.hom = eqToHom (congrArg (fun z : Arrow D => z.left) h) ≫ B.hom ≫
      eqToHom (congrArg (fun z : Arrow D => z.right) h).symm := by
  subst h
  simp

/-- A morphism conjugated by two round trips of `CategoryTheory.eqToHom` is itself. The four
equalities are read off different presentations of the same two objects, which is why this is
stated over an abstract category and applied with `exact`. -/
private lemma eqToHom_loop {E : Type u₁} [Category E] {x x' y y' : E} (h₁ : x = x') (h₂ : x' = x)
    (f : x ⟶ y) (h₃ : y = y') (h₄ : y' = y) :
    eqToHom h₁ ≫ (eqToHom h₂ ≫ f ≫ eqToHom h₃) ≫ eqToHom h₄ = f := by
  subst h₁ h₃
  simp

/-- **The natural transformation read off a functor to the arrow category.** Given
identifications of the source and the target functors of `H` with `F` and `G`, the arrows
`H.obj x` are the components of a natural transformation `F ⟶ G`. -/
def Functor.natTransOfArrow (H : C ⥤ Arrow D) {F G : C ⥤ D}
    (hF : H ⋙ Arrow.leftFunc = F) (hG : H ⋙ Arrow.rightFunc = G) : F ⟶ G :=
  eqToHom hF.symm ≫ Functor.whiskerLeft H Arrow.leftToRight ≫ eqToHom hG

/-- The components of `CategoryTheory.Functor.natTransOfArrow` are the arrows `H.obj x`. -/
lemma Functor.natTransOfArrow_app (H : C ⥤ Arrow D) {F G : C ⥤ D}
    (hF : H ⋙ Arrow.leftFunc = F) (hG : H ⋙ Arrow.rightFunc = G) (x : C) :
    (H.natTransOfArrow hF hG).app x =
      eqToHom (Functor.congr_obj hF.symm x) ≫ (H.obj x).hom ≫
        eqToHom (Functor.congr_obj hG x) := by
  rw [Functor.natTransOfArrow]
  simp only [NatTrans.comp_app, eqToHom_app, Functor.whiskerLeft_app, Arrow.leftToRight_app,
    Category.assoc]
  rfl

/-- **`CategoryTheory.Functor.natTransOfArrow` restricted along a functor `P` is the
transformation whose arrow functor `H` restricts to.** The stagewise datum is stated at the
composite functors `P ⋙ F` and `P ⋙ G`, so that no transport appears. -/
lemma Functor.natTransOfArrow_app_of_comp (P : C' ⥤ C) (H : C ⥤ Arrow D) {F G : C ⥤ D}
    (hF : H ⋙ Arrow.leftFunc = F) (hG : H ⋙ Arrow.rightFunc = G)
    (σ' : (P ⋙ F) ⟶ (P ⋙ G)) (hc : P ⋙ H = σ'.arrowFunctor) (a : C') :
    (H.natTransOfArrow hF hG).app (P.obj a) = σ'.app a := by
  have h : H.obj (P.obj a) = Arrow.mk (σ'.app a) := Functor.congr_obj hc a
  rw [Functor.natTransOfArrow_app, Arrow.hom_eq_of_eq h]
  exact eqToHom_loop _ _ _ _ _

end Arrow

namespace Cat

universe t u v w

section Transitions

variable {J : Type v} [Category.{w} J] (Y : J ⥤ Cat.{t, t}) [HasColimit Y]

/-- The colimit inclusion of a stage is the inclusion of any later stage, precomposed with the
transition functor, read on objects. -/
lemma colimit_ι_obj_map {i j : J} (r : i ⟶ j) (a : Y.obj i) :
    (colimit.ι Y j).toFunctor.obj ((Y.map r).toFunctor.obj a) =
      (colimit.ι Y i).toFunctor.obj a :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w Y r)) a

/-- The colimit inclusion of a stage is the inclusion of any later stage, precomposed with the
transition functor, after a further functor. -/
lemma map_comp_ι_comp {D : Type u} [Category.{t} D] (H : ↑(colimit Y) ⥤ D) {i j : J}
    (r : i ⟶ j) :
    (Y.map r).toFunctor ⋙ ((colimit.ι Y j).toFunctor ⋙ H) =
      (colimit.ι Y i).toFunctor ⋙ H :=
  congrArg (fun K : Y.obj i ⥤ ↑(colimit Y) => K ⋙ H)
    (congrArg Cat.Hom.toFunctor (colimit.w Y r))

end Transitions

section Stages

variable {J : Type v} [Category.{w} J]
  (X : J ⥤ Cat.{max u v w, max u v w}) [HasColimit X]
  [HasColimit (X ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
  {D : Type (max u v w)} [Category.{max u v w} D] {F G : ↑(colimit X) ⥤ D}

variable (σ : ∀ j : J, ((colimit.ι X j).toFunctor ⋙ F) ⟶ ((colimit.ι X j).toFunctor ⋙ G))
  (hσ : ∀ {i j : J} (r : i ⟶ j) (a : X.obj i), (σ i).app a =
    eqToHom (congrArg F.obj (colimit_ι_obj_map X r a).symm) ≫
      (σ j).app ((X.map r).toFunctor.obj a) ≫
        eqToHom (congrArg G.obj (colimit_ι_obj_map X r a)))

include σ hσ in
/-- **The cocone of arrow categories of a compatible family of stagewise natural
transformations.** Its vertex is the arrow category of `D` and its leg at a stage is the arrow
functor (`CategoryTheory.NatTrans.arrowFunctor`) of the transformation given there; the
compatibility `hσ` is exactly its naturality. -/
noncomputable def stagesArrowCocone : Cocone X where
  pt := Cat.of (Arrow D)
  ι :=
    { app := fun j => (NatTrans.arrowFunctor (σ j)).toCatHom
      naturality := fun {i j} r => Cat.Hom.ext <|
        (NatTrans.arrowFunctor_comp (X.map r).toFunctor (σ j) (σ i)
          (map_comp_ι_comp X F r) (map_comp_ι_comp X G r) fun a => hσ r a).trans
          (Functor.comp_id _).symm }

/-- The colimit inclusion of a stage, followed by the functor
`CategoryTheory.Cat.stagesArrowCocone` descends to, is the arrow functor of the stagewise
transformation. -/
lemma ι_comp_desc_stagesArrowCocone (j : J) :
    (colimit.ι X j).toFunctor ⋙ (colimit.desc X (stagesArrowCocone.{u, v, w} X σ hσ)).toFunctor =
      (σ j).arrowFunctor :=
  congrArg Cat.Hom.toFunctor (colimit.ι_desc (stagesArrowCocone.{u, v, w} X σ hσ) j)

/-- Postcomposing the functor `CategoryTheory.Cat.stagesArrowCocone` descends to with `P` gives `K`
as soon as this holds at every stage. -/
private lemma desc_stagesArrowCocone_comp_eq (P : Arrow D ⥤ D) (K : ↑(colimit X) ⥤ D)
    (h : ∀ j, (σ j).arrowFunctor ⋙ P = (colimit.ι X j).toFunctor ⋙ K) :
    (colimit.desc X (stagesArrowCocone.{u, v, w} X σ hσ)).toFunctor ⋙ P = K :=
  congrArg Cat.Hom.toFunctor <| show _ ≫ P.toCatHom = K.toCatHom from
    colimit.hom_ext fun j => Cat.Hom.ext <|
      (congrArg (fun L : X.obj j ⥤ Arrow D => L ⋙ P)
        (ι_comp_desc_stagesArrowCocone.{u, v, w} X σ hσ j)).trans (h j)

/-- The functor `CategoryTheory.Cat.stagesArrowCocone` descends to has `F` for its source. -/
lemma desc_stagesArrowCocone_comp_leftFunc :
    (colimit.desc X (stagesArrowCocone.{u, v, w} X σ hσ)).toFunctor ⋙ Arrow.leftFunc = F :=
  desc_stagesArrowCocone_comp_eq X σ hσ _ _ fun _ => rfl

/-- The functor `CategoryTheory.Cat.stagesArrowCocone` descends to has `G` for its target. -/
lemma desc_stagesArrowCocone_comp_rightFunc :
    (colimit.desc X (stagesArrowCocone.{u, v, w} X σ hσ)).toFunctor ⋙ Arrow.rightFunc = G :=
  desc_stagesArrowCocone_comp_eq X σ hσ _ _ fun _ => rfl

/-- **A natural transformation out of a colimit in `Cat`, built from stagewise natural
transformations.** The stagewise data must agree along the transition functors of the diagram
(`hσ`); the resulting transformation restricts to the given one at every stage
(`CategoryTheory.Cat.natTransOfStages_app`). -/
noncomputable def natTransOfStages : F ⟶ G :=
  Functor.natTransOfArrow (colimit.desc X (stagesArrowCocone.{u, v, w} X σ hσ)).toFunctor
    (desc_stagesArrowCocone_comp_leftFunc.{u, v, w} X σ hσ)
    (desc_stagesArrowCocone_comp_rightFunc.{u, v, w} X σ hσ)

/-- **`CategoryTheory.Cat.natTransOfStages` restricts to the given transformation at every
stage.** -/
lemma natTransOfStages_app (j : J) (a : X.obj j) :
    (natTransOfStages.{u, v, w} X σ hσ).app ((colimit.ι X j).toFunctor.obj a) = (σ j).app a :=
  Functor.natTransOfArrow_app_of_comp (colimit.ι X j).toFunctor
    (colimit.desc X (stagesArrowCocone.{u, v, w} X σ hσ)).toFunctor _ _ (σ j)
    (ι_comp_desc_stagesArrowCocone.{u, v, w} X σ hσ j) a

end Stages

section StagesIso

variable {J : Type v} [Category.{w} J]
  (X : J ⥤ Cat.{max u v w, max u v w}) [HasColimit X]
  [HasColimit (X ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
  {D : Type (max u v w)} [Category.{max u v w} D] {F G : ↑(colimit X) ⥤ D}
  (ε : ∀ j : J, ((colimit.ι X j).toFunctor ⋙ F) ≅ ((colimit.ι X j).toFunctor ⋙ G))
  (hε : ∀ {i j : J} (r : i ⟶ j) (a : X.obj i), (ε i).hom.app a =
    eqToHom (congrArg F.obj (colimit_ι_obj_map X r a).symm) ≫
      (ε j).hom.app ((X.map r).toFunctor.obj a) ≫
        eqToHom (congrArg G.obj (colimit_ι_obj_map X r a)))

/-- A natural transformation out of a colimit in `Cat` whose restriction to every stage is an
isomorphism is an isomorphism: every object of the colimit comes from a stage. -/
lemma isIso_natTransOfStages_of_isIso
    (σ : ∀ j : J, ((colimit.ι X j).toFunctor ⋙ F) ⟶ ((colimit.ι X j).toFunctor ⋙ G))
    (hσ : ∀ {i j : J} (r : i ⟶ j) (a : X.obj i), (σ i).app a =
      eqToHom (congrArg F.obj (colimit_ι_obj_map X r a).symm) ≫
        (σ j).app ((X.map r).toFunctor.obj a) ≫
          eqToHom (congrArg G.obj (colimit_ι_obj_map X r a)))
    (h : ∀ (j : J) (a : X.obj j), IsIso ((σ j).app a)) :
    IsIso (natTransOfStages.{u, v, w} X σ hσ) := by
  have happ : ∀ z : ↑(colimit X), IsIso ((natTransOfStages.{u, v, w} X σ hσ).app z) := by
    intro z
    obtain ⟨j, a, rfl⟩ := exists_stage_obj_of_colimit.{u, v, w} X z
    rw [natTransOfStages_app]
    exact h j a
  exact NatIso.isIso_of_isIso_app _

include ε hε in
/-- **A natural isomorphism out of a colimit in `Cat`, built from stagewise isomorphisms.** The
stagewise data must agree along the transition functors of the diagram (`hε`); the resulting
isomorphism restricts to the given one at every stage
(`CategoryTheory.Cat.natIsoOfStages_hom_app`). -/
noncomputable def natIsoOfStages : F ≅ G :=
  letI := isIso_natTransOfStages_of_isIso.{u, v, w} X (fun j => (ε j).hom) hε
    fun j a => inferInstanceAs (IsIso (((ε j).app a).hom))
  asIso (natTransOfStages.{u, v, w} X (fun j => (ε j).hom) hε)

/-- `CategoryTheory.Cat.natIsoOfStages` is `CategoryTheory.Cat.natTransOfStages`. -/
lemma natIsoOfStages_hom :
    (natIsoOfStages.{u, v, w} X ε hε).hom = natTransOfStages.{u, v, w} X (fun j => (ε j).hom) hε :=
  rfl

/-- **`CategoryTheory.Cat.natIsoOfStages` restricts to the given isomorphism at every stage.** -/
lemma natIsoOfStages_hom_app (j : J) (a : X.obj j) :
    (natIsoOfStages.{u, v, w} X ε hε).hom.app ((colimit.ι X j).toFunctor.obj a) = (ε j).hom.app a :=
  natTransOfStages_app.{u, v, w} X (fun j => (ε j).hom) hε j a

/-- **The inverse of `CategoryTheory.Cat.natIsoOfStages` restricts to the inverse of the given
isomorphism at every stage.** -/
lemma natIsoOfStages_inv_app (j : J) (a : X.obj j) :
    (natIsoOfStages.{u, v, w} X ε hε).inv.app ((colimit.ι X j).toFunctor.obj a) =
      (ε j).inv.app a := by
  have h : (ε j).hom.app a ≫
      (natIsoOfStages.{u, v, w} X ε hε).inv.app ((colimit.ι X j).toFunctor.obj a) = 𝟙 _ := by
    conv_lhs => rw [← natIsoOfStages_hom_app.{u, v, w} X ε hε j a]
    exact (natIsoOfStages.{u, v, w} X ε hε).hom_inv_id_app _
  exact (cancel_epi ((ε j).hom.app a)).mp (h.trans ((ε j).hom_inv_id_app a).symm)

end StagesIso

end Cat

end CategoryTheory

end
