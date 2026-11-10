module

public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatTwoFibreProduct

/-!
# The comparison out of the colimit of a stagewise 2-fibre product of diagrams of categories

Let `α : X ⟶ Y` and `γ : Z ⟶ Y` be morphisms of diagrams of categories indexed by `J`. The
stagewise 2-fibre product `CategoryTheory.Cat.twoFibreProductDiagram` has a canonical cocone on
the 2-fibre product of the colimits, because each colimit inclusion fits into a strictly
commuting square with `α`, resp. `γ`, and `colimMap`. This file builds that cocone and the
resulting comparison functor

`colim (Xⱼ ×_{Yⱼ} Zⱼ) ⥤ (colim Xⱼ) ×_{colim Yⱼ} (colim Zⱼ)`,

and records that its composite with each colimit inclusion is the stagewise comparison. That the
comparison is an equivalence for filtered `J` — "filtered colimits of categories commute with
2-fibre products", used with the details omitted in the proof of Stacks 0CMW — is not proved
here.

## Main definitions

* `CategoryTheory.Cat.twoFibreProductStage`: the stagewise comparison into the 2-fibre product
  of the colimits.
* `CategoryTheory.Cat.twoFibreProductCocone`: the cocone it assembles into.
* `CategoryTheory.Cat.colimitTwoFibreProductComparison`: the comparison functor.

## Main results

* `CategoryTheory.Cat.colimitTwoFibreProductComparison_ι`: the comparison restricted to a stage
  is the stagewise comparison.

## Implementation notes

Both the stagewise comparison and the transitions of the stagewise 2-fibre product are instances
of the functoriality `CategoryTheory.Limits.CategoricalPullback.map` of Stacks 02XA, whose two
2-cells are here the transports along strictly commuting squares: `α.naturality` for the
transitions and `CategoryTheory.Limits.ι_colimMap` for the stagewise comparison. The cocone
condition is therefore an equality of functors into a 2-fibre product, proved exactly as the
functoriality law `CategoryTheory.Cat.twoFibreProductMap_comp`: with
`CategoryTheory.Cat.categoricalPullback_obj_ext` on objects and
`CategoryTheory.Limits.CategoricalPullback.hom_ext` on morphisms, the resulting chains of
transports being collapsed by `CategoryTheory.Cat.eqToHom_chain₃`.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 02XA](https://stacks.math.columbia.edu/tag/02XA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Cat

universe t v w

section Comparison

variable {J : Type v} [Category.{w} J]
  {X Y Z : J ⥤ Cat.{t, t}} (α : X ⟶ Y) (γ : Z ⟶ Y)
  [HasColimit X] [HasColimit Y] [HasColimit Z]

/-- The square relating a colimit inclusion to the colimit of a morphism of diagrams, read on
underlying functors. It commutes strictly, like a naturality square. -/
lemma ι_colimMap_toFunctor (j : J) :
    (colimit.ι X j).toFunctor ⋙ (colimMap α).toFunctor =
      (α.app j).toFunctor ⋙ (colimit.ι Y j).toFunctor := by
  rw [← Cat.Hom.comp_toFunctor, ← Cat.Hom.comp_toFunctor, ι_colimMap]

/-- The stagewise comparison from the 2-fibre product at a stage into the 2-fibre product of the
colimits. -/
noncomputable def twoFibreProductStage (j : J) :
    CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor ⥤
      CategoricalPullback (colimMap α).toFunctor (colimMap γ).toFunctor :=
  CategoricalPullback.map (α.app j).toFunctor (γ.app j).toFunctor
    (colimit.ι X j).toFunctor (colimit.ι Z j).toFunctor (colimit.ι Y j).toFunctor
    (colimMap α).toFunctor (colimMap γ).toFunctor
    (eqToIso (ι_colimMap_toFunctor γ j))
    (eqToIso (ι_colimMap_toFunctor α j).symm)

/-- The first component of the stagewise comparison at an object is the colimit inclusion of its
first component. -/
@[simp]
lemma twoFibreProductStage_obj_fst (j : J)
    (P : CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor) :
    ((twoFibreProductStage α γ j).obj P).fst = (colimit.ι X j).toFunctor.obj P.fst := rfl

/-- The second component of the stagewise comparison at an object is the colimit inclusion of its
second component. -/
@[simp]
lemma twoFibreProductStage_obj_snd (j : J)
    (P : CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor) :
    ((twoFibreProductStage α γ j).obj P).snd = (colimit.ι Z j).toFunctor.obj P.snd := rfl

/-- The first component of the stagewise comparison at a morphism is the colimit inclusion of its
first component. -/
@[simp]
lemma twoFibreProductStage_map_fst (j : J)
    {P Q : CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor} (f : P ⟶ Q) :
    ((twoFibreProductStage α γ j).map f).fst = (colimit.ι X j).toFunctor.map f.fst := rfl

/-- The second component of the stagewise comparison at a morphism is the colimit inclusion of its
second component. -/
@[simp]
lemma twoFibreProductStage_map_snd (j : J)
    {P Q : CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor} (f : P ⟶ Q) :
    ((twoFibreProductStage α γ j).map f).snd = (colimit.ι Z j).toFunctor.map f.snd := rfl

/-- The filling isomorphism of the stagewise comparison, with its two 2-cells written as
transports. -/
lemma twoFibreProductStage_obj_iso_hom (j : J)
    (P : CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor) :
    ((twoFibreProductStage α γ j).obj P).iso.hom =
      eqToHom (Functor.congr_obj (ι_colimMap_toFunctor α j) P.fst) ≫
        (colimit.ι Y j).toFunctor.map P.iso.hom ≫
          eqToHom (Functor.congr_obj (ι_colimMap_toFunctor γ j) P.snd).symm := by
  change (eqToIso (ι_colimMap_toFunctor α j).symm).inv.app P.fst ≫
      (colimit.ι Y j).toFunctor.map P.iso.hom ≫
        (eqToIso (ι_colimMap_toFunctor γ j)).inv.app P.snd = _
  simp only [CategoryTheory.eqToIso.inv]
  rw [CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_app]

/-- `CategoryTheory.Cat.twoFibreProductStage_obj_iso_hom` with the endpoints of its two transports
written as the two legs read at the comparison's value rather than as the composites
`CategoryTheory.Cat.ι_colimMap_toFunctor` produces. The two spellings are definitionally equal,
but only at default transparency: a tactic that has to compose the transport with a neighbouring
morphism cannot cross that gap on its own, and this is the form in which it can. -/
lemma twoFibreProductStage_obj_iso_hom_aligned (j : J)
    (P : CategoricalPullback (α.app j).toFunctor (γ.app j).toFunctor) :
    ((twoFibreProductStage α γ j).obj P).iso.hom =
      eqToHom ((congrArg (colimMap α).toFunctor.obj
            (twoFibreProductStage_obj_fst α γ j P)).trans
          (((Functor.comp_obj (colimit.ι X j).toFunctor (colimMap α).toFunctor P.fst).symm.trans
              (Functor.congr_obj (ι_colimMap_toFunctor α j) P.fst)).trans
            (Functor.comp_obj ((α.app j).toFunctor) (colimit.ι Y j).toFunctor P.fst))) ≫
        (colimit.ι Y j).toFunctor.map P.iso.hom ≫
          eqToHom ((((Functor.comp_obj ((γ.app j).toFunctor)
                  (colimit.ι Y j).toFunctor P.snd).symm.trans
                (Functor.congr_obj (ι_colimMap_toFunctor γ j) P.snd).symm).trans
              (Functor.comp_obj (colimit.ι Z j).toFunctor (colimMap γ).toFunctor P.snd)).trans
            (congrArg (colimMap γ).toFunctor.obj
              (twoFibreProductStage_obj_snd α γ j P).symm)) :=
  twoFibreProductStage_obj_iso_hom α γ j P

/-- A chain of three transports on either side of a morphism is the single transport, stated
with `Eq.trans` on the right so that `rw` determines every argument from the left-hand side
alone: the intermediate objects of such a chain are only definitionally equal, so a statement
whose right-hand side had to be matched syntactically would not fire. -/
lemma eqToHom_chain₃_trans {C : Type*} [Category C] {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : C}
    (p₁ : a₁ = a₂) (p₂ : a₂ = a₃) (p₃ : a₃ = a₄) (f : a₄ ⟶ b₁)
    (q₁ : b₁ = b₂) (q₂ : b₂ = b₃) (q₃ : b₃ = b₄) :
    eqToHom p₁ ≫ eqToHom p₂ ≫ eqToHom p₃ ≫ f ≫ eqToHom q₁ ≫ eqToHom q₂ ≫ eqToHom q₃ =
      eqToHom (p₁.trans (p₂.trans p₃)) ≫ f ≫ eqToHom (q₁.trans (q₂.trans q₃)) := by
  cases p₁; cases p₂; cases p₃; cases q₁; cases q₂; cases q₃; simp

/-- A chain of two transports on either side of a morphism is the single transport, in the same
`Eq.trans` form as `CategoryTheory.Cat.eqToHom_chain₃_trans`. -/
lemma eqToHom_chain₂_trans {C : Type*} [Category C] {a₁ a₂ a₃ b₁ b₂ b₃ : C}
    (p₁ : a₁ = a₂) (p₂ : a₂ = a₃) (f : a₃ ⟶ b₁) (q₁ : b₁ = b₂) (q₂ : b₂ = b₃) :
    eqToHom p₁ ≫ eqToHom p₂ ≫ f ≫ eqToHom q₁ ≫ eqToHom q₂ =
      eqToHom (p₁.trans p₂) ≫ f ≫ eqToHom (q₁.trans q₂) := by
  cases p₁; cases p₂; cases q₁; cases q₂; simp

/-- A morphism of a stage, transported to a later stage and then included into the colimit, is
its own inclusion into the colimit, modulo the induced transports. -/
lemma colimit_ι_map_map {W : J ⥤ Cat.{t, t}} [HasColimit W] {j k : J} (s : j ⟶ k)
    {a b : W.obj j} (m : a ⟶ b) :
    (colimit.ι W k).toFunctor.map ((W.map s).toFunctor.map m) =
      eqToHom (Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w W s)) a) ≫
        (colimit.ι W j).toFunctor.map m ≫
          eqToHom (Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w W s)) b).symm := by
  simpa only [Cat.Hom.comp_toFunctor, Functor.comp_map] using
    Functor.congr_hom (congrArg Cat.Hom.toFunctor (colimit.w W s)) m

/-- **The cocone condition for the stagewise comparisons.** -/
lemma twoFibreProductMap_comp_twoFibreProductStage {j k : J} (s : j ⟶ k) :
    twoFibreProductMap α γ s ⋙ twoFibreProductStage α γ k = twoFibreProductStage α γ j := by
  refine CategoryTheory.Functor.ext (fun P => ?_) (fun P Q f => ?_)
  · refine categoricalPullback_obj_ext
      (show ((twoFibreProductMap α γ s ⋙ twoFibreProductStage α γ k).obj P).fst =
          ((twoFibreProductStage α γ j).obj P).fst from
        Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w X s)) P.fst)
      (show ((twoFibreProductMap α γ s ⋙ twoFibreProductStage α γ k).obj P).snd =
          ((twoFibreProductStage α γ j).obj P).snd from
        Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w Z s)) P.snd) ?_
    dsimp only [Functor.comp_obj, twoFibreProductMap_obj_fst, twoFibreProductMap_obj_snd]
    rw [twoFibreProductStage_obj_iso_hom, twoFibreProductMap_obj_iso_hom',
      twoFibreProductStage_obj_iso_hom]
    dsimp only [Functor.comp_obj, twoFibreProductMap_obj_fst, twoFibreProductMap_obj_snd,
      twoFibreProductStage_obj_fst, twoFibreProductStage_obj_snd]
    rw [Functor.map_comp, Functor.map_comp, CategoryTheory.eqToHom_map,
      CategoryTheory.eqToHom_map, colimit_ι_map_map]
    simp only [Category.assoc]
    exact (eqToHom_chain₃_trans _ _ _ _ _ _ _).trans
      (eqToHom_chain₂_trans _ _ _ _ _).symm
  · apply CategoricalPullback.hom_ext <;>
    · dsimp only [Functor.comp_map, twoFibreProductStage_map_fst, twoFibreProductMap_map_fst,
        twoFibreProductStage_map_snd, twoFibreProductMap_map_snd]
      refine (colimit_ι_map_map s _).trans ?_
      simp [categoricalPullback_eqToHom_fst, categoricalPullback_eqToHom_snd]

/-- The canonical cocone on the stagewise 2-fibre product with apex the 2-fibre product of the
colimits. -/
noncomputable def twoFibreProductCocone : Cocone (twoFibreProductDiagram α γ) where
  pt := Cat.of (CategoricalPullback (colimMap α).toFunctor (colimMap γ).toFunctor)
  ι :=
    { app j := (twoFibreProductStage α γ j).toCatHom
      naturality _ _ s := Cat.Hom.ext <|
        (twoFibreProductMap_comp_twoFibreProductStage α γ s).trans (Functor.comp_id _).symm }

/-- **The comparison functor out of the colimit of a stagewise 2-fibre product.** -/
noncomputable def colimitTwoFibreProductComparison [HasColimit (twoFibreProductDiagram α γ)] :
    (colimit (twoFibreProductDiagram α γ) : Cat) ⥤
      CategoricalPullback (colimMap α).toFunctor (colimMap γ).toFunctor :=
  (colimit.desc (twoFibreProductDiagram α γ) (twoFibreProductCocone α γ)).toFunctor

/-- **The comparison restricted to a stage is the stagewise comparison.** -/
lemma colimitTwoFibreProductComparison_ι [HasColimit (twoFibreProductDiagram α γ)] (j : J) :
    (colimit.ι (twoFibreProductDiagram α γ) j).toFunctor ⋙
        colimitTwoFibreProductComparison α γ =
      twoFibreProductStage α γ j := by
  change ((colimit.ι (twoFibreProductDiagram α γ) j) ≫
      colimit.desc (twoFibreProductDiagram α γ) (twoFibreProductCocone α γ)).toFunctor = _
  rw [colimit.ι_desc]
  rfl

end Comparison

end CategoryTheory.Cat

end
