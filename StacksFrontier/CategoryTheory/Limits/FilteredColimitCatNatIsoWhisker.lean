module

public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatNatTransConstruction

/-!
# Stagewise isomorphisms out of a colimit in `Cat` that all come from one isomorphism

Let `F G : colimit X ⥤ D` be functors out of a colimit in `CategoryTheory.Cat` whose restrictions
to each stage `j` factor, by equalities, as `P j ⋙ F₀` and `P j ⋙ G₀` through one category `C₀`,
and let `Θ : F₀ ≅ G₀`. This file builds from `Θ` stagewise isomorphisms between the restrictions
of `F` and `G`, and shows that they are compatible with the transition functors of the diagram, in
the sense of `CategoryTheory.Cat.natIsoOfStages`, when the functors `P j` are strictly compatible
with them.

## Main definitions

* `CategoryTheory.Cat.stageIsoOfWhisker`: the stagewise isomorphism obtained from `Θ` and the two
  factorizations.

## Main results

* `CategoryTheory.Cat.stageIsoOfWhisker_hom_app` and
  `CategoryTheory.Cat.stageIsoOfWhisker_inv_app`: its components.
* `CategoryTheory.Cat.stageIsoOfWhisker_compat`: the family is compatible with the transition
  functors, which is the hypothesis `CategoryTheory.Cat.natIsoOfStages` asks for.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Cat

universe t v w t₀ u₀ tC uC

/-- A component of an isomorphism of functors at an object, read at another presentation of that
object. -/
private lemma iso_hom_app_eq_of_obj_eq {E₁ : Type*} {E₂ : Type*} [Category E₁] [Category E₂]
    {A₁ A₂ : E₁ ⥤ E₂} (Θ : A₁ ≅ A₂) {x y : E₁} (h : x = y) :
    Θ.hom.app y =
      eqToHom (congrArg A₁.obj h.symm) ≫ Θ.hom.app x ≫ eqToHom (congrArg A₂.obj h) := by
  subst h
  simp

variable {J : Type v} [Category.{w} J] (X : J ⥤ Cat.{t, t}) [HasColimit X]
  {D : Type u₀} [Category.{t₀} D] {F G : ↑(colimit X) ⥤ D}
  {C₀ : Type uC} [Category.{tC} C₀] {F₀ G₀ : C₀ ⥤ D} (Θ : F₀ ≅ G₀)
  (P : ∀ j : J, ↑(X.obj j) ⥤ C₀)
  (hL : ∀ j : J, (colimit.ι X j).toFunctor ⋙ F = P j ⋙ F₀)
  (hR : ∀ j : J, (colimit.ι X j).toFunctor ⋙ G = P j ⋙ G₀)

/-- **The stagewise isomorphism attached to one isomorphism and two factorizations.** The
restrictions of `F` and `G` to the stage `j` are `P j ⋙ F₀` and `P j ⋙ G₀`, and `Θ : F₀ ≅ G₀`
compares them after whiskering. -/
noncomputable def stageIsoOfWhisker (j : J) :
    ((colimit.ι X j).toFunctor ⋙ F) ≅ ((colimit.ι X j).toFunctor ⋙ G) :=
  eqToIso (hL j) ≪≫ Functor.isoWhiskerLeft (P j) Θ ≪≫ eqToIso (hR j).symm

/-- The components of `CategoryTheory.Cat.stageIsoOfWhisker` are those of `Θ`, transported along
the two factorizations. -/
lemma stageIsoOfWhisker_hom_app (j : J) (a : X.obj j) :
    (stageIsoOfWhisker X Θ P hL hR j).hom.app a =
      eqToHom (Functor.congr_obj (hL j) a) ≫ Θ.hom.app ((P j).obj a) ≫
        eqToHom (Functor.congr_obj (hR j).symm a) := by
  simp only [stageIsoOfWhisker, Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
    CategoryTheory.eqToHom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]

/-- The inverse components of `CategoryTheory.Cat.stageIsoOfWhisker`. -/
lemma stageIsoOfWhisker_inv_app (j : J) (a : X.obj j) :
    (stageIsoOfWhisker X Θ P hL hR j).inv.app a =
      eqToHom (Functor.congr_obj (hR j) a) ≫ Θ.inv.app ((P j).obj a) ≫
        eqToHom (Functor.congr_obj (hL j).symm a) := by
  simp only [stageIsoOfWhisker, Iso.trans_inv, NatTrans.comp_app, eqToIso.inv,
    CategoryTheory.eqToHom_app, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    Category.assoc]

/-- **The family `CategoryTheory.Cat.stageIsoOfWhisker` is compatible with the transition
functors of the diagram**, in the sense of `CategoryTheory.Cat.natIsoOfStages`, when the factoring
functors `P j` are strictly compatible with them. -/
lemma stageIsoOfWhisker_compat
    (hP : ∀ {i j : J} (r : i ⟶ j), (X.map r).toFunctor ⋙ P j = P i)
    {i j : J} (r : i ⟶ j) (a : X.obj i) :
    (stageIsoOfWhisker X Θ P hL hR i).hom.app a =
      eqToHom (congrArg F.obj (colimit_ι_obj_map X r a).symm) ≫
        (stageIsoOfWhisker X Θ P hL hR j).hom.app ((X.map r).toFunctor.obj a) ≫
          eqToHom (congrArg G.obj (colimit_ι_obj_map X r a)) := by
  have hobj : (P j).obj ((X.map r).toFunctor.obj a) = (P i).obj a :=
    Functor.congr_obj (hP r) a
  rw [stageIsoOfWhisker_hom_app, stageIsoOfWhisker_hom_app,
    iso_hom_app_eq_of_obj_eq Θ hobj]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

end CategoryTheory.Cat

end
