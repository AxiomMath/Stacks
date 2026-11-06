module

public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import Mathlib.CategoryTheory.Category.Cat.Colimit
public import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Filtered colimits in the category of categories

A colimit of a diagram `F : I ⥤ Cat` is computed in Mathlib as a quotient, so neither its
objects nor its morphisms are presented as coming from a stage of the diagram. This file supplies
the two facts that make a *filtered* such colimit behave like a filtered colimit of sets:

* every object of `colimit F` is the image of an object of some stage, and two objects of stages
  with the same image in the colimit already agree at a common later stage;
* every morphism of `colimit F` between images of stage objects is, at a common later stage, the
  image of a morphism of that stage.

## Main results

* `CategoryTheory.Cat.exists_stage_obj_of_colimit`
* `CategoryTheory.Cat.exists_common_stage_eq_of_colimit_ι_obj_eq`
* `CategoryTheory.Cat.exists_stage_map_of_colimit`

## Implementation notes

The statement about *objects* is obtained by transporting the question to simplicial sets. The
nerve functor has the homotopy-category functor as a left inverse up to isomorphism
(`CategoryTheory.nerveFunctorCompHoFunctorIso`) and the latter preserves colimits, so `colimit F`
is the homotopy category of the colimit of the nerves
(`CategoryTheory.Cat.colimitIsoHoColimitNerve`); the objects of a homotopy category are the
`0`-simplices, colimits of simplicial sets are computed objectwise, and colimits of types are
where the jointly-surjective and filtered-identification statements of Mathlib live.

The statement about *morphisms* cannot be obtained the same way, because a morphism of a homotopy
category is an equivalence class of paths of `1`-simplices, not a `1`-simplex. Instead it is a
terminality argument inside `Cat`: the morphisms that *do* come from a stage form a
multiplicative class (`CategoryTheory.MorphismProperty.IsMultiplicative`) — filteredness is what
makes two composable stage morphisms land at a common stage — so they span a wide subcategory of
`colimit F` through which the colimit cocone factors. The factorisation composed with the
inclusion is the identity of `colimit F` by the universal property, so every morphism of
`colimit F` is in the class.

Both statements are inevitably heterogeneous: a morphism of a stage maps to a morphism between
*images* of its endpoints, and those images are only *equal* to the given objects, not
definitionally them. `CategoryTheory.Cat.transport_hom_of_heq`,
`CategoryTheory.Cat.map_heq_of_eq` and `CategoryTheory.Cat.comp_heq_of_eq` are the three
transports needed to use them.

## References

* [Stacks Project, Tag 0CMS](https://stacks.math.columbia.edu/tag/0CMS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite SimplicialObject

namespace CategoryTheory.Cat

universe u v w

/-- A colimit in `Cat` is the homotopy category of the colimit of the nerves: the nerve is
fully faithful with the homotopy-category functor as a left inverse
(`CategoryTheory.nerveFunctorCompHoFunctorIso`), and the homotopy-category functor preserves
colimits, being a left adjoint. -/
noncomputable def colimitIsoHoColimitNerve
    {I : Type v} [Category.{w} I]
    (F : I ⥤ Cat.{max u v w, max u v w}) [HasColimit F]
    [HasColimit (F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})] :
    colimit F ≅ SSet.hoFunctor.{max u v w}.obj
      (colimit (F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})) := by
  let G := F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w}
  let n : G ⋙ SSet.hoFunctor.{max u v w} ≅ F :=
    (Functor.associator F CategoryTheory.nerveFunctor.{max u v w, max u v w}
      SSet.hoFunctor.{max u v w}).symm ≪≫
      Functor.isoWhiskerLeft F CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w} ≪≫
        F.rightUnitor
  exact (HasColimit.isoOfNatIso n).symm ≪≫
    (preservesColimitIso SSet.hoFunctor.{max u v w} G).symm

/-- `CategoryTheory.Cat.colimitIsoHoColimitNerve` composed with the colimit inclusion of a
stage is the inverse of the nerve-homotopy comparison at that stage, followed by the image of
the colimit inclusion of the nerves. -/
lemma colimitIsoHoColimitNerve_hom_ι
    {I : Type v} [Category.{w} I]
    (F : I ⥤ Cat.{max u v w, max u v w}) [HasColimit F]
    [HasColimit (F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    (i : I) :
    colimit.ι F i ≫ (colimitIsoHoColimitNerve.{u, v, w} F).hom =
      (((Functor.associator F CategoryTheory.nerveFunctor.{max u v w, max u v w}
          SSet.hoFunctor.{max u v w}).symm ≪≫
          Functor.isoWhiskerLeft F CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w} ≪≫
            F.rightUnitor).inv.app i) ≫
        SSet.hoFunctor.{max u v w}.map
          (colimit.ι (F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w}) i) := by
  let G := F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w}
  let n : G ⋙ SSet.hoFunctor.{max u v w} ≅ F :=
    (Functor.associator F CategoryTheory.nerveFunctor.{max u v w, max u v w}
      SSet.hoFunctor.{max u v w}).symm ≪≫
      Functor.isoWhiskerLeft F CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w} ≪≫
        F.rightUnitor
  calc
    colimit.ι F i ≫ (colimitIsoHoColimitNerve.{u, v, w} F).hom =
        (colimit.ι F i ≫ (HasColimit.isoOfNatIso n).inv) ≫
          (preservesColimitIso SSet.hoFunctor.{max u v w} G).inv := by
            simp [colimitIsoHoColimitNerve, Iso.trans_hom, Iso.symm_hom, G, n]
    _ = (n.inv.app i ≫ colimit.ι (G ⋙ SSet.hoFunctor.{max u v w}) i) ≫
          (preservesColimitIso SSet.hoFunctor.{max u v w} G).inv := by
            rw [HasColimit.isoOfNatIso_ι_inv]
    _ = n.inv.app i ≫ SSet.hoFunctor.{max u v w}.map (colimit.ι G i) := by
          rw [Category.assoc, ι_preservesColimitIso_inv]

/-- `CategoryTheory.Cat.colimitIsoHoColimitNerve` sends the image of an object of a stage to
the image of its vertex in the colimit of the nerves. -/
lemma colimitIsoHoColimitNerve_obj_ι
    {I : Type v} [Category.{w} I]
    (F : I ⥤ Cat.{max u v w, max u v w}) [HasColimit F]
    [HasColimit (F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    (i : I) (x : F.obj i) :
    ((colimitIsoHoColimitNerve.{u, v, w} F).hom.toFunctor.obj
      ((colimit.ι F i).toFunctor.obj x)) =
      (SSet.mapHomotopyCategory
        (colimit.ι (F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w}) i)).obj
        ((CategoryTheory.nerveFunctorCompHoFunctorIso.inv.app (F.obj i)).toFunctor.obj x) := by
  have h := congrArg (fun f : Cat.Hom _ _ => f.toFunctor.obj x)
    (colimitIsoHoColimitNerve_hom_ι.{u, v, w} F i)
  simpa [Functor.comp_obj, CategoryTheory.nerveFunctorCompHoFunctorIso] using h

universe uCat vCat

private lemma catIso_inv_hom_obj {C D : Cat.{vCat, uCat}}
    (e : C ≅ D) (x : C) : e.inv.toFunctor.obj (e.hom.toFunctor.obj x) = x := by
  simpa only [Cat.Hom.comp_obj, Cat.Hom.id_obj] using
    congrArg (fun f : Cat.Hom _ _ => f.toFunctor.obj x) e.hom_inv_id

private lemma catIso_hom_inv_obj {C D : Cat.{vCat, uCat}}
    (e : C ≅ D) (x : D) : e.hom.toFunctor.obj (e.inv.toFunctor.obj x) = x := by
  simpa only [Cat.Hom.comp_obj, Cat.Hom.id_obj] using
    congrArg (fun f : Cat.Hom _ _ => f.toFunctor.obj x) e.inv_hom_id

private lemma homotopyObj_map {X Y : SSet.{uCat}} (f : X ⟶ Y)
    (x : X.HomotopyCategory) :
    SSet.HomotopyCategory.objEquiv.{uCat} ((SSet.mapHomotopyCategory f).obj x) =
      f.app (op (SimplexCategory.mk 0)) (SSet.HomotopyCategory.objEquiv.{uCat} x) := by
  cases x using SSet.HomotopyCategory.rec with
  | mk x => rfl

private lemma exists_stage_of_colimit_app
    {I : Type v} [Category.{w} I]
    (H : I ⥤ SSet.{max u v w}) [HasColimit H]
    (n : SimplexCategoryᵒᵖ) [HasColimit (H ⋙ (evaluation _ _).obj n)]
    (x : (colimit H).obj n) :
    ∃ (i : I) (y : (H.obj i).obj n), (colimit.ι H i).app n y = x := by
  let T := H ⋙ (evaluation _ _).obj n
  let e := colimitObjIsoColimitCompEvaluation H n
  obtain ⟨i, y, hy⟩ := Types.jointly_surjective' (e.hom x)
  have hs : e.hom ((colimit.ι H i).app n y) = colimit.ι T i y :=
    ConcreteCategory.congr_hom (colimitObjIsoColimitCompEvaluation_ι_app_hom H i n) y
  exact ⟨i, y, by simpa using congrArg e.inv.hom (hs.trans hy)⟩

private lemma exists_common_stage_eq_of_colimit_app_eq
    {I : Type v} [Category.{w} I] [IsFiltered I]
    (H : I ⥤ SSet.{max u v w}) [HasColimit H]
    (n : SimplexCategoryᵒᵖ) [HasColimit (H ⋙ (evaluation _ _).obj n)]
    {i j : I} (x : (H.obj i).obj n) (y : (H.obj j).obj n)
    (h : (colimit.ι H i).app n x = (colimit.ι H j).app n y) :
    ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k), (H.map f).app n x = (H.map g).app n y := by
  let T := H ⋙ (evaluation _ _).obj n
  let e := colimitObjIsoColimitCompEvaluation H n
  have h' : colimit.ι T i x = colimit.ι T j y := by
    have hi : e.hom ((colimit.ι H i).app n x) = colimit.ι T i x :=
      ConcreteCategory.congr_hom (colimitObjIsoColimitCompEvaluation_ι_app_hom H i n) x
    have hj : e.hom ((colimit.ι H j).app n y) = colimit.ι T j y :=
      ConcreteCategory.congr_hom (colimitObjIsoColimitCompEvaluation_ι_app_hom H j n) y
    exact hi.symm.trans ((congrArg e.hom h).trans hj)
  exact (Types.FilteredColimit.colimit_eq_iff T).mp h'

/-- **Objects of a filtered colimit in `Cat` are identified only at a later stage.** If two
objects, taken from stages `i` and `j` of a filtered diagram of categories, have the same image
in the colimit, then they already agree at some stage `k` after both. -/
lemma exists_common_stage_eq_of_colimit_ι_obj_eq
    {I : Type v} [Category.{w} I] [IsFiltered I]
    (F : I ⥤ Cat.{max u v w, max u v w}) [HasColimit F]
    [HasColimit (F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    {i j : I} (x : F.obj i) (y : F.obj j)
    (h : (colimit.ι F i).toFunctor.obj x = (colimit.ι F j).toFunctor.obj y) :
    ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k),
      (F.map f).toFunctor.obj x = (F.map g).toFunctor.obj y := by
  let H := F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w}
  let e := colimitIsoHoColimitNerve.{u, v, w} F
  let x₀ := (SSet.HomotopyCategory.objEquiv.{max u v w})
    ((CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w}.inv.app (F.obj i)).toFunctor.obj x)
  let y₀ := (SSet.HomotopyCategory.objEquiv.{max u v w})
    ((CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w}.inv.app (F.obj j)).toFunctor.obj y)
  let neI := CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w}.app (F.obj i)
  let neJ := CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w}.app (F.obj j)
  have hx₀ : SSet.HomotopyCategory.mk x₀ =
      neI.inv.toFunctor.obj x :=
    (SSet.HomotopyCategory.objEquiv.{max u v w}).symm_apply_apply _
  have hy₀ : SSet.HomotopyCategory.mk y₀ =
      neJ.inv.toFunctor.obj y :=
    (SSet.HomotopyCategory.objEquiv.{max u v w}).symm_apply_apply _
  have h' : (colimit.ι H i).app (op (SimplexCategory.mk 0)) x₀ =
      (colimit.ι H j).app (op (SimplexCategory.mk 0)) y₀ := by
    have heq := congrArg e.hom.toFunctor.obj h
    rw [colimitIsoHoColimitNerve_obj_ι, colimitIsoHoColimitNerve_obj_ι] at heq
    have hpts := congrArg (SSet.HomotopyCategory.objEquiv.{max u v w}) heq
    rw [homotopyObj_map.{max u v w}, homotopyObj_map.{max u v w}] at hpts
    simpa [x₀, y₀] using hpts
  obtain ⟨k, f, g, hxy⟩ := exists_common_stage_eq_of_colimit_app_eq.{u, v, w} H
    (op (SimplexCategory.mk 0)) x₀ y₀ h'
  refine ⟨k, f, g, ?_⟩
  have key : ∀ {m : I} (u : m ⟶ k) (z : F.obj m)
      (z₀ : (H.obj m).obj (op (SimplexCategory.mk 0))),
      SSet.HomotopyCategory.mk z₀ =
        (CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w}.app
          (F.obj m)).inv.toFunctor.obj z →
      (CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w}.app (F.obj k)).hom.toFunctor.obj
        ((SSet.hoFunctor.map (H.map u)).toFunctor.obj (SSet.HomotopyCategory.mk z₀)) =
          (F.map u).toFunctor.obj z := by
    intro m u z z₀ hz₀
    have hn' := congrArg (fun w : Cat.Hom _ _ => w.toFunctor.obj (SSet.HomotopyCategory.mk z₀))
      ((CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w}).hom.naturality (F.map u))
    have hz : (CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w}.hom.app
        (F.obj m)).toFunctor.obj (SSet.HomotopyCategory.mk z₀) = z := by
      rw [hz₀]
      exact catIso_hom_inv_obj
        (CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w}.app (F.obj m)) z
    simpa [Cat.Hom.comp_toFunctor, Functor.comp_obj, SSet.hoFunctor,
      SSet.mapHomotopyCategory_obj_mk, hz, H, Functor.comp_map] using hn'
  have hmid : SSet.HomotopyCategory.mk ((H.map f).app (op (SimplexCategory.mk 0)) x₀) =
      SSet.HomotopyCategory.mk ((H.map g).app (op (SimplexCategory.mk 0)) y₀) :=
    congrArg SSet.HomotopyCategory.mk hxy
  rw [← key f x x₀ hx₀, ← key g y y₀ hy₀]
  exact congrArg _ hmid

/-- **Objects of a colimit in `Cat` come from a stage.** Every object of the colimit of a
diagram of categories is the image of an object of one of the stages. -/
lemma exists_stage_obj_of_colimit
    {I : Type v} [Category.{w} I]
    (F : I ⥤ Cat.{max u v w, max u v w}) [HasColimit F]
    [HasColimit (F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    (x : ↑(colimit F)) :
    ∃ (i : I) (y : F.obj i), (colimit.ι F i).toFunctor.obj y = x := by
  let H := F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w}
  let e := colimitIsoHoColimitNerve.{u, v, w} F
  let p := SSet.HomotopyCategory.objEquiv.{max u v w} (e.hom.toFunctor.obj x)
  obtain ⟨i, z, hz⟩ := exists_stage_of_colimit_app.{u, v, w} H
    (op (SimplexCategory.mk 0)) p
  let y :=
    (CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w}.app (F.obj i)).hom.toFunctor.obj
      (SSet.HomotopyCategory.mk z)
  have hobj : e.hom.toFunctor.obj ((colimit.ι F i).toFunctor.obj y) =
      e.hom.toFunctor.obj x := by
    rw [colimitIsoHoColimitNerve_obj_ι]
    show (SSet.mapHomotopyCategory (colimit.ι H i)).obj
        ((CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w}.app
          (F.obj i)).inv.toFunctor.obj y) = _
    rw [catIso_inv_hom_obj
      (CategoryTheory.nerveFunctorCompHoFunctorIso.{max u v w}.app (F.obj i))
      (SSet.HomotopyCategory.mk z)]
    rw [SSet.mapHomotopyCategory_obj_mk]
    calc
      SSet.HomotopyCategory.mk ((colimit.ι H i).app (op (SimplexCategory.mk 0)) z) =
          SSet.HomotopyCategory.mk p := congrArg SSet.HomotopyCategory.mk (by simpa [p] using hz)
      _ = e.hom.toFunctor.obj x :=
        (SSet.HomotopyCategory.objEquiv.{max u v w}).symm_apply_apply _
  have hobj' := congrArg e.inv.toFunctor.obj hobj
  have hleft := catIso_inv_hom_obj e ((colimit.ι F i).toFunctor.obj y)
  have hright := catIso_inv_hom_obj e x
  rw [hleft, hright] at hobj'
  exact ⟨i, y, hobj'⟩

/-- Composition respects heterogeneous equality of morphisms along equalities of their sources
and targets. -/
lemma comp_heq_of_eq {C : Type*} [Category C]
    {a b c a' b' c' : C} (ha : a = a') (hb : b = b') (hc : c = c')
    {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'} {g' : b' ⟶ c'}
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  subst a' b' c'
  cases hf
  cases hg
  rfl

private def stageMorphism {I : Type v} [Category.{w} I]
    (F : I ⥤ Cat.{max u v w, max u v w}) [HasColimit F] :
    MorphismProperty (colimit F : Cat) := fun a b f =>
  ∃ (i : I) (x y : F.obj i) (g : x ⟶ y),
    (colimit.ι F i).toFunctor.obj x = a ∧
    (colimit.ι F i).toFunctor.obj y = b ∧
    HEq ((colimit.ι F i).toFunctor.map g) f

private lemma stageMorphism_isMultiplicative
    {I : Type v} [Category.{w} I] [IsFiltered I]
    (F : I ⥤ Cat.{max u v w, max u v w}) [HasColimit F]
    [HasColimit (F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})] :
    (stageMorphism.{u, v, w} F).IsMultiplicative := by
  refine { id_mem := ?_, comp_mem := ?_ }
  · intro a
    obtain ⟨i, x, rfl⟩ := exists_stage_obj_of_colimit.{u, v, w} F a
    exact ⟨i, x, x, 𝟙 x, rfl, rfl, by simp⟩
  · intro a b c f g hf hg
    obtain ⟨i, x, y, f', hx, hy, hf⟩ := hf
    obtain ⟨j, y', z, g', hy', hz, hg⟩ := hg
    obtain ⟨k, s, t, e⟩ :=
      exists_common_stage_eq_of_colimit_ι_obj_eq.{u, v, w} F y y' (hy.trans hy'.symm)
    have hs := congrArg Cat.Hom.toFunctor (colimit.w F s)
    have ht := congrArg Cat.Hom.toFunctor (colimit.w F t)
    have hxk := (Functor.congr_obj hs x).trans hx
    have hyk := (Functor.congr_obj hs y).trans hy
    have hzk := (Functor.congr_obj ht z).trans hz
    refine ⟨k, (F.map s).toFunctor.obj x, (F.map t).toFunctor.obj z,
      (F.map s).toFunctor.map f' ≫ eqToHom e ≫ (F.map t).toFunctor.map g',
      hxk, hzk, ?_⟩
    rw [Functor.map_comp, Functor.map_comp, eqToHom_map]
    exact comp_heq_of_eq hxk hyk hzk
      ((Functor.hcongr_hom hs f').trans hf)
      ((eqToHom_comp_heq _ _).trans ((Functor.hcongr_hom ht g').trans hg))

private lemma isStageMorphism
    {I : Type v} [Category.{w} I] [IsFiltered I]
    (F : I ⥤ Cat.{max u v w, max u v w}) [HasColimit F]
    [HasColimit (F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    {a b : (colimit F : Cat)} (f : a ⟶ b) : stageMorphism.{u, v, w} F f := by
  let P := stageMorphism.{u, v, w} F
  let : P.IsMultiplicative := stageMorphism_isMultiplicative.{u, v, w} F
  let inc := wideSubcategoryInclusion P
  let lift (i : I) : F.obj i ⥤ WideSubcategory P :=
    { obj := fun x => ⟨(colimit.ι F i).toFunctor.obj x⟩
      map := fun {x y} g => ⟨(colimit.ι F i).toFunctor.map g,
        ⟨i, x, y, g, rfl, rfl, HEq.rfl⟩⟩
      map_id := fun x => by apply WideSubcategory.hom_ext; exact CategoryTheory.Functor.map_id _ _
      map_comp := fun g h => by apply WideSubcategory.hom_ext; exact Functor.map_comp _ _ _ }
  have hlift (i : I) : lift i ⋙ inc = (colimit.ι F i).toFunctor := rfl
  let c : Cocone F :=
    { pt := Cat.of (WideSubcategory P)
      ι := { app := fun i => (lift i).toCatHom
             naturality := by
               intro i j s
               apply Cat.Hom.ext
               refine CategoryTheory.Functor.ext (fun x => WideSubcategory.ext
                 (Functor.congr_obj (congrArg Cat.Hom.toFunctor (colimit.w F s)) x)) ?_
               intro x y g
               apply inc.map_injective
               simp only [Functor.map_comp, eqToHom_map]
               show (colimit.ι F j).toFunctor.map ((F.map s).toFunctor.map g) =
                 eqToHom _ ≫ (colimit.ι F i).toFunctor.map g ≫ eqToHom _
               exact Functor.congr_hom (congrArg Cat.Hom.toFunctor (colimit.w F s)) g } }
  let d := colimit.desc F c
  have hd : d ≫ inc.toCatHom = 𝟙 (colimit F) := colimit.hom_ext fun i => by
    rw [← Category.assoc, colimit.ι_desc]
    exact (Category.comp_id _).symm
  have he := congrArg Cat.Hom.toFunctor hd
  obtain ⟨i, x, y, g, hx, hy, hg⟩ : P ((d.toFunctor ⋙ inc).map f) := (d.toFunctor.map f).property
  exact ⟨i, x, y, g, hx.trans (Functor.congr_obj he a), hy.trans (Functor.congr_obj he b),
    hg.trans (Functor.hcongr_hom he f)⟩

/-- **Morphisms of a filtered colimit in `Cat` come from a stage.** A morphism of the colimit
between the images of objects of stages `i` and `j` is, after passing to a common later stage
`k`, the image of a morphism of that stage. -/
lemma exists_stage_map_of_colimit
    {I : Type v} [Category.{w} I] [IsFiltered I]
    (F : I ⥤ Cat.{max u v w, max u v w}) [HasColimit F]
    [HasColimit (F ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
    (i j : I) (a : F.obj i) (b : F.obj j)
    (f : (colimit.ι F i).toFunctor.obj a ⟶ (colimit.ι F j).toFunctor.obj b) :
    ∃ (k : I) (s : i ⟶ k) (t : j ⟶ k)
      (g : (F.map s).toFunctor.obj a ⟶ (F.map t).toFunctor.obj b),
      HEq ((colimit.ι F k).toFunctor.map g) f := by
  obtain ⟨r, x, y, g, hx, hy, hg⟩ := isStageMorphism.{u, v, w} F f
  obtain ⟨k, s, t, e⟩ := exists_common_stage_eq_of_colimit_ι_obj_eq.{u, v, w} F a x hx.symm
  have ht := congrArg Cat.Hom.toFunctor (colimit.w F t)
  obtain ⟨l, m, n, e'⟩ := exists_common_stage_eq_of_colimit_ι_obj_eq.{u, v, w} F
    ((F.map t).toFunctor.obj y) b ((Functor.congr_obj ht y).trans hy)
  have hcomp := congrArg Cat.Hom.toFunctor (F.map_comp s m)
  let g' := eqToHom (Functor.congr_obj hcomp a) ≫
    (F.map m).toFunctor.map (eqToHom e ≫ (F.map t).toFunctor.map g) ≫ eqToHom e'
  refine ⟨l, s ≫ m, n, g', ?_⟩
  dsimp only [g']
  simp only [Functor.map_comp, eqToHom_map,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact (Functor.hcongr_hom (congrArg Cat.Hom.toFunctor (colimit.w F m))
    ((F.map t).toFunctor.map g)).trans ((Functor.hcongr_hom ht g).trans hg)

/-- A functor carries a heterogeneous equality of morphisms to one of their images. -/
lemma map_heq_of_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {a b a' b' : C} (ha : a = a') (hb : b = b')
    {f : a ⟶ b} {g : a' ⟶ b'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst a' b'
  cases h
  rfl

/-- Two heterogeneously equal morphisms are related by the `eqToHom`s of the equalities of
their sources and targets. -/
lemma transport_hom_of_heq {C : Type*} [Category C]
    {a b a' b' : C} (ha : a = a') (hb : b = b')
    {f : a ⟶ b} {g : a' ⟶ b'} (h : HEq f g) :
    f ≫ eqToHom hb = eqToHom ha ≫ g := by
  subst a' b'
  cases h
  simp

end CategoryTheory.Cat

end
