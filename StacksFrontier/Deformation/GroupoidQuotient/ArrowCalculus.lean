module

public import StacksFrontier.Deformation.Groupoid.HomInverse
public import StacksFrontier.Deformation.GroupoidQuotient.MinimalAutoequivalence

/-!
# Calculus of arrows in a groupoid in functors

Elementwise rules for the arrows of a groupoid in functors `(U, R, s, t, c)` on a category `C`:
source and target of a composite, naturality of composition and of inverses, the unit and
inverse laws, and the behaviour of a morphism of groupoids in functors on inverses. Then the
three consequences of an equivalence on quotients that are used to compare two groupoids in
functors presenting the same category: arrows between images of objects lift (fullness), arrows
with the same source, target and image agree (faithfulness), and every object is the target of
an arrow out of an image (essential surjectivity).

## Main results

* `Deformation.GroupoidInFunctors.compose_source_eq`, `compose_target_eq`,
  `arrows_map_compose`, `compose_inverseArrow`, `compose_identity_eq`, `inverseArrow_natural`,
  `eq_inverseArrow_of_compose_eq_identity`.
* `Deformation.GroupoidInFunctors.Hom.exists_arrow_of_full`,
  `Deformation.GroupoidInFunctors.Hom.eq_of_faithful`,
  `Deformation.GroupoidInFunctors.Hom.exists_arrow_of_essSurj`.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Deformation

namespace GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

/-- The source of a composite is the source of its second factor. -/
public theorem compose_source_eq (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (a b : G.arrows.obj T) (h : G.source.app T a = G.target.app T b) :
    G.source.app T (G.compose T a b h) = G.source.app T b :=
  (G.pointwiseData T).source_comp a b h

/-- The target of a composite is the target of its first factor. -/
public theorem compose_target_eq (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (a b : G.arrows.obj T) (h : G.source.app T a = G.target.app T b) :
    G.target.app T (G.compose T a b h) = G.target.app T a :=
  (G.pointwiseData T).target_comp a b h

/-- Composition commutes with transport along morphisms of the base. -/
public alias arrows_map_compose := Deformation.compose_natural

/-- Composition depends only on the two arrows. -/
public theorem compose_congr' (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    {a a' b b' : G.arrows.obj T} (ha : a = a') (hb : b = b')
    (h : G.source.app T a = G.target.app T b) (h' : G.source.app T a' = G.target.app T b') :
    G.compose T a b h = G.compose T a' b' h' := by
  subst ha hb
  rfl

/-- The identity arrow of an object has that object as source. -/
public theorem identity_source_eq (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (x : G.objects.obj T) : G.source.app T (G.identity T x) = x :=
  (G.evaluationArrowEquiv T x x (𝟙 (show G.Evaluation T from x))).2.1

/-- The identity arrow of an object has that object as target. -/
public theorem identity_target_eq (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (x : G.objects.obj T) : G.target.app T (G.identity T x) = x :=
  (G.evaluationArrowEquiv T x x (𝟙 (show G.Evaluation T from x))).2.2

/-- An arrow with source `x` and target `y` is represented by a morphism `x ⟶ y` of the
evaluated groupoid. -/
private theorem exists_evaluation_hom (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (a : G.arrows.obj T) (x y : G.Evaluation T) (hs : G.source.app T a = x)
    (ht : G.target.app T a = y) : ∃ α : x ⟶ y, (G.evaluationArrowEquiv T x y α).1 = a :=
  ⟨(G.evaluationArrowEquiv T x y).symm ⟨a, hs, ht⟩, by rw [Equiv.apply_symm_apply]⟩

/-- **The inverse law.** An arrow composed with its inverse is the identity of its target. -/
public theorem compose_inverseArrow (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (a : G.arrows.obj T) (h : G.source.app T a = G.target.app T (inverseArrow G T a)) :
    G.compose T a (inverseArrow G T a) h = G.identity T (G.target.app T a) := by
  let α := (G.evaluationArrowEquiv T (G.source.app T a) (G.target.app T a)).symm ⟨a, rfl, rfl⟩
  have hα : (G.evaluationArrowEquiv T _ _ α).1 = a := by rw [Equiv.apply_symm_apply]
  have hc := G.evaluationArrowEquiv_comp T (Groupoid.inv α) α
  rw [Groupoid.inv_comp, G.evaluationArrowEquiv_id] at hc
  rw [hc]
  exact G.compose_congr' T hα.symm rfl _ _

/-- **The unit law.** An arrow composed with the identity of its source is itself. -/
public theorem compose_identity_eq (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (a : G.arrows.obj T)
    (h : G.source.app T a = G.target.app T (G.identity T (G.source.app T a))) :
    G.compose T a (G.identity T (G.source.app T a)) h = a := by
  obtain ⟨α, hα⟩ := G.exists_evaluation_hom T a _ _ rfl rfl
  have hc := G.evaluationArrowEquiv_comp T (𝟙 _) α
  rw [Category.id_comp] at hc
  exact (G.compose_congr' T hα.symm (G.evaluationArrowEquiv_id T _).symm _ _).trans
    (hc.symm.trans hα)

/-- **Inverses are unique.** An arrow `c` from the target of `b` to its source with
`b ∘ c` the identity is the inverse of `b`. -/
public theorem eq_inverseArrow_of_compose_eq_identity (G : GroupoidInFunctors.{u, v, w} C)
    (T : C) (b c : G.arrows.obj T) (hcs : G.source.app T c = G.target.app T b)
    (hct : G.target.app T c = G.source.app T b)
    (h : G.source.app T b = G.target.app T c)
    (hbc : G.compose T b c h = G.identity T (G.target.app T b)) :
    c = inverseArrow G T b := by
  let β := (G.evaluationArrowEquiv T (G.source.app T b) (G.target.app T b)).symm ⟨b, rfl, rfl⟩
  have hβ : (G.evaluationArrowEquiv T _ _ β).1 = b := by rw [Equiv.apply_symm_apply]
  obtain ⟨γ, hγ⟩ := G.exists_evaluation_hom T c _ _ hcs hct
  have hcomp : γ ≫ β = 𝟙 _ := by
    refine (G.evaluationArrowEquiv T _ _).injective (Subtype.ext ?_)
    rw [G.evaluationArrowEquiv_comp, G.evaluationArrowEquiv_id, G.compose_congr' T hβ hγ _ h, hbc]
  rw [← hγ, IsIso.eq_inv_of_inv_hom_id hcomp, ← Groupoid.inv_eq_inv]
  rfl

/-- Inverses commute with transport along morphisms of the base. -/
public alias inverseArrow_natural := Deformation.evalMap_inverse

/-- **Arrows between images lift** along a morphism of groupoids in functors whose evaluation is
full. -/
public theorem Hom.exists_arrow_of_full {G H : GroupoidInFunctors.{u, v, w} C} (F : Hom G H)
    (T : C) [(F.evaluation T).Full] (x y : G.objects.obj T) (b : H.arrows.obj T)
    (hs : H.source.app T b = F.mapObjects.app T x)
    (ht : H.target.app T b = F.mapObjects.app T y) :
    ∃ a : G.arrows.obj T, G.source.app T a = x ∧ G.target.app T a = y ∧
      F.mapArrows.app T a = b := by
  obtain ⟨β, hβ⟩ := H.exists_evaluation_hom T b ((F.evaluation T).obj x) ((F.evaluation T).obj y)
    hs ht
  obtain ⟨α, hα⟩ := (F.evaluation T).map_surjective β
  refine ⟨(G.evaluationArrowEquiv T x y α).1, (G.evaluationArrowEquiv T x y α).2.1,
    (G.evaluationArrowEquiv T x y α).2.2, ?_⟩
  rw [← Hom.evaluation_map_arrow, hα, hβ]

/-- **Arrows are determined by their endpoints and image** along a morphism of groupoids in
functors whose evaluation is faithful. -/
public theorem Hom.eq_of_faithful {G H : GroupoidInFunctors.{u, v, w} C} (F : Hom G H)
    (T : C) [(F.evaluation T).Faithful] (a a' : G.arrows.obj T)
    (hs : G.source.app T a = G.source.app T a') (ht : G.target.app T a = G.target.app T a')
    (h : F.mapArrows.app T a = F.mapArrows.app T a') : a = a' := by
  obtain ⟨α, hα⟩ := G.exists_evaluation_hom T a _ _ rfl rfl
  obtain ⟨α', hα'⟩ := G.exists_evaluation_hom T a' _ _ hs.symm ht.symm
  have hmap : (F.evaluation T).map α = (F.evaluation T).map α' := by
    refine (H.evaluationArrowEquiv T _ _).injective (Subtype.ext ?_)
    rw [Hom.evaluation_map_arrow, Hom.evaluation_map_arrow, hα, hα', h]
  rw [← hα, ← hα', (F.evaluation T).map_injective hmap]

/-- **Every object is the target of an arrow out of an image** along a morphism of groupoids in
functors whose functor on quotients is essentially surjective. -/
public theorem Hom.exists_arrow_of_essSurj {G H : GroupoidInFunctors.{u, v, w} C}
    (F : Hom G H) [(quotientMap F).EssSurj] (T : C) (z : H.objects.obj T) :
    ∃ (x : G.objects.obj T) (c : H.arrows.obj T),
      H.source.app T c = F.mapObjects.app T x ∧ H.target.app T c = z := by
  obtain ⟨X, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := quotientMap F)
    (⟨T, z⟩ : Grothendieck (evaluationFunctor H))
  let β : X.base ⟶ T := i.hom.base
  let φ : (show H.Evaluation T from H.objects.map β (F.mapObjects.app X.base X.fiber)) ⟶
      (show H.Evaluation T from z) := i.hom.fiber
  refine ⟨G.objects.map β X.fiber, (H.evaluationArrowEquiv T _ _ φ).1, ?_,
    (H.evaluationArrowEquiv T _ _ φ).2.2⟩
  rw [(H.evaluationArrowEquiv T _ _ φ).2.1]
  exact (NatTrans.naturality_apply F.mapObjects β X.fiber).symm

end GroupoidInFunctors

end Deformation

end
