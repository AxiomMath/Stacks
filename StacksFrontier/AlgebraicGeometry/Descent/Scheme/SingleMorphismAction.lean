module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphism

/-!
# Descent data relative to one morphism, read on generalized points

Let `f : X ⟶ S` be a morphism of schemes and let `V` be a scheme over `X`.  A candidate gluing
map for `V` is a morphism `φ : V ×_S X ⟶ X ×_S V` of schemes over `S`, the fibre products
being binary products in `Over S`.  Such a `φ` is the same thing as an operation which takes a
generalized point `v` of `V` and a generalized point `x` of `X` over the same test object and
returns a new generalized point of `V`, lying over `x`.  This file introduces that operation
and translates the three conditions a descent datum imposes — that `φ` lie over `X ×_S X`, the
cocycle condition on `X ×_S X ×_S X`, and the compatibility condition on a morphism of descent
data — into conditions on it.

## Main definitions

* `AlgebraicGeometry.gluingAction` is the operation determined by a candidate gluing map.
* `AlgebraicGeometry.DescentDatum.act` is the operation of the gluing isomorphism of a descent
  datum relative to a single morphism.

## Main results

* `AlgebraicGeometry.cocycle_iff_gluingAction_act_act`: **for a candidate gluing map lying over
  `X ×_S X`, the cocycle condition says exactly that acting twice is acting once**, that is
  that `(v · x) · y = v · y`.
* `AlgebraicGeometry.DescentDatum.act_act` and `AlgebraicGeometry.DescentDatum.act_self` are
  the two laws the action of a descent datum obeys; the second is the normalization along the
  diagonal.
* `AlgebraicGeometry.DescentDatum.hom_comm_iff`: a morphism of `X`-schemes commutes with two
  gluing isomorphisms exactly when it is equivariant for the two actions.
* `AlgebraicGeometry.DescentDatum.transition_hom_left_eq`: a gluing isomorphism is recovered
  from its action.

## References

* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Limits

/-- The universal generalized point of a left-associated triple product is the identity: the
pair of its three projections, assembled in the same shape, is the identity morphism. -/
lemma prodLift_triple_eq_id {C : Type*} [Category C] [HasBinaryProducts C] (A B D : C) :
    prod.lift (prod.lift ((prod.fst : (A ⨯ B) ⨯ D ⟶ A ⨯ B) ≫ prod.fst)
        ((prod.fst : (A ⨯ B) ⨯ D ⟶ A ⨯ B) ≫ prod.snd)) prod.snd = 𝟙 ((A ⨯ B) ⨯ D) := by
  refine prod.hom_ext ?_ ?_
  · refine prod.hom_ext ?_ ?_ <;> simp
  · simp

end CategoryTheory.Limits

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- The action of a generalized point `x` of `X` on a generalized point `v` of `V`, determined
by a candidate gluing map `φ : V ×_S X ⟶ X ×_S V`: the `V`-component of `φ (v, x)`. -/
def gluingAction (V : Over X)
    (φ : (Over.map f).obj V ⨯ Over.mk f ⟶ Over.mk f ⨯ (Over.map f).obj V)
    {T : Over S} (v : T ⟶ (Over.map f).obj V) (x : T ⟶ Over.mk f) :
    T ⟶ (Over.map f).obj V :=
  prod.lift v x ≫ φ ≫ prod.snd

variable (V : Over X)
  (φ : (Over.map f).obj V ⨯ Over.mk f ⟶ Over.mk f ⨯ (Over.map f).obj V)

/-- The action commutes with change of test object. -/
@[simp]
lemma comp_gluingAction {T U : Over S} (k : U ⟶ T)
    (v : T ⟶ (Over.map f).obj V) (x : T ⟶ Over.mk f) :
    k ≫ gluingAction V φ v x = gluingAction V φ (k ≫ v) (k ≫ x) := by
  simp only [gluingAction, ← Category.assoc, prod.comp_lift]

/-- The point produced by the action lies over the acting point of `X`. -/
lemma gluingAction_comp_structureMap
    (h2 : φ ≫ prod.snd ≫ structureMap f V = prod.snd)
    {T : Over S} (v : T ⟶ (Over.map f).obj V) (x : T ⟶ Over.mk f) :
    gluingAction V φ v x ≫ structureMap f V = x := by
  simp only [gluingAction, Category.assoc]
  rw [h2, prod.lift_snd]

/-- The `X ×_S X`-component of `φ (v, x)` is the point of `X` under `v`. -/
lemma gluingAction_prodLift_comp_fst (h1 : φ ≫ prod.fst = prod.fst ≫ structureMap f V)
    {T : Over S} (v : T ⟶ (Over.map f).obj V) (x : T ⟶ Over.mk f) :
    prod.lift v x ≫ φ ≫ prod.fst = v ≫ structureMap f V := by
  rw [h1, ← Category.assoc, prod.lift_fst]

/-- A candidate gluing map lying over `X ×_S X` is recovered from its action. -/
lemma gluingAction_eq_lift (h1 : φ ≫ prod.fst = prod.fst ≫ structureMap f V) :
    φ = prod.lift (prod.fst ≫ structureMap f V) (gluingAction V φ prod.fst prod.snd) := by
  apply prod.hom_ext
  · rw [prod.lift_fst, h1]
  · rw [prod.lift_snd, gluingAction, prod.lift_fst_snd, Category.id_comp]

section Cocycle

variable {T : Over S} (v : T ⟶ (Over.map f).obj V) (x y : T ⟶ Over.mk f)

/-- The `V`-component of the left-hand side of the cocycle diagram, at a generalized point of
`(V ×_S X) ×_S X`, is the result of acting twice. -/
lemma gluingAction_cocycleLhs_snd :
    prod.lift (prod.lift v x) y ≫ prod.map φ (𝟙 (Over.mk f)) ≫ prodMapLastTwo φ ≫ prod.snd =
      gluingAction V φ (gluingAction V φ v x) y := by
  simp only [prodMapLastTwo, prod.associator_hom, prod.associator_inv]
  simp [gluingAction, prod.comp_lift, prod.comp_lift_assoc, ← prod.lift_fst_comp_snd_comp]

/-- The `V`-component of the right-hand side of the cocycle diagram, at a generalized point of
`(V ×_S X) ×_S X`, is the result of acting once, by the third coordinate. -/
lemma gluingAction_cocycleRhs_snd :
    prod.lift (prod.lift v x) y ≫ prodMapFirstThird φ ≫ prod.snd = gluingAction V φ v y := by
  simp only [prodMapFirstThird, prodMapLastTwo, prod.associator_hom, prod.associator_inv,
    prod.braiding_hom]
  simp [gluingAction, prod.comp_lift, prod.comp_lift_assoc, ← prod.lift_fst_comp_snd_comp]

/-- The `X ×_S X`-component of the left-hand side of the cocycle diagram, at a generalized
point `((v, x), y)` of `(V ×_S X) ×_S X`, is the pair of the point of `X` under `v` and `x`. -/
lemma gluingAction_cocycleLhs_fst (h1 : φ ≫ prod.fst = prod.fst ≫ structureMap f V)
    (h2 : φ ≫ prod.snd ≫ structureMap f V = prod.snd) :
    prod.lift (prod.lift v x) y ≫ prod.map φ (𝟙 (Over.mk f)) ≫ prodMapLastTwo φ ≫ prod.fst =
      prod.lift (v ≫ structureMap f V) x := by
  simp only [prodMapLastTwo, prod.associator_hom, prod.associator_inv]
  apply prod.hom_ext
  · simp [prod.comp_lift, ← prod.lift_fst_comp_snd_comp, h1]
  · simp [prod.comp_lift, ← prod.lift_fst_comp_snd_comp, h1, h2]

/-- The `X ×_S X`-component of the right-hand side of the cocycle diagram, at a generalized
point `((v, x), y)` of `(V ×_S X) ×_S X`, is the pair of the point of `X` under `v` and `x`. -/
lemma gluingAction_cocycleRhs_fst (h1 : φ ≫ prod.fst = prod.fst ≫ structureMap f V) :
    prod.lift (prod.lift v x) y ≫ prodMapFirstThird φ ≫ prod.fst =
      prod.lift (v ≫ structureMap f V) x := by
  simp only [prodMapFirstThird, prodMapLastTwo, prod.associator_hom, prod.associator_inv,
    prod.braiding_hom]
  apply prod.hom_ext
  · simp [prod.comp_lift, ← prod.lift_fst_comp_snd_comp, h1]
  · simp [prod.comp_lift, ← prod.lift_fst_comp_snd_comp]

end Cocycle

/-- **The cocycle condition is the law that acting twice is acting once.**  For a candidate
gluing map lying over `X ×_S X`, the cocycle condition on `X ×_S X ×_S X` holds if and only if
`(v · x) · y = v · y` for all generalized points. -/
lemma cocycle_iff_gluingAction_act_act
    (h1 : φ ≫ prod.fst = prod.fst ≫ structureMap f V)
    (h2 : φ ≫ prod.snd ≫ structureMap f V = prod.snd) :
    prod.map φ (𝟙 (Over.mk f)) ≫ prodMapLastTwo φ = prodMapFirstThird φ ↔
      ∀ {T : Over S} (v : T ⟶ (Over.map f).obj V) (x y : T ⟶ Over.mk f),
        gluingAction V φ (gluingAction V φ v x) y = gluingAction V φ v y := by
  constructor
  · intro hc T v x y
    have h := congrArg (fun t ↦ prod.lift (prod.lift v x) y ≫ t ≫
      (prod.snd : _ ⟶ (Over.map f).obj V)) hc
    simp only [prodMapLastTwo, prodMapFirstThird, prod.associator_hom, prod.associator_inv,
      prod.braiding_hom] at h
    simpa [gluingAction, prod.comp_lift, prod.comp_lift_assoc,
      ← prod.lift_fst_comp_snd_comp] using h
  · intro ha
    rw [← Category.id_comp (prod.map φ (𝟙 (Over.mk f)) ≫ prodMapLastTwo φ),
      ← Category.id_comp (prodMapFirstThird φ), ← prodLift_triple_eq_id]
    refine prod.hom_ext ?_ ?_
    · simpa only [Category.assoc] using (gluingAction_cocycleLhs_fst V φ _ _ _ h1 h2).trans
        (gluingAction_cocycleRhs_fst V φ _ _ _ h1).symm
    · simpa only [Category.assoc, ha] using (gluingAction_cocycleLhs_snd V φ _ _ _).trans
        ((ha _ _ _).trans (gluingAction_cocycleRhs_snd V φ _ _ _).symm)

namespace DescentDatum

/-- The action of a generalized point of `X` on a generalized point of the scheme underlying a
descent datum: the `V`-component of `φ (v, x)`. -/
def act (D : DescentDatum f) {T : Over S} (v : T ⟶ (Over.map f).obj D.over)
    (x : T ⟶ Over.mk f) : T ⟶ (Over.map f).obj D.over :=
  gluingAction D.over D.transition.hom.left v x

variable (D : DescentDatum f)

/-- The gluing isomorphism of a descent datum lies over the first factor of `X ×_S X`. -/
lemma transition_hom_left_comp_fst :
    D.transition.hom.left ≫ prod.fst = prod.fst ≫ structureMap f D.over :=
  D.gluing_hom_fst () ()

/-- The gluing isomorphism of a descent datum lies over the second factor of `X ×_S X`. -/
lemma transition_hom_left_comp_snd_structureMap :
    D.transition.hom.left ≫ prod.snd ≫ structureMap f D.over = prod.snd :=
  D.gluing_hom_snd_structureMap () ()

/-- The action commutes with change of test object. -/
@[simp]
lemma comp_act {T U : Over S} (k : U ⟶ T) (v : T ⟶ (Over.map f).obj D.over)
    (x : T ⟶ Over.mk f) : k ≫ D.act v x = D.act (k ≫ v) (k ≫ x) :=
  comp_gluingAction D.over D.transition.hom.left k v x

/-- The point produced by the action lies over the acting point of `X`. -/
@[simp]
lemma act_comp_structureMap {T : Over S} (v : T ⟶ (Over.map f).obj D.over)
    (x : T ⟶ Over.mk f) : D.act v x ≫ structureMap f D.over = x :=
  gluingAction_comp_structureMap D.over D.transition.hom.left
    D.transition_hom_left_comp_snd_structureMap v x

/-- The gluing isomorphism of a descent datum is recovered from its action. -/
lemma transition_hom_left_eq :
    D.transition.hom.left =
      prod.lift (prod.fst ≫ structureMap f D.over) (D.act prod.fst prod.snd) :=
  gluingAction_eq_lift D.over D.transition.hom.left D.transition_hom_left_comp_fst

/-- **Acting twice is acting once.**  This is the cocycle condition of a descent datum, read on
generalized points. -/
lemma act_act {T : Over S} (v : T ⟶ (Over.map f).obj D.over) (x y : T ⟶ Over.mk f) :
    D.act (D.act v x) y = D.act v y :=
  (cocycle_iff_gluingAction_act_act D.over D.transition.hom.left
    D.transition_hom_left_comp_fst D.transition_hom_left_comp_snd_structureMap).mp
    D.cocycle_triangle v x y

/-- **A point of `V` is fixed by the point of `X` it lies over.**  This is the normalization of
the gluing isomorphism along the diagonal. -/
lemma act_self {T : Over S} (v : T ⟶ (Over.map f).obj D.over) :
    D.act v (v ≫ structureMap f D.over) = v := by
  have hdiag : D.act (𝟙 ((Over.map f).obj D.over)) (structureMap f D.over) =
      𝟙 ((Over.map f).obj D.over) := D.diagHom_eq_id
  calc D.act v (v ≫ structureMap f D.over)
      = v ≫ D.act (𝟙 ((Over.map f).obj D.over)) (structureMap f D.over) := by
        rw [comp_act, Category.comp_id]
    _ = v := by rw [hdiag, Category.comp_id]

/-- **A morphism of `X`-schemes commutes with two gluing isomorphisms exactly when it is
equivariant.**  This is the compatibility condition of a morphism of descent data, read on
generalized points. -/
lemma hom_comm_iff (D E : DescentDatum f) (h : D.over ⟶ E.over) :
    prod.map ((Over.map f).map h) (𝟙 (Over.mk f)) ≫ E.transition.hom.left =
        D.transition.hom.left ≫ prod.map (𝟙 (Over.mk f)) ((Over.map f).map h) ↔
      ∀ {T : Over S} (v : T ⟶ (Over.map f).obj D.over) (x : T ⟶ Over.mk f),
        D.act v x ≫ (Over.map f).map h = E.act (v ≫ (Over.map f).map h) x := by
  have hmap : (Over.map f).map h ≫ structureMap f E.over = structureMap f D.over :=
    Over.OverMorphism.ext (Over.w h)
  have key1 : ∀ {T : Over S} (v : T ⟶ (Over.map f).obj D.over) (x : T ⟶ Over.mk f),
      prod.lift v x ≫ (prod.map ((Over.map f).map h) (𝟙 (Over.mk f)) ≫
          E.transition.hom.left) ≫ prod.snd = E.act (v ≫ (Over.map f).map h) x := by
    intro T v x
    simp only [act, gluingAction, Category.assoc, ← Category.assoc (prod.lift v x),
      prod.lift_map, Category.comp_id]
  have key2 : ∀ {T : Over S} (v : T ⟶ (Over.map f).obj D.over) (x : T ⟶ Over.mk f),
      prod.lift v x ≫ (D.transition.hom.left ≫
          prod.map (𝟙 (Over.mk f)) ((Over.map f).map h)) ≫ prod.snd =
        D.act v x ≫ (Over.map f).map h := by
    intro T v x
    simp only [act, gluingAction, Category.assoc, prod.map_snd]
  constructor
  · intro hc T v x
    rw [← key1, ← key2, hc]
  · intro ha
    have hu := prod.lift_fst_snd (X := (Over.map f).obj D.over) (Y := Over.mk f)
    have hL := key1 (prod.fst : (Over.map f).obj D.over ⨯ Over.mk f ⟶ _) prod.snd
    have hR := key2 (prod.fst : (Over.map f).obj D.over ⨯ Over.mk f ⟶ _) prod.snd
    rw [hu, Category.id_comp] at hL hR
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, E.transition_hom_left_comp_fst, prod.map_fst_assoc, hmap,
        Category.assoc, prod.map_fst, Category.comp_id, D.transition_hom_left_comp_fst]
    · rw [hL, hR, ha]

end DescentDatum

end AlgebraicGeometry

end

end
