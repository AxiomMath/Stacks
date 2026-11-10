module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.GluingAction

/-!
# Comparing two base changes of a descent datum

Let `D` be a descent datum for `a : X ⟶ S` with underlying object `V` over `X`, and let
`f₀, f₁ : X' ⟶ X` satisfy `f₀ ≫ a = f₁ ≫ a`. The gluing action of `D` carries a point of `V`
over `f₀` to a point of `V` over `f₁`, hence gives a morphism `f₀^* V ⟶ f₁^* V` over `X'`.
The cocycle condition makes these morphisms compose, so each is an isomorphism, and they are
natural in `D`.

## Main definitions

* `AlgebraicGeometry.DescentData.baseChangeMap` is the comparison morphism, and
  `AlgebraicGeometry.DescentData.baseChangeIso` the isomorphism it defines.
* `AlgebraicGeometry.DescentData.baseChangeSourceMap` is the map `f₀^* V ⟶ V ×_S X` sending
  `(v, x')` to `(v, f₁ x')`.

## Main results

* `AlgebraicGeometry.DescentData.baseChangeMap_comp` and
  `AlgebraicGeometry.DescentData.baseChangeMap_self` are the composition and identity laws.
* `AlgebraicGeometry.DescentData.baseChangeMap_naturality` is naturality in the datum.

## References

* [Stacks Project, Tag 023Y](https://stacks.math.columbia.edu/tag/023Y)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.DescentData

open CategoryTheory Limits

section PullbackMap

variable {X X' : Scheme.{u}} (f : X' ⟶ X)

/-- For `v : V ⟶ W` over `X`, the base change `f^* v` followed by the first projection of
`f^* W` equals the first projection of `f^* V` followed by `v`. -/
@[reassoc]
lemma pullbackMap_left_fst {V W : Over X} (v : V ⟶ W) :
    ((Over.pullback f).map v).left ≫ pullback.fst W.hom f =
      pullback.fst V.hom f ≫ v.left := by
  simp [Over.pullback_map_left]

/-- For `v : V ⟶ W` over `X`, the base change `f^* v` commutes with the second projections
of `f^* V` and `f^* W` to `X'`. -/
@[reassoc]
lemma pullbackMap_left_snd {V W : Over X} (v : V ⟶ W) :
    ((Over.pullback f).map v).left ≫ pullback.snd W.hom f = pullback.snd V.hom f := by
  simp [Over.pullback_map_left]

end PullbackMap

variable {S X X' : Scheme.{u}} {a : X ⟶ S} (D : DescentData (fun _ : Unit ↦ a))
  (f₀ f₁ : X' ⟶ X) (hf : f₀ ≫ a = f₁ ≫ a)

include hf in
/-- The points `v` of `V` and `f₁ x'` of `X` attached to a point `(v, x')` of `f₀^* V` have
the same image in `S`. -/
lemma baseChangeAct_cond :
    pullback.fst (D.obj ()).hom f₀ ≫ (D.obj ()).hom ≫ a =
      (pullback.snd (D.obj ()).hom f₀ ≫ f₁) ≫ a := by
  rw [← Category.assoc, pullback.condition, Category.assoc, hf, Category.assoc]

/-- The map from `f₀^* V` to `V ×_S X` sending a point `(v, x')` to `(v, f₁ x')`. -/
def baseChangeSourceMap : pullback (D.obj ()).hom f₀ ⟶ pullback ((D.obj ()).hom ≫ a) a :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ f₁) (D.baseChangeAct_cond f₀ f₁ hf)

/-- The first component of `baseChangeSourceMap` is the projection `f₀^* V ⟶ V`. -/
@[reassoc]
lemma baseChangeSourceMap_fst :
    D.baseChangeSourceMap f₀ f₁ hf ≫ pullback.fst ((D.obj ()).hom ≫ a) a =
      pullback.fst (D.obj ()).hom f₀ :=
  pullback.lift_fst _ _ _

/-- The second component of `baseChangeSourceMap` is the projection `f₀^* V ⟶ X'` followed
by `f₁`. -/
@[reassoc]
lemma baseChangeSourceMap_snd :
    D.baseChangeSourceMap f₀ f₁ hf ≫ pullback.snd ((D.obj ()).hom ≫ a) a =
      pullback.snd (D.obj ()).hom f₀ ≫ f₁ :=
  pullback.lift_snd _ _ _

/-- The gluing action of `D` applied to the tautological point of `f₀^* V`, producing a point
of `V` over `f₁`. -/
def baseChangeAct : pullback (D.obj ()).hom f₀ ⟶ (D.obj ()).left :=
  D.act (pullback.fst (D.obj ()).hom f₀) (pullback.snd (D.obj ()).hom f₀ ≫ f₁)
    (D.baseChangeAct_cond f₀ f₁ hf)

/-- `baseChangeAct` is `baseChangeSourceMap` followed by the gluing action `actOn`. -/
lemma baseChangeAct_eq :
    D.baseChangeAct f₀ f₁ hf = D.baseChangeSourceMap f₀ f₁ hf ≫ D.actOn := rfl

/-- The point `baseChangeAct` of `V` lies over `f₁ x'`. -/
@[reassoc]
lemma baseChangeAct_hom :
    D.baseChangeAct f₀ f₁ hf ≫ (D.obj ()).hom = pullback.snd (D.obj ()).hom f₀ ≫ f₁ :=
  D.act_hom _ _ _

/-- The comparison morphism `f₀^* V ⟶ f₁^* V` over `X'`. -/
def baseChangeMap :
    (Over.pullback f₀).obj (D.obj ()) ⟶ (Over.pullback f₁).obj (D.obj ()) :=
  Over.homMk (pullback.lift (D.baseChangeAct f₀ f₁ hf) (pullback.snd (D.obj ()).hom f₀)
    (D.baseChangeAct_hom f₀ f₁ hf)) (pullback.lift_snd _ _ _)

/-- The first component of `baseChangeMap` is `baseChangeAct`. -/
@[reassoc]
lemma baseChangeMap_left_fst :
    (D.baseChangeMap f₀ f₁ hf).left ≫ pullback.fst (D.obj ()).hom f₁ =
      D.baseChangeAct f₀ f₁ hf :=
  pullback.lift_fst _ _ _

/-- The second component of `baseChangeMap` is the projection `f₀^* V ⟶ X'`. -/
@[reassoc]
lemma baseChangeMap_left_snd :
    (D.baseChangeMap f₀ f₁ hf).left ≫ pullback.snd (D.obj ()).hom f₁ =
      pullback.snd (D.obj ()).hom f₀ :=
  pullback.lift_snd _ _ _

/-- Two morphisms `f₀^* V ⟶ f₁^* W` over `X'` agree once their first projections agree. -/
private lemma pullback_over_hom_ext {f₀ f₁ : X' ⟶ X} {V W : Over X}
    {g h : (Over.pullback f₀).obj V ⟶ (Over.pullback f₁).obj W}
    (H : g.left ≫ pullback.fst W.hom f₁ = h.left ≫ pullback.fst W.hom f₁) : g = h :=
  Over.OverMorphism.ext (pullback.hom_ext H ((Over.w g).trans (Over.w h).symm))

/-- The comparison morphisms compose: `f₀^* V ⟶ f₁^* V ⟶ f₂^* V` is the comparison morphism
`f₀^* V ⟶ f₂^* V`. -/
lemma baseChangeMap_comp (f₂ : X' ⟶ X) (hf' : f₁ ≫ a = f₂ ≫ a) :
    D.baseChangeMap f₀ f₁ hf ≫ D.baseChangeMap f₁ f₂ hf' =
      D.baseChangeMap f₀ f₂ (hf.trans hf') := by
  refine pullback_over_hom_ext ?_
  · rw [Over.comp_left, Category.assoc, D.baseChangeMap_left_fst, D.baseChangeMap_left_fst,
      baseChangeAct, D.comp_act]
    refine (D.act_congr (D.baseChangeMap_left_fst f₀ f₁ hf) ?_).trans
      (D.act_act (pullback.fst (D.obj ()).hom f₀) (pullback.snd (D.obj ()).hom f₀ ≫ f₁)
        (pullback.snd (D.obj ()).hom f₀ ≫ f₂) (D.baseChangeAct_cond f₀ f₁ hf) ?_)
    · rw [← Category.assoc, D.baseChangeMap_left_snd]
    · simp only [Category.assoc, hf']

/-- The comparison morphism `f₀^* V ⟶ f₀^* V` is the identity. -/
lemma baseChangeMap_self : D.baseChangeMap f₀ f₀ rfl = 𝟙 _ := by
  refine pullback_over_hom_ext ?_
  · rw [D.baseChangeMap_left_fst, Over.id_left, Category.id_comp, baseChangeAct]
    exact (D.act_congr rfl pullback.condition.symm).trans
      (D.act_self (pullback.fst (D.obj ()).hom f₀))

/-- The comparison isomorphism `f₀^* V ≅ f₁^* V` over `X'`. -/
def baseChangeIso :
    (Over.pullback f₀).obj (D.obj ()) ≅ (Over.pullback f₁).obj (D.obj ()) where
  hom := D.baseChangeMap f₀ f₁ hf
  inv := D.baseChangeMap f₁ f₀ hf.symm
  hom_inv_id := by rw [D.baseChangeMap_comp, D.baseChangeMap_self]
  inv_hom_id := by rw [D.baseChangeMap_comp, D.baseChangeMap_self]

/-- The comparison morphism is natural in the descent datum: it commutes with the base
changes along `f₀` and `f₁` of a morphism `g : D ⟶ E` of descent data. -/
lemma baseChangeMap_naturality {D E : DescentData (fun _ : Unit ↦ a)} (g : D ⟶ E) :
    D.baseChangeMap f₀ f₁ hf ≫ (Over.pullback f₁).map (g.hom ()) =
      (Over.pullback f₀).map (g.hom ()) ≫ E.baseChangeMap f₀ f₁ hf := by
  refine pullback_over_hom_ext ?_
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc,
      pullbackMap_left_fst, D.baseChangeMap_left_fst_assoc, baseChangeAct,
      D.act_naturality, E.baseChangeMap_left_fst, baseChangeAct, E.comp_act]
    exact E.act_congr (by rw [pullbackMap_left_fst])
      (by rw [← Category.assoc, pullbackMap_left_snd])

end AlgebraicGeometry.DescentData
