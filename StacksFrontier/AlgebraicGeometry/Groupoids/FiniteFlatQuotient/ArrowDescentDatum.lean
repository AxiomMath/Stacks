module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphismAction
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.QuotientArrows

/-!
# The descent datum carried by the arrow scheme of a groupoid along a quotient of its objects

Let `G = (U, R, s, t, c)` be a groupoid scheme over `S`, let `q : U ⟶ Ū` be a morphism, and let
`K` be a system of quotient arrows for `q`, i.e. an identification of the kernel pair `U ×_Ū U`
with a subgroupoid of `R`.  Then the arrow scheme `R`, viewed as a scheme over `U ×_S U` through
`j = (t, s)`, carries a canonical descent datum relative to the morphism
`q × q : U ×_S U ⟶ Ū ×_S Ū`: its gluing isomorphism sends a pair consisting of an arrow `r` and
a point `(a, b)` of `U ×_S U` lying over the same point of `Ū ×_S Ū` to the twisted arrow
`[a, t r] ∘ r ∘ [s r, b]`.

That datum is the descent datum `φ` of the proof of the fourth conclusion of Tag 04S4, here
formed in the slice of schemes over `Ū ×_S Ū`.  The same twist, as a descent transport in the
slice of `Over S` over `Ū ×_S Ū` where the generalized points of the groupoid live, is
`AlgebraicGeometry.GroupoidQuotientArrows.arrowTransport`.

## Main definitions

* `AlgebraicGeometry.pairChart`, `AlgebraicGeometry.pairBase`, `AlgebraicGeometry.pairCover`
  and `AlgebraicGeometry.arrowsOverPair` name the four schemes and morphisms the descent is
  relative to.
* `AlgebraicGeometry.GroupoidQuotientArrows.act` is the gluing action on generalized points.
* `AlgebraicGeometry.GroupoidQuotientArrows.arrowsDescentDatum` is the descent datum.

## Main results

* `AlgebraicGeometry.GroupoidQuotientArrows.act_act` and
  `AlgebraicGeometry.GroupoidQuotientArrows.act_self`: the two laws of the action, which are the
  cocycle condition and the normalization of the gluing isomorphism.
* `AlgebraicGeometry.GroupoidQuotientArrows.arrowsDescentDatum_over`: the scheme the datum is
  carried by is the arrow scheme over `U ×_S U`.

## Implementation notes

The binary products of `AlgebraicGeometry.DescentData` are taken in the slice over the base of
the covering, here the scheme `Ū ×_S Ū`, whereas the groupoid lives in the slice over `S`.  A
generalized point over a test object `T` of the first slice is therefore transported to the
second by `AlgebraicGeometry.GroupoidQuotientArrows.pairTest`, which re-reads `T` as a scheme
over `S`; the two transports `arrowPt` and `basePt` are the identity on underlying schemes, so
every identity between transported points is an identity of morphisms of schemes and is proved
by `CategoryTheory.Over.OverMorphism.ext`.

The cocycle condition is not verified as a diagram on the triple product: the translation of
`AlgebraicGeometry.cocycle_iff_gluingAction_act_act` turns it into the law that acting twice is
acting once, which for the twist is
`AlgebraicGeometry.GroupoidQuotientArrows.twistHom_twistHom`.

## References

* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- The chart `U ×_S U` of the descent of the arrow scheme, as a scheme. -/
abbrev pairChart (G : GroupoidScheme S) : Scheme.{u} := (G.objects ⨯ G.objects : Over S).left

/-- The base `Ū ×_S Ū` of the descent of the arrow scheme, as a scheme. -/
abbrev pairBase (Ub : Over S) : Scheme.{u} := (Ub ⨯ Ub : Over S).left

/-- The covering morphism `U ×_S U ⟶ Ū ×_S Ū` of the descent of the arrow scheme. -/
abbrev pairCover {G : GroupoidScheme S} {Ub : Over S} (q : G.objects ⟶ Ub) :
    pairChart G ⟶ pairBase Ub := (prod.map q q).left

/-- The arrow scheme, as a scheme over `U ×_S U` through `j = (t, s)`. -/
abbrev arrowsOverPair (G : GroupoidScheme S) : Over (pairChart G) :=
  Over.mk (groupoidPreRelation G).left

namespace GroupoidQuotientArrows

variable {G : GroupoidScheme S} {Ub : Over S} (q : G.objects ⟶ Ub)

/-- A test scheme over `Ū ×_S Ū`, read as a scheme over `S`. -/
abbrev pairTest (Ub : Over S) (T : Over (pairBase Ub)) : Over S :=
  Over.mk (T.hom ≫ (Ub ⨯ Ub : Over S).hom)

/-- The scheme over `Ū ×_S Ū` whose descent datum is at issue: the arrow scheme, pushed from
the chart to the base. -/
abbrev arrowsOverBase : Over (pairBase Ub) :=
  (Over.map (pairCover q)).obj (arrowsOverPair G)

section Points

variable {T T' : Over (pairBase Ub)}

/-- The structure morphism of the arrow scheme, factored through the chart and the base. -/
lemma arrows_hom_eq : G.arrows.hom =
    (groupoidPreRelation G).left ≫ pairCover q ≫ (Ub ⨯ Ub : Over S).hom := by
  rw [Over.w (prod.map q q), Over.w (groupoidPreRelation G)]

/-- A morphism of test schemes over `Ū ×_S Ū`, read over `S`. -/
def pairTestMap (k : T' ⟶ T) : pairTest Ub T' ⟶ pairTest Ub T :=
  Over.homMk k.left (by
    change k.left ≫ T.hom ≫ (Ub ⨯ Ub : Over S).hom = T'.hom ≫ (Ub ⨯ Ub : Over S).hom
    rw [← Category.assoc, Over.w k])

/-- The morphism `pairTestMap k` has the same underlying morphism of schemes as `k`. -/
@[simp]
lemma pairTestMap_left (k : T' ⟶ T) : (pairTestMap k).left = k.left := rfl

/-- A generalized point of the arrow scheme over `Ū ×_S Ū`, read as one over `S`. -/
def arrowPt (v : T ⟶ arrowsOverBase q) : pairTest Ub T ⟶ G.arrows :=
  Over.homMk v.left (by
    have hv : v.left ≫ (groupoidPreRelation G).left ≫ pairCover q = T.hom := Over.w v
    calc v.left ≫ G.arrows.hom
        = (v.left ≫ (groupoidPreRelation G).left ≫ pairCover q) ≫
            (Ub ⨯ Ub : Over S).hom := by
          rw [arrows_hom_eq q]
          simp only [Category.assoc]
      _ = T.hom ≫ (Ub ⨯ Ub : Over S).hom := by rw [hv])

/-- A generalized point of the chart `U ×_S U`, read as one over `S`. -/
def basePt (x : T ⟶ Over.mk (pairCover q)) :
    pairTest Ub T ⟶ (G.objects ⨯ G.objects : Over S) :=
  Over.homMk x.left (by
    have hx : x.left ≫ pairCover q = T.hom := Over.w x
    calc x.left ≫ (G.objects ⨯ G.objects : Over S).hom
        = (x.left ≫ pairCover q) ≫ (Ub ⨯ Ub : Over S).hom := by
          rw [← Over.w (prod.map q q)]
          simp only [Category.assoc]
      _ = T.hom ≫ (Ub ⨯ Ub : Over S).hom := by rw [hx])

/-- The point `arrowPt q v` has the same underlying morphism of schemes as `v`. -/
@[simp]
lemma arrowPt_left (v : T ⟶ arrowsOverBase q) : (arrowPt q v).left = v.left := rfl

/-- The point `basePt q x` has the same underlying morphism of schemes as `x`. -/
@[simp]
lemma basePt_left (x : T ⟶ Over.mk (pairCover q)) : (basePt q x).left = x.left := rfl

/-- Reading a point of the arrow scheme over `S` is injective. -/
private lemma arrowPt_injective :
    Function.Injective (arrowPt q : (T ⟶ arrowsOverBase q) → (pairTest Ub T ⟶ G.arrows)) :=
  fun _ _ h => Over.OverMorphism.ext (congrArg (·.left) h)

/-- Reading a point of the arrow scheme over `S` commutes with precomposition. -/
lemma arrowPt_comp (k : T' ⟶ T) (v : T ⟶ arrowsOverBase q) :
    arrowPt q (k ≫ v) = pairTestMap k ≫ arrowPt q v :=
  Over.OverMorphism.ext (by simp only [arrowPt_left, Over.comp_left, pairTestMap_left])

/-- Reading a point of the chart `U ×_S U` over `S` commutes with precomposition. -/
lemma basePt_comp (k : T' ⟶ T) (x : T ⟶ Over.mk (pairCover q)) :
    basePt q (k ≫ x) = pairTestMap k ≫ basePt q x :=
  Over.OverMorphism.ext (by simp only [basePt_left, Over.comp_left, pairTestMap_left])

/-- A point of the arrow scheme and the point of the chart it lies over. -/
lemma basePt_structureMap (v : T ⟶ arrowsOverBase q) :
    basePt q (v ≫ structureMap (pairCover q) (arrowsOverPair G)) =
      arrowPt q v ≫ groupoidPreRelation G :=
  Over.OverMorphism.ext rfl

/-- The two points of `U ×_S U` recorded by a pair of generalized points lie over the same
points of `Ū` as the target and the source of the arrow. -/
lemma pair_compat (v : T ⟶ arrowsOverBase q) (x : T ⟶ Over.mk (pairCover q)) :
    arrowPt q v ≫ groupoidPreRelation G ≫ prod.map q q = basePt q x ≫ prod.map q q := by
  refine Over.OverMorphism.ext ?_
  simp only [Over.comp_left, arrowPt_left, basePt_left]
  exact (Over.w v).trans (Over.w x).symm

/-- The first component of `x` and the target of the arrow `v` lie over the same point of `Ū`. -/
lemma arrowPt_target (v : T ⟶ arrowsOverBase q) (x : T ⟶ Over.mk (pairCover q)) :
    (basePt q x ≫ prod.fst) ≫ q = (arrowPt q v ≫ G.target) ≫ q := by
  simpa only [groupoidPreRelation, Category.assoc, prod.lift_map, prod.lift_fst, prod.map_fst]
    using (congrArg (· ≫ (prod.fst : (Ub ⨯ Ub : Over S) ⟶ Ub)) (pair_compat q v x)).symm

/-- The source of the arrow `v` and the second component of `x` lie over the same point of `Ū`. -/
lemma arrowPt_source (v : T ⟶ arrowsOverBase q) (x : T ⟶ Over.mk (pairCover q)) :
    (arrowPt q v ≫ G.source) ≫ q = (basePt q x ≫ prod.snd) ≫ q := by
  simpa only [groupoidPreRelation, Category.assoc, prod.lift_map, prod.lift_snd, prod.map_snd]
    using congrArg (· ≫ (prod.snd : (Ub ⨯ Ub : Over S) ⟶ Ub)) (pair_compat q v x)

end Points

section Action

variable (K : GroupoidQuotientArrows G q) {T T' : Over (pairBase Ub)}
  (v : T ⟶ arrowsOverBase q) (x : T ⟶ Over.mk (pairCover q))

/-- The twisted arrow, as a generalized point of the arrow scheme over `S`. -/
def actHom : pairTest Ub T ⟶ G.arrows :=
  K.twistHom (arrowPt q v) rfl rfl (arrowPt_target q v x) (arrowPt_source q v x)

/-- The target of the twisted arrow is the first component of `x`. -/
@[simp]
lemma actHom_target : K.actHom q v x ≫ G.target = basePt q x ≫ prod.fst :=
  K.twistHom_target _ _ _ _ _

/-- The source of the twisted arrow is the second component of `x`. -/
@[simp]
lemma actHom_source : K.actHom q v x ≫ G.source = basePt q x ≫ prod.snd :=
  K.twistHom_source _ _ _ _ _

/-- The twisted arrow lies over the point `x` of `U ×_S U` through `j = (t, s)`. -/
lemma actHom_comp_preRelation : K.actHom q v x ≫ groupoidPreRelation G = basePt q x := by
  refine prod.hom_ext ?_ ?_ <;>
    simp only [groupoidPreRelation, Category.assoc, prod.lift_fst, prod.lift_snd,
      actHom_target, actHom_source]

/-- **The gluing action.** The arrow underlying `v`, twisted to have target and source the two
components of `x`. -/
def act : T ⟶ arrowsOverBase q :=
  Over.homMk (K.actHom q v x).left (by
    have h := congrArg (fun m : pairTest Ub T ⟶ _ => m.left)
      (K.actHom_comp_preRelation q v x)
    rw [Over.comp_left] at h
    calc (K.actHom q v x).left ≫ (groupoidPreRelation G).left ≫ pairCover q
        = ((K.actHom q v x).left ≫ (groupoidPreRelation G).left) ≫ pairCover q :=
          (Category.assoc _ _ _).symm
      _ = x.left ≫ pairCover q := by rw [h, basePt_left]
      _ = T.hom := Over.w x)

/-- The point `act q v x` has the same underlying morphism of schemes as `actHom q v x`. -/
@[simp]
lemma act_left : (K.act q v x).left = (K.actHom q v x).left := rfl

/-- Read over `S`, the point `act q v x` is the twisted arrow `actHom q v x`. -/
@[simp]
lemma arrowPt_act : arrowPt q (K.act q v x) = K.actHom q v x :=
  Over.OverMorphism.ext rfl

/-- The point `act q v x` of the arrow scheme lies over the point `x` of the chart. -/
@[simp]
lemma act_comp_structureMap :
    K.act q v x ≫ structureMap (pairCover q) (arrowsOverPair G) = x :=
  Over.OverMorphism.ext (by
    have h := congrArg (fun m : pairTest Ub T ⟶ _ => m.left) (K.actHom_comp_preRelation q v x)
    rwa [Over.comp_left] at h)

/-- The twisted arrow is natural in the test scheme. -/
lemma pairTestMap_actHom (k : T' ⟶ T) :
    pairTestMap k ≫ K.actHom q v x = K.actHom q (k ≫ v) (k ≫ x) := by
  have ha' : (pairTestMap k ≫ basePt q x ≫ prod.fst) ≫ q =
      ((pairTestMap k ≫ arrowPt q v) ≫ G.target) ≫ q := by
    simpa only [Category.assoc] using congrArg (pairTestMap k ≫ ·) (arrowPt_target q v x)
  have hb' : ((pairTestMap k ≫ arrowPt q v) ≫ G.source) ≫ q =
      (pairTestMap k ≫ basePt q x ≫ prod.snd) ≫ q := by
    simpa only [Category.assoc] using congrArg (pairTestMap k ≫ ·) (arrowPt_source q v x)
  refine (K.twistHom_pre (arrowPt q v) rfl rfl (arrowPt_target q v x) (arrowPt_source q v x)
    (pairTestMap k) rfl rfl ha' hb' (Category.assoc _ _ _) (Category.assoc _ _ _) rfl
    rfl).trans ?_
  refine K.twistHom_congr _ _ _ _ _ _ _ _ (arrowPt_comp q k v).symm ?_ ?_ <;>
    rw [basePt_comp, Category.assoc]

/-- The gluing action is natural in the test scheme. -/
lemma comp_act (k : T' ⟶ T) : k ≫ K.act q v x = K.act q (k ≫ v) (k ≫ x) :=
  arrowPt_injective q (by
    rw [arrowPt_comp, arrowPt_act, arrowPt_act, K.pairTestMap_actHom])

/-- **Acting twice is acting once.** -/
lemma act_act (y : T ⟶ Over.mk (pairCover q)) :
    K.act q (K.act q v x) y = K.act q v y := by
  have hacta : (basePt q y ≫ prod.fst) ≫ q = (K.actHom q v x ≫ G.target) ≫ q := by
    simpa only [arrowPt_act] using arrowPt_target q (K.act q v x) y
  have hacts : (K.actHom q v x ≫ G.source) ≫ q = (basePt q y ≫ prod.snd) ≫ q := by
    simpa only [arrowPt_act] using arrowPt_source q (K.act q v x) y
  have h1 : K.actHom q (K.act q v x) y = K.twistHom (K.actHom q v x) rfl rfl hacta hacts :=
    K.twistHom_congr _ _ _ _ _ _ _ _ (arrowPt_act q K v x) rfl rfl
  have h2 : K.twistHom (K.actHom q v x) rfl rfl hacta hacts = K.actHom q v y :=
    K.twistHom_twistHom (arrowPt q v) rfl rfl (arrowPt_target q v x) (arrowPt_source q v x)
      rfl rfl hacta hacts (arrowPt_target q v y) (arrowPt_source q v y)
  exact arrowPt_injective q (by rw [arrowPt_act, arrowPt_act]; exact h1.trans h2)

/-- **A point is fixed by the point of the chart it lies over.** -/
lemma act_self : K.act q v (v ≫ structureMap (pairCover q) (arrowsOverPair G)) = v := by
  have hay : basePt q (v ≫ structureMap (pairCover q) (arrowsOverPair G)) ≫ prod.fst =
      arrowPt q v ≫ G.target := by
    simp only [basePt_structureMap, Category.assoc, groupoidPreRelation, prod.lift_fst]
  have hbx : basePt q (v ≫ structureMap (pairCover q) (arrowsOverPair G)) ≫ prod.snd =
      arrowPt q v ≫ G.source := by
    simp only [basePt_structureMap, Category.assoc, groupoidPreRelation, prod.lift_snd]
  have h : K.actHom q v (v ≫ structureMap (pairCover q) (arrowsOverPair G)) = arrowPt q v :=
    K.twistHom_self _ _ _ _ _ hay hbx
  exact arrowPt_injective q (by rw [arrowPt_act]; exact h)

end Action

section Gluing

variable (K : GroupoidQuotientArrows G q)

/-- The gluing morphism of the descent datum, at the universal generalized point. -/
def gluingMap : arrowsOverBase q ⨯ Over.mk (pairCover q) ⟶
    Over.mk (pairCover q) ⨯ arrowsOverBase q :=
  prod.lift (prod.fst ≫ structureMap (pairCover q) (arrowsOverPair G))
    (K.act q prod.fst prod.snd)

/-- The inverse of the gluing morphism, at the universal generalized point. -/
def gluingInv : Over.mk (pairCover q) ⨯ arrowsOverBase q ⟶
    arrowsOverBase q ⨯ Over.mk (pairCover q) :=
  prod.lift (K.act q prod.snd prod.fst)
    (prod.snd ≫ structureMap (pairCover q) (arrowsOverPair G))

/-- The first component of the gluing morphism is the point of the chart under the arrow. -/
@[simp]
lemma gluingMap_fst : K.gluingMap q ≫ prod.fst =
    prod.fst ≫ structureMap (pairCover q) (arrowsOverPair G) := prod.lift_fst _ _

/-- The second component of the gluing morphism is the gluing action. -/
@[simp]
lemma gluingMap_snd : K.gluingMap q ≫ prod.snd = K.act q prod.fst prod.snd := prod.lift_snd _ _

/-- The first component of the inverse gluing morphism is the gluing action. -/
@[simp]
lemma gluingInv_fst : K.gluingInv q ≫ prod.fst = K.act q prod.snd prod.fst := prod.lift_fst _ _

/-- The second component of the inverse gluing morphism is the point of the chart under the
arrow. -/
@[simp]
lemma gluingInv_snd : K.gluingInv q ≫ prod.snd =
    prod.snd ≫ structureMap (pairCover q) (arrowsOverPair G) := prod.lift_snd _ _

/-- The gluing morphism followed by its inverse is the identity. -/
lemma gluingMap_gluingInv : K.gluingMap q ≫ K.gluingInv q = 𝟙 _ := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, gluingInv_fst, K.comp_act, gluingMap_fst, gluingMap_snd, K.act_act,
      K.act_self, Category.id_comp]
  · rw [Category.assoc, gluingInv_snd, ← Category.assoc, gluingMap_snd,
      K.act_comp_structureMap, Category.id_comp]

/-- The inverse of the gluing morphism followed by the gluing morphism is the identity. -/
lemma gluingInv_gluingMap : K.gluingInv q ≫ K.gluingMap q = 𝟙 _ := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, gluingMap_fst, ← Category.assoc, gluingInv_fst,
      K.act_comp_structureMap, Category.id_comp]
  · rw [Category.assoc, gluingMap_snd, K.comp_act, gluingInv_fst, gluingInv_snd, K.act_act,
      K.act_self, Category.id_comp]

/-- The gluing isomorphism of the descent datum. -/
def gluingObjIso : arrowsOverBase q ⨯ Over.mk (pairCover q) ≅
    Over.mk (pairCover q) ⨯ arrowsOverBase q where
  hom := K.gluingMap q
  inv := K.gluingInv q
  hom_inv_id := K.gluingMap_gluingInv q
  inv_hom_id := K.gluingInv_gluingMap q

/-- The gluing isomorphism, as an isomorphism over `(U ×_S U) ×_{Ū ×_S Ū} (U ×_S U)`. -/
def gluingIso :
    Over.mk (prod.map (structureMap (pairCover q) (arrowsOverPair G))
        (𝟙 (Over.mk (pairCover q)))) ≅
      Over.mk (prod.map (𝟙 (Over.mk (pairCover q)))
        (structureMap (pairCover q) (arrowsOverPair G))) :=
  Over.isoMk (K.gluingObjIso q) (by
    change K.gluingMap q ≫ prod.map (𝟙 (Over.mk (pairCover q)))
        (structureMap (pairCover q) (arrowsOverPair G)) =
      prod.map (structureMap (pairCover q) (arrowsOverPair G)) (𝟙 (Over.mk (pairCover q)))
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prod.map_fst, ← Category.assoc, gluingMap_fst, Category.comp_id,
        prod.map_fst]
    · rw [Category.assoc, prod.map_snd, ← Category.assoc, gluingMap_snd,
        K.act_comp_structureMap, prod.map_snd, Category.comp_id])

/-- The underlying morphism of the gluing isomorphism is the gluing morphism. -/
@[simp]
lemma gluingIso_hom_left : (K.gluingIso q).hom.left = K.gluingMap q := rfl

/-- The action on generalized points induced by the gluing morphism is `act`. -/
lemma gluingAction_gluingMap {T : Over (pairBase Ub)} (v : T ⟶ arrowsOverBase q)
    (x : T ⟶ Over.mk (pairCover q)) :
    gluingAction (arrowsOverPair G) (K.gluingMap q) v x = K.act q v x := by
  rw [gluingAction, gluingMap_snd, K.comp_act, prod.lift_fst, prod.lift_snd]

/-- **The descent datum carried by the arrow scheme** relative to `U ×_S U ⟶ Ū ×_S Ū`. -/
def arrowsDescentDatum : DescentDatum (pairCover q) :=
  DescentDatum.mk' (arrowsOverPair G) (K.gluingIso q) (by
    rw [gluingIso_hom_left]
    refine (cocycle_iff_gluingAction_act_act (arrowsOverPair G) (K.gluingMap q)
      (by rw [gluingMap_fst]) (by rw [← Category.assoc, gluingMap_snd,
        K.act_comp_structureMap])).2 ?_
    intro T v x y
    simp only [gluingAction_gluingMap, K.act_act])

/-- The scheme carrying the descent datum is the arrow scheme over `U ×_S U`. -/
@[simp]
lemma arrowsDescentDatum_over : (K.arrowsDescentDatum q).over = arrowsOverPair G := rfl

end Gluing

end GroupoidQuotientArrows

end AlgebraicGeometry

end

end
