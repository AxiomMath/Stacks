module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Sites.Continuous
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.CanonicalDatum
public import StacksFrontier.CategoryTheory.Sites.Descent.LocallyRepresentableSheaves
public import StacksCore.Tactic.StacksAttribute

/-!
# Descent data of schemes in terms of sheaves

Let `J` be a subcanonical Grothendieck topology on the category of schemes — the Zariski, étale,
smooth, syntomic and fppf topologies are such (each is coarser than the fpqc topology, which is
subcanonical) — let `S` be a scheme and let `{f i : X i ⟶ S}` be a covering of `S` for `J`.
Stacks 02W5 identifies the category of descent data `(V_i, φ_ij)` of schemes relative to
`{f i}` (Stacks 023W, `AlgebraicGeometry.DescentData`) with the category of sheaves `F` on
`(Sch/S)_J` such that every product `h_{X i} × F` is representable. Moreover the scheme
representing `h_{X i} × F` is `V_i`, and `F` is representable exactly when the descent datum is
effective (Stacks 02VU, `AlgebraicGeometry.DescentData.IsFamilyEffective`).

## Main definitions

* `AlgebraicGeometry.DescentData.toPresheaf`: the presheaf `T ↦ Hom(can T, D)` of a descent
  datum `D`, morphisms of descent data out of the canonical descent datum of `T`.
* `AlgebraicGeometry.DescentData.eval`: the canonical morphism from the canonical descent datum
  of `V_i` to `D`, whose `j`-th component is `φ_ij` followed by the projection to `V_j`.
* `AlgebraicGeometry.DescentData.sheavesLocallyRepresentable`: the sheaves `F` on `(Sch/S)_J`
  for which every `h_{X i} × F` is representable.
* `AlgebraicGeometry.DescentData.toSheaf`: the functor from descent data to those sheaves.
* `AlgebraicGeometry.DescentData.descentDatum`: the descent datum built from representations of
  the products `h_{X i} × F`, with gluing isomorphisms `V_i ×_S X_j ≅ X_i ×_S V_j` given by the
  fact that both represent `h_{X i} × F × h_{X j}`.

## Main results

* `AlgebraicGeometry.DescentData.sheafEquivalence` is Stacks 02W5: descent data relative to a
  `J`-covering are equivalent to sheaves on `(Sch/S)_J` with every `h_{X i} × F` representable.
* `AlgebraicGeometry.DescentData.representableBy_sheafEquivalence_functor` and
  `AlgebraicGeometry.DescentData.representableBy_sheafEquivalence_inverse` are part (1), in both
  directions: `h_{X i} × F` is represented by the `i`-th component of the descent datum.
* `AlgebraicGeometry.DescentData.isRepresentable_sheafEquivalence_functor_iff` and
  `AlgebraicGeometry.DescentData.isRepresentable_iff_isFamilyEffective_sheafEquivalence_inverse`
  are part (2), in both directions: `F` is representable if and only if the corresponding descent
  datum is effective.
* `AlgebraicGeometry.DescentData.isSheaf_toPresheaf`: the presheaf of a descent datum is a sheaf.
* `AlgebraicGeometry.DescentData.full_canonicalFunctor` and
  `AlgebraicGeometry.DescentData.faithful_canonicalFunctor`: the canonical descent datum functor
  is fully faithful for a covering of a subcanonical topology.

## Implementation notes

The source builds the sheaf of a descent datum as a coequalizer of sheaves, which needs a
sheafification functor for `Type u`-valued sheaves on the large category of schemes over `S`.
Instead the sheaf is the presheaf `T ↦ Hom(can T, D)`, whose sections over `T` are families of
morphisms `T ×_S X_i ⟶ V_i` over `X_i` compatible with the `φ_ij`; it is a sheaf because each
`h_{V_i}` is, and only limits indexed by the covering are involved. For the same reason the
abstract-site version `CategoryTheory.GrothendieckTopology.locallyRepresentableEquivalence`,
whose hypothesis `HasLimitsOfSize.{max u v, max u v} (Type v)` fails for the category of
schemes, is not used.

The representing object of `h_{X i} × F_D` is `V_i`: a morphism `W ⟶ V_i` over `S` gives the
morphism `W ⟶ X_i` and the section `can W ⟶ can V_i ⟶ D` obtained from `eval`, and conversely a
pair `(q, ψ)` gives `ψ_i` composed with the graph `W ⟶ W ×_S X_i` of `q`. That these are
inverse uses that `φ_ii` restricts to the identity on the diagonal, a consequence of the cocycle
condition (`AlgebraicGeometry.DescentData.lift_gluing_diag`).

The sites `(Sch/S)_τ` of the source are the big sites of a chosen set of schemes; here the
category is `Over S` in `Scheme.{u}` and the index type of the covering is `Type u`, which is how
the library reads a big site.

## References

* [Stacks Project, Tag 02W5](https://stacks.math.columbia.edu/tag/02W5)
* [Stacks Project, Tag 023W](https://stacks.math.columbia.edu/tag/023W)
* [Stacks Project, Tag 02VU](https://stacks.math.columbia.edu/tag/02VU)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-! ### Restriction of sections along products and the canonical datum -/

section NestedMaps

variable {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*)

@[simp]
lemma map_prodLift_map_fst_apply {W A B : C} [HasBinaryProduct A B] (x : W ⟶ A) (y : W ⟶ B)
    (t : P.obj (op A)) :
    P.map (prod.lift x y).op (P.map (prod.fst : A ⨯ B ⟶ A).op t) = P.map x.op t := by
  have h := congrArg (fun h ↦ P.map h.op t) (prod.lift_fst x y)
  simp only [op_comp, Functor.map_comp_apply] at h
  exact h

@[simp]
lemma map_prodLift_map_snd_apply {W A B : C} [HasBinaryProduct A B] (x : W ⟶ A) (y : W ⟶ B)
    (t : P.obj (op B)) :
    P.map (prod.lift x y).op (P.map (prod.snd : A ⨯ B ⟶ B).op t) = P.map y.op t := by
  have h := congrArg (fun h ↦ P.map h.op t) (prod.lift_snd x y)
  simp only [op_comp, Functor.map_comp_apply] at h
  exact h

@[simp]
lemma map_prodMap_map_fst_apply {A B A' B' : C} [HasBinaryProduct A B] [HasBinaryProduct A' B']
    (x : A ⟶ A') (y : B ⟶ B') (t : P.obj (op A')) :
    P.map (prod.map x y).op (P.map (prod.fst : A' ⨯ B' ⟶ A').op t) =
      P.map (prod.fst : A ⨯ B ⟶ A).op (P.map x.op t) := by
  have h := congrArg (fun h ↦ P.map h.op t) (prod.map_fst x y)
  simp only [op_comp, Functor.map_comp_apply] at h
  exact h

@[simp]
lemma map_prodMap_map_snd_apply {A B A' B' : C} [HasBinaryProduct A B] [HasBinaryProduct A' B']
    (x : A ⟶ A') (y : B ⟶ B') (t : P.obj (op B')) :
    P.map (prod.map x y).op (P.map (prod.snd : A' ⨯ B' ⟶ B').op t) =
      P.map (prod.snd : A ⨯ B ⟶ B).op (P.map y.op t) := by
  have h := congrArg (fun h ↦ P.map h.op t) (prod.map_snd x y)
  simp only [op_comp, Functor.map_comp_apply] at h
  exact h

end NestedMaps

/-! ### Morphisms over a member of the family, read over the base -/

/-- A morphism over `S` between two schemes over `Y`, viewed over `S` along `h : Y ⟶ S`, which is
compatible with their structure maps to `Y`, as a morphism over `Y`. -/
def overHomOfMap {Y : Scheme.{u}} (h : Y ⟶ S) {A B : Over Y}
    (m : (Over.map h).obj A ⟶ (Over.map h).obj B)
    (hm : m ≫ structureMap h B = structureMap h A) : A ⟶ B :=
  Over.homMk m.left (by simpa using congrArg CommaMorphism.left hm)

lemma map_overHomOfMap {Y : Scheme.{u}} (h : Y ⟶ S) {A B : Over Y}
    (m : (Over.map h).obj A ⟶ (Over.map h).obj B)
    (hm : m ≫ structureMap h B = structureMap h A) :
    (Over.map h).map (overHomOfMap h m hm) = m :=
  Over.OverMorphism.ext rfl

@[reassoc (attr := simp)]
lemma map_comp_structureMap {Y : Scheme.{u}} (h : Y ⟶ S) {A B : Over Y} (a : A ⟶ B) :
    (Over.map h).map a ≫ structureMap h B = structureMap h A :=
  Over.OverMorphism.ext (Over.w a)

lemma over_hom_ext_of_map {Y : Scheme.{u}} (h : Y ⟶ S) {A B : Over Y} {a b : A ⟶ B}
    (hab : (Over.map h).map a = (Over.map h).map b) : a = b :=
  Over.OverMorphism.ext (by simpa using congrArg CommaMorphism.left hab)

namespace CanonicalDatum

variable {ι : Type u} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ S)

@[simp]
lemma functor_map_hom {U V : Over S} (g : U ⟶ V) (i : ι) :
    ((CanonicalDatum.functor f).map g).hom i = (Over.pullback (f i)).map g := rfl

@[simp]
lemma functor_obj_gluing_hom_left (U : Over S) (i j : ι) :
    (((CanonicalDatum.functor f).obj U).gluing i j).hom.left = transition U (f i) (f j) := rfl

/-- The comparison of a component of the canonical datum with the product over `S` is natural. -/
@[reassoc (attr := simp)]
lemma map_pullback_map_comp_lift {Y : Scheme.{u}} (g : Y ⟶ S) {U V : Over S} (h : U ⟶ V) :
    (Over.map g).map ((Over.pullback g).map h) ≫
        prod.lift (originalProjection V g) (structureMap g ((Over.pullback g).obj V)) =
      prod.lift (originalProjection U g) (structureMap g ((Over.pullback g).obj U)) ≫
        prod.map h (𝟙 _) := by
  apply prod.hom_ext <;> simp

/-- The lift into a component followed by the canonical transition and the second projection
is the lift into the other component. -/
@[reassoc (attr := simp)]
lemma lift_transition_snd {Y Y' : Scheme.{u}} (g : Y ⟶ S) (g' : Y' ⟶ S) {U W : Over S}
    (a : W ⟶ component U g) (b : W ⟶ Over.mk g') :
    prod.lift a b ≫ transition U g g' ≫ prod.snd =
      componentLift (a ≫ originalProjection U g) b := by
  apply component_hom_ext <;> simp

variable {f} (P : (Over S)ᵒᵖ ⥤ Type*)

@[simp]
lemma map_transition_map_snd_map_original_apply {Y Y' : Scheme.{u}} (U : Over S) (g : Y ⟶ S)
    (g' : Y' ⟶ S) (t : P.obj (op U)) :
    P.map (transition U g g').op (P.map prod.snd.op (P.map (originalProjection U g').op t)) =
      P.map prod.fst.op (P.map (originalProjection U g).op t) := by
  have h := congrArg (fun h ↦ P.map h.op t) (transition_original U g g')
  simp only [op_comp, Functor.map_comp_apply] at h
  exact h

@[simp]
lemma map_componentMap_map_original_apply {Y : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    (g : Y ⟶ S) (t : P.obj (op V)) :
    P.map ((Over.map g).map ((Over.pullback g).map h)).op (P.map (originalProjection V g).op t) =
      P.map (originalProjection U g).op (P.map h.op t) := by
  have e := congrArg (fun e ↦ P.map e.op t) (componentMap_original h g)
  simp only [op_comp, Functor.map_comp_apply] at e
  exact e

@[simp]
lemma map_componentLift_map_original_apply {Y : Scheme.{u}} {U T : Over S} {g : Y ⟶ S}
    (a : T ⟶ U) (b : T ⟶ Over.mk g) (t : P.obj (op U)) :
    P.map (componentLift a b).op (P.map (originalProjection U g).op t) = P.map a.op t := by
  have e := congrArg (fun e ↦ P.map e.op t) (componentLift_original a b)
  simp only [op_comp, Functor.map_comp_apply] at e
  exact e

end CanonicalDatum

namespace DescentData

open CanonicalDatum

variable {ι : Type u} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}

/-- The `i`-th component of a descent datum, as a scheme over `S`. -/
abbrev overBase (D : DescentData f) (i : ι) : Over S := (Over.map (f i)).obj (D.obj i)

/-! ### Consequences of the cocycle condition -/

/-- The cocycle condition, read on the last factor. -/
lemma gluing_cocycle_snd (D : DescentData f) (i j k : ι) {W : Over S}
    (a : W ⟶ D.overBase i ⨯ Over.mk (f j)) (b : W ⟶ Over.mk (f k)) :
    prod.lift (a ≫ (D.gluing i j).hom.left ≫ prod.snd) b ≫ (D.gluing j k).hom.left ≫
        prod.snd =
      prod.lift (a ≫ prod.fst) b ≫ (D.gluing i k).hom.left ≫ prod.snd := by
  have h := congrArg (fun t ↦ prod.lift a b ≫ t ≫ prod.snd) (D.cocycle i j k)
  have key₁ : prod.lift a b ≫ (prod.map (D.gluing i j).hom.left (𝟙 (Over.mk (f k))) ≫
      prodMapLastTwo (D.gluing j k).hom.left) ≫ prod.snd =
        prod.lift (a ≫ (D.gluing i j).hom.left ≫ prod.snd) b ≫ (D.gluing j k).hom.left ≫
          prod.snd := by
    simp only [prodMapLastTwo, prod.associator_hom, prod.associator_inv, prod.lift_map_assoc,
      Category.comp_id, Category.assoc, prod.lift_snd, prod.comp_lift_assoc, prod.lift_snd_assoc]
    simp
  have key₂ : prod.lift a b ≫ prodMapFirstThird (D.gluing i k).hom.left ≫ prod.snd =
      prod.lift (a ≫ prod.fst) b ≫ (D.gluing i k).hom.left ≫ prod.snd := by
    simp only [prodMapFirstThird, prodMapLastTwo, prod.associator_hom, prod.associator_inv,
      prod.braiding_hom, Category.assoc, prod.lift_snd, prod.map_snd, prod.map_fst_assoc,
      prod.lift_fst_assoc, prod.lift_snd_assoc, prod.comp_lift_assoc, prod.lift_map_assoc,
      Category.comp_id, prod.lift_fst]
  exact key₁.symm.trans (h.trans key₂)

/-- The restriction of the gluing isomorphism `φ_ii` to the diagonal, read on the second
factor. -/
def diagEndo (D : DescentData f) (i : ι) : D.overBase i ⟶ D.overBase i :=
  prod.lift (𝟙 _) (structureMap (f i) (D.obj i)) ≫ (D.gluing i i).hom.left ≫ prod.snd

lemma diagEndo_structureMap (D : DescentData f) (i : ι) :
    D.diagEndo i ≫ structureMap (f i) (D.obj i) = structureMap (f i) (D.obj i) := by
  simp [diagEndo]

lemma diagEndo_comp_self (D : DescentData f) (i : ι) :
    D.diagEndo i ≫ D.diagEndo i = D.diagEndo i := by
  have h := D.gluing_cocycle_snd i i i (prod.lift (𝟙 _) (structureMap (f i) (D.obj i)))
    (structureMap (f i) (D.obj i))
  simp only [prod.lift_fst] at h
  change prod.lift (D.diagEndo i) (structureMap (f i) (D.obj i)) ≫
    (D.gluing i i).hom.left ≫ prod.snd = D.diagEndo i at h
  have e : prod.lift (D.diagEndo i) (structureMap (f i) (D.obj i)) =
      D.diagEndo i ≫ prod.lift (𝟙 _) (structureMap (f i) (D.obj i)) := by
    apply prod.hom_ext <;> simp [diagEndo_structureMap]
  calc D.diagEndo i ≫ D.diagEndo i =
        (D.diagEndo i ≫ prod.lift (𝟙 _) (structureMap (f i) (D.obj i))) ≫
          (D.gluing i i).hom.left ≫ prod.snd := by
        rw [Category.assoc]; rfl
    _ = D.diagEndo i := by rw [← e]; exact h

lemma diagEndo_retraction (D : DescentData f) (i : ι) :
    D.diagEndo i ≫ prod.lift (structureMap (f i) (D.obj i)) (𝟙 _) ≫
        (D.gluing i i).inv.left ≫ prod.fst = 𝟙 _ := by
  have e : D.diagEndo i ≫ prod.lift (structureMap (f i) (D.obj i)) (𝟙 _) =
      prod.lift (𝟙 _) (structureMap (f i) (D.obj i)) ≫ (D.gluing i i).hom.left := by
    apply prod.hom_ext
    · simp [diagEndo_structureMap]
    · simp [diagEndo]
  rw [← Category.assoc, e, Category.assoc, Over.hom_left_inv_left_assoc]
  simp

lemma diagEndo_eq_id (D : DescentData f) (i : ι) : D.diagEndo i = 𝟙 _ := by
  have h := congrArg (· ≫ prod.lift (structureMap (f i) (D.obj i)) (𝟙 _) ≫
    (D.gluing i i).inv.left ≫ prod.fst) (D.diagEndo_comp_self i)
  simp only [Category.assoc, diagEndo_retraction, Category.comp_id] at h
  exact h

/-- The gluing isomorphism `φ_ii` restricts to the identity on the diagonal. -/
lemma lift_gluing_diag (D : DescentData f) (i : ι) :
    prod.lift (𝟙 _) (structureMap (f i) (D.obj i)) ≫ (D.gluing i i).hom.left =
      prod.lift (structureMap (f i) (D.obj i)) (𝟙 _) := by
  apply prod.hom_ext
  · simp
  · have := D.diagEndo_eq_id i
    rw [diagEndo] at this
    simpa using this

/-! ### The canonical morphisms `eval` -/

/-- The map from the `j`-th component of the canonical datum of the `i`-th component of `D` to
the `j`-th component of `D`, read through the gluing isomorphism `φ_ij`. -/
def evalMap (D : DescentData f) (i j : ι) :
    component (D.overBase i) (f j) ⟶ D.overBase j :=
  prod.lift (originalProjection _ (f j)) (structureMap (f j) _) ≫ (D.gluing i j).hom.left ≫
    prod.snd

@[reassoc (attr := simp)]
lemma evalMap_structureMap (D : DescentData f) (i j : ι) :
    D.evalMap i j ≫ structureMap (f j) (D.obj j) =
      structureMap (f j) ((Over.pullback (f j)).obj (D.overBase i)) := by
  simp [evalMap]

lemma componentLift_evalMap_self (D : DescentData f) (i : ι) :
    componentLift (𝟙 _) (structureMap (f i) (D.obj i)) ≫ D.evalMap i i = 𝟙 _ := by
  have e : componentLift (𝟙 (D.overBase i)) (structureMap (f i) (D.obj i)) ≫
      prod.lift (originalProjection _ (f i)) (structureMap (f i) _) =
        prod.lift (𝟙 _) (structureMap (f i) (D.obj i)) := by
    apply prod.hom_ext <;> simp
  rw [evalMap, ← Category.assoc, e, ← Category.assoc, lift_gluing_diag]
  simp

/-- The `j`-th component of `eval`, as a morphism over `X j`. -/
def evalHom (D : DescentData f) (i j : ι) :
    (Over.pullback (f j)).obj (D.overBase i) ⟶ D.obj j :=
  overHomOfMap (f j) (D.evalMap i j) (D.evalMap_structureMap i j)

lemma map_evalHom (D : DescentData f) (i j : ι) :
    (Over.map (f j)).map (D.evalHom i j) = D.evalMap i j :=
  map_overHomOfMap _ _ _

/-- The canonical morphism from the canonical descent datum of the `i`-th component of a descent
datum `D` to `D`: on the `j`-th component it is `φ_ij` followed by the projection. -/
def eval (D : DescentData f) (i : ι) : (CanonicalDatum.functor f).obj (D.overBase i) ⟶ D where
  hom j := D.evalHom i j
  comm j k := by
    change prod.map ((Over.map (f j)).map (D.evalHom i j)) (𝟙 _) ≫ (D.gluing j k).hom.left =
      transition (D.overBase i) (f j) (f k) ≫ prod.map (𝟙 _) ((Over.map (f k)).map (D.evalHom i k))
    rw [map_evalHom, map_evalHom]
    apply prod.hom_ext
    · simp
    · have h := D.gluing_cocycle_snd i j k
        (prod.fst ≫ prod.lift (originalProjection (D.overBase i) (f j))
          (structureMap (f j) ((Over.pullback (f j)).obj (D.overBase i)))) prod.snd
      have e₁ : prod.map (D.evalMap i j) (𝟙 (Over.mk (f k))) =
          prod.lift (prod.fst ≫ prod.lift (originalProjection (D.overBase i) (f j))
            (structureMap (f j) ((Over.pullback (f j)).obj (D.overBase i))) ≫
              (D.gluing i j).hom.left ≫ prod.snd) prod.snd := by
        apply prod.hom_ext <;> simp [evalMap]
      have e₂ : transition (D.overBase i) (f j) (f k) ≫ prod.snd ≫
          prod.lift (originalProjection (D.overBase i) (f k))
            (structureMap (f k) ((Over.pullback (f k)).obj (D.overBase i))) =
          prod.lift ((prod.fst ≫ prod.lift (originalProjection (D.overBase i) (f j))
            (structureMap (f j) ((Over.pullback (f j)).obj (D.overBase i)))) ≫ prod.fst)
              prod.snd := by
        apply prod.hom_ext <;> simp
      rw [Category.assoc, Category.assoc, prod.map_snd, e₁, evalMap, reassoc_of% e₂]
      simpa only [Category.assoc] using h

/-- Naturality of `eval` in the descent datum. -/
lemma eval_comp {D D' : DescentData f} (α : D ⟶ D') (i : ι) :
    D.eval i ≫ α =
      (CanonicalDatum.functor f).map ((Over.map (f i)).map (α.hom i)) ≫ D'.eval i := by
  refine hom_ext fun j ↦ over_hom_ext_of_map (f j) ?_
  change (Over.map (f j)).map (D.evalHom i j ≫ α.hom j) =
    (Over.map (f j)).map ((Over.pullback (f j)).map ((Over.map (f i)).map (α.hom i)) ≫
      D'.evalHom i j)
  rw [(Over.map (f j)).map_comp (D.evalHom i j) (α.hom j),
    (Over.map (f j)).map_comp ((Over.pullback (f j)).map _) (D'.evalHom i j)]
  rw [map_evalHom, map_evalHom, evalMap, evalMap, map_pullback_map_comp_lift_assoc]
  simp only [Category.assoc]
  rw [reassoc_of% (α.comm i j), prod.map_snd]

/-- The second consequence of the cocycle condition: on `X_i ×_S V_i ×_S X_j` the two
canonical morphisms agree. -/
lemma map_gluing_snd_eval (D : DescentData f) (i j : ι) :
    (CanonicalDatum.functor f).map ((D.gluing i j).hom.left ≫ prod.snd) ≫ D.eval j =
      (CanonicalDatum.functor f).map prod.fst ≫ D.eval i := by
  refine hom_ext fun k ↦ over_hom_ext_of_map (f k) ?_
  change (Over.map (f k)).map ((Over.pullback (f k)).map ((D.gluing i j).hom.left ≫ prod.snd) ≫
      D.evalHom j k) =
    (Over.map (f k)).map ((Over.pullback (f k)).map prod.fst ≫ D.evalHom i k)
  rw [(Over.map (f k)).map_comp ((Over.pullback (f k)).map _) (D.evalHom j k),
    (Over.map (f k)).map_comp ((Over.pullback (f k)).map _) (D.evalHom i k)]
  rw [map_evalHom, map_evalHom, evalMap, evalMap, map_pullback_map_comp_lift_assoc,
    map_pullback_map_comp_lift_assoc]
  have h := D.gluing_cocycle_snd i j k (originalProjection _ (f k)) (structureMap (f k) _)
  have e₁ : prod.lift (originalProjection (D.overBase i ⨯ Over.mk (f j)) (f k))
      (structureMap (f k) ((Over.pullback (f k)).obj (D.overBase i ⨯ Over.mk (f j)))) ≫
        prod.map ((D.gluing i j).hom.left ≫ prod.snd) (𝟙 _) =
      prod.lift (originalProjection (D.overBase i ⨯ Over.mk (f j)) (f k) ≫
        (D.gluing i j).hom.left ≫ prod.snd)
        (structureMap (f k) ((Over.pullback (f k)).obj (D.overBase i ⨯ Over.mk (f j)))) := by
    apply prod.hom_ext <;> simp
  have e₂ : prod.lift (originalProjection (D.overBase i ⨯ Over.mk (f j)) (f k))
      (structureMap (f k) ((Over.pullback (f k)).obj (D.overBase i ⨯ Over.mk (f j)))) ≫
        prod.map prod.fst (𝟙 _) =
      prod.lift (originalProjection (D.overBase i ⨯ Over.mk (f j)) (f k) ≫ prod.fst)
        (structureMap (f k) ((Over.pullback (f k)).obj (D.overBase i ⨯ Over.mk (f j)))) := by
    apply prod.hom_ext <;> simp
  exact ((reassoc_of% e₁) ((D.gluing j k).hom.left ≫ prod.snd)).trans
    (h.trans ((reassoc_of% e₂) ((D.gluing i k).hom.left ≫ prod.snd)).symm)

/-! ### The presheaf of a descent datum -/

/-- The presheaf on `Sch/S` attached to a descent datum `D`: its value on `T` is the set of
morphisms of descent data from the canonical descent datum of `T` to `D`. -/
abbrev toPresheaf (D : DescentData f) : (Over S)ᵒᵖ ⥤ Type u :=
  (CanonicalDatum.functor f).op ⋙ yoneda.obj D

variable (f) in
/-- The functor sending a descent datum to its presheaf. -/
abbrev toPresheafFunctor : DescentData f ⥤ (Over S)ᵒᵖ ⥤ Type u :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (CanonicalDatum.functor f).op

/-- The `i`-th component of a morphism out of a canonical descent datum, with its source written
as a fibre product. -/
def canComp {T : Over S} {D : DescentData f} (ψ : (CanonicalDatum.functor f).obj T ⟶ D) (i : ι) :
    (Over.pullback (f i)).obj T ⟶ D.obj i :=
  ψ.hom i

lemma canComp_comm {T : Over S} {D : DescentData f} (ψ : (CanonicalDatum.functor f).obj T ⟶ D)
    (i j : ι) :
    prod.map ((Over.map (f i)).map (canComp ψ i)) (𝟙 (Over.mk (f j))) ≫ (D.gluing i j).hom.left =
      transition T (f i) (f j) ≫ prod.map (𝟙 _) ((Over.map (f j)).map (canComp ψ j)) :=
  ψ.comm i j

lemma canComp_map_comp {T T' : Over S} {D : DescentData f} (g : T' ⟶ T)
    (ψ : (CanonicalDatum.functor f).obj T ⟶ D) (i : ι) :
    canComp ((CanonicalDatum.functor f).map g ≫ ψ) i = (Over.pullback (f i)).map g ≫ canComp ψ i :=
  rfl

lemma canComp_comp {T : Over S} {D D' : DescentData f}
    (ψ : (CanonicalDatum.functor f).obj T ⟶ D) (α : D ⟶ D') (i : ι) :
    canComp (ψ ≫ α) i = canComp ψ i ≫ α.hom i :=
  rfl

lemma canComp_eval (D : DescentData f) (i j : ι) : canComp (D.eval i) j = D.evalHom i j :=
  rfl

lemma canHom_ext {T : Over S} {D : DescentData f} {ψ ψ' : (CanonicalDatum.functor f).obj T ⟶ D}
    (h : ∀ i, canComp ψ i = canComp ψ' i) : ψ = ψ' :=
  hom_ext h

/-- `h_{X i} × F_D` is represented by the `i`-th component of `D`. -/
def representableBy (D : DescentData f) (i : ι) :
    (FunctorToTypes.prod (yoneda.obj (Over.mk (f i))) D.toPresheaf).RepresentableBy
      (D.overBase i) where
  homEquiv {V} :=
    { toFun v := (v ≫ structureMap (f i) (D.obj i), (CanonicalDatum.functor f).map v ≫ D.eval i)
      invFun x := componentLift (𝟙 V) x.1 ≫ (Over.map (f i)).map (canComp (T := V) x.2 i)
      left_inv v := by
        change componentLift (𝟙 V) (v ≫ structureMap (f i) (D.obj i)) ≫
          (Over.map (f i)).map (canComp ((CanonicalDatum.functor f).map v ≫ D.eval i) i) = v
        rw [canComp_map_comp, canComp_eval, Functor.map_comp, map_evalHom]
        have e : componentLift (𝟙 V) (v ≫ structureMap (f i) (D.obj i)) ≫
            (Over.map (f i)).map ((Over.pullback (f i)).map v) =
              v ≫ componentLift (𝟙 _) (structureMap (f i) (D.obj i)) := by
          apply component_hom_ext <;> simp
        rw [reassoc_of% e, componentLift_evalMap_self, Category.comp_id]
      right_inv x := by
        obtain ⟨q, ψ⟩ := x
        change ((componentLift (𝟙 V) q ≫ (Over.map (f i)).map (canComp (T := V) ψ i)) ≫
            structureMap (f i) (D.obj i), (CanonicalDatum.functor f).map
              (componentLift (𝟙 V) q ≫ (Over.map (f i)).map (canComp (T := V) ψ i)) ≫ D.eval i) =
          (q, ψ)
        refine Prod.ext ?_ ?_ <;> dsimp only
        · rw [Category.assoc, map_comp_structureMap, componentLift_structure]
        · refine canHom_ext fun j ↦ over_hom_ext_of_map (f j) ?_
          rw [canComp_map_comp, canComp_eval, Functor.map_comp, map_evalHom, evalMap,
            map_pullback_map_comp_lift_assoc]
          have e : prod.lift (originalProjection V (f j))
              (structureMap (f j) ((Over.pullback (f j)).obj V)) ≫
                prod.map (componentLift (𝟙 V) q ≫ (Over.map (f i)).map (canComp (T := V) ψ i))
                  (𝟙 _) =
              prod.lift (originalProjection V (f j) ≫ componentLift (𝟙 V) q)
                (structureMap (f j) ((Over.pullback (f j)).obj V)) ≫
                prod.map ((Over.map (f i)).map (canComp (T := V) ψ i)) (𝟙 _) := by
            apply prod.hom_ext <;> simp
          have e' : componentLift ((originalProjection V (f j) ≫ componentLift (𝟙 V) q) ≫
              originalProjection V (f i)) (structureMap (f j) ((Over.pullback (f j)).obj V)) =
                𝟙 _ := by
            apply component_hom_ext <;> simp
          rw [reassoc_of% e, reassoc_of% (canComp_comm (T := V) ψ i j), prod.map_snd,
            lift_transition_snd_assoc, e', Category.id_comp] }
  homEquiv_comp {V V'} g v := by
    change ((g ≫ v) ≫ structureMap (f i) (D.obj i),
        (CanonicalDatum.functor f).map (g ≫ v) ≫ D.eval i) =
      (g ≫ v ≫ structureMap (f i) (D.obj i),
        (CanonicalDatum.functor f).map g ≫ (CanonicalDatum.functor f).map v ≫ D.eval i)
    rw [Category.assoc, Functor.map_comp, Category.assoc]

lemma representableBy_homEquiv_apply (D : DescentData f) (i : ι) {V : Over S}
    (v : V ⟶ D.overBase i) :
    (D.representableBy i).homEquiv v =
      (v ≫ structureMap (f i) (D.obj i), (CanonicalDatum.functor f).map v ≫ D.eval i) := rfl

/-! ### The presheaf of a descent datum is a sheaf -/

/-- A component of the canonical datum is the product over `S`. -/
def componentIsoProd {Y : Scheme.{u}} (U : Over S) (g : Y ⟶ S) :
    component U g ≅ U ⨯ Over.mk g where
  hom := prod.lift (originalProjection U g) (structureMap g ((Over.pullback g).obj U))
  inv := componentLift prod.fst prod.snd
  hom_inv_id := by apply component_hom_ext <;> simp
  inv_hom_id := by apply prod.hom_ext <;> simp

lemma componentIsoProd_hom {Y : Scheme.{u}} (U : Over S) (g : Y ⟶ S) :
    (componentIsoProd U g).hom =
      prod.lift (originalProjection U g) (structureMap g ((Over.pullback g).obj U)) := rfl

section Sheaf

variable (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]

/-- The presheaf attached to a descent datum is a sheaf on `(Sch/S)_J`. -/
theorem isSheaf_toPresheaf (D : DescentData f) :
    Presieve.IsSheaf (J.over S) D.toPresheaf := by
  have hP : ∀ i, Presieve.IsSheaf (J.over S)
      ((Over.pullback (f i)).op ⋙ yoneda.obj (D.obj i)) := fun i ↦
    Functor.op_comp_isSheaf_of_isSheaf_type (Over.pullback (f i)) (J.over S)
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J.over (X i)) _)
  have hQ : ∀ i j, Presieve.IsSheaf (J.over S)
      ((Over.pullback (f i)).op ⋙ (Over.map (f i)).op ⋙ (Over.pullback (f j)).op ⋙
        (Over.map (f j)).op ⋙ yoneda.obj (D.overBase j)) := fun i j ↦
    Functor.op_comp_isSheaf_of_isSheaf_type (Over.pullback (f i)) (J.over S)
      (Functor.op_comp_isSheaf_of_isSheaf_type (Over.map (f i)) (J.over (X i))
        (Functor.op_comp_isSheaf_of_isSheaf_type (Over.pullback (f j)) (J.over S)
          (Functor.op_comp_isSheaf_of_isSheaf_type (Over.map (f j)) (J.over (X j))
            (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J.over S) _))))
  intro T R hR x hx
  have hcomp : ∀ i, ∃ a : (Over.pullback (f i)).obj T ⟶ D.obj i,
      ∀ ⦃T' : Over S⦄ (g : T' ⟶ T) (hg : R g),
        (Over.pullback (f i)).map g ≫ a = canComp (T := T') (x g hg) i := by
    intro i
    obtain ⟨a, ha, -⟩ := hP i R hR (fun T' g hg ↦ (x g hg).hom i) (by
      intro _ _ _ g₁ g₂ _ _ h₁ h₂ w
      exact congrArg (fun φ ↦ φ.hom i) (hx g₁ g₂ h₁ h₂ w))
    exact ⟨a, ha⟩
  choose a ha using hcomp
  have hcomm : ∀ i j, prod.map ((Over.map (f i)).map (a i)) (𝟙 (Over.mk (f j))) ≫
      (D.gluing i j).hom.left =
        transition T (f i) (f j) ≫ prod.map (𝟙 _) ((Over.map (f j)).map (a j)) := by
    intro i j
    apply prod.hom_ext
    · simp
    · simp only [Category.assoc, prod.map_snd]
      rw [← cancel_epi (componentIsoProd (component T (f i)) (f j)).hom, componentIsoProd_hom]
      · refine ((hQ i j) R hR).isSeparatedFor.ext ?_
        intro T' g hg
        change (Over.map (f j)).map ((Over.pullback (f j)).map ((Over.map (f i)).map
            ((Over.pullback (f i)).map g))) ≫ _ =
          (Over.map (f j)).map ((Over.pullback (f j)).map ((Over.map (f i)).map
            ((Over.pullback (f i)).map g))) ≫ _
        rw [map_pullback_map_comp_lift_assoc, map_pullback_map_comp_lift_assoc]
        have hg₁ := canComp_comm (T := T') (x g hg) i j
        have hg₂ : prod.map ((Over.map (f i)).map ((Over.pullback (f i)).map g))
            (𝟙 (Over.mk (f j))) ≫ transition T (f i) (f j) =
              transition T' (f i) (f j) ≫
                prod.map (𝟙 _) ((Over.map (f j)).map ((Over.pullback (f j)).map g)) :=
          ((CanonicalDatum.functor f).map g).comm i j
        rw [prod.map_map_assoc, ← Functor.map_comp, ha i g hg, Category.comp_id,
          reassoc_of% hg₁, prod.map_snd, reassoc_of% hg₂, prod.map_snd_assoc,
          ← Functor.map_comp, ha j g hg]
  refine ⟨⟨a, hcomm⟩, fun T' g hg ↦ ?_, fun ψ hψ ↦ ?_⟩
  · exact hom_ext fun i ↦ ha i g hg
  · refine hom_ext fun i ↦ ((hP i) R hR).isSeparatedFor.ext ?_
    intro T' g hg
    change (Over.pullback (f i)).map g ≫ ψ.hom i = (Over.pullback (f i)).map g ≫ a i
    rw [ha i g hg]
    exact congrArg (fun φ ↦ φ.hom i) (hψ g hg)

end Sheaf

/-! ### Faithfulness -/

lemma toPresheafFunctor_map_app {D D' : DescentData f} (α : D ⟶ D') {T : Over S}
    (ψ : (CanonicalDatum.functor f).obj T ⟶ D) :
    ((toPresheafFunctor f).map α).app (op T) ψ = ψ ≫ α := rfl

instance faithful_toPresheafFunctor : (toPresheafFunctor f).Faithful where
  map_injective {D D'} α β h := by
    refine hom_ext fun i ↦ ?_
    have h' : D.eval i ≫ α = D.eval i ≫ β :=
      congrArg (fun η ↦ η.app (op (D.overBase i)) (D.eval i)) h
    rw [eval_comp, eval_comp] at h'
    apply over_hom_ext_of_map (f i)
    apply (D'.representableBy i).homEquiv.injective
    rw [representableBy_homEquiv_apply, representableBy_homEquiv_apply, map_comp_structureMap,
      map_comp_structureMap, h']

/-! ### Coverings by the canonical components -/

section Covering

variable {J : GrothendieckTopology Scheme.{u}} (hf : Sieve.ofArrows X f ∈ J S)
include hf

/-- The fibre products `T ×_S X i` cover `T` in `(Sch/S)_J`. -/
lemma ofArrows_originalProjection_mem (T : Over S) :
    Sieve.ofArrows (fun i ↦ component T (f i)) (fun i ↦ originalProjection T (f i)) ∈
      J.over S T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  refine J.superset_covering ?_ (J.pullback_stable T.hom hf)
  rintro W g ⟨Y, a, b, ⟨i⟩, hab⟩
  exact ⟨_, pullback.lift g a hab.symm, pullback.fst _ _, ⟨i⟩, pullback.lift_fst _ _ _⟩

lemma isSheafFor_ofArrows {P : (Over S)ᵒᵖ ⥤ Type u} (hP : Presieve.IsSheaf (J.over S) P)
    (T : Over S) :
    (Presieve.ofArrows (fun i ↦ component T (f i))
      (fun i ↦ originalProjection T (f i))).IsSheafFor P :=
  (Presieve.isSheafFor_iff_generate _).2 (hP _ (ofArrows_originalProjection_mem hf T))

lemma ext_of_ofArrows {P : (Over S)ᵒᵖ ⥤ Type u} (hP : Presieve.IsSheaf (J.over S) P)
    {T : Over S} {t₁ t₂ : P.obj (op T)}
    (h : ∀ i, P.map (originalProjection T (f i)).op t₁ =
      P.map (originalProjection T (f i)).op t₂) :
    t₁ = t₂ :=
  (isSheafFor_ofArrows hf hP T).isSeparatedFor.ext (by rintro _ _ ⟨i⟩; exact h i)

end Covering

/-! ### Fullness -/

section Full

variable {J : GrothendieckTopology Scheme.{u}} [J.Subcanonical] (hf : Sieve.ofArrows X f ∈ J S)
include hf

/-- The functor from descent data to presheaves is full. -/
theorem full_toPresheafFunctor : (toPresheafFunctor f).Full where
  map_surjective {D D'} η := by
    have hη : ∀ {T T' : Over S} (g : T' ⟶ T) (ψ : (CanonicalDatum.functor f).obj T ⟶ D),
        η.app (op T') ((CanonicalDatum.functor f).map g ≫ ψ) =
          (CanonicalDatum.functor f).map g ≫ η.app (op T) ψ :=
      fun g ψ ↦ NatTrans.naturality_apply η g.op ψ
    choose m hm using fun i ↦ (D'.representableBy i).homEquiv.surjective
      (structureMap (f i) (D.obj i), η.app (op (D.overBase i)) (D.eval i))
    have hm₁ : ∀ i, m i ≫ structureMap (f i) (D'.obj i) = structureMap (f i) (D.obj i) :=
      fun i ↦ congrArg Prod.fst (hm i)
    have hm₂ : ∀ i, (CanonicalDatum.functor f).map (m i) ≫ D'.eval i =
        η.app (op (D.overBase i)) (D.eval i) := fun i ↦ congrArg Prod.snd (hm i)
    have hcomm : ∀ i j, prod.map (m i) (𝟙 (Over.mk (f j))) ≫ (D'.gluing i j).hom.left =
        (D.gluing i j).hom.left ≫ prod.map (𝟙 (Over.mk (f i))) (m j) := by
      intro i j
      apply prod.hom_ext
      · simp [hm₁]
      · simp only [Category.assoc, prod.map_snd]
        apply (D'.representableBy j).homEquiv.injective
        rw [representableBy_homEquiv_apply, representableBy_homEquiv_apply]
        refine Prod.ext ?_ ?_
        · simp [hm₁]
        · have L : (CanonicalDatum.functor f).map (prod.map (m i) (𝟙 (Over.mk (f j))) ≫
              (D'.gluing i j).hom.left ≫ prod.snd) ≫ D'.eval j =
                η.app (op (D.overBase i ⨯ Over.mk (f j)))
                  ((CanonicalDatum.functor f).map prod.fst ≫ D.eval i) := by
            rw [Functor.map_comp_assoc, map_gluing_snd_eval, ← Functor.map_comp_assoc,
              prod.map_fst, Functor.map_comp_assoc, hm₂, hη]
          have R : (CanonicalDatum.functor f).map ((D.gluing i j).hom.left ≫ prod.snd ≫ m j) ≫
              D'.eval j = η.app (op (D.overBase i ⨯ Over.mk (f j)))
                ((CanonicalDatum.functor f).map prod.fst ≫ D.eval i) := by
            rw [← map_gluing_snd_eval, hη, ← hm₂, ← Functor.map_comp_assoc, Category.assoc]
          exact L.trans R.symm
    refine ⟨{ hom := fun i ↦ overHomOfMap (f i) (m i) (hm₁ i), comm := fun i j ↦ hcomm i j }, ?_⟩
    ext T ψ
    obtain ⟨T⟩ := T
    change (CanonicalDatum.functor f).obj T ⟶ D at ψ
    change ψ ≫ _ = η.app (op T) ψ
    refine ext_of_ofArrows hf (isSheaf_toPresheaf J D') fun i ↦ ?_
    change (CanonicalDatum.functor f).map (originalProjection T (f i)) ≫ ψ ≫ _ =
      (CanonicalDatum.functor f).map (originalProjection T (f i)) ≫ η.app (op T) ψ
    obtain ⟨v, hv⟩ := (D.representableBy i).homEquiv.surjective
      (structureMap (f i) ((Over.pullback (f i)).obj T),
        (CanonicalDatum.functor f).map (originalProjection T (f i)) ≫ ψ)
    have hv₂ : (CanonicalDatum.functor f).map v ≫ D.eval i =
        (CanonicalDatum.functor f).map (originalProjection T (f i)) ≫ ψ := congrArg Prod.snd hv
    rw [← Category.assoc, ← hv₂, Category.assoc, eval_comp, ← hη, ← hv₂, hη, ← hm₂]
    rfl

end Full


/-! ### The canonical descent datum functor is fully faithful -/

/-- The `i`-th component of a morphism between canonical descent data. -/
def canMapComp {T Z : Over S}
    (ψ : (CanonicalDatum.functor f).obj T ⟶ (CanonicalDatum.functor f).obj Z) (i : ι) :
    (Over.pullback (f i)).obj T ⟶ (Over.pullback (f i)).obj Z :=
  ψ.hom i

lemma canMapComp_comm {T Z : Over S}
    (ψ : (CanonicalDatum.functor f).obj T ⟶ (CanonicalDatum.functor f).obj Z) (i j : ι) :
    prod.map ((Over.map (f i)).map (canMapComp ψ i)) (𝟙 (Over.mk (f j))) ≫
        transition Z (f i) (f j) =
      transition T (f i) (f j) ≫ prod.map (𝟙 _) ((Over.map (f j)).map (canMapComp ψ j)) :=
  ψ.comm i j

section Canonical

variable {J : GrothendieckTopology Scheme.{u}} [J.Subcanonical] (hf : Sieve.ofArrows X f ∈ J S)
include hf

/-- Morphisms of schemes over `S` are determined by their base changes to the members of a
covering family. -/
theorem faithful_canonicalFunctor : (CanonicalDatum.functor f).Faithful where
  map_injective {T Z} a b h := by
    refine ext_of_ofArrows hf (P := yoneda.obj Z)
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J.over S) _)
      fun i ↦ ?_
    change originalProjection T (f i) ≫ a = originalProjection T (f i) ≫ b
    have e : (Over.map (f i)).map ((Over.pullback (f i)).map a) =
        (Over.map (f i)).map ((Over.pullback (f i)).map b) :=
      congrArg (fun φ ↦ (Over.map (f i)).map (φ.hom i)) h
    rw [← componentMap_original, e, componentMap_original]

/-- Morphisms between canonical descent data of schemes over `S` descend. -/
theorem full_canonicalFunctor : (CanonicalDatum.functor f).Full where
  map_surjective {T Z} ψ := by
    have hZ := isSheafFor_ofArrows hf (P := yoneda.obj Z)
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J.over S) _) T
    rw [Presieve.isSheafFor_arrows_iff] at hZ
    obtain ⟨a, ha, -⟩ := hZ
      (fun i ↦ (Over.map (f i)).map (canMapComp ψ i) ≫ originalProjection Z (f i))
      (by
        intro i j W b₁ b₂ hb
        change b₁ ≫ (Over.map (f i)).map (canMapComp ψ i) ≫ originalProjection Z (f i) =
          b₂ ≫ (Over.map (f j)).map (canMapComp ψ j) ≫ originalProjection Z (f j)
        have hc := canMapComp_comm ψ i j
        have e : componentLift (b₁ ≫ originalProjection T (f i))
            (b₂ ≫ structureMap (f j) ((Over.pullback (f j)).obj T)) = b₂ := by
          apply component_hom_ext <;> simp [hb]
        have h₁ := congrArg (fun t ↦ prod.lift b₁
          (b₂ ≫ structureMap (f j) ((Over.pullback (f j)).obj T)) ≫ t ≫ prod.snd ≫
            originalProjection Z (f j)) hc
        dsimp only at h₁
        rw [Category.assoc, Category.assoc, transition_original, prod.map_fst_assoc,
          prod.lift_fst_assoc, prod.map_snd_assoc, lift_transition_snd_assoc, e] at h₁
        exact h₁)
    refine ⟨a, hom_ext fun i ↦ over_hom_ext_of_map (f i) ?_⟩
    change (Over.map (f i)).map ((Over.pullback (f i)).map a) =
      (Over.map (f i)).map (canMapComp ψ i)
    apply component_hom_ext
    · rw [componentMap_original]
      exact ha i
    · rw [componentMap_structure, map_comp_structureMap]

end Canonical

/-! ### Essential surjectivity -/

section EssSurj

variable {P : (Over S)ᵒᵖ ⥤ Type u}

variable (f P) in
/-- A representation of `h_{X i} × P` by a scheme over `X i`, normalized so that its projection to
`h_{X i}` is the structure map. -/
structure LocalRep (i : ι) where
  /-- The representing scheme over `X i`. -/
  obj : Over (X i)
  /-- The representation. -/
  rep : (FunctorToTypes.prod (yoneda.obj (Over.mk (f i))) P).RepresentableBy
    ((Over.map (f i)).obj obj)
  rep_fst : (rep.homEquiv (𝟙 _)).1 = structureMap (f i) obj

namespace LocalRep

variable {i : ι} (R : LocalRep f P i)

/-- The tautological section of `P` over the representing scheme. -/
def sect : P.obj (op ((Over.map (f i)).obj R.obj)) := (R.rep.homEquiv (𝟙 _)).2

lemma homEquiv_apply {V : Over S} (v : V ⟶ (Over.map (f i)).obj R.obj) :
    R.rep.homEquiv v = (v ≫ structureMap (f i) R.obj, P.map v.op R.sect) := by
  rw [Functor.RepresentableBy.prod_homEquiv_eq, R.rep_fst]
  rfl

lemma hom_ext {V : Over S} {v w : V ⟶ (Over.map (f i)).obj R.obj}
    (h₁ : v ≫ structureMap (f i) R.obj = w ≫ structureMap (f i) R.obj)
    (h₂ : P.map v.op R.sect = P.map w.op R.sect) : v = w :=
  R.rep.homEquiv.injective (by rw [R.homEquiv_apply, R.homEquiv_apply, h₁, h₂])

/-- The morphism to the representing scheme given by a morphism to `X i` and a section. -/
def lift {V : Over S} (q : V ⟶ Over.mk (f i)) (s : P.obj (op V)) :
    V ⟶ (Over.map (f i)).obj R.obj :=
  R.rep.homEquiv.symm (q, s)

lemma homEquiv_lift {V : Over S} (q : V ⟶ Over.mk (f i)) (s : P.obj (op V)) :
    R.rep.homEquiv (R.lift q s) = (q, s) :=
  R.rep.homEquiv.apply_symm_apply _

@[reassoc (attr := simp)]
lemma lift_structureMap {V : Over S} (q : V ⟶ Over.mk (f i)) (s : P.obj (op V)) :
    R.lift q s ≫ structureMap (f i) R.obj = q := by
  have := R.homEquiv_lift q s
  rw [R.homEquiv_apply] at this
  exact congrArg Prod.fst this

@[simp]
lemma map_lift_sect {V : Over S} (q : V ⟶ Over.mk (f i)) (s : P.obj (op V)) :
    P.map (R.lift q s).op R.sect = s := by
  have := R.homEquiv_lift q s
  rw [R.homEquiv_apply] at this
  exact congrArg Prod.snd this

@[simp]
lemma comp_lift {V V' : Over S} (a : V' ⟶ V) (q : V ⟶ Over.mk (f i)) (s : P.obj (op V)) :
    a ≫ R.lift q s = R.lift (a ≫ q) (P.map a.op s) :=
  R.hom_ext (by simp) (by simp)

/-- The representing object of a representation of `h_{X i} × P`, read over `X i`. -/
def isoObjOfRepresentableBy {Z : Over S}
    (r : (FunctorToTypes.prod (yoneda.obj (Over.mk (f i))) P).RepresentableBy Z) :
    (Over.map (f i)).obj (Over.mk (r.homEquiv (𝟙 Z)).1.left) ≅ Z :=
  Over.isoMk (Iso.refl _) (by simpa using (Over.w (r.homEquiv (𝟙 Z)).1).symm)

/-- A representation of `h_{X i} × P` can be normalized. -/
def ofRepresentableBy {Z : Over S}
    (r : (FunctorToTypes.prod (yoneda.obj (Over.mk (f i))) P).RepresentableBy Z) :
    LocalRep f P i where
  obj := Over.mk (r.homEquiv (𝟙 Z)).1.left
  rep := r.ofIsoObj (isoObjOfRepresentableBy r)
  rep_fst := by
    have h := congrArg Prod.fst (r.prod_homEquiv_eq (isoObjOfRepresentableBy r).hom)
    refine (congrArg (fun u ↦ (r.homEquiv u).1) (Category.id_comp _)).trans (h.trans ?_)
    exact Over.OverMorphism.ext (by simp [isoObjOfRepresentableBy])

lemma nonempty (h : (yoneda.obj (Over.mk (f i)) ⨯ P).IsRepresentable) :
    Nonempty (LocalRep f P i) := by
  obtain ⟨Z, ⟨r⟩⟩ := h.has_representation
  exact ⟨ofRepresentableBy (r.ofIso (FunctorToTypes.binaryProductIso _ _))⟩

end LocalRep

variable (R : ∀ i, LocalRep f P i)

/-- The gluing map `V_i ×_S X_j ⟶ X_i ×_S V_j` of local representations: both represent
`h_{X i} × P × h_{X j}`. -/
def gl (i j : ι) : (Over.map (f i)).obj (R i).obj ⨯ Over.mk (f j) ⟶
    Over.mk (f i) ⨯ (Over.map (f j)).obj (R j).obj :=
  prod.lift (prod.fst ≫ structureMap (f i) (R i).obj)
    ((R j).lift prod.snd (P.map prod.fst.op (R i).sect))

@[reassoc (attr := simp)]
lemma gl_fst (i j : ι) : gl R i j ≫ prod.fst = prod.fst ≫ structureMap (f i) (R i).obj :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
lemma gl_snd (i j : ι) :
    gl R i j ≫ prod.snd = (R j).lift prod.snd (P.map prod.fst.op (R i).sect) :=
  prod.lift_snd _ _

@[simp]
lemma map_gl_map_snd_apply (i j : ι) (t : P.obj (op ((Over.map (f j)).obj (R j).obj))) :
    P.map (gl R i j).op (P.map prod.snd.op t) =
      P.map ((R j).lift prod.snd (P.map prod.fst.op (R i).sect)).op t := by
  have h := congrArg (fun h ↦ P.map h.op t) (gl_snd R i j)
  simp only [op_comp, Functor.map_comp_apply] at h
  exact h

@[simp]
lemma map_gl_map_fst_apply (i j : ι) (t : P.obj (op (Over.mk (f i)))) :
    P.map (gl R i j).op (P.map prod.fst.op t) =
      P.map prod.fst.op (P.map (structureMap (f i) (R i).obj).op t) := by
  have h := congrArg (fun h ↦ P.map h.op t) (gl_fst R i j)
  simp only [op_comp, Functor.map_comp_apply] at h
  exact h

/-- The inverse of `gl`. -/
def glInv (i j : ι) : Over.mk (f i) ⨯ (Over.map (f j)).obj (R j).obj ⟶
    (Over.map (f i)).obj (R i).obj ⨯ Over.mk (f j) :=
  prod.lift ((R i).lift prod.fst (P.map prod.snd.op (R j).sect))
    (prod.snd ≫ structureMap (f j) (R j).obj)

@[reassoc (attr := simp)]
lemma glInv_fst (i j : ι) :
    glInv R i j ≫ prod.fst = (R i).lift prod.fst (P.map prod.snd.op (R j).sect) :=
  prod.lift_fst _ _

@[reassoc (attr := simp)]
lemma glInv_snd (i j : ι) : glInv R i j ≫ prod.snd = prod.snd ≫ structureMap (f j) (R j).obj :=
  prod.lift_snd _ _

@[simp]
lemma map_glInv_map_fst_apply (i j : ι) (t : P.obj (op ((Over.map (f i)).obj (R i).obj))) :
    P.map (glInv R i j).op (P.map prod.fst.op t) =
      P.map ((R i).lift prod.fst (P.map prod.snd.op (R j).sect)).op t := by
  have h := congrArg (fun h ↦ P.map h.op t) (glInv_fst R i j)
  simp only [op_comp, Functor.map_comp_apply] at h
  exact h

/-- The gluing isomorphism of local representations. -/
def glIso (i j : ι) : (Over.map (f i)).obj (R i).obj ⨯ Over.mk (f j) ≅
    Over.mk (f i) ⨯ (Over.map (f j)).obj (R j).obj where
  hom := gl R i j
  inv := glInv R i j
  hom_inv_id := by
    apply prod.hom_ext
    · apply (R i).hom_ext <;> simp
    · simp
  inv_hom_id := by
    apply prod.hom_ext
    · simp
    · apply (R j).hom_ext <;> simp

/-- The descent datum of local representations. -/
abbrev descentDatum : DescentData f where
  obj i := (R i).obj
  gluing i j := Over.isoMk (glIso R i j) (by apply prod.hom_ext <;> simp [glIso])
  cocycle i j k := by
    change prod.map (gl R i j) (𝟙 _) ≫ prodMapLastTwo (gl R j k) = prodMapFirstThird (gl R i k)
    apply prod.hom_ext
    · apply prod.hom_ext <;> simp [prodMapLastTwo, prodMapFirstThird]
    · apply (R k).hom_ext <;> simp [prodMapLastTwo, prodMapFirstThird]

/-- The morphism of descent data attached to a section of `P` over `T`. -/
def toHom (T : Over S) (x : P.obj (op T)) :
    (CanonicalDatum.functor f).obj T ⟶ descentDatum R where
  hom i := overHomOfMap (f i) ((R i).lift (structureMap (f i) ((Over.pullback (f i)).obj T))
    (P.map (originalProjection T (f i)).op x))
    ((R i).lift_structureMap (structureMap (f i) ((Over.pullback (f i)).obj T))
      (P.map (originalProjection T (f i)).op x))
  comm i j := by
    change prod.map ((R i).lift (structureMap (f i) ((Over.pullback (f i)).obj T))
        (P.map (originalProjection T (f i)).op x)) (𝟙 _) ≫ gl R i j =
      transition T (f i) (f j) ≫ prod.map (𝟙 _) ((R j).lift
        (structureMap (f j) ((Over.pullback (f j)).obj T))
          (P.map (originalProjection T (f j)).op x))
    apply prod.hom_ext
    · simp
    · apply (R j).hom_ext <;> simp

lemma map_toHom_hom (T : Over S) (x : P.obj (op T)) (i : ι) :
    (Over.map (f i)).map (canComp (toHom R T x) i) =
      (R i).lift (structureMap (f i) ((Over.pullback (f i)).obj T))
        (P.map (originalProjection T (f i)).op x) :=
  Over.OverMorphism.ext rfl

lemma toHom_naturality {T T' : Over S} (g : T' ⟶ T) (x : P.obj (op T)) :
    toHom R T' (P.map g.op x) = (CanonicalDatum.functor f).map g ≫ toHom R T x := by
  refine canHom_ext fun i ↦ over_hom_ext_of_map (f i) ?_
  rw [canComp_map_comp, Functor.map_comp, map_toHom_hom, map_toHom_hom]
  apply (R i).hom_ext
  · rw [LocalRep.lift_structureMap, Category.assoc, LocalRep.lift_structureMap,
      componentMap_structure]
  · rw [LocalRep.comp_lift, LocalRep.map_lift_sect, LocalRep.map_lift_sect,
      map_componentMap_map_original_apply]

variable {J : GrothendieckTopology Scheme.{u}} (hf : Sieve.ofArrows X f ∈ J S)
include hf

lemma toHom_bijective (hP : Presieve.IsSheaf (J.over S) P) (T : Over S) :
    Function.Bijective (toHom R T) := by
  constructor
  · intro x y h
    refine ext_of_ofArrows hf hP fun i ↦ ?_
    have e := congrArg (fun φ ↦ P.map ((Over.map (f i)).map (canComp φ i)).op (R i).sect) h
    simpa only [map_toHom_hom, LocalRep.map_lift_sect] using e
  · intro ψ
    have hT := isSheafFor_ofArrows hf hP T
    rw [Presieve.isSheafFor_arrows_iff] at hT
    obtain ⟨x, hx, -⟩ := hT (fun i ↦ P.map ((Over.map (f i)).map (canComp ψ i)).op (R i).sect) (by
      intro i j W b₁ b₂ hb
      have hc : prod.map ((Over.map (f i)).map (canComp ψ i)) (𝟙 (Over.mk (f j))) ≫ gl R i j =
          transition T (f i) (f j) ≫ prod.map (𝟙 _) ((Over.map (f j)).map (canComp ψ j)) :=
        canComp_comm ψ i j
      have e : componentLift (b₁ ≫ originalProjection T (f i))
          (b₂ ≫ structureMap (f j) ((Over.pullback (f j)).obj T)) = b₂ := by
        apply component_hom_ext <;> simp [hb]
      have key : b₂ ≫ (Over.map (f j)).map (canComp ψ j) =
          prod.lift (b₁ ≫ (Over.map (f i)).map (canComp ψ i))
            (b₂ ≫ structureMap (f j) ((Over.pullback (f j)).obj T)) ≫ gl R i j ≫ prod.snd := by
        have h₁ := congrArg (fun t ↦ prod.lift b₁
          (b₂ ≫ structureMap (f j) ((Over.pullback (f j)).obj T)) ≫ t ≫ prod.snd) hc
        dsimp only at h₁
        rw [Category.assoc, Category.assoc, prod.map_snd, lift_transition_snd_assoc, e,
          ← Category.assoc, prod.lift_map, Category.comp_id] at h₁
        exact h₁.symm
      have := congrArg (fun v ↦ P.map v.op (R j).sect) key
      simp only [op_comp, Functor.map_comp_apply, gl_snd, LocalRep.comp_lift,
        LocalRep.map_lift_sect, map_prodLift_map_fst_apply] at this
      exact this.symm)
    refine ⟨x, canHom_ext fun i ↦ over_hom_ext_of_map (f i) ?_⟩
    rw [map_toHom_hom]
    apply (R i).hom_ext
    · rw [LocalRep.lift_structureMap, map_comp_structureMap]
    · rw [LocalRep.map_lift_sect, hx i]

/-- A sheaf is isomorphic to the presheaf of the descent datum of its local representations. -/
def presheafIso (hP : Presieve.IsSheaf (J.over S) P) : P ≅ (descentDatum R).toPresheaf :=
  NatIso.ofComponents
    (fun T ↦ (Equiv.ofBijective (toHom R T.unop) (toHom_bijective R hf hP T.unop)).toIso)
    (by
      intro T T' g
      ext x
      exact toHom_naturality R g.unop x)

end EssSurj

/-! ### The equivalence -/

/-- The sheaves `F` on `(Sch/S)_J` such that every product `h_{X i} × F` is representable. -/
def sheavesLocallyRepresentable (J : GrothendieckTopology Scheme.{u}) (f : ∀ i, X i ⟶ S) :
    ObjectProperty (Sheaf (J.over S) (Type u)) :=
  fun F ↦ ∀ i, (yoneda.obj (Over.mk (f i)) ⨯ F.obj).IsRepresentable

/-- The functor from descent data to sheaves, sending `D` to `T ↦ Hom(can T, D)`. -/
def toSheaf (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical] (f : ∀ i, X i ⟶ S) :
    DescentData f ⥤ (sheavesLocallyRepresentable J f).FullSubcategory :=
  (sheavesLocallyRepresentable J f).lift
    (ObjectProperty.lift (Presheaf.IsSheaf (J.over S) (A := Type u)) (toPresheafFunctor f)
      fun D ↦ (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_toPresheaf J D))
    fun D i ↦
      ((D.representableBy i).ofIso (FunctorToTypes.binaryProductIso _ _).symm).isRepresentable

variable {J : GrothendieckTopology Scheme.{u}} [J.Subcanonical]

instance : (toSheaf J f).Faithful where
  map_injective h := (toPresheafFunctor f).map_injective (congrArg (fun φ ↦ φ.hom.hom) h)

variable (hf : Sieve.ofArrows X f ∈ J S)
include hf

theorem full_toSheaf : (toSheaf J f).Full where
  map_surjective {D D'} φ := by
    have := full_toPresheafFunctor hf
    obtain ⟨α, hα⟩ := (toPresheafFunctor f).map_surjective φ.hom.hom
    exact ⟨α, ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ hα)⟩

theorem essSurj_toSheaf : (toSheaf J f).EssSurj where
  mem_essImage G := by
    have R : ∀ i, LocalRep f G.obj.obj i := fun i ↦ (LocalRep.nonempty (G.property i)).some
    have hP : Presieve.IsSheaf (J.over S) G.obj.obj :=
      (isSheaf_iff_isSheaf_of_type _ _).1 G.obj.property
    exact ⟨descentDatum R, ⟨ObjectProperty.isoMk _ (ObjectProperty.isoMk _
      (presheafIso R hf hP).symm)⟩⟩

end DescentData

/-! ### Stacks 02W5 -/

namespace DescentData

open CanonicalDatum

variable {ι : Type u} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
  {J : GrothendieckTopology Scheme.{u}} [J.Subcanonical] (hf : Sieve.ofArrows X f ∈ J S)

/-- **Stacks 02W5.** Let `J` be a subcanonical topology on the category of schemes (for instance
the Zariski, étale, smooth, syntomic or fppf topology), let `S` be a scheme and let
`{f i : X i ⟶ S}` be a `J`-covering of `S`. Then descent data `(V_i, φ_ij)` of schemes relative to
`{f i}` are equivalent to sheaves `F` on `(Sch/S)_J` such that every product `h_{X i} × F` is
representable. The functor sends `D` to the sheaf `T ↦ Hom(can T, D)` of morphisms of descent
data out of the canonical descent datum of `T`. -/
@[stacks 02W5 "the equivalence of categories"]
noncomputable def sheafEquivalence :
    DescentData f ≌ (sheavesLocallyRepresentable J f).FullSubcategory :=
  haveI := full_toSheaf hf
  haveI := essSurj_toSheaf hf
  haveI : (toSheaf J f).IsEquivalence := {}
  (toSheaf J f).asEquivalence

lemma sheafEquivalence_functor : (sheafEquivalence hf).functor = toSheaf J f := rfl

/-- **Stacks 02W5, part (1)**, from left to right: for a descent datum `(V_i, φ_ij)`, the product
`h_{X i} × F` with the corresponding sheaf `F` is represented by `V_i`, viewed as a scheme over
`S`. -/
@[stacks 02W5 "part (1): the objects representing `h_{S_i} × F` are the schemes `X_i`"]
noncomputable def representableBy_sheafEquivalence_functor (D : DescentData f) (i : ι) :
    (yoneda.obj (Over.mk (f i)) ⨯ ((sheafEquivalence hf).functor.obj D).obj.obj).RepresentableBy
      ((Over.map (f i)).obj (D.obj i)) :=
  (D.representableBy i).ofIso (FunctorToTypes.binaryProductIso _ _).symm

/-- **Stacks 02W5, part (1)**, from right to left: for a sheaf `F` on `(Sch/S)_J` with every
`h_{X i} × F` representable, the product `h_{X i} × F` is represented by the `i`-th component of
the corresponding descent datum, viewed as a scheme over `S`. -/
@[stacks 02W5 "part (1), from sheaves to descent data"]
noncomputable def representableBy_sheafEquivalence_inverse
    (F : (sheavesLocallyRepresentable J f).FullSubcategory) (i : ι) :
    (yoneda.obj (Over.mk (f i)) ⨯ F.obj.obj).RepresentableBy
      ((Over.map (f i)).obj (((sheafEquivalence hf).inverse.obj F).obj i)) :=
  (representableBy_sheafEquivalence_functor hf ((sheafEquivalence hf).inverse.obj F) i).ofIso
    (prod.mapIso (Iso.refl _) ((sheafToPresheaf _ _).mapIso
      ((ObjectProperty.ι _).mapIso ((sheafEquivalence hf).counitIso.app F))))

/-- **Stacks 02W5, part (2)**: the sheaf corresponding to a descent datum is representable if and
only if the descent datum is effective. -/
@[stacks 02W5 "part (2): `F` is representable if and only if the descent datum is effective"]
theorem isRepresentable_sheafEquivalence_functor_iff (D : DescentData f) :
    ((sheafEquivalence hf).functor.obj D).obj.obj.IsRepresentable ↔ D.IsFamilyEffective := by
  have := full_canonicalFunctor hf
  have := faithful_canonicalFunctor hf
  have := full_toPresheafFunctor hf
  let hff : (CanonicalDatum.functor f).FullyFaithful := .ofFullyFaithful _
  let hN : (toPresheafFunctor f).FullyFaithful := .ofFullyFaithful _
  let yIso : ∀ Z : Over S,
      yoneda.obj Z ≅ (toPresheafFunctor f).obj ((CanonicalDatum.functor f).obj Z) := fun Z ↦
    NatIso.ofComponents (fun T ↦ (hff.homEquiv (X := T.unop) (Y := Z)).toIso) (by
      intro T T' g
      ext a
      change (CanonicalDatum.functor f).map (g.unop ≫ a) =
        (CanonicalDatum.functor f).map g.unop ≫ (CanonicalDatum.functor f).map a
      exact Functor.map_comp _ _ _)
  change D.toPresheaf.IsRepresentable ↔ (CanonicalDatum.functor f).essImage D
  constructor
  · rintro ⟨Z, ⟨r⟩⟩
    exact ⟨Z, ⟨hN.preimageIso ((yIso Z).symm ≪≫ r.toIso)⟩⟩
  · rintro ⟨Z, ⟨e⟩⟩
    exact Functor.IsRepresentable.mk' (yIso Z ≪≫ (toPresheafFunctor f).mapIso e)

/-- **Stacks 02W5, part (2)**, from the side of sheaves: a sheaf `F` on `(Sch/S)_J` with every
`h_{X i} × F` representable is representable if and only if the corresponding descent datum is
effective. -/
@[stacks 02W5 "part (2), from sheaves to descent data"]
theorem isRepresentable_iff_isFamilyEffective_sheafEquivalence_inverse
    (F : (sheavesLocallyRepresentable J f).FullSubcategory) :
    F.obj.obj.IsRepresentable ↔ ((sheafEquivalence hf).inverse.obj F).IsFamilyEffective := by
  rw [← isRepresentable_sheafEquivalence_functor_iff hf]
  let e := (sheafToPresheaf _ _).mapIso
    ((ObjectProperty.ι _).mapIso ((sheafEquivalence hf).counitIso.app F))
  constructor
  · rintro ⟨Z, ⟨r⟩⟩
    exact (r.ofIso e.symm).isRepresentable
  · rintro ⟨Z, ⟨r⟩⟩
    exact (r.ofIso e).isRepresentable

end DescentData

end AlgebraicGeometry
