module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equifibered
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Simplicial.GroupoidNerve
import StacksCore.Tactic.StacksAttribute

/-!
# The cartesian map from the Čech nerve of the source of a groupoid scheme

For a groupoid scheme `G` over a base scheme, the Čech nerve of its source morphism maps to the
nerve of `G`. On vertices this map is the target morphism, and on successive edges it sends a
pair of arrows with a common source to their quotient. Every naturality square of this
simplicial morphism is cartesian.

The map is defined degreewise through the functor-of-points description of the nerve supplied by
`Stacks.Groupoids.GroupoidScheme.GroupoidSimplicialScheme`: a string of `n + 1` arrows out of a
common source, which is what a generalized point of the degree-`n` Čech object is, is sent to
the string whose successive arrows are `rᵢ ∘ rᵢ₊₁⁻¹`. Each square in which one leg is a vertex
of the simplex is cartesian because a simplex of the nerve together with one arrow over a chosen
vertex lifts uniquely to a simplex of the Čech nerve; the general naturality square then follows
by composing two such.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.CartesianTargetMap`: a cartesian simplicial morphism from the
  Čech nerve of the source to the nerve, together with its vertex and edge formulas.

## Main results

* `Stacks.Groupoids.GroupoidScheme.groupoidCechNerveTarget`: the canonical such morphism.

## Implementation notes

The degree-`n` formula is expressed on generalized points, through the natural description of
the nerve of a groupoid scheme; the formula in degree zero is recorded separately. Being a
natural transformation already supplies compatibility with all faces and degeneracies.

## References

* [Stacks Project, Tag 07TQ](https://stacks.math.columbia.edu/tag/07TQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject

universe u

namespace Stacks.Groupoids.GroupoidScheme

/-- A family of arrows with a common source determines a simplex of the opposite groupoid. -/
@[implicit_reducible] private noncomputable def quotientComposableArrows {C : Type*} [Groupoid C]
    {n : ℕ} {b : C} (v : Fin (n + 1) → C) (r : ∀ i, b ⟶ v i) :
    ComposableArrows Cᵒᵖ n where
  obj i := op (v i)
  map {i j} _ := (Groupoid.inv (r j) ≫ r i).op
  map_id i := by simp
  map_comp {i j k} f g := by
    apply Quiver.Hom.unop_inj
    simp [← Category.assoc]

private lemma evaluation_transport {S : Scheme.{u}}
    {G : GroupoidScheme S} {T : Over S}
    {a b c d : (G.Evaluation T)ᵒᵖ} (h : a = b) (k : c = d) (f : b ⟶ c) :
    (eqToHom h ≫ f ≫ eqToHom k).unop.arrow = f.unop.arrow := by
  subst b d
  simp

private lemma pointFunctor_ext {S : Scheme.{u}}
    {G : GroupoidScheme S} {T : Over S} {n : ℕ}
    {F H : ComposableArrows (G.Evaluation T)ᵒᵖ n}
    (ho : ∀ i, (F.obj i).unop = (H.obj i).unop)
    (hm : ∀ i j (h : i ≤ j), (F.map (homOfLE h)).unop.arrow =
      (H.map (homOfLE h)).unop.arrow) : F = H := by
  apply ComposableArrows.ext (fun i => unop_injective (ho i))
  intro i hi
  apply Quiver.Hom.unop_inj
  apply EvaluationHom.ext
  rw [evaluation_transport]
  exact hm _ _ _

private noncomputable abbrev cechObj {S : Scheme.{u}} (G : GroupoidScheme S) (n : ℕ) :=
  (Arrow.mk G.source).cechNerve.obj (op (SimplexCategory.mk n))

private noncomputable def cechArrow {S : Scheme.{u}}
    (G : GroupoidScheme S) {n : ℕ} {T : Over S}
    (x : T ⟶ cechObj G n) (i : Fin (n + 1)) :
    (show G.Evaluation T from x ≫ WidePullback.base (fun _ : Fin (n + 1) => G.source)) ⟶
      (show G.Evaluation T from
        x ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) i ≫ G.target) where
  arrow := x ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) i
  source_eq := by simp only [Category.assoc, WidePullback.π_arrow]
  target_eq := Category.assoc _ _ _

private noncomputable def cechPointFunctor {S : Scheme.{u}}
    (G : GroupoidScheme S) {n : ℕ} {T : Over S}
    (x : T ⟶ cechObj G n) : ComposableArrows (G.Evaluation T)ᵒᵖ n :=
  quotientComposableArrows _ (cechArrow G x)

private lemma cechPointFunctor_obj {S : Scheme.{u}}
    (G : GroupoidScheme S) {n : ℕ} {T : Over S}
    (x : T ⟶ cechObj G n) (i : Fin (n + 1)) :
    ((cechPointFunctor G x).obj i).unop =
      x ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) i ≫ G.target := rfl

private lemma cechPointFunctor_map {S : Scheme.{u}}
    (G : GroupoidScheme S) {n : ℕ} {T : Over S}
    (x : T ⟶ cechObj G n) (i j : Fin (n + 1)) (h : i ≤ j) :
    ((cechPointFunctor G x).map (homOfLE h)).unop.arrow =
      G.compose (x ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) i)
        ((x ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) j) ≫ G.inverse)
        (by simp only [Category.assoc, G.target_inverse, WidePullback.π_arrow]) := rfl

private lemma compose_precomp {S : Scheme.{u}}
    (G : GroupoidScheme S) {T T' : Over S}
    (f : T' ⟶ T) (a b : T ⟶ G.arrows) (w : a ≫ G.source = b ≫ G.target) :
    f ≫ G.compose a b w = G.compose (f ≫ a) (f ≫ b)
      (by simp only [Category.assoc, w]) := by
  dsimp [GroupoidScheme.compose]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst,
    pullback.lift_snd]

private noncomputable def cechDegreeMap {S : Scheme.{u}}
    (G : GroupoidScheme S)
    (X : GroupoidSimplicialScheme G) (n : ℕ) :
    cechObj G n ⟶ X.simplicialScheme.obj (op (SimplexCategory.mk n)) :=
  (X.pointEquiv n _).symm (cechPointFunctor G (𝟙 _))

private lemma cechDegreeMap_point {S : Scheme.{u}}
    (G : GroupoidScheme S)
    (X : GroupoidSimplicialScheme G) {n : ℕ} {T : Over S}
    (x : T ⟶ cechObj G n) :
    X.pointEquiv n T (x ≫ cechDegreeMap G X n) = cechPointFunctor G x := by
  apply pointFunctor_ext
  · intro i
    rw [X.pointEquiv_naturality_obj]
    simp [cechDegreeMap, cechPointFunctor_obj]
  · intro i j h
    rw [X.pointEquiv_naturality_map,
      show X.pointEquiv n _ (cechDegreeMap G X n) = cechPointFunctor G (𝟙 _) from
        Equiv.apply_symm_apply _ _, cechPointFunctor_map, cechPointFunctor_map]
    simp only [Category.id_comp, compose_precomp, Category.assoc]

private lemma cech_map_π {S : Scheme.{u}}
    (G : GroupoidScheme S) {m n : ℕ}
    (α : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (i : Fin (m + 1)) :
    (Arrow.mk G.source).cechNerve.map α.op ≫
      WidePullback.π (fun _ : Fin (m + 1) => G.source) i =
      WidePullback.π (fun _ : Fin (n + 1) => G.source) (α.toOrderHom i) := by
  apply WidePullback.lift_π

private lemma cechPointFunctor_simplicial {S : Scheme.{u}}
    (G : GroupoidScheme S) {m n : ℕ} {T : Over S}
    (α : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : T ⟶ cechObj G n) :
    cechPointFunctor G (x ≫ (Arrow.mk G.source).cechNerve.map α.op) =
      (cechPointFunctor G x).whiskerLeft α.toOrderHom.monotone.functor := by
  apply pointFunctor_ext
  · intro i
    change (x ≫ _) ≫ _ ≫ G.target = x ≫ _ ≫ G.target
    simp only [Category.assoc, reassoc_of% (cech_map_π G α i)]
    rfl
  · intro i j h
    change ((cechPointFunctor G (x ≫ _)).map (homOfLE h)).unop.arrow =
      ((cechPointFunctor G x).map (homOfLE (α.toOrderHom.monotone h))).unop.arrow
    simp only [cechPointFunctor_map, Category.assoc, cech_map_π]

private noncomputable def cechTargetHom {S : Scheme.{u}}
    (G : GroupoidScheme S)
    (X : GroupoidSimplicialScheme G) :
    (Arrow.mk G.source).cechNerve ⟶ X.simplicialScheme where
  app n := cechDegreeMap G X n.unop.len
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply (X.pointEquiv m _).injective
    rw [cechDegreeMap_point]
    have he := X.pointEquiv_map α.unop _ (cechDegreeMap G X n)
    simp only [Quiver.Hom.op_unop] at he
    rw [he]
    simp only [cechDegreeMap, Equiv.apply_symm_apply]
    simpa only [Category.id_comp, Quiver.Hom.op_unop] using
      cechPointFunctor_simplicial G α.unop (𝟙 _)

private noncomputable def nerveVertex {S : Scheme.{u}}
    {G : GroupoidScheme S}
    (X : GroupoidSimplicialScheme G)
    {n : ℕ} (i : Fin (n + 1)) :
    X.simplicialScheme.obj (op (SimplexCategory.mk n)) ⟶ G.objects :=
  ((X.pointEquiv n _ (𝟙 _)).obj i).unop

private lemma nerveVertex_point {S : Scheme.{u}}
    {G : GroupoidScheme S}
    (X : GroupoidSimplicialScheme G)
    {n : ℕ} {T : Over S}
    (x : T ⟶ X.simplicialScheme.obj (op (SimplexCategory.mk n))) (i : Fin (n + 1)) :
    x ≫ nerveVertex X i = ((X.pointEquiv n T x).obj i).unop := by
  dsimp [nerveVertex]
  rw [← X.pointEquiv_naturality_obj, Category.comp_id]

private lemma cechDegreeMap_vertex {S : Scheme.{u}}
    (G : GroupoidScheme S)
    (X : GroupoidSimplicialScheme G)
    {n : ℕ} (i : Fin (n + 1)) :
    cechDegreeMap G X n ≫ nerveVertex X i =
      WidePullback.π (fun _ : Fin (n + 1) => G.source) i ≫ G.target := by
  rw [nerveVertex_point]
  simp only [cechDegreeMap, Equiv.apply_symm_apply, cechPointFunctor_obj, Category.id_comp]

private lemma nerveVertex_naturality {S : Scheme.{u}}
    {G : GroupoidScheme S}
    (X : GroupoidSimplicialScheme G) {m n : ℕ}
    (α : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (i : Fin (m + 1)) :
    X.simplicialScheme.map α.op ≫ nerveVertex X i = nerveVertex X (α.toOrderHom i) := by
  rw [nerveVertex_point]
  have h := X.pointEquiv_map α _ (𝟙 _)
  simp only [Category.id_comp] at h
  rw [h]
  rfl

/-- Transport between two vertices, using the initial vertex of the simplex. -/
private noncomputable def chainPath {C : Type*} [Groupoid C] {n : ℕ}
    (F : ComposableArrows Cᵒᵖ n) (i j : Fin (n + 1)) :
    (F.obj i).unop ⟶ (F.obj j).unop :=
  (F.map (homOfLE (Fin.zero_le i))).unop ≫
    Groupoid.inv (F.map (homOfLE (Fin.zero_le j))).unop

private lemma chainPath_map {C : Type*} [Groupoid C] {n : ℕ}
    (F : ComposableArrows Cᵒᵖ n) (i j : Fin (n + 1)) (h : i ≤ j) :
    chainPath F j i = (F.map (homOfLE h)).unop := by
  have he := congrArg Quiver.Hom.unop
    (F.map_comp (homOfLE (Fin.zero_le i)) (homOfLE h))
  dsimp [chainPath]
  rw [show F.map (homOfLE (Fin.zero_le j)) =
    F.map (homOfLE (Fin.zero_le i) ≫ homOfLE h) from rfl, he]
  simp [Category.assoc]

private lemma chainPath_quotient {C : Type*} [Groupoid C] {n : ℕ}
    {b : C} (v : Fin (n + 1) → C) (r : ∀ i, b ⟶ v i) (i j : Fin (n + 1)) :
    r i ≫ chainPath (quotientComposableArrows v r) i j = r j := by
  dsimp [chainPath, quotientComposableArrows]
  simp [Groupoid.inv_eq_inv, Category.assoc]

private lemma cech_coordinate_reconstruct {S : Scheme.{u}}
    (G : GroupoidScheme S) {n : ℕ} {T : Over S}
    (x : T ⟶ cechObj G n) (i j : Fin (n + 1)) :
    x ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) j =
      G.compose (chainPath (cechPointFunctor G x) i j).arrow
        (x ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) i)
        (by rw [(chainPath (cechPointFunctor G x) i j).source_eq]; rfl) :=
  (congrArg EvaluationHom.arrow (chainPath_quotient _ (cechArrow G x) i j)).symm

private lemma cech_point_ext {S : Scheme.{u}}
    (G : GroupoidScheme S) {n : ℕ} {T : Over S}
    {x y : T ⟶ cechObj G n} (i : Fin (n + 1))
    (hi : x ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) i =
      y ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) i)
    (h : cechPointFunctor G x = cechPointFunctor G y) : x = y := by
  have hc (j : Fin (n + 1)) :
      x ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) j =
      y ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) j := by
    rw [cech_coordinate_reconstruct G x i j, cech_coordinate_reconstruct G y i j]
    have hp := congrArg (fun F : ComposableArrows (G.Evaluation T)ᵒᵖ n =>
      (chainPath F i j).arrow) h
    dsimp [GroupoidScheme.compose]
    congr 1
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst] using hp
    · simpa only [pullback.lift_snd] using hi
  apply WidePullback.hom_ext (fun _ : Fin (n + 1) => G.source) x y hc
  simpa only [Category.assoc, WidePullback.π_arrow] using
    congrArg (fun a => a ≫ G.source) hi

private lemma quotientComposableArrows_reconstruct {C : Type*} [Groupoid C] {n : ℕ}
    (F : ComposableArrows Cᵒᵖ n) (i : Fin (n + 1)) {b : C}
    (a : b ⟶ (F.obj i).unop) :
    quotientComposableArrows (fun j => (F.obj j).unop)
      (fun j => a ≫ chainPath F i j) = F := by
  apply ComposableArrows.ext (F := quotientComposableArrows (fun j => (F.obj j).unop)
    (fun j => a ≫ chainPath F i j)) (G := F) (fun j => by dsimp [quotientComposableArrows])
  intro k hk
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Quiver.Hom.unop_inj
  change Groupoid.inv (a ≫ chainPath F i ⟨k + 1, by omega⟩) ≫
    (a ≫ chainPath F i ⟨k, by omega⟩) =
    (F.map (homOfLE (show (⟨k, by omega⟩ : Fin (n + 1)) ≤ ⟨k + 1, by omega⟩
      from Nat.le_succ k))).unop
  rw [← chainPath_map]
  simp [chainPath, Groupoid.inv_eq_inv, Category.assoc]

private noncomputable def cechLiftFamily {S : Scheme.{u}}
    (G : GroupoidScheme S) {n : ℕ} {T : Over S} {b : G.Evaluation T}
    {v : Fin (n + 1) → G.Evaluation T} (r : ∀ i, b ⟶ v i) : T ⟶ cechObj G n :=
  WidePullback.lift b (fun i => (r i).arrow) (fun i => (r i).source_eq)

private lemma cechLiftFamily_π {S : Scheme.{u}}
    (G : GroupoidScheme S) {n : ℕ} {T : Over S} {b : G.Evaluation T}
    {v : Fin (n + 1) → G.Evaluation T} (r : ∀ i, b ⟶ v i) (i : Fin (n + 1)) :
    cechLiftFamily G r ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) i =
      (r i).arrow := by
  apply WidePullback.lift_π

private lemma cechLiftFamily_point {S : Scheme.{u}}
    (G : GroupoidScheme S) {n : ℕ} {T : Over S} {b : G.Evaluation T}
    {v : Fin (n + 1) → G.Evaluation T} (r : ∀ i, b ⟶ v i) :
    cechPointFunctor G (cechLiftFamily G r) = quotientComposableArrows v r := by
  apply pointFunctor_ext
  · intro i
    change cechLiftFamily G r ≫ _ ≫ G.target = v i
    rw [← Category.assoc, cechLiftFamily_π, (r i).target_eq]
  · intro i j h
    rw [cechPointFunctor_map]
    change G.compose _ _ _ = G.compose (r i).arrow ((r j).arrow ≫ G.inverse) _
    simp only [cechLiftFamily_π]

/-- A simplex of the nerve and one arrow over a chosen vertex uniquely lift to a simplex of the
Čech nerve. -/
private lemma cechDegreeMap_vertex_isPullback {S : Scheme.{u}}
    (G : GroupoidScheme S)
    (X : GroupoidSimplicialScheme G)
    {n : ℕ} (i : Fin (n + 1)) :
    IsPullback (WidePullback.π (fun _ : Fin (n + 1) => G.source) i)
      (cechDegreeMap G X n) G.target (nerveVertex X i) := by
  refine IsPullback.mk' (cechDegreeMap_vertex G X i).symm ?_ ?_
  · intro T x y hi h
    apply cech_point_ext G i hi
    rw [← cechDegreeMap_point G X x, ← cechDegreeMap_point G X y, h]
  · intro T a b w
    let F := X.pointEquiv n T b
    let a' : (show G.Evaluation T from a ≫ G.source) ⟶ (F.obj i).unop :=
      ⟨a, rfl, w.trans (nerveVertex_point X b i)⟩
    let r := fun j => a' ≫ chainPath F i j
    refine ⟨cechLiftFamily G r, ?_, ?_⟩
    · rw [cechLiftFamily_π]
      change (a' ≫ chainPath F i i).arrow = a
      rw [show chainPath F i i = 𝟙 _ by simp [chainPath], Category.comp_id]
    · apply (X.pointEquiv n T).injective
      rw [cechDegreeMap_point, cechLiftFamily_point]
      exact quotientComposableArrows_reconstruct F i a'

private lemma cechTargetHom_equifibered {S : Scheme.{u}}
    (G : GroupoidScheme S)
    (X : GroupoidSimplicialScheme G) :
    NatTrans.Equifibered (cechTargetHom G X) := by
  rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
  have ho := cechDegreeMap_vertex_isPullback G X (α.unop.toOrderHom 0)
  have hr := cechDegreeMap_vertex_isPullback G X (0 : Fin (m + 1))
  have ht := cech_map_π G α.unop 0
  have hb := nerveVertex_naturality X α.unop 0
  simp only [Quiver.Hom.op_unop] at ht hb
  rw [← ht, ← hb] at ho
  exact ho.of_right ((cechTargetHom G X).naturality α) hr

/-- A cartesian simplicial map from the Čech nerve of the source of a groupoid scheme to its
nerve, with its canonical vertex and edge formulas. -/
structure CartesianTargetMap {S : Scheme.{u}}
    (G : GroupoidScheme S) (X : GroupoidSimplicialScheme G) where
  /-- The simplicial morphism. -/
  hom : (Arrow.mk G.source).cechNerve ⟶ X.simplicialScheme
  /-- Every naturality square of the morphism is cartesian. -/
  equifibered : NatTrans.Equifibered hom
  /-- In degree zero the morphism is the target map. -/
  vertex (T : Over S) (x : T ⟶ ((Arrow.mk G.source).cechNerve).obj
      (op (SimplexCategory.mk 0))) :
    x ≫ hom.app (op (SimplexCategory.mk 0)) ≫ X.objectsIso.hom =
      x ≫ WidePullback.π (fun _ : Fin 1 => G.source) 0 ≫ G.target
  /-- On each successive edge of a simplex, the morphism takes the pair of arrows with a common
  source to their quotient. -/
  edge (n : ℕ) (T : Over S)
      (x : T ⟶ ((Arrow.mk G.source).cechNerve).obj (op (SimplexCategory.mk n)))
      (i : Fin n) :
      ∀ (w : (x ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) i.castSucc) ≫ G.source =
          ((x ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) i.succ) ≫
            G.inverse) ≫ G.target),
        ((X.pointEquiv n T (x ≫ hom.app (op (SimplexCategory.mk n)))).map
          (homOfLE (Fin.castSucc_le_succ i))).unop.arrow =
          G.compose
            (x ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) i.castSucc)
            ((x ≫ WidePullback.π (fun _ : Fin (n + 1) => G.source) i.succ) ≫ G.inverse)
            w

/-- The canonical cartesian map from the Čech nerve of the source of a groupoid scheme to its
nerve. -/
@[stacks 07TQ]
noncomputable def groupoidCechNerveTarget {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    CartesianTargetMap G (groupoidSimplicialScheme G) := by
  exact Classical.choice (show Nonempty
      (CartesianTargetMap G (groupoidSimplicialScheme G)) from by
    let X := groupoidSimplicialScheme G
    refine ⟨{
        hom := cechTargetHom G X
        equifibered := cechTargetHom_equifibered G X
        vertex := ?_
        edge := ?_ }⟩
    · intro T x
      change (x ≫ cechDegreeMap G X 0) ≫ X.objectsIso.hom = _
      rw [← X.pointEquiv_zero, cechDegreeMap_point]
      rfl
    · intro n T x i w
      change ((X.pointEquiv n T (x ≫ cechDegreeMap G X n)).map
        (homOfLE (Fin.castSucc_le_succ i))).unop.arrow = _
      rw [cechDegreeMap_point, cechPointFunctor_map])

end Stacks.Groupoids.GroupoidScheme

end
