module

public import Mathlib.AlgebraicTopology.CechNerve
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.SingleMorphism
public import StacksFrontier.AlgebraicGeometry.Simplicial.CartesianDescentData
import StacksCore.Tactic.StacksAttribute

/-!
# Descent in terms of simplicial schemes

For a morphism of schemes `f : X ⟶ S`, the simplicial scheme `(X/S)_•` has the `(n + 1)`-fold
fibre product of `X` over `S` in degree `n`; it is the Čech nerve of `f`. A cartesian simplicial
scheme `π : Y ⟶ (X/S)_•` has `V = Y_0` over `X`, and the two faces `d¹_0, d¹_1 : Y_1 ⟶ Y_0`
together with `π_1 : Y_1 ⟶ X ×_S X` identify `Y_1` with both `V ×_S X` and `X ×_S V`. The
resulting isomorphism `φ : V ×_S X ≅ X ×_S V` makes `(V, φ)` a descent datum relative to `f`.

## Main definitions

* `AlgebraicGeometry.simplicialScheme`: the simplicial scheme `(X/S)_•` of `f : X ⟶ S`.
* `AlgebraicGeometry.SimplicialScheme.simplex`, `edgeSimplex`, `vertexSimplex` and `triSimplex`
  build a simplex of `(X/S)_•` out of its vertices.
* `AlgebraicGeometry.SimplicialScheme.transport` transports a point of `V` along an edge of
  `(X/S)_•`; `descentObj` is `V` as a scheme over `X` and `transitionOver` is `φ`.
* `AlgebraicGeometry.SimplicialScheme.toDescentDatum`: the descent datum `(V, φ)` relative
  to `f`.

## Main results

* `AlgebraicGeometry.SimplicialScheme.transport_self`, `transport_trans` and `transport_inv`:
  transport is unital, transitive and invertible. Transitivity is the cocycle condition.
* `AlgebraicGeometry.SimplicialScheme.isPullback_cartesianLeft` and
  `isPullback_cartesianRight`: **`(d¹_1, pr_1 ∘ π_1)` and `(pr_0 ∘ π_1, d¹_0)` identify `Y_1`
  with `V ×_S X` and with `X ×_S V`.**
* `AlgebraicGeometry.SimplicialScheme.toDescentDatum` and `cartesianDescentDatum`: **`(V, φ)`
  is a descent datum relative to `X ⟶ S`.**
* `AlgebraicGeometry.SimplicialScheme.cartesian_actMap`: `φ` is the isomorphism `d¹_0` and `π_1`
  induce.

## Implementation notes

A point of `(X/S)_n` is a tuple of `n + 1` points of `X` over one point of `S`, so an edge of a
simplex is determined by its two vertices. Hence the edge action of a descent datum on
`(X/S)_•`, which in general depends on the edge, is a transport between vertices; the unit and
cocycle conditions of `Stacks.Simplicial.Descent.DescentDatum` become `transport_self` and
`transport_trans`. The gluing isomorphism of `AlgebraicGeometry.DescentDatum` is an isomorphism
of products taken in `Over S`, and its cocycle triangle reads, on a point `((v, x₁), x₂)` of
`(V ×_S X) ×_S X`, as transitivity of transport along `x₀ → x₁ → x₂`.

## References

* [Stacks Project, Tag 024A](https://stacks.math.columbia.edu/tag/024A)
* [Stacks Project, Tag 024B](https://stacks.math.columbia.edu/tag/024B)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Simplicial.Descent
open scoped Simplicial

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The simplicial scheme `(X/S)_•` associated to `f : X ⟶ S`: its degree-`n` part is the
`(n + 1)`-fold fibre product of `X` over `S`, i.e. it is the Čech nerve of `f`. -/
@[stacks 024A]
def simplicialScheme : SimplicialObject Scheme.{u} := (Arrow.mk f).cechNerve

namespace SimplicialScheme

/-- The `i`-th projection `(X/S)_n ⟶ X`. -/
abbrev proj (n : ℕ) (i : Fin (n + 1)) : (simplicialScheme f).obj (op ⦋n⦌) ⟶ X :=
  WidePullback.π (fun _ : Fin (n + 1) => f) i
/-- The structure morphism `(X/S)_n ⟶ S`. -/
abbrev baseMap (n : ℕ) : (simplicialScheme f).obj (op ⦋n⦌) ⟶ S :=
  WidePullback.base (fun _ : Fin (n + 1) => f)
/-- Each projection `(X/S)_n ⟶ X` followed by `f` is the structure morphism `(X/S)_n ⟶ S`. -/
@[reassoc (attr := simp)] lemma proj_comp (n : ℕ) (i : Fin (n + 1)) :
    proj f n i ≫ f = baseMap f n :=
  WidePullback.π_arrow _ i
/-- The `n`-simplex of `(X/S)_•` with vertices `x`, all lying over `s : T ⟶ S`. -/
def simplex {T : Scheme.{u}} {n : ℕ} (x : Fin (n + 1) → (T ⟶ X)) (s : T ⟶ S)
    (h : ∀ i, x i ≫ f = s) : T ⟶ (simplicialScheme f).obj (op ⦋n⦌) := WidePullback.lift s x h
/-- The `i`-th vertex of `simplex f x s h` is `x i`. -/
@[reassoc (attr := simp)] lemma simplex_proj {T : Scheme.{u}} {n : ℕ}
    (x : Fin (n + 1) → (T ⟶ X)) (s : T ⟶ S) (h : ∀ i, x i ≫ f = s) (i : Fin (n + 1)) :
    simplex f x s h ≫ proj f n i = x i := by apply WidePullback.lift_π
/-- A point of `(X/S)_n` is determined by its `n + 1` vertices. -/
lemma hom_ext {T : Scheme.{u}} {n : ℕ} {a b : T ⟶ (simplicialScheme f).obj (op ⦋n⦌)}
    (h : ∀ i, a ≫ proj f n i = b ≫ proj f n i) : a = b :=
  WidePullback.hom_ext _ _ _ h <| by
    change a ≫ baseMap f n = b ≫ baseMap f n
    simpa only [Category.assoc, proj_comp] using congrArg (· ≫ f) (h 0)
/-- A simplicial operator reindexes the vertices. -/
@[reassoc (attr := simp)] lemma map_proj {n m : ℕ} (g : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌)
    (k : Fin (m + 1)) : (simplicialScheme f).map g.op ≫ proj f m k = proj f n (g.toOrderHom k) := by
  apply WidePullback.lift_π
/-- A point of `(X/S)_0` is determined by its unique vertex. -/
lemma zero_hom_ext {T : Scheme.{u}} {a b : T ⟶ (simplicialScheme f).obj (op ⦋0⦌)}
    (h : a ≫ proj f 0 0 = b ≫ proj f 0 0) : a = b := by
  apply hom_ext; intro k; fin_cases k; exact h

/-- The edge from `i` to `j` sends `0` to `i`. -/
lemma edge_ohom_zero {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (edge i j h).toOrderHom 0 = i := rfl
/-- The edge from `i` to `j` sends `1` to `j`. -/
lemma edge_ohom_one {n : ℕ} (i j : Fin (n + 1)) (h : i ≤ j) :
    (edge i j h).toOrderHom 1 = j := rfl
/-- The vertex `i` sends the point of `⦋0⦌` to `i`. -/
lemma vertex_ohom {n : ℕ} (i : Fin (n + 1)) (k : Fin 1) :
    (vertex i).toOrderHom k = i := rfl
/-- The face `δ 1 : ⦋0⦌ ⟶ ⦋1⦌` sends the point of `⦋0⦌` to `0`. -/
lemma delta_one_ohom (k : Fin 1) : (SimplexCategory.δ (1 : Fin 2)).toOrderHom k = 0 := by
  fin_cases k; decide
/-- The face `δ 0 : ⦋0⦌ ⟶ ⦋1⦌` sends the point of `⦋0⦌` to `1`. -/
lemma delta_zero_ohom (k : Fin 1) : (SimplexCategory.δ (0 : Fin 2)).toOrderHom k = 1 := by
  fin_cases k; decide

/-- The 1-simplex of `(X/S)_•` with vertices `x` and `y`. -/
def edgeSimplex {T : Scheme.{u}} (x y : T ⟶ X) (h : x ≫ f = y ≫ f) :
    T ⟶ (simplicialScheme f).obj (op ⦋1⦌) :=
  simplex f ![x, y] (x ≫ f) (by intro k; fin_cases k <;> simp [h])
/-- The vertex `0` of the 1-simplex with vertices `x` and `y` is `x`. -/
@[reassoc (attr := simp)] lemma edgeSimplex_proj_zero {T : Scheme.{u}} (x y : T ⟶ X)
    (h : x ≫ f = y ≫ f) : edgeSimplex f x y h ≫ proj f 1 0 = x := by simp [edgeSimplex]
/-- The vertex `1` of the 1-simplex with vertices `x` and `y` is `y`. -/
@[reassoc (attr := simp)] lemma edgeSimplex_proj_one {T : Scheme.{u}} (x y : T ⟶ X)
    (h : x ≫ f = y ≫ f) : edgeSimplex f x y h ≫ proj f 1 1 = y := by simp [edgeSimplex]
/-- Precomposing the 1-simplex with vertices `x` and `y` with `a` gives the 1-simplex with
vertices `a ≫ x` and `a ≫ y`. -/
lemma edgeSimplex_precomp {T T' : Scheme.{u}} (a : T' ⟶ T) (x y : T ⟶ X)
    (hxy : x ≫ f = y ≫ f) :
    a ≫ edgeSimplex f x y hxy =
      edgeSimplex f (a ≫ x) (a ≫ y) (by simp [Category.assoc, hxy]) := by
  apply hom_ext; intro k; fin_cases k <;> simp
/-- Any edge of a simplex is the 1-simplex on its two vertices. -/
lemma map_edge_eq {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) {T : Scheme.{u}}
    (t : T ⟶ (simplicialScheme f).obj (op ⦋n⦌)) :
    t ≫ (simplicialScheme f).map (edge i j hij).op =
      edgeSimplex f (t ≫ proj f n i) (t ≫ proj f n j) (by simp) := by
  apply hom_ext; intro k
  fin_cases k <;> simp [edgeSimplex, edge_ohom_zero, edge_ohom_one]

/-! ### Transport -/

variable {f} in
/-- Transport of a point of `V` along the edge of `(X/S)_•` from `x` to `y`. -/
def transport (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f)) {T : Scheme.{u}}
    (x y : T ⟶ X) (hxy : x ≫ f = y ≫ f) (v : T ⟶ D.V.left)
    (hv : v ≫ D.V.hom ≫ proj f 0 0 = x) : T ⟶ D.V.left :=
  action D.iso.hom (edgeSimplex f x y hxy) v
    (by apply zero_hom_ext; simpa [SimplicialObject.δ, delta_one_ohom] using hv)

variable {f} in
/-- Transport from `x` to `y` lands over `y`. -/
@[reassoc] lemma transport_base (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f))
    {T : Scheme.{u}} (x y : T ⟶ X) (hxy : x ≫ f = y ≫ f) (v : T ⟶ D.V.left)
    (hv : v ≫ D.V.hom ≫ proj f 0 0 = x) :
    transport D x y hxy v hv ≫ D.V.hom ≫ proj f 0 0 = y := by
  rw [← Category.assoc, show transport D x y hxy v hv ≫ D.V.hom = _ from
    action_base D.iso.hom (edgeSimplex f x y hxy) v
      (by apply zero_hom_ext; simpa [SimplicialObject.δ, delta_one_ohom] using hv)]
  simp [SimplicialObject.δ, delta_zero_ohom]

variable {f} in
/-- Transport depends only on the two endpoints and on the point transported. -/
lemma transport_congr (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f))
    {T : Scheme.{u}} {x y x' y' : T ⟶ X} (hxy : x ≫ f = y ≫ f) (hxy' : x' ≫ f = y' ≫ f)
    {v v' : T ⟶ D.V.left} (hv : v ≫ D.V.hom ≫ proj f 0 0 = x)
    (hv' : v' ≫ D.V.hom ≫ proj f 0 0 = x')
    (hx : x = x') (hy : y = y') (hvv : v = v') :
    transport D x y hxy v hv = transport D x' y' hxy' v' hv' := by
  subst hx; subst hy; subst hvv; rfl

variable {f} in
/-- On `(X/S)_•` the edge action depends only on the two vertices. -/
lemma edgeAction_eq_transport (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f))
    {n : ℕ} {T : Scheme.{u}} (t : T ⟶ (simplicialScheme f).obj (op ⦋n⦌))
    (i j : Fin (n + 1)) (hij : i ≤ j)
    (v : T ⟶ D.V.left) (hv : v ≫ D.V.hom = t ≫ (simplicialScheme f).map (vertex i).op) :
    edgeAction D t i j hij v hv =
      transport D (t ≫ proj f n i) (t ≫ proj f n j) (by simp) v
        (by simpa [vertex_ohom] using congrArg (· ≫ proj f 0 0) hv) :=
  action_congr D.iso.hom _ _ (map_edge_eq f i j hij t) rfl

variable {f} in
/-- Transport commutes with precomposition. -/
lemma transport_precomp (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f))
    {T T' : Scheme.{u}} (a : T' ⟶ T) (x y : T ⟶ X) (hxy : x ≫ f = y ≫ f)
    (v : T ⟶ D.V.left) (hv : v ≫ D.V.hom ≫ proj f 0 0 = x) :
    a ≫ transport D x y hxy v hv =
      transport D (a ≫ x) (a ≫ y) (by simp [Category.assoc, hxy]) (a ≫ v)
        (by rw [Category.assoc, hv]) :=
  (action_precomp D.iso.hom a _ v _).symm.trans
    (action_congr D.iso.hom _ _ (edgeSimplex_precomp f a x y hxy) rfl)

/-- The 0-simplex of `(X/S)_•` at `x`. -/
def vertexSimplex {T : Scheme.{u}} (x : T ⟶ X) : T ⟶ (simplicialScheme f).obj (op ⦋0⦌) :=
  simplex f (fun _ => x) (x ≫ f) (by intro k; fin_cases k; rfl)
/-- The vertex of the 0-simplex at `x` is `x`. -/
@[simp] lemma vertexSimplex_proj {T : Scheme.{u}} (x : T ⟶ X) (k : Fin 1) :
    vertexSimplex f x ≫ proj f 0 k = x := by simp [vertexSimplex]

/-- The 2-simplex of `(X/S)_•` with vertices `x`, `y` and `z`. -/
def triSimplex {T : Scheme.{u}} (x y z : T ⟶ X) (hxy : x ≫ f = y ≫ f)
    (hyz : y ≫ f = z ≫ f) : T ⟶ (simplicialScheme f).obj (op ⦋2⦌) :=
  simplex f ![x, y, z] (x ≫ f) (by intro k; fin_cases k <;> simp [hxy, hyz])
/-- The vertex `0` of the 2-simplex with vertices `x`, `y` and `z` is `x`. -/
@[simp] lemma triSimplex_proj_zero {T : Scheme.{u}} (x y z : T ⟶ X) (hxy : x ≫ f = y ≫ f)
    (hyz : y ≫ f = z ≫ f) : triSimplex f x y z hxy hyz ≫ proj f 2 0 = x := by simp [triSimplex]
/-- The vertex `1` of the 2-simplex with vertices `x`, `y` and `z` is `y`. -/
@[simp] lemma triSimplex_proj_one {T : Scheme.{u}} (x y z : T ⟶ X) (hxy : x ≫ f = y ≫ f)
    (hyz : y ≫ f = z ≫ f) : triSimplex f x y z hxy hyz ≫ proj f 2 1 = y := by simp [triSimplex]
/-- The vertex `2` of the 2-simplex with vertices `x`, `y` and `z` is `z`. -/
@[simp] lemma triSimplex_proj_two {T : Scheme.{u}} (x y z : T ⟶ X) (hxy : x ≫ f = y ≫ f)
    (hyz : y ≫ f = z ≫ f) : triSimplex f x y z hxy hyz ≫ proj f 2 2 = z := by simp [triSimplex]

/-- A point of `V` lying over vertex `i` of a simplex `t` is compatible with `t` at vertex `i`. -/
private lemma hom_eq_vertex {f : X ⟶ S}
    (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f)) {n : ℕ}
    {T : Scheme.{u}} (t : T ⟶ (simplicialScheme f).obj (op ⦋n⦌)) (i : Fin (n + 1))
    (v : T ⟶ D.V.left) (hv : v ≫ D.V.hom ≫ proj f 0 0 = t ≫ proj f n i) :
    v ≫ D.V.hom = t ≫ (simplicialScheme f).map (vertex i).op := by
  apply zero_hom_ext; simpa [vertex_ohom] using hv

/-- The edge action along an edge of `t` is transport between any two points equal to its
vertices, applied to any point equal to `v`. -/
private lemma edgeAction_eq_transport_of_eq
    {f : X ⟶ S} (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f)) {n : ℕ}
    {T : Scheme.{u}}
    (t : T ⟶ (simplicialScheme f).obj (op ⦋n⦌)) (i j : Fin (n + 1)) (hij : i ≤ j) {x y : T ⟶ X}
    (hx : t ≫ proj f n i = x) (hy : t ≫ proj f n j = y) (hxy : x ≫ f = y ≫ f)
    {v v' : T ⟶ D.V.left} (hvv : v = v') (hv : v ≫ D.V.hom = t ≫ (simplicialScheme f).map
      (vertex i).op) (hv' : v' ≫ D.V.hom ≫ proj f 0 0 = x) :
    edgeAction D t i j hij v hv = transport D x y hxy v' hv' := by
  subst hx hy hvv
  rw [edgeAction_eq_transport]

variable {f} in
/-- Transport along a degenerate edge is the identity. -/
lemma transport_self (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f))
    {T : Scheme.{u}}
    (x : T ⟶ X) (hxx : x ≫ f = x ≫ f) (v : T ⟶ D.V.left)
    (hv : v ≫ D.V.hom ≫ proj f 0 0 = x) : transport D x x hxx v hv = v := by
  have hv0 := hom_eq_vertex D (vertexSimplex f x) (0 : Fin 1) v (by simpa using hv)
  rw [← edgeAction_eq_transport_of_eq D _ 0 0 le_rfl (by simp) (by simp) hxx rfl hv0 hv]
  exact edgeAction_self D (vertexSimplex f x) 0 v hv0

variable {f} in
/-- Transport is transitive; this is the cocycle condition. -/
lemma transport_trans (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f))
    {T : Scheme.{u}}
    (x y z : T ⟶ X) (hxy : x ≫ f = y ≫ f) (hyz : y ≫ f = z ≫ f) (v : T ⟶ D.V.left)
    (hv : v ≫ D.V.hom ≫ proj f 0 0 = x) :
    transport D x z (hxy.trans hyz) v hv =
      transport D y z hyz (transport D x y hxy v hv) (transport_base D x y hxy v hv) := by
  have hv0 := hom_eq_vertex D (triSimplex f x y z hxy hyz) (0 : Fin 3) v (by simpa using hv)
  have H := edgeAction_trans D (triSimplex f x y z hxy hyz) 0 1 2 (by decide) (by decide) v hv0
  exact (edgeAction_eq_transport_of_eq D _ 0 2 (by decide) (by simp) (by simp)
    (hxy.trans hyz) rfl hv0 hv).symm.trans <| H.trans <|
    edgeAction_eq_transport_of_eq D _ 1 2 (by decide) (by simp) (by simp) hyz
      (edgeAction_eq_transport_of_eq D _ 0 1 (by decide) (by simp) (by simp) hxy rfl hv0 hv) _
      (transport_base D x y hxy v hv)

variable {f} in
/-- Transporting back along the reversed edge recovers the original point. -/
lemma transport_inv (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f))
    {T : Scheme.{u}}
    (x y : T ⟶ X) (hxy : x ≫ f = y ≫ f) (v : T ⟶ D.V.left)
    (hv : v ≫ D.V.hom ≫ proj f 0 0 = x) :
    transport D y x hxy.symm (transport D x y hxy v hv) (transport_base D x y hxy v hv) = v := by
  rw [← transport_trans D x y x hxy hxy.symm v hv]
  exact transport_self D x _ v hv

variable {f} in
/-- The scheme `V = Y_0` underlying a descent datum on `(X/S)_•`, viewed over `X`. -/
def descentObj (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f)) : Over X :=
  Over.mk (D.V.hom ≫ proj f 0 0)

section Transition

variable {f} (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f))

/-- The first projection of `V ×_S X`. -/
abbrev leftFst : (Over.map f).obj (descentObj D) ⨯ Over.mk f ⟶ (Over.map f).obj (descentObj D) :=
  prod.fst
/-- The second projection of `V ×_S X`. -/
abbrev leftSnd : (Over.map f).obj (descentObj D) ⨯ Over.mk f ⟶ Over.mk f := prod.snd
/-- The first projection of `X ×_S V`. -/
abbrev rightFst : Over.mk f ⨯ (Over.map f).obj (descentObj D) ⟶ Over.mk f := prod.fst
/-- The second projection of `X ×_S V`. -/
abbrev rightSnd : Over.mk f ⨯ (Over.map f).obj (descentObj D) ⟶ (Over.map f).obj (descentObj D) :=
  prod.snd

/-- Two morphisms out of `W` in `Over S` have the same composite with the structure maps. -/
private lemma left_comp_hom_eq {W A B : Over S} (u : W ⟶ A) (v : W ⟶ B) :
    u.left ≫ A.hom = v.left ≫ B.hom :=
  (Over.w u).trans (Over.w v).symm

/-- The two components of a point `q` of `V ×_S X`, the first one read in `X`, lie over the same
point of `S`. -/
lemma actMap_cond {W : Over S} (q : W ⟶ (Over.map f).obj (descentObj D) ⨯ Over.mk f) :
    ((q ≫ leftFst D).left ≫ (descentObj D).hom) ≫ f = (q ≫ leftSnd D).left ≫ f := by
  simpa using left_comp_hom_eq (q ≫ leftFst D) (q ≫ leftSnd D)

/-- The two components of a point `q` of `X ×_S V`, the second one read in `X`, lie over the same
point of `S`. -/
lemma actMapInv_cond {W : Over S} (q : W ⟶ Over.mk f ⨯ (Over.map f).obj (descentObj D)) :
    ((q ≫ rightSnd D).left ≫ (descentObj D).hom) ≫ f = (q ≫ rightFst D).left ≫ f := by
  simpa using left_comp_hom_eq (q ≫ rightSnd D) (q ≫ rightFst D)

/-- The two projections of `V ×_S X`, the first one read in `X`, agree over `S`. -/
lemma actMap_hxy : ((leftFst D).left ≫ (descentObj D).hom) ≫ f = (leftSnd D).left ≫ f := by
  simpa using actMap_cond D (𝟙 _)

/-- The two projections of `X ×_S V`, the second one read in `X`, agree over `S`. -/
lemma actMapInv_hxy : ((rightSnd D).left ≫ (descentObj D).hom) ≫ f = (rightFst D).left ≫ f := by
  simpa using actMapInv_cond D (𝟙 _)

/-- The transition action `(v, x₁) ↦ φ(v, x₁)`, as a map of `S`-schemes. -/
def actMap : (Over.map f).obj (descentObj D) ⨯ Over.mk f ⟶ (Over.map f).obj (descentObj D) :=
  Over.homMk
    (transport D ((leftFst D).left ≫ (descentObj D).hom) ((leftSnd D).left)
      (actMap_hxy D) ((leftFst D).left) rfl)
    (by
      have hb : transport D ((leftFst D).left ≫ (descentObj D).hom) ((leftSnd D).left)
          (actMap_hxy D) ((leftFst D).left) rfl ≫ (descentObj D).hom = (leftSnd D).left :=
        transport_base D _ _ (actMap_hxy D) _ rfl
      change transport D ((leftFst D).left ≫ (descentObj D).hom) ((leftSnd D).left)
          (actMap_hxy D) ((leftFst D).left) rfl ≫ (descentObj D).hom ≫ f = _
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) hb).trans
        (by simpa only [Over.mk_hom] using Over.w (leftSnd D))))

/-- The inverse transition action `(x₀, w) ↦ φ⁻¹(x₀, w)`. -/
def actMapInv : Over.mk f ⨯ (Over.map f).obj (descentObj D) ⟶ (Over.map f).obj (descentObj D) :=
  Over.homMk
    (transport D ((rightSnd D).left ≫ (descentObj D).hom) ((rightFst D).left)
      (actMapInv_hxy D) ((rightSnd D).left) rfl)
    (by
      have hb : transport D ((rightSnd D).left ≫ (descentObj D).hom) ((rightFst D).left)
          (actMapInv_hxy D) ((rightSnd D).left) rfl ≫ (descentObj D).hom = (rightFst D).left :=
        transport_base D _ _ (actMapInv_hxy D) _ rfl
      change transport D ((rightSnd D).left ≫ (descentObj D).hom) ((rightFst D).left)
          (actMapInv_hxy D) ((rightSnd D).left) rfl ≫ (descentObj D).hom ≫ f = _
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) hb).trans
        (by simpa only [Over.mk_hom] using Over.w (rightFst D))))

/-- `φ(v, x₁)` lies over `x₁`. -/
@[reassoc (attr := simp)] lemma actMap_structureMap :
    actMap D ≫ structureMap f (descentObj D) = leftSnd D :=
  Over.OverMorphism.ext <| transport_base D _ _ (actMap_hxy D) _ rfl

/-- `φ⁻¹(x₀, w)` lies over `x₀`. -/
@[reassoc (attr := simp)] lemma actMapInv_structureMap :
    actMapInv D ≫ structureMap f (descentObj D) = rightFst D :=
  Over.OverMorphism.ext <| transport_base D _ _ (actMapInv_hxy D) _ rfl

/-- Precomposing a transport between the components `a`, `b` of a point of `P` with `q : W ⟶ P`
transports between the components of `q ≫ a` and `q ≫ b`. -/
private lemma comp_left_transport {P W : Over S} (q : W ⟶ P)
    (a : P ⟶ (Over.map f).obj (descentObj D)) (b : P ⟶ Over.mk f)
    (h : (a.left ≫ (descentObj D).hom) ≫ f = b.left ≫ f)
    (h' : ((q ≫ a).left ≫ (descentObj D).hom) ≫ f = (q ≫ b).left ≫ f) :
    q.left ≫ transport D (a.left ≫ (descentObj D).hom) b.left h a.left rfl =
      transport D ((q ≫ a).left ≫ (descentObj D).hom) (q ≫ b).left h' (q ≫ a).left rfl :=
  (transport_precomp D q.left _ _ h _ rfl).trans
    (transport_congr D _ _ _ _
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (descentObj D).hom) (Over.comp_left _ _ _ q a).symm))
      (Over.comp_left _ _ _ q b).symm (Over.comp_left _ _ _ q a).symm)

/-- At a point `q` of `V ×_S X`, the transition action is transport from the image in `X` of the
first component of `q` to its second component. -/
lemma actMap_comp {W : Over S} (q : W ⟶ (Over.map f).obj (descentObj D) ⨯ Over.mk f) :
    (q ≫ actMap D).left =
      transport D ((q ≫ leftFst D).left ≫ (descentObj D).hom) ((q ≫ leftSnd D).left)
        (actMap_cond D q) ((q ≫ leftFst D).left) rfl :=
  comp_left_transport D q (leftFst D) (leftSnd D) (actMap_hxy D) _

/-- At a point `q` of `X ×_S V`, the inverse transition action is transport from the image in `X`
of the second component of `q` to its first component. -/
lemma actMapInv_comp {W : Over S} (q : W ⟶ Over.mk f ⨯ (Over.map f).obj (descentObj D)) :
    (q ≫ actMapInv D).left =
      transport D ((q ≫ rightSnd D).left ≫ (descentObj D).hom) ((q ≫ rightFst D).left)
        (actMapInv_cond D q) ((q ≫ rightSnd D).left) rfl :=
  comp_left_transport D q (rightSnd D) (rightFst D) (actMapInv_hxy D) _

/-- The transition action followed by `V ⟶ X` is the second projection of `V ×_S X`. -/
lemma actMap_left_base : (actMap D).left ≫ (descentObj D).hom = (leftSnd D).left :=
  transport_base D _ _ (actMap_hxy D) _ rfl

/-- The inverse transition action followed by `V ⟶ X` is the first projection of `X ×_S V`. -/
lemma actMapInv_left_base : (actMapInv D).left ≫ (descentObj D).hom = (rightFst D).left :=
  transport_base D _ _ (actMapInv_hxy D) _ rfl

/-- `φ : V ×_S X ⟶ X ×_S V`, as a map of `S`-schemes. -/
def transitionHom : (Over.map f).obj (descentObj D) ⨯ Over.mk f ⟶
    Over.mk f ⨯ (Over.map f).obj (descentObj D) :=
  prod.lift (leftFst D ≫ structureMap f (descentObj D)) (actMap D)

/-- `φ⁻¹ : X ×_S V ⟶ V ×_S X`, as a map of `S`-schemes. -/
def transitionInv : Over.mk f ⨯ (Over.map f).obj (descentObj D) ⟶
    (Over.map f).obj (descentObj D) ⨯ Over.mk f :=
  prod.lift (actMapInv D) (rightSnd D ≫ structureMap f (descentObj D))

/-- The first component of `φ(v, x₁)` is the image of `v` in `X`. -/
@[reassoc (attr := simp)] lemma transitionHom_fst :
    transitionHom D ≫ prod.fst = leftFst D ≫ structureMap f (descentObj D) := by
  simp [transitionHom]
/-- The second component of `φ` is the transition action. -/
@[reassoc (attr := simp)] lemma transitionHom_snd :
    transitionHom D ≫ prod.snd = actMap D := by simp [transitionHom]
/-- The first component of `φ⁻¹` is the inverse transition action. -/
@[reassoc (attr := simp)] lemma transitionInv_fst :
    transitionInv D ≫ prod.fst = actMapInv D := by simp [transitionInv]
/-- The second component of `φ⁻¹(x₀, w)` is the image of `w` in `X`. -/
@[reassoc (attr := simp)] lemma transitionInv_snd :
    transitionInv D ≫ prod.snd = rightSnd D ≫ structureMap f (descentObj D) := by
  simp [transitionInv]

/-- The inverse transition action undoes `φ`. -/
lemma transitionHom_comp_actMapInv : transitionHom D ≫ actMapInv D = leftFst D := by
  apply Over.OverMorphism.ext
  rw [actMapInv_comp]
  refine (transport_congr D _ _ _ _ ?_ ?_ ?_).trans
    (transport_inv D _ _ (actMap_hxy D) _ rfl)
  · have h := congrArg Over.Hom.left (transitionHom_snd D)
    exact (congrArg (· ≫ (descentObj D).hom) h).trans (actMap_left_base D)
  · exact congrArg Over.Hom.left (transitionHom_fst D)
  · exact congrArg Over.Hom.left (transitionHom_snd D)

/-- The transition action undoes `φ⁻¹`. -/
lemma transitionInv_comp_actMap : transitionInv D ≫ actMap D = rightSnd D := by
  apply Over.OverMorphism.ext
  rw [actMap_comp]
  refine (transport_congr D _ _ _ _ ?_ ?_ ?_).trans
    (transport_inv D _ _ (actMapInv_hxy D) _ rfl)
  · have h := congrArg Over.Hom.left (transitionInv_fst D)
    exact (congrArg (· ≫ (descentObj D).hom) h).trans (actMapInv_left_base D)
  · exact congrArg Over.Hom.left (transitionInv_snd D)
  · exact congrArg Over.Hom.left (transitionInv_fst D)

/-- **`φ : V ×_S X ≅ X ×_S V`.** -/
def transitionProd : (Over.map f).obj (descentObj D) ⨯ Over.mk f ≅
    Over.mk f ⨯ (Over.map f).obj (descentObj D) where
  hom := transitionHom D
  inv := transitionInv D
  hom_inv_id := by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, transitionInv_fst, transitionHom_comp_actMapInv, Category.id_comp]
    · rw [Category.assoc, transitionInv_snd, transitionHom_snd_assoc, actMap_structureMap,
        Category.id_comp]
  inv_hom_id := by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, transitionHom_fst, transitionInv_fst_assoc, actMapInv_structureMap,
        Category.id_comp]
    · rw [Category.assoc, transitionHom_snd, transitionInv_comp_actMap, Category.id_comp]

/-- The source of the cocycle triangle, `(V ×_S X) ×_S X`. -/
abbrev triple : Over S :=
  ((Over.map f).obj (descentObj D) ⨯ Over.mk f) ⨯ Over.mk f

/-- The `V`-component of the left-hand side of the cocycle triangle at `((v, x₁), x₂)` is the
transition action applied to `(φ(v, x₁), x₂)`. -/
lemma cocycle_lhs_snd :
    prod.map (transitionHom D) (𝟙 (Over.mk f)) ≫
        prodMapLastTwo (transitionHom D) ≫ prod.snd =
      prod.lift (prod.fst ≫ actMap D) (prod.snd : triple D ⟶ Over.mk f) ≫ actMap D := by
  simp [prodMapLastTwo, prod.comp_lift, prod.comp_lift_assoc]

/-- The `V`-component of the right-hand side of the cocycle triangle at `((v, x₁), x₂)` is the
transition action applied to `(v, x₂)`. -/
lemma cocycle_rhs_snd :
    prodMapFirstThird (transitionHom D) ≫ prod.snd =
      prod.lift (prod.fst ≫ prod.fst) (prod.snd : triple D ⟶ Over.mk f) ≫ actMap D := by
  simp [prodMapFirstThird, prodMapLastTwo, prod.comp_lift]

section Cocycle

variable {W : Over S} (a : W ⟶ (Over.map f).obj (descentObj D)) (b c : W ⟶ Over.mk f)

/-- The image in `X` of `a : W ⟶ V` and a morphism `b : W ⟶ X` over `S` lie over the same point
of `S`. -/
lemma lift_cond : (a.left ≫ (descentObj D).hom) ≫ f = b.left ≫ f := by
  simpa using left_comp_hom_eq a b

/-- Two morphisms `b c : W ⟶ X` over `S` lie over the same point of `S`. -/
lemma base_cond : b.left ≫ f = c.left ≫ f := by
  simpa using left_comp_hom_eq b c

/-- The transition action at the point `(a, b)` of `V ×_S X` is transport from the image of `a`
in `X` to `b`. -/
lemma actMap_lift_left :
    (prod.lift a b ≫ actMap D).left =
      transport D (a.left ≫ (descentObj D).hom) b.left (lift_cond D a b) a.left rfl := by
  have ha : prod.lift a b ≫ leftFst D = a := prod.lift_fst _ _
  have hb : prod.lift a b ≫ leftSnd D = b := prod.lift_snd _ _
  rw [actMap_comp]
  exact transport_congr D _ _ _ _ (by rw [ha]) (by rw [hb]) (by rw [ha])

/-- **The cocycle condition for `φ`**: transporting along `x₀ → x₁` and then `x₁ → x₂` is
transporting along `x₀ → x₂`. -/
lemma actMap_lift_comp :
    prod.lift (prod.lift a b ≫ actMap D) c ≫ actMap D = prod.lift a c ≫ actMap D := by
  apply Over.OverMorphism.ext
  have h1 : prod.lift (prod.lift a b ≫ actMap D) c ≫ leftFst D = prod.lift a b ≫ actMap D :=
    prod.lift_fst _ _
  have h2 : prod.lift (prod.lift a b ≫ actMap D) c ≫ leftSnd D = c := prod.lift_snd _ _
  have hab : (prod.lift a b ≫ actMap D).left ≫ (descentObj D).hom = b.left := by
    have hO : (prod.lift a b ≫ actMap D) ≫ structureMap f (descentObj D) = b := by
      rw [Category.assoc, actMap_structureMap, prod.lift_snd]
    exact congrArg Over.Hom.left hO
  have e1 : (prod.lift (prod.lift a b ≫ actMap D) c ≫ actMap D).left =
      transport D b.left c.left (base_cond b c)
        (transport D (a.left ≫ (descentObj D).hom) b.left (lift_cond D a b) a.left rfl)
        (transport_base D _ _ (lift_cond D a b) _ rfl) := by
    rw [actMap_comp]
    exact transport_congr D _ _ _ _ (by rw [h1]; exact hab) (by rw [h2])
      (by rw [h1]; exact actMap_lift_left D a b)
  have e2 : (prod.lift a c ≫ actMap D).left =
      transport D (a.left ≫ (descentObj D).hom) c.left
        ((lift_cond D a b).trans (base_cond b c)) a.left rfl :=
    actMap_lift_left D a c
  exact e1.trans
    ((transport_trans D (a.left ≫ (descentObj D).hom) b.left c.left (lift_cond D a b)
      (base_cond b c) a.left rfl).symm.trans e2.symm)

end Cocycle

end Transition

variable {f} in
/-- `φ` commutes with the projections of `V ×_S X` and `X ×_S V` to `X ×_S X`. -/
lemma transitionHom_over (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f)) :
    transitionHom D ≫ prod.map (𝟙 (Over.mk f)) (structureMap f (descentObj D)) =
      prod.map (structureMap f (descentObj D)) (𝟙 (Over.mk f)) := by
  refine prod.hom_ext ?_ ?_ <;> simp

variable {f} in
/-- `φ`, as an isomorphism over `X ×_S X`. -/
def transitionOver (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f)) :
    Over.mk (prod.map (structureMap f (descentObj D)) (𝟙 (Over.mk f))) ≅
      Over.mk (prod.map (𝟙 (Over.mk f)) (structureMap f (descentObj D))) :=
  Over.isoMk (transitionProd D) (transitionHom_over D)

variable {f} in
/-- **The descent datum `(V, φ)` relative to `f : X ⟶ S`** attached to a descent datum on
`(X/S)_•`. -/
@[stacks 024B "the descent datum (V, φ) attached to a descent datum on (X/S)_•"]
def toDescentDatum (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f)) :
    AlgebraicGeometry.DescentDatum f :=
  AlgebraicGeometry.DescentDatum.mk' (descentObj D) (transitionOver D) (by
    have hleft : (transitionOver D).hom.left = transitionHom D := rfl
    rw [hleft]
    refine prod.hom_ext ?_ ?_
    · refine prod.hom_ext ?_ ?_ <;>
        simp [prodMapLastTwo, prodMapFirstThird, prod.comp_lift, prod.comp_lift_assoc]
    · have hpf : prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) =
          (prod.fst : triple D ⟶ (Over.map f).obj (descentObj D) ⨯ Over.mk f) := by
        refine prod.hom_ext ?_ ?_ <;> simp
      have H := actMap_lift_comp D (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) prod.snd
      rw [hpf] at H
      rw [Category.assoc, cocycle_lhs_snd, cocycle_rhs_snd]
      exact H)

/-- A point of `(X/S)_1` is determined by its two vertices. -/
lemma one_hom_ext {T : Scheme.{u}} {a b : T ⟶ (simplicialScheme f).obj (op ⦋1⦌)}
    (h₀ : a ≫ proj f 1 0 = b ≫ proj f 1 0) (h₁ : a ≫ proj f 1 1 = b ≫ proj f 1 1) : a = b := by
  refine hom_ext f (fun k => ?_)
  fin_cases k
  · exact h₀
  · exact h₁

/-- The face `d¹_1 : (X/S)_1 ⟶ (X/S)_0` keeps the vertex `0`. -/
@[reassoc (attr := simp)] lemma delta_one_proj :
    (simplicialScheme f).δ (1 : Fin 2) ≫ proj f 0 0 = proj f 1 0 := by
  simp [SimplicialObject.δ, delta_one_ohom]

/-- The face `d¹_0 : (X/S)_1 ⟶ (X/S)_0` keeps the vertex `1`. -/
@[reassoc (attr := simp)] lemma delta_zero_proj :
    (simplicialScheme f).δ (0 : Fin 2) ≫ proj f 0 0 = proj f 1 1 := by
  simp [SimplicialObject.δ, delta_zero_ohom]

/-- The face `d¹_1 : (X/S)_1 ⟶ (X/S)_0` and the vertex `1` exhibit `(X/S)_1` as `(X/S)_0 ×_S X`. -/
lemma isPullback_delta_one :
    IsPullback ((simplicialScheme f).δ (1 : Fin 2)) (proj f 1 1) (proj f 0 0 ≫ f) f := by
  have hd : (simplicialScheme f).δ (1 : Fin 2) ≫ proj f 0 0 = proj f 1 0 := delta_one_proj f
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [← Category.assoc, hd, proj_comp, proj_comp]
  · intro T φ φ' h₁ h₂
    refine one_hom_ext f ?_ h₂
    rw [← hd, ← Category.assoc, ← Category.assoc, h₁]
  · intro T a b h
    rw [← Category.assoc] at h
    refine ⟨edgeSimplex f (a ≫ proj f 0 0) b h, ?_, edgeSimplex_proj_one f _ _ _⟩
    refine zero_hom_ext f ?_
    rw [Category.assoc, hd, edgeSimplex_proj_zero]

/-- The face `d¹_0 : (X/S)_1 ⟶ (X/S)_0` and the vertex `0` exhibit `(X/S)_1` as
`(X/S)_0 ×_S X`. -/
lemma isPullback_delta_zero :
    IsPullback ((simplicialScheme f).δ (0 : Fin 2)) (proj f 1 0) (proj f 0 0 ≫ f) f := by
  have hd : (simplicialScheme f).δ (0 : Fin 2) ≫ proj f 0 0 = proj f 1 1 := delta_zero_proj f
  refine IsPullback.mk' ?_ ?_ ?_
  · rw [← Category.assoc, hd, proj_comp, proj_comp]
  · intro T φ φ' h₁ h₂
    refine one_hom_ext f h₂ ?_
    rw [← hd, ← Category.assoc, ← Category.assoc, h₁]
  · intro T a b h
    rw [← Category.assoc] at h
    refine ⟨edgeSimplex f b (a ≫ proj f 0 0) h.symm, ?_, edgeSimplex_proj_zero f _ _ _⟩
    refine zero_hom_ext f ?_
    rw [Category.assoc, hd, edgeSimplex_proj_one]

variable {f} in
/-- **`(d¹₁, pr₁ ∘ π₁) : Y₁ ⟶ V ×_S X` is an isomorphism.** -/
@[stacks 024B "the isomorphism V ×_S X ← Y_1 given by (d¹_1, pr_1 ∘ π_1)"]
lemma isPullback_cartesianLeft (Y : Stacks.Simplicial.Descent.Cartesian (simplicialScheme f)) :
    IsPullback (Y.1.left.δ (1 : Fin 2)) (Y.1.hom.app (op ⦋1⦌) ≫ proj f 1 1)
      ((descentObj (cartesianDatum Y)).hom ≫ f) f := by
  have H := (Y.2 (SimplexCategory.δ (1 : Fin 2)).op).paste_vert (isPullback_delta_one f)
  rwa [← Category.assoc] at H

variable {f} in
/-- **`(pr₀ ∘ π₁, d¹₀) : Y₁ ⟶ X ×_S V` is an isomorphism.** -/
@[stacks 024B "the isomorphism Y_1 → X ×_S V given by (pr_0 ∘ π_1, d¹_0)"]
lemma isPullback_cartesianRight (Y : Stacks.Simplicial.Descent.Cartesian (simplicialScheme f)) :
    IsPullback (Y.1.hom.app (op ⦋1⦌) ≫ proj f 1 0) (Y.1.left.δ (0 : Fin 2)) f
      ((descentObj (cartesianDatum Y)).hom ≫ f) := by
  have H := ((Y.2 (SimplexCategory.δ (0 : Fin 2)).op).paste_vert (isPullback_delta_zero f)).flip
  rwa [← Category.assoc] at H

variable {f} in
/-- `φ` is the isomorphism induced by `d¹₀` and `π₁`: a point of `V ×_S X` lifted to a point
`y` of `Y₁` is sent to the zeroth face of `y`. -/
@[stacks 024B "φ is the isomorphism resulting from d¹_0 and π_1"]
lemma cartesian_actMap (Y : Stacks.Simplicial.Descent.Cartesian (simplicialScheme f)) {W : Over S}
    (q : W ⟶ (Over.map f).obj (descentObj (cartesianDatum Y)) ⨯ Over.mk f)
    (y : W.left ⟶ Y.1.left.obj (op ⦋1⦌))
    (h₁ : y ≫ Y.1.left.δ (1 : Fin 2) = (q ≫ prod.fst).left)
    (h₂ : y ≫ Y.1.hom.app (op ⦋1⦌) ≫ proj f 1 1 = (q ≫ prod.snd).left) :
    (q ≫ actMap (cartesianDatum Y)).left = y ≫ Y.1.left.δ (0 : Fin 2) := by
  have hnat : Y.1.left.δ (1 : Fin 2) ≫ Y.1.hom.app (op ⦋0⦌) =
      Y.1.hom.app (op ⦋1⦌) ≫ (simplicialScheme f).δ (1 : Fin 2) :=
    Y.1.hom.naturality (SimplexCategory.δ (1 : Fin 2)).op
  have ht : edgeSimplex f ((q ≫ prod.fst).left ≫ (descentObj (cartesianDatum Y)).hom)
        ((q ≫ prod.snd).left) (actMap_cond (cartesianDatum Y) q) =
      y ≫ Y.1.hom.app (op ⦋1⦌) := by
    refine one_hom_ext f ?_ ?_
    · rw [edgeSimplex_proj_zero, ← h₁]
      change y ≫ Y.1.left.δ (1 : Fin 2) ≫ Y.1.hom.app (op ⦋0⦌) ≫ proj f 0 0 = _
      rw [← Category.assoc (Y.1.left.δ (1 : Fin 2)), hnat, Category.assoc,
        Category.assoc, delta_one_proj]
    · rw [edgeSimplex_proj_one, ← h₂, Category.assoc]
  rw [actMap_comp]
  exact Eq.trans
    (action_congr (cartesianDatum Y).iso.hom _ _ ht h₁.symm) (cartesian_action Y y)

variable {f} in
/-- The scheme over `X` underlying the descent datum `(V, φ)` is `V`. -/
@[simp] lemma toDescentDatum_over
    (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f)) :
    (toDescentDatum D).over = descentObj D := rfl

variable {f} in
/-- The gluing isomorphism of the descent datum `(V, φ)` is `φ`. -/
@[simp] lemma toDescentDatum_transition
    (D : Stacks.Simplicial.Descent.DescentDatum (simplicialScheme f)) :
    (toDescentDatum D).transition = transitionOver D := rfl

variable {f} in
/-- **`(V, φ)` is a descent datum relative to `X ⟶ S`**, for `V = Y₀` over `X` and `φ` the
isomorphism `V ×_S X ≅ X ×_S V` induced by `d¹₀`, `d¹₁` and `π₁` on a cartesian simplicial
scheme `Y` over `(X/S)_•`. -/
@[stacks 024B "(V, φ) is a descent datum relative to X ⟶ S, for cartesian Y over (X/S)_•"]
def cartesianDescentDatum (Y : Stacks.Simplicial.Descent.Cartesian (simplicialScheme f)) :
    AlgebraicGeometry.DescentDatum f :=
  toDescentDatum (cartesianDatum Y)

variable {f} in
/-- The scheme over `X` underlying the descent datum of a cartesian `Y` is `V = Y₀`. -/
@[simp] lemma cartesianDescentDatum_over
    (Y : Stacks.Simplicial.Descent.Cartesian (simplicialScheme f)) :
    (cartesianDescentDatum Y).over = descentObj (cartesianDatum Y) := rfl

variable {f} in
/-- `(d¹₁, pr₁ ∘ π₁) : Y₁ ≅ V ×_S X`. -/
def cartesianIsoLeft (Y : Stacks.Simplicial.Descent.Cartesian (simplicialScheme f)) :
    Y.1.left.obj (op ⦋1⦌) ≅ pullback ((descentObj (cartesianDatum Y)).hom ≫ f) f :=
  (isPullback_cartesianLeft Y).isoPullback

variable {f} in
/-- `(pr₀ ∘ π₁, d¹₀) : Y₁ ≅ X ×_S V`. -/
def cartesianIsoRight (Y : Stacks.Simplicial.Descent.Cartesian (simplicialScheme f)) :
    Y.1.left.obj (op ⦋1⦌) ≅ pullback f ((descentObj (cartesianDatum Y)).hom ≫ f) :=
  (isPullback_cartesianRight Y).isoPullback

end SimplicialScheme

end AlgebraicGeometry
