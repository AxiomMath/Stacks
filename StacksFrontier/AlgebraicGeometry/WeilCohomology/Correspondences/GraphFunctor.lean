module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GradedStructure
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Graph
public import StacksCore.Tactic.StacksAttribute

/-!
# The contravariant graph functor to correspondences

Sending a smooth projective scheme over `k` to itself and a morphism `f : Y ⟶ X` to the class
`[Γ_f] ∈ Corr⁰(X, Y)` of its graph is a contravariant functor from smooth projective schemes to
the graded category of correspondences.

The proof here is the one through proper pushforward rather than through the proper intersection
of `Γ_f × Z` with `X × Γ_g` in the triple product. Write `f ×ₛ 𝟙` for the morphism
`Y ×_S W ⟶ X ×_S W` induced by `f : Y ⟶ X`. Two scheme-theoretic identities, both proved below,
carry the whole argument:

* `(f ×ₛ 𝟙) ∘ δ_Y = Γ_f`, the graph of `f` is the image of the diagonal of `Y` under `f ×ₛ 𝟙`;
* `(f ×ₛ 𝟙) ∘ (g ×ₛ 𝟙) = (g ≫ f) ×ₛ 𝟙`, these morphisms are functorial in `f`.

Hence `[Γ_f] = (f ×ₛ 𝟙)_*[Δ_Y]`, and the two functor laws drop out of proper-pushforward
functoriality together with the facts that the diagonal class is a unit for composition of
correspondences and that composition commutes with proper pushforward in the outer variable.

## Main definitions

* `Stacks.WeilCohomology.prodMapFst`: the morphism `f ×ₛ 𝟙 : Y ×_S W ⟶ X ×_S W`.
* `Stacks.WeilCohomology.GradedCompositionData.PushforwardData`: the carried proper-pushforward
  input — pushforward of correspondences along `f ×ₛ 𝟙`, functorial, and commuting with
  composition of correspondences in the outer variable.
* `Stacks.WeilCohomology.GradedCompositionData.PushforwardData.graphCorrespondence`: the graph
  class `[Γ_f] ∈ Corr⁰(X, Y)`, namely `(f ×ₛ 𝟙)_*[Δ_Y]`.
* `Stacks.WeilCohomology.GradedCompositionData.PushforwardData.graphHom`: that class read as a
  morphism `X ⟶ Y` of the category of correspondences.
* `Stacks.WeilCohomology.GradedCompositionData.PushforwardData.graphFunctor`: the resulting
  contravariant functor.

## Main results

* `Stacks.WeilCohomology.diagonal_comp_prodMapFst`: `δ_Y ≫ (f ×ₛ 𝟙) = Γ_f`.
* `Stacks.WeilCohomology.graphMorphism_id`: the graph of an identity is the diagonal.
* `Stacks.WeilCohomology.graphMorphism_comp_prodMapFst`: `Γ_g ≫ (f ×ₛ 𝟙) = Γ_{g ≫ f}`.
* `Stacks.WeilCohomology.prodMapFst_comp_prodMapFst`: `f ×ₛ 𝟙` is functorial in `f`.
* `Stacks.WeilCohomology.GradedCompositionData.PushforwardData.graphCorrespondence_id` and
  `...pushL_graphCorrespondence`: `[Γ_{𝟙 X}] = [Δ_X]`, and pushing `[Γ_g]` forward along
  `f ×ₛ 𝟙` gives `[Γ_{g ≫ f}]`.
* `...graphHom_id` and `...graphHom_comp`: the two functor laws, `[Γ_{𝟙 X}] = 𝟙 X` and
  `[Γ_g] ∘ [Γ_f] = [Γ_{g ≫ f}]`.
* `Stacks.WeilCohomology.GradedCompositionData.PushforwardData.graphFunctor`: **Stacks 0FG3**,
  the contravariant functor, identity on objects, with `f ↦ [Γ_f]`.
* `...graphHom_mem_grade`: the morphism attached to `f` is homogeneous of degree zero, that is
  it lies in `Corr⁰(X, Y)`.

## Implementation notes

**What is proved and what is carried.** The `@[stacks 0FG3]` attribute is keyed. What is
*proved* is the whole of 0FG3: that the assignment is the identity on objects, that identities
go to identities, that composites go to composites in the reversed order, and therefore that
there is a functor `Cᵒᵖ ⥤ Corr`. What is *carried* is intersection-theoretic input that this
repository does not have, in two packets.

The first packet is `Stacks.WeilCohomology.GradedCompositionData` itself, which the file
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GradedStructure` introduces for
Stacks 0FG2 and documents there: composition of correspondences, its `ℚ`-bilinearity,
associativity and the unit laws for the diagonal class, standing in for Stacks 0FG0 (1) and the
diagonal computation of Stacks 0FFD.

The second packet is `Stacks.WeilCohomology.GradedCompositionData.PushforwardData`, added here.
Its fields are:

* `pushL`, proper pushforward `Corrʳ(X, Y) → Corrʳ(X', Y)` along `u ×ₛ 𝟙` for `u : X ⟶ X'`.
  A morphism of smooth projective schemes over a field is proper, so `u ×ₛ 𝟙` is proper, and
  proper pushforward preserves the dimension grading, which is how `Corrʳ` is graded; this is
  Stacks 02RW together with the well-definedness on rational equivalence of Stacks 02S2.
* `pushL_id` and `pushL_comp`, functoriality of proper pushforward — again Stacks 02RW — read
  through `Stacks.WeilCohomology.prodMapFst_comp_prodMapFst`, which is proved below and is what
  makes the two statements the functoriality of a single pushforward operation.
* `comp_pushL`, that composition of correspondences commutes with proper pushforward in the
  outer variable: `(u ×ₛ 𝟙)_*(c) ∘ c' = (u ×ₛ 𝟙)_*(c ∘ c')`. Through the three-projection
  formula of Stacks 0FG0 this is flat base change for the projection `pr₁₂` along
  `u ×ₛ 𝟙 ×ₛ 𝟙`, the projection formula of Stacks 0FFC for that morphism, and functoriality of
  proper pushforward.

No field of `PushforwardData` mentions graphs, the diagonal, identities or composites of
graphs: each is a statement about *arbitrary* correspondences and an *arbitrary* morphism, so
neither the conclusion of 0FG3 nor any part of it is among the hypotheses. In particular this
is deliberately weaker carried data than the `graph_id` and `graph_comp` fields of
`Stacks.WeilCohomology.CorrespondenceStructure` in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.MonoidalStructure`, which carries
the conclusion of 0FG3 outright because Stacks 0FG7 needs it and does not reprove it. The two
structures are independent; nothing below uses `CorrespondenceStructure`.

**Why `[Γ_f] = (f ×ₛ 𝟙)_*[Δ_Y]` is a definition and not a claim.** The graph class is
`(γ_f)_*[Y]` for the graph morphism `γ_f : Y ⟶ X ×_S Y` of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Graph`, and the diagonal class is
`(δ_Y)_*[Y]`. Since `δ_Y ≫ (f ×ₛ 𝟙) = γ_f` — this is
`Stacks.WeilCohomology.diagonal_comp_prodMapFst`, proved below — pushforward functoriality
forces `(γ_f)_*[Y] = (f ×ₛ 𝟙)_*(δ_Y)_*[Y] = (f ×ₛ 𝟙)_*[Δ_Y]`. So defining the graph
correspondence by the right-hand side is not a choice; it is the only value it can have, and the
scheme-level identity that says so is a theorem of this file rather than a hypothesis.

**Abstraction over the geometry.** As in
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Graph`,
`...Correspondences.Transpose` and `...Correspondences.GradedStructure`, smoothness,
projectivity and the base field are not imposed: the categorical argument uses none of them.
Instantiating `Corr X Y r` by `Stacks.WeilCohomology.Correspondence` on the smooth projective
schemes over `k` recovers the statement of the source verbatim. The scheme-level lemmas are
likewise stated over an arbitrary base scheme `S`.

**Degrees.** Both `[Γ_f]` and `[Δ_X]` are homogeneous of degree zero, but composing them
produces a correspondence indexed by `0 + 0`, which is the same integer as `0` written another
way and not the same type. As in `...Correspondences.GradedStructure`, every identity involving
composition is therefore stated after `DirectSum.of` in the total morphism module, where no cast
appears; `graphHom` is exactly that image, so the functor laws are equalities of morphisms of
the category of correspondences with nothing to transport.

## References

* [Stacks Project, Tag 0FG3](https://stacks.math.columbia.edu/tag/0FG3)
* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Tag 0FG1](https://stacks.math.columbia.edu/tag/0FG1)
* [Stacks Project, Tag 0FG2](https://stacks.math.columbia.edu/tag/0FG2)
* [Stacks Project, Tag 0FFC](https://stacks.math.columbia.edu/tag/0FFC)
* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe v w u

namespace Stacks.WeilCohomology

/-! ### The geometry of graphs and of products with a fixed factor -/

section Geometry

variable {S W X Y Z : Scheme.{u}}

/-- The morphism `f ×ₛ 𝟙_W : Y ×_S W ⟶ X ×_S W` induced by a morphism `f : Y ⟶ X` over `S`,
acting on the first factor only. -/
noncomputable abbrev prodMapFst (pX : X ⟶ S) (pY : Y ⟶ S) (pW : W ⟶ S) (f : Y ⟶ X)
    (hf : f ≫ pX = pY) : pullback pY pW ⟶ pullback pX pW :=
  pullback.map pY pW pX pW f (𝟙 W) (𝟙 S) (by simpa using hf.symm) (by simp)

/-- The first projection after `f ×ₛ 𝟙_W` is the first projection followed by `f`. -/
@[reassoc (attr := simp)]
theorem prodMapFst_comp_fst (pX : X ⟶ S) (pY : Y ⟶ S) (pW : W ⟶ S) (f : Y ⟶ X)
    (hf : f ≫ pX = pY) :
    prodMapFst pX pY pW f hf ≫ pullback.fst pX pW = pullback.fst pY pW ≫ f :=
  pullback.lift_fst _ _ _

/-- The second projection after `f ×ₛ 𝟙_W` is the second projection. -/
@[reassoc (attr := simp)]
theorem prodMapFst_comp_snd (pX : X ⟶ S) (pY : Y ⟶ S) (pW : W ⟶ S) (f : Y ⟶ X)
    (hf : f ≫ pX = pY) :
    prodMapFst pX pY pW f hf ≫ pullback.snd pX pW = pullback.snd pY pW :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The graph of `f : Y ⟶ X` is the image of the diagonal of `Y` under `f ×ₛ 𝟙_Y`:
`δ_Y ≫ (f ×ₛ 𝟙) = γ_f`. -/
theorem diagonal_comp_prodMapFst (pX : X ⟶ S) (pY : Y ⟶ S) (f : Y ⟶ X) (hf : f ≫ pX = pY) :
    pullback.diagonal pY ≫ prodMapFst pX pY pY f hf = graphMorphism pX pY f hf := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- The graph of an identity is the diagonal: `γ_{𝟙 X} = δ_X`. -/
theorem graphMorphism_id (pX : X ⟶ S) (h : (𝟙 X) ≫ pX = pX) :
    graphMorphism pX pX (𝟙 X) h = pullback.diagonal pX := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- Composing the graph of `g : Z ⟶ Y` with `f ×ₛ 𝟙_Z` gives the graph of `g ≫ f`:
`γ_g ≫ (f ×ₛ 𝟙) = γ_{g ≫ f}`. -/
theorem graphMorphism_comp_prodMapFst (pX : X ⟶ S) (pY : Y ⟶ S) (pZ : Z ⟶ S) (f : Y ⟶ X)
    (hf : f ≫ pX = pY) (g : Z ⟶ Y) (hg : g ≫ pY = pZ) (hgf : (g ≫ f) ≫ pX = pZ) :
    graphMorphism pY pZ g hg ≫ prodMapFst pX pY pZ f hf = graphMorphism pX pZ (g ≫ f) hgf := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, prodMapFst_comp_fst, ← Category.assoc, graphMorphism_fst,
      graphMorphism_fst]
  · rw [Category.assoc, prodMapFst_comp_snd, graphMorphism_snd, graphMorphism_snd]

/-- The morphisms `f ×ₛ 𝟙_W` are functorial in `f`:
`(g ×ₛ 𝟙) ≫ (f ×ₛ 𝟙) = (g ≫ f) ×ₛ 𝟙`. -/
theorem prodMapFst_comp_prodMapFst (pX : X ⟶ S) (pY : Y ⟶ S) (pZ : Z ⟶ S) (pW : W ⟶ S)
    (f : Y ⟶ X) (hf : f ≫ pX = pY) (g : Z ⟶ Y) (hg : g ≫ pY = pZ)
    (hgf : (g ≫ f) ≫ pX = pZ) :
    prodMapFst pY pZ pW g hg ≫ prodMapFst pX pY pW f hf =
      prodMapFst pX pZ pW (g ≫ f) hgf := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- The morphism induced by an identity is an identity: `𝟙 ×ₛ 𝟙 = 𝟙`. -/
@[simp]
theorem prodMapFst_id (pX : X ⟶ S) (pW : W ⟶ S) (h : (𝟙 X) ≫ pX = pX) :
    prodMapFst pX pX pW (𝟙 X) h = 𝟙 (pullback pX pW) := by
  refine pullback.hom_ext ?_ ?_ <;> simp

end Geometry

/-! ### Proper pushforward of correspondences -/

section Abstract

variable {C : Type u} [Category.{v} C] {Corr : C → C → ℤ → Type w}
  [∀ X Y : C, ∀ r : ℤ, AddCommGroup (Corr X Y r)]
  [∀ X Y : C, ∀ r : ℤ, Module ℚ (Corr X Y r)]

namespace GradedCompositionData

/-- Proper pushforward of correspondences along `u ×ₛ 𝟙`, carried as data: for `u : X ⟶ X'` a
`ℚ`-linear map `Corrʳ(X, Y) → Corrʳ(X', Y)`, functorial in `u`, which commutes with composition
of correspondences in the outer variable.

Every field is intersection-theoretic input that this repository does not have, and none of them
refers to graphs, diagonals or composites of graphs: see the implementation notes of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphFunctor`. -/
structure PushforwardData (D : GradedCompositionData Corr) where
  /-- Proper pushforward along `u ×ₛ 𝟙`; the dimension grading, hence the degree, is
  preserved. -/
  pushL : ∀ {X X' Y : C}, (X ⟶ X') → ∀ {r : ℤ}, Corr X Y r →ₗ[ℚ] Corr X' Y r
  /-- Proper pushforward along an identity is the identity. -/
  pushL_id : ∀ {X Y : C} {r : ℤ} (a : Corr X Y r), pushL (𝟙 X) a = a
  /-- Proper pushforward is functorial. -/
  pushL_comp : ∀ {X X' X'' Y : C} (u : X ⟶ X') (v : X' ⟶ X'') {r : ℤ} (a : Corr X Y r),
    pushL (u ≫ v) a = pushL v (pushL u a)
  /-- Composition of correspondences commutes with proper pushforward in the outer variable. -/
  comp_pushL : ∀ {X X' Y Z : C} (u : X ⟶ X') {r s : ℤ} (a : Corr X Y r) (c : Corr Y Z s),
    D.comp (pushL u a) c = pushL u (D.comp a c)

namespace PushforwardData

variable {D : GradedCompositionData Corr} (P : D.PushforwardData)

/-- Proper pushforward along `u ×ₛ 𝟙`, extended to the total morphism modules. -/
def pushLTotal {X X' : C} (u : X ⟶ X') (Y : C) :
    TotalCorrespondence Corr X Y →ₗ[ℚ] TotalCorrespondence Corr X' Y :=
  DirectSum.toModule ℚ ℤ _ fun r ↦
    (DirectSum.lof ℚ ℤ (fun k ↦ Corr X' Y k) r).comp (P.pushL u)

/-- On a homogeneous correspondence of degree `r`, `pushLTotal` is proper pushforward in
degree `r`. -/
@[simp]
theorem pushLTotal_of {X X' : C} (u : X ⟶ X') (Y : C) (r : ℤ) (a : Corr X Y r) :
    P.pushLTotal u Y (DirectSum.of (fun k ↦ Corr X Y k) r a) =
      DirectSum.of (fun k ↦ Corr X' Y k) r (P.pushL u a) := by
  rw [← DirectSum.lof_eq_of ℚ, ← DirectSum.lof_eq_of ℚ, pushLTotal]
  exact DirectSum.toModule_lof ℚ (φ := fun r ↦
    (DirectSum.lof ℚ ℤ (fun k ↦ Corr X' Y k) r).comp (P.pushL u)) r a

/-! ### The graph correspondence -/

/-- The graph correspondence `[Γ_f] ∈ Corr⁰(X, Y)` of a morphism `f : Y ⟶ X`: the proper
pushforward of the diagonal class of `Y` along `f ×ₛ 𝟙`. By
`Stacks.WeilCohomology.diagonal_comp_prodMapFst` the graph `Γ_f` is the image of the diagonal
`δ_Y` under `f ×ₛ 𝟙`, so this is the class of the graph. -/
def graphCorrespondence {X Y : C} (f : Y ⟶ X) : Corr X Y 0 :=
  P.pushL f (D.diagonal Y)

/-- The graph of an identity is the diagonal class, matching
`Stacks.WeilCohomology.graphMorphism_id` on schemes. -/
@[simp]
theorem graphCorrespondence_id (X : C) : P.graphCorrespondence (𝟙 X) = D.diagonal X :=
  P.pushL_id _

/-- Proper pushforward of a graph class along `u ×ₛ 𝟙` is the graph class of the composite,
matching `Stacks.WeilCohomology.graphMorphism_comp_prodMapFst` on schemes. -/
theorem pushL_graphCorrespondence {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) :
    P.pushL f (P.graphCorrespondence g) = P.graphCorrespondence (g ≫ f) :=
  (P.pushL_comp g f (D.diagonal Z)).symm

/-! ### The functor -/

/-- The graph correspondence of `f : Y ⟶ X`, read as a morphism `X ⟶ Y` of the category of
correspondences. -/
def graphHom {X Y : C} (f : Y ⟶ X) : (Obj.mk X : D.Obj) ⟶ Obj.mk Y :=
  DirectSum.of (fun k ↦ Corr X Y k) 0 (P.graphCorrespondence f)

/-- The morphism of correspondences attached to `f : Y ⟶ X` is homogeneous of degree zero: it
lies in `Corr⁰(X, Y)`. -/
theorem graphHom_mem_grade {X Y : C} (f : Y ⟶ X) :
    P.graphHom f ∈ GradedCategory.grade (R := ℚ) (Obj.mk X : D.Obj) (Obj.mk Y) 0 :=
  (D.mem_grade_iff).2 ⟨P.graphCorrespondence f, rfl⟩

/-- The graph of an identity is the identity correspondence. -/
@[simp]
theorem graphHom_id (X : C) : P.graphHom (𝟙 X) = 𝟙 (Obj.mk X : D.Obj) := by
  rw [graphHom, graphCorrespondence_id, D.id_eq (Obj.mk X)]

/-- Graphs compose contravariantly: `[Γ_g] ∘ [Γ_f] = [Γ_{g ≫ f}]`, that is
`graphHom f ≫ graphHom g = graphHom (g ≫ f)`.

The diagonal class is a unit for composition of correspondences and composition commutes with
proper pushforward in the outer variable, so composing the two graph classes pushes the second
one forward along `f ×ₛ 𝟙`; by `pushL_graphCorrespondence` that is the graph class of
`g ≫ f`. -/
theorem graphHom_comp {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) :
    P.graphHom f ≫ P.graphHom g = P.graphHom (g ≫ f) := by
  have hcomp : D.comp (P.graphCorrespondence f) (P.graphCorrespondence g) =
      P.pushL f (D.comp (D.diagonal Y) (P.graphCorrespondence g)) :=
    P.comp_pushL f (D.diagonal Y) (P.graphCorrespondence g)
  calc P.graphHom f ≫ P.graphHom g
      = DirectSum.of (fun k ↦ Corr X Z k) (0 + 0)
          (D.comp (P.graphCorrespondence f) (P.graphCorrespondence g)) :=
        D.of_comp_of (X := Obj.mk X) (Y := Obj.mk Y) (Z := Obj.mk Z) _ _
    _ = P.pushLTotal f Z (DirectSum.of (fun k ↦ Corr Y Z k) (0 + 0)
          (D.comp (D.diagonal Y) (P.graphCorrespondence g))) := by
        rw [pushLTotal_of, hcomp]
    _ = P.pushLTotal f Z
          (DirectSum.of (fun k ↦ Corr Y Z k) 0 (P.graphCorrespondence g)) := by
        rw [D.of_diagonal_comp (P.graphCorrespondence g)]
    _ = P.graphHom (g ≫ f) := by
        rw [pushLTotal_of, graphHom, pushL_graphCorrespondence]

/-- **Stacks Project, Tag 0FG3.** The contravariant functor from the ambient category — in the
source the smooth projective schemes over `k` — to the category of correspondences which is the
identity on objects and sends `f : Y ⟶ X` to the class `[Γ_f] ∈ Corr⁰(X, Y)` of its graph.

Keyed: the functor, its two laws and the identity on objects are all proved. The carried input
is the composition of correspondences of `Stacks.WeilCohomology.GradedCompositionData`, as for
Stacks 0FG2, together with proper pushforward of correspondences along `u ×ₛ 𝟙` and its
compatibilities in `Stacks.WeilCohomology.GradedCompositionData.PushforwardData` — Stacks 02RW,
02S2, the three-projection formula of Stacks 0FG0 and the projection formula of Stacks 0FFC.
No carried field refers to graphs. See the implementation notes of the file. -/
@[stacks 0FG3 "the contravariant functor f ↦ [graph f] to correspondences, identity on objects"]
def graphFunctor : Cᵒᵖ ⥤ D.Obj where
  obj X := Obj.mk X.unop
  map f := P.graphHom f.unop
  map_id X := P.graphHom_id X.unop
  map_comp f g := (P.graphHom_comp f.unop g.unop).symm

/-- The graph functor is the identity on objects. -/
@[simp]
theorem graphFunctor_obj (X : Cᵒᵖ) : (P.graphFunctor.obj X).as = X.unop := rfl

/-- The graph functor sends `f : Y ⟶ X` to the class of its graph. -/
@[simp]
theorem graphFunctor_map {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    P.graphFunctor.map f = P.graphHom f.unop := rfl

end PushforwardData

end GradedCompositionData

end Abstract

end Stacks.WeilCohomology

end
