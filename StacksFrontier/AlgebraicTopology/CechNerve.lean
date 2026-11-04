module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Coskeletal
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.IntervalCases

/-!
# Augmentations and morphisms into Čech nerves

Augmentations of simplicial objects, morphisms into the Čech nerve of a morphism, and the canonical
morphism from an augmented simplicial object to a Čech nerve.
-/

/-!
## Augmentations of a simplicial object are morphisms out of degree zero

Let `C` be a category, `X` an object of `C` and `U` a simplicial object of `C`. An augmentation
`ε : U ⟶ X` of `U` towards `X` is a morphism from `U` into the constant simplicial object on
`X` ([Stacks, Tag 018G]). Such an ε is the same thing as a single morphism
`ε₀ : U_0 ⟶ X` satisfying the one equation `ε₀ ∘ d^1_0 = ε₀ ∘ d^1_1`: every augmentation
restricts to such an `ε₀` in degree `0`, and conversely every such `ε₀` is the degree `0`
component of exactly one augmentation, namely the one with `ε_n = ε₀ ∘ U(α)` for any
`α : ⦋0⦌ ⟶ ⦋n⦌`.

Uniqueness holds without that equation: naturality of an augmentation `ε` at
`(SimplexCategory.const ⦋0⦌ i 0).op` expresses `ε.app (op i)` as
`U(const ⦋0⦌ i 0) ≫ ε.app (op ⦋0⦌)`, because every face and degeneracy of the constant
simplicial object is `𝟙 X`. The same naturality at `(SimplexCategory.δ 0).op` and
`(SimplexCategory.δ 1).op` identifies both `U.δ 0 ≫ ε₀` and `U.δ 1 ≫ ε₀` with `ε.app (op ⦋1⦌)`,
which gives the equation. Conversely the equation propagates from the two face maps `U_1 ⟶ U_0`
to all pairs of vertices: any `a : Fin (i.len + 1)` is the image of `1` under
`SimplexCategory.mkOfLe 0 a : ⦋1⦌ ⟶ i`, whose composites with `δ 1` and `δ 0` are the constant
maps at `0` and at `a`.

### Main results

* `CategoryTheory.SimplicialObject.existsUnique_hom_const_app_zero_eq_iff`: a morphism
  `ε₀ : U_0 ⟶ X` is the degree `0` component of a unique morphism `U ⟶ (const C).obj X` if and
  only if `U.δ 0 ≫ ε₀ = U.δ 1 ≫ ε₀`.

### References

* [Stacks, Tag 018H](https://stacks.math.columbia.edu/tag/018H)
-/

section

open CategoryTheory Opposite Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

section

variable (U : SimplicialObject C) {X : C}

/-- Every component of an augmentation `ε : U ⟶ (const C).obj X` is its degree `0` component
composed with the map induced by a vertex, since the faces of the constant simplicial object
are identities. -/
private lemma app_eq_map_const_op_comp_app_zero (ε : U ⟶ (SimplicialObject.const C).obj X)
    (i : SimplexCategoryᵒᵖ) :
    ε.app i = U.map (SimplexCategory.const ⦋0⦌ i.unop 0).op ≫ ε.app (op ⦋0⦌) := by
  simp

variable (ε₀ : U _⦋0⦌ ⟶ X) (h : U.δ 0 ≫ ε₀ = U.δ 1 ≫ ε₀)

include h

/-- If `ε₀ : U_0 ⟶ X` equalizes the two face maps `U_1 ⟶ U_0`, then it is unchanged by the map
induced by any vertex `a` of `i`, compared with the vertex `0`: the two vertices are the ends of
the edge `SimplexCategory.mkOfLe 0 a`. -/
private lemma map_const_op_comp_eq_map_const_zero_op_comp (i : SimplexCategory)
    (a : Fin (i.len + 1)) :
    U.map (SimplexCategory.const ⦋0⦌ i a).op ≫ ε₀ =
      U.map (SimplexCategory.const ⦋0⦌ i 0).op ≫ ε₀ := by
  set γ : ⦋1⦌ ⟶ i := SimplexCategory.mkOfLe (0 : Fin (i.len + 1)) a (Fin.zero_le a)
  have h0 : SimplexCategory.δ (0 : Fin 2) ≫ γ = SimplexCategory.const ⦋0⦌ i a := by
    rw [SimplexCategory.δ_zero_eq_const, SimplexCategory.const_comp]; rfl
  have h1 : SimplexCategory.δ (1 : Fin 2) ≫ γ = SimplexCategory.const ⦋0⦌ i 0 := by
    rw [SimplexCategory.δ_one_eq_const, SimplexCategory.const_comp]; rfl
  rw [← h0, ← h1]
  simp only [op_comp, U.map_comp, Category.assoc]
  rw [← U.δ_def 0, ← U.δ_def 1, h]

/-- The hypothesis of `CategoryTheory.SimplicialObject.augment` follows from its single instance
at `⦋1⦌`: every `g : ⦋0⦌ ⟶ i` is the constant map at the vertex `g 0`. -/
private lemma map_op_comp_eq (i : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ i) :
    U.map g₁.op ≫ ε₀ = U.map g₂.op ≫ ε₀ := by
  rw [SimplexCategory.eq_const_of_zero g₁, SimplexCategory.eq_const_of_zero g₂]
  exact (map_const_op_comp_eq_map_const_zero_op_comp U ε₀ h i _).trans
    (map_const_op_comp_eq_map_const_zero_op_comp U ε₀ h i _).symm

end

/-- Let `U` be a simplicial object of a category `C`, let `X : C` and let `ε₀ : U_0 ⟶ X`. Then `ε₀`
extends to a unique augmentation of `U` towards `X`, i.e. to a unique morphism
`U ⟶ (const C).obj X` with `ε₀` as its degree `0` component, precisely when
`U.δ 0 ≫ ε₀ = U.δ 1 ≫ ε₀`. -/
@[stacks 018H "restriction to degree 0 is a bijection from augmentations of U towards X \
  onto the morphisms ε₀ : U_0 ⟶ X with ε₀ ∘ d^1_0 = ε₀ ∘ d^1_1"]
public theorem existsUnique_hom_const_app_zero_eq_iff (U : SimplicialObject C) (X : C)
    (ε₀ : U _⦋0⦌ ⟶ X) :
    (∃! ε : U ⟶ (const C).obj X, ε.app (op ⦋0⦌) = ε₀) ↔ U.δ 0 ≫ ε₀ = U.δ 1 ≫ ε₀ := by
  constructor
  · rintro ⟨ε, rfl, -⟩
    have h0 := ε.naturality (SimplexCategory.δ (0 : Fin 2)).op
    have h1 := ε.naturality (SimplexCategory.δ (1 : Fin 2)).op
    simp only [Functor.const_obj_map] at h0 h1
    rw [U.δ_def 0, U.δ_def 1, h0, h1]
  · intro h
    refine ⟨(U.augment X ε₀ (map_op_comp_eq U ε₀ h)).hom, U.augment_hom_zero X ε₀ _,
      fun ε hε => ?_⟩
    ext i
    rw [app_eq_map_const_op_comp_app_zero U ε i, hε,
      app_eq_map_const_op_comp_app_zero U (U.augment X ε₀ (map_op_comp_eq U ε₀ h)).hom i,
      U.augment_hom_zero X ε₀ _]
    rfl

end CategoryTheory.SimplicialObject

end

/-!
## Morphisms into the Čech nerve of a morphism

Let `C` be a category with fibred products and let `f : Y ⟶ X` be a morphism of `C`. Let `U` be
the Čech nerve `f.cechNerve` of `f` (Mathlib's `Arrow.cechNerve`), the simplicial object whose
`n`-th term is the `(n + 1)`-fold fibred product `Y ×_X Y ×_X ⋯ ×_X Y`. For every simplicial
object `V` of `C` there are bijections
`Mor(V, U) = Mor(sk₁ V, sk₁ U) = {g₀ : V₀ ⟶ Y | f ∘ g₀ ∘ d¹₀ = f ∘ g₀ ∘ d¹₁}`, and in particular
`U = cosk₁ sk₁ U`.

Here `sk₁` is `SimplicialObject.truncation 1`, restriction along `Δ_{≤1} ↪ Δ`; `cosk₁` is
`SimplicialObject.cosk 1`, the right Kan extension along that inclusion; and `d¹₀, d¹₁ : V₁ ⟶ V₀`
are `V.δ (0 : Fin 2)` and `V.δ (1 : Fin 2)`.

### Main definitions

* `HasCechPullbacks`: the wide pullbacks `Y ×_X ⋯ ×_X Y` of `Fin (n + 1)` copies of `f`, that is
  the terms of the Čech nerve of `f`, all exist.
* `HasCosk₁`: every `1`-truncated simplicial object of `C` has a right Kan extension along
  `(SimplexCategory.Truncated.inclusion 1).op`.
* `π₀`: the projection `U₀ ⟶ Y` out of the degree-`0` term of the Čech nerve.
* `tr0`: the object `[0]` of `SimplexCategory.Truncated 1`.
* `truncationHomEquiv`: morphisms `sk₁ V ⟶ sk₁ W` as natural transformations between the
  restrictions of `V` and `W` along `(SimplexCategory.Truncated.inclusion 1).op`.
* `deg0Component`: the degree-`0` component `V₀ ⟶ Y` of a morphism `sk₁ V ⟶ sk₁ U`.
* `cechNerveIsPointwiseRanAt`: at each object `op [m]` of `Δᵒᵖ`, the canonical cone with apex
  `U_m` over the `1`-truncated comma diagram is a limit cone.
* `cechNerveIsoCosk`: the isomorphism `U ≅ cosk₁ (sk₁ U)` given by the adjunction unit.

### Main results

* `cechNerve_isRightKanExtension`: `U` is the right Kan extension of its own `1`-truncation
  along `(SimplexCategory.Truncated.inclusion 1).op`, with the identity comparison map.
* `truncation_bijective_into_cechNerve`: `g ↦ sk₁ g` is a bijection
  `Mor(V, U) → Mor(sk₁ V, sk₁ U)`.
* `truncated_mor_equiv_setOf`: taking the degree-`0` component is a bijection from
  `Mor(sk₁ V, sk₁ U)` onto the morphisms `g₀ : V₀ ⟶ Y` with
  `V.δ 0 ≫ g₀ ≫ f = V.δ 1 ≫ g₀ ≫ f`.
* `cechNerve_isCoskeletal`: the unit `U ⟶ cosk₁ (sk₁ U)` is an isomorphism.

### References

* [Stacks, Tag 018I](https://stacks.math.columbia.edu/tag/018I)
-/

section

@[expose] public section

open CategoryTheory SimplicialObject Limits Opposite

/-- Two morphisms into a wide pullback over a nonempty family of legs agree as soon as all their
projections agree; the base leg is then automatic. -/
lemma CategoryTheory.Limits.WidePullback.hom_ext_of_π {C : Type*} [Category C] {J : Type*}
    [Nonempty J] {B : C} {objs : J → C} {arrows : ∀ j : J, objs j ⟶ B}
    [HasWidePullback B objs arrows] {T : C} (g g' : T ⟶ widePullback B objs arrows)
    (h : ∀ j : J, g ≫ WidePullback.π arrows j = g' ≫ WidePullback.π arrows j) : g = g' :=
  WidePullback.hom_ext _ _ _ h <| by
    rw [← WidePullback.π_arrow arrows (Classical.arbitrary J), ← Category.assoc, h,
      Category.assoc]

namespace CategoryTheory.SimplicialObject

universe v u

variable {C : Type u} [Category.{v} C]

/-- Every `1`-truncated simplicial object of `C` has a right Kan extension along
`(SimplexCategory.Truncated.inclusion 1).op`; equivalently the `1`-coskeleton functor `cosk₁` on
`C` and its adjunction with `sk₁` exist. -/
class HasCosk₁ (C : Type u) [Category.{v} C] : Prop where
  /-- Every `1`-truncated simplicial object `F` of `C` has a right Kan extension along
  `(SimplexCategory.Truncated.inclusion 1).op`. -/
  has : ∀ (F : (SimplexCategory.Truncated 1)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion 1).op.HasRightKanExtension F

attribute [instance] HasCosk₁.has

/-- The object `[0]` of `SimplexCategory.Truncated 1`. -/
abbrev tr0 : (SimplexCategory.Truncated 1) := ⟨SimplexCategory.mk 0, by norm_num⟩

/-- The structure maps of the `1`-truncation of `V` are the structure maps of `V` along
`(SimplexCategory.Truncated.inclusion 1).op`. -/
lemma truncation_obj_map (V : SimplicialObject C) {X Z : (SimplexCategory.Truncated 1)ᵒᵖ}
    (θ : X ⟶ Z) :
    ((truncation 1).obj V).map θ = V.map ((SimplexCategory.Truncated.inclusion 1).op.map θ) :=
  rfl

/-- The `1`-truncation of `V` is its restriction along
`(SimplexCategory.Truncated.inclusion 1).op`. -/
lemma truncation_obj_eq (V : SimplicialObject C) :
    (truncation 1).obj V = (SimplexCategory.Truncated.inclusion 1).op ⋙ V := by
  rw [truncation, Functor.whiskeringLeft_obj_obj]

/-- Morphisms `sk₁ V ⟶ sk₁ W` are the natural transformations between the restrictions of `V` and
`W` along `(SimplexCategory.Truncated.inclusion 1).op`. -/
def truncationHomEquiv (V W : SimplicialObject C) :
    ((truncation 1).obj V ⟶ (truncation 1).obj W) ≃
      ((SimplexCategory.Truncated.inclusion 1).op ⋙ V ⟶
        (SimplexCategory.Truncated.inclusion 1).op ⋙ W) :=
  (CategoryTheory.eqToIso (truncation_obj_eq V)).homCongr
    (CategoryTheory.eqToIso (truncation_obj_eq W))

end CategoryTheory.SimplicialObject

namespace CategoryTheory.Arrow

universe v u

variable {C : Type u} [Category.{v} C]

/-- The wide pullbacks `Y ×_X ⋯ ×_X Y` of `Fin (n + 1)` copies of `f : Y ⟶ X`, that is the terms
of the Čech nerve of `f`, all exist. -/
class HasCechPullbacks (f : Arrow C) : Prop where
  has : ∀ (n : ℕ), HasWidePullback f.right (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom)

attribute [instance] HasCechPullbacks.has

section

variable (f : Arrow C) [HasCechPullbacks f]

/-- The projection `U₀ ⟶ Y` out of the degree-`0` term of the Čech nerve of `f : Y ⟶ X`, which is
the wide pullback of a single copy of `f`. -/
noncomputable def π₀ :
    (cechNerve f).obj (op (SimplexCategory.mk 0)) ⟶ f.left :=
  WidePullback.π (fun _ : Fin 1 => f.hom) 0

/-- A structure map of the Čech nerve `U` followed by the `j`-th projection is the projection
indexed by the image of `j`. -/
lemma cechNerve_map_π {X Z : SimplexCategoryᵒᵖ} (g : X ⟶ Z) (j : Fin (Z.unop.len + 1)) :
    (cechNerve f).map g ≫ WidePullback.π (fun _ : Fin (Z.unop.len + 1) => f.hom) j
      = WidePullback.π (fun _ : Fin (X.unop.len + 1) => f.hom)
          (SimplexCategory.Hom.toOrderHom g.unop j) := by
  rw [Arrow.cechNerve_map, WidePullback.lift_π]

/-- The structure map of the Čech nerve `U` along the vertex `j` of `[n]`, followed by
`π₀ : U₀ ⟶ Y`, is the `j`-th projection `U_n ⟶ Y`. -/
lemma cechNerve_map_const_π₀ {n : SimplexCategory} (j : Fin (n.len + 1)) :
    (cechNerve f).map (SimplexCategory.const (SimplexCategory.mk 0) n j).op ≫ π₀ f
      = WidePullback.π (fun _ : Fin (n.len + 1) => f.hom) j := by
  rw [π₀, cechNerve_map_π, Quiver.Hom.unop_op, SimplexCategory.const_apply]

/-- A structure map of the Čech nerve `U` followed by the map to `X` is the map to `X`. -/
lemma cechNerve_map_base {X Z : SimplexCategoryᵒᵖ} (g : X ⟶ Z) :
    (cechNerve f).map g ≫ WidePullback.base (fun _ : Fin (Z.unop.len + 1) => f.hom)
      = WidePullback.base (fun _ : Fin (X.unop.len + 1) => f.hom) := by
  rw [Arrow.cechNerve_map, WidePullback.lift_base]

end

/-- If `g₀ : V₀ ⟶ Y` satisfies `f ∘ g₀ ∘ d¹₀ = f ∘ g₀ ∘ d¹₁`, then `f ∘ g₀ ∘ V(const i)` does not
depend on the vertex `i` of a `1`-truncated simplex. -/
lemma map_const_comp_eq (f : Arrow C) {V : SimplicialObject C}
    {g₀ : V.obj (op (SimplexCategory.mk 0)) ⟶ f.left}
    (hg : V.δ (0 : Fin 2) ≫ g₀ ≫ f.hom = V.δ (1 : Fin 2) ≫ g₀ ≫ f.hom) :
    ∀ (X : SimplexCategory.Truncated 1) (i : Fin (X.obj.len + 1)),
      (V.map (SimplexCategory.const (SimplexCategory.mk 0) X.obj i).op ≫ g₀) ≫ f.hom
        = V.map (SimplexCategory.const (SimplexCategory.mk 0) X.obj 0).op ≫ g₀ ≫ f.hom :=
  fun X i => (Category.assoc _ _ _).trans
    (map_const_op_comp_eq_map_const_zero_op_comp V (g₀ ≫ f.hom) hg X.obj i)

/-- The degree-`0` component `V₀ ⟶ Y` of a morphism `sk₁ V ⟶ sk₁ U` of `1`-truncated simplicial
objects, namely its component at `[0]` followed by the projection `π₀ : U₀ ⟶ Y`. -/
noncomputable def deg0Component {f : Arrow C} [HasCechPullbacks f] {V : SimplicialObject C}
    (g : (truncation 1).obj V ⟶ (truncation 1).obj (cechNerve f)) :
    V.obj (op (SimplexCategory.mk 0)) ⟶ f.left :=
  (truncationHomEquiv V _ g).app (op tr0) ≫ π₀ f

/-- The degree-`0` component of a morphism `sk₁ V ⟶ sk₁ U` satisfies the cocycle condition
`f ∘ g₀ ∘ d¹₀ = f ∘ g₀ ∘ d¹₁`. -/
lemma deg0Component_cocycle {f : Arrow C} [HasCechPullbacks f] {V : SimplicialObject C}
    (g : (truncation 1).obj V ⟶ (truncation 1).obj (cechNerve f)) :
    V.δ (0 : Fin 2) ≫ deg0Component g ≫ f.hom
      = V.δ (1 : Fin 2) ≫ deg0Component g ≫ f.hom := by
  have step : ∀ (i : Fin 2),
      V.δ i ≫ deg0Component g ≫ f.hom
        = (truncationHomEquiv V _ g).app
            (op ⟨SimplexCategory.mk 1, by norm_num⟩ : (SimplexCategory.Truncated 1)ᵒᵖ) ≫
            WidePullback.base (fun _ : Fin 2 => f.hom) := fun i => by
    have hnat := (truncationHomEquiv V _ g).naturality
      (Quiver.Hom.op (⟨SimplexCategory.δ i⟩ : (tr0 ⟶ ⟨SimplexCategory.mk 1, by norm_num⟩)))
    rw [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, ObjectProperty.ι_map] at hnat
    rw [deg0Component, Category.assoc, π₀, WidePullback.π_arrow, ← Category.assoc, δ_def, hnat,
      Category.assoc]
    congr 1
    exact cechNerve_map_base f _
  rw [step 0, step 1]

/-- The functor `(SimplexCategory.Truncated.inclusion 1).op : Δ_{≤1}ᵒᵖ ⥤ Δᵒᵖ`. -/
local notation "L₁" => Functor.op (SimplexCategory.Truncated.inclusion 1)

/-- The vertex `i` of `[m]`, as the object `[0] ⟶ [m]` of the comma category
`StructuredArrow (op [m]) (SimplexCategory.Truncated.inclusion 1).op`. -/
abbrev vertexArrow (M : SimplexCategory) (i : Fin (M.len + 1)) :
    StructuredArrow (op M) (SimplexCategory.Truncated.inclusion 1).op :=
  StructuredArrow.mk (Y := op tr0)
    (Quiver.Hom.op (SimplexCategory.const (SimplexCategory.mk 0) M i))

/-- For each object `op [m]` of `Δᵒᵖ`, the canonical cone with apex `U_m` over the comma diagram
`StructuredArrow.proj (op [m]) L ⋙ (L ⋙ cechNerve f)` of `L = (Truncated.inclusion 1).op` is a
limit cone; that is, `RightExtension.mk (cechNerve f) (𝟙 _)` is a pointwise right Kan extension
at `op [m]`. -/
noncomputable def cechNerveIsPointwiseRanAt
    (f : Arrow C) [HasCechPullbacks f]
    (Y : SimplexCategoryᵒᵖ) :
    (Functor.RightExtension.mk (cechNerve f)
        (𝟙 ((SimplexCategory.Truncated.inclusion 1).op ⋙ cechNerve
            f))).IsPointwiseRightKanExtensionAt Y := by
  obtain ⟨M⟩ := Y
  have key : ∀ (s : Cone (StructuredArrow.proj (op M) L₁ ⋙ (L₁ ⋙ cechNerve f)))
      (g : StructuredArrow (op M) L₁) (j : Fin ((g.right.unop).obj.len + 1)),
      s.π.app g ≫ WidePullback.π (fun _ : Fin ((g.right.unop).obj.len + 1) => f.hom) j
        = s.π.app (vertexArrow M ((SimplexCategory.Hom.toOrderHom g.hom.unop) j))
            ≫ WidePullback.π (fun _ : Fin 1 => f.hom) 0 := by
    intro s g j
    let α : g ⟶ vertexArrow M ((SimplexCategory.Hom.toOrderHom g.hom.unop) j) :=
      StructuredArrow.homMk
        (Quiver.Hom.op
          (⟨SimplexCategory.const (SimplexCategory.mk 0) (g.right.unop).obj j⟩ :
            (tr0 ⟶ g.right.unop)))
        (Quiver.Hom.unop_inj.eq_iff.mp (SimplexCategory.Hom.ext_zero_left _ _ rfl))
    have hπ : (cechNerve f).map ((L₁).map α.right) ≫ π₀ f
        = WidePullback.π (fun _ : Fin ((g.right.unop).obj.len + 1) => f.hom) j := by
      simp only [α, StructuredArrow.homMk_right, Functor.op_map, Quiver.Hom.unop_op,
        ObjectProperty.ι_map]
      exact cechNerve_map_const_π₀ f j
    rw [← hπ, ← Category.assoc, π₀]
    exact congrArg (· ≫ WidePullback.π (fun _ : Fin 1 => f.hom) 0) (s.w α)
  have hvtxπ : ∀ i : Fin (M.len + 1),
      (cechNerve f).map (vertexArrow M i).hom ≫ π₀ f
        = WidePullback.π (fun _ : Fin (M.len + 1) => f.hom) i := fun i => by
    rw [StructuredArrow.mk_hom_eq_self]
    exact cechNerve_map_const_π₀ f i
  have legπ : ∀ (g : StructuredArrow (op M) L₁),
      ((Functor.RightExtension.mk (cechNerve f) (𝟙 (L₁ ⋙ cechNerve f))).coneAt
          (op M)).π.app g
        = (cechNerve f).map g.hom := fun _ => by
    simp [Functor.RightExtension.coneAt_π_app]
  let edge : Fin (M.len + 1) → StructuredArrow (op M) L₁ := fun i =>
    StructuredArrow.mk (Y := op (⟨SimplexCategory.mk 1, by norm_num⟩ :
        SimplexCategory.Truncated 1)) (S := op M) (T := L₁)
      (Quiver.Hom.op (SimplexCategory.mkHom ⟨![(0 : Fin (M.len+1)), i], by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp_all⟩))
  have hedge₀ : ∀ i, (SimplexCategory.Hom.toOrderHom (edge i).hom.unop) 0 = 0 := fun _ => by
    simp [edge]
  have hedge₁ : ∀ i, (SimplexCategory.Hom.toOrderHom (edge i).hom.unop) 1 = i := fun _ => by
    simp [edge]
  unfold Functor.RightExtension.IsPointwiseRightKanExtensionAt
  refine IsLimit.mk ?lift ?fac ?uniq
  · intro s
    refine (WidePullback.lift
      ((s.π.app (vertexArrow M 0) ≫ WidePullback.π (fun _ : Fin 1 => f.hom) 0) ≫ f.hom)
      (fun i => s.π.app (vertexArrow M i) ≫ WidePullback.π (fun _ : Fin 1 => f.hom) 0) ?_)
    intro i
    have k₁ := key s (edge i) 1
    have k₀ := key s (edge i) 0
    rw [hedge₁] at k₁
    rw [hedge₀] at k₀
    rw [← k₁, ← k₀]
    simp
  · intro s j
    rw [legπ]
    refine WidePullback.hom_ext_of_π _ _ (fun i => ?_)
    rw [Category.assoc]
    refine (congrArg (_ ≫ ·) (cechNerve_map_π f j.hom i)).trans ?_
    rw [WidePullback.lift_π]
    exact (key s j i).symm
  · intro s mm hmm
    refine WidePullback.hom_ext_of_π _ _ (fun i => ?_)
    rw [WidePullback.lift_π]
    have hm := hmm (vertexArrow M i)
    rw [legπ] at hm
    rw [← hvtxπ i, ← Category.assoc, hm, π₀]

/-- The Čech nerve `U` of `f` is the right Kan extension of its own `1`-truncation
`(SimplexCategory.Truncated.inclusion 1).op ⋙ U` along
`(SimplexCategory.Truncated.inclusion 1).op`, with the identity as comparison map. -/
theorem cechNerve_isRightKanExtension (f : Arrow C) [HasCechPullbacks f] :
    (cechNerve f).IsRightKanExtension
      (𝟙 ((SimplexCategory.Truncated.inclusion 1).op ⋙ cechNerve f)) :=
  Functor.RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (E := Functor.RightExtension.mk (cechNerve f) _) (cechNerveIsPointwiseRanAt f)

/-- For a simplicial object `V` and the Čech nerve `U` of `f : Y ⟶ X`,
the map `Mor(V, U) → Mor(sk₁ V, sk₁ U)`, `g ↦ sk₁ g`, induced by the `1`-truncation functor, is a
bijection. -/
@[stacks 018I "(1)"]
theorem truncation_bijective_into_cechNerve
    (f : Arrow C) [HasCechPullbacks f] (V : SimplicialObject C) :
    Function.Bijective
      (fun g : V ⟶ cechNerve f => (truncation 1).map g) := by
  have := cechNerve_isRightKanExtension f
  have key : ⇑((cechNerve f).homEquivOfIsRightKanExtension
      (𝟙 ((SimplexCategory.Truncated.inclusion 1).op ⋙ cechNerve f)) V)
        = fun g => Functor.whiskerLeft (SimplexCategory.Truncated.inclusion 1).op g := by
    funext g
    simp [Functor.homEquivOfIsRightKanExtension]
  rw [truncation]
  simp only [Functor.whiskeringLeft_obj_map]
  rw [← key]
  exact Equiv.bijective _

/-- Morphisms `sk₁ V ⟶ sk₁ U` of `1`-truncated simplicial objects
correspond bijectively to the morphisms `g₀ : V₀ ⟶ Y` satisfying
`f ∘ g₀ ∘ d¹₀ = f ∘ g₀ ∘ d¹₁`, the bijection sending `g` to its degree-`0` component
`deg0Component g`. -/
@[stacks 018I "(2)"]
theorem truncated_mor_equiv_setOf
    (f : Arrow C) [HasCechPullbacks f] (V : SimplicialObject C) :
    ∃ e : ((truncation 1).obj V ⟶ (truncation 1).obj (cechNerve f)) ≃
        { g₀ : V.obj (op (SimplexCategory.mk 0)) ⟶ f.left //
            V.δ (0 : Fin 2) ≫ g₀ ≫ f.hom = V.δ (1 : Fin 2) ≫ g₀ ≫ f.hom },
      ∀ g, (e g : V.obj (op (SimplexCategory.mk 0)) ⟶ f.left) = deg0Component g := by
  have vtxComp : ∀ (g : (SimplexCategory.Truncated.inclusion 1).op ⋙ V ⟶
        (SimplexCategory.Truncated.inclusion 1).op ⋙ cechNerve f)
      (Z : (SimplexCategory.Truncated 1)ᵒᵖ) (j : Fin (Z.unop.obj.len+1)),
      V.map (SimplexCategory.const (SimplexCategory.mk 0) Z.unop.obj j).op
          ≫ deg0Component ((truncationHomEquiv V _).symm g)
        = g.app Z ≫ WidePullback.π (fun _ : Fin (Z.unop.obj.len+1) => f.hom) j := by
    intro g Z j
    have hnat := g.naturality
      (Quiver.Hom.op (⟨SimplexCategory.const (SimplexCategory.mk 0) Z.unop.obj j⟩ : tr0 ⟶ Z.unop))
    simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, ObjectProperty.ι_map] at hnat
    rw [deg0Component, Equiv.apply_symm_apply, ← Category.assoc, hnat, Category.assoc]
    exact congrArg (g.app Z ≫ ·) (cechNerve_map_const_π₀ f j)
  let mkApp : ∀ (g₀ : V.obj (op (SimplexCategory.mk 0)) ⟶ f.left),
      (∀ (X : SimplexCategory.Truncated 1) (i : Fin (X.obj.len + 1)),
        (V.map (SimplexCategory.const (SimplexCategory.mk 0) X.obj i).op ≫ g₀) ≫ f.hom
          = V.map (SimplexCategory.const (SimplexCategory.mk 0) X.obj 0).op ≫ g₀ ≫ f.hom) →
      ∀ (Z : (SimplexCategory.Truncated 1)ᵒᵖ),
        ((SimplexCategory.Truncated.inclusion 1).op ⋙ V).obj Z ⟶
          ((SimplexCategory.Truncated.inclusion 1).op ⋙ cechNerve f).obj Z :=
    fun g₀ hcoc Z => WidePullback.lift
      (V.map (SimplexCategory.const (SimplexCategory.mk 0) Z.unop.obj 0).op ≫ g₀ ≫ f.hom)
      (fun i => V.map (SimplexCategory.const (SimplexCategory.mk 0) Z.unop.obj i).op ≫ g₀)
      (fun i => hcoc Z.unop i)
  have mkAppπ : ∀ (g₀) (hcoc) (Z : (SimplexCategory.Truncated 1)ᵒᵖ) (j : Fin (Z.unop.obj.len+1)),
      mkApp g₀ hcoc Z ≫ WidePullback.π (fun _ : Fin (Z.unop.obj.len+1) => f.hom) j
        = V.map (SimplexCategory.const (SimplexCategory.mk 0) Z.unop.obj j).op ≫ g₀ :=
    fun _ _ _ j => WidePullback.lift_π _ _ _ _ j
  have hmapπ : ∀ (X Y : (SimplexCategory.Truncated 1)ᵒᵖ) (θ : X ⟶ Y) (j : Fin (Y.unop.obj.len+1)),
      ((SimplexCategory.Truncated.inclusion 1).op ⋙ cechNerve f).map θ
          ≫ WidePullback.π (fun _ : Fin (Y.unop.obj.len+1) => f.hom) j
        = WidePullback.π (fun _ : Fin (X.unop.obj.len+1) => f.hom)
            (SimplexCategory.Hom.toOrderHom
              ((SimplexCategory.Truncated.inclusion 1).op.map θ).unop j) :=
    fun _ _ θ j => cechNerve_map_π f ((SimplexCategory.Truncated.inclusion 1).op.map θ) j
  have mkNat : ∀ (g₀) (hcoc) (X Y : (SimplexCategory.Truncated 1)ᵒᵖ) (θ : X ⟶ Y),
      ((SimplexCategory.Truncated.inclusion 1).op ⋙ V).map θ ≫ mkApp g₀ hcoc Y
        = mkApp g₀ hcoc X ≫ ((SimplexCategory.Truncated.inclusion 1).op ⋙ cechNerve f).map θ := by
    intro g₀ hcoc X Y θ
    have natπ : ∀ (j : Fin (Y.unop.obj.len+1)),
        (((SimplexCategory.Truncated.inclusion 1).op ⋙ V).map θ ≫ mkApp g₀ hcoc Y)
            ≫ WidePullback.π (fun _ : Fin (Y.unop.obj.len+1) => f.hom) j
          = (mkApp g₀ hcoc X ≫ ((SimplexCategory.Truncated.inclusion 1).op ⋙ cechNerve f).map θ)
              ≫ WidePullback.π (fun _ : Fin (Y.unop.obj.len+1) => f.hom) j := fun j => by
      rw [Category.assoc, mkAppπ g₀ hcoc Y j, Category.assoc, hmapπ X Y θ j, mkAppπ g₀ hcoc X _,
        Functor.comp_map, ← Category.assoc, ← V.map_comp,
        show ((SimplexCategory.Truncated.inclusion 1).op.map θ) ≫ (SimplexCategory.const
          (SimplexCategory.mk 0) Y.unop.obj j).op
            = (SimplexCategory.const (SimplexCategory.mk 0) Y.unop.obj j ≫
                ((SimplexCategory.Truncated.inclusion 1).op.map θ).unop).op from rfl,
        SimplexCategory.const_comp _ _ j]
      rfl
    exact WidePullback.hom_ext_of_π _ _ natπ
  refine ⟨(truncationHomEquiv V _).trans {
    toFun := fun g => ⟨deg0Component ((truncationHomEquiv V _).symm g), deg0Component_cocycle _⟩
    invFun := fun ⟨g₀, hg⟩ =>
      { app := mkApp g₀ (map_const_comp_eq f hg)
        naturality := mkNat g₀ (map_const_comp_eq f hg) }
    left_inv := ?_
    right_inv := ?_ }, ?_⟩
  · exact fun g => NatTrans.ext (funext fun Z => WidePullback.hom_ext_of_π _ _ fun j =>
      (mkAppπ _ (map_const_comp_eq f (deg0Component_cocycle _)) Z j).trans (vtxComp g Z j))
  · rintro ⟨g₀, hg⟩
    apply Subtype.ext
    dsimp only
    rw [deg0Component, Equiv.apply_symm_apply, π₀]
    refine (mkAppπ g₀ (map_const_comp_eq f hg) (op tr0) 0).trans ?_
    have hid : SimplexCategory.const (SimplexCategory.mk 0) (op tr0).unop.obj 0
        = 𝟙 (SimplexCategory.mk 0) := SimplexCategory.const_eq_id
    rw [hid, op_id, V.map_id, Category.id_comp]
  · intro g
    simp

/-- The Čech nerve `U` is `1`-coskeletal: the unit
`U ⟶ cosk₁ (sk₁ U)` of the `sk₁`/`cosk₁` adjunction is an isomorphism. -/
@[stacks 018I "(3)"]
theorem cechNerve_isCoskeletal
    (f : Arrow C) [HasCechPullbacks f] [HasCosk₁ C] :
    IsIso ((coskAdj (C := C) 1).unit.app (cechNerve f)) :=
  (isCoskeletal_iff_isIso (cechNerve f) 1).mp ⟨cechNerve_isRightKanExtension f⟩

/-- The isomorphism `U ≅ cosk₁ (sk₁ U)` between the Čech nerve of `f` and the `1`-coskeleton of
its `1`-truncation, given by the unit of the `sk₁`/`cosk₁` adjunction. -/
noncomputable def cechNerveIsoCosk
    (f : Arrow C) [HasCechPullbacks f] [HasCosk₁ C] :
    cechNerve f ≅ (cosk 1).obj (cechNerve f) :=
  have : IsIso ((coskAdj (C := C) 1).unit.app (cechNerve f)) :=
    cechNerve_isCoskeletal f
  asIso ((coskAdj (C := C) 1).unit.app (cechNerve f))

end CategoryTheory.Arrow

end

end

/-!
## The canonical morphism from an augmented simplicial object to a Čech nerve

Let `C` be a category with fibre products, let `V` be a simplicial object of `C` and let
`ε : V ⟶ X` be an augmentation of `V` towards an object `X` of `C` ([Stacks, Tag 018G]), with
degree `0` component `ε₀ : V_0 ⟶ X`. Let `U` be the simplicial object whose `n`th term is the
`(n + 1)`-fold fibre product `V_0 ×_X ⋯ ×_X V_0`, i.e. the Čech nerve of `ε₀`
([Stacks, Example 016E]). Then there is a canonical morphism `V ⟶ U`: its `n`th component is
`(V(α_0), …, V(α_n)) : V_n ⟶ V_0 ×_X ⋯ ×_X V_0`, where `α_i : ⦋0⦌ ⟶ ⦋n⦌` picks out the vertex `i`,
the required compatibility over `X` holding because `ε` is an augmentation ([Stacks, Tag 018H]),
and it is the unique morphism `V ⟶ U` which is the identity of `V_0` in degree `0`
([Stacks, Tag 018I]).

### Main results

* `CategoryTheory.SimplicialObject.existsUnique_hom_cechNerve_app_zero_comp_π_eq_id`: there is a
  unique morphism `g : V ⟶ (Arrow.mk ε₀).cechNerve` whose degree `0` component is the canonical
  isomorphism `V_0 ≅ V_0 ×_X X`, i.e. with `g.app (op ⦋0⦌) ≫ WidePullback.π _ 0 = 𝟙 V_0`.

### References

* [Stacks, Tag 018J](https://stacks.math.columbia.edu/tag/018J)
-/

section

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

section

variable (f : Arrow C)
  [∀ n : ℕ, HasWidePullback.{0} f.right (fun _ : Fin (n + 1) => f.left) fun _ => f.hom]
  {V : SimplicialObject C}

/-- The `i`th projection of the degree `n` component of a morphism `g` from a simplicial object `V`
into the Čech nerve of an arrow `f` is `V(α_i)` followed by the degree `0` component of `g`
projected to `f.left`, where `α_i : ⦋0⦌ ⟶ ⦋n⦌` is the vertex `i`. -/
private lemma app_comp_π (g : V ⟶ f.cechNerve) (n : SimplexCategoryᵒᵖ)
    (i : Fin (n.unop.len + 1)) :
    g.app n ≫ WidePullback.π _ i =
      V.map (SimplexCategory.const ⦋0⦌ n.unop i).op ≫ g.app (op ⦋0⦌) ≫ WidePullback.π _ 0 := by
  have : f.HasCechPullbacks := ⟨inferInstance⟩
  rw [← f.cechNerve_map_const_π₀ i, ← Category.assoc,
    ← g.naturality (SimplexCategory.const ⦋0⦌ n.unop i).op, Category.assoc]
  rfl

/-- A morphism from a simplicial object into the Čech nerve of an arrow `f` is determined by the
composite of its degree `0` component with the projection to `f.left`. -/
private lemma hom_ext_of_app_zero_comp_π (g g' : V ⟶ f.cechNerve)
    (h : g.app (op ⦋0⦌) ≫ WidePullback.π _ 0 = g'.app (op ⦋0⦌) ≫ WidePullback.π _ 0) : g = g' := by
  ext n : 2
  refine WidePullback.hom_ext_of_π _ _ fun j => ?_
  rw [app_comp_π f g, app_comp_π f g', h]

end

/-- The morphism `W.left ⟶ F.cechNerve` that the Čech adjunction produces from
`h : Augmented.toArrow.obj W ⟶ F` recovers `h.left` in degree `0`: its degree `0` component
composed with the projection to `F.left` is `h.left` again. -/
private lemma equivalenceLeftToRight_left_app_zero_comp_π [HasFiniteWidePullbacks C]
    (W : SimplicialObject.Augmented C) (F : Arrow C)
    (h : SimplicialObject.Augmented.toArrow.obj W ⟶ F) :
    (SimplicialObject.equivalenceLeftToRight W F h).left.app (op ⦋0⦌) ≫ WidePullback.π _ 0 =
      h.left :=
  congrArg Arrow.Hom.left ((SimplicialObject.cechNerveEquiv W F).symm_apply_apply h)

/-- Let `C` be a category with fibre products, let `V` be a simplicial object of `C` and let
`ε : V ⟶ (const C).obj X` be an augmentation of `V` towards `X : C`, with degree `0` component
`ε₀ : V_0 ⟶ X`. Let `U` be the Čech nerve of `ε₀`, whose `n`th term is the `(n + 1)`-fold fibre
product `V_0 ×_X ⋯ ×_X V_0`. Then there is exactly one morphism `V ⟶ U` whose degree `0` component
is the canonical isomorphism `V_0 ≅ V_0 ×_X X`. -/
@[stacks 018J "the canonical morphism V ⟶ U, pinned as the unique morphism to the Čech nerve \
  of ε₀ which is the identity of V_0 in degree 0"]
public theorem existsUnique_hom_cechNerve_app_zero_comp_π_eq_id [HasFiniteWidePullbacks C]
    (V : SimplicialObject C) (X : C) (ε : V ⟶ (const C).obj X) :
    ∃! g : V ⟶ (Arrow.mk (ε.app (op ⦋0⦌) : V _⦋0⦌ ⟶ X)).cechNerve,
      g.app (op ⦋0⦌) ≫ WidePullback.π _ 0 = 𝟙 (V _⦋0⦌) := by
  have key := equivalenceLeftToRight_left_app_zero_comp_π
    (⟨V, X, ε⟩ : SimplicialObject.Augmented C) (Arrow.mk (ε.app (op ⦋0⦌))) (𝟙 _)
  exact ⟨_, key, fun g hg => hom_ext_of_app_zero_comp_π _ g _ (hg.trans key.symm)⟩

end CategoryTheory.SimplicialObject

end
