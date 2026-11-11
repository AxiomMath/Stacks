module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Actions of group schemes, by their functor of points

Let `S` be a scheme and `(G, m)` a group scheme over `S`. An action of `G` on a scheme `X` over
`S` is a morphism `a : G ×_S X ⟶ X` of schemes over `S` such that, for every scheme `T` over
`S`, the induced map `G(T) × X(T) ⟶ X(T)`, `(g, x) ↦ a ∘ (g, x)`, makes the set `X(T)` of
`T`-valued points a `G(T)`-set. If `X` and `Y` are schemes over `S` with actions of `G`, a
morphism `ψ : X ⟶ Y` of schemes over `S` is `G`-equivariant if for every `T` over `S` the map
`ψ : X(T) ⟶ Y(T)` is a morphism of `G(T)`-sets.

Group schemes over `S` are `AlgebraicGeometry.GroupSchemeOverPoints`, the functor-of-points
definition of the source, and the fibre product `G ×_S X` is the cartesian product `G ⊗ X` of
`Over S`. Through the internal group object `AlgebraicGeometry.GroupSchemeOverPoints.grpObj`,
these actions are exactly the module objects `CategoryTheory.ModObj` of Mathlib, and equivariant
morphisms are exactly the morphisms `CategoryTheory.IsModHom` of module objects.

## Main definitions

* `AlgebraicGeometry.GroupSchemeOverPoints.Action` is an action of a group scheme `G` over `S`
  on a scheme `X` over `S`, in the functor-of-points sense of the source.
* `AlgebraicGeometry.GroupSchemeOverPoints.Action.mulAction` is the `G(T)`-set structure on
  `X(T)` induced by an action.
* `AlgebraicGeometry.GroupSchemeOverPoints.Action.IsEquivariant` is `G`-equivariance of a
  morphism between schemes over `S` endowed with actions of `G`.

## Main results

* `AlgebraicGeometry.GroupSchemeOverPoints.Action.exists_act_eq_iff` characterizes the action
  morphisms of actions by the commutativity of the associativity and unit diagrams.
* `AlgebraicGeometry.GroupSchemeOverPoints.Action.isEquivariant_iff_comp` characterizes
  equivariance by the single identity `a ≫ ψ = (G ◁ ψ) ≫ b` of morphisms over `S`.
* `AlgebraicGeometry.GroupSchemeOverPoints.Action.equivModObj` identifies actions of `G` on `X`
  with Mathlib's module objects `ModObj` over the internal group object of `G`.
* `AlgebraicGeometry.GroupSchemeOverPoints.Action.isEquivariant_iff_isModHom` identifies
  equivariant morphisms with Mathlib's morphisms `IsModHom` of module objects.

## Implementation notes

A `G(T)`-set structure on `X(T)` whose action map is `(g, x) ↦ a ∘ (g, x)` exists exactly when
this map satisfies the two axioms of a left group action, that the identity acts trivially and
that `(g h) x = g (h x)`; these two conditions, for every `T`, are the fields of
`AlgebraicGeometry.GroupSchemeOverPoints.Action`, and the structure itself is
`AlgebraicGeometry.GroupSchemeOverPoints.Action.mulAction`. The group `G(T)` is the group of
`T`-valued points given by the group scheme, and its multiplication is induced by `m`.

## References

* [Stacks Project, Tag 022Z](https://stacks.math.columbia.edu/tag/022Z)
* [Stacks Project, Tag 03LD](https://stacks.math.columbia.edu/tag/03LD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory

universe u

namespace AlgebraicGeometry

namespace GroupSchemeOverPoints

variable {S : Scheme.{u}} (G : GroupSchemeOverPoints S)

/-- Precomposition with a morphism `φ : T' ⟶ T` over `S` is multiplicative on points. -/
lemma comp_mul {T T' : Over S} (φ : T' ⟶ T) (a b : T ⟶ G.obj) :
    φ ≫ (a * b) = (φ ≫ a) * (φ ≫ b) := by
  rw [G.mul_eq, G.mul_eq, ← Category.assoc, comp_lift]

/-- Precomposition with a morphism `φ : T' ⟶ T` over `S` preserves the identity point. -/
lemma comp_one {T T' : Over S} (φ : T' ⟶ T) : φ ≫ (1 : T ⟶ G.obj) = 1 := by
  have h : (φ ≫ (1 : T ⟶ G.obj)) * (φ ≫ 1) = φ ≫ 1 := by rw [← G.comp_mul, mul_one]
  exact mul_eq_left.mp h

/-- **Stacks Project, Tag 022Z** (1). An action of the group scheme `G` over `S` on the scheme
`X` over `S`: a morphism `a : G ×_S X ⟶ X` of schemes over `S` such that for every scheme `T`
over `S` the map `G(T) × X(T) ⟶ X(T)`, `(g, x) ↦ a ∘ (g, x)`, defines the structure of a
`G(T)`-set on `X(T)`, namely the identity of `G(T)` acts trivially and `(g h) x = g (h x)`. -/
@[stacks 022Z "part (1): an action of a group scheme on a scheme over the base"]
structure Action (X : Over S) where
  /-- The action morphism `a : G ×_S X ⟶ X` over `S`. -/
  act : G.obj ⊗ X ⟶ X
  /-- The identity of `G(T)` acts trivially on `X(T)`, for every `T` over `S`. -/
  one_smul (T : Over S) (x : T ⟶ X) : lift 1 x ≫ act = x
  /-- The induced map is compatible with the multiplication of `G(T)`, for every `T` over `S`. -/
  mul_smul (T : Over S) (g h : T ⟶ G.obj) (x : T ⟶ X) :
    lift (g * h) x ≫ act = lift g (lift h x ≫ act) ≫ act

namespace Action

variable {G} {X Y Z : Over S}

/-- Two actions of `G` on `X` with the same action morphism are equal. -/
@[ext]
lemma ext {A B : G.Action X} (h : A.act = B.act) : A = B := by
  cases A
  cases B
  cases h
  rfl

/-- The structure of a `G(T)`-set on `X(T)` defined by an action of `G` on `X`: a point
`g` of `G(T)` acts on a point `x` of `X(T)` by `a ∘ (g, x)`. -/
noncomputable abbrev mulAction (A : G.Action X) (T : Over S) : MulAction (T ⟶ G.obj) (T ⟶ X) where
  smul g x := lift g x ≫ A.act
  one_smul := A.one_smul T
  mul_smul := A.mul_smul T

/-- In the `G(T)`-set `X(T)` defined by an action `a`, the point `g` acts on `x` by
`a ∘ (g, x)`. -/
lemma smul_def (A : G.Action X) {T : Over S} (g : T ⟶ G.obj) (x : T ⟶ X) :
    letI := A.mulAction T
    g • x = lift g x ≫ A.act :=
  rfl

/-- The action on points is natural in the test scheme: for `φ : T' ⟶ T` over `S`,
`φ ∘ (g x) = (φ ∘ g) (φ ∘ x)`. -/
lemma comp_smul (A : G.Action X) {T T' : Over S} (φ : T' ⟶ T) (g : T ⟶ G.obj) (x : T ⟶ X) :
    φ ≫ (lift g x ≫ A.act) = lift (φ ≫ g) (φ ≫ x) ≫ A.act := by
  rw [← Category.assoc, comp_lift]

/-- **Stacks Project, Tag 022Z** (2). A morphism `ψ : X ⟶ Y` of schemes over `S`, where `X` and
`Y` carry actions `A` and `B` of `G`, is `G`-equivariant if for every scheme `T` over `S` the
map `ψ : X(T) ⟶ Y(T)` is a morphism of `G(T)`-sets. -/
@[stacks 022Z "part (2): equivariant morphisms"]
def IsEquivariant (A : G.Action X) (B : G.Action Y) (ψ : X ⟶ Y) : Prop :=
  ∀ (T : Over S) (g : T ⟶ G.obj) (x : T ⟶ X),
    letI := A.mulAction T
    letI := B.mulAction T
    (g • x) ≫ ψ = g • (x ≫ ψ)

/-- Equivariance spelled out with the action morphisms: `ψ ∘ a ∘ (g, x) = b ∘ (g, ψ ∘ x)` for
all points `g` of `G(T)` and `x` of `X(T)`. -/
lemma isEquivariant_iff (A : G.Action X) (B : G.Action Y) (ψ : X ⟶ Y) :
    IsEquivariant A B ψ ↔ ∀ (T : Over S) (g : T ⟶ G.obj) (x : T ⟶ X),
      (lift g x ≫ A.act) ≫ ψ = lift g (x ≫ ψ) ≫ B.act :=
  Iff.rfl

/-- A `G`-equivariant morphism `ψ : X ⟶ Y` induces, for every `T` over `S`, a morphism of
`G(T)`-sets `X(T) ⟶ Y(T)`. -/
noncomputable def IsEquivariant.mulActionHom {A : G.Action X} {B : G.Action Y} {ψ : X ⟶ Y}
    (h : IsEquivariant A B ψ) (T : Over S) :
    letI := A.mulAction T
    letI := B.mulAction T
    MulActionHom (id (α := T ⟶ G.obj)) (T ⟶ X) (T ⟶ Y) :=
  letI := A.mulAction T
  letI := B.mulAction T
  { toFun := (· ≫ ψ)
    map_smul' := h T }

/-- The `G(T)`-set map induced by an equivariant morphism `ψ` is composition with `ψ`. -/
@[simp]
lemma IsEquivariant.mulActionHom_apply {A : G.Action X} {B : G.Action Y} {ψ : X ⟶ Y}
    (h : IsEquivariant A B ψ) (T : Over S) (x : T ⟶ X) :
    h.mulActionHom T x = x ≫ ψ :=
  rfl

/-- Equivariance is the single identity `a ≫ ψ = (G ◁ ψ) ≫ b` of morphisms over `S`. -/
lemma isEquivariant_iff_comp (A : G.Action X) (B : G.Action Y) (ψ : X ⟶ Y) :
    IsEquivariant A B ψ ↔ A.act ≫ ψ = (G.obj ◁ ψ) ≫ B.act := by
  rw [isEquivariant_iff]
  refine ⟨fun h => ?_, fun h T g x => ?_⟩
  · have := h (G.obj ⊗ X) (fst _ _) (snd _ _)
    rwa [lift_fst_snd, Category.id_comp, ← lift_whiskerLeft, lift_fst_snd,
      Category.id_comp] at this
  · rw [Category.assoc, h, ← Category.assoc, lift_whiskerLeft]

/-- The identity is equivariant. -/
lemma isEquivariant_id (A : G.Action X) : IsEquivariant A A (𝟙 X) := by
  intro T g x
  simp only [Category.comp_id]

/-- A composite of equivariant morphisms is equivariant. -/
lemma IsEquivariant.comp {A : G.Action X} {B : G.Action Y} {C : G.Action Z} {ψ : X ⟶ Y}
    {φ : Y ⟶ Z} (hψ : IsEquivariant A B ψ) (hφ : IsEquivariant B C φ) :
    IsEquivariant A C (ψ ≫ φ) := by
  intro T g x
  rw [← Category.assoc, hψ T g x, hφ T g (x ≫ ψ), Category.assoc]

/-- An action of `G` on `X` is a module object over the internal group object `G.grpObj` of
`Over S`, with the action morphism as scalar multiplication. -/
@[reducible]
noncomputable def modObj (A : G.Action X) : letI := G.grpObj; ModObj G.obj X :=
  letI := G.grpObj
  { smul := A.act
    one_smul := by
      change (MonObj.one ▷ X) ≫ A.act = (λ_ X).hom
      rw [leftUnitor_hom, ← Category.id_comp (MonObj.one ▷ X ≫ A.act), ← lift_fst_snd,
        lift_whiskerRight_assoc]
      change lift (fst _ _ ≫ (1 : 𝟙_ (Over S) ⟶ G.obj)) (snd _ _) ≫ A.act = snd _ _
      rw [G.comp_one, A.one_smul]
    mul_smul := by
      change (MonObj.mul ▷ X) ≫ A.act =
        (α_ G.obj G.obj X).hom ≫ (G.obj ◁ A.act) ≫ A.act
      have key : lift (lift (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _)) (snd _ _) =
          𝟙 ((G.obj ⊗ G.obj) ⊗ X) := by
        ext <;> simp
      calc (MonObj.mul ▷ X) ≫ A.act
          = lift (lift (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _)) (snd _ _) ≫
              (MonObj.mul ▷ X) ≫ A.act := by rw [key, Category.id_comp]
        _ = lift (lift (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _)) (snd _ _) ≫
              (α_ G.obj G.obj X).hom ≫ (G.obj ◁ A.act) ≫ A.act := by
          rw [lift_whiskerRight_assoc, G.grpObj_mul, ← G.mul_eq, A.mul_smul,
            lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
        _ = _ := by rw [key, Category.id_comp] }

/-- The scalar multiplication of the module object attached to an action is the action
morphism. -/
lemma modObj_smul (A : G.Action X) :
    letI := G.grpObj
    letI := A.modObj
    ModObj.smul (M := G.obj) (X := X) = A.act :=
  rfl

/-- A module object over the internal group object `G.grpObj` of `Over S` is an action of `G`,
with the scalar multiplication as action morphism. -/
noncomputable def ofModObj (X : Over S) (h : letI := G.grpObj; ModObj G.obj X) :
    G.Action X :=
  letI := G.grpObj
  letI : ModObj G.obj X := h
  { act := ModObj.smul (M := G.obj)
    one_smul T x := by
      have h1 : ((1 : 𝟙_ (Over S) ⟶ G.obj) ▷ X) ≫ ModObj.smul (M := G.obj) = (λ_ X).hom :=
        ModObj.one_smul (M := G.obj) X
      rw [← G.comp_one (toUnit T), ← lift_whiskerRight_assoc, h1, leftUnitor_hom, lift_snd]
    mul_smul T g k x := by
      have h1 : (G.mul ▷ X) ≫ ModObj.smul (M := G.obj) =
          (α_ G.obj G.obj X).hom ≫ (G.obj ◁ ModObj.smul (M := G.obj)) ≫
            ModObj.smul (M := G.obj) := by
        rw [← G.grpObj_mul]
        exact ModObj.mul_smul (M := G.obj) X
      rw [G.mul_eq, ← lift_whiskerRight_assoc, h1, lift_lift_associator_hom_assoc,
        lift_whiskerLeft_assoc] }

/-- The action morphism of the action attached to a module object is its scalar
multiplication. -/
lemma ofModObj_act (X : Over S) (h : letI := G.grpObj; ModObj G.obj X) :
    (ofModObj X h).act = (letI := G.grpObj; ModObj.smul (M := G.obj) (X := X)) :=
  rfl

/-- **Stacks Project, Tag 022Z** (1), compared with Mathlib. Actions of the group scheme `G`
on `X` in the functor-of-points sense are the same as module objects `ModObj` over the
internal group object `G.grpObj` of `Over S`. -/
@[stacks 022Z "part (1): actions are the module objects over the internal group object"]
noncomputable def equivModObj (X : Over S) :
    G.Action X ≃ (letI := G.grpObj; ModObj G.obj X) where
  toFun A := A.modObj
  invFun h := ofModObj X h
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Stacks Project, Tag 022Z** (2), compared with Mathlib. A morphism `ψ : X ⟶ Y` over `S` is
`G`-equivariant for actions `A` and `B` exactly when it is a morphism `IsModHom` of the
associated module objects over the internal group object `G.grpObj`. -/
@[stacks 022Z "part (2): equivariant morphisms are the morphisms of module objects"]
theorem isEquivariant_iff_isModHom (A : G.Action X) (B : G.Action Y) (ψ : X ⟶ Y) :
    IsEquivariant A B ψ ↔
      letI := G.grpObj
      letI := A.modObj
      letI := B.modObj
      IsModHom G.obj ψ := by
  let := G.grpObj
  let := A.modObj
  let := B.modObj
  rw [isEquivariant_iff_comp]
  exact ⟨fun h => ⟨h⟩, fun h => h.smul_hom⟩

/-- The associativity diagram of an action: `a ∘ (m × 1_X) = a ∘ (1_G × a)` as morphisms
`G ×_S G ×_S X ⟶ X`, the two triple fibre products being identified by the associator. -/
theorem act_assoc (A : G.Action X) :
    (G.mul ▷ X) ≫ A.act = (α_ G.obj G.obj X).hom ≫ (G.obj ◁ A.act) ≫ A.act := by
  let := G.grpObj
  let := A.modObj
  rw [← G.grpObj_mul]
  exact ModObj.mul_smul (M := G.obj) X

/-- The unit diagram of an action: `a ∘ (e × 1_X) = 1_X` as morphisms `X ⟶ X`, where
`e × 1_X : X ⟶ G ×_S X` is the morphism `x ↦ (e, x)`. -/
theorem act_unit (A : G.Action X) :
    lift (toUnit X ≫ (1 : 𝟙_ (Over S) ⟶ G.obj)) (𝟙 X) ≫ A.act = 𝟙 X := by
  rw [G.comp_one, A.one_smul]

/-- **Stacks Project, Tag 03LD**. A morphism `a : G ×_S X ⟶ X` of schemes over `S` is an action
of `G` on `X/S` in the sense of Tag 022Z (it makes every `X(T)` a `G(T)`-set) exactly when the
associativity diagram `a ∘ (m × 1_X) = a ∘ (1_G × a)` and the unit diagram
`a ∘ (e × 1_X) = 1_X` commute. -/
@[stacks 03LD "actions in the sense of 022Z are the morphisms making both diagrams commute"]
theorem exists_act_eq_iff (a : G.obj ⊗ X ⟶ X) :
    (∃ A : G.Action X, A.act = a) ↔
      (G.mul ▷ X) ≫ a = (α_ G.obj G.obj X).hom ≫ (G.obj ◁ a) ≫ a ∧
        lift (toUnit X ≫ (1 : 𝟙_ (Over S) ⟶ G.obj)) (𝟙 X) ≫ a = 𝟙 X := by
  refine ⟨?_, fun ⟨hm, hu⟩ => ⟨{ act := a, one_smul := ?_, mul_smul := ?_ }, rfl⟩⟩
  · rintro ⟨A, rfl⟩
    exact ⟨A.act_assoc, A.act_unit⟩
  · intro T x
    calc lift 1 x ≫ a = x ≫ lift (toUnit X ≫ (1 : 𝟙_ (Over S) ⟶ G.obj)) (𝟙 X) ≫ a := by
          rw [← Category.assoc, comp_lift, ← Category.assoc, G.comp_one, Category.comp_id]
      _ = x := by rw [hu, Category.comp_id]
  · intro T g h x
    rw [G.mul_eq, ← lift_whiskerRight_assoc, hm, lift_lift_associator_hom_assoc,
      lift_whiskerLeft_assoc]

end Action

end GroupSchemeOverPoints

end AlgebraicGeometry
