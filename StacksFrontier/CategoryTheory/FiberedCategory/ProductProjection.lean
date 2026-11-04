module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Products.Basic

/-!
# The projection of a product category is a fibred category

For categories `D` and `C` the second projection `D × C ⥤ C` is a fibred category: a morphism
`b : V ⟶ U` of `C` and an object `(d, U)` over `U` have the strongly cartesian lift
`(𝟙 d, b) : (d, V) ⟶ (d, U)`, and the fibre over `U` is a copy of `D`.

## Main results

* `CategoryTheory.Prod.snd_isStronglyCartesian_id`: the canonical lift `(𝟙 d, b)` is strongly
  cartesian.
* `CategoryTheory.Prod.snd_isFibered`: the second projection of a product category is fibred.
* `CategoryTheory.Prod.isStronglyCartesian_snd_iff_isIso_fst`: a morphism of `D × C` is strongly
  cartesian for the second projection exactly when its first component is an isomorphism.

## Implementation notes

A morphism of `D × C` lifts a morphism of `C` exactly when its second component is that
morphism, so the universal property amounts to the observation that a morphism into `(d, V)`
is determined by its first component together with the morphism of `C` it lifts.

The characterisation of the strongly cartesian morphisms is what identifies the covering
families of the topology that `D × C` inherits from a site `C` along the second projection: a
covering family of `(d, U)` consists of morphisms `(c i, b i) : (d i, V i) ⟶ (d, U)` with each
`c i` invertible and `{b i}` a covering of `U`. In particular such a family admits pullbacks
along arbitrary morphisms of `D × C` as soon as `C` has the pullbacks of the `b i`, the first
coordinate contributing only a pullback along an isomorphism; that is the covering-pullback
clause of Stacks continuity, `Stacks.Sites.PreservesCoveringPullbacks`, which the Čech
computation behind Stacks 0D6X consumes.

The first projection is fibred for the same reason; only the second is recorded, that being the
projection along which `Δ × C` is fibred over a site `C` in Stacks 09D0.

## References

* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0)
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} [Category.{v₁} D] {C : Type u₂} [Category.{v₂} C]

/-- A morphism of `D × C` with invertible first component is strongly cartesian for the second
projection. -/
private theorem Prod.snd_isStronglyCartesian_of_isIso_fst {X Y : D × C} (φ : Y ⟶ X) [IsIso φ.1] :
    (CategoryTheory.Prod.snd D C).IsStronglyCartesian φ.2 φ := by
  have _ : (CategoryTheory.Prod.snd D C).IsHomLift φ.2 φ := IsHomLift.map _ φ
  refine { universal_property' := fun {a'} g φ' _ => ?_ }
  have hg : g ≫ φ.2 = (CategoryTheory.Prod.snd D C).map φ' := IsHomLift.eq_of_isHomLift _ _ _
  refine ⟨(φ'.1 ≫ inv φ.1, g), ⟨IsHomLift.of_fac _ _ _ rfl rfl (by simp),
    Prod.ext (by simp) hg⟩, ?_⟩
  rintro χ ⟨_, hχ⟩
  refine Prod.ext ?_ (IsHomLift.eq_of_isHomLift _ g χ).symm
  rw [← (congrArg _root_.Prod.fst hχ : χ.1 ≫ φ.1 = φ'.1)]
  simp

/-- **The canonical cartesian lift.** `(𝟙 d, b) : (d, V) ⟶ (d, U)` is strongly cartesian for the
second projection over `b : V ⟶ U`: a morphism into `(d, V)` is determined by its first
component together with the morphism of `C` it lifts. -/
instance Prod.snd_isStronglyCartesian_id (a : D × C) {V : C} (b : V ⟶ a.2) :
    (CategoryTheory.Prod.snd D C).IsStronglyCartesian b
      ((𝟙 a.1, b) : ((a.1, V) : D × C) ⟶ a) :=
  Prod.snd_isStronglyCartesian_of_isIso_fst ((𝟙 a.1, b) : ((a.1, V) : D × C) ⟶ a)

/-- A morphism of `D × C` that is strongly cartesian for the second projection has invertible
first component. -/
private theorem Prod.isIso_fst_of_isStronglyCartesian {X Y : D × C} (φ : Y ⟶ X)
    [(CategoryTheory.Prod.snd D C).IsStronglyCartesian
      ((CategoryTheory.Prod.snd D C).map φ) φ] : IsIso φ.1 := by
  have _ : (CategoryTheory.Prod.snd D C).IsHomLift
      (𝟙 Y.2 ≫ (CategoryTheory.Prod.snd D C).map φ)
      ((𝟙 X.1, φ.2) : ((X.1, Y.2) : D × C) ⟶ X) :=
    IsHomLift.of_fac _ _ _ rfl rfl (by simp)
  obtain ⟨χ, ⟨hχlift, hχ⟩, -⟩ :=
    Functor.IsStronglyCartesian.universal_property'
      (p := CategoryTheory.Prod.snd D C) (φ := φ) (a' := ((X.1, Y.2) : D × C))
      ((CategoryTheory.Prod.snd D C).map φ) (𝟙 Y.2)
      ((𝟙 X.1, φ.2) : ((X.1, Y.2) : D × C) ⟶ X)
  have h1 : χ.1 ≫ φ.1 = 𝟙 X.1 := congrArg _root_.Prod.fst hχ
  have _ : (CategoryTheory.Prod.snd D C).IsHomLift (𝟙 Y.2) (𝟙 Y) :=
    IsHomLift.of_fac _ _ _ rfl rfl (by simp)
  have _ : (CategoryTheory.Prod.snd D C).IsHomLift (𝟙 Y.2)
      ((φ.1 ≫ χ.1, 𝟙 Y.2) : Y ⟶ Y) :=
    IsHomLift.of_fac _ _ _ rfl rfl (by simp)
  have h2 : ((φ.1 ≫ χ.1, 𝟙 Y.2) : Y ⟶ Y) = 𝟙 Y :=
    Functor.IsStronglyCartesian.ext (CategoryTheory.Prod.snd D C)
      ((CategoryTheory.Prod.snd D C).map φ) φ (𝟙 Y.2)
      (Prod.ext (by simpa using congrArg (fun k => φ.1 ≫ k) h1) (by simp))
  exact ⟨χ.1, congrArg _root_.Prod.fst h2, h1⟩

/-- **The strongly cartesian morphisms of the second projection are those with invertible first
component.** A morphism `(c, b) : (d', V) ⟶ (d, U)` is strongly cartesian over `b` exactly when
`c` is an isomorphism.

One direction factors `(c, b)` as the isomorphism `(c, 𝟙 V)` followed by the canonical cartesian
lift `(𝟙 d, b)`, both of which are strongly cartesian. The other applies the universal property
to `(𝟙 d, b) : (d, V) ⟶ (d, U)`, which produces a two-sided inverse of `c`.

This is what identifies the covering families of the topology that `D × C` inherits from a site
`C` along the second projection: they are the families `{(𝟙, b i) : (d, V i) ⟶ (d, U)}`, up to
isomorphism in the first coordinate, for `{b i}` a covering of `U`. -/
theorem Prod.isStronglyCartesian_snd_iff_isIso_fst {X Y : D × C} (φ : Y ⟶ X) :
    (CategoryTheory.Prod.snd D C).IsStronglyCartesian
      ((CategoryTheory.Prod.snd D C).map φ) φ ↔ IsIso φ.1 :=
  ⟨fun _ => Prod.isIso_fst_of_isStronglyCartesian φ,
    fun _ => Prod.snd_isStronglyCartesian_of_isIso_fst φ⟩

/-- **The second projection of a product category is a fibred category.** The cartesian lift of
`b : V ⟶ U` at an object `(d, U)` is `(𝟙 d, b) : (d, V) ⟶ (d, U)`. -/
instance Prod.snd_isFibered : (CategoryTheory.Prod.snd D C).IsFibered :=
  Functor.IsFibered.of_exists_isStronglyCartesian fun a _ f =>
    ⟨_, _, Prod.snd_isStronglyCartesian_id a f⟩

end CategoryTheory

end
