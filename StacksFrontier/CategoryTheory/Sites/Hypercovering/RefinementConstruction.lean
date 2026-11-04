module

public import StacksFrontier.AlgebraicTopology.SimplicialObject.Limits
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Power
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ConstantPowerMatching

/-!
# The refinement of a simplicial object by a morphism in one degree

Given a simplicial object `K` of a category `E` and a morphism `u : Z ⟶ K_k` into its term in a
fixed degree `k`, the fibre product of `K` and `Hom(C[k], Z)` over `Hom(C[k], K_k)` is a
simplicial object mapping to `K` whose degree-`k` component factors through `u`. This file
constructs it, for an arbitrary ambient category `E` with fibre products and with the degreewise
powers by the standard cosimplicial set `C[k]`.

## Main definitions

* `constSimplexPower`: the simplicial object `Hom(C[k], T)`, the `C[k]`-power of the constant
  simplicial object at `T`.
* `constSimplexPowerUnit`: the morphism `K ⟶ Hom(C[k], K_k)` of [Stacks, Tag 0B13].
* `refinementByCovering`: the refinement, `K ×_{Hom(C[k], K_k)} Hom(C[k], Z)`.
* `refinementByCoveringMap`: its morphism to `K`.
* `refinementByCoveringFactor`: the factorisation of the degree-`k` component through `u`.

## Main results

* `refinementByCoveringFactor_comp`: the degree-`k` component of `refinementByCoveringMap`
  factors through `u`.

## Implementation notes

This is the construction underlying [Stacks, Tag 01GJ], separated from the proof that it is a
hypercovering. That proof needs the ambient category to be the semi-representable objects over an
object of a site, and in particular needs all finite limits; the construction itself needs only
the fibre products and the powers, so it can be instantiated both at the semi-representable
objects over an object and at the semi-representable objects of the site itself, which has no
terminal object unless the site does.

The index sets `C[k]_n = Mor_Δ(⦋k⦌, ⦋n⦌)` are finite and nonempty, so the required powers exist
as soon as `E` has binary products; they are taken as hypotheses here rather than derived, so
that a consumer may supply them by whichever route its ambient category provides.

## References

* [Stacks Project, Tag 01GJ](https://stacks.math.columbia.edu/tag/01GJ)
* [Stacks Project, Tag 0B13](https://stacks.math.columbia.edu/tag/0B13)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Stacks.CategoryTheory.Hypercovering

/- `SimplicialObject.power` is semireducible, so a degree `(V.power U).obj n` and the product
`∏ᶜ fun _ : U.obj n.unop => V.obj n` that it is are equal only at default transparency, and the
`eqToHom` of `SimplicialObject.power_obj` is not even type-correct at `implicit` transparency.
Making that one declaration implicitly reducible here is strictly narrower than relaxing every
defeq check in the file. -/
attribute [local implicit_reducible] CategoryTheory.SimplicialObject.power

/-- `Hom(U, f)`: the degreewise `U`-power of a morphism `f`, for `U` a cosimplicial set. -/
noncomputable def constPowerMap {D : Type u} [Category.{v} D]
    {A B : D} (f : A ⟶ B) (U : CosimplicialObject (Type w))
    [∀ n : SimplexCategoryᵒᵖ,
      HasProduct fun _ : U.obj n.unop => ((SimplicialObject.const D).obj A).obj n]
    [∀ n : SimplexCategoryᵒᵖ,
      HasProduct fun _ : U.obj n.unop => ((SimplicialObject.const D).obj B).obj n]
    [∀ n : SimplexCategoryᵒᵖ, HasProduct fun _ : U.obj n.unop => A]
    [∀ n : SimplexCategoryᵒᵖ, HasProduct fun _ : U.obj n.unop => B] :
    ((SimplicialObject.const D).obj A).power U ⟶
      ((SimplicialObject.const D).obj B).power U where
  app n := CategoryTheory.Limits.Pi.map fun _ => f
  naturality := by
    intro i j φ
    apply Pi.hom_ext
    intro α
    simp [SimplicialObject.power, Category.assoc, CategoryTheory.Limits.Pi.map_π]

variable {E : Type u} [Category.{v} E]

/-- The coordinates of the standard cosimplicial set `C[k]` in each degree form a finite type:
they are the maps `⦋k⦌ ⟶ m` of the simplex category, lifted to `Type w`. -/
instance finite_simplexPowerIndex_obj (k : ℕ) (m : SimplexCategory) :
    Finite ((simplexPowerIndex.{w} k).obj m) := by
  rw [CosimplicialObject.uliftCoyoneda_spec.1 (SimplexCategory.mk k) m]
  infer_instance

/-- The coordinates of the standard cosimplicial set `C[k]` in each degree are nonempty: the
constant map `⦋k⦌ ⟶ m` is one of them.

Not an instance: a competing `Inhabited` route changes which term `default` elaborates to at the
local `Unique` instances of the matching lemmas, where the index set is a singleton. -/
theorem nonempty_simplexPowerIndex_obj (k : ℕ) (m : SimplexCategory) :
    Nonempty ((simplexPowerIndex.{w} k).obj m) :=
  ⟨ULift.up (SimplexCategory.const (SimplexCategory.mk k) m 0)⟩

section Power

variable (T : E) (k : ℕ)
  [inst : ∀ m : SimplexCategoryᵒᵖ,
    HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => T]

/-- The products that `Hom(C[k], T)` is built from, in the spelling `SimplicialObject.power`
expects: for a constant simplicial object the degree-`m` factor is `T` itself, but only after
`Functor.const` is unfolded. -/
instance hasProduct_constSimplexPowerFactor (m : SimplexCategoryᵒᵖ) :
    HasProduct (fun _ : (simplexPowerIndex.{w} k).obj m.unop =>
      ((SimplicialObject.const E).obj T).obj m) :=
  inferInstanceAs (HasProduct (fun _ : (simplexPowerIndex.{w} k).obj m.unop => T))

/-- `Hom(C[k], T)`: the `C[k]`-power of the constant simplicial object at `T`. Its degree-`n`
term is the product of copies of `T` indexed by the maps `⦋k⦌ ⟶ ⦋n⦌`. -/
noncomputable abbrev constSimplexPower : SimplicialObject E :=
  ((SimplicialObject.const E).obj T).power (simplexPowerIndex.{w} k)

/-- The coordinate of `Hom(C[k], T)` in degree `n` at a map `α : ⦋k⦌ ⟶ ⦋n⦌`. A degree of the
power is the product it is built from only definitionally, so the projection is taken once here,
at the type its consumers state. -/
noncomputable def constSimplexPowerProj (n : ℕ)
    (α : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk n)) :
    (constSimplexPower T k).obj (Opposite.op (SimplexCategory.mk n)) ⟶ T :=
  Pi.π (fun _ : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk n) => T) α

/-- A morphism into a degree of `Hom(C[k], T)` is exactly its family of coordinates. -/
theorem bijective_comp_constSimplexPowerProj (n : ℕ) (W : E) :
    Function.Bijective
      (fun (g : W ⟶ (constSimplexPower T k).obj (Opposite.op (SimplexCategory.mk n)))
        (α : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk n)) =>
          g ≫ constSimplexPowerProj T k n α) := by
  show Function.Bijective (fun (g : W ⟶
    ∏ᶜ fun _ : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk n) => T) α =>
      g ≫ Pi.π (fun _ : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk n) => T) α)
  exact ⟨fun f g h => Pi.hom_ext _ _ fun α => congrFun h α,
    fun f => ⟨Pi.lift f, by funext α; simp⟩⟩

/-- The coordinates of `Hom(C[k], T)` are natural: a simplicial structure map reindexes them
along the cosimplicial structure map of `C[k]`. -/
theorem constSimplexPowerProj_naturality (n m : ℕ)
    (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (α : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk m)) :
    (constSimplexPower T k).map φ.op ≫ constSimplexPowerProj T k m α =
      constSimplexPowerProj T k n ((simplexPowerIndex.{w} k).map φ α) := by
  simp [constSimplexPower, constSimplexPowerProj, SimplicialObject.power]

/-- `constSimplexPowerProj_naturality` with the structure map given as a morphism of
`SimplexCategoryᵒᵖ` rather than as the opposite of a morphism of `SimplexCategory`: the two are
the same morphism, but only the latter spelling matches a goal produced by a naturality
square. -/
theorem constSimplexPowerProj_naturality_op (n m : ℕ)
    (φ : Opposite.op (SimplexCategory.mk n) ⟶ Opposite.op (SimplexCategory.mk m))
    (α : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk m)) :
    (constSimplexPower T k).map φ ≫ constSimplexPowerProj T k m α =
      constSimplexPowerProj T k n ((simplexPowerIndex.{w} k).map φ.unop α) :=
  constSimplexPowerProj_naturality T k n m φ.unop α

end Power

/-- `Hom(C[k], u)`: the degreewise `C[k]`-power of a morphism. -/
noncomputable def constSimplexPowerMap {Y Z : E} (u : Z ⟶ Y) (k : ℕ)
    [∀ m : SimplexCategoryᵒᵖ,
      HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => Y]
    [∀ m : SimplexCategoryᵒᵖ,
      HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => Z] :
    constSimplexPower Z k ⟶ constSimplexPower Y k :=
  constPowerMap u (simplexPowerIndex.{w} k)

/-- The coordinates of `Hom(C[k], u)`: the coordinate at `α` of its degree-`n` component is the
coordinate at `α` followed by `u`. -/
theorem constSimplexPowerMap_app_comp_proj {Y Z : E} (u : Z ⟶ Y) (k : ℕ)
    [∀ m : SimplexCategoryᵒᵖ,
      HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => Y]
    [∀ m : SimplexCategoryᵒᵖ,
      HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => Z]
    (n : ℕ) (α : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk n)) :
    (constSimplexPowerMap.{w} u k).app (Opposite.op (SimplexCategory.mk n)) ≫
        constSimplexPowerProj Y k n α = constSimplexPowerProj Z k n α ≫ u :=
  CategoryTheory.Limits.Pi.map_π (fun _ => u) α

section RefinementData

variable (K : SimplicialObject E) (k : ℕ) {Z : E}
  (u : Z ⟶ K.obj (Opposite.op (SimplexCategory.mk k)))
  [∀ m : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop =>
    K.obj (Opposite.op (SimplexCategory.mk k))]
  [∀ m : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj m.unop => Z]

/-- A morphism of simplicial objects into `Hom(C[k], K_k)` is exactly a morphism from its
degree-`k` term to `K_k`: this is the adjunction of [Stacks, Tag 0B13] read at `C[k]`. -/
theorem bijective_comp_constSimplexPowerUnit (V : SimplicialObject E) :
    Function.Bijective
      (fun γ : V ⟶ constSimplexPower.{w} (K.obj (Opposite.op (SimplexCategory.mk k))) k =>
        γ.app (Opposite.op (SimplexCategory.mk k)) ≫
          constSimplexPowerProj (K.obj (Opposite.op (SimplexCategory.mk k))) k k
            (ULift.up (𝟙 (SimplexCategory.mk k)))) :=
  (SimplicialObject.bijective_comp_proj_id_of_prod_coyoneda
    (K.obj (Opposite.op (SimplexCategory.mk k))) k _
    (fun n α => constSimplexPowerProj _ k n α)
    (fun n W => bijective_comp_constSimplexPowerProj _ k n W)
    (fun n m φ α => constSimplexPowerProj_naturality _ k n m φ α)).1 V

/-- The morphism `K ⟶ Hom(C[k], K_k)` whose degree-`k` coordinate at the identity of `⦋k⦌` is the
identity: the unit of the adjunction of [Stacks, Tag 0B13] at `K`. -/
noncomputable def constSimplexPowerUnit :
    K ⟶ constSimplexPower.{w} (K.obj (Opposite.op (SimplexCategory.mk k))) k :=
  ((bijective_comp_constSimplexPowerUnit K k K).2 (𝟙 _)).choose

/-- The defining property of `constSimplexPowerUnit`: its coordinate at the identity of `⦋k⦌` in
degree `k` is the identity of `K_k`. -/
theorem constSimplexPowerUnit_app_comp_proj :
    (constSimplexPowerUnit.{w} K k).app (Opposite.op (SimplexCategory.mk k)) ≫
        constSimplexPowerProj (K.obj (Opposite.op (SimplexCategory.mk k))) k k
          (ULift.up (𝟙 (SimplexCategory.mk k))) = 𝟙 _ :=
  ((bijective_comp_constSimplexPowerUnit K k K).2 (𝟙 _)).choose_spec

variable [HasPullbacks E]

/-- **The refinement of a simplicial object by a morphism in one fixed degree.** Given
`u : Z ⟶ K_k` into the degree-`k` term of `K`, this is the fibre product of `K` and
`Hom(C[k], Z)` over `Hom(C[k], K_k)`. It maps to `K` by `refinementByCoveringMap`, and its
degree-`k` component factors through `u` by `refinementByCoveringFactor_comp`. -/
noncomputable def refinementByCovering : SimplicialObject E :=
  SimplicialObject.fibreProduct (constSimplexPowerUnit.{w} K k) (constSimplexPowerMap.{w} u k)

/-- The morphism from the refinement to `K`: the first projection of the fibre product. -/
noncomputable def refinementByCoveringMap : refinementByCovering.{w} K k u ⟶ K where
  app d := pullback.fst ((constSimplexPowerUnit.{w} K k).app d)
    ((constSimplexPowerMap.{w} u k).app d)
  naturality _ _ _ := pullback.lift_fst _ _ _

/-- The factorisation of the degree-`k` component of `refinementByCoveringMap` through `u`: the
second projection of the fibre product, read in the coordinate at the identity of `⦋k⦌`. -/
noncomputable def refinementByCoveringFactor :
    (refinementByCovering.{w} K k u).obj (Opposite.op (SimplexCategory.mk k)) ⟶ Z :=
  pullback.snd ((constSimplexPowerUnit.{w} K k).app (Opposite.op (SimplexCategory.mk k)))
      ((constSimplexPowerMap.{w} u k).app (Opposite.op (SimplexCategory.mk k))) ≫
    constSimplexPowerProj Z k k (ULift.up (𝟙 (SimplexCategory.mk k)))

/-- The degree-`k` component of the refining morphism factors through `u`. -/
theorem refinementByCoveringFactor_comp :
    refinementByCoveringFactor.{w} K k u ≫ u =
      (refinementByCoveringMap.{w} K k u).app (Opposite.op (SimplexCategory.mk k)) := by
  let d := Opposite.op (SimplexCategory.mk k)
  let c := constSimplexPowerUnit.{w} K k
  let b := constSimplexPowerMap.{w} u k
  let eId : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk k) :=
    ULift.up (𝟙 (SimplexCategory.mk k))
  let projZ := constSimplexPowerProj Z k k eId
  let projY := constSimplexPowerProj (K.obj d) k k eId
  have hproj : c.app d ≫ projY = 𝟙 _ := constSimplexPowerUnit_app_comp_proj K k
  have hpow : projZ ≫ u = b.app d ≫ projY :=
    (constSimplexPowerMap_app_comp_proj.{w} u k k eId).symm
  show (pullback.snd (c.app d) (b.app d) ≫ projZ) ≫ u =
    pullback.fst (c.app d) (b.app d)
  rw [Category.assoc, hpow, ← Category.assoc, ← pullback.condition, Category.assoc, hproj,
    Category.comp_id]

end RefinementData

end Stacks.CategoryTheory.Hypercovering

end
