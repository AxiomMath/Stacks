module

public import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
public import Mathlib.Basic.Countable.Basic
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Copower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The object `Hom(U, V)` for a simplicial set `U` and a simplicial object `V`

For a simplicial set `U` and a simplicial object `V`, the object `Hom(U, V)` is the simplicial
object representing morphisms `U × W → V`. This file defines it, proves that it exists when the
simplex sets of `U` are finite and nonempty, and shows that it turns pushouts of simplicial sets
into fibre products.
-/

/-!
## Hom from a simplicial set into a simplicial object

Let `C` be a category, let `U` be a simplicial set and let `V` be a simplicial object of `C`. A
simplicial object `H` of `C` *is a* `Hom(U, V)` when there are bijections
`Mor_{Simp(C)}(W, H) = Mor_{Simp(C)}(W × U, V)`, functorial in the simplicial object `W` of `C`.
Here `W × U` is the product of a simplicial object with a simplicial set, whose `n`-th term is the
coproduct `∐_{u ∈ U_n} W_n` [Stacks, Tag 017C]. Such an `H` need not exist, and when it does it is
determined only up to isomorphism; so the mathematical content of the definition is the *datum* of
the above family of bijections, i.e. `H` represents the functor `W ↦ Mor_{Simp(C)}(W × U, V)`. In
the language of enriched category theory this is the cotensor (or power) of `V` by `U`; it is not
the internal hom of `Simp(C)` [Stacks, Tag 017G].

Morphisms `W × U ⟶ V` are, by the very construction of the product, the families of morphisms
`(f_{n, u} : W_n ⟶ V_n)_{n ≥ 0, u ∈ U_n}` satisfying `f_{m, U(φ)(u)} ∘ W(φ) = V(φ) ∘ f_{n, u}` for
all `φ : [m] → [n]` [Stacks, Tag 017D], and such a family is the same thing as a morphism of
simplicial sets `U ⟶ sHom W V` into the simplicial enrichment of `Simp(C)`.

### Main definitions

* `CategoryTheory.SimplicialObject.IsHomFromSSet`: the datum making a simplicial object `H` of `C`
  a `Hom(U, V)` for a simplicial set `U` and a simplicial object `V`, namely a representation of
  the functor `W ↦ Mor(W × U, V)`.

### References

* [Stacks, Tag 017I](https://stacks.math.columbia.edu/tag/017I)
-/

section

open CategoryTheory SimplicialCategory Opposite

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- **Stacks 017I**.
`IsHomFromSSet U V H` is the datum exhibiting a simplicial object `H` of a category `C` as a
`Hom(U, V)` for a simplicial set `U` and a simplicial object `V` of `C`: a bijection
`Mor(W, H) ≃ Mor(W × U, V)`, functorial in the simplicial object `W` of `C`. The right-hand side is
written as `U ⟶ sHom W V`, the morphisms of simplicial sets from `U` into the enriched hom of `W`
and `V`. -/
@[stacks 017I]
public abbrev IsHomFromSSet (U : SSet.{v}) (V H : SimplicialObject C) :=
  ((sHomFunctor (SimplicialObject C)).flip.obj V ⋙
    coyoneda.obj (op U)).RepresentableBy H

end CategoryTheory.SimplicialObject

end

/-!
## Hom from simplicial sets into simplicial objects

Let `C` be a category with coproducts of any two objects and with countable limits, let `U` be a
simplicial set with `U_n` finite and nonempty for all `n ≥ 0`, and let `V` be a simplicial object
of `C`. Then the functor `Cᵒᵖ ⥤ Type`, `X ↦ Mor_{Simp(C)}(X × U, V)`, is representable, by the
limit of the diagram `⟨n, u⟩ ↦ V_n` over the category of elements of `U`. Here `X × U` is the
product `V.copower U` of [Stacks, Tag 017C] with `V` the constant simplicial object on `X`, which
exists because a family indexed by a finite nonempty type has a coproduct as soon as binary
coproducts exist (`CategoryTheory.Limits.hasCoproduct_of_finite_nonempty`).

### Main definitions

* `CategoryTheory.SimplicialObject.prodSSetFunctor`: `V ↦ U × V` as a functor
  `SimplicialObject C ⥤ SimplicialObject C`.
* `CategoryTheory.SimplicialObject.prodConstSSet`: the functor `C ⥤ SimplicialObject C` sending
  `X` to the product of `U` with the constant simplicial object on `X`.
* `CategoryTheory.SimplicialObject.simpHomFromSSet`: the functor `Cᵒᵖ ⥤ Type`,
  `X ↦ Mor_{Simp(C)}(X × U, V)`.
* `CategoryTheory.SimplicialObject.simpHomDiagram`: the diagram `U.Elements ⥤ C` sending
  `⟨n, u⟩` to `V_n` and a morphism lying over `f : n ⟶ n'` to `V(f)`.
* `CategoryTheory.SimplicialObject.simpHomRepObj`: the limit of `simpHomDiagram U V`.
* `CategoryTheory.SimplicialObject.SimpHomConeFamily`: a family of morphisms `X ⟶ V_n`, one for
  each element `⟨n, u⟩` of `U`, compatible with `simpHomDiagram U V`.
* `CategoryTheory.SimplicialObject.simpHomLimitEquiv`: morphisms `X ⟶ simpHomRepObj U V` are
  compatible families with apex `X`.
* `CategoryTheory.SimplicialObject.simpHomFamilyEquiv`: compatible families with apex `X` are
  morphisms `X × U ⟶ V`.
* `CategoryTheory.SimplicialObject.simpHomRepresentableBy`: `simpHomRepObj U V` represents
  `simpHomFromSSet U V`.

### Main results

* `CategoryTheory.SimplicialObject.simpHomFromSSet_isRepresentable`: the functor
  `X ↦ Mor_{Simp(C)}(X × U, V)` is representable.

### References

* [Stacks, Tag 017J](https://stacks.math.columbia.edu/tag/017J)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The functor `Simp(C) ⥤ Simp(C)`, `V ↦ U × V = V.copower U`, for a simplicial set `U` with
every `U_n` finite and nonempty. -/
@[implicit_reducible]
noncomputable def prodSSetFunctor (U : SSet.{0}) [∀ n, Finite (U.obj n)] [∀ n, Nonempty (U.obj n)]
    [HasBinaryCoproducts C] : SimplicialObject C ⥤ SimplicialObject C where
  obj V := V.copower U
  map η := Functor.copowerMap η (𝟙 U)
  map_id V := Functor.copowerMap_id V U
  map_comp η θ := by rw [Functor.copowerMap_comp, Category.comp_id]

/-- The functor `C ⥤ Simp(C)` sending `X` to the product `X × U` of `U` with the constant
simplicial object on `X`; in degree `n` this is the coproduct `∐_{u ∈ U_n} X`. -/
noncomputable abbrev prodConstSSet (U : SSet.{0}) [∀ n, Finite (U.obj n)] [∀ n, Nonempty (U.obj n)]
    [HasBinaryCoproducts C] : C ⥤ SimplicialObject C :=
  SimplicialObject.const C ⋙ prodSSetFunctor U

/-- On the component of `(X × U)_n = ∐_{u ∈ U_n} X` indexed by `u`, the action of `X × U` on
`f : n ⟶ n'` is the inclusion of the component indexed by `U(f)(u) ∈ U_{n'}`. -/
lemma prodConstSSet_ι_map [HasBinaryCoproducts C]
    (U : SSet.{0}) [∀ n, Finite (U.obj n)] [∀ n, Nonempty (U.obj n)]
    (X : C) {n n' : SimplexCategoryᵒᵖ} (f : n ⟶ n') (u : U.obj n) :
    Sigma.ι (fun (_ : U.obj n) => X) u ≫ ((prodConstSSet U).obj X).map f
      = Sigma.ι (fun (_ : U.obj n') => X) (U.map f u) := by
  simp [prodSSetFunctor]

/-- The functor `F : Cᵒᵖ ⥤ Sets`, `X ↦ Mor_{Simp(C)}(X × U, V)`, acting on `α : X' ⟶ X` by
precomposition with `α × U : X' × U ⟶ X × U`. -/
noncomputable abbrev simpHomFromSSet (U : SSet.{0}) [∀ n, Finite (U.obj n)]
    [∀ n, Nonempty (U.obj n)]
    [HasBinaryCoproducts C] (V : SimplicialObject C) : Cᵒᵖ ⥤ Type _ :=
  (prodConstSSet U).op ⋙ yoneda.obj V

/-- `simpHomFromSSet U V` acts on `α : X' ⟶ X` by precomposition with `α × U`. -/
@[simp] lemma simpHomFromSSet_map (U : SSet.{0}) [∀ n, Finite (U.obj n)]
    [∀ n, Nonempty (U.obj n)] [HasBinaryCoproducts C] (V : SimplicialObject C)
    {X X' : C} (α : X ⟶ X') (θ : (prodConstSSet U).obj X' ⟶ V) :
    (simpHomFromSSet U V).map α.op θ = (prodConstSSet U).map α ≫ θ := rfl

/-- The category of elements of a simplicial set `U` with every `U_n` finite is countable: its
objects form the countable set `Σ n, U_n`, and between two objects there are only finitely many
morphisms, namely a subtype of the finite set of simplex maps `n ⟶ n'`. -/
instance instCountableCategoryElements (U : SSet.{0}) [∀ n, Finite (U.obj n)] :
    CountableCategory U.Elements := by
  have hlen : Function.Injective (fun x : SimplexCategory => x.len) :=
    fun _ _ h => SimplexCategory.ext h
  have : Countable SimplexCategory := hlen.countable
  have : Countable SimplexCategoryᵒᵖ := Countable.of_equiv _ Opposite.equivToOpposite
  have hHom : ∀ a b : SimplexCategory, Finite (a ⟶ b) := fun a b =>
    Finite.of_injective (β := Fin (a.len + 1) → Fin (b.len + 1)) (fun f => f.toOrderHom)
      fun _ _ h => SimplexCategory.Hom.ext _ _ (DFunLike.coe_injective h)
  have hHomOp : ∀ a b : SimplexCategoryᵒᵖ, Finite (a ⟶ b) := fun a b =>
    have := hHom b.unop a.unop
    Finite.of_equiv _ (opEquiv a b).symm
  refine ⟨Countable.of_equiv (Σ n : SimplexCategoryᵒᵖ, U.obj n)
    ⟨fun p => .mk p.2, fun x => ⟨x.obj, x.val⟩, fun _ => rfl, fun _ => rfl⟩, ?_⟩
  intro x y
  have := hHomOp ((CategoryOfElements.π U).obj x) ((CategoryOfElements.π U).obj y)
  exact Function.Injective.countable (f := fun f : x ⟶ y => f.hom)
    fun _ _ h => Functor.Elements.Hom.ext h

/-- The diagram `U.Elements ⥤ C` sending `⟨n, u⟩` to `V_n` and a morphism lying over
`f : n ⟶ n'` to `V(f)`. -/
noncomputable abbrev simpHomDiagram (U : SSet.{0}) (V : SimplicialObject C) : U.Elements ⥤ C :=
  CategoryOfElements.π U ⋙ V

/-- The limit of `simpHomDiagram U V`, which exists because `U.Elements` is a countable category
and `C` has countable limits. -/
noncomputable abbrev simpHomRepObj [HasCountableLimits C]
    (U : SSet.{0}) [∀ n, Finite (U.obj n)] (V : SimplicialObject C) : C :=
  limit (simpHomDiagram U V)

/-- A compatible family with apex `X`: a morphism `X ⟶ V_n` for each element `⟨n, u⟩` of `U`,
subject to `s ⟨n, u⟩ ≫ V(f) = s ⟨n', U(f)(u)⟩` for every `f : n ⟶ n'`. Equivalently, a cone on
`simpHomDiagram U V` with vertex `X`. -/
@[ext]
structure SimpHomConeFamily (U : SSet.{0}) (V : SimplicialObject C) (X : C) where
  /-- The morphism `X ⟶ V_n` attached to the element `p = ⟨n, u⟩`. -/
  leg (p : U.Elements) : X ⟶ (simpHomDiagram U V).obj p
  /-- The legs are compatible with the diagram. -/
  leg_comp {p q : U.Elements} (f : p ⟶ q) : leg p ≫ (simpHomDiagram U V).map f = leg q

/-- Morphisms `X ⟶ lim 𝒱` correspond bijectively to compatible families with apex `X`, by the
universal property of the limit. -/
noncomputable def simpHomLimitEquiv [HasCountableLimits C]
    (U : SSet.{0}) [∀ n, Finite (U.obj n)] (V : SimplicialObject C) (X : C) :
    (X ⟶ simpHomRepObj U V) ≃ SimpHomConeFamily U V X where
  toFun g :=
    { leg := fun p => g ≫ limit.π (simpHomDiagram U V) p
      leg_comp := fun {_ _} f => by rw [Category.assoc, limit.w] }
  invFun s := limit.lift (simpHomDiagram U V) ⟨X, ⟨s.leg, fun {_ _} f => by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
    exact (s.leg_comp f).symm⟩⟩
  left_inv g := limit.hom_ext fun p => by simp [simpHomRepObj]
  right_inv s := by ext p; simp [simpHomRepObj]

/-- Compatible families with apex `X` correspond bijectively to morphisms of simplicial objects
`X × U ⟶ V`: the components `θ_n : ∐_{u ∈ U_n} X ⟶ V_n` of such a morphism are, by the universal
property of the coproduct, families `(θ_{n,u} : X ⟶ V_n)_{u ∈ U_n}`, and naturality of `θ` is the
compatibility condition. -/
noncomputable def simpHomFamilyEquiv
    [HasBinaryCoproducts C]
    (U : SSet.{0}) [∀ n, Finite (U.obj n)] [∀ n, Nonempty (U.obj n)]
    (V : SimplicialObject C) (X : C) :
    SimpHomConeFamily U V X ≃ ((prodConstSSet U).obj X ⟶ V) where
  toFun s :=
    { app := fun n => Sigma.desc (fun u => show X ⟶ V.obj n from s.leg (U.elementsMk n u))
      naturality := fun n n' f => Sigma.hom_ext _ _ fun u => by
        rw [← Category.assoc, show Sigma.ι
              (fun (_ : U.obj n) => ((SimplicialObject.const C).obj X).obj n) u
              ≫ ((prodConstSSet U).obj X).map f
            = Sigma.ι (fun (_ : U.obj n') => X) (U.map f u) from
          prodConstSSet_ι_map U X f u, Sigma.ι_desc, ← Category.assoc, Sigma.ι_desc]
        have h := s.leg_comp (Functor.Elements.homMk (x := U.elementsMk n u)
          (y := U.elementsMk n' (U.map f u)) f rfl)
        exact h.symm }
  invFun θ :=
    { leg := fun p => Sigma.ι (fun (_ : U.obj p.obj) => X) p.val ≫ θ.app p.obj
      leg_comp := fun {p q} f => by
        have hmap : (simpHomDiagram U V).map f = V.map f.hom := rfl
        rw [hmap]
        change (Sigma.ι (fun (_ : U.obj p.obj) => X) p.val ≫ θ.app p.obj) ≫ V.map f.hom =
          Sigma.ι (fun (_ : U.obj q.obj) => X) q.val ≫ θ.app q.obj
        rw [Category.assoc, ← θ.naturality f.hom, ← Category.assoc, prodConstSSet_ι_map,
          f.map_val] }
  left_inv s := SimpHomConeFamily.ext (funext fun p => Sigma.ι_desc _ _)
  right_inv θ :=
    SimplicialObject.hom_ext _ _ fun n => Sigma.hom_ext _ _ fun u => Sigma.ι_desc _ _

set_option backward.isDefEq.respectTransparency false in
/-- The bijection assembled from `simpHomLimitEquiv` and `simpHomFamilyEquiv` is natural in `X`:
precomposing `g : X' ⟶ lim 𝒱` with `α : X ⟶ X'` corresponds to precomposing the unwound
simplicial morphism with `α × U`. -/
theorem simpHomEquiv_naturality
    [HasBinaryCoproducts C] [HasCountableLimits C]
    (U : SSet.{0}) [∀ n, Finite (U.obj n)] [∀ n, Nonempty (U.obj n)]
    (V : SimplicialObject C) {X X' : C} (α : X ⟶ X') (g : X' ⟶ simpHomRepObj U V) :
    (simpHomFamilyEquiv U V X) ((simpHomLimitEquiv U V X) (α ≫ g))
      = (simpHomFromSSet U V).map α.op
          ((simpHomFamilyEquiv U V X') ((simpHomLimitEquiv U V X') g)) := by
  rw [simpHomFromSSet_map]
  refine SimplicialObject.hom_ext _ _ fun n => Sigma.hom_ext _ _ fun u => ?_
  dsimp only [simpHomFamilyEquiv, simpHomLimitEquiv, Equiv.coe_fn_mk, NatTrans.comp_app]
  rw [← Category.assoc, Sigma.ι_desc]
  dsimp only [Functor.comp_map, prodSSetFunctor]
  rw [Functor.ι_copowerMap_app, Category.assoc (((const C).map α).app n), Sigma.ι_desc]
  simp

/-- The object `simpHomRepObj U V` represents `simpHomFromSSet U V`. -/
noncomputable def simpHomRepresentableBy
    [HasBinaryCoproducts C] [HasCountableLimits C]
    (U : SSet.{0}) [∀ n, Finite (U.obj n)] [∀ n, Nonempty (U.obj n)]
    (V : SimplicialObject C) :
    (simpHomFromSSet U V).RepresentableBy (simpHomRepObj U V) where
  homEquiv {X} := (simpHomLimitEquiv U V X).trans (simpHomFamilyEquiv U V X)
  homEquiv_comp α g := simpHomEquiv_naturality U V α g

/-- **Stacks 017J**. Let `C` be a category with coproducts of any two objects and with countable
limits, let `U` be a simplicial set with `U_n` finite and nonempty for all `n ≥ 0`, and let `V`
be a simplicial object of `C`. Then the functor `Cᵒᵖ ⥤ Sets`, `X ↦ Mor_{Simp(C)}(X × U, V)`, is
representable. -/
@[stacks 017J]
theorem simpHomFromSSet_isRepresentable
    [HasBinaryCoproducts C] [HasCountableLimits C]
    (U : SSet.{0}) [∀ n, Finite (U.obj n)] [∀ n, Nonempty (U.obj n)]
    (V : SimplicialObject C) :
    (simpHomFromSSet U V).IsRepresentable :=
  (simpHomRepresentableBy U V).isRepresentable

end CategoryTheory.SimplicialObject

end

end

/-!
## Limits indexed by the simplices of a finite simplicial set

Let `U` be a simplicial set with finitely many nondegenerate simplices, that is with `U_n`
finite for every `n` and every `n`-simplex degenerate for `n ≫ 0`, and let `C` be a category
with finite limits. Then every diagram indexed by the category `U.Elements` of simplices of
`U` has a limit in `C`, because the simplices of dimension `≤ 2 d` form a finite initial
subcategory of `U.Elements` whenever every simplex of dimension `≥ d` is degenerate.

For a simplicial object `V` of `C` this makes the functor `Cᵒᵖ ⥤ Set`,
`X ↦ Mor_{Simp(C)}(X × U, V)`, representable by `limit (CategoryOfElements.π U ⋙ V)`, since a
morphism `X × U ⟶ V` of simplicial objects is exactly a cone with vertex `X` over
`CategoryOfElements.π U ⋙ V : U.Elements ⥤ C`, `(n, u) ↦ V_n`.

### Main results

* `SSet.hasLimitsOfShape_elements`: every diagram indexed by the simplices of a finite
  simplicial set has a limit in a category with finite limits.

### References

* [Stacks, Tag 017K](https://stacks.math.columbia.edu/tag/017K)
-/

section

open CategoryTheory CategoryTheory.Limits Simplicial SimplexCategory Opposite

universe w v u

namespace SSet

/-- If `φ₁ : ⦋n + 1⦌ ⟶ ⦋k₁⦌` and `φ₂ : ⦋n + 1⦌ ⟶ ⦋k₂⦌` with `k₁ + k₂ < n + 1`, then
there is an index `i` at which both `φ₁` and `φ₂` are constant. -/
private lemma exists_repeat {n k₁ k₂ : ℕ} (φ₁ : ⦋n + 1⦌ ⟶ ⦋k₁⦌) (φ₂ : ⦋n + 1⦌ ⟶ ⦋k₂⦌)
    (h : k₁ + k₂ < n + 1) :
    ∃ i : Fin (n + 1), φ₁.toOrderHom i.castSucc = φ₁.toOrderHom i.succ ∧
      φ₂.toOrderHom i.castSucc = φ₂.toOrderHom i.succ := by
  by_contra hc
  simp only [not_exists, not_and] at hc
  have hlt : ∀ {k : ℕ} (φ : ⦋n + 1⦌ ⟶ ⦋k⦌) (i : Fin (n + 1)),
      (φ.toOrderHom i.castSucc : ℕ) = φ.toOrderHom i.succ ∨
        (φ.toOrderHom i.castSucc : ℕ) < φ.toOrderHom i.succ := fun φ i =>
    Nat.eq_or_lt_of_le (Fin.le_def.1 (φ.toOrderHom.monotone (Fin.castSucc_le_succ i)))
  have hmono : StrictMono (fun t : Fin (n + 2) =>
      (⟨(φ₁.toOrderHom t : ℕ) + (φ₂.toOrderHom t : ℕ), by
        have h₁ := (φ₁.toOrderHom t).is_le
        have h₂ := (φ₂.toOrderHom t).is_le
        simp only [SimplexCategory.len_mk] at h₁ h₂
        lia⟩ : Fin (k₁ + k₂ + 1))) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    simp only [Fin.lt_def]
    rcases hlt φ₁ i with he | h₁ <;> rcases hlt φ₂ i with h₂ | h₂
    · exact (hc i (Fin.ext he) (Fin.ext h₂)).elim
    all_goals lia
  have hcard := Fintype.card_le_of_injective _ hmono.injective
  simp only [Fintype.card_fin] at hcard
  lia

/-- The degeneracy operator `U(σ i)` of a simplicial set is injective. -/
private lemma injective_map_σ (U : SSet.{w}) {n : ℕ} (i : Fin (n + 1)) :
    Function.Injective (U.map (SimplexCategory.σ i).op) :=
  Function.LeftInverse.injective (g := U.map (SimplexCategory.δ i.castSucc).op)
    (U.δ_comp_σ_self_apply i)

/-- Two simplices `v₁`, `v₂` with a common image `U(φ₁)(v₁) = U(φ₂)(v₂)` in dimension `n`
have a common image in a dimension `j ≤ k₁ + k₂` through which both `φ₁` and `φ₂`
factor. -/
private lemma exists_mediator (U : SSet.{w}) {k₁ k₂ : ℕ} (v₁ : U _⦋k₁⦌) (v₂ : U _⦋k₂⦌) :
    ∀ (n : ℕ) (φ₁ : ⦋n⦌ ⟶ ⦋k₁⦌) (φ₂ : ⦋n⦌ ⟶ ⦋k₂⦌),
      U.map φ₁.op v₁ = U.map φ₂.op v₂ →
      ∃ (j : ℕ) (_ : j ≤ k₁ + k₂) (l : ⦋n⦌ ⟶ ⦋j⦌) (χ₁ : ⦋j⦌ ⟶ ⦋k₁⦌) (χ₂ : ⦋j⦌ ⟶ ⦋k₂⦌),
        l ≫ χ₁ = φ₁ ∧ l ≫ χ₂ = φ₂ ∧ U.map χ₁.op v₁ = U.map χ₂.op v₂ := by
  intro n
  induction n with
  | zero => exact fun φ₁ φ₂ h => ⟨0, Nat.zero_le _, 𝟙 _, φ₁, φ₂, by simp, by simp, h⟩
  | succ n ih =>
    intro φ₁ φ₂ h
    by_cases hn : n + 1 ≤ k₁ + k₂
    · exact ⟨n + 1, hn, 𝟙 _, φ₁, φ₂, by simp, by simp, h⟩
    · obtain ⟨i, hi₁, hi₂⟩ := exists_repeat φ₁ φ₂ (by lia)
      obtain ⟨ψ₁, hψ₁⟩ := eq_σ_comp_of_not_injective' φ₁ i hi₁
      obtain ⟨ψ₂, hψ₂⟩ := eq_σ_comp_of_not_injective' φ₂ i hi₂
      obtain ⟨j, hj, l, χ₁, χ₂, e₁, e₂, e₃⟩ := ih ψ₁ ψ₂ (injective_map_σ U i (by
        simp only [← Functor.map_comp_apply, ← op_comp, ← hψ₁, ← hψ₂]
        exact h))
      exact ⟨j, hj, SimplexCategory.σ i ≫ l, χ₁, χ₂, by rw [Category.assoc, e₁, hψ₁],
        by rw [Category.assoc, e₂, hψ₂], e₃⟩

section

variable (U : SSet.{w}) (N : ℕ)

/-- The simplices of `U` of dimension `≤ N`. -/
private abbrev dimLE : ObjectProperty U.Elements := fun x => x.1.unop.len ≤ N

variable (z : U.Elements)

/-- The object of `CostructuredArrow (dimLE U N).ι z` given by a simplex `v` of dimension
`k ≤ N` presenting the simplex `z` as `U(φ)(v)`. -/
private def costructuredArrowMk {k : ℕ} (hk : k ≤ N) (v : U _⦋k⦌) (φ : ⦋z.1.unop.len⦌ ⟶ ⦋k⦌)
    (h : U.map φ.op v = z.2) : CostructuredArrow (dimLE U N).ι z :=
  CostructuredArrow.mk (Y := (⟨U.elementsMk (op ⦋k⦌) v, hk⟩ : (dimLE U N).FullSubcategory))
    (show U.elementsMk (op ⦋k⦌) v ⟶ z from ⟨φ.op, h⟩)

/-- Every object of `CostructuredArrow (dimLE U N).ι z` is of the form `costructuredArrowMk`. -/
private lemma eq_costructuredArrowMk (x : CostructuredArrow (dimLE U N).ι z) :
    x = costructuredArrowMk U N z x.left.property x.left.obj.2 x.hom.hom.unop x.hom.map_val := rfl

/-- A morphism between two such objects: the target simplex `v'` is the image `U(ψ)(v)` of
the source simplex and the presentation `φ` of `z` factors as `φ' ≫ ψ`. -/
private lemma nonempty_hom {k k' : ℕ} (hk : k ≤ N) (hk' : k' ≤ N) (v : U _⦋k⦌) (v' : U _⦋k'⦌)
    (φ : ⦋z.1.unop.len⦌ ⟶ ⦋k⦌) (φ' : ⦋z.1.unop.len⦌ ⟶ ⦋k'⦌) (h : U.map φ.op v = z.2)
    (h' : U.map φ'.op v' = z.2) (ψ : ⦋k'⦌ ⟶ ⦋k⦌) (hv : U.map ψ.op v = v')
    (hφ : φ' ≫ ψ = φ) :
    Nonempty (costructuredArrowMk U N z hk v φ h ⟶ costructuredArrowMk U N z hk' v' φ' h') :=
  ⟨CostructuredArrow.homMk (ObjectProperty.homMk (P := dimLE U N)
      (show U.elementsMk (op ⦋k⦌) v ⟶ U.elementsMk (op ⦋k'⦌) v' from ⟨ψ.op, hv⟩))
    (Functor.Elements.Hom.ext (op_comp.symm.trans (congrArg Quiver.Hom.op hφ)))⟩

/-- The homomorphisms of `U.Elements` between two simplices form a finite set. -/
private lemma finite_elements_hom (x y : U.Elements) : Finite (x ⟶ y) := by
  have : Finite (x.1 ⟶ y.1) :=
    Finite.of_equiv _ (Opposite.equivToOpposite (α := (y.1.unop ⟶ x.1.unop)))
  exact Finite.of_injective (fun f : x ⟶ y => f.1) fun a b h => Functor.Elements.Hom.ext h

/-- The simplices of dimension `≤ N` of a simplicial set with finitely many simplices in
each dimension form a finite set. -/
private lemma finite_dimLE [U.Finite] : Finite (dimLE U N).FullSubcategory :=
  Finite.of_surjective (α := Σ k : Fin (N + 1), U _⦋(k : ℕ)⦌)
    (fun p => ⟨U.elementsMk (op ⦋(p.1 : ℕ)⦌) p.2, p.1.is_le⟩)
    fun x => ⟨⟨⟨x.obj.1.unop.len, Nat.lt_succ_of_le x.property⟩, x.obj.2⟩, rfl⟩

/-- Limits indexed by the simplices of dimension `≤ N` exist in any category with finite
limits. -/
private lemma hasLimitsOfShape_dimLE [U.Finite] (C : Type u) [Category.{v} C]
    [HasFiniteLimits C] : HasLimitsOfShape (dimLE U N).FullSubcategory C := by
  have := finite_dimLE U N
  obtain ⟨q, ⟨e⟩⟩ := Finite.exists_equiv_fin (dimLE U N).FullSubcategory
  let f : Fin q → (dimLE U N).FullSubcategory := e.symm
  have : FinCategory (InducedCategory (dimLE U N).FullSubcategory f) :=
    { fintypeObj := inferInstanceAs (Fintype (Fin q))
      fintypeHom := fun x y =>
        have := finite_elements_hom U (f x).obj (f y).obj
        have : Finite (f x ⟶ f y) := Finite.of_surjective _ ObjectProperty.homMk_surjective
        have : Finite (x ⟶ y) := Finite.of_equiv _ (InducedCategory.homEquiv (F := f)).symm
        Fintype.ofFinite _ }
  have : (inducedFunctor f).EssSurj := ⟨fun Y => ⟨e Y, ⟨eqToIso (by simp [f])⟩⟩⟩
  have : (inducedFunctor f).IsEquivalence := { }
  exact hasLimitsOfShape_of_equivalence (inducedFunctor f).asEquivalence

end

section

variable (U : SSet.{w}) (d : ℕ) [U.HasDimensionLT d]

/-- A nondegenerate simplex of a simplicial set of dimension `< d` has dimension `< d`. -/
private lemma lt_of_nonDegenerate {m : ℕ} (y : U.nonDegenerate m) : m < d := by
  by_contra hcon
  exact absurd y.property (by simp [SSet.nonDegenerate_eq_empty_of_hasDimensionLT U d m (by lia)])

/-- Every object of `CostructuredArrow (dimLE U (2 * d)).ι z` receives a morphism from an
object whose simplex is nondegenerate, hence of dimension `< d`. -/
private lemma exists_nonDegenerate_hom (z : U.Elements) {k : ℕ} (hk : k ≤ 2 * d) (v : U _⦋k⦌)
    (φ : ⦋z.1.unop.len⦌ ⟶ ⦋k⦌) (h : U.map φ.op v = z.2) :
    ∃ (m : ℕ) (hm : m ≤ 2 * d) (_ : m < d) (y : U _⦋m⦌) (ψ : ⦋z.1.unop.len⦌ ⟶ ⦋m⦌)
      (h' : U.map ψ.op y = z.2),
      Nonempty (costructuredArrowMk U (2 * d) z hm y ψ h' ⟶
        costructuredArrowMk U (2 * d) z hk v φ h) := by
  obtain ⟨m, e, -, y, hy⟩ := U.exists_nonDegenerate (n := k) v
  have hy' : v = U.map e.op (y : U _⦋m⦌) := hy
  have hmd : m < d := lt_of_nonDegenerate U d y
  refine ⟨m, by lia, hmd, (y : U _⦋m⦌), φ ≫ e, ?_, ?_⟩
  · rw [op_comp, Functor.map_comp_apply, ← hy']
    exact h
  · exact nonempty_hom U (2 * d) z (by lia) hk (y : U _⦋m⦌) v (φ ≫ e) φ _ h e hy'.symm rfl

/-- Any two objects of `CostructuredArrow (dimLE U (2 * d)).ι z` are connected by a
zigzag. -/
private lemma zigzag_obj (z : U.Elements) {k₁ k₂ : ℕ} (hk₁ : k₁ ≤ 2 * d) (hk₂ : k₂ ≤ 2 * d)
    (v₁ : U _⦋k₁⦌) (v₂ : U _⦋k₂⦌) (φ₁ : ⦋z.1.unop.len⦌ ⟶ ⦋k₁⦌) (φ₂ : ⦋z.1.unop.len⦌ ⟶ ⦋k₂⦌)
    (h₁ : U.map φ₁.op v₁ = z.2) (h₂ : U.map φ₂.op v₂ = z.2) :
    Zigzag (costructuredArrowMk U (2 * d) z hk₁ v₁ φ₁ h₁)
      (costructuredArrowMk U (2 * d) z hk₂ v₂ φ₂ h₂) := by
  obtain ⟨m₁, hm₁, hmd₁, y₁, ψ₁, hy₁, ⟨g₁⟩⟩ := exists_nonDegenerate_hom U d z hk₁ v₁ φ₁ h₁
  obtain ⟨m₂, hm₂, hmd₂, y₂, ψ₂, hy₂, ⟨g₂⟩⟩ := exists_nonDegenerate_hom U d z hk₂ v₂ φ₂ h₂
  obtain ⟨j, hj, l, χ₁, χ₂, e₁, e₂, e₃⟩ :=
    exists_mediator U y₁ y₂ z.1.unop.len ψ₁ ψ₂ (hy₁.trans hy₂.symm)
  have hj' : j ≤ 2 * d := by lia
  have hw : U.map l.op (U.map χ₁.op y₁) = z.2 := by
    simp only [← Functor.map_comp_apply, ← op_comp, e₁]
    exact hy₁
  obtain ⟨w₁⟩ := nonempty_hom U (2 * d) z hm₁ hj' y₁ (U.map χ₁.op y₁) ψ₁ l hy₁ hw χ₁ rfl e₁
  obtain ⟨w₂⟩ := nonempty_hom U (2 * d) z hm₂ hj' y₂ (U.map χ₁.op y₁) ψ₂ l hy₂ hw χ₂ e₃.symm e₂
  exact Relation.ReflTransGen.head (Or.inr ⟨g₁⟩)
    (Relation.ReflTransGen.head (Or.inl ⟨w₁⟩)
      (Relation.ReflTransGen.head (Or.inr ⟨w₂⟩)
        (Relation.ReflTransGen.single (Or.inl ⟨g₂⟩))))

/-- The inclusion of the simplices of dimension `≤ 2 d` into `U.Elements` is an initial
functor. -/
private lemma initial_ι : (dimLE U (2 * d)).ι.Initial where
  out z := by
    have : Nonempty (CostructuredArrow (dimLE U (2 * d)).ι z) := by
      obtain ⟨m, e, -, y, hy⟩ := U.exists_nonDegenerate (n := z.1.unop.len) z.2
      have : m < d := lt_of_nonDegenerate U d y
      exact ⟨costructuredArrowMk U (2 * d) z (by lia) (y : U _⦋m⦌) e hy.symm⟩
    refine zigzag_isConnected fun x y => ?_
    rw [eq_costructuredArrowMk U (2 * d) z x, eq_costructuredArrowMk U (2 * d) z y]
    exact zigzag_obj U d z x.left.property y.left.property x.left.obj.2 y.left.obj.2
      x.hom.hom.unop y.hom.hom.unop x.hom.map_val y.hom.map_val

end

/-- **Stacks 017K**.
Let `U` be a simplicial set with finitely many nondegenerate simplices, i.e. with `U_n`
finite for all `n` and with all `n`-simplices degenerate for `n ≫ 0`, and let `C` be a
category with finite limits. Then every diagram indexed by the category `U.Elements` of
simplices of `U` has a limit in `C`. -/
@[stacks 017K]
public instance hasLimitsOfShape_elements (U : SSet.{w}) [U.Finite] (C : Type u)
    [Category.{v} C] [HasFiniteLimits C] : HasLimitsOfShape U.Elements C := by
  obtain ⟨d, hd⟩ := U.hasDimensionLT_of_finite
  have : U.HasDimensionLT d := hd
  have : HasLimitsOfShape (dimLE U (2 * d)).FullSubcategory C :=
    hasLimitsOfShape_dimLE U (2 * d) C
  have : (dimLE U (2 * d)).ι.Initial := initial_ι U d
  exact Functor.Initial.hasLimitsOfShape_of_initial (dimLE U (2 * d)).ι

end SSet

end

/-!
## Hom from a finite simplicial set into a simplicial object

Let `C` be a category with finite limits, let `U` be a *finite* simplicial set — finitely many
nondegenerate simplices, equivalently each `U_n` finite and every `n`-simplex degenerate for
`n ≫ 0` — and let `V` be a simplicial object of `C`. Then the simplicial object `Hom(U, V)` of
the source exists: there is a simplicial object `H` of `C` together with bijections
`Mor(W, H) = Mor(W × U, V)`, functorial in the simplicial object `W` of `C`. Moreover its terms
are the expected ones: `H_n` represents `X ↦ Mor(X × U × Δ[n], V)`, which is the functor
represented by `Hom(U × Δ[n], V)_0`.

Here `W × A`, for a simplicial object `W` of `C` and a simplicial set `A`, is the source's
product: `(W × A)_n = ∐_{a ∈ A_n} W_n`. A morphism `W × A ⟶ V` is therefore the same thing as
a family of morphisms `f_a : W_n ⟶ V_n` indexed by `a ∈ A_n`, `n ≥ 0`, such that
`W(φ) ≫ f_{A(φ)(a)} = f_a ≫ V(φ)` for every `φ : ⦋m⦌ ⟶ ⦋n⦌` and every `a ∈ A_n`. That family
is exactly `CategoryTheory.Functor.HomObj W V A`, whose `naturality` field is the displayed
identity, and `CategoryTheory.Functor.functorHomEquiv` identifies it with `A ⟶ sHom W V`, the
`SSet`-enriched hom of `SimplicialObject C`. The statement below is phrased with the latter,
so that the hom-sets `Mor(W × U, V)` are available whether or not the objects `W × U` are; the
monoidal product `⊗` of `SSet` is the cartesian product, so `U ⊗ Δ[n]` is the source's
`U × Δ[n]`.

For `W` constant with value `X`, a family `Functor.HomObj W V A` is exactly a cone with vertex
`X` over the diagram `A.Elements ⥤ C`, `(m, a) ↦ V_m`. Consequently the object of `C`
representing `X ↦ Mor(X × A, V)` is the limit of that diagram, which exists for `A` finite by
[Stacks, Tag 017K]. Taking `A = U ⊗ Δ[n]` and using that `Δ[-]` is a cosimplicial simplicial set
gives the terms of `Hom(U, V)` together with its structure maps, and the morphisms
`W ⟶ Hom(U, V)` are computed by restricting the `n`-th one along the tautological simplex
`id ∈ Δ[n]_n`, as in the source's proof.

### Main results

* `CategoryTheory.SimplicialObject.exists_representableBy_sHom`: for `U` a finite simplicial
  set and `V` a simplicial object of a category with finite limits, the functor
  `W ↦ (U ⟶ sHom W V)`, i.e. `W ↦ Mor(W × U, V)`, is representable by a simplicial object `H`
  of `C`, whose `n`-th term represents `X ↦ Mor(X × U × Δ[n], V)`.

### References

* [Stacks, Tag 017L](https://stacks.math.columbia.edu/tag/017L)
-/

section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialCategory
  MonoidalCategory Opposite

open scoped Simplicial

universe v v' u u'

namespace CategoryTheory.SimplicialObject


variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- The diagram of simplices of `A` in `C` attached to a simplicial object `V`, sending an
`m`-simplex of `A` to `V_m`. -/
private abbrev diag (V : SimplicialObject C) (A : SSet.{v}) : A.Elements ⥤ C :=
  CategoryOfElements.π A ⋙ V

section

variable (V : SimplicialObject C) (A : SSet.{v})

omit [HasFiniteLimits C] in
/-- The compatibility of a family of morphisms `X ⟶ V_m` with the structure maps, i.e. the
naturality of a morphism `X × A ⟶ V` for `X` a constant simplicial object, reads
`y_a ≫ V(θ) = y_{A(θ)(a)}`. -/
private lemma app_comp_map {X : C}
    (y : Functor.HomObj ((SimplicialObject.const C).obj X) V A) {m m' : SimplexCategoryᵒᵖ}
    (θ : m ⟶ m') (a : A.obj m) : y.app m a ≫ V.map θ = y.app m' (A.map θ a) := by
  simpa using (y.naturality θ a).symm

omit [HasFiniteLimits C] in
/-- Conversely, a family of morphisms `X ⟶ V_m` indexed by the `m`-simplices of `A` and
compatible with the structure maps of `V` is a morphism `X × A ⟶ V` with `X` constant. -/
private def constHomObjMk {X : C} (φ : ∀ m : SimplexCategoryᵒᵖ, A.obj m → (X ⟶ V.obj m))
    (hφ : ∀ {m m' : SimplexCategoryᵒᵖ} (θ : m ⟶ m') (a : A.obj m),
      φ m a ≫ V.map θ = φ m' (A.map θ a)) :
    Functor.HomObj ((SimplicialObject.const C).obj X) V A where
  app := φ
  naturality θ a := by simpa using (hφ θ a).symm

variable [A.Finite]

/-- The object of `C` representing `X ↦ Mor(X × A, V)`: the limit of `(m, a) ↦ V_m` over the
simplices of the simplicial set `A`. -/
private noncomputable def limObj : C := limit (diag V A)

/-- The projection of `limObj V A` at an `m`-simplex `a` of `A`. -/
private noncomputable def limπ (m : SimplexCategoryᵒᵖ) (a : A.obj m) : limObj V A ⟶ V.obj m :=
  limit.π (diag V A) (A.elementsMk m a)

/-- Two morphisms into `limObj V A` that agree after every projection are equal. -/
private lemma limObj_hom_ext {X : C} {f g : X ⟶ limObj V A}
    (h : ∀ (m : SimplexCategoryᵒᵖ) (a : A.obj m), f ≫ limπ V A m a = g ≫ limπ V A m a) :
    f = g :=
  limit.hom_ext fun p ↦ h p.1 p.2

/-- The projections of `limObj V A` are compatible with the structure maps of `V`:
`π_a ≫ V(θ) = π_{A(θ)(a)}`. -/
private lemma limπ_comp_map {m m' : SimplexCategoryᵒᵖ} (θ : m ⟶ m') (a : A.obj m) :
    limπ V A m a ≫ V.map θ = limπ V A m' (A.map θ a) :=
  limit.w (diag V A) (Functor.Elements.homMk (x := A.elementsMk m a)
    (y := A.elementsMk m' (A.map θ a)) θ rfl)

/-- The object `limObj V A` represents `X ↦ Mor(X × A, V)`: a morphism `X ⟶ limObj V A` is the
same thing as a family of morphisms `X ⟶ V_m` indexed by the `m`-simplices of `A` and compatible
with the structure maps of `V`, i.e. as a morphism `X × A ⟶ V` of simplicial objects with `X`
constant. -/
private noncomputable def limObjEquiv (X : C) :
    (X ⟶ limObj V A) ≃ Functor.HomObj ((SimplicialObject.const C).obj X) V A where
  toFun f :=
    { app := fun m a ↦ f ≫ limπ V A m a
      naturality := fun {m m'} θ a ↦ by simp [limπ_comp_map] }
  invFun y :=
    limit.lift (diag V A)
      { pt := X
        π :=
          { app := fun p ↦ y.app p.1 p.2
            naturality := fun {p q} θ ↦ by
              rw [Functor.const_obj_map]
              exact (Category.id_comp _).trans
                ((app_comp_map V A y θ.1 p.2).trans (by rw [θ.2])).symm } }
  left_inv f := limObj_hom_ext V A fun m a ↦ limit.lift_π (F := diag V A) _ (A.elementsMk m a)
  right_inv y :=
    by ext m a; exact limit.lift_π (F := diag V A) _ (A.elementsMk m a)

/-- The morphism `X ⟶ limObj V A` attached to a family `y` has `y.app m a` as its component at
the `m`-simplex `a` of `A`. -/
private lemma limObjEquiv_symm_comp_limπ {X : C}
    (y : Functor.HomObj ((SimplicialObject.const C).obj X) V A) (m : SimplexCategoryᵒᵖ)
    (a : A.obj m) : (limObjEquiv V A X).symm y ≫ limπ V A m a = y.app m a :=
  limit.lift_π (F := diag V A) _ (A.elementsMk m a)

end

section

variable (V : SimplicialObject C)

/-- Restriction of `limObj V` along a morphism of simplicial sets. -/
private noncomputable def limRestr {A B : SSet.{v}} [A.Finite] [B.Finite] (f : A ⟶ B) :
    limObj V B ⟶ limObj V A :=
  limit.pre (diag V B) (CategoryOfElements.map f)

/-- The projection of `limRestr V f` at an `m`-simplex `a` of `A` is the projection of
`limObj V B` at `f(a)`. -/
private lemma limRestr_π {A B : SSet.{v}} [A.Finite] [B.Finite] (f : A ⟶ B)
    (m : SimplexCategoryᵒᵖ) (a : A.obj m) :
    limRestr V f ≫ limπ V A m a = limπ V B m (f.app m a) :=
  limit.pre_π _ _ _

/-- Restriction along the identity of `A` is the identity of `limObj V A`. -/
private lemma limRestr_id {A : SSet.{v}} [A.Finite] : limRestr V (𝟙 A) = 𝟙 _ := by
  refine limObj_hom_ext V A fun m a ↦ ?_
  rw [limRestr_π, Category.id_comp]
  rfl

/-- Restriction along a composite `f ≫ g` is the composite of the restrictions along `g` and
along `f`, in that order. -/
private lemma limRestr_comp {A B D : SSet.{v}} [A.Finite] [B.Finite] [D.Finite]
    (f : A ⟶ B) (g : B ⟶ D) : limRestr V (f ≫ g) = limRestr V g ≫ limRestr V f := by
  refine limObj_hom_ext V A fun m a ↦ ?_
  rw [Category.assoc, limRestr_π, limRestr_π, limRestr_π]
  rfl

/-- The simplicial object `Hom(U, V)` of [Stacks, Tag 017L]: its `n`-th term is the limit of
`(m, a) ↦ V_m` over the simplices `a` of `U ⊗ Δ[n]`. -/
private noncomputable def shom (U : SSet.{v}) [U.Finite] : SimplicialObject C where
  obj n := limObj V (U ⊗ SSet.stdSimplex.obj n.unop)
  map φ := limRestr V (U ◁ SSet.stdSimplex.map φ.unop)
  map_id n := by simp [limRestr_id]
  map_comp f g := by
    simp [limRestr_comp]

variable (U : SSet.{v}) [U.Finite]

/-- The projection of `Hom(U, V)_n` at an `m`-simplex of `U ⊗ Δ[n]`. -/
private noncomputable def shomπ (n m : SimplexCategoryᵒᵖ)
    (x : (U ⊗ SSet.stdSimplex.obj n.unop).obj m) : (shom V U).obj n ⟶ V.obj m :=
  limπ V (U ⊗ SSet.stdSimplex.obj n.unop) m x

/-- Two morphisms into `Hom(U, V)_n` that agree after every projection are equal. -/
private lemma shom_hom_ext {X : C} {n : SimplexCategoryᵒᵖ} {f g : X ⟶ (shom V U).obj n}
    (h : ∀ (m : SimplexCategoryᵒᵖ) (x : (U ⊗ SSet.stdSimplex.obj n.unop).obj m),
      f ≫ shomπ V U n m x = g ≫ shomπ V U n m x) : f = g :=
  limObj_hom_ext V _ h

/-- The projections of `Hom(U, V)_n` are compatible with the structure maps of `V`: the
projection at a simplex `x`, followed by `V(θ)`, is the projection at `(U ⊗ Δ[n])(θ)(x)`. -/
private lemma shomπ_comp_map {n m m' : SimplexCategoryᵒᵖ} (θ : m ⟶ m')
    (x : (U ⊗ SSet.stdSimplex.obj n.unop).obj m) :
    shomπ V U n m x ≫ V.map θ =
      shomπ V U n m' ((U ⊗ SSet.stdSimplex.obj n.unop).map θ x) :=
  limπ_comp_map V _ θ x

/-- The structure map `Hom(U, V)(φ)`, followed by the projection at a simplex `x` of
`U ⊗ Δ[n']`, is the projection at the simplex of `U ⊗ Δ[n]` obtained from `x` by moving its
`Δ`-coordinate along `φ`. -/
private lemma shom_map_shomπ {n n' : SimplexCategoryᵒᵖ} (φ : n ⟶ n') (m : SimplexCategoryᵒᵖ)
    (x : (U ⊗ SSet.stdSimplex.obj n'.unop).obj m) :
    (shom V U).map φ ≫ shomπ V U n' m x =
      shomπ V U n m ((U ◁ SSet.stdSimplex.map φ.unop).app m x) :=
  limRestr_π V _ m x

/-- The `n`-th term of `Hom(U, V)` represents `X ↦ Mor(X × U × Δ[n], V)`: a morphism
`X ⟶ Hom(U, V)_n` is the same thing as a morphism `X × U × Δ[n] ⟶ V` with `X` constant. -/
private noncomputable def shomEquiv (n : SimplexCategoryᵒᵖ) (X : C) :
    (X ⟶ (shom V U).obj n) ≃
      Functor.HomObj ((SimplicialObject.const C).obj X) V (U ⊗ SSet.stdSimplex.obj n.unop) :=
  limObjEquiv V _ X

/-- The morphism `X ⟶ Hom(U, V)_n` attached to a family `y` has `y.app m x` as its component at
the `m`-simplex `x` of `U ⊗ Δ[n]`. -/
private lemma shomEquiv_symm_comp_shomπ {n : SimplexCategoryᵒᵖ} {X : C}
    (y : Functor.HomObj ((SimplicialObject.const C).obj X) V (U ⊗ SSet.stdSimplex.obj n.unop))
    (m : SimplexCategoryᵒᵖ) (x : (U ⊗ SSet.stdSimplex.obj n.unop).obj m) :
    (shomEquiv V U n X).symm y ≫ shomπ V U n m x = y.app m x :=
  limObjEquiv_symm_comp_limπ V _ y m x

/-- Under `shomEquiv`, precomposition by `g : X ⟶ X'` is the precomposition of a family by `g`. -/
private lemma shomEquiv_comp {n : SimplexCategoryᵒᵖ} {X X' : C} (g : X ⟶ X')
    (f : X' ⟶ (shom V U).obj n) :
    shomEquiv V U n X (g ≫ f) =
      (Functor.HomObj.ofNatTrans ((SimplicialObject.const C).map g)).comp
        (shomEquiv V U n X' f) :=
  by ext m x; exact Category.assoc g f (shomπ V U n m x)

end

section

variable (U : SSet.{v})

/-- The simplex `(u, id)` of `U ⊗ Δ[m]` attached to an `m`-simplex `u` of `U`. -/
private abbrev taut (m : SimplexCategoryᵒᵖ) (u : U.obj m) :
    (U ⊗ SSet.stdSimplex.obj m.unop).obj m :=
  (u, SSet.stdSimplex.objEquiv.symm (𝟙 m.unop))

/-- Pushing the tautological `m`-simplex of `U ⊗ Δ[m]` forward to the degree `m'` along
`φ : m ⟶ m'` in both possible ways — moving the `Δ`-coordinate by `φ`, or restricting it along
`φ` — gives the simplex `(U(φ)(u), φ)`. -/
private lemma whiskerLeft_app_taut {m m' : SimplexCategoryᵒᵖ} (φ : m ⟶ m') (u : U.obj m) :
    (U ◁ SSet.stdSimplex.map φ.unop).app m' (taut U m' (U.map φ u)) =
      (U ⊗ SSet.stdSimplex.obj m.unop).map φ (taut U m u) := rfl

/-- Restricting the tautological `m`-simplex of `U ⊗ Δ[m]` along an `m`-simplex `ψ` of `Δ[n]`
gives back the simplex `(u, ψ)`. -/
private lemma whiskerLeft_app_taut_objEquiv {n : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (z : (U ⊗ SSet.stdSimplex.{v}.obj n).obj m) :
    (U ◁ SSet.stdSimplex.map (SSet.stdSimplex.objEquiv z.2)).app m (taut U m z.1) = z :=
  Prod.ext rfl ((SSet.stdSimplex.objEquiv_symm_comp _ _).symm.trans
    (by rw [Category.id_comp, Equiv.symm_apply_apply]))

end

section

variable (V : SimplicialObject C) (U : SSet.{v}) [U.Finite]

/-- A morphism `W ⟶ Hom(U, V)` restricts, in degree `m`, along the tautological simplex
`id ∈ Δ[m]_m` to a family of morphisms `W_m ⟶ V_m` indexed by the `m`-simplices of `U`, i.e. to
a morphism `W × U ⟶ V`. -/
private noncomputable def toHomObj {W : SimplicialObject C} (f : W ⟶ shom V U) :
    Functor.HomObj W V U where
  app m u := f.app m ≫ shomπ V U m m (taut U m u)
  naturality {m m'} φ u := by
    rw [← Category.assoc, f.naturality φ, Category.assoc, shom_map_shomπ, Category.assoc,
      shomπ_comp_map, whiskerLeft_app_taut]

/-- The component of `toHomObj V U f` at an `m`-simplex `u` of `U` is `f_m` followed by the
projection at the tautological simplex `(u, id)`. -/
private lemma toHomObj_app {W : SimplicialObject C} (f : W ⟶ shom V U) (m : SimplexCategoryᵒᵖ)
    (u : U.obj m) : (toHomObj V U f).app m u = f.app m ≫ shomπ V U m m (taut U m u) :=
  rfl

/-- Precomposition by `g : W ⟶ W'` corresponds, under `toHomObj`, to the precomposition of a
family by `g`. -/
private lemma toHomObj_comp {W W' : SimplicialObject C} (g : W ⟶ W') (f : W' ⟶ shom V U) :
    toHomObj V U (g ≫ f) = (Functor.HomObj.ofNatTrans g).comp (toHomObj V U f) :=
  by ext m u; exact Category.assoc (g.app m) (f.app m) (shomπ V U m m (taut U m u))

omit [HasFiniteLimits C] [U.Finite] in
/-- The morphism `W_n × (U ⊗ Δ[n]) ⟶ V` attached to a morphism `x : W × U ⟶ V`: at the simplex
`(u, ψ) ∈ U_m × Δ[n]_m` it is `W(ψ) ≫ x_{m, u}`. -/
private def constHomObj {W : SimplicialObject C} (x : Functor.HomObj W V U)
    (n : SimplexCategoryᵒᵖ) :
    Functor.HomObj ((SimplicialObject.const C).obj (W.obj n)) V
      (U ⊗ SSet.stdSimplex.obj n.unop) :=
  constHomObjMk V _ (fun m z ↦ W.map (SSet.stdSimplex.objEquiv z.2).op ≫ x.app m z.1)
    fun θ z ↦ by
      rw [Category.assoc, ← x.naturality θ z.1, ← Category.assoc, ← W.map_comp]
      rfl

omit [HasFiniteLimits C] [U.Finite] in
/-- The component of `constHomObj V U x n` at a simplex `z = (u, ψ)` of `U ⊗ Δ[n]` is
`W(ψ) ≫ x_{m, u}`. -/
private lemma constHomObj_app {W : SimplicialObject C} (x : Functor.HomObj W V U)
    (n m : SimplexCategoryᵒᵖ) (z : (U ⊗ SSet.stdSimplex.obj n.unop).obj m) :
    (constHomObj V U x n).app m z = W.map (SSet.stdSimplex.objEquiv z.2).op ≫ x.app m z.1 :=
  rfl

/-- A morphism `x : W × U ⟶ V` of simplicial objects induces a morphism `W ⟶ Hom(U, V)`: its
degree `n` component is the morphism into the limit `Hom(U, V)_n` given by the family
`constHomObj x n`. -/
private noncomputable def ofHomObj {W : SimplicialObject C} (x : Functor.HomObj W V U) :
    W ⟶ shom V U where
  app n := (shomEquiv V U n (W.obj n)).symm (constHomObj V U x n)
  naturality {n n'} φ := by
    refine shom_hom_ext V U fun m z ↦ ?_
    rw [Category.assoc, shomEquiv_symm_comp_shomπ, Category.assoc, shom_map_shomπ,
      shomEquiv_symm_comp_shomπ, constHomObj_app, constHomObj_app, ← Category.assoc,
      ← W.map_comp]
    rfl

/-- The degree `n` component of `ofHomObj V U x`, followed by the projection at a simplex
`z = (u, ψ)` of `U ⊗ Δ[n]`, is `W(ψ) ≫ x_{m, u}`. -/
private lemma ofHomObj_app_shomπ {W : SimplicialObject C} (x : Functor.HomObj W V U)
    (n m : SimplexCategoryᵒᵖ) (z : (U ⊗ SSet.stdSimplex.obj n.unop).obj m) :
    (ofHomObj V U x).app n ≫ shomπ V U n m z =
      W.map (SSet.stdSimplex.objEquiv z.2).op ≫ x.app m z.1 :=
  shomEquiv_symm_comp_shomπ V U (constHomObj V U x n) m z

/-- The universal property of `Hom(U, V)`: morphisms `W ⟶ Hom(U, V)` of simplicial objects are
the same thing as morphisms `W × U ⟶ V`. -/
private noncomputable def homObjEquiv (W : SimplicialObject C) :
    (W ⟶ shom V U) ≃ Functor.HomObj W V U where
  toFun := toHomObj V U
  invFun := ofHomObj V U
  left_inv f := by
    ext n
    refine shom_hom_ext V U fun m z ↦ ?_
    rw [ofHomObj_app_shomπ, toHomObj_app, ← Category.assoc,
      f.naturality (SSet.stdSimplex.objEquiv z.2).op, Category.assoc, shom_map_shomπ]
    exact congrArg (fun w ↦ f.app n ≫ shomπ V U n m w) (whiskerLeft_app_taut_objEquiv U z)
  right_inv x := by
    ext m u
    rw [toHomObj_app, ofHomObj_app_shomπ]
    simp

end

section

variable (V : SimplicialObject C) (A : SSet.{v})

omit [HasFiniteLimits C]

/-- Under the bijection `(A ⟶ sHom W V) ≃ Mor(W × A, V)`, the enriched precomposition by
`g : W ⟶ W'` is the precomposition of a family `(f'_{m, u})` by `g`. -/
private lemma functorHomEquiv_comp_eHomWhiskerRight {W W' : SimplicialObject C} (g : W ⟶ W')
    (y : A ⟶ sHom W' V) :
    Functor.functorHomEquiv W V A (y ≫ eHomWhiskerRight SSet.{v} g V) =
      (Functor.HomObj.ofNatTrans g).comp (Functor.functorHomEquiv W' V A y) :=
  by ext; rfl

/-- A family of bijections `Mor(X, H) ≃ Mor(G X × A, V)`, compatible with precomposition,
represents the functor `X ↦ (A ⟶ sHom (G X) V)`, i.e. `X ↦ Mor(G X × A, V)`. -/
private def representableByOfHomObjEquiv {D : Type u'} [Category.{v'} D]
    (G : D ⥤ SimplicialObject C) (H : D) (e : ∀ X : D, (X ⟶ H) ≃ Functor.HomObj (G.obj X) V A)
    (he : ∀ {X Y : D} (g : X ⟶ Y) (f : Y ⟶ H),
      e X (g ≫ f) = (Functor.HomObj.ofNatTrans (G.map g)).comp (e Y f)) :
    (G.op ⋙ sHomFunctor (SimplicialObject C) ⋙
      (evaluation (SimplicialObject C) SSet.{v}).obj V ⋙
      coyoneda.obj (op A)).RepresentableBy H where
  homEquiv {X} := (e X).trans (Functor.functorHomEquiv (G.obj X) V A).symm
  homEquiv_comp {X Y} g f := by
    have h : e X (g ≫ f) = Functor.functorHomEquiv (G.obj X) V A
        ((Functor.functorHomEquiv (G.obj Y) V A).symm (e Y f) ≫
          eHomWhiskerRight SSet.{v} (G.map g) V) := by
      rw [functorHomEquiv_comp_eHomWhiskerRight, Equiv.apply_symm_apply, he]
    exact (Equiv.symm_apply_eq _).2 h

end

/-- **Stacks 017L**.
Let `C` be a category with finite limits, let `U` be a finite simplicial set and let `V` be a
simplicial object of `C`. Then the simplicial object `Hom(U, V)` exists: the functor
`W ↦ (U ⟶ sHom W V)` on `(SimplicialObject C)ᵒᵖ`, which is `W ↦ Mor(W × U, V)`, is representable
by a simplicial object `H` of `C`; moreover `H _⦋n⦌` represents `X ↦ Mor(X × U × Δ[n], V)`, the
functor represented by `Hom(U × Δ[n], V)_0`. -/
@[stacks 017L, sga "4 V 7.3.6.0" "U finite, C fin. limits"]
public theorem exists_representableBy_sHom {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (U : SSet.{v}) [U.Finite] (V : SimplicialObject C) :
    ∃ H : SimplicialObject C,
      Nonempty ((sHomFunctor (SimplicialObject C) ⋙
        (evaluation (SimplicialObject C) SSet.{v}).obj V ⋙
        coyoneda.obj (op U)).RepresentableBy H) ∧
      ∀ n : ℕ, Nonempty (((SimplicialObject.const C).op ⋙ sHomFunctor (SimplicialObject C) ⋙
        (evaluation (SimplicialObject C) SSet.{v}).obj V ⋙
        coyoneda.obj (op (U ⊗ Δ[n]))).RepresentableBy (H _⦋n⦌)) :=
  ⟨shom V U,
    ⟨representableByOfHomObjEquiv V U (𝟭 _) (shom V U) (homObjEquiv V U)
      fun g f ↦ toHomObj_comp V U g f⟩,
    fun n ↦ ⟨representableByOfHomObjEquiv V (U ⊗ Δ[n]) (SimplicialObject.const C) _
      (shomEquiv V U (op ⦋n⦌)) fun g f ↦ shomEquiv_comp V U g f⟩⟩

end CategoryTheory.SimplicialObject

end

/-!
## Hom objects out of a pushout of simplicial sets

Let `C` be a category, let `T` be a simplicial object of `C` and let `K` be a simplicial set.
Following [Stacks, Tag 017I] one writes `Hom(K, T)` for a simplicial object of `C` representing
`W ↦ Mor_{Simp(C)}(W × K, T)`, where `W × K` is the simplicial object `n ↦ ∐_{u ∈ K_n} W_n` of
[Stacks, Tag 017C]. Its object of `0`-simplices `Hom(K, T)₀` represents the presheaf
`X ↦ Mor_{Simp(C)}(X × K, T)` on `C`, and by [Stacks, Tag 017L] the whole simplicial object is
recovered from these, since `Hom(K, T)_n = Hom(K × Δ[n], T)₀`.

This file records [Stacks, Tag 017N]: `Hom(-, T)` turns a pushout of simplicial sets into a
fibre product,
`Hom(V ⨿_U W, T) = Hom(V, T) ×_{Hom(U, T)} Hom(W, T)`,
in the sense that the four `Hom` objects, with the morphisms induced by `U → V`, `U → W` and by
the two morphisms into the pushout, form a cartesian square in `C`.

A morphism of simplicial objects `X × K ⟶ T` is the same thing as a family of morphisms
`f_u : X ⟶ T_n`, one for every `n ≥ 0` and every `u ∈ K_n`, subject to
`f_u ≫ T(φ) = f_{K(φ)(u)}` for all `φ : ⦋m⦌ ⟶ ⦋n⦌`: indeed a morphism out of `X × K` is a
family of morphisms out of the coproducts `∐_{u ∈ K_n} X`, and its naturality is the displayed
identity. Such a family is exactly a morphism of simplicial sets
`K ⟶ T ⋙ coyoneda.obj (op X)`, the target being the simplicial set `n ↦ Mor_C(X, T_n)` of
`X`-points of `T`. The presheaf represented by `Hom(K, T)₀` is written in the latter form below,
i.e. as `coyoneda ⋙ (Functor.whiskeringLeft _ C (Type v)).obj T ⋙ coyoneda.obj (op K)`; this
makes sense whether or not the simplicial objects `X × K` exist.

An `X`-point of the fibre product is a pair of morphisms `V ⟶ T ⋙ coyoneda.obj (op X)`,
`W ⟶ T ⋙ coyoneda.obj (op X)` agreeing on `U`, hence a single morphism out of the pushout
`P = V ⨿_U W`, hence a single morphism `X ⟶ Hom(P, T)₀`.

### Main results

* `CategoryTheory.SimplicialObject.isPullback_hom_of_isPushout`: for a pushout square of
  simplicial sets and a simplicial object `T`, the objects representing
  `X ↦ Mor(X × K, T)` for the four simplicial sets `K` in the square form a pullback square,
  along the canonically induced morphisms.

### References

* [Stacks, Tag 017N](https://stacks.math.columbia.edu/tag/017N)
-/

section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe v u u₁ u₂

namespace CategoryTheory.SimplicialObject

section InducedHom

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-- The morphism `HK' ⟶ HK` induced by `k : K ⟶ K'`, where `HK` represents the presheaf
`X ↦ Mor_D(K, G X)` on `C` and `HK'` represents `X ↦ Mor_D(K', G X)`: it is the morphism
corresponding to the universal element of `HK'` restricted along `k`. On points it is
precomposition with `k`. -/
private def inducedHom (G : Cᵒᵖ ⥤ D) {K K' : D} (k : K ⟶ K') {HK HK' : C}
    (hK : (G ⋙ coyoneda.obj (op K)).RepresentableBy HK)
    (hK' : (G ⋙ coyoneda.obj (op K')).RepresentableBy HK') : HK' ⟶ HK :=
  hK.homEquiv.symm (k ≫ hK'.homEquiv (𝟙 HK'))

/-- `inducedHom G k hK hK'` is precomposition with `k` on points: for every `u : X ⟶ HK'`, the
element of `Mor_D(K, G X)` corresponding to `u` followed by it is `k` followed by the element of
`Mor_D(K', G X)` corresponding to `u`. -/
private lemma homEquiv_comp_inducedHom (G : Cᵒᵖ ⥤ D) {K K' : D} (k : K ⟶ K') {HK HK' : C}
    (hK : (G ⋙ coyoneda.obj (op K)).RepresentableBy HK)
    (hK' : (G ⋙ coyoneda.obj (op K')).RepresentableBy HK')
    {X : C} (u : X ⟶ HK') :
    hK.homEquiv (u ≫ inducedHom G k hK hK') = k ≫ hK'.homEquiv u := by
  rw [inducedHom, hK.comp_homEquiv_symm, Equiv.apply_symm_apply, hK'.homEquiv_eq u]
  exact Category.assoc _ _ _

/-- `inducedHom` is contravariantly functorial: the morphism induced by `k ≫ k'` is the morphism
induced by `k'` followed by the morphism induced by `k`. -/
private lemma inducedHom_comp_inducedHom (G : Cᵒᵖ ⥤ D) {K K' K'' : D} (k : K ⟶ K')
    (k' : K' ⟶ K'') {HK HK' HK'' : C}
    (hK : (G ⋙ coyoneda.obj (op K)).RepresentableBy HK)
    (hK' : (G ⋙ coyoneda.obj (op K')).RepresentableBy HK')
    (hK'' : (G ⋙ coyoneda.obj (op K'')).RepresentableBy HK'') :
    inducedHom G k' hK' hK'' ≫ inducedHom G k hK hK' = inducedHom G (k ≫ k') hK hK'' := by
  apply hK.homEquiv.injective
  rw [homEquiv_comp_inducedHom, inducedHom, inducedHom, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, Category.assoc]

section IsPushout

variable (G : Cᵒᵖ ⥤ D) {U V W P : D} {a : U ⟶ V} {b : U ⟶ W} {f : V ⟶ P} {g : W ⟶ P}
  (h : IsPushout a b f g) {HU HV HW HP : C}
  (hU : (G ⋙ coyoneda.obj (op U)).RepresentableBy HU)
  (hV : (G ⋙ coyoneda.obj (op V)).RepresentableBy HV)
  (hW : (G ⋙ coyoneda.obj (op W)).RepresentableBy HW)
  (hP : (G ⋙ coyoneda.obj (op P)).RepresentableBy HP)

include h

/-- The universal property of the pushout, read on representing objects: an `X`-point of `HV`
and an `X`-point of `HW` that agree on `HU` are the images of a unique `X`-point of `HP`. Under
the representability bijections they are morphisms `V ⟶ G X` and `W ⟶ G X` agreeing on `U`,
hence come from a unique morphism `V ⨿_U W ⟶ G X`. -/
private lemma existsUnique_inducedHom {X : C} (s₁ : X ⟶ HV) (s₂ : X ⟶ HW)
    (hs : s₁ ≫ inducedHom G a hU hV = s₂ ≫ inducedHom G b hU hW) :
    ∃! u : X ⟶ HP, u ≫ inducedHom G f hV hP = s₁ ∧ u ≫ inducedHom G g hW hP = s₂ := by
  refine ⟨hP.homEquiv.symm (h.desc (hV.homEquiv s₁) (hW.homEquiv s₂) ?_), ⟨?_, ?_⟩, ?_⟩
  · rw [← homEquiv_comp_inducedHom, ← homEquiv_comp_inducedHom, hs]
  · exact hV.homEquiv.injective (by
      rw [homEquiv_comp_inducedHom, Equiv.apply_symm_apply, IsPushout.inl_desc])
  · exact hW.homEquiv.injective (by
      rw [homEquiv_comp_inducedHom, Equiv.apply_symm_apply, IsPushout.inr_desc])
  · rintro m ⟨hm₁, hm₂⟩
    refine hP.homEquiv.injective ?_
    rw [Equiv.apply_symm_apply]
    exact h.hom_ext (by rw [h.inl_desc, ← homEquiv_comp_inducedHom, hm₁])
      (by rw [h.inr_desc, ← homEquiv_comp_inducedHom, hm₂])

/-- A pushout goes to a fibre product of representing objects. Let `G : Cᵒᵖ ⥤ D` be a functor
and let `U ⟶ V`, `U ⟶ W`, `V ⟶ P`, `W ⟶ P` be a pushout square in `D`. Assume that
for each `K` among `U`, `V`, `W`, `P` the presheaf `X ↦ Mor_D(K, G X)` on `C` is represented by
an object `HK`. Then `HP` is the fibre product of `HV` and `HW` over `HU`, along the morphisms
induced by the four morphisms of the square. -/
private theorem isPullback_inducedHom_of_isPushout :
    IsPullback (inducedHom G f hV hP) (inducedHom G g hW hP)
      (inducedHom G a hU hV) (inducedHom G b hU hW) := by
  have comm : inducedHom G f hV hP ≫ inducedHom G a hU hV
      = inducedHom G g hW hP ≫ inducedHom G b hU hW := by
    rw [inducedHom_comp_inducedHom, inducedHom_comp_inducedHom, h.w]
  have huniv := fun (s : PullbackCone (inducedHom G a hU hV) (inducedHom G b hU hW)) =>
    existsUnique_inducedHom G h hU hV hW hP s.fst s.snd s.condition
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk comm (fun s => (huniv s).choose)
    (fun s => (huniv s).choose_spec.1.1) (fun s => (huniv s).choose_spec.1.2)
    (fun s m hm₁ hm₂ => (huniv s).choose_spec.2 m ⟨hm₁, hm₂⟩))

end IsPushout

end InducedHom

/-- **Stacks 017N**.
Let `T` be a simplicial object of a category `C`, let `a : U ⟶ V` and `b : U ⟶ W` be morphisms
of simplicial sets, and let `P = V ⨿_U W` be their pushout, with structure morphisms
`f : V ⟶ P`, `g : W ⟶ P`. Assume that for each of the four simplicial sets `K = U, V, W, P` the
presheaf `X ↦ Mor_{Simp(C)}(X × K, T) = Mor_{SSet}(K, T ⋙ coyoneda.obj (op X))` on `C` is
represented by an object `Hom(K, T)₀` of `C` — as it is, by [Stacks, Tag 017L], when `C` has
coproducts of any two objects and finite limits, the `U_n`, `V_n`, `W_n` are finite nonempty and
all simplices of `U`, `V`, `W` in high enough degree are degenerate. Then
`Hom(P, T)₀ = Hom(V, T)₀ ×_{Hom(U, T)₀} Hom(W, T)₀`
via the morphisms induced by `f`, `g`, `a` and `b`. -/
@[stacks 017N "stated in degree 0, for the representing objects of `X ↦ Mor(X × K, T)`"]
public theorem isPullback_hom_of_isPushout {C : Type u} [Category.{v} C]
    (T : SimplicialObject C) {U V W P : SSet.{v}}
    {a : U ⟶ V} {b : U ⟶ W} {f : V ⟶ P} {g : W ⟶ P} (h : IsPushout a b f g)
    {HU HV HW HP : C}
    (hU : (coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ C (Type v)).obj T ⋙
        coyoneda.obj (op U)).RepresentableBy HU)
    (hV : (coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ C (Type v)).obj T ⋙
        coyoneda.obj (op V)).RepresentableBy HV)
    (hW : (coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ C (Type v)).obj T ⋙
        coyoneda.obj (op W)).RepresentableBy HW)
    (hP : (coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ C (Type v)).obj T ⋙
        coyoneda.obj (op P)).RepresentableBy HP) :
    IsPullback (hV.homEquiv.symm (f ≫ hP.homEquiv (𝟙 HP)))
      (hW.homEquiv.symm (g ≫ hP.homEquiv (𝟙 HP)))
      (hU.homEquiv.symm (a ≫ hV.homEquiv (𝟙 HV)))
      (hU.homEquiv.symm (b ≫ hW.homEquiv (𝟙 HW))) :=
  isPullback_inducedHom_of_isPushout
    (coyoneda ⋙ (Functor.whiskeringLeft SimplexCategoryᵒᵖ C (Type v)).obj T) h hU hV hW hP

end CategoryTheory.SimplicialObject

end
