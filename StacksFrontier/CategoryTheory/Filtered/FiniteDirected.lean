module

public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
public import Mathlib.Order.Preorder.Finite

/-!
# Finite directed sets versus finite filtered categories

Stacks 09P8 contrasts two finiteness statements about colimits.

* A finite directed set has a greatest element `i∞`, so a colimit over it is *trivial*: the
  structure map from the value at `i∞` to the colimit is an isomorphism.
* A colimit over a finite *filtered category* need not be trivial. The source's witness is the
  category with a single object and a single non-trivial morphism `e` satisfying `e = e ∘ e`;
  the colimit of a diagram `M` of sets over it is the image of the idempotent `M e`.

## Main results

* `exists_isTop`: a finite nonempty directed preorder has a greatest element.
* `IsTop.isTerminal`: a greatest element is a terminal object of the preorder category.
* `CategoryTheory.exists_isTop_and_isIso_colimit_ι`: **Stacks 09P8**, first half.
* `CategoryTheory.Limits.SingleObj.isFiltered_of_forall_exists_mul_eq` and
  `CategoryTheory.Limits.SingleObj.instIsFilteredSingleObjOfMonoidWithZero`: `SingleObj M` is
  filtered as soon as any two elements of `M` can be equalized by left multiplication, which
  happens in particular when `M` has a zero.
* `CategoryTheory.Limits.SingleObj.isColimitRangeCocone`: **Stacks 09P8**, second half — the
  colimit of a diagram of sets indexed by `SingleObj M` is the image of the idempotent given by a
  left-absorbing element `e` of `M`.
* `CategoryTheory.Limits.SingleObj.not_injective_ι_constDiagram`: the promised failure of
  triviality, over the source's index category `SingleObj (WithZero Unit)`, which is both finite
  (a `FinCategory`) and filtered.

## Implementation notes

The source's index category — one object, one non-trivial idempotent endomorphism — is
`CategoryTheory.SingleObj M` for `M` the two-element monoid `WithZero Unit`, whose non-identity
element is `0`. Working with a general monoid `M` and a left-absorbing element `e` (`e * x = e`)
rather than with that two-element monoid costs nothing and makes the idempotent hypothesis
`e * e = e` automatic. The self-map `x ↦ F.map e x` of the value of the diagram is written using
the `MulAction M (F.obj (SingleObj.star M))` instance from
`Mathlib/CategoryTheory/Limits/Shapes/SingleObj.lean`, so `e • x` *is* `F.map e x`; this is
`CategoryTheory.Limits.SingleObj.smul_eq_map`.
-/

@[expose] public section

universe u v

open CategoryTheory Limits

/-- A `Fintype` structure on `WithZero α`, which is `Option α` with `0` playing the role of
`none`. -/
instance WithZero.instFintype {α : Type u} [Fintype α] : Fintype (WithZero α) :=
  inferInstanceAs (Fintype (Option α))

/-- A greatest element of a preorder is a terminal object of the associated category. This is the
converse of `CategoryTheory.Limits.IsTerminal.orderTop`. -/
def IsTop.isTerminal {I : Type u} [Preorder I] {i : I} (hi : IsTop i) : IsTerminal i :=
  letI : OrderTop I := { top := i, le_top := hi }
  Preorder.isTerminalTop I

/-- A finite nonempty directed preorder has a greatest element: a maximal element exists by
finiteness, and in a directed order maximal elements are greatest. -/
theorem exists_isTop {I : Type u} [Preorder I] [Finite I] [Nonempty I] [IsDirectedOrder I] :
    ∃ i : I, IsTop i := by
  obtain ⟨b, -, hb⟩ :=
    Finite.exists_le_maximal (p := fun _ : I => True) (a := Classical.arbitrary I) trivial
  exact ⟨b, IsMax.isTop fun _ hc => hb.le_of_ge trivial hc⟩

namespace CategoryTheory

/-- **Stacks 09P8**, first half. A finite directed set `I` has a greatest element `i∞`, and
therefore every colimit over `I` is trivial: the structure map from the value at `i∞` to the
colimit is an isomorphism. -/
@[stacks 09P8 "first half: a colimit over a finite directed set is trivial"]
theorem exists_isTop_and_isIso_colimit_ι {I : Type u} [Preorder I] [Finite I] [Nonempty I]
    [IsDirectedOrder I] {C : Type*} [Category C] (F : I ⥤ C) [HasColimit F] :
    ∃ i : I, IsTop i ∧ IsIso (colimit.ι F i) := by
  obtain ⟨i, hi⟩ := exists_isTop (I := I)
  exact ⟨i, hi, isIso_ι_of_isTerminal hi.isTerminal F⟩

namespace Limits.SingleObj

open CategoryTheory.SingleObj

section Filtered

variable {M : Type u} [Monoid M]

/-- The single-object category on a monoid `M` is filtered as soon as any two elements of `M`
become equal after multiplying on the left by a suitable element. The condition on objects is
vacuous, and the condition on morphisms is exactly this. -/
lemma isFiltered_of_forall_exists_mul_eq (h : ∀ f g : M, ∃ a : M, a * f = a * g) :
    IsFiltered (SingleObj M) where
  cocone_objs _ _ := ⟨star M, 1, 1, trivial⟩
  cocone_maps := fun {_ _} f g =>
    have ⟨a, ha⟩ := h f g
    ⟨star M, a, ha⟩
  nonempty := ⟨star M⟩

/-- If `M` has a zero then `SingleObj M` is filtered: multiplying on the left by `0` equalizes
any two morphisms. -/
instance instIsFilteredSingleObjOfMonoidWithZero {M : Type u} [MonoidWithZero M] :
    IsFiltered (SingleObj M) :=
  isFiltered_of_forall_exists_mul_eq fun _ _ => ⟨0, by rw [zero_mul, zero_mul]⟩

end Filtered

section Colimit

variable {M : Type u} [Monoid M] (F : SingleObj M ⥤ Type v) (e : M)

/-- The `MulAction` of `M` on the value of a diagram `F : SingleObj M ⥤ Type v` is by the maps of
the diagram: `e • x` is `M(e)(x)` in the notation of the source. -/
lemma smul_eq_map (g : M) (x : F.obj (star M)) : g • x = F.map g x := rfl

/-- If `e` is left-absorbing then the self-map `x ↦ e • x` of the value of the diagram swallows
every other map of the diagram. -/
lemma smul_smul_eq_smul (he : ∀ x : M, e * x = e) (g : M) (x : F.obj (star M)) :
    e • g • x = e • x := by
  rw [smul_smul, he]

/-- The cocone on `F : SingleObj M ⥤ Type v` whose vertex is the image of the idempotent
`x ↦ e • x` attached to a left-absorbing element `e`, with that idempotent as structure map.
`isColimitRangeCocone` shows it is a colimit. -/
def rangeCocone (he : ∀ x : M, e * x = e) : Cocone F where
  pt := Set.range fun x : F.obj (star M) => e • x
  ι :=
    { app := fun _ => ↾Set.rangeFactorization fun x : F.obj (star M) => e • x
      naturality := fun _ _ g => by
        ext x
        exact Subtype.ext (smul_smul_eq_smul F e he g x) }

/-- **Stacks 09P8**, second half. Let `e` be a left-absorbing element of a monoid `M`, so in
particular an idempotent. The colimit of a diagram of sets indexed by the single-object category
`SingleObj M` is the image of the idempotent `x ↦ e • x`, that is, of the map by which `e` acts.
For the source's index category — one object with one non-trivial morphism `e` satisfying
`e = e ∘ e` — take `M = WithZero Unit` and `e = 0`. -/
@[stacks 09P8 "second half: the colimit over the one-object category on an idempotent"]
def isColimitRangeCocone (he : ∀ x : M, e * x = e) : IsColimit (rangeCocone F e he) where
  desc s := ↾fun y => s.ι.app (star M) y.1
  fac s _ := by
    ext x
    exact ConcreteCategory.congr_hom (s.w (j := star M) (j' := star M) e) x
  uniq s m w := by
    ext ⟨-, x, rfl⟩
    exact (ConcreteCategory.congr_hom (w (star M)) x).trans
      (ConcreteCategory.congr_hom (s.w (j := star M) (j' := star M) e) x).symm

/-- The structure map into the colimit is injective exactly when the idempotent `x ↦ e • x` is.
So the colimit is trivial — the value of the diagram itself — precisely when that idempotent is
injective. -/
lemma injective_rangeCocone_ι_iff (he : ∀ x : M, e * x = e) :
    Function.Injective ((rangeCocone F e he).ι.app (star M)) ↔
      Function.Injective fun x : F.obj (star M) => e • x := by
  refine ⟨fun h x y hxy => h (Subtype.ext hxy), fun h x y hxy => h ?_⟩
  exact congrArg Subtype.val hxy

end Colimit

/-- The source's index category is finite. -/
example : FinCategory (SingleObj (WithZero Unit)) := inferInstance

/-- The source's index category is filtered. -/
example : IsFiltered (SingleObj (WithZero Unit)) := inferInstance

/-- The non-identity morphism of the source's index category is non-trivial and idempotent. -/
example : (0 : WithZero Unit) ≠ 1 ∧ (0 : WithZero Unit) * 0 = 0 := ⟨zero_ne_one, mul_zero 0⟩

/-- The diagram of sets on the source's index category `SingleObj (WithZero Unit)` — one object
and one non-trivial morphism `0`, which satisfies `0 * 0 = 0` — given by a type `X` and a
constant self-map of `X`. -/
def constDiagram (X : Type v) (a : X) : SingleObj (WithZero Unit) ⥤ Type v where
  obj _ := X
  map g := WithZero.recZeroCoe (↾Function.const X a) (fun _ => 𝟙 X) g
  map_id _ := rfl
  map_comp g h := by
    induction g using WithZero.recZeroCoe with
    | zero =>
      induction h using WithZero.recZeroCoe with
      | zero => rfl
      | coe b => cases b; rfl
    | coe b =>
      cases b
      induction h using WithZero.recZeroCoe with
      | zero => rfl
      | coe c => cases c; rfl

/-- The colimit of `constDiagram X a` is the image of a constant map, a singleton, so its
structure map is not injective as soon as `X` has an element other than `a`. Together with
`instIsFilteredSingleObjOfMonoidWithZero` and the `FinCategory` instance on
`SingleObj (WithZero Unit)`, this is the second assertion of Stacks 09P8: a colimit indexed by a
*finite filtered* category need not be trivial. -/
@[stacks 09P8 "second half: the colimit need not be trivial"]
theorem not_injective_ι_constDiagram {X : Type v} (a : X) (hX : ∃ x : X, x ≠ a) :
    ¬ Function.Injective
      ((rangeCocone (constDiagram X a) 0 fun x => zero_mul x).ι.app
        (star (WithZero Unit))) := by
  obtain ⟨x, hx⟩ := hX
  rw [injective_rangeCocone_ι_iff]
  exact fun h => hx (h (a₁ := x) (a₂ := a) rfl)

end Limits.SingleObj

end CategoryTheory
