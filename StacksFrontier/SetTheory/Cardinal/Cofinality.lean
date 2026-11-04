module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Regular
public import StacksCore.Tactic.StacksAttribute

/-!
# Cofinality: unbounded ordinals and maps into ordinal-indexed colimits

## Cofinalities are unbounded (Stacks 05N3)

Stacks 05N3 records that for every cardinal `κ` there is an ordinal whose cofinality
exceeds `κ`; equivalently, the cofinality function `Ordinal.cof` takes arbitrarily large
values, so no cardinal bounds all cofinalities.

The witness is the standard one. Set `λ = κ ⊔ ℵ₀`, an infinite cardinal, and take the
ordinal `α = (λ⁺).ord`, the initial ordinal of the cardinal successor of `λ`. Successors
of infinite cardinals are regular (`Cardinal.isRegular_succ`), and a regular cardinal `c`
satisfies `c.ord.cof = c` (`Cardinal.IsRegular.cof_ord`), so `α.cof = λ⁺ > λ ≥ κ`.

Here `Order.succ` on `Cardinal` is the cardinal successor `λ⁺`, and `Cardinal.ord` sends a
cardinal to its initial ordinal.

## Maps into an ordinal-indexed colimit (Stacks 05N2)

Stacks 05N2: if `T = colim_{α < β} T_α` is the colimit of an ordinal-indexed direct system
and `S` is a set with `|S| < cf(β)`, then every map `φ : S → T` factors through one of the
stages, i.e. there are an `α < β` and a `φ_α : S → T_α` with `ι_α ∘ φ_α = φ`.

The direct system and its colimit are Mathlib's: `DirectedSystem F f` for the functoriality
laws and `DirectLimit F f` for the colimit, the quotient of `Σ i, F i` identifying `x : F i`
with its image in any later stage. The canonical map `ι_α` is `fun x => ⟦⟨α, x⟩⟧`.

Indexing is by the subtype `{α : Ordinal // α < β}`, which keeps the system genuinely
`β`-indexed. That subtype is a directed order for every `β` — two indices are bounded by
their maximum, and for `β = 0` it is empty and the condition holds vacuously — so
`DirectLimit` applies with no side condition on `β`. Since the stages are `Type u` and the
index type is `Type (u+1)`, the colimit lands in `Type (u+1)` while the source set `S`
stays in `Type u`, matching the hypothesis `|S| < cf(β)`.

Following Mathlib's `DirectLimit` API, the transition maps are an arbitrary `FunLike`
family rather than bare functions, so the statement covers systems of sets (with the
identity `FunLike` on `F i → F j`) and systems of bundled homs alike.

The proof picks a representative `⟨α_s, t_s⟩` of `φ s` for each `s : S`
(`DirectLimit.exists_eq_mk`). The supremum `⨆ s, α_s` is still `< β`, the family being
indexed by a set of cardinality `< cf(β)` (`Ordinal.iSup_lt_of_lt_cof`), so pushing every
representative forward to that supremum gives the required factorization
(`DirectLimit.mk_apply`).
-/

@[expose] public section

namespace Cardinal

/-- **Stacks 05N3.** For every cardinal `κ` there is an ordinal `α` with `κ < cf(α)`:
the successor of the infinite cardinal `κ ⊔ ℵ₀` is regular, so the ordinal it indexes has
cofinality `(κ ⊔ ℵ₀)⁺`, which is strictly greater than `κ`. -/
@[stacks 05N3]
theorem exists_ordinal_cof_gt (κ : Cardinal) : ∃ α : Ordinal, κ < α.cof :=
  ⟨(Order.succ (κ ⊔ Cardinal.aleph0)).ord, by
    rw [(Cardinal.isRegular_succ le_sup_right).cof_ord]
    exact lt_of_le_of_lt le_sup_left (Order.lt_succ _)⟩

end Cardinal

namespace Ordinal

universe u v

/-- **Stacks 05N2.** Let `β` be an ordinal and `(F_α)_{α < β}` an ordinal-indexed direct
system with colimit `DirectLimit F f` and canonical maps `ι_α : F_α → DirectLimit F f`,
`x ↦ ⟦⟨α, x⟩⟧`. Let `S` be a set and `φ : S → DirectLimit F f` a function. If the
cofinality of `β` exceeds the cardinality of `S`, then `φ` factors through a single stage:
there are an `α < β` and a `φ_α : S → F_α` with `ι_α ∘ φ_α = φ`. -/
@[stacks 05N2]
theorem exists_factorization_of_mk_lt_cof {β : Ordinal.{u}}
    {F : {α : Ordinal.{u} // α < β} → Type u}
    {T : ∀ ⦃i j : {α : Ordinal.{u} // α < β}⦄, i ≤ j → Sort v}
    (f : ∀ i j (h : i ≤ j), T h)
    [∀ ⦃i j : {α : Ordinal.{u} // α < β}⦄ (h : i ≤ j), FunLike (T h) (F i) (F j)]
    [DirectedSystem F (f · · ·)]
    {S : Type u} (φ : S → DirectLimit F f)
    (hcof : Cardinal.mk S < β.cof) :
    ∃ (i : {α : Ordinal.{u} // α < β}) (φi : S → F i),
      (fun s => (⟦⟨i, φi s⟩⟧ : DirectLimit F f)) = φ := by
  have hrep (s : S) : ∃ i x, φ s = (⟦⟨i, x⟩⟧ : DirectLimit F f) :=
    DirectLimit.exists_eq_mk f (φ s)
  choose a t hat using hrep
  have hlt : (⨆ s, (a s).1) < β := Ordinal.iSup_lt_of_lt_cof hcof fun s => (a s).2
  have hle : ∀ s, a s ≤ (⟨_, hlt⟩ : {α : Ordinal.{u} // α < β}) := fun s => Ordinal.le_iSup _ s
  refine ⟨⟨_, hlt⟩, fun s => f _ _ (hle s) (t s), funext fun s => ?_⟩
  rw [DirectLimit.mk_apply]
  exact (hat s).symm

end Ordinal

end
