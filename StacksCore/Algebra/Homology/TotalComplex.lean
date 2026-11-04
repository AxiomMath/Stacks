module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.TotalComplex
public import StacksCore.CategoryTheory.GradedObject
import StacksCore.Tactic.StacksAttribute

/-! ## The total complex of a double complex

Stacks 012Z defines the associated simple complex `sA^• = Tot(A^{•, •})` of a double complex
`A^{•, •}` in an additive category by `sA^n = ⨁_{n = p + q} A^{p, q}` "(if it exists)", with
differential `d^n = ∑_{n = p + q} (d₁^{p, q} + (-1)^p d₂^{p, q})`.

Mathlib's `HomologicalComplex₂.total K c₁₂` is this for a bicomplex over any two complex shapes
`c₁`, `c₂` and any target shape `c₁₂` carrying a `TotalComplexShape c₁ c₂ c₁₂`, over any
preadditive category. The tag's "if it exists" is the hypothesis `K.HasTotal c₁₂`: for every `n`
the coproduct of the summands `(K.X p).X q` over the pairs with `π (p, q) = n` exists, and that
coproduct is the degree-`n` term. The differential is `total_d : d = D₁ + D₂`, where by `d₁_eq`
and `d₂_eq` the two pieces act on the summand `A^{p, q}` as `ε₁ • d₁^{p, q}` and `ε₂ • d₂^{p, q}`
for the signs of the `TotalComplexShape`. For cochain complexes indexed by `ℤ` the signs are
`ε₁ = 1` and `ε₂ (p, q) = (-1)^p` — see `StacksCore.Algebra.Homology.ComplexShapeSigns` — so the
differential is the tag's `d₁ + (-1)^p d₂` exactly; `ιTotal_d_up_ℤ` below states that summand-wise.
`totalFunctor` is `Tot` as a functor.

The remark after the definition gives two existence criteria. Countable direct sums: with
`HasCountableCoproducts C` and countable index types, instance search finds `K.HasTotal c₁₂` on
its own; the Mathlib instance doing the work is attributed in
`StacksCore.CategoryTheory.Limits.Shapes.Countable`. Finitely many nonzero `A^{p, n - p}` for each
`n`: `hasTotal_of_finite`, which needs finite coproducts only.

`total.map` is additive in the morphism, and `totalFunctor` is an additive functor. Mathlib has
only `map_id` and `map_comp`; the additivity is what lets a complex of bicomplexes be integrated
termwise into a bicomplex, see `HomologicalComplex₃.int₂₃`.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape

add_to_stacks 012Z "for any shapes with a `TotalComplexShape`, over any preadditive category"
  HomologicalComplex₂.total
add_to_stacks 012Z "the tag's \"if it exists\": each `⨁_{π (p, q) = n} A^{p, q}` exists"
  HomologicalComplex₂.HasTotal
add_to_stacks 012Z "the differential is `D₁ + D₂`" HomologicalComplex₂.total_d
add_to_stacks 012Z "`D₁` acts on the summand `A^{p, q}` by `ε₁ • d₁^{p, q}`"
  HomologicalComplex₂.d₁_eq
add_to_stacks 012Z "`D₂` acts on the summand `A^{p, q}` by `ε₂ • d₂^{p, q}`"
  HomologicalComplex₂.d₂_eq
add_to_stacks 012Z "`Tot` as a functor" HomologicalComplex₂.totalFunctor

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C]

section existence

variable {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

/-- **Stacks 012Z**, the existence remark: `Tot(A)` exists when finite coproducts do and each
antidiagonal `{(p, q) | π (p, q) = n}` carries only finitely many nonzero terms. -/
@[stacks 012Z "existence: finite coproducts, finitely many nonzero `A^{p, n - p}` for each `n`"]
theorem hasTotal_of_finite (K : HomologicalComplex₂ C c₁ c₂) (c₁₂ : ComplexShape I₁₂)
    [TotalComplexShape c₁ c₂ c₁₂] [HasFiniteCoproducts C]
    (h : ∀ n, {pq : I₁ × I₂ | π c₁ c₂ c₁₂ pq = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite) :
    K.HasTotal c₁₂ :=
  GradedObject.hasMap_of_finite _ _ h

end existence

section additive

variable {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (c₁₂ : ComplexShape I₁₂) [DecidableEq I₁₂] [TotalComplexShape c₁ c₂ c₁₂]

namespace total

variable {K L : HomologicalComplex₂ C c₁ c₂} (φ φ' : K ⟶ L) [K.HasTotal c₁₂] [L.HasTotal c₁₂]

@[simp]
lemma map_add : map (φ + φ') c₁₂ = map φ c₁₂ + map φ' c₁₂ := by
  ext
  simp

@[simp]
lemma map_neg : map (-φ) c₁₂ = -map φ c₁₂ := by
  ext
  simp

@[simp]
lemma map_sub : map (φ - φ') c₁₂ = map φ c₁₂ - map φ' c₁₂ := by
  ext
  simp

variable (K L) in
@[simp]
lemma map_zero : map (0 : K ⟶ L) c₁₂ = 0 := by
  ext
  simp

end total

variable (C c₁ c₂) [∀ (K : HomologicalComplex₂ C c₁ c₂), K.HasTotal c₁₂]

instance : (totalFunctor C c₁ c₂ c₁₂).Additive where
  map_add := total.map_add _ _ _

end additive

variable (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]

/-- **Stacks 012Z**, the differential summand-wise for a `ℤ`-cochain double complex: on the
summand `A^{p, q}` of `Tot(A)^n` it is `d₁^{p, q} + (-1)^p d₂^{p, q}`. -/
@[stacks 012Z "the tag's formula `d₁ + (-1)^p d₂` on each summand, for `ℤ`-cochain complexes",
  sga "4 Vbis 2.3.2" "differential formula", sga "4 XVII 1.1.4" "double complex, ⊕ case"]
theorem ιTotal_d_up_ℤ (p q n : ℤ) (h : p + q = n) :
    K.ιTotal (up ℤ) p q n h ≫ (K.total (up ℤ)).d n (n + 1) =
      (K.d p (p + 1)).f q ≫ K.ιTotal (up ℤ) (p + 1) q (n + 1) (by dsimp; lia) +
        p.negOnePow •
          ((K.X p).d q (q + 1) ≫ K.ιTotal (up ℤ) p (q + 1) (n + 1) (by dsimp; lia)) := by
  rw [K.total_d, Preadditive.comp_add, K.ι_D₁, K.ι_D₂,
    K.d₁_eq (up ℤ) (i₁ := p) (i₁' := p + 1) rfl q (n + 1) (by dsimp; lia),
    K.d₂_eq (up ℤ) p (i₂ := q) (i₂' := q + 1) rfl (n + 1) (by dsimp; lia)]
  simp

end HomologicalComplex₂
