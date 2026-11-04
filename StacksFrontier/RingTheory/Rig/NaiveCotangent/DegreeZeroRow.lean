module

public import StacksFrontier.RingTheory.Rig.NaiveCotangent.SixTerm

/-!
# The degree-`0` row of Stacks 0ALM, and the six-term sequence it feeds

**Stacks 0ALM** derives its six-term exact sequence from a commutative diagram with exact
rows

```
0 ⟶ ⨁ᵢ C dxᵢ ⟶ ⨁ᵢ C dxᵢ ⊕ ⨁ⱼ C dyⱼ ⟶ ⨁ⱼ C dyⱼ ⟶ 0
      ↑                 ↑                ↑
    J/J² ⊗_B C  ⟶     K/K²      ⟶    J'/(J')²     ⟶ 0
```

for presentations `B = A⟨x₁, …, x_r⟩/J`, `C = B⟨y₁, …, y_s⟩/J'` and the combined
presentation `C = A⟨x, y⟩/K`, and then applies the snake lemma.  The snake step is
`NaiveCotangent.exists_sixTerm_exact`.  This file discharges the **degree-`0` row**: for the
combined presentation the three degree-`0` terms are the finite free modules `⨁_{i<r} C`,
`⨁_{i<r+s} C` and `⨁_{j<s} C`, and the row is the split short exact sequence that extends a
tuple by zeros and reads off the last `s` coordinates.

The row is proved for arbitrary `r` and `s`, independently of the combined presentation.

## Main definitions

* `NaiveCotangent.finInl`: `⨁_{i<r} C → ⨁_{i<r+s} C`, extension by zero.
* `NaiveCotangent.finProj`: `⨁_{i<r+s} C → ⨁_{j<s} C`, the last `s` coordinates.
* `NaiveCotangent.TwoTerm.ofFree`: the two-term complex `M --d--> ⨁_{i<r} C`, the shape every
  naive cotangent complex of a presentation by `r` variables has.
* `NaiveCotangent.chainMapInl`, `NaiveCotangent.chainMapProj`: the two chain maps of the
  diagram, given the two commuting squares.

## Main results

* `NaiveCotangent.injective_finInl`, `NaiveCotangent.surjective_finProj`,
  `NaiveCotangent.exact_finInl_finProj`: the degree-`0` row is short exact.
* `NaiveCotangent.exists_sixTerm_exact_of_finAppend`: **the six-term exact sequence of
  Stacks 0ALM, with its degree-`0` row discharged** — it remains to supply the two
  commuting squares and the right exactness of the degree-`1` row.

## Implementation notes

The splitting is written with `Fin.append` and `Fin.natAdd` rather than through a linear
equivalence `(Fin (r+s) → C) ≃ₗ (Fin r → C) × (Fin s → C)`, because the degree-`0` terms of
the naive cotangent complexes are literally `Fin n → C` and an equivalence would have to be
transported across the two squares at every use.  `Fin.addCases` reduces every proof to the
two `Fin.append_left` / `Fin.append_right` simp lemmas.

## References

* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
* [Stacks Project, Tag 07JW](https://stacks.math.columbia.edu/tag/07JW)
-/

@[expose] public section

namespace NaiveCotangent

open Function

section Row

variable (C : Type*) [CommRing C] (r s : ℕ)

/-- The inclusion `⨁_{i<r} C → ⨁_{i<r+s} C` of the first `r` coordinates, extending a tuple
by zeros.  In Stacks 0ALM this is `⨁ᵢ C dxᵢ → ⨁ᵢ C dxᵢ ⊕ ⨁ⱼ C dyⱼ`. -/
public def finInl : (Fin r → C) →ₗ[C] (Fin (r + s) → C) where
  toFun v := Fin.append v 0
  map_add' v w := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  map_smul' c v := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

/-- The projection `⨁_{i<r+s} C → ⨁_{j<s} C` onto the last `s` coordinates.  In Stacks 0ALM
this is `⨁ᵢ C dxᵢ ⊕ ⨁ⱼ C dyⱼ → ⨁ⱼ C dyⱼ`. -/
public def finProj : (Fin (r + s) → C) →ₗ[C] (Fin s → C) where
  toFun w j := w (Fin.natAdd r j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Extension by zero is the identity on the first `r` coordinates. -/
@[simp] public theorem finInl_apply_castAdd (v : Fin r → C) (i : Fin r) :
    finInl C r s v (Fin.castAdd s i) = v i :=
  Fin.append_left _ _ _

/-- Extension by zero vanishes on the last `s` coordinates. -/
@[simp] public theorem finInl_apply_natAdd (v : Fin r → C) (j : Fin s) :
    finInl C r s v (Fin.natAdd r j) = 0 :=
  Fin.append_right _ _ _

/-- The `j`-th coordinate of `finProj C r s w` is the `(r + j)`-th coordinate of `w`. -/
@[simp] public theorem finProj_apply (w : Fin (r + s) → C) (j : Fin s) :
    finProj C r s w j = w (Fin.natAdd r j) :=
  rfl

/-- Extension by zero is injective. -/
public theorem injective_finInl : Injective (finInl C r s) := by
  intro v w h
  funext i
  simpa using congrFun h (Fin.castAdd s i)

/-- Reading off the last `s` coordinates is surjective. -/
public theorem surjective_finProj : Surjective (finProj C r s) := by
  intro u
  refine ⟨Fin.append 0 u, ?_⟩
  funext j
  simp [finProj]

/-- The degree-`0` row `0 → ⨁_{i<r} C → ⨁_{i<r+s} C → ⨁_{j<s} C → 0` is exact in the
middle: a tuple whose last `s` coordinates vanish is the extension by zero of its first `r`
coordinates. -/
public theorem exact_finInl_finProj : Exact (finInl C r s) (finProj C r s) := by
  refine fun w => ⟨fun hw => ⟨fun i => w (Fin.castAdd s i), funext fun i => ?_⟩, ?_⟩
  · exact Fin.addCases (fun j => by simp) (fun j => by simpa using (congrFun hw j).symm) i
  · rintro ⟨v, rfl⟩
    funext j
    simp

end Row

/-! ## Two-term complexes with finite free degree-`0` term -/

namespace TwoTerm

/-- The two-term complex `M --d--> ⨁_{i<r} C`.  Every naive cotangent complex of a
presentation by `r` variables has this shape, with `M` the conormal module. -/
public def ofFree {C : Type*} [CommRing C] {M : Type*} [AddCommGroup M] [Module C M] {r : ℕ}
    (d : M →ₗ[C] (Fin r → C)) : TwoTerm C where
  X₁ := M
  X₀ := Fin r → C
  d := d

/-- The differential of `TwoTerm.ofFree d` is `d`. -/
@[simp] public theorem ofFree_d {C : Type*} [CommRing C] {M : Type*} [AddCommGroup M]
    [Module C M] {r : ℕ} (d : M →ₗ[C] (Fin r → C)) : (ofFree d).d = d := rfl

end TwoTerm

section Diagram

variable {C : Type*} [CommRing C] {r s : ℕ} {M₁ M₂ M₃ : Type*}
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module C M₁] [Module C M₂] [Module C M₃]
  {dX : M₁ →ₗ[C] (Fin r → C)} {dY : M₂ →ₗ[C] (Fin (r + s) → C)} {dZ : M₃ →ₗ[C] (Fin s → C)}

/-- The left-hand chain map of the diagram of Stacks 0ALM: the degree-`1` map `a` together
with extension by zero in degree `0`. -/
public def chainMapInl (a : M₁ →ₗ[C] M₂) (hα : dY ∘ₗ a = (finInl C r s) ∘ₗ dX) :
    ChainMap (TwoTerm.ofFree dX) (TwoTerm.ofFree dY) where
  f₁ := a
  f₀ := finInl C r s
  comm := hα

/-- The right-hand chain map of the diagram of Stacks 0ALM: the degree-`1` map `b` together
with the projection onto the last `s` coordinates in degree `0`. -/
public def chainMapProj (b : M₂ →ₗ[C] M₃) (hβ : dZ ∘ₗ b = (finProj C r s) ∘ₗ dY) :
    ChainMap (TwoTerm.ofFree dY) (TwoTerm.ofFree dZ) where
  f₁ := b
  f₀ := finProj C r s
  comm := hβ

/-- The degree-`0` component of `chainMapInl a hα` is `finInl C r s`. -/
@[simp] public theorem chainMapInl_f₀ (a : M₁ →ₗ[C] M₂)
    (hα : dY ∘ₗ a = (finInl C r s) ∘ₗ dX) :
    (chainMapInl a hα).f₀ = finInl C r s := rfl

/-- The degree-`0` component of `chainMapProj b hβ` is `finProj C r s`. -/
@[simp] public theorem chainMapProj_f₀ (b : M₂ →ₗ[C] M₃)
    (hβ : dZ ∘ₗ b = (finProj C r s) ∘ₗ dY) :
    (chainMapProj b hβ).f₀ = finProj C r s := rfl

/-- **The six-term exact sequence of Stacks 0ALM, with its degree-`0` row discharged.**

Let `C` be a commutative ring and let

```
X :  M₁ --dX--> ⨁_{i<r} C      Y :  M₂ --dY--> ⨁_{i<r+s} C      Z :  M₃ --dZ--> ⨁_{j<s} C
```

be two-term complexes of `C`-modules whose degree-`0` terms are the finite free modules of
the combined presentation, let `a : M₁ → M₂` and `b : M₂ → M₃` make the two squares over
`finInl` and `finProj` commute, and suppose the degree-`1` row `M₁ → M₂ → M₃ → 0` is exact.
Then there is a six-term exact sequence

```
H⁻¹ X → H⁻¹ Y → H⁻¹ Z --δ--> H⁰ X → H⁰ Y → H⁰ Z → 0.
```

Applied to `X = NL^∧_{B/A} ⊗_B C`, `Y = NL^∧_{C/A}`, `Z = NL^∧_{C/B}` for presentations
`B = A⟨x⟩/J`, `C = B⟨y⟩/J'` and the combined presentation `C = A⟨x, y⟩/K`, this is **Stacks
0ALM**: the degree-`0` row is exactly the split row proved above, so all that is left to
supply is the combined presentation and the right exactness of
`J/J² ⊗_B C → K/K² → J'/(J')² → 0`. -/
public theorem exists_sixTerm_exact_of_finAppend (a : M₁ →ₗ[C] M₂) (b : M₂ →ₗ[C] M₃)
    (hα : dY ∘ₗ a = (finInl C r s) ∘ₗ dX) (hβ : dZ ∘ₗ b = (finProj C r s) ∘ₗ dY)
    (hb : Surjective b) (hab : Exact a b) :
    ∃ δ : H₁ (TwoTerm.ofFree dZ) →ₗ[C] H₀ (TwoTerm.ofFree dX),
      Exact (chainMapInl a hα).onH₁ (chainMapProj b hβ).onH₁ ∧
        Exact (chainMapProj b hβ).onH₁ δ ∧ Exact δ (chainMapInl a hα).onH₀ ∧
          Exact (chainMapInl a hα).onH₀ (chainMapProj b hβ).onH₀ ∧
            Surjective (chainMapProj b hβ).onH₀ :=
  exists_sixTerm_exact (chainMapInl a hα) (chainMapProj b hβ) (injective_finInl C r s)
    (exact_finInl_finProj C r s) (surjective_finProj C r s) hb hab

end Diagram

end NaiveCotangent

end
