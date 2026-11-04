module

public import Mathlib.Algebra.Module.SnakeLemma
public import StacksFrontier.RingTheory.NaiveCotangent.Defs

/-!
# The six-term exact sequence of a degreewise exact triple of two-term complexes

Let `X ⟶ Y ⟶ Z` be chain maps of two-term complexes of `S`-modules, written

```
X :  X₁ --d--> X₀        Y :  Y₁ --d--> Y₀        Z :  Z₁ --d--> Z₀
```

with the degree-`1` term in cohomological degree `-1`.  Assume that the degree-`0` row
`0 → X₀ → Y₀ → Z₀ → 0` is short exact and that the degree-`1` row `X₁ → Y₁ → Z₁ → 0` is
exact.  Then the kernels and cokernels of the three differentials fit into a six-term
exact sequence

```
H⁻¹ X → H⁻¹ Y → H⁻¹ Z --δ--> H⁰ X → H⁰ Y → H⁰ Z → 0
```

where `H⁻¹ = ker d` is `NaiveCotangent.H₁` and `H⁰ = coker d` is `NaiveCotangent.H₀`.
Exactness at `H⁻¹ X` is not asserted, because the degree-`1` row is only right exact.

This is the homological step of **Stacks 0ALM**, the transitivity sequence for the
completed naive cotangent complex: there `X`, `Y`, `Z` are `NL^∧_{B/A} ⊗_B C`,
`NL^∧_{C/A}` and `NL^∧_{C/B}` for presentations `B = A⟨x⟩/J`, `C = B⟨y⟩/J'`,
`C = A⟨x, y⟩/K`, the degree-`0` row is `0 → ⨁ C dxᵢ → ⨁ C dxᵢ ⊕ ⨁ C dyⱼ → ⨁ C dyⱼ → 0`
and the degree-`1` row is `J/J² ⊗_B C → K/K² → J'/(J')² → 0`.  The source's proof is
"apply the snake lemma", and that is what this file does; it is stated for an arbitrary
degreewise exact triple of two-term complexes, so it is equally the homological step of
the uncompleted Stacks 00S2.

## Main results

* `NaiveCotangent.connecting`: the connecting map `δ : H⁻¹ Z → H⁰ X`.
* `NaiveCotangent.exists_connecting_zigZag` and `NaiveCotangent.connecting_apply`: a zig-zag
  `(y, x)` for a class in `H⁻¹ Z` always exists, and `δ` sends that class to the class of `x`.
  This pair determines `δ` completely, and it is what a comparison of `δ` with a differently
  constructed connecting map has to go through.
* `NaiveCotangent.exact_onH₁`, `NaiveCotangent.exact_onH₁_connecting`,
  `NaiveCotangent.exact_connecting_onH₀`, `NaiveCotangent.exact_onH₀`,
  `NaiveCotangent.surjective_onH₀`: exactness at each of the five interior nodes.
* `NaiveCotangent.exists_sixTerm_exact`: the five assertions packaged together.

## Implementation notes

The connecting map is Mathlib's `SnakeLemma.δ'` for the diagram whose top row is the
degree-`1` row, whose bottom row is the degree-`0` row and whose vertical maps are the
three differentials; the kernel and cokernel data it quantifies over are instantiated at
`Submodule.subtype (H₁ Z)` and `Submodule.mkQ (LinearMap.range X.d)`.  The two middle
exactness assertions are then `SnakeLemma.exact_δ'_right` and `SnakeLemma.exact_δ'_left`;
the three outer ones are elementary diagram chases and are proved here directly.

The two-term complexes, their chain maps and the induced maps on `ker` and `coker` are
the ones of `StacksFrontier/RingTheory/NaiveCotangent/Defs.lean`.

## References

* [Stacks Project, Tag 0ALM](https://stacks.math.columbia.edu/tag/0ALM)
* [Stacks Project, Tag 00S2](https://stacks.math.columbia.edu/tag/00S2)
-/

@[expose] public section

namespace NaiveCotangent

open Function

variable {S : Type*} [CommRing S] {X Y Z : TwoTerm S}

/-- The defining square of a chain map, read on elements. -/
@[simp] public theorem ChainMap.comm_apply (α : ChainMap X Y) (x : X.X₁) :
    Y.d (α.f₁ x) = α.f₀ (X.d x) := by
  simpa using LinearMap.congr_fun α.comm x

/-- The map induced on `ker d` is the restriction of the degree-`1` component. -/
@[simp] public theorem ChainMap.coe_onH₁ (α : ChainMap X Y) (x : H₁ X) :
    ((α.onH₁ x : H₁ Y) : Y.X₁) = α.f₁ (x : X.X₁) := rfl

/-- The map induced on `coker d` is the one induced by the degree-`0` component. -/
@[simp] public theorem ChainMap.onH₀_mkQ (α : ChainMap X Y) (x : X.X₀) :
    α.onH₀ (Submodule.mkQ (LinearMap.range X.d) x) =
      Submodule.mkQ (LinearMap.range Y.d) (α.f₀ x) := rfl

/-- The inclusion of `ker d` into the degree-`1` term is natural in the chain map. -/
public theorem subtype_comp_onH₁ (α : ChainMap X Y) :
    α.f₁.comp (Submodule.subtype (H₁ X)) = (Submodule.subtype (H₁ Y)).comp α.onH₁ :=
  LinearMap.ext fun _ => rfl

/-- The projection of the degree-`0` term onto `coker d` is natural in the chain map. -/
public theorem onH₀_comp_mkQ (α : ChainMap X Y) :
    α.onH₀.comp (Submodule.mkQ (LinearMap.range X.d)) =
      (Submodule.mkQ (LinearMap.range Y.d)).comp α.f₀ :=
  LinearMap.ext fun _ => rfl

/-- Exactness at `H⁻¹ Y`: if the degree-`0` map `X₀ → Y₀` is injective and the degree-`1`
row is exact at `Y₁`, then `ker d_X → ker d_Y → ker d_Z` is exact. -/
public theorem exact_onH₁ (α : ChainMap X Y) (β : ChainMap Y Z)
    (hα₀ : Injective α.f₀) (h₁ : Exact α.f₁ β.f₁) :
    Exact α.onH₁ β.onH₁ := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (h₁ (y : Y.X₁)).mp (congrArg Subtype.val hy)
    have hxd : X.d x = 0 := by
      refine hα₀ ?_
      rw [map_zero, ← ChainMap.comm_apply α x, hx]
      exact y.2
    exact ⟨⟨x, hxd⟩, Subtype.ext hx⟩
  · rintro ⟨x, rfl⟩
    exact Subtype.ext ((h₁ (α.f₁ (x : X.X₁))).mpr ⟨(x : X.X₁), rfl⟩)

/-- Exactness at `H⁰ Y`: if the degree-`0` row is exact at `Y₀` and the degree-`1` map
`Y₁ → Z₁` is surjective, then `coker d_X → coker d_Y → coker d_Z` is exact. -/
public theorem exact_onH₀ (α : ChainMap X Y) (β : ChainMap Y Z)
    (h₀ : Exact α.f₀ β.f₀) (hβ₁ : Surjective β.f₁) :
    Exact α.onH₀ β.onH₀ := by
  intro ybar
  constructor
  · intro hy
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range Y.d) ybar
    rw [ChainMap.onH₀_mkQ, ← LinearMap.mem_ker, Submodule.ker_mkQ] at hy
    obtain ⟨z₁, hz₁⟩ := hy
    obtain ⟨y₁, hy₁⟩ := hβ₁ z₁
    have hsub : β.f₀ (y - Y.d y₁) = 0 := by
      rw [map_sub, ← ChainMap.comm_apply β y₁, hy₁, hz₁, sub_self]
    obtain ⟨x, hx⟩ := (h₀ (y - Y.d y₁)).mp hsub
    refine ⟨Submodule.mkQ (LinearMap.range X.d) x, ?_⟩
    rw [ChainMap.onH₀_mkQ]
    refine (Submodule.Quotient.eq _).mpr ?_
    rw [hx, sub_sub_cancel_left]
    exact Submodule.neg_mem _ ⟨y₁, rfl⟩
  · rintro ⟨xbar, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range X.d) xbar
    rw [ChainMap.onH₀_mkQ, ChainMap.onH₀_mkQ,
      (h₀ (α.f₀ x)).mpr ⟨x, rfl⟩, map_zero]

/-- Exactness at `H⁰ Z`: a surjection in degree `0` induces a surjection on cokernels. -/
public theorem surjective_onH₀ (β : ChainMap Y Z) (hβ₀ : Surjective β.f₀) :
    Surjective β.onH₀ := by
  intro zbar
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range Z.d) zbar
  obtain ⟨y, rfl⟩ := hβ₀ z
  exact ⟨Submodule.mkQ (LinearMap.range Y.d) y, ChainMap.onH₀_mkQ β y⟩

/-- The connecting map `δ : H⁻¹ Z → H⁰ X` of the snake lemma, for a triple of two-term
complexes whose degree-`0` row is left exact and whose degree-`1` row is right exact. -/
public noncomputable def connecting (α : ChainMap X Y) (β : ChainMap Y Z)
    (hα₀ : Injective α.f₀) (h₀ : Exact α.f₀ β.f₀)
    (hβ₁ : Surjective β.f₁) (h₁ : Exact α.f₁ β.f₁) :
    H₁ Z →ₗ[S] H₀ X :=
  SnakeLemma.δ' X.d Y.d Z.d α.f₁ β.f₁ h₁ α.f₀ β.f₀ h₀ α.comm.symm β.comm.symm
    (Submodule.subtype (H₁ Z)) (LinearMap.exact_subtype_ker_map Z.d)
    (Submodule.mkQ (LinearMap.range X.d)) (LinearMap.exact_map_mkQ_range X.d) hβ₁ hα₀

/-- **A zig-zag for a class in `H⁻¹ Z` exists.**  Every element `z` of `H⁻¹ Z = ker d_Z` lifts
along the degree-`1` map `Y₁ → Z₁` to a `y`, and the image of that lift under `d_Y` comes from
the degree-`0` term of `X`.  These are the two choices the snake lemma makes, and the pair
`(y, x)` is what `NaiveCotangent.connecting_apply` consumes. -/
public theorem exists_connecting_zigZag (α : ChainMap X Y) (β : ChainMap Y Z)
    (h₀ : Exact α.f₀ β.f₀) (hβ₁ : Surjective β.f₁) (z : H₁ Z) :
    ∃ (y : Y.X₁) (x : X.X₀), β.f₁ y = (z : Z.X₁) ∧ α.f₀ x = Y.d y := by
  obtain ⟨y, hy⟩ := hβ₁ (z : Z.X₁)
  have hz : β.f₀ (Y.d y) = 0 := by
    rw [← ChainMap.comm_apply β y, hy]
    exact z.2
  obtain ⟨x, hx⟩ := (h₀ (Y.d y)).mp hz
  exact ⟨y, x, hy, hx⟩

/-- **The value of the connecting map on a zig-zag.**  If `y` lifts `z : H⁻¹ Z = ker d_Z` along
the degree-`1` map `Y₁ → Z₁` and `x` is a preimage of `d_Y y` along the degree-`0` map
`X₀ → Y₀`, then the connecting map sends `z` to the class of `x` in `H⁰ X = coker d_X`.

This is the snake lemma's own characterisation `SnakeLemma.δ'_eq` of the connecting map, read at
the kernel and cokernel data that `NaiveCotangent.connecting` instantiates.  It is the handle any
comparison of this connecting map with a differently constructed one has to go through: the two
choices `y` and `x` are arbitrary, so the identity determines `δ` completely, and
`NaiveCotangent.exists_connecting_zigZag` says a zig-zag always exists. -/
public theorem connecting_apply (α : ChainMap X Y) (β : ChainMap Y Z)
    (hα₀ : Injective α.f₀) (h₀ : Exact α.f₀ β.f₀)
    (hβ₁ : Surjective β.f₁) (h₁ : Exact α.f₁ β.f₁)
    (z : H₁ Z) (y : Y.X₁) (hy : β.f₁ y = (z : Z.X₁)) (x : X.X₀) (hx : α.f₀ x = Y.d y) :
    connecting α β hα₀ h₀ hβ₁ h₁ z = Submodule.mkQ (LinearMap.range X.d) x :=
  SnakeLemma.δ'_eq X.d Y.d Z.d α.f₁ β.f₁ h₁ α.f₀ β.f₀ h₀ α.comm.symm β.comm.symm
    (Submodule.subtype (H₁ Z)) (LinearMap.exact_subtype_ker_map Z.d)
    (Submodule.mkQ (LinearMap.range X.d)) (LinearMap.exact_map_mkQ_range X.d) hβ₁ hα₀
    z y hy x hx

/-- Exactness at `H⁻¹ Z`: the image of `H⁻¹ Y → H⁻¹ Z` is the kernel of the connecting map. -/
public theorem exact_onH₁_connecting (α : ChainMap X Y) (β : ChainMap Y Z)
    (hα₀ : Injective α.f₀) (h₀ : Exact α.f₀ β.f₀)
    (hβ₁ : Surjective β.f₁) (h₁ : Exact α.f₁ β.f₁) :
    Exact β.onH₁ (connecting α β hα₀ h₀ hβ₁ h₁) :=
  SnakeLemma.exact_δ'_right (i₁ := X.d) (i₂ := Y.d) (i₃ := Z.d)
    (f₁ := α.f₁) (f₂ := β.f₁) (hf := h₁) (g₁ := α.f₀) (g₂ := β.f₀) (hg := h₀)
    (h₁ := α.comm.symm) (h₂ := β.comm.symm)
    (ι₂ := Submodule.subtype (H₁ Y)) (hι₂ := LinearMap.exact_subtype_ker_map Y.d)
    (ι₃ := Submodule.subtype (H₁ Z)) (hι₃ := LinearMap.exact_subtype_ker_map Z.d)
    (π₁ := Submodule.mkQ (LinearMap.range X.d)) (hπ₁ := LinearMap.exact_map_mkQ_range X.d)
    hβ₁ hα₀ β.onH₁ (subtype_comp_onH₁ β) Subtype.val_injective

/-- Exactness at `H⁰ X`: the image of the connecting map is the kernel of `H⁰ X → H⁰ Y`. -/
public theorem exact_connecting_onH₀ (α : ChainMap X Y) (β : ChainMap Y Z)
    (hα₀ : Injective α.f₀) (h₀ : Exact α.f₀ β.f₀)
    (hβ₁ : Surjective β.f₁) (h₁ : Exact α.f₁ β.f₁) :
    Exact (connecting α β hα₀ h₀ hβ₁ h₁) α.onH₀ :=
  SnakeLemma.exact_δ'_left (i₁ := X.d) (i₂ := Y.d) (i₃ := Z.d)
    (f₁ := α.f₁) (f₂ := β.f₁) (hf := h₁) (g₁ := α.f₀) (g₂ := β.f₀) (hg := h₀)
    (h₁ := α.comm.symm) (h₂ := β.comm.symm)
    (ι₃ := Submodule.subtype (H₁ Z)) (hι₃ := LinearMap.exact_subtype_ker_map Z.d)
    (π₁ := Submodule.mkQ (LinearMap.range X.d)) (hπ₁ := LinearMap.exact_map_mkQ_range X.d)
    (π₂ := Submodule.mkQ (LinearMap.range Y.d)) (hπ₂ := LinearMap.exact_map_mkQ_range Y.d)
    hβ₁ hα₀ α.onH₀ (onH₀_comp_mkQ α) (Submodule.mkQ_surjective _)

/-- The six-term exact sequence
`H⁻¹ X → H⁻¹ Y → H⁻¹ Z → H⁰ X → H⁰ Y → H⁰ Z → 0`
attached to a triple of two-term complexes whose degree-`0` row is short exact and whose
degree-`1` row is right exact.  This is the homological content of **Stacks 0ALM**. -/
public theorem exists_sixTerm_exact (α : ChainMap X Y) (β : ChainMap Y Z)
    (hα₀ : Injective α.f₀) (h₀ : Exact α.f₀ β.f₀) (hβ₀ : Surjective β.f₀)
    (hβ₁ : Surjective β.f₁) (h₁ : Exact α.f₁ β.f₁) :
    ∃ δ : H₁ Z →ₗ[S] H₀ X,
      Exact α.onH₁ β.onH₁ ∧ Exact β.onH₁ δ ∧ Exact δ α.onH₀ ∧
        Exact α.onH₀ β.onH₀ ∧ Surjective β.onH₀ :=
  ⟨connecting α β hα₀ h₀ hβ₁ h₁, exact_onH₁ α β hα₀ h₁,
    exact_onH₁_connecting α β hα₀ h₀ hβ₁ h₁, exact_connecting_onH₀ α β hα₀ h₀ hβ₁ h₁,
    exact_onH₀ α β h₀ hβ₁, surjective_onH₀ β hβ₀⟩

end NaiveCotangent

end
