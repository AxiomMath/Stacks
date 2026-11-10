module

public import Mathlib.Algebra.Polynomial.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwist

/-!
# Recognising a family of tensor powers from invertibility

`Stacks.GradedRing.IsTensorPowerFamily 𝓛` asks of a family `𝓛 : ℕ → Submodule R T` of
`R`-submodules of an `R`-algebra `T` that `𝓛 0 = R`, that `𝓛 i * 𝓛 j = 𝓛 (i + j)`, and that
multiplication `𝓛 i ⊗_R 𝓛 j → T` be injective — so that the product submodule *is* the tensor
product of the factors.

The last field is the only one with content, and this file supplies it from invertibility of the
members alone. Multiplication `𝓛 i ⊗_R 𝓛 j → ↥(𝓛 i * 𝓛 j)` is surjective for free
(`Submodule.mulMap'_surjective`: the product submodule is spanned by products). A surjection
between invertible modules is bijective (`Module.Invertible.bijective_of_surjective`), and
`𝓛 i ⊗_R 𝓛 j` is invertible when both factors are. So once `𝓛 i * 𝓛 j = 𝓛 (i + j)` is known and
every `𝓛 n` is invertible, injectivity is automatic.

That is `injective_mulMap_of_invertible`, and `isTensorPowerFamily_of_invertible` assembles the
class from it. The point is that **no coherence isomorphism is traversed**: a transport of the
tensor-sections comparison across the multiplication `ℒ^{⊗ i} ⊗ ℒ^{⊗ j} ≅ ℒ^{⊗ (i + j)}` would
have to match two spellings of a threefold tensor product, whereas invertibility is a property of
each member separately and the product submodule's spanning property is definitional.

For the geometric application `T` is a ring of sections over an open of the base and `𝓛 n` the
sections of the `n`-th tensor power of an invertible module; over an open on which that module is
*trivialized* the family is the family of `R`-multiples of the powers of a single element, and
`isTensorPowerFamily_span_pow` handles it with no hypothesis beyond non-torsionness of that
element. `Polynomial.isTensorPowerFamily_span_X_pow` is the universal such family, exhibiting a
term of the class.

## Main results

* `Stacks.GradedRing.injective_mulMap_of_invertible`: **the transport** — for invertible
  submodules with invertible product, multiplication from the tensor product is injective.
* `Stacks.GradedRing.isTensorPowerFamily_of_invertible`: a family with `𝓛 0 = R`, additive
  degrees and invertible members is a family of tensor powers.
* `Stacks.GradedRing.isTensorPowerFamily_pow`: the powers of a single submodule, all invertible,
  are such a family.
* `Stacks.GradedRing.invertible_span_singleton`: the `R`-multiples of a non-torsion element form
  an invertible submodule.
* `Stacks.GradedRing.isTensorPowerFamily_span_pow`: **the trivialized family** `𝓛 n = R · t ^ n`
  attached to an element `t` no power of which is torsion.
* `Stacks.GradedRing.Polynomial.isTensorPowerFamily_span_X_pow`: the family `R · X ^ n` in
  `R[X]`, a term of `Stacks.GradedRing.IsTensorPowerFamily`.

## References

* [Stacks Project, Tag 02NB](https://stacks.math.columbia.edu/tag/02NB)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

universe u

open scoped TensorProduct

namespace Stacks.GradedRing

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]

/-! ### The transport -/

/-- The corestriction of multiplication to the product submodule is the multiplication map, read
in `T`. Pinned once so that the coercion is never unfolded again below. -/
theorem coe_mulMap' (M N : Submodule R T) (x : M ⊗[R] N) :
    ((Submodule.mulMap' M N x : ↥(M * N)) : T) = Submodule.mulMap M N x := rfl

/-- **Multiplication realizes the tensor product of two invertible submodules.** If `M` and `N`
are invertible `R`-submodules of `T` and their product `M * N` is invertible too, then
`M ⊗_R N → T` is injective.

This is the field `Stacks.GradedRing.IsTensorPowerFamily.mulMap_injective`, and it is the one
step of that class with mathematical content. Surjectivity of `Submodule.mulMap'` is free, and a
surjection between invertible modules is bijective. -/
theorem injective_mulMap_of_invertible (M N : Submodule R T) [Module.Invertible R M]
    [Module.Invertible R N] [Module.Invertible R ↥(M * N)] :
    Function.Injective (Submodule.mulMap M N) := by
  have hbij : Function.Bijective (Submodule.mulMap' M N) :=
    Module.Invertible.bijective_of_surjective (Submodule.mulMap'_surjective M N)
  intro x y hxy
  exact hbij.injective (Subtype.ext (by rw [coe_mulMap', coe_mulMap', hxy]))

/-- **A family of invertible submodules whose degrees add is a family of tensor powers.** -/
theorem isTensorPowerFamily_of_invertible (𝓛 : ℕ → Submodule R T)
    (hinj : Function.Injective (algebraMap R T)) (h0 : 𝓛 0 = 1)
    (hmul : ∀ i j : ℕ, 𝓛 i * 𝓛 j = 𝓛 (i + j))
    (hinv : ∀ n : ℕ, Module.Invertible R ↥(𝓛 n)) :
    IsTensorPowerFamily 𝓛 where
  algebraMap_injective := hinj
  degree_zero := h0
  mul_eq := hmul
  mulMap_injective i j := by
    have := hinv i
    have := hinv j
    have hij : Module.Invertible R ↥(𝓛 i * 𝓛 j) := by
      rw [hmul i j]; exact hinv (i + j)
    exact injective_mulMap_of_invertible (𝓛 i) (𝓛 j)

/-- **The powers of an invertible submodule are a family of tensor powers.** The additivity of
degrees is `pow_add`, so nothing is left to check beyond invertibility. -/
theorem isTensorPowerFamily_pow (L : Submodule R T)
    (hinj : Function.Injective (algebraMap R T))
    (hinv : ∀ n : ℕ, Module.Invertible R ↥(L ^ n)) :
    IsTensorPowerFamily (fun n ↦ L ^ n) :=
  isTensorPowerFamily_of_invertible _ hinj (pow_zero L) (fun i j ↦ (pow_add L i j).symm) hinv

/-! ### The trivialized family -/

/-- Scalar multiplication by a non-torsion element is injective. Pinned once; every coordinate
computation below is an application of it. -/
theorem injective_smul_of_ne_zero {t : T} (ht : ∀ r : R, r • t = 0 → r = 0) :
    Function.Injective (fun r : R ↦ r • t) := by
  intro a b hab
  exact sub_eq_zero.mp (ht _ (by rw [sub_smul, show a • t = b • t from hab, sub_self]))

/-- **The `R`-multiples of a non-torsion element are free of rank one on it.** -/
theorem bijective_toSpanSingleton_span {t : T} (ht : ∀ r : R, r • t = 0 → r = 0) :
    Function.Bijective (LinearMap.toSpanSingleton R ↥(Submodule.span R {t})
      ⟨t, Submodule.mem_span_singleton_self t⟩) := by
  constructor
  · exact fun r r' hrr' ↦ injective_smul_of_ne_zero ht (congrArg Subtype.val hrr')
  · intro x
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp x.2
    exact ⟨r, Subtype.ext hr⟩

/-- **The `R`-multiples of a non-torsion element form an invertible submodule**: it is free of
rank one on that element. -/
theorem invertible_span_singleton {t : T} (ht : ∀ r : R, r • t = 0 → r = 0) :
    Module.Invertible R ↥(Submodule.span R {t}) :=
  invertible_of_bijective_toSpanSingleton (bijective_toSpanSingleton_span ht)

/-- **The trivialized family of tensor powers.** If no power of `t` is a torsion element then
`n ↦ R · t ^ n` is a family of tensor powers. Over an open of the base on which an invertible
module is trivialized by a section `t`, this is the family of its tensor powers. -/
theorem isTensorPowerFamily_span_pow {t : T} (hinj : Function.Injective (algebraMap R T))
    (ht : ∀ (n : ℕ) (r : R), r • t ^ n = 0 → r = 0) :
    IsTensorPowerFamily (fun n ↦ Submodule.span R {t ^ n}) := by
  refine isTensorPowerFamily_of_invertible _ hinj ?_ ?_ fun n ↦
    invertible_span_singleton (ht n)
  · show Submodule.span R {t ^ 0} = 1
    rw [pow_zero, Submodule.one_eq_span]
  · intro i j
    show Submodule.span R {t ^ i} * Submodule.span R {t ^ j} = Submodule.span R {t ^ (i + j)}
    rw [Submodule.span_mul_span, Set.singleton_mul_singleton, pow_add]

/-! ### The identity twist

The source's proof of Tag 02NC opens "This is the identity map when `ℒ ≅ 𝒪_S`". That case is
realized here: when the twisting family is `n ↦ R · t ^ n` the twist of `𝒜` by it is `𝒜` again,
and the twisting datum is the coordinate isomorphism `𝒜 d ⊗ R · t ^ d ≅ 𝒜 d`. This is the only
term of `Stacks.GradedRing.InvertibleTwist` in the development, so it is what shows the whole
hypothesis bundle of the absolute Tag 02NC machinery to be inhabited. -/

/-- The coordinate of a multiple of `t ^ d` with respect to `t ^ d`, as a linear equivalence
`R · t ^ d ≃ R`. -/
def spanCoord {t : T} (ht : ∀ (n : ℕ) (r : R), r • t ^ n = 0 → r = 0) (d : ℕ) :
    ↥(Submodule.span R {t ^ d}) ≃ₗ[R] R :=
  (LinearEquiv.ofBijective _ (bijective_toSpanSingleton_span (ht d))).symm

/-- **The defining property of the coordinate**: it is the scalar that produces the element from
`t ^ d`. Pinned as a named lemma; it is the only fact about `spanCoord` used below. -/
theorem spanCoord_smul {t : T} (ht : ∀ (n : ℕ) (r : R), r • t ^ n = 0 → r = 0) (d : ℕ)
    (l : ↥(Submodule.span R {t ^ d})) : spanCoord ht d l • t ^ d = (l : T) := by
  exact congrArg Subtype.val
    ((LinearEquiv.ofBijective _ (bijective_toSpanSingleton_span (ht d))).apply_symm_apply l)

/-- The coordinate is determined by `spanCoord_smul`. -/
theorem spanCoord_eq_of_smul {t : T} (ht : ∀ (n : ℕ) (r : R), r • t ^ n = 0 → r = 0) (d : ℕ)
    (l : ↥(Submodule.span R {t ^ d})) (r : R) (hr : r • t ^ d = (l : T)) :
    spanCoord ht d l = r :=
  injective_smul_of_ne_zero (ht d) ((spanCoord_smul ht d l).trans hr.symm)

/-- **The coordinate is multiplicative in the degree.** -/
theorem spanCoord_mul {t : T} (ht : ∀ (n : ℕ) (r : R), r • t ^ n = 0 → r = 0) (i j : ℕ)
    (l : ↥(Submodule.span R {t ^ i})) (m : ↥(Submodule.span R {t ^ j}))
    (hlm : (l : T) * m ∈ Submodule.span R {t ^ (i + j)}) :
    spanCoord ht (i + j) ⟨(l : T) * m, hlm⟩ = spanCoord ht i l * spanCoord ht j m := by
  refine spanCoord_eq_of_smul ht (i + j) _ _ ?_
  change (spanCoord ht i l * spanCoord ht j m) • t ^ (i + j) = (l : T) * (m : T)
  rw [pow_add, ← smul_mul_smul_comm, spanCoord_smul ht i l, spanCoord_smul ht j m]

/-- **The coordinate of the unit in degree zero is one.** -/
theorem spanCoord_one {t : T} (ht : ∀ (n : ℕ) (r : R), r • t ^ n = 0 → r = 0)
    (h0 : (1 : T) ∈ Submodule.span R {t ^ 0}) : spanCoord ht 0 ⟨1, h0⟩ = 1 := by
  refine spanCoord_eq_of_smul ht 0 _ 1 ?_
  change (1 : R) • t ^ 0 = (1 : T)
  rw [pow_zero, one_smul]

variable {A : Type u} [CommRing A] [Algebra R A]

/-- **The identity twist.** For the trivialized family `𝓛 n = R · t ^ n`, the graded algebra `𝒜`
is its own twist: the degree-`d` datum is `𝒜 d ⊗_R R · t ^ d ≅ 𝒜 d`, reading off the coordinate
with respect to `t ^ d`.

This is a term of `Stacks.GradedRing.InvertibleTwist`, which with
`Stacks.GradedRing.isTensorPowerFamily_span_pow` and
`Stacks.GradedRing.invertible_span_singleton` supplies every hypothesis the absolute Tag 02NC
development takes. -/
def identityTwist (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] {t : T}
    (ht : ∀ (n : ℕ) (r : R), r • t ^ n = 0 → r = 0) :
    InvertibleTwist 𝒜 (fun n ↦ Submodule.span R {t ^ n}) 𝒜 where
  piece d := (TensorProduct.congr (LinearEquiv.refl R ↥(𝒜 d)) (spanCoord ht d)).trans
    (TensorProduct.rid R ↥(𝒜 d))
  piece_mul i j x y l m hlm := by
    simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      TensorProduct.rid_tmul, SetLike.val_smul, spanCoord_mul ht i j l m hlm]
    rw [smul_mul_smul_comm]
  piece_one h0 := by
    simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      TensorProduct.rid_tmul, spanCoord_one ht h0, one_smul]

open scoped Polynomial in
/-- **The universal family of tensor powers**: the `R`-multiples of the powers of `X` in `R[X]`.
This exhibits a term of `Stacks.GradedRing.IsTensorPowerFamily`; it is the trivialized family of
`Stacks.GradedRing.isTensorPowerFamily_span_pow` at the generic trivializing element. -/
theorem isTensorPowerFamily_span_X_pow :
    IsTensorPowerFamily (fun n ↦ Submodule.span R {(Polynomial.X : R[X]) ^ n}) := by
  have ht : ∀ (n : ℕ) (r : R), r • (Polynomial.X : R[X]) ^ n = 0 → r = 0 := fun n r hr ↦ by
    simpa using congrArg (fun p : R[X] ↦ p.coeff n) hr
  exact isTensorPowerFamily_span_pow Polynomial.C_injective ht

/-- **The trivial family of tensor powers**, every member the whole of `R` inside `R`. This is the
case `ℒ ≅ 𝒪_S` of Tag 02NB, where the source's proof of Tag 02NC says the comparison is the
identity. -/
theorem isTensorPowerFamily_one : IsTensorPowerFamily (fun _ : ℕ ↦ (1 : Submodule R R)) := by
  refine isTensorPowerFamily_of_invertible _ (fun a b hab ↦ by simpa using hab) rfl
    (fun i j ↦ by simp) fun n ↦ ?_
  have h1 : (1 : Submodule R R) = ⊤ := Ideal.one_eq_top
  rw [h1]
  exact Module.Invertible.congr (Submodule.topEquiv (R := R) (M := R)).symm

end Stacks.GradedRing

end
