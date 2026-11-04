module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPolynomial.Basic
public import StacksFrontier.Deformation.ObstructionVariationQuadratic

/-!
# The degree-one Yoneda square of a cyclic module does not vanish

Let `P` be a commutative ring, `K ⊆ P` an ideal and `B = P ⧸ K`. The dévissage that would carry
Stacks 0DZ7 and Stacks 0DZB from a square-zero to a nilpotent kernel needs the quadratic term of
`Deformation.ObstructionVariation`'s law

`ω(e · M) = ω(M) + δ(e) + sq(e)`

to vanish, where `sq` is the degree-one Yoneda square `Ext¹_P(B, N) → Ext²_P(B, N)` (the cup
square pushed along the multiplication `N ⊗ N → N`; for `N = B` it is Yoneda composition
`CategoryTheory.Abelian.Ext.comp` of a class with itself). The hope on record was that `sq`
vanishes whenever the module is *cyclic*, since then `End(B) = B` is commutative and the
obstruction cannot be the nonzero commutator which refutes additivity for `M = (ZMod 2)²` in
`StacksFrontier.Deformation.ObstructionVariationQuadratic`.

**That hope is false, and this file refutes it.** Cyclicity of `B` makes `sq` additive, not zero.
For `a ∈ P` with `a ≠ 0`, `a² = 0` and `Ann(a) = (a)` — the smallest instance being `P = ZMod 4`,
`a = 2`, `B = ZMod 2` — the sequence

`0 → P ⧸ (a) --·a--> P --can--> P ⧸ (a) → 0`

is short exact with projective middle term, so the connecting map of the contravariant long exact
`Ext` sequence is *injective*; its own class `e` therefore has `e ∘ e = 0` only if `e = 0`, and
`e = 0` would split the sequence, putting `1` in `(a)` and so forcing `a = a · a · c = 0`. So
`e ∘ e ≠ 0` with `B = P ⧸ (a)` cyclic.

The positive direction is the complementary one: when `K = (f)` for a nonzerodivisor `f` — the
length-one lci case — `B` has projective dimension at most one, `Ext²_P(B, N) = 0` outright and
every degree-one Yoneda square vanishes for trivial reasons.

## Main definitions

* `Deformation.YonedaSquare.mulQuotSelf`: multiplication by `a`, read on `P ⧸ (a)` as a map
  **to `P`**; well defined exactly because `a² = 0`.
* `Deformation.YonedaSquare.selfExtShortComplex`: the periodic self-extension
  `0 → P ⧸ (a) → P → P ⧸ (a) → 0` of `P`-modules.
* `Deformation.YonedaSquare.regularShortComplex`: the free resolution
  `0 → P --·f--> P → P ⧸ (f) → 0` of the quotient by a principal ideal.

## Main results

* `Deformation.YonedaSquare.shortExact_selfExtShortComplex`: the periodic sequence is short
  exact when `Ann(a) ⊆ (a)`.
* `Deformation.YonedaSquare.extClass_ne_zero`: its class in `Ext¹_P(P ⧸ (a), P ⧸ (a))` is
  nonzero as soon as `a ≠ 0`; a retraction would make `1` a multiple of `a`, hence `a = 0`.
* `Deformation.YonedaSquare.extClass_comp_self_ne_zero`: **the refutation.** The degree-one
  Yoneda square of that class is nonzero in `Ext²_P(P ⧸ (a), P ⧸ (a))`, with `P ⧸ (a)` cyclic.
* `Deformation.YonedaSquare.zmod_four_extClass_comp_self_ne_zero`: the same for `P = ZMod 4`,
  `a = 2`, `B = ZMod 4 ⧸ (2)`, a two-element ring — so no largeness or exoticism is involved.
* `Deformation.YonedaSquare.mvPolynomial_zmod_four_extClass_comp_self_ne_zero`: the same for
  `P = (ZMod 4)[x₁, …, xₙ]` and `a = 2`, which is a **polynomial ring over the base of a
  square-zero thickening** — the shape of the `P'` that the dévissage of Stacks 0DZ7 builds.
* `Deformation.YonedaSquare.CyclicYonedaSquareVanishes` and
  `Deformation.YonedaSquare.not_cyclicYonedaSquareVanishes`: the vanishing statement a repair of
  the dévissage would consume, named and **refuted in every universe**.
* `Deformation.YonedaSquare.ext_eq_zero_of_regular`: for `f` a nonzerodivisor,
  `Ext^(n+2)_P(P ⧸ (f), N) = 0` for every `N`, whence
  `Deformation.YonedaSquare.comp_self_eq_zero_of_regular`: **every** degree-one Yoneda
  square of `P ⧸ (f)` vanishes.
* `Deformation.YonedaSquare.comp_self_eq_zero_of_hasProjectiveDimensionLT_two`: the same
  conclusion from the weakest hypothesis that gives it for free, projective dimension `< 2`.
* `Deformation.YonedaSquare.smul_comp_smul_self`: `sq` is quadratic-homogeneous,
  `sq(c • e) = c² • sq(e)`, so its image is not closed under scalars either.

## Implementation notes

**Which product this is.** `CategoryTheory.Abelian.Ext.comp` is the Yoneda product, and
`CategoryTheory.ShortComplex.ShortExact.extClass` is the class of a short exact sequence; both
are Mathlib's. The square of a class `e ∈ Ext¹_P(B, N)` with coefficients in a general `B`-module
`N` is the cup product `Ext¹(B, N) ⊗ Ext¹(B, N) → Ext²(B, N ⊗_B N)` followed by the
multiplication of `N`; for `N = B` the multiplication `B ⊗_B B → B` is an isomorphism and the cup
square is Yoneda composition, which is what is used here. That is also the case the dévissage
meets first: with `A' = ZMod 4 → A = ZMod 2` and `I = (2)` one has `K₁ = I/I² = A` and
`K₂ = I²/I³ = A`, so `M ⊗ K₁ ≅ M` and the quadratic term is literally the Yoneda square on
`Ext^•_P(M, M)`. The square with coefficients in a general `N` is not formalized here; what is
refuted is the vanishing statement for `N = B`, which the vanishing statement for general `N`
contains.

**Why cyclicity cannot help, in one line.** Classically — this is not formalized here, and the
only part of it the file proves is the one it needs — `Ext^•_{ZMod 4}(ZMod 2, ZMod 2)` is the
polynomial ring `(ZMod 2)[t]` on a degree-one generator, the minimal resolution being periodic,
and `t² ≠ 0` there. Non-cyclicity is what refutes *additivity* of `e ↦ e ∘ e` (over a matrix ring
the polarization `ef + fe` survives), and for cyclic `B` in residue characteristic two the square
map is additive, being a Frobenius. It is not zero; `t² ≠ 0` is the whole point. Graded
commutativity of the Yoneda algebra gives only `2·sq(e) = 0`, which is empty in characteristic
two, and `Deformation.YonedaSquare.smul_comp_smul_self` records the homogeneity that does survive.

**Relation to the counterexamples on record.** The ambient ring of
`StacksFrontier.Deformation.ObstructionVariationQuadratic` is `P = (ZMod 2)[x]/(x²)`, and the
nodal-cubic refutation of Stacks 0DZ2 (not imported here) states its own
ambient ring as `P = NC[x]/(x²)`, free of rank two over `NC`, with module `M = P/(x)`. In such a
`P` the element `a = x` satisfies the three hypotheses below — `x ≠ 0`, `x² = 0`, and
`Ann(x) = (x)` by freeness on `{1, x}` — so `Deformation.YonedaSquare.extClass_comp_self_ne_zero`
applies there and the degree-one Yoneda square of those instances is nonzero. That is not proved
here for those instances, since neither is in this module's import closure; it is recorded because
it settles a question those files raise. In particular the cyclicity of the nodal
counterexample's `M` is consistent with everything below: it is a cyclic module whose square
does **not** vanish, so no contradiction arises between that counterexample and the vanishing
results proved here, which need the generator of `K` to be a nonzerodivisor.

**What the refutation does not cover, and what that leaves open.** In both instances exhibited
the quotient `B = P ⧸ (a)` is **not flat** over the coefficient ring: `a` is taken from the base
(`a = 2 ∈ ZMod 4`), so `B` is killed by `2` and has `ZMod 4`-torsion. The dévissage of Stacks
0DZ7 and 0DZB applies its quadratic term to an `M` that *is* flat over `A`, so these instances
refute the general statement about cyclic modules without being instances of the dévissage's own
data. The nodal-cubic refutation of Stacks 0DZ2 is the other way round: its `M = NC` is flat
over its `A`, and its `a = x` satisfies the hypotheses below, but its `P` is free of rank two
over the base and **not smooth**. So what this file leaves open is exactly the conjunction `P`
smooth over the base *and* `M` flat over the base — which is the separation a repair of 0DZ7 or
0DZB would have to exploit, and is not cyclicity of `M`.

**What is not claimed.** Nothing here discharges Stacks 0DZ7 or Stacks 0DZB, and nothing here
refutes them: what it refutes is one proposed *input* to their dévissage, namely that the
quadratic term vanishes for cyclic modules. The lci case `K` generated by a regular sequence of
length `c ≥ 2` is **not** settled here either; the classical reason squares vanish there is that
`Ext^•_P(B, B)` is the exterior algebra on the dual of the conormal module, in which degree-one
squares vanish identically even in characteristic two, and that identification needs a
comparison of the Yoneda product with a Koszul resolution which this repository does not have.
Only the length-one case, where `Ext²` vanishes outright, is formalized below. So the line this
file draws is: squares vanish for `K` principal and generated by a nonzerodivisor, and do not
vanish for `K` principal and generated by an `a ≠ 0` with `Ann(a) = (a)`.

**The nearby Mathlib map.** `Ideal.mulQuot a I : R ⧸ I →ₗ[R] R ⧸ (a • I)` is multiplication by
`a` between two quotients. With `I = (a)` and `a² = 0` its target is `R ⧸ ⊥`, so it carries the
same information as `Deformation.YonedaSquare.mulQuotSelf`, but the middle term of the periodic
sequence has to be `P` itself for `CategoryTheory.Projective` to be available on it, and
transporting along `R ⧸ ⊥ ≅ R` costs more than the three-line `Submodule.liftQ` below.

## References

* [Stacks Project, Tag 0DZ7](https://stacks.math.columbia.edu/tag/0DZ7)
* [Stacks Project, Tag 0DZB](https://stacks.math.columbia.edu/tag/0DZB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u

namespace Deformation.YonedaSquare

variable {P : Type u} [CommRing P]

/-! ### The periodic self-extension of `P ⧸ (a)` -/

/-- Multiplication by `a`, read on the quotient `P ⧸ (a)`. It is well defined exactly because
`a * a = 0`, and its image is the ideal `(a)`. -/
def mulQuotSelf (a : P) (hsq : a * a = 0) : (P ⧸ Ideal.span {a}) →ₗ[P] P :=
  (Ideal.span {a}).liftQ (LinearMap.toSpanSingleton P P a) (by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    simp [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_assoc, hsq])

/-- `mulQuotSelf a hsq` sends the class of `x` to `x * a`. -/
@[simp]
theorem mulQuotSelf_mk (a : P) (hsq : a * a = 0) (x : P) :
    mulQuotSelf a hsq (Submodule.Quotient.mk x) = x * a := rfl

/-- The quotient map `P → P ⧸ I` kills the image of a map with range `I`. -/
private theorem mkQ_comp_eq_zero_of_range_eq {M : Type*} [AddCommGroup M] [Module P M]
    (g : M →ₗ[P] P) (I : Ideal P) (h : LinearMap.range g = I) : I.mkQ ∘ₗ g = 0 := by
  subst h
  exact LinearMap.range_mkQ_comp g

/-- A map `g` with range `I` is exact against the quotient map `P → P ⧸ I`. -/
private theorem exact_mkQ_of_range_eq {M : Type*} [AddCommGroup M] [Module P M]
    (g : M →ₗ[P] P) (I : Ideal P) (h : LinearMap.range g = I) : Function.Exact g I.mkQ := by
  subst h
  exact LinearMap.exact_map_mkQ_range g

/-- The image of `mulQuotSelf a hsq` is the ideal `(a)`. -/
private theorem range_mulQuotSelf (a : P) (hsq : a * a = 0) :
    LinearMap.range (mulQuotSelf a hsq) = Ideal.span {a} := by
  rw [mulQuotSelf, Submodule.range_liftQ, LinearMap.range_toSpanSingleton]

/-- The composite `P ⧸ (a) --·a--> P --can--> P ⧸ (a)` is zero. -/
theorem mkQ_comp_mulQuotSelf (a : P) (hsq : a * a = 0) :
    (Ideal.span {a}).mkQ ∘ₗ mulQuotSelf a hsq = 0 :=
  mkQ_comp_eq_zero_of_range_eq _ _ (range_mulQuotSelf a hsq)

/-- The sequence `P ⧸ (a) --·a--> P --can--> P ⧸ (a)` is exact at `P`. -/
theorem exact_mulQuotSelf (a : P) (hsq : a * a = 0) :
    Function.Exact (mulQuotSelf a hsq) (Ideal.span {a}).mkQ :=
  exact_mkQ_of_range_eq _ _ (range_mulQuotSelf a hsq)

/-- Multiplication by `a` from `P ⧸ (a)` to `P` is injective when `Ann(a) ⊆ (a)`. -/
theorem injective_mulQuotSelf (a : P) (hsq : a * a = 0)
    (hann : ∀ x : P, x * a = 0 → x ∈ Ideal.span {a}) :
    Function.Injective (mulQuotSelf a hsq) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ fun x hx ↦ hann x hx

/-- The periodic self-extension `0 → P ⧸ (a) --·a--> P --can--> P ⧸ (a) → 0`: a short complex
of `P`-modules whose two outer terms are the same cyclic module, and whose middle term is free
of rank one. -/
abbrev selfExtShortComplex (a : P) (hsq : a * a = 0) : ShortComplex (ModuleCat.{u} P) :=
  ShortComplex.mk (ModuleCat.ofHom (mulQuotSelf a hsq))
    (ModuleCat.ofHom (Ideal.span {a}).mkQ)
    (by rw [← ModuleCat.ofHom_comp, mkQ_comp_mulQuotSelf, ModuleCat.ofHom_zero])

/-- The periodic self-extension `0 → P ⧸ (a) → P → P ⧸ (a) → 0` is short exact when
`Ann(a) ⊆ (a)`. -/
theorem shortExact_selfExtShortComplex (a : P) (hsq : a * a = 0)
    (hann : ∀ x : P, x * a = 0 → x ∈ Ideal.span {a}) :
    (selfExtShortComplex a hsq).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (exact_mulQuotSelf a hsq) (injective_mulQuotSelf a hsq hann)
    (Submodule.mkQ_surjective _)

/-- `a` annihilates `P ⧸ (a)`. -/
theorem smul_quot_eq_zero (a : P) (y : P ⧸ Ideal.span {a}) : a • y = 0 := by
  refine Submodule.Quotient.induction_on _ y fun z ↦ ?_
  rw [← Submodule.Quotient.mk_smul]
  exact (Submodule.Quotient.mk_eq_zero _).2
    (Ideal.mem_span_singleton'.2 ⟨z, by rw [smul_eq_mul, mul_comm]⟩)

/-! ### The class of the periodic sequence, and its Yoneda square -/

variable (a : P) (hsq : a * a = 0) (hann : ∀ x : P, x * a = 0 → x ∈ Ideal.span {a})

/-- The class of the periodic sequence is nonzero as soon as `a ≠ 0`: a retraction of
multiplication by `a` would make `1` a multiple of `a`, hence `a = a * a * c = 0`. -/
theorem extClass_ne_zero (ha : a ≠ 0) :
    (shortExact_selfExtShortComplex a hsq hann).extClass ≠ 0 := by
  intro h
  obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁
    (shortExact_selfExtShortComplex a hsq hann) (selfExtShortComplex a hsq).X₁
    (Ext.mk₀ (𝟙 (selfExtShortComplex a hsq).X₁)) (add_zero 1) (by rw [Ext.comp_mk₀_id]; exact h)
  rw [← Ext.mk₀_homEquiv₀_apply x₂, Ext.mk₀_comp_mk₀] at hx₂
  have hr := (Ext.mk₀_bijective _ _).1 hx₂
  set r := Ext.homEquiv₀ x₂
  have key := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp hr) (Submodule.Quotient.mk (1 : P))
  rw [ModuleCat.hom_comp] at key
  simp only [LinearMap.comp_apply, ModuleCat.hom_ofHom, mulQuotSelf_mk, one_mul, ModuleCat.hom_id,
    LinearMap.id_apply] at key
  have hz : (ModuleCat.Hom.hom r) a = 0 := by
    have h1 : (ModuleCat.Hom.hom r) a = a • (ModuleCat.Hom.hom r) 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [h1, smul_quot_eq_zero]
  rw [hz] at key
  have h1 : (1 : P) ∈ Ideal.span {a} := (Submodule.Quotient.mk_eq_zero _).1 key.symm
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  exact ha (by rw [← one_mul a, ← hc, mul_assoc, hsq, mul_zero])

/-- **The degree-one Yoneda square of a cyclic module need not vanish.** For `a ≠ 0` with
`a * a = 0` and `Ann(a) = (a)`, the class `e` of the periodic sequence
`0 → P ⧸ (a) → P → P ⧸ (a) → 0` has `e ∘ e ≠ 0` in `Ext²_P(P ⧸ (a), P ⧸ (a))`, while
`P ⧸ (a)` is a cyclic `P`-module.

The middle term of the sequence is free, so the connecting map
`Ext¹_P(P ⧸ (a), P ⧸ (a)) → Ext²_P(P ⧸ (a), P ⧸ (a))` — which is composition with `e` — has
trivial kernel; and `e` itself is not zero. -/
theorem extClass_comp_self_ne_zero (ha : a ≠ 0) :
    (shortExact_selfExtShortComplex a hsq hann).extClass.comp
        (shortExact_selfExtShortComplex a hsq hann).extClass one_add_one_eq_two ≠ 0 := by
  intro h
  obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁
    (shortExact_selfExtShortComplex a hsq hann) (selfExtShortComplex a hsq).X₁
    (shortExact_selfExtShortComplex a hsq hann).extClass one_add_one_eq_two h
  refine extClass_ne_zero a hsq hann ha ?_
  rw [← hx₂, Ext.eq_zero_of_projective x₂, Ext.comp_zero]

/-- The square map is homogeneous of degree two: `sq (c • e) = c² • sq e`. So the image of the
obstruction-variation map is not closed under scalars either, independently of additivity. -/
theorem smul_comp_smul_self {X Y : ModuleCat.{u} P} (c : P) (e : Ext X Y 1) (f : Ext Y X 1) :
    (c • e).comp (c • f) one_add_one_eq_two = (c * c) • e.comp f one_add_one_eq_two := by
  rw [Ext.smul_comp, Ext.comp_smul, smul_smul]

/-! ### The smallest instance: `P = ZMod 4` -/

/-- `2 * 2 = 0` in `ZMod 4`. -/
theorem zmod_four_sq : (2 : ZMod 4) * 2 = 0 := by decide

/-- `Ann(2) = (2)` in `ZMod 4`. -/
theorem zmod_four_ann (x : ZMod 4) (hx : x * 2 = 0) : x ∈ Ideal.span {(2 : ZMod 4)} := by
  rw [Ideal.mem_span_singleton']
  revert x
  decide

/-- **The refutation at the smallest instance.** `P = ZMod 4`, `a = 2`, `B = P ⧸ (2)` — a ring
with two elements, cyclic over `P` — has a degree-one Yoneda self-square that is nonzero. -/
theorem zmod_four_extClass_comp_self_ne_zero :
    (shortExact_selfExtShortComplex (2 : ZMod 4) zmod_four_sq zmod_four_ann).extClass.comp
        (shortExact_selfExtShortComplex (2 : ZMod 4) zmod_four_sq zmod_four_ann).extClass
          one_add_one_eq_two ≠ 0 :=
  extClass_comp_self_ne_zero (2 : ZMod 4) zmod_four_sq zmod_four_ann (by decide)

/-! ### The same on a polynomial ring over the deformation base -/

/-- `Ann(2) = (2)` in `MvPolynomial σ (ZMod 4)`: the base ring annihilator spreads to a free
module over it. This is `Module.Flat.exists_eq_smul_of_smul_eq_zero` of
`StacksFrontier.Deformation.ObstructionVariationQuadratic` applied to the free `ZMod 4`-module
`MvPolynomial σ (ZMod 4)`. -/
theorem mvPolynomial_zmod_four_ann {σ : Type u} (p : MvPolynomial σ (ZMod 4))
    (hp : p * MvPolynomial.C 2 = 0) :
    p ∈ Ideal.span {(MvPolynomial.C 2 : MvPolynomial σ (ZMod 4))} := by
  have h2 : (2 : ZMod 4) • p = 0 := by
    rw [MvPolynomial.smul_eq_C_mul, mul_comm]
    exact hp
  obtain ⟨w, hw⟩ := Module.Flat.exists_eq_smul_of_smul_eq_zero (R := ZMod 4)
    (M := MvPolynomial σ (ZMod 4)) (a := 2) (b := 2) (by decide) h2
  exact Ideal.mem_span_singleton'.2 ⟨w, by rw [hw, MvPolynomial.smul_eq_C_mul, mul_comm]⟩

/-- `(C 2)² = 0` in `MvPolynomial σ (ZMod 4)`. -/
theorem mvPolynomial_zmod_four_sq {σ : Type u} :
    (MvPolynomial.C 2 : MvPolynomial σ (ZMod 4)) * MvPolynomial.C 2 = 0 := by
  rw [← map_mul, zmod_four_sq, map_zero]

/-- **The refutation on the dévissage's own ambient ring.** `P = A'[x₁, …]` for
`A' = ZMod 4`, `a = 2`, `B = P ⧸ (2) = (ZMod 2)[x₁, …]`: a polynomial ring over the base of a
square-zero thickening, and a cyclic quotient of it, whose degree-one Yoneda self-square is
nonzero. So neither cyclicity of the module nor smoothness of `P` over the base rules the
quadratic term out; what does is the regularity of the generator of `K`. -/
theorem mvPolynomial_zmod_four_extClass_comp_self_ne_zero {σ : Type u} :
    (shortExact_selfExtShortComplex (MvPolynomial.C 2 : MvPolynomial σ (ZMod 4))
          mvPolynomial_zmod_four_sq mvPolynomial_zmod_four_ann).extClass.comp
        (shortExact_selfExtShortComplex (MvPolynomial.C 2 : MvPolynomial σ (ZMod 4))
          mvPolynomial_zmod_four_sq mvPolynomial_zmod_four_ann).extClass
          one_add_one_eq_two ≠ 0 :=
  extClass_comp_self_ne_zero (MvPolynomial.C 2 : MvPolynomial σ (ZMod 4))
    mvPolynomial_zmod_four_sq mvPolynomial_zmod_four_ann (by
      intro h
      have h0 : (2 : ZMod 4) = 0 :=
        MvPolynomial.C_injective σ (ZMod 4) (h.trans (map_zero MvPolynomial.C).symm)
      exact absurd h0 (by decide))

/-! ### The refuted statement, named -/

/-- **The vanishing statement a repair of the dévissage would consume**: for every commutative
ring `P`, every ideal `K` and every degree-one class of the cyclic `P`-module `P ⧸ K`, the Yoneda
square vanishes. This is the hypothesis `sq = 0` of the obstruction-variation law
`ω(e · M) = ω(M) + δ(e) + sq(e)`, read at the coefficients `N = B` in which the dévissage first
meets it, and quantified over exactly the class of modules the instance of Stacks 0DZ7 and
Stacks 0DZB provides: cyclic ones. It is false. -/
def CyclicYonedaSquareVanishes : Prop :=
  ∀ (P : Type u) [CommRing P] (K : Ideal P)
    (e : Ext (ModuleCat.of P (P ⧸ K)) (ModuleCat.of P (P ⧸ K)) 1),
      e.comp e one_add_one_eq_two = 0

/-- **`sq` does not vanish for cyclic modules**, in every universe. The witness is
`P = (ZMod 4)[x]` with `K = (2)`, through
`Deformation.YonedaSquare.mvPolynomial_zmod_four_extClass_comp_self_ne_zero`. A vanishing
statement with coefficients in a general `B`-module `N` would contain this one, so it is refuted
along with it. -/
theorem not_cyclicYonedaSquareVanishes : ¬ CyclicYonedaSquareVanishes.{u} := fun h ↦
  mvPolynomial_zmod_four_extClass_comp_self_ne_zero (σ := PUnit.{u + 1})
    (h _ (Ideal.span {MvPolynomial.C 2}) _)

/-! ### The length-one lci case: squares vanish because `Ext²` does -/

/-- The composite `P --·f--> P --can--> P ⧸ (f)` is zero. -/
theorem mkQ_comp_toSpanSingleton (f : P) :
    (Ideal.span {f}).mkQ ∘ₗ LinearMap.toSpanSingleton P P f = 0 :=
  mkQ_comp_eq_zero_of_range_eq _ _ (LinearMap.range_toSpanSingleton f)

/-- The free resolution `0 → P --·f--> P → P ⧸ (f) → 0` of `P ⧸ (f)`. -/
abbrev regularShortComplex (f : P) : ShortComplex (ModuleCat.{u} P) :=
  ShortComplex.mk (ModuleCat.ofHom (LinearMap.toSpanSingleton P P f))
    (ModuleCat.ofHom (Ideal.span {f}).mkQ)
    (by rw [← ModuleCat.ofHom_comp, mkQ_comp_toSpanSingleton, ModuleCat.ofHom_zero])

/-- The sequence `P --·f--> P --can--> P ⧸ (f)` is exact at the middle term. -/
theorem exact_toSpanSingleton (f : P) :
    Function.Exact (LinearMap.toSpanSingleton P P f) (Ideal.span {f}).mkQ :=
  exact_mkQ_of_range_eq _ _ (LinearMap.range_toSpanSingleton f)

/-- Multiplication by a nonzerodivisor `f` is injective on `P`. -/
theorem injective_toSpanSingleton (f : P) (hf : ∀ x : P, x * f = 0 → x = 0) :
    Function.Injective (LinearMap.toSpanSingleton P P f) := by
  intro x y hxy
  simp only [LinearMap.toSpanSingleton_apply, smul_eq_mul] at hxy
  refine sub_eq_zero.1 (hf _ ?_)
  rw [sub_mul, hxy, sub_self]

/-- For `f` a nonzerodivisor, `0 → P --·f--> P → P ⧸ (f) → 0` is short exact. -/
theorem shortExact_regularShortComplex (f : P) (hf : ∀ x : P, x * f = 0 → x = 0) :
    (regularShortComplex f).ShortExact :=
  ModuleCat.shortComplex_shortExact _ (exact_toSpanSingleton f) (injective_toSpanSingleton f hf)
    (Submodule.mkQ_surjective _)

/-- For `f` a nonzerodivisor, `P ⧸ (f)` has projective dimension at most one. -/
theorem hasProjectiveDimensionLT_two_of_regular (f : P) (hf : ∀ x : P, x * f = 0 → x = 0) :
    HasProjectiveDimensionLT (ModuleCat.of P (P ⧸ Ideal.span {f})) 2 :=
  (shortExact_regularShortComplex f hf).hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance

/-- For `f` a nonzerodivisor, `Ext^(n+2)_P(P ⧸ (f), N) = 0` for every `N`. -/
theorem ext_eq_zero_of_regular (f : P) (hf : ∀ x : P, x * f = 0 → x = 0)
    (N : ModuleCat.{u} P) (n : ℕ) (e : Ext (ModuleCat.of P (P ⧸ Ideal.span {f})) N (n + 2)) :
    e = 0 :=
  have := hasProjectiveDimensionLT_two_of_regular f hf
  e.eq_zero_of_hasProjectiveDimensionLT 2 (by lia)

/-- **Every** degree-one Yoneda square of `P ⧸ (f)` vanishes when `f` is a nonzerodivisor: the
target group `Ext²` is itself zero. This is the length-one lci case, and it is the only case in
which the vanishing is formal. -/
theorem comp_self_eq_zero_of_regular (f : P) (hf : ∀ x : P, x * f = 0 → x = 0)
    (e : Ext (ModuleCat.of P (P ⧸ Ideal.span {f})) (ModuleCat.of P (P ⧸ Ideal.span {f})) 1) :
    e.comp e one_add_one_eq_two = 0 :=
  ext_eq_zero_of_regular f hf _ 0 _

/-- The vanishing of degree-one Yoneda squares from the weakest hypothesis that gives it for
free: projective dimension less than two. -/
theorem comp_self_eq_zero_of_hasProjectiveDimensionLT_two (B : ModuleCat.{u} P)
    [HasProjectiveDimensionLT B 2] (e : Ext B B 1) : e.comp e one_add_one_eq_two = 0 :=
  Ext.eq_zero_of_hasProjectiveDimensionLT _ 2 (by lia)

end Deformation.YonedaSquare
