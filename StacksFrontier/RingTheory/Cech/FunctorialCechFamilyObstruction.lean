module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Span

/-!
# There is no functorial choice of Čech generators

Tag 099D asks for a complex `K(A, I)` of `A`-modules attached to a pair of a commutative ring and
a finitely generated ideal, together with a map of complexes `K(A, I) → K(B, IB)` for every ring
map `φ : A → B`, the maps composing *on the nose*. The library already has that datum for a pair
carrying a **chosen finite generating family**: the complex is `Cech.cechComplex f A`, the map is
`Stacks.CechRingBaseChange.complexMap φ f`, which goes from the Čech complex of `f₁, …, f_r` over
`A` to the Čech complex of `φ(f₁), …, φ(f_r)` over `B`, and the composition law on the nose is
`Stacks.CechRingBaseChange.complexMap_comp`. The same is true of the other map of complexes the
library has between Čech complexes, the restriction `Cech.cechRestrict` to an ordered subfamily.

So the obvious route to 099D is to *choose*, for every pair `(A, I)`, a finite generating family
of `I`, and to let `K(A, I)` be its Čech complex. Both available maps of complexes then require
the generators chosen for `(B, IB)` to be images under `φ` of the generators chosen for `(A, I)`.
**This file proves that no such choice exists**, so that route is closed.

The obstruction is invariance, not cardinality. A choice of generators compatible with transport
is in particular compatible with transport along an *automorphism* `φ` of `A` with `I.map φ = I`,
and there it says that `φ` permutes the chosen finite generating set of `I`. Take `A = K[X]` with
`K` a field, `I = (X)`, and `φ` the dilation `X ↦ cX` for a scalar `c` no power of which is `1`:
a finite set permuted by `φ` consists of fixed points of a power of `φ`, dilation multiplies the
leading coefficient of a polynomial of degree `d` by `c ^ d`, and so a fixed polynomial of the
dilation lying in `(X)` is zero. The chosen generators of `(X)` would then all be zero.

This says nothing against tag 099D itself: the source's `K(A, I)` is not a Čech complex, only
isomorphic to one in `D(A)`, and it is functorial because it is the value at `(A, I)` of a complex
of presheaves of modules on the category of pairs — an object which, unlike a Čech complex,
carries an action of the automorphism group of the pair. What the result below pins down is that
the strictification cannot be avoided by a clever choice of generators, and so that an inhabitant
of `Stacks.LocalCohomology.FunctorialCechData` must build a genuinely new complex.

It says nothing against tag 099E either, and the distinction is worth stating because it is easy
to over-read. Tag 099E asserts `∃ K ⟶ 𝒪` in `D(𝒪)` such that *for every* object `U` and *every*
finite family generating `ℐ|_U` there *exists* an isomorphism with the extended alternating Čech
complex of that family. The generators are universally quantified and handed to the statement;
no choice function on objects appears, and the only compatibility demanded is the triangle with
the two augmentations to `𝒪_U`. So the invariance obstruction below, which is about a *chosen*
assignment of generators to pairs, is not in 099E's path at all. That generator-dependence is
harmless up to canonical isomorphism is in fact already proved here, with no functorial choice:
`Stacks.LocalCohomology.exists_extendedCechObject_iso_of_span_eq`.

## Main definitions

* `Stacks.FunctorialCechFamily.dilate` — the dilation `p(X) ↦ p(cX)` of a polynomial ring, as a
  ring homomorphism.
* `Stacks.FunctorialCechFamily.FunctorialGenerators` — a choice, for every commutative ring and
  every finitely generated ideal, of a finite generating set, such that every chosen generator of
  `IB` is the image of a chosen generator of `I`. This is the hypothesis under which
  `Stacks.CechRingBaseChange.complexMap` and `Cech.cechRestrict` assemble into the data (1)–(3)
  of tag 099D.

## Main results

* `Stacks.FunctorialCechFamily.exists_notMem_dilate_image` — for a field `K`, a scalar `c` no
  power of which is `1`, and a finite generating set `S` of the ideal `(X) ⊆ K[X]`, some element
  of `S` is not the dilation by `c` of an element of `S`.
* `Stacks.FunctorialCechFamily.FunctorialGenerators.elim`,
  `Stacks.FunctorialCechFamily.isEmpty_functorialGenerators` — **there is no functorial choice of
  generators**.
* `Stacks.FunctorialCechFamily.not_transportedFamily` — the same, in the `Fin r`-indexed form that
  `Stacks.CechRingBaseChange.complexMap` consumes: there is no assignment of a finite generating
  family to each pair such that each generator chosen for `(B, IB)` is the `φ`-image of a
  generator chosen for `(A, I)`.
* `Stacks.FunctorialCechFamily.not_subset_image_of_map` — the ideal `IB` is not in general
  contained in the set-image `φ(I)`, so taking the whole of `I` as the index set does not
  transport either.
* `Stacks.FunctorialCechFamily.not_exists_common_generating_subFinset` — two finite generating
  families of an ideal need not have a common generating subfamily, so the finite generating
  families of an ideal are directed under inclusion but not codirected.

## Two choice-free routes, and what each runs into

Two designs for `K(A, I)` make no choice of generators, and so are untouched by
`isEmpty_functorialGenerators`: take the extended alternating Čech complex on the whole of `I`
as an index set, or take a colimit of the Čech complexes of all finite generating families of
`I` over the poset of those families. Both are functorial in `(A, I)` *as index data*; what
neither of them is, is a diagram of Čech complexes.

The reason is the variance of the Čech complex in its index family, which is forced by the
component formula `Cech.cechD_component`: the `T`-component of `d x` is the alternating sum of
the components of `x` at the sets `T ∖ k` for `k ∈ T`. Reading off the components indexed by
subsets of a subfamily is therefore a map of complexes — that is `Cech.cechRestrict`, and it runs
from the Čech complex of the *larger* family to that of the smaller one — while extending a
cochain by zero is not: for the families `f` and `f, g` of one and two elements and the element
`1` in degree zero, the differential of the extension has both the `{f}`- and the `{g}`-component
equal to `1`, whereas the extension of the differential has `{g}`-component `0`.

So the poset of finite generating families indexes a diagram of Čech complexes whose maps run
*down* the poset, and the colimit over that diagram is a colimit over the opposite poset, which
computes the right thing only if that opposite poset is filtered.
`not_exists_common_generating_subFinset` says it is not. The limit over the poset does exist, and
a degree-`p` element of it is a compatible family of cochains on the `p`-element subsets of each
finite generating family, i.e. a cochain on the `p`-element subsets of the whole of `I` — the
Čech complex on all of `I`, in its product form, which is where the two designs meet. (For an
infinite index set only the product form is a complex: the differential adds an index, so on a
direct sum it would be an infinite sum, while the component formula shows the product form's
differential is the finite alternating sum over the elements of the target index set.)

That complex, in turn, is not functorial in the pair. Both maps of complexes the library has
between Čech complexes — base change `Stacks.CechRingBaseChange.complexMap`, which keeps the
index set and sends the family `f` to `φ ∘ f`, and the restriction `Cech.cechRestrict` to an
ordered subfamily — produce a map from the Čech complex of `f` over `A` to the Čech complex of a
family whose members are `φ`-images of members of `f`. With the whole of `I` as the index set for
`(A, I)` and the whole of `IB` as the index set for `(B, IB)`, that asks for `IB ⊆ φ(I)` as sets,
and `not_subset_image_of_map` refutes it: for `K[X] → K[X][Y]` and `I = (X)` the element `Y · X`
of `IB` is not the image of an element of `I`.

Neither statement is a proof that no inhabitant of
`Stacks.LocalCohomology.FunctorialCechData` exists — the source constructs one, and not out of
Čech complexes. They delimit what a Čech-indexed design can do.

## Implementation notes

The counterexample ring is `K[X]` for `K = ULift.{u} ℚ`, so that it lives in the universe `u` in
which `Stacks.LocalCohomology.FunctorialCechData.{u}` quantifies over rings; the dilation factor
is `2`, whose powers in `ℚ` are never `1`. Nothing depends on `ℚ`: any field with an element of
infinite multiplicative order would do.

The hypothesis of `FunctorialGenerators.gens_map` is the weakest form of transport that makes
either of the library's two maps of complexes available — it does not even ask that the chosen
generating sets have the same cardinality, nor that the transport be the whole family. It is
therefore refuted a fortiori for the literal hypothesis of
`Stacks.CechRingBaseChange.complexMap`, which is that the family for `(B, IB)` *is* `φ ∘ f`.

No `@[stacks]` attribute is attached: this is a statement about what tag 099D cannot be proved
by, not a part of its conclusion.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.FunctorialCechFamily

/-! ### Dilation of a polynomial ring -/

section Dilate

variable {K : Type*} [Field K] {c : K}

/-- **Dilation.** The ring endomorphism `p(X) ↦ p(cX)` of a polynomial ring. For `c ≠ 0` it is an
automorphism, with inverse the dilation by `c⁻¹`. -/
def dilate (c : K) : K[X] →+* K[X] :=
  Polynomial.compRingHom (C c * X)

/-- The dilation by `c` sends `p` to the composite `p(cX)`. -/
theorem dilate_apply (c : K) (p : K[X]) : dilate c p = p.comp (C c * X) := rfl

/-- The dilation by `c` sends `X` to `cX`. -/
@[simp]
theorem dilate_X (c : K) : dilate c X = C c * X := by
  rw [dilate_apply, X_comp]

/-- For `c ≠ 0` the dilation by `c` is injective. -/
theorem dilate_injective (hc : c ≠ 0) : Function.Injective (dilate c) := by
  intro p q h
  have h2 := congrArg (fun r => dilate c⁻¹ r) h
  simp only [dilate_apply] at h2
  rwa [comp_assoc, comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ hc, C_1, one_mul, comp_X, comp_X] at h2

/-- For `c ≠ 0` the dilation by `c` preserves the degree of a polynomial. -/
theorem natDegree_dilate (hc : c ≠ 0) (p : K[X]) : (dilate c p).natDegree = p.natDegree := by
  rw [dilate_apply, natDegree_comp, natDegree_C_mul hc, natDegree_X, mul_one]

/-- Dilation multiplies the leading coefficient of a polynomial of degree `d` by `c ^ d`. -/
theorem leadingCoeff_dilate (hc : c ≠ 0) (p : K[X]) :
    (dilate c p).leadingCoeff = p.leadingCoeff * c ^ p.natDegree := by
  rw [dilate_apply,
    leadingCoeff_comp (by rw [natDegree_C_mul hc, natDegree_X]; exact one_ne_zero),
    leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, mul_one]

/-- For `c ≠ 0` every iterate of the dilation by `c` preserves the degree of a polynomial. -/
theorem natDegree_dilate_iterate (hc : c ≠ 0) (p : K[X]) (n : ℕ) :
    ((dilate c)^[n] p).natDegree = p.natDegree := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', natDegree_dilate hc, ih]

/-- For `c ≠ 0` the `n`-th iterate of the dilation by `c` multiplies the leading coefficient of a
polynomial of degree `d` by `c ^ (n * d)`. -/
theorem leadingCoeff_dilate_iterate (hc : c ≠ 0) (p : K[X]) (n : ℕ) :
    ((dilate c)^[n] p).leadingCoeff = p.leadingCoeff * c ^ (n * p.natDegree) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', leadingCoeff_dilate hc, ih, natDegree_dilate_iterate hc,
      mul_assoc, ← pow_add, Nat.succ_mul]

/-- **The dilation is an automorphism of the pair `(K[X], (X))`:** it carries the ideal `(X)` onto
itself, so it is a morphism of pairs in the sense of tag 099D. -/
theorem map_dilate_span_X (hc : c ≠ 0) :
    Ideal.map (dilate c) (Ideal.span {(X : K[X])}) = Ideal.span {(X : K[X])} := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 (Ideal.span_le.2 ?_)) (Ideal.span_le.2 ?_)
  · intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    simp only [SetLike.mem_coe, Ideal.mem_comap, dilate_X]
    exact Ideal.mem_span_singleton'.2 ⟨C c, rfl⟩
  · intro y hy
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    have h1 := Ideal.mem_map_of_mem (dilate c) (Ideal.subset_span (rfl : X ∈ {(X : K[X])}))
    rw [dilate_X] at h1
    have h2 := Ideal.mul_mem_left _ (C c⁻¹) h1
    rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul] at h2

/-- **A polynomial in `(X)` fixed by an iterate of the dilation is zero.** If no power of `c` is
`1` then a nonzero fixed polynomial would have to be a nonzero constant, which does not lie in the
ideal `(X)`. -/
theorem eq_zero_of_dilate_iterate_eq_self (hc : c ≠ 0) (hroot : ∀ n : ℕ, c ^ n = 1 → n = 0)
    {p : K[X]} {n : ℕ} (hn : n ≠ 0) (hfix : (dilate c)^[n] p = p)
    (hmem : p ∈ Ideal.span {(X : K[X])}) : p = 0 := by
  by_contra hp
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp
  have h1 : p.leadingCoeff * c ^ (n * p.natDegree) = p.leadingCoeff * 1 := by
    rw [mul_one, ← leadingCoeff_dilate_iterate hc p n, hfix]
  have h2 : p.natDegree = 0 := by
    rcases Nat.mul_eq_zero.1 (hroot _ (mul_left_cancel₀ hlc h1)) with h | h
    · exact absurd h hn
    · exact h
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 hmem
  have h4 : p.eval 0 = 0 := by rw [hq]; simp
  have h5 : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero h2
  rw [h5, eval_C] at h4
  exact hp (by rw [h5, h4, map_zero])

/-- **A finite generating set of `(X) ⊆ K[X]` is not stable under dilation.** Some element of it
is not the dilation of an element of it.

This is the obstruction: a choice of generators transported along ring maps would, at the
automorphism `dilate c` of the pair `(K[X], (X))`, give a generating set each of whose elements is
the dilation of another one, hence a generating set permuted by the dilation. -/
theorem exists_notMem_dilate_image (hc : c ≠ 0) (hroot : ∀ n : ℕ, c ^ n = 1 → n = 0)
    (S : Finset K[X]) (hspan : Ideal.span (S : Set K[X]) = Ideal.span {(X : K[X])}) :
    ∃ p ∈ S, ∀ q ∈ S, p ≠ dilate c q := by
  classical
  by_contra hcon
  push Not at hcon
  -- `S` is contained in its image, hence equal to it, hence stable under the dilation.
  have hstable : ∀ p ∈ S, dilate c p ∈ S := by
    have hsub : S ⊆ S.image (dilate c) := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := hcon p hp
      exact Finset.mem_image_of_mem _ hq
    have heq : S = S.image (dilate c) :=
      Finset.eq_of_subset_of_card_le hsub Finset.card_image_le
    intro p hp
    rw [heq]
    exact Finset.mem_image_of_mem _ hp
  have hiter : ∀ p ∈ S, ∀ n : ℕ, (dilate c)^[n] p ∈ S := by
    intro p hp n
    induction n with
    | zero => simpa using hp
    | succ n ih => rw [Function.iterate_succ_apply']; exact hstable _ ih
  -- The orbit of an element of `S` stays in the finite set `S`, so the element is fixed by an
  -- iterate of the dilation, and is therefore zero.
  have hzero : ∀ p ∈ S, p = 0 := by
    intro p hp
    have hmem : p ∈ Ideal.span {(X : K[X])} := by
      rw [← hspan]; exact Ideal.subset_span hp
    obtain ⟨i, j, hij, hfix⟩ :=
      Finite.exists_ne_map_eq_of_infinite
        (fun n : ℕ => (⟨(dilate c)^[n] p, hiter p hp n⟩ : {x // x ∈ S}))
    have hfix' : (dilate c)^[i] p = (dilate c)^[j] p := by simpa using hfix
    have key : ∀ i m : ℕ, m ≠ 0 → (dilate c)^[i + m] p = (dilate c)^[i] p → p = 0 := by
      intro i m hm h
      rw [Function.iterate_add_apply] at h
      exact eq_zero_of_dilate_iterate_eq_self hc hroot hm
        (((dilate_injective hc).iterate i) h) hmem
    rcases le_total i j with hle | hle
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
      exact key i m (by omega) hfix'.symm
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hle
      exact key j m (by omega) hfix'
  -- A generating set of zeros generates the zero ideal, but `X ≠ 0`.
  rw [Ideal.span_eq_bot.2 hzero] at hspan
  have hx : (X : K[X]) ∈ Ideal.span {(X : K[X])} := Ideal.subset_span rfl
  rw [← hspan, Ideal.mem_bot] at hx
  exact X_ne_zero hx

end Dilate

/-! ### The dilation factor -/

/-- The scalar `2`, in the universe-`u` copy of `ℚ` used for the counterexample. -/
def dilationFactor : ULift.{u} ℚ := ULift.up 2

/-- The dilation factor corresponds to `2 : ℚ` under `ULift.ringEquiv`. -/
theorem ringEquiv_dilationFactor :
    (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ) dilationFactor = 2 := rfl

/-- The dilation factor is nonzero. -/
theorem dilationFactor_ne_zero : (dilationFactor.{u}) ≠ 0 := by
  intro h
  have h2 := congrArg (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ) h
  rw [ringEquiv_dilationFactor, map_zero] at h2
  exact absurd h2 (by norm_num)

/-- No positive power of the dilation factor is `1`. -/
theorem dilationFactor_pow_eq_one (n : ℕ) (h : (dilationFactor.{u}) ^ n = 1) : n = 0 := by
  have h3 := congrArg (ULift.ringEquiv : ULift.{u} ℚ ≃+* ℚ) h
  rw [map_pow, map_one, ringEquiv_dilationFactor] at h3
  have h4 : ((2 ^ n : ℕ) : ℚ) = ((1 : ℕ) : ℚ) := by push_cast; exact h3
  simpa using Nat.pow_eq_one.1 (Nat.cast_injective h4)

/-! ### No functorial choice of generators -/

/-- **A strictly functorial choice of generators.** For every commutative ring `A` in the fixed
universe and every finitely generated ideal `I ⊆ A`, a finite generating set of `I`, such that
every chosen generator of `IB` is the image under `φ : A → B` of a chosen generator of `I`.

This is the hypothesis under which the library's maps of complexes between Čech complexes —
`Stacks.CechRingBaseChange.complexMap`, which transports the whole family, and
`Cech.cechRestrict`, which restricts to an ordered subfamily — assemble into the data (1)–(3) of
tag 099D with `K(A, I)` the Čech complex of the chosen family. -/
structure FunctorialGenerators where
  /-- The chosen finite generating set. -/
  gens (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) : Finset A
  /-- The chosen set generates the ideal. -/
  span_gens (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    Ideal.span (gens A I hI : Set A) = I
  /-- Every chosen generator of `J = IB` is the image of a chosen generator of `I`. -/
  gens_map {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hI : I.FG)
    (J : Ideal B) (hJ : J.FG) (hφ : J = I.map φ) {b : B} (hb : b ∈ gens B J hJ) :
    ∃ a ∈ gens A I hI, b = φ a

/-- **There is no strictly functorial choice of generators.** Applying the transport hypothesis to
the dilation `X ↦ 2X`, an automorphism of the pair `(ℚ[X], (X))`, would make the chosen generating
set of `(X)` stable under dilation, which `exists_notMem_dilate_image` forbids. -/
theorem FunctorialGenerators.elim (G : FunctorialGenerators.{u}) : False := by
  have hc : dilationFactor.{u} ≠ 0 := dilationFactor_ne_zero
  have hI : (Ideal.span {(X : (ULift.{u} ℚ)[X])}).FG := Submodule.fg_span (Set.finite_singleton _)
  obtain ⟨p, hp, hp'⟩ := exists_notMem_dilate_image hc dilationFactor_pow_eq_one
    (G.gens (ULift.{u} ℚ)[X] (Ideal.span {X}) hI) (G.span_gens _ _ hI)
  obtain ⟨a, ha, hpa⟩ := G.gens_map (dilate dilationFactor.{u}) (Ideal.span {X}) hI
    (Ideal.span {X}) hI (map_dilate_span_X hc).symm hp
  exact hp' a ha hpa

/-- The type of strictly functorial choices of generators is empty. -/
theorem isEmpty_functorialGenerators : IsEmpty FunctorialGenerators.{u} :=
  ⟨FunctorialGenerators.elim⟩

/-- **No functorial choice of a finite generating family**, in the `Fin r`-indexed form that
`Stacks.CechRingBaseChange.complexMap` consumes. There is no assignment, to every pair of a ring
and a finitely generated ideal, of a finite generating family, such that every member of the
family chosen for `(B, IB)` is the `φ`-image of a member of the family chosen for `(A, I)`.

In particular there is none with `family B (I.map φ) = φ ∘ family A I`, which is what
`Stacks.CechRingBaseChange.complexMap` requires of its two families, and none with the family for
`(B, IB)` an ordered subfamily of `φ ∘ family A I`, which is what a composite with
`Cech.cechRestrict` would require. -/
theorem not_transportedFamily
    (rank : (A : Type u) → [CommRing A] → (I : Ideal A) → I.FG → ℕ)
    (family : (A : Type u) → [CommRing A] → (I : Ideal A) → (hI : I.FG) → Fin (rank A I hI) → A)
    (hspan : ∀ (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG),
      Ideal.span (Set.range (family A I hI)) = I)
    (hfamily : ∀ (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (hI : I.FG)
      (J : Ideal B) (hJ : J.FG), J = I.map φ →
      ∀ i : Fin (rank B J hJ), ∃ j : Fin (rank A I hI),
        family B J hJ i = φ (family A I hI j)) :
    False := by
  classical
  refine FunctorialGenerators.elim
    { gens := fun A inst I hI => Finset.image (family A I hI) Finset.univ
      span_gens := ?_
      gens_map := ?_ }
  · intro A inst I hI
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hspan A I hI
  · intro A B instA instB φ I hI J hJ hφ b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨j, hj⟩ := hfamily A B φ I hI J hJ hφ i
    exact ⟨family A I hI j, Finset.mem_image_of_mem _ (Finset.mem_univ _), hj⟩

/-! ### The two choice-free routes -/

/-- **The ideal `IB` is strictly larger than the image of `I`.** For the inclusion of `K[X]` into
`K[X][Y]` as the constants and `I = (X)`, the element `Y · X` lies in `IB` but is not the image of
an element of `I`: the image consists of the polynomials of degree zero in `Y`, and `Y · X` has a
nonzero coefficient in degree one. -/
theorem notMem_image_X_mul_C_X {K : Type u} [CommRing K] [Nontrivial K] :
    (X * C (X : K[X]) : (K[X])[X]) ∉
      (C : K[X] →+* (K[X])[X]) '' (Ideal.span {(X : K[X])} : Set K[X]) := by
  rintro ⟨p, -, hp⟩
  have h1 : (X * C (X : K[X]) : (K[X])[X]).coeff 1 = (X : K[X]) := by
    simp
  rw [← hp, Polynomial.coeff_C] at h1
  simp only [ite_eq_right (one_ne_zero (α := ℕ))] at h1
  exact X_ne_zero h1.symm

/-- **The whole ideal is not transported along a ring map.** There is no containment
`IB ⊆ φ(I)` of sets in general, so the extended alternating Čech complex on the whole of `I`
admits neither of the library's two maps of complexes — base change, which keeps the index set,
and restriction to an ordered subfamily — onto the extended alternating Čech complex on the whole
of `IB`. -/
theorem not_subset_image_of_map :
    ¬ ∀ (A B : Type u) [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A), I.FG →
        ((I.map φ : Ideal B) : Set B) ⊆ φ '' (I : Set A) := by
  intro h
  refine notMem_image_X_mul_C_X (K := ULift.{u} ℚ) (h _ _ C
    (Ideal.span {(X : (ULift.{u} ℚ)[X])}) (Submodule.fg_span (Set.finite_singleton _)) ?_)
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span rfl))

/-- **Two finite generating families of an ideal need not have a common generating subfamily.**
In a field, `{1}` and `{2}` both generate the unit ideal and their only common subfamily is
empty, which generates the zero ideal. So the finite generating families of a finitely generated
ideal, which `Cech.cechRestrict` turns into a diagram of Čech complexes pointing from the larger
family to the smaller one, are directed under inclusion but not codirected: the opposite poset,
over which that diagram is a colimit, is not filtered. -/
theorem not_exists_common_generating_subFinset :
    ¬ ∀ (A : Type u) [CommRing A] (I : Ideal A) (S T : Finset A),
        Ideal.span (S : Set A) = I → Ideal.span (T : Set A) = I →
        ∃ U : Finset A, U ⊆ S ∧ U ⊆ T ∧ Ideal.span (U : Set A) = I := by
  intro h
  have h1 : Ideal.span ((({1} : Finset (ULift.{u} ℚ)) : Set (ULift.{u} ℚ))) = ⊤ := by
    simp
  have h2 : Ideal.span ((({dilationFactor.{u}} : Finset (ULift.{u} ℚ)) :
      Set (ULift.{u} ℚ))) = ⊤ := by
    simpa using
      Ideal.span_singleton_eq_top.mpr (isUnit_iff_ne_zero.mpr dilationFactor_ne_zero.{u})
  have hne : (1 : ULift.{u} ℚ) ≠ dilationFactor.{u} := fun he =>
    one_ne_zero (dilationFactor_pow_eq_one 1 (by rw [pow_one, ← he]))
  obtain ⟨U, hU1, hU2, hU⟩ := h (ULift.{u} ℚ) ⊤ {1} {dilationFactor.{u}} h1 h2
  have hUempty : U = ∅ := by
    refine Finset.subset_empty.mp ?_
    have hsub := Finset.subset_inter hU1 hU2
    rwa [Finset.singleton_inter_of_notMem (by simpa using hne)] at hsub
  rw [hUempty] at hU
  simp only [Finset.coe_empty, Ideal.span_empty] at hU
  exact absurd hU bot_ne_top

end Stacks.FunctorialCechFamily

end
