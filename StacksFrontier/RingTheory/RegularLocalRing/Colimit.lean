module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import Mathlib.Algebra.Category.Ring.FilteredColimits

public import StacksFrontier.RingTheory.RegularLocalRing.Basic

@[expose] public section

universe u w

/-!
# A Noetherian directed colimit of regular local rings is regular

Let `(R i, φ i i')` be a directed system of local rings whose transition maps are local ring maps
and let `R = colim_i R i`. If every `R i` is a regular local ring and `R` is Noetherian, then `R`
is a regular local ring. The Noetherian hypothesis cannot be dropped: `colim_n k[x^{1/2ⁿ}]`
localized at its maximal ideal is a directed colimit of discrete valuation rings along local
inclusions which is a non-Noetherian valuation ring.

## Main results

* `CommRingCat.isRegularLocalRing_pt_of_forall_isRegularLocalRing_of_forall_isLocalHom`: the
  colimit of a directed system of regular local rings with local transition maps is a regular local
  ring as soon as it is Noetherian.
* `Stacks.RegularLocalRing.DirectedColimit.isRegularLocalRing_quotient_span_singleton`: for `A`
  regular local and `x ∈ 𝔪_A ∖ 𝔪_A²`, the quotient `A ⧸ xA` is a regular local ring.

## Implementation notes

A directed system of rings is a functor `F : J ⥤ CommRingCat` out of a nonempty directed preorder
`J`, and "`R` is the colimit" is an arbitrary cocone `c` together with `IsColimit c`, so `R` is
`c.pt` and the canonical maps `R i → R` are the legs `c.ι.app i`. Locality of a transition map is
`IsLocalHom (F.map u).hom`. `IsRegularLocalRing` bundles `IsLocalRing` and `IsNoetherianRing`, so
that `c.pt` is local is part of the conclusion, and the Noetherian hypothesis is the instance
`[IsNoetherianRing c.pt]`.

The hypothesis `[Small.{u} J]` makes `IsColimit c` in `CommRingCat.{u}` the colimit computed on
elements, and the statement is false without it: a directed system of `Type u` fields whose union
is larger than every type in `Type u` has only cocones with subsingleton vertex, and the zero ring
then satisfies the universal property while being Noetherian and not local.

The proof works with element-level data, `Stacks.RegularLocalRing.DirectedColimit.ColimitData`: a
family of ring maps `f j : A j →+* R` out of a directed system `(A j, φ)` whose legs are jointly
surjective and such that an element killed by a leg is killed by a transition map. These two
properties pass to the quotient systems `A j ⧸ (x j)`, which come with no colimit cocone.

## References

* [StacksProject 07DX](https://stacks.math.columbia.edu/tag/07DX)
* [StacksProject 00NQ](https://stacks.math.columbia.edu/tag/00NQ), for the regularity of
  `A ⧸ xA`
* [StacksProject 00NP](https://stacks.math.columbia.edu/tag/00NP), for a regular local ring being
  a domain
* [StacksProject 00NU](https://stacks.math.columbia.edu/tag/00NU), for the converse step
-/

open CategoryTheory Limits IsLocalRing

@[expose] public section



namespace Stacks.RegularLocalRing.DirectedColimit

open Stacks.RegularLocalRing.SpanFinrank

/-! ### Commutative algebra of the induction step -/

/-- A Noetherian local ring whose maximal ideal needs no generators is regular. -/
private theorem isRegularLocalRing_of_spanFinrank_maximalIdeal_eq_zero {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (h : (maximalIdeal R).spanFinrank = 0) :
    IsRegularLocalRing R :=
  IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ <| by
    rw [h]; simpa using ringKrullDim_nonneg_of_nontrivial (R := R)

/-- Quotienting a local ring by an element of its maximal ideal leaves a nontrivial ring. -/
private theorem nontrivial_quotient_span_singleton {R : Type*} [CommRing R] [IsLocalRing R]
    {x : R} (hx : x ∈ maximalIdeal R) : Nontrivial (R ⧸ Ideal.span {x}) :=
  Submodule.Quotient.nontrivial_iff.mpr fun h =>
    (mem_maximalIdeal x).mp hx (Ideal.span_singleton_eq_top.mp h)

/-- A local ring map carries the `n`-th power of the maximal ideal into the `n`-th power of the
maximal ideal. -/
private theorem map_maximalIdeal_pow_le {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (g : R →+* S) [IsLocalHom g] (n : ℕ) :
    (maximalIdeal R ^ n).map g ≤ maximalIdeal S ^ n := by
  rw [Ideal.map_pow]
  exact pow_le_pow_left' (map_maximalIdeal_le g) n

/-- In a Noetherian local ring whose maximal ideal needs at least one generator there is an
element of the maximal ideal outside its square. -/
private theorem exists_notMem_sq {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hd : (maximalIdeal R).spanFinrank ≠ 0) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 := by
  by_contra h
  push Not at h
  have hle : maximalIdeal R ≤ maximalIdeal R • maximalIdeal R := fun x hx => by
    rw [Ideal.smul_eq_mul, ← pow_two]; exact h x hx
  refine hd ?_
  rw [Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
    (IsNoetherian.noetherian _) hle (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])]
  simp

/-- Quotienting a Noetherian local ring by an element of `𝔪 ∖ 𝔪²` lowers the number of generators
of the maximal ideal. -/
private theorem spanFinrank_maximalIdeal_quotient_succ_le {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {x : R} [IsLocalRing (R ⧸ Ideal.span {x})] (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) :
    (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank :=
  spanFinrank_maximalIdeal_succ_le_of_surjective (Ideal.Quotient.mk (Ideal.span {x}))
    Ideal.Quotient.mk_surjective hx hx2
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x))

/-- In a domain, an element outside the square of the maximal ideal is a nonzerodivisor. -/
private theorem mem_nonZeroDivisors_of_notMem_sq {R : Type*} [CommRing R] [IsLocalRing R]
    [IsDomain R] {x : R} (hx2 : x ∉ maximalIdeal R ^ 2) : x ∈ nonZeroDivisors R :=
  mem_nonZeroDivisors_of_ne_zero fun h => hx2 (h ▸ Submodule.zero_mem _)

/-- If `A` is a regular local ring and `x ∈ 𝔪_A` does not lie in `𝔪_A²`, then `A ⧸ xA` is a
regular local ring. -/
public theorem isRegularLocalRing_quotient_span_singleton {A : Type*} [CommRing A]
    [IsRegularLocalRing A] {x : A} (hx : x ∈ maximalIdeal A) (hx2 : x ∉ maximalIdeal A ^ 2) :
    IsRegularLocalRing (A ⧸ Ideal.span {x}) := by
  have hdom : IsDomain A := IsRegularLocalRing.isDomain A
  have : Nontrivial (A ⧸ Ideal.span {x}) := nontrivial_quotient_span_singleton hx
  have : IsLocalRing (A ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hdim : ringKrullDim (A ⧸ Ideal.span {x}) + 1 = ringKrullDim A :=
    ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_notMem_sq hx2) hx
  have hsf := spanFinrank_maximalIdeal_quotient_succ_le hx hx2
  have hle : ((maximalIdeal (A ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞)
        + ((1 : ℕ) : WithBot ℕ∞)
      ≤ ringKrullDim (A ⧸ Ideal.span {x}) + ((1 : ℕ) : WithBot ℕ∞) := by
    rw [Nat.cast_one, hdim, ← IsRegularLocalRing.spanFinrank_maximalIdeal]
    exact_mod_cast hsf
  exact IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _
    (ENat.WithBot.add_le_add_natCast_right_iff.mp hle)

/-- The elements above a fixed one in a directed preorder are again directed. -/
private theorem isDirectedOrder_subtype_le {J : Type*} [Preorder J] [IsDirectedOrder J] (i : J) :
    IsDirectedOrder {j : J // i ≤ j} :=
  ⟨fun a b => by
    obtain ⟨k, hak, hbk⟩ := exists_ge_ge a.1 b.1
    exact ⟨⟨k, a.2.trans hak⟩, hak, hbk⟩⟩

/-! ### Directed systems presented on elements -/

/-- The data making a commutative ring `R` the colimit of a directed system `(A j, φ)` of regular
local rings along local ring maps, read on elements: the maps `f j : A j →+* R` are compatible
with the transitions, jointly surjective, and an element of some `A j` killed by `f j` is killed
by a transition map out of `j`. -/
private structure ColimitData {R : Type u} [CommRing R] {J : Type w} [Preorder J]
    {A : J → Type u} [∀ j, CommRing (A j)]
    (φ : ∀ ⦃i j : J⦄, i ≤ j → (A i →+* A j)) (f : ∀ j, A j →+* R) : Prop where
  /-- The transition maps compose. -/
  comp : ∀ ⦃i j k : J⦄ (h₁ : i ≤ j) (h₂ : j ≤ k) (a : A i), φ h₂ (φ h₁ a) = φ (h₁.trans h₂) a
  /-- The maps to `R` are compatible with the transition maps. -/
  fac : ∀ ⦃i j : J⦄ (h : i ≤ j) (a : A i), f j (φ h a) = f i a
  /-- The maps to `R` are jointly surjective. -/
  surj : ∀ x : R, ∃ (j : J) (a : A j), f j a = x
  /-- An element killed by its map to `R` is killed by a transition map. -/
  ker : ∀ (j : J) (a : A j), f j a = 0 → ∃ (k : J) (h : j ≤ k), φ h a = 0
  /-- The transition maps are local ring maps. -/
  isLocalHom : ∀ ⦃i j : J⦄ (h : i ≤ j), IsLocalHom (φ h)
  /-- The members are regular local rings. -/
  regular : ∀ j, IsRegularLocalRing (A j)

namespace ColimitData

variable {R : Type u} [CommRing R] {J : Type w} [Preorder J] [IsDirectedOrder J]
  {A : J → Type u} [∀ j, CommRing (A j)] {φ : ∀ ⦃i j : J⦄, i ≤ j → (A i →+* A j)}
  {f : ∀ j, A j →+* R}

/-- Two elements of `R` are the images of elements of one and the same member. -/
private theorem exists_common (d : ColimitData φ f) (x y : R) :
    ∃ (j : J) (a b : A j), f j a = x ∧ f j b = y := by
  obtain ⟨i, a, ha⟩ := d.surj x
  obtain ⟨j, b, hb⟩ := d.surj y
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  exact ⟨k, φ hik a, φ hjk b, by rw [d.fac, ha], by rw [d.fac, hb]⟩

/-- Every leg of the presentation is a local ring map. -/
private theorem isLocalHom_leg (d : ColimitData φ f) (j : J) : IsLocalHom (f j) := by
  refine ⟨fun a hu => ?_⟩
  obtain ⟨u, hu'⟩ := hu.exists_right_inv
  obtain ⟨m, b, hb⟩ := d.surj u
  obtain ⟨k, hjk, hmk⟩ := exists_ge_ge j m
  obtain ⟨l, hkl, hl⟩ := d.ker k (φ hjk a * φ hmk b - 1) (by
    rw [map_sub, map_mul, d.fac, d.fac, hb, map_one, hu', sub_self])
  rw [map_sub, map_mul, map_one, sub_eq_zero, d.comp, d.comp] at hl
  have := d.isLocalHom (hjk.trans hkl)
  exact isUnit_of_map_unit _ _ (IsUnit.of_mul_eq_one _ hl)

omit [IsDirectedOrder J] in
/-- The colimit of a nonempty directed system of local rings is nontrivial. -/
private theorem nontrivial [Nonempty J] (d : ColimitData φ f) : Nontrivial R := by
  refine ⟨1, 0, fun h => ?_⟩
  obtain ⟨k, hk, hzero⟩ := d.ker (Classical.arbitrary J) 1 (by rw [map_one, ← h])
  have := (d.regular k).toIsLocalRing
  rw [map_one] at hzero
  exact one_ne_zero hzero

/-- The colimit of a directed system of local rings along local ring maps is local. -/
private theorem isLocalRing [Nonempty J] (d : ColimitData φ f) : IsLocalRing R := by
  have := d.nontrivial
  refine IsLocalRing.of_nonunits_add fun x y hx hy => ?_
  obtain ⟨j, a, b, ha, hb⟩ := d.exists_common x y
  have := (d.regular j).toIsLocalRing
  have := d.isLocalHom_leg j
  have hab : f j (a + b) = x + y := by rw [map_add, ha, hb]
  refine fun h => (mem_maximalIdeal (a + b)).mp (add_mem ?_ ?_)
    (isUnit_of_map_unit (f j) _ (hab ▸ h))
  · exact (mem_maximalIdeal a).mpr fun hu => hx (ha ▸ hu.map (f j))
  · exact (mem_maximalIdeal b).mpr fun hu => hy (hb ▸ hu.map (f j))

/-- The colimit of a directed system of domains is a domain. -/
private theorem isDomain [Nonempty J] (d : ColimitData φ f) : IsDomain R := by
  have := d.nontrivial
  refine (isDomain_iff_noZeroDivisors_and_nontrivial R).mpr ⟨⟨fun {x y} hxy => ?_⟩, inferInstance⟩
  obtain ⟨j, a, b, ha, hb⟩ := d.exists_common x y
  obtain ⟨k, hjk, hk⟩ := d.ker j (a * b) (by rw [map_mul, ha, hb, hxy])
  have := d.regular k
  have := IsRegularLocalRing.isDomain (A k)
  rw [map_mul, mul_eq_zero] at hk
  rcases hk with hk | hk
  · exact Or.inl (by rw [← ha, ← d.fac hjk a, hk, map_zero])
  · exact Or.inr (by rw [← hb, ← d.fac hjk b, hk, map_zero])

/-- If the image in `R` of `a : A j` lies in the ideal generated by the image of `a₀ : A i`, then
already `a` lies in the ideal generated by the image of `a₀` at some later stage `k`. -/
private theorem exists_mem_span_singleton (d : ColimitData φ f) {i j : J} (a₀ : A i) {a : A j}
    (h : f j a ∈ Ideal.span {f i a₀}) :
    ∃ (k : J) (hjk : j ≤ k) (hik : i ≤ k), φ hjk a ∈ Ideal.span {φ hik a₀} := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h
  obtain ⟨m, b, hb⟩ := d.surj r
  obtain ⟨k₀, hjk₀, hmk₀⟩ := exists_ge_ge j m
  obtain ⟨k, hk₀, hik⟩ := exists_ge_ge k₀ i
  have hjk : j ≤ k := hjk₀.trans hk₀
  have hmk : m ≤ k := hmk₀.trans hk₀
  obtain ⟨l, hkl, hl⟩ := d.ker k (φ hjk a - φ hmk b * φ hik a₀) (by
    rw [map_sub, map_mul, d.fac, d.fac, d.fac, hb, hr, sub_self])
  rw [map_sub, map_mul, d.comp, d.comp, d.comp, sub_eq_zero] at hl
  exact ⟨l, hjk.trans hkl, hik.trans hkl,
    Ideal.mem_span_singleton'.mpr ⟨φ (hmk.trans hkl) b, hl.symm⟩⟩

/-- The transition maps of the system quotiented by `a₀ : A i`: at stages `j ≤ k` above `i`, the
map `A j ⧸ (a₀) → A k ⧸ (a₀)` induced by `φ`. -/
private def quotientMap (d : ColimitData φ f) {i : J} (a₀ : A i) ⦃j k : {j : J // i ≤ j}⦄
    (h : j ≤ k) : (A j.1 ⧸ Ideal.span {φ j.2 a₀}) →+* (A k.1 ⧸ Ideal.span {φ k.2 a₀}) :=
  Ideal.quotientMap _ (φ (h : j.1 ≤ k.1)) <| by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, d.comp]
    exact Ideal.mem_span_singleton_self _

/-- The legs of the system quotiented by `a₀ : A i`: the maps `A j ⧸ (a₀) → R ⧸ (f i a₀)` induced
by the legs `f j`. -/
private def quotientLeg (d : ColimitData φ f) {i : J} (a₀ : A i) (j : {j : J // i ≤ j}) :
    (A j.1 ⧸ Ideal.span {φ j.2 a₀}) →+* (R ⧸ Ideal.span {f i a₀}) :=
  Ideal.quotientMap _ (f j.1) <| by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, d.fac]
    exact Ideal.mem_span_singleton_self _

omit [IsDirectedOrder J] in
private theorem quotientMap_mk (d : ColimitData φ f) {i : J} (a₀ : A i)
    ⦃j k : {j : J // i ≤ j}⦄ (h : j ≤ k) (a : A j.1) :
    d.quotientMap a₀ h (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (φ (h : j.1 ≤ k.1) a) := rfl

omit [IsDirectedOrder J] in
private theorem quotientLeg_mk (d : ColimitData φ f) {i : J} (a₀ : A i)
    (j : {j : J // i ≤ j}) (a : A j.1) :
    d.quotientLeg a₀ j (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (f j.1 a) := rfl

section IsLocalRing

variable [IsLocalRing R]

/-- If the image in `R` of `a : A j` lies in `𝔪 ∖ 𝔪²`, then `A j ⧸ aA j` is a regular local
ring. -/
private theorem isRegularLocalRing_quotient_of_map (d : ColimitData φ f) {j : J} {a : A j}
    (h : f j a ∈ maximalIdeal R) (h2 : f j a ∉ maximalIdeal R ^ 2) :
    IsRegularLocalRing (A j ⧸ Ideal.span {a}) := by
  have := d.regular j
  have := d.isLocalHom_leg j
  exact isRegularLocalRing_quotient_span_singleton
    ((maximalIdeal_comap (f j)).le (Ideal.mem_comap.mpr h))
    fun hm => h2 (map_maximalIdeal_pow_le (f j) 2 (Ideal.mem_map_of_mem _ hm))

/-- If `a₀ : A i` has image `x = f i a₀` in `𝔪 ∖ 𝔪²`, then the quotients `A j ⧸ (a₀)` at the
stages `j ≥ i` present `R ⧸ xR` as a directed colimit of regular local rings along local ring
maps. -/
private theorem quotient (d : ColimitData φ f) {i : J} (a₀ : A i)
    (h : f i a₀ ∈ maximalIdeal R) (h2 : f i a₀ ∉ maximalIdeal R ^ 2) :
    ColimitData (A := fun j : {j : J // i ≤ j} => A j.1 ⧸ Ideal.span {φ j.2 a₀})
      (d.quotientMap a₀) (d.quotientLeg a₀) := by
  have hreg : ∀ j : {j : J // i ≤ j}, IsRegularLocalRing (A j.1 ⧸ Ideal.span {φ j.2 a₀}) :=
    fun j => d.isRegularLocalRing_quotient_of_map (by rwa [d.fac]) (by rwa [d.fac])
  refine ⟨?_, ?_, ?_, ?_, ?_, hreg⟩
  · intro j k l h₁ h₂ b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [quotientMap_mk, quotientMap_mk, quotientMap_mk, d.comp]
  · intro j k hjk b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [quotientMap_mk, quotientLeg_mk, quotientLeg_mk, d.fac]
  · intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨j, a, ha⟩ := d.surj r
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact ⟨⟨k, hik⟩, Ideal.Quotient.mk _ (φ hjk a), by rw [quotientLeg_mk, d.fac, ha]⟩
  · intro j b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [quotientLeg_mk, Ideal.Quotient.eq_zero_iff_mem] at hb
    obtain ⟨k, hjk, hik, hk⟩ := d.exists_mem_span_singleton a₀ hb
    refine ⟨⟨k, hik⟩, hjk, ?_⟩
    rwa [quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]
  · intro j k hjk
    have := (d.regular j.1).toIsLocalRing
    have := (d.regular k.1).toIsLocalRing
    have := (hreg k).toIsLocalRing
    have := d.isLocalHom (hjk : j.1 ≤ k.1)
    have hmk : IsLocalHom (Ideal.Quotient.mk (Ideal.span {φ k.2 a₀})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    refine ⟨fun b hb => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [quotientMap_mk] at hb
    exact (isUnit_of_map_unit (φ (hjk : j.1 ≤ k.1)) a (isUnit_of_map_unit _ _ hb)).map _

end IsLocalRing

end ColimitData

/-! ### The induction -/

/-- A Noetherian local ring presented as the colimit of a directed system of regular local rings
along local ring maps, on element-level data, whose maximal ideal is generated by at most `n`
elements, is a regular local ring. -/
private theorem isRegularLocalRing_of_colimitData :
    ∀ (n : ℕ) {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
      {J : Type w} [Preorder J] [IsDirectedOrder J] [Nonempty J]
      {A : J → Type u} [∀ j, CommRing (A j)]
      {φ : ∀ ⦃i j : J⦄, i ≤ j → (A i →+* A j)} {f : ∀ j, A j →+* R},
      ColimitData φ f → (maximalIdeal R).spanFinrank ≤ n → IsRegularLocalRing R := by
  intro n
  induction n with
  | zero =>
      intro R _ _ _ J _ _ _ A _ φ f _ hn
      exact isRegularLocalRing_of_spanFinrank_maximalIdeal_eq_zero (Nat.le_zero.mp hn)
  | succ n ih =>
      intro R _ _ _ J _ _ _ A _ φ f d hn
      by_cases h0 : (maximalIdeal R).spanFinrank = 0
      · exact isRegularLocalRing_of_spanFinrank_maximalIdeal_eq_zero h0
      obtain ⟨x, hx, hx2⟩ := exists_notMem_sq h0
      obtain ⟨i, a₀, rfl⟩ := d.surj x
      have := isDirectedOrder_subtype_le i
      have : Nonempty {j : J // i ≤ j} := ⟨⟨i, le_rfl⟩⟩
      have dq := d.quotient a₀ hx hx2
      have := dq.isLocalRing
      have := d.isDomain
      have hdrop := spanFinrank_maximalIdeal_quotient_succ_le hx hx2
      exact isRegularLocalRing_of_nonZeroDivisor R _ (mem_nonZeroDivisors_of_notMem_sq hx2)
        (ih dq (by omega))

/-! ### Colimit cocones -/

/-- For an index preorder in the universe of the rings, a colimit cocone over a directed system of
regular local rings along local ring maps in `CommRingCat` presents its vertex on elements. -/
private theorem colimitData_of_isColimit {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    {F : J ⥤ CommRingCat.{u}} (hreg : ∀ j : J, IsRegularLocalRing (F.obj j))
    (hloc : ∀ ⦃i j : J⦄ (u : i ⟶ j), IsLocalHom (F.map u).hom)
    {c : Cocone F} (hc : IsColimit c) :
    ColimitData (R := (c.pt : Type u)) (A := fun j => (F.obj j : Type u))
      (fun _ _ h => (F.map (homOfLE h)).hom) (fun j => (c.ι.app j).hom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, hreg⟩
  · intro j k l h₁ h₂ a
    have hmap : F.map (homOfLE (h₁.trans h₂)) = F.map (homOfLE h₁) ≫ F.map (homOfLE h₂) := by
      rw [← F.map_comp]; congr 1
    exact congr($hmap.symm a)
  · intro j k h a
    exact congr($(c.w (homOfLE h)) a)
  · intro x
    obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep _ hc x
    exact ⟨j, y, hy⟩
  · intro j a ha
    obtain ⟨k, u, v, huv⟩ := hc.eq_iff.mp
      (show (c.ι.app j).hom a = (c.ι.app j).hom 0 by rw [ha, map_zero])
    have h1 : (F.map u).hom a = (F.map v).hom (0 : F.obj j) := huv
    exact ⟨k, leOfHom u, by rw [show (F.map (homOfLE (leOfHom u))).hom a = (F.map u).hom a from rfl,
      h1, map_zero]⟩
  · intro j k h
    exact hloc (homOfLE h)

/-- The colimit of a directed system of regular local rings whose transition maps are local ring
maps is a regular local ring as soon as it is Noetherian. -/
public theorem solution
    {J : Type w} [Preorder J] [IsDirectedOrder J] [Nonempty J] [Small.{u} J]
    {F : J ⥤ CommRingCat.{u}}
    (hreg : ∀ j : J, IsRegularLocalRing (F.obj j))
    (hloc : ∀ ⦃i j : J⦄ (u : i ⟶ j), IsLocalHom (F.map u).hom)
    {c : Cocone F} (hc : IsColimit c) [IsNoetherianRing c.pt] :
    IsRegularLocalRing c.pt := by
  classical
  let _ : Preorder (Shrink.{u} J) := Preorder.lift (equivShrink J).symm
  have o : Shrink.{u} J ≃o J :=
    { toEquiv := (equivShrink J).symm, map_rel_iff' := Iff.rfl }
  have : IsDirectedOrder (Shrink.{u} J) := ⟨fun a b => by
    obtain ⟨k, h1, h2⟩ := exists_ge_ge (o a) (o b)
    exact ⟨o.symm k, by simpa using o.symm.map_rel_iff.mpr h1,
      by simpa using o.symm.map_rel_iff.mpr h2⟩⟩
  have : Nonempty (Shrink.{u} J) := ⟨equivShrink J (Classical.arbitrary J)⟩
  have hloc' : ∀ ⦃a b : Shrink.{u} J⦄ (v : a ⟶ b),
      IsLocalHom ((o.equivalence.functor ⋙ F).map v).hom := fun _ _ v =>
    hloc (o.equivalence.functor.map v)
  have data := colimitData_of_isColimit (F := o.equivalence.functor ⋙ F)
    (fun j => hreg (o j)) hloc' (hc.whiskerEquivalence o.equivalence)
  have : IsLocalRing (c.pt : Type u) := data.isLocalRing
  exact isRegularLocalRing_of_colimitData (R := (c.pt : Type u)) _ data le_rfl

end Stacks.RegularLocalRing.DirectedColimit

end

open CategoryTheory Limits

@[expose] public section

namespace CommRingCat

/-- Let `F : J ⥤ CommRingCat` be a directed system `(R i, φ i i')` of commutative rings over a
nonempty, `u`-small directed preorder `J`, and let `c` be a colimit cocone on `F`, so that `c.pt`
is `colim_i R i`. If every `R i` is a regular local ring, every transition map is a local ring map,
and the colimit is Noetherian, then the colimit is a regular local ring — in particular it is
local, its maximal ideal being the colimit of the maximal ideals of the `R i`. -/
@[stacks 07DX "The directed system is a functor on a nonempty `u`-small directed preorder together
  with an arbitrary colimit cocone, as in 0AS7; locality of a transition map is `IsLocalHom` of
  the underlying ring homomorphism; `IsRegularLocalRing` of the colimit includes the assertion
  that it is local. See the module docstring."]
public theorem isRegularLocalRing_pt_of_forall_isRegularLocalRing_of_forall_isLocalHom
    {J : Type w} [Preorder J] [IsDirectedOrder J] [Nonempty J] [Small.{u} J]
    {F : J ⥤ CommRingCat.{u}}
    (hreg : ∀ j : J, IsRegularLocalRing (F.obj j))
    (hloc : ∀ ⦃i j : J⦄ (u : i ⟶ j), IsLocalHom (F.map u).hom)
    {c : Cocone F} (hc : IsColimit c) [IsNoetherianRing c.pt] :
    IsRegularLocalRing c.pt :=
  Stacks.RegularLocalRing.DirectedColimit.solution (F := F) (J := J) hreg hloc hc

end CommRingCat

end
