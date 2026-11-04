module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.RingTheory.GradedAlgebra.Radical

/-!
# An external direct sum of rings is a graded ring

Mathlib has two unrelated pictures of a graded ring.

* The **internal** one, `GradedRing 𝒜` for a family `𝒜 : ι → σ` of additive subgroups of a ring
  `A` that decomposes `A`. Every statement about homogeneous ideals — `Ideal.IsHomogeneous`,
  `HomogeneousIdeal.irrelevant`, `ProjectiveSpectrum`, and so graded prime avoidance — is stated
  in this picture.
* The **external** one, `DirectSum.GRing A` for a family of types `A : ι → Type*`, which makes
  `⨁ i, A i` a ring. Every graded ring this repository *builds* is of this kind: the section ring
  `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` of Stacks Tag 01CV is
  `Stacks.GradedSections.sectionRing`, an external direct sum of `Hom`-groups in a monoidal
  category.

Nothing connects them, so a graded ring built the second way cannot be fed to a lemma stated the
first way. This file supplies the bridge: the images of the structure maps `DirectSum.of A i` are
additive subgroups of `⨁ i, A i` which grade it, and the decomposition is the identity in
disguise.

## Main definitions

* `Stacks.ExternalGrading.summand`: the `i`-th summand of `⨁ i, A i`, as an `AddSubgroup`.
* `Stacks.ExternalGrading.summandEquiv`: the summand is additively `A i`.

## Main results

* `Stacks.ExternalGrading.gradedRing`: `GradedRing (summand A)` for any `DirectSum.GRing A`.
  This is the instance that makes the internal-picture API available on an external direct sum.
* `Stacks.ExternalGrading.isHomogeneousElem_of`: every `DirectSum.of A i a` is a homogeneous
  element, and `Stacks.ExternalGrading.mem_summand_iff` is the converse — a homogeneous element of
  degree `i` is `DirectSum.of A i a`. Together these let a statement produced by a lemma about
  homogeneous elements be read back as a statement about one summand, which is what every
  consumer of this file does.
* `Stacks.ExternalGrading.mem_irrelevant_iff_degree_zero_eq_zero`: membership in the irrelevant
  ideal is the vanishing of the degree-zero component, with no `GradedRing.proj` in sight.

## Implementation notes

`AddSubgroup` satisfies both `AddSubmonoidClass` (needed by `GradedRing`) and `AddSubgroupClass`
(needed by graded prime avoidance), so one choice of carrier serves both.

`decompose'` is taken to be `DirectSum.map` of the summand equivalences rather than
`DirectSum.congrAddEquiv` of them: the two are the same map, but `DirectSum.map` has the
computation rule `DirectSum.map_of` stated for it, and `congrAddEquiv` has no application lemma
at this pin, so the inverse proofs are two rewrites each instead of a `change` through the
bundled equivalence.

Both inverse proofs go by `DirectSum.induction_on` rather than by extensionality of additive
maps: the two composites are additive, but `decompose'` is a bare function in the
`DirectSum.Decomposition` structure, so there is no bundled map to apply `AddMonoidHom.ext` to.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV) — the graded ring whose
  carrier is an external direct sum, and the reason this bridge is needed.
-/

@[expose] public section

open DirectSum

universe u v

namespace Stacks.ExternalGrading

section Carrier

variable {ι : Type u} [DecidableEq ι] {A : ι → Type v} [∀ i, AddCommGroup (A i)]

/-- **The `i`-th summand of an external direct sum, as an additive subgroup of the sum.** This is
the carrier of the internal grading that `Stacks.ExternalGrading.gradedRing` puts on
`⨁ i, A i`. -/
def summand (A : ι → Type v) [∀ i, AddCommGroup (A i)] (i : ι) : AddSubgroup (⨁ i, A i) :=
  (DirectSum.of A i).range

/-- An element lies in the `i`-th summand exactly when it is `DirectSum.of A i a` for some
`a : A i`. -/
theorem mem_summand_iff {i : ι} {x : ⨁ i, A i} :
    x ∈ summand A i ↔ ∃ a : A i, DirectSum.of A i a = x := Iff.rfl

/-- The element `DirectSum.of A i a` lies in the `i`-th summand. -/
theorem of_mem_summand (i : ι) (a : A i) : DirectSum.of A i a ∈ summand A i := ⟨a, rfl⟩

/-- Every element of a single summand is a homogeneous element. -/
theorem isHomogeneousElem_of (i : ι) (a : A i) :
    SetLike.IsHomogeneousElem (summand A) (DirectSum.of A i a) :=
  ⟨i, of_mem_summand i a⟩

/-- **The `i`-th summand is additively `A i`.** The forward map is `DirectSum.of A i` and the
inverse is evaluation at `i`. -/
def summandEquiv (A : ι → Type v) [∀ i, AddCommGroup (A i)] (i : ι) : A i ≃+ summand A i where
  toFun a := ⟨DirectSum.of A i a, of_mem_summand i a⟩
  invFun x := (x : ⨁ i, A i) i
  left_inv a := DirectSum.of_eq_same i a
  right_inv := by
    rintro ⟨x, a, rfl⟩
    exact Subtype.ext (congrArg (DirectSum.of A i) (DirectSum.of_eq_same i a))
  map_add' a b := Subtype.ext (map_add (DirectSum.of A i) a b)

/-- The image of `a : A i` under `Stacks.ExternalGrading.summandEquiv` is `DirectSum.of A i a`. -/
@[simp] theorem summandEquiv_apply_coe (i : ι) (a : A i) :
    ((summandEquiv A i a : summand A i) : ⨁ i, A i) = DirectSum.of A i a := rfl

/-- The componentwise decomposition of an external direct sum into its summands. -/
noncomputable def decomposeHom (A : ι → Type v) [∀ i, AddCommGroup (A i)] :
    (⨁ i, A i) →+ ⨁ i, summand A i :=
  DirectSum.map fun i ↦ (summandEquiv A i).toAddMonoidHom

/-- The decomposition sends `DirectSum.of A i a` to the element of the `i`-th summand it
defines. -/
@[simp] theorem decomposeHom_of (i : ι) (a : A i) :
    decomposeHom A (DirectSum.of A i a) =
      DirectSum.of (fun i ↦ summand A i) i (summandEquiv A i a) :=
  DirectSum.map_of _ i a

end Carrier

section Ring

variable {ι : Type u} [DecidableEq ι] [AddMonoid ι] {A : ι → Type v}
  [∀ i, AddCommGroup (A i)] [DirectSum.GRing A]

/-- **The summands are multiplicatively graded.** `DirectSum.of_zero_one` places the unit in
degree `0` and `DirectSum.of_mul_of` is the degree additivity. -/
instance gradedMonoid : SetLike.GradedMonoid (summand A) where
  one_mem := ⟨GradedMonoid.GOne.one, DirectSum.of_zero_one A⟩
  mul_mem := by
    rintro i j x y ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨GradedMonoid.GMul.mul a b, (DirectSum.of_mul_of a b).symm⟩

/-- **The summands decompose the sum.** -/
noncomputable instance decomposition : DirectSum.Decomposition (summand A) where
  decompose' := decomposeHom A
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i a => rw [decomposeHom_of, DirectSum.coeAddMonoidHom_of, summandEquiv_apply_coe]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i a =>
        obtain ⟨b, hb⟩ := a.2
        rw [DirectSum.coeAddMonoidHom_of, ← hb, decomposeHom_of]
        exact congrArg _ (Subtype.ext hb)
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **An external direct sum of additive groups with a graded ring structure is a graded ring in
Mathlib's internal sense**, graded by the images of its own structure maps. -/
noncomputable instance gradedRing : GradedRing (summand A) where

/-- The canonical decomposition sends `DirectSum.of A i a` to the element of the `i`-th summand
it defines. -/
theorem decompose_of (i : ι) (a : A i) :
    DirectSum.decompose (summand A) (DirectSum.of A i a) =
      DirectSum.of (fun i ↦ summand A i) i (summandEquiv A i a) :=
  decomposeHom_of i a

/-- **The homogeneous components, computed.** The `i`-th piece of the canonical decomposition of
`x` is its `i`-th coordinate, re-embedded by `DirectSum.of`. This is the workhorse of every
homogeneity proof about an ideal of `⨁ i, A i`: `Ideal.IsHomogeneous` asks that each
`DirectSum.decompose` component of a member be a member, and this turns that into a statement
about one coordinate. -/
theorem coe_decompose_apply (x : ⨁ i, A i) (i : ι) :
    ((DirectSum.decompose (summand A) x i : summand A i) : ⨁ i, A i) =
      DirectSum.of A i (x i) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j a =>
      rw [decompose_of]
      by_cases h : i = j
      · subst h
        rw [DirectSum.of_eq_same, DirectSum.of_eq_same, summandEquiv_apply_coe]
      · have h1 := DirectSum.of_eq_of_ne (β := fun k ↦ (summand A k : Type _)) j i
          (summandEquiv A j a) h
        have h2 := DirectSum.of_eq_of_ne j i a h
        rw [h1, h2]
        simp
  | add x y hx hy =>
      rw [DirectSum.decompose_add, DFinsupp.add_apply, AddSubgroup.coe_add, hx, hy,
        DFinsupp.add_apply, map_add]

/-- **The degree-zero component, computed.** -/
theorem proj_zero_apply (x : ⨁ i, A i) :
    GradedRing.proj (summand A) 0 x = DirectSum.of A 0 (x 0) :=
  coe_decompose_apply x 0

end Ring

section Irrelevant

variable {ι : Type u} [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι]
  [CanonicallyOrderedAdd ι] {A : ι → Type v} [∀ i, AddCommGroup (A i)] [DirectSum.GRing A]

/-- **Membership in the irrelevant ideal is the vanishing of the degree-zero component.** -/
theorem mem_irrelevant_iff_degree_zero_eq_zero (x : ⨁ i, A i) :
    x ∈ HomogeneousIdeal.irrelevant (summand A) ↔ x 0 = 0 := by
  rw [HomogeneousIdeal.mem_irrelevant_iff, proj_zero_apply]
  exact ⟨fun h ↦ by simpa using congrArg (fun z : ⨁ i, A i ↦ z 0) h, fun h ↦ by rw [h]; simp⟩

/-- **A summand of positive degree lies in the irrelevant ideal.** This is the hypothesis
`I ≤ S₊` that graded prime avoidance asks of its ideal, in the form it is checked. -/
theorem of_mem_irrelevant {i : ι} (hi : i ≠ 0) (a : A i) :
    DirectSum.of A i a ∈ HomogeneousIdeal.irrelevant (summand A) := by
  classical
  rw [mem_irrelevant_iff_degree_zero_eq_zero, DirectSum.of_eq_of_ne i 0 a (Ne.symm hi)]

end Irrelevant

end Stacks.ExternalGrading

end
