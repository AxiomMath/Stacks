module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.Valued.WithVal
public import StacksCore.Tactic.StacksAttribute

/-!
# Unramified cusp forms on `GL₂` of the adeles

Let `K` be a field. A *place* `v` of `K` is a nontrivial valuation subring of `K`; write `K_v`
for the completion of `K` at `v` and `O_v ⊆ K_v` for its ring of integers. The adele ring
`A = ∏'_v K_v` is the restricted product of the `K_v` relative to the `O_v`, and `O = ∏_v O_v`
is its subring of integral adeles. An unramified cusp form on `GL₂(A)` with values in `Λ` is a
function `f : GL₂(A) → Λ` invariant under right multiplication by `GL₂(K)`, invariant under
left multiplication by `GL₂(O)`, and whose constant term along the unipotent `(1, z; 0, 1)`,
integrated over `A` modulo `K`, vanishes.

## Main definitions

* `Stacks.Adeles.Place` — a place of `K`, that is, a nontrivial valuation subring of `K`.
* `Stacks.Adeles.Place.completion` and `Stacks.Adeles.Place.integers` — the completion `K_v`
  and its ring of integers `O_v`.
* `Stacks.Adeles.AdeleRing` — the adele ring `A = ∏'_v K_v`.
* `Stacks.Adeles.integralAdeles` — the subring `O = ∏_v O_v` of `A`.
* `Stacks.Adeles.principalAdeles` — the subring of `A` of diagonal adeles, that is, the image
  of `K`.
* `Stacks.Adeles.IsUnramifiedCuspForm` — the three defining conditions.

## Implementation notes

Places are taken to be the nontrivial valuation subrings of `K`. For `K = k(X)` the function
field of a geometrically irreducible smooth projective curve over a finite field `k` these are
exactly the local rings of `X` at its closed points, which is the identification behind the
statement that a place of `K` is the same thing as a closed point of `X`. The curve plays no
further role in the definition, so everything below is stated for an arbitrary field `K`.

`GL₂(K)` and `GL₂(O)` enter through `principalAdeles` and `integralAdeles` and the induced maps
`Matrix.GeneralLinearGroup.map` into `GL₂(A)`. There is deliberately no diagonal ring map
`K → A`: that map exists only because every element of `K` is integral at all but finitely many
places, which is a theorem about curves and not available for a general field. The subring
`principalAdeles` of diagonal adeles is its image, is defined with no such obligation, and for
a global function field is isomorphic to `K`; so `GL (Fin 2) (principalAdeles K)` is `GL₂(K)`
acting on `GL₂(A)`.

The constant term is stated without measure theory. By the first condition the integrand
`z ↦ f (x * (1, z; 0, 1))` is invariant under translation by `K`, and by the second it is
invariant under translation by an open additive subgroup `U` of `A` — namely by those `z` with
`(1, z; 0, 1) ∈ x⁻¹ GL₂(O) x` — so it factors through the finite group `A / (K + U)`. The
normalized integral over `A` modulo `K` is therefore the sum over a transversal of `A / (K + U)`
divided by the order of that group, which is a power of the characteristic and hence invertible
in the usual coefficient rings. Vanishing of the integral is thus equivalent to vanishing of
the finite sum, for one and hence for every admissible `U` and transversal, and that is what is
required below. In particular no invertibility hypothesis on `Λ` is needed, and `Λ` need only
be an additive commutative monoid.

## References

* [Stacks Project, Tag 03VS](https://stacks.math.columbia.edu/tag/03VS)
-/

@[expose] public noncomputable section

open Matrix
open scoped RestrictedProduct

universe u w

namespace Stacks.Adeles

/-- A place of a field `K`: a valuation subring of `K` other than `K` itself. -/
public def Place (K : Type u) [Field K] : Type u := {A : ValuationSubring K // A ≠ ⊤}

namespace Place

variable {K : Type u} [Field K]

/-- The completion `K_v` of `K` at a place `v`. -/
public abbrev completion (v : Place K) : Type u := v.1.valuation.Completion

/-- The ring of integers `O_v ⊆ K_v`, the valuation subring of the extended valuation. -/
public abbrev integers (v : Place K) : ValuationSubring v.completion := Valued.v.valuationSubring

/-- The canonical map `K → K_v` from a field into its completion at a place. -/
public def coeRingHom (v : Place K) : K →+* v.completion :=
  UniformSpace.Completion.coeRingHom.comp (WithVal.equiv v.1.valuation).symm.toRingHom

end Place

/-- The adele ring `A = ∏'_v K_v` of a field `K`: the restricted product of the completions
`K_v` with respect to the rings of integers `O_v`. -/
public abbrev AdeleRing (K : Type u) [Field K] : Type u :=
  Πʳ v : Place K, [v.completion, v.integers]

variable {K : Type u} [Field K]

/-- The integral adeles `O = ∏_v O_v`, as a subring of the adele ring. -/
public def integralAdeles (K : Type u) [Field K] : Subring (AdeleRing K) where
  carrier := {x | ∀ v, x v ∈ v.integers}
  one_mem' _ := one_mem _
  zero_mem' _ := zero_mem _
  mul_mem' hx hy v := by simpa using mul_mem (hx v) (hy v)
  add_mem' hx hy v := by simpa using add_mem (hx v) (hy v)
  neg_mem' hx v := by simpa using neg_mem (hx v)

/-- An adele is integral exactly when each of its components is. -/
@[simp]
public theorem mem_integralAdeles {x : AdeleRing K} :
    x ∈ integralAdeles K ↔ ∀ v, x v ∈ v.integers := Iff.rfl

/-- The principal adeles: those adeles all of whose components come from a single element of
`K`. This subring is the image of the diagonal embedding of `K`. -/
public def principalAdeles (K : Type u) [Field K] : Subring (AdeleRing K) where
  carrier := {x | ∃ c : K, ∀ v, x v = v.coeRingHom c}
  one_mem' := ⟨1, fun v => by simp⟩
  zero_mem' := ⟨0, fun v => by simp⟩
  mul_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c * d, fun v => by simp [hc v, hd v]⟩
  add_mem' := by
    rintro x y ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, fun v => by simp [hc v, hd v]⟩
  neg_mem' := by
    rintro x ⟨c, hc⟩
    exact ⟨-c, fun v => by simp [hc v]⟩

/-- An adele is principal exactly when it is the diagonal image of an element of `K`. -/
@[simp]
public theorem mem_principalAdeles {x : AdeleRing K} :
    x ∈ principalAdeles K ↔ ∃ c : K, ∀ v, x v = v.coeRingHom c := Iff.rfl

/-- An unramified cusp form on `GL₂(A)` with values in `Λ`: a function on `GL₂(A)` invariant
under right multiplication by `GL₂(K)` and under left multiplication by `GL₂(O)`, whose
constant term along the unipotent `(1, z; 0, 1)` over `A` modulo `K` vanishes.

See [Stacks Project, Tag 03VS](https://stacks.math.columbia.edu/tag/03VS). -/
@[stacks 03VS]
public structure IsUnramifiedCuspForm {Λ : Type w} [AddCommMonoid Λ]
    (f : GL (Fin 2) (AdeleRing K) → Λ) : Prop where
  /-- Part (1): invariance under right multiplication by `GL₂(K)`. -/
  right_invariant (x : GL (Fin 2) (AdeleRing K)) (γ : GL (Fin 2) (principalAdeles K)) :
    f (x * GeneralLinearGroup.map (principalAdeles K).subtype γ) = f x
  /-- Part (2): invariance under left multiplication by `GL₂(O)`. -/
  left_invariant (x : GL (Fin 2) (AdeleRing K)) (u : GL (Fin 2) (integralAdeles K)) :
    f (GeneralLinearGroup.map (integralAdeles K).subtype u * x) = f x
  /-- Part (3): for every `x`, the constant term of `z ↦ f (x * (1, z; 0, 1))` over `A` modulo
  `K` vanishes, expressed as the vanishing of the sum over a transversal `s` of `A / (K + U)`
  for an open additive subgroup `U` of `A` leaving the integrand invariant. -/
  vanishing_constant_term (x : GL (Fin 2) (AdeleRing K)) (U : AddSubgroup (AdeleRing K))
      (hU : IsOpen (U : Set (AdeleRing K)))
      (hinv : ∀ z : AdeleRing K, ∀ y ∈ U,
        f (x * GeneralLinearGroup.upperRightHom (z + y)) =
          f (x * GeneralLinearGroup.upperRightHom z))
      (s : Finset (AdeleRing K))
      (hs : ∀ a : AdeleRing K, ∃! z ∈ s, a - z ∈ (principalAdeles K).toAddSubgroup ⊔ U) :
    ∑ z ∈ s, f (x * GeneralLinearGroup.upperRightHom z) = 0

end Stacks.Adeles

end
