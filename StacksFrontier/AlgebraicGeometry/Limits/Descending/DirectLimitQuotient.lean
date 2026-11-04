module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Quotients of a direct limit of rings

Let `A` be a directed system of commutative rings and let `p` be an ideal of its direct limit.
Pulling `p` back to every component gives a directed system of quotient rings, and its direct
limit is canonically isomorphic to the quotient of the original direct limit by `p`.

## Main definitions

* `Ring.DirectLimit.quotientTransitionMap`: the transition map induced on the componentwise
  quotients.
* `Ring.DirectLimit.toQuotient`: the comparison map from the direct limit of the componentwise
  quotients to the quotient of the direct limit.
* `Ring.DirectLimit.quotientDirectLimitEquiv`: the canonical isomorphism from the direct limit of
  the componentwise quotients to the quotient of the direct limit, bundled with the equation
  describing it on the image of every component.

## Implementation notes

The statement is given for an arbitrary ideal, not only for a prime one.
-/

@[expose] public section

namespace Ring.DirectLimit

universe u v

variable {ι : Type u} [Preorder ι]
variable (A : ι → Type v) [∀ i, CommRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j)

/-- The map induced on the componentwise quotients by the pullbacks of an ideal of the direct
limit. -/
noncomputable def quotientTransitionMap
    (p : Ideal (Ring.DirectLimit A (f · · ·))) (i j : ι) (h : i ≤ j) :
    A i ⧸ p.comap (Ring.DirectLimit.of A (f · · ·) i) →+*
      A j ⧸ p.comap (Ring.DirectLimit.of A (f · · ·) j) :=
  Ideal.quotientMap _ (f i j h) fun x hx => by simpa using hx

variable [Nonempty ι] [IsDirectedOrder ι]
variable [DirectedSystem A fun i j h => f i j h]

/-- The comparison map from the direct limit of the componentwise quotients to the quotient of
the direct limit. -/
noncomputable def toQuotient
    (p : Ideal (Ring.DirectLimit A (f · · ·))) :
    Ring.DirectLimit
        (fun i => A i ⧸ p.comap (Ring.DirectLimit.of A (f · · ·) i))
        (quotientTransitionMap A f p · · ·) →+*
      Ring.DirectLimit A (f · · ·) ⧸ p :=
  Ring.DirectLimit.lift _ _ _
    (fun i => Ideal.quotientMap p (Ring.DirectLimit.of A (f · · ·) i) le_rfl)
    (by
      intro i j hij x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp [quotientTransitionMap])

omit [Nonempty ι] [IsDirectedOrder ι] [DirectedSystem A fun i j h => f i j h] in
/-- The comparison map sends the class of `x : A i` to the class of its image in the direct
limit. -/
@[simp] lemma toQuotient_of_mk
    (p : Ideal (Ring.DirectLimit A (f · · ·))) (i : ι) (x : A i) :
    toQuotient A f p
        (Ring.DirectLimit.of _ (quotientTransitionMap A f p · · ·) i
          (Ideal.Quotient.mk _ x)) =
      Ideal.Quotient.mk p (Ring.DirectLimit.of A (f · · ·) i x) := by
  simp [toQuotient]

omit [DirectedSystem A fun i j h => f i j h] in
/-- The comparison map is injective. -/
lemma toQuotient_injective
    (p : Ideal (Ring.DirectLimit A (f · · ·))) :
    Function.Injective (toQuotient A f p) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro z hz
  induction z using Ring.DirectLimit.induction_on with
  | ih i x =>
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [toQuotient_of_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (show x ∈ p.comap _ from hz), map_zero]

omit [DirectedSystem A fun i j h => f i j h] in
/-- The comparison map is surjective. -/
lemma toQuotient_surjective
    (p : Ideal (Ring.DirectLimit A (f · · ·))) :
    Function.Surjective (toQuotient A f p) := by
  intro z
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction z using Ring.DirectLimit.induction_on with
  | ih i x =>
      exact ⟨Ring.DirectLimit.of _ (quotientTransitionMap A f p · · ·) i
        (Ideal.Quotient.mk _ x), toQuotient_of_mk A f p i x⟩

/-- The canonical equivalence between the direct limit of the componentwise quotients and the
quotient of the direct limit, characterised by its value on the image of every component. -/
noncomputable def quotientDirectLimitEquiv
    (p : Ideal (Ring.DirectLimit A (f · · ·))) :
    { e : Ring.DirectLimit
          (fun i => A i ⧸ p.comap (Ring.DirectLimit.of A (f · · ·) i))
          (quotientTransitionMap A f p · · ·) ≃+*
          Ring.DirectLimit A (f · · ·) ⧸ p //
      ∀ (i : ι) (x : A i),
        e (Ring.DirectLimit.of _ (quotientTransitionMap A f p · · ·) i
          (Ideal.Quotient.mk _ x)) =
          Ideal.Quotient.mk p (Ring.DirectLimit.of A (f · · ·) i x) } :=
  ⟨RingEquiv.ofBijective (toQuotient A f p)
    ⟨toQuotient_injective A f p, toQuotient_surjective A f p⟩, toQuotient_of_mk A f p⟩

end Ring.DirectLimit

end
