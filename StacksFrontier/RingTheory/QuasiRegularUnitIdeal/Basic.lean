module

public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Defs.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-regularity is vacuous where the generated ideal is the unit ideal

Let `R` be a commutative ring, `M` an `R`-module and `f = f_0, …, f_{c-1}` a sequence in `R`
generating the ideal `J`. Quasi-regularity of `f` on `M`, Stacks tag 061P, is bijectivity of the
comparison map `Φ_M : (R/J)[X_0, …, X_{c-1}] ⊗_{R/J} (M/JM) → ⨁_{n ≥ 0} J^n M / J^{n+1} M` of
tag 061N. When `J = R` the source of `Φ_M` is a module over the zero ring `R/J`, hence zero, and
`Φ_M` is always surjective; so `Φ_M` is bijective for *every* module `M` and *every* sequence with
that span. Quasi-regularity therefore asserts nothing at all about such a sequence.

This is the obstruction a proof of Stacks tag 063U has to route around. Tag 063D part (1) asks of
a regular ideal sheaf that near each point of `Supp(O_X/J)` there be generators forming a regular
sequence, and `Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularSequenceOn` — a condition on
sheaves on the chosen open — holds exactly when, at *every* point of that open, each generator is a
nonzerodivisor modulo its predecessors. At a point outside the immersed subscheme the generators
span the whole stalk, so by the result below the quasi-regularity hypothesis of tag 063S is empty
there and supplies no such nonzerodivisor. The pointwise commutative algebra available for tag 063U
— tag 0CEP (`Koszul.quasiRegular_and_h1Regular_baseChange_of_quotient_flat`), tag 061S
(`RingTheory.Sequence.IsRegular.of_isQuasiRegular_of_mem_maximalIdeal`) and tag 0470
(`Module.Flat.isRegular_and_flat_quotient_ofList_smul_of_isRegular_maximalIdeal`) — all require the
generators to lie in the maximal ideal, so none of them reaches those points. The open set has to
be shrunk, which is what tags 061L and 062Y do in the source.

## Main results

* `isQuasiRegular_of_jid_eq_top`: a sequence spanning the unit ideal is `M`-quasi-regular, for
  every `M`.
* `isQuasiRegular_of_isUnit_mem`: in particular a sequence one of whose terms is a unit.
* `isQuasiRegular_cons_one`: the explicit witness `t, 1`, quasi-regular for every `t`, in
  particular for a zero divisor.

## Implementation notes

Only injectivity has to be proved: surjectivity of the comparison map is unconditional, and is
`quasiRegularCanonicalMap_surjective`. Injectivity is read off from the vanishing of the source
`Source M f = (R/J)[X] ⊗_{R/J} (M/JM)`.

That vanishing deliberately avoids the scalars `qrRbar f = R ⧸ Jid f`. Deducing it from
`Subsingleton (qrRbar f)` — by `Module.subsingleton`, or by `1 = 0` and `one_smul` — requires the
instance `Module (qrRbar f) (Source M f)`, and that search does not terminate inside the heartbeat
budget: the canonical module structure of the tensor product and `TensorProduct.leftModule` through
the `qrRbar f`-algebra `(R/J)[X]` are both candidates, and comparing them unfolds a polynomial ring
over a quotient ring. The argument is made on the right-hand factor instead: `Jid f = ⊤` gives
`Jid f • ⊤ = ⊤` and hence `Subsingleton (qrMbar M f)` by `Submodule.Quotient.subsingleton_iff`, and
`eq_zero_of_subsingleton_right` kills the tensor product by induction on it. Its ring and factors
are then read off `Source M f` by unification, with no instance search at all.

The target is *not* shown to be subsingleton, although it is: each graded piece is an `R ⧸ Jid f`
module by `Tcomp_RbarModule`, but the direct sum carries no such instance, and surjectivity makes
the detour unnecessary.

## What is not done

Nothing here proves any part of Stacks tag 063U, and nothing here is about schemes. This file
records a property of the definition of quasi-regularity, namely that it is empty on the locus
where the ideal is the unit ideal; it does not supply the shrinking that tag 063U needs, and no
`stacks` attribute is attached.

## References

* [Stacks Project, Equation 10.69.0.1 (Tag 061N)](https://stacks.math.columbia.edu/tag/061N)
* [Stacks Project, Definition 10.69.1 (Tag 061P)](https://stacks.math.columbia.edu/tag/061P)
* [Stacks Project, Definition 31.20.1 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
* [Stacks Project, Lemma 31.23.4 (Tag 063U)](https://stacks.math.columbia.edu/tag/063U)
-/

@[expose] public section

open RingTheory.Sequence

namespace Stacks.AlgebraicGeometry.QuasiRegularUnitIdeal

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A tensor product whose right-hand factor is zero is zero. -/
theorem eq_zero_of_subsingleton_right {S A N : Type*} [CommRing S] [AddCommMonoid A] [Module S A]
    [AddCommMonoid N] [Module S N] (hN : ∀ n : N, n = 0) (x : TensorProduct S A N) : x = 0 := by
  induction x with
  | zero => rfl
  | tmul a n => rw [hN n, TensorProduct.tmul_zero]
  | add p q hp hq => rw [hp, hq, add_zero]

/-- **A sequence generating the unit ideal is quasi-regular on every module.** The comparison map
of Stacks tag 061N has source `(R/J)[X] ⊗_{R/J} (M/JM)`, which vanishes because `JM = M`, and it is
always surjective. -/
@[ega "0 15.1.12" "(ii)", sga "1 II 4.14" "more general"]
theorem isQuasiRegular_of_jid_eq_top {rs : List R}
    (h : Jid (fun i : Fin rs.length => rs[i]) = ⊤) : IsQuasiRegular M rs := by
  have htop : Jid (fun i : Fin rs.length => rs[i]) • (⊤ : Submodule R M) = ⊤ := by
    rw [h, Submodule.top_smul]
  have hsub : Subsingleton (qrMbar M (fun i : Fin rs.length => rs[i])) :=
    Submodule.Quotient.subsingleton_iff.mpr htop
  refine ⟨fun a b _ => ?_, quasiRegularCanonicalMap_surjective _⟩
  exact (eq_zero_of_subsingleton_right (fun n => hsub.allEq n 0) a).trans
    (eq_zero_of_subsingleton_right (fun n => hsub.allEq n 0) b).symm

/-- **A sequence one of whose terms is a unit is quasi-regular on every module.** This is the shape
in which the vacuity is met at a point outside the immersed subscheme of Stacks tag 063U: there
some generator of the defining ideal is a unit in the stalk. -/
@[ega "0 15.1.12" "(ii)", sga "1 II 4.14" "If J=A"]
theorem isQuasiRegular_of_isUnit_mem {rs : List R} {u : R} (hu : IsUnit u) (hmem : u ∈ rs) :
    IsQuasiRegular M rs := by
  refine isQuasiRegular_of_jid_eq_top (Ideal.eq_top_of_isUnit_mem _ ?_ hu)
  obtain ⟨i, hi, hrs⟩ := List.mem_iff_getElem.mp hmem
  exact Ideal.subset_span ⟨⟨i, hi⟩, hrs⟩

/-- **The vacuity exhibited.** For every `t` the two-term sequence `t, 1` is quasi-regular on `R`.
Taking `t` a zero divisor gives a quasi-regular sequence whose first term is not a nonzerodivisor,
so quasi-regularity alone cannot produce the nonzerodivisor condition that
`Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularSequenceOn` demands at every point. -/
@[ega "0 15.1.12" "(ii)"]
theorem isQuasiRegular_cons_one (t : R) : IsQuasiRegular R [t, 1] :=
  isQuasiRegular_of_isUnit_mem isUnit_one (by simp)

end Stacks.AlgebraicGeometry.QuasiRegularUnitIdeal

end
