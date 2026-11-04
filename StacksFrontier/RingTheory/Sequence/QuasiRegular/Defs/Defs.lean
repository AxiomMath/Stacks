module

public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-regular sequences

Let `R` be a commutative ring, let `M` be an `R`-module and let `f_1, …, f_c ∈ R` be a finite
sequence of elements, generating the ideal `J = (f_1, …, f_c)`. There is a canonical map of graded
`(R/J)[X_1, …, X_c]`-modules
`Φ_M : (R/J)[X_1, …, X_c] ⊗_{R/J} (M/JM) → ⨁_{n ≥ 0} J^n M / J^{n+1} M`, determined by
`X_1^{e_1} ⋯ X_c^{e_c} ⊗ m̄ ↦ f_1^{e_1} ⋯ f_c^{e_c} m mod J^{e_1 + … + e_c + 1} M`, and it is
always surjective. The sequence `f_1, …, f_c` is *`M`-quasi-regular* when `Φ_M` is an isomorphism,
and *quasi-regular* when this holds for `M = R`, in which case the isomorphism reads
`(R/J)[X_1, …, X_c] ≅ ⨁_{n ≥ 0} J^n / J^{n+1}`.

## Main definitions

* `RingTheory.Sequence.IsQuasiRegular M rs`: the sequence `rs` of elements of `R` is
  `M`-quasi-regular, i.e. the canonical map `Φ_M` above is an isomorphism.

## Main results

* `RingTheory.Sequence.isQuasiRegular_map_iff`: quasi-regularity of the image of a list in an
  `R`-algebra, in terms of the canonical map indexed by the original list.

## References

* [Stacks Project, Tag 061P](https://stacks.math.columbia.edu/tag/061P)
* [Stacks Project, Tag 061N](https://stacks.math.columbia.edu/tag/061N)
-/

@[expose] public section

namespace RingTheory.Sequence

/-- A sequence `rs = f_1, …, f_c` of elements of a commutative ring `R` is **`M`-quasi-regular**,
for an `R`-module `M`, if the canonical map of graded `(R/J)[X_1, …, X_c]`-modules
`Φ_M : (R/J)[X_1, …, X_c] ⊗_{R/J} (M/JM) → ⨁_{n ≥ 0} J^n M / J^{n+1} M`,
`X_1^{e_1} ⋯ X_c^{e_c} ⊗ m̄ ↦ f_1^{e_1} ⋯ f_c^{e_c} m mod J^{e_1 + … + e_c + 1} M`, is an
isomorphism, where `J = (f_1, …, f_c)`. An `R`-quasi-regular sequence is called simply a
*quasi-regular sequence*. -/
@[stacks 061P,
  ega "0 15.1.7" "quasi-regular half",
  ega "0 15.1.4" "M-quasi-regular",
  ega "0 15.2.2" "special case",
  ega "IV 19.5.1",
  ega "IV 19.5.5.2" "more general"]
def IsQuasiRegular {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (rs : List R) : Prop :=
  Function.Bijective (quasiRegularCanonicalMap (M := M) fun i : Fin rs.length => rs[i])

/-- Quasi-regularity of the image of a list in an `R`-algebra `S`, read off the canonical map
indexed by `Fin rs.length`. -/
public theorem isQuasiRegular_map_iff {R : Type*} [CommRing R] (rs : List R) (S : Type*)
    [CommRing S] [Algebra R S] (N : Type*) [AddCommGroup N] [Module S N] :
    IsQuasiRegular N (rs.map (algebraMap R S)) ↔
      Function.Bijective
        (quasiRegularCanonicalMap (M := N) (fun i : Fin rs.length => algebraMap R S rs[i])) :=
  bijective_quasiRegularCanonicalMap_congr (List.length_map ..) _ _ fun _ ↦ by simp

end RingTheory.Sequence

end
