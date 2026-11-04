module

public import StacksFrontier.RingTheory.Koszul.PowProIsoDerived

/-!
# The two Koszul systems of modules are pro-isomorphic in the derived category

Let `f₁, …, f_r` be elements of a commutative ring `R`, let `K_m` be the Koszul differential
graded algebra with `d ξᵢ = fᵢ ^ m` and fix `t ≥ 1`. Over the inverse system of Koszul algebras
there are two inverse systems of left differential graded modules, the system `({}_{t+n}K_t)` and
the system `(K_{t+n} ⊗_R K_t)`, assembled in
`StacksFrontier/RingTheory/Koszul/PowModuleSystems.lean`. This file exhibits them as
*pro-isomorphic in the derived category*, which is the second step of the proof of Tag 0GZJ: the
step that lets Tag 0GZI replace `K_n ⊗_R K_t` by `K_t`.

The data is the one assembled in `StacksFrontier/RingTheory/Koszul/PowProIsoDerived.lean`: the
indices are the multiples `t, 2t, 3t, …` of `t` measured from the base `t` of the system, the
maps in one direction are the comparison maps of Tag 0GZ7 followed by the comparison of the two
presentations of `K_n ⊗_R K_t` over `K_N`, and the maps in the other direction are the
multiplication maps `μ : K_m ⊗_R K_t → K_t` read as semilinear homomorphisms. The two
composition identities are
`DifferentialGraded.StrictModuleSystem.RegularComparison.fwdBwd` and
`DifferentialGraded.StrictModuleSystem.RegularComparison.bwdFwd` applied to the two composites of
Tag 0GZ7.

## Main definitions

* `Koszul.powProIsoIdx`: the indices of the pro-isomorphism, the multiples of `t`.
* `Koszul.powCrossStructure`: the presentation of `K_{t + t(2i+1)} ⊗_R K_t` as a differential
  graded algebra over `K_{t + t(2i+2)}` that the comparison map of Tag 0GZ7 uses, and
  `Koszul.powCrossStructure_eq`, its identification with the presentation the system of modules
  provides.
* `Koszul.powProIsoFwd` and `Koszul.powProIsoBwd`: the maps of the pro-isomorphism.
* `Koszul.powProIsoDerived`: **the two Koszul systems are pro-isomorphic in the derived
  category.**

## Main results

* `Koszul.powProIsoFwdBwd` and `Koszul.powProIsoBwdFwd`: the two composition identities.

## Implementation notes

*Why a presentation has to be named.* A system of modules asks for its `n`-th term to be the
module `K_{t+n} ⊗_R K_t` read over `K_{t+n}` through `a ↦ a ⊗ 1`, and for the comparison with the
term at a larger index to be a restriction of scalars along the transition homomorphism. Tag
0GZ7 instead produces a map into `K_n ⊗_R K_t` read over `K_N` through the single homomorphism
`K_N → K_n → K_n ⊗_R K_t`. Restriction along a composite is the composite of the restrictions on
the nose here, but the graded opposite of a composite is only *equal* to the composite of the
graded opposites, by `DifferentialGradedAlgebra.oppHom_comp`; `Koszul.powCrossStructure_eq` is
that equation and `DifferentialGraded.StrictModuleSystem.RegularComparison.crossRestrHom`, the
identity of `K_n ⊗_R K_t`, is the resulting homomorphism. No transport along an equality of
objects occurs.

*The indices.* The multiples of `t` are used because Tag 0GZ7 asks for a gap of at least `t`
between the two indices it relates, and every multiple of `t` is of the form
`t + (index of the system)`, so no transport along an equality of natural numbers — hence none
along an equality of Koszul algebras — is needed.

*Everything is spelled once.* The two composition identities mention a component
`(S.restrComp h h').hom.app X` of the natural isomorphism comparing a two-step restriction of
scalars with a one-step one. The derived restriction functors are produced by a universal
property, so that component cannot be evaluated: two spellings of it are decided only by
unfolding the universal property, which does not terminate in reasonable time, and the only
feasible decision is that the two are the same term. Every ingredient of these statements is
therefore written exactly as `DifferentialGraded.ProIsoDerived` writes it, and that fixes three
choices that would otherwise be free:

* the inverse system of Koszul algebras is `(Koszul.powStrictAlgebraSystem f ht).toAlgebraSystem`
  throughout, which is also how `Koszul.powRestrictedModuleSystem` and
  `Koszul.powBaseTensorModuleSystem` name it, rather than the equal
  `Koszul.powAlgebraSystem f ht`;
* the indices are the named function `Koszul.powProIsoIdx`, not `fun j => t * j`, so that
  `idx c` leaves no beta-redex inside the component;
* the inequalities between the indices are written as `DifferentialGraded.ProIsoDerived` writes
  them: `Nat.le_succ` with both indices passed explicitly, so that the indices are literally
  `2 * i + 1` and `2 * i + 2` rather than `Nat.succ (2 * i + 1)`, and the named
  `DifferentialGraded.proIsoIdx_even_le_even` and `DifferentialGraded.proIsoIdx_odd_le_odd`; and
  the objects at which the component is taken are passed explicitly to
  `DifferentialGraded.StrictModuleSystem.RegularComparison.fwdBwd` and
  `DifferentialGraded.StrictModuleSystem.RegularComparison.bwdFwd` instead of being left to
  unification.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7) supplies the comparison
  maps.
* [Stacks Project, Tag 0GZI](https://stacks.math.columbia.edu/tag/0GZI) is what a
  pro-isomorphism in the derived category is for.
* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ) is the statement whose
  second step this is.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Koszul

open DifferentialGraded DifferentialGradedAlgebra DifferentialGradedModule
open DifferentialGraded.StrictModuleSystem

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) {t : ℕ} (ht : 1 ≤ t)

/-- **The indices of the pro-isomorphism:** the multiples of `t`, measured from the base `t` of
the inverse system, so that the `j`-th chosen Koszul algebra is `K_{t + t * j}`.

This is a named function rather than the anonymous `fun j => t * j` because it is substituted for
the index field of `DifferentialGraded.ProIsoDerived`, whose composition identities mention a
component `(S.restrComp h h').hom.app (N.obj (idx c))` of a natural isomorphism built by a
universal property: an anonymous function leaves a beta-redex at `idx c` inside that component,
and deciding that it agrees with its reduct is not feasible there, whereas a named function
leaves the two sides literally equal. -/
def powProIsoIdx (t j : ℕ) : ℕ := t * j

/-- The chosen indices increase strictly, because `t ≥ 1`. -/
theorem powProIsoIdx_strictMono (ht : 1 ≤ t) : StrictMono (powProIsoIdx t) :=
  strictMono_nat_of_lt_succ fun j => by
    have h : powProIsoIdx t (j + 1) = powProIsoIdx t j + t := by
      simp only [powProIsoIdx]
      ring
    simp only [powProIsoIdx] at h ⊢
    omega

/-- Two consecutive chosen indices of the same parity pair are in increasing order. -/
theorem powProIsoIdx_le (t : ℕ) {j k : ℕ} (h : j ≤ k) : powProIsoIdx t j ≤ powProIsoIdx t k :=
  Nat.mul_le_mul_left t h

/-- **The presentation of `K_{t + t(2i+1)} ⊗_R K_t` over `K_{t + t(2i+2)}`** that the comparison
map of Tag 0GZ7 uses: the transition homomorphism followed by the inclusion of the first factor,
read on the graded opposite algebras. -/
def powCrossStructure (i : ℕ) :
    ((powStrictAlgebraSystem f ht).alg (powProIsoIdx t (2 * i + 2))).Hom
      ((powRegularComparison f ht).big (powProIsoIdx t (2 * i + 1))) :=
  oppHom (powTensorStructure f t (ht.trans (Nat.le_add_right t (t * (2 * i + 1))))
    (Nat.add_le_add_left (powIdx_le t i) t))

/-- The presentation `Koszul.powCrossStructure` is the one the system of modules provides: the
inclusion of the first factor composed with the transition homomorphism. The two differ only in
that the graded opposite of a composite is the composite of the graded opposites. -/
theorem powCrossStructure_eq (i : ℕ) :
    ((powRegularComparison f ht).incl (powProIsoIdx t (2 * i + 1))).comp
        ((powStrictAlgebraSystem f ht).trans
          (powProIsoIdx_le t (j := 2 * i + 1) (k := 2 * i + 2) (Nat.le_succ _))) =
      powCrossStructure f ht i :=
  oppHom_comp
    (powTransition f (ht.trans (Nat.le_add_right t (t * (2 * i + 1))))
      (Nat.add_le_add_left (powIdx_le t i) t))
    (tensorInclLeft (powAlgebra f (t + t * (2 * i + 1))) (powAlgebra f t))

/-- **The maps of the pro-isomorphism from `({}_{t+n}K_t)` to `(K_{t+n} ⊗_R K_t)`:** the
comparison map of Tag 0GZ7 at the indices `t(2i+1) ≤ t(2i+2)`, followed by the identification of
the two presentations of `K_{t+t(2i+1)} ⊗_R K_t` over `K_{t+t(2i+2)}`. -/
def powProIsoFwd (i : ℕ) :
    (powRestrictedModuleSystem f ht).obj (powProIsoIdx t (2 * i + 2)) ⟶
      ((powStrictAlgebraSystem f ht).toAlgebraSystem.restr
          ((powProIsoIdx_strictMono ht).monotone (a := 2 * i + 1) (b := 2 * i + 2)
            (Nat.le_succ _))).obj
        ((powBaseTensorModuleSystem f ht).obj (powProIsoIdx t (2 * i + 1))) :=
  powComparisonArrow f ht i ≫
    derivedTrans ((powStrictAlgebraSystem f ht).trans
        ((powProIsoIdx_strictMono ht).monotone (a := 2 * i + 1) (b := 2 * i + 2) (Nat.le_succ _)))
      ((powRegularComparison f ht).crossRestrHom
        ((powProIsoIdx_strictMono ht).monotone (a := 2 * i + 1) (b := 2 * i + 2) (Nat.le_succ _))
        (powCrossStructure f ht i) (powCrossStructure_eq f ht i))

/-- **The maps of the pro-isomorphism from `(K_{t+n} ⊗_R K_t)` to `({}_{t+n}K_t)`:** the
multiplication map `μ : K_{t+t(2i+1)} ⊗_R K_t → K_t`, read as a homomorphism semilinear over the
transition homomorphism `K_{t+t(2i+1)} → K_{t+t(2i)}`. -/
def powProIsoBwd (i : ℕ) :
    (powBaseTensorModuleSystem f ht).obj (powProIsoIdx t (2 * i + 1)) ⟶
      ((powStrictAlgebraSystem f ht).toAlgebraSystem.restr
          ((powProIsoIdx_strictMono ht).monotone (a := 2 * i) (b := 2 * i + 1)
            (Nat.le_succ _))).obj
        ((powRestrictedModuleSystem f ht).obj (powProIsoIdx t (2 * i))) :=
  derivedTrans ((powStrictAlgebraSystem f ht).trans
      ((powProIsoIdx_strictMono ht).monotone (a := 2 * i) (b := 2 * i + 1) (Nat.le_succ _)))
    ((powRegularComparison f ht).mulTrans
      ((powProIsoIdx_strictMono ht).monotone (a := 2 * i) (b := 2 * i + 1) (Nat.le_succ _)))

/-- **The first composition identity:** the comparison map of Tag 0GZ7 followed by the
multiplication map is the transition map of the system `({}_{t+n}K_t)`. This is the first
composite of Tag 0GZ7, `Koszul.powComparisonArrow_comp_powMulHom`, which says that the composite
of the comparison map with the multiplication map is the identity. -/
theorem powProIsoFwdBwd (i : ℕ) :
    powProIsoFwd f ht i ≫
        ((powStrictAlgebraSystem f ht).toAlgebraSystem.restr
            ((powProIsoIdx_strictMono ht).monotone (a := 2 * i + 1) (b := 2 * i + 2)
              (Nat.le_succ _))).map
          (powProIsoBwd f ht i) ≫
          ((powStrictAlgebraSystem f ht).toAlgebraSystem.restrComp
              ((powProIsoIdx_strictMono ht).monotone (a := 2 * i) (b := 2 * i + 1)
                (Nat.le_succ _))
              ((powProIsoIdx_strictMono ht).monotone (a := 2 * i + 1) (b := 2 * i + 2)
                (Nat.le_succ _))).hom.app
            ((powRestrictedModuleSystem f ht).obj (powProIsoIdx t (2 * i))) =
      (powRestrictedModuleSystem f ht).trans
        ((powProIsoIdx_strictMono ht).monotone (proIsoIdx_even_le_even i)) :=
  (powRegularComparison f ht).fwdBwd
    ((powProIsoIdx_strictMono ht).monotone (a := 2 * i) (b := 2 * i + 1) (Nat.le_succ _))
    ((powProIsoIdx_strictMono ht).monotone (a := 2 * i + 1) (b := 2 * i + 2) (Nat.le_succ _))
    (powCrossStructure f ht i) (powCrossStructure_eq f ht i) (powComparisonArrow f ht i)
    (powComparisonArrow_comp_powMulHom f ht i)
    ((powRestrictedModuleSystem f ht).obj (powProIsoIdx t (2 * i))) rfl
    (powProIsoBwd f ht i) HEq.rfl
    ((powRestrictedModuleSystem f ht).trans
      ((powProIsoIdx_strictMono ht).monotone (proIsoIdx_even_le_even i))) HEq.rfl

/-- **The second composition identity:** the multiplication map followed by the comparison map of
Tag 0GZ7 is the transition map of the system `(K_{t+n} ⊗_R K_t)`. This is the second composite of
Tag 0GZ7, `Koszul.powMulBaseHom_comp_powComparisonArrow`, which says that the composite of the
multiplication map with the comparison map is `τ ⊗ id`. -/
theorem powProIsoBwdFwd (i : ℕ) :
    powProIsoBwd f ht (i + 1) ≫
        ((powStrictAlgebraSystem f ht).toAlgebraSystem.restr
            ((powProIsoIdx_strictMono ht).monotone (a := 2 * (i + 1)) (b := 2 * (i + 1) + 1)
              (Nat.le_succ _))).map
          (powProIsoFwd f ht i) ≫
          ((powStrictAlgebraSystem f ht).toAlgebraSystem.restrComp
              ((powProIsoIdx_strictMono ht).monotone (a := 2 * i + 1) (b := 2 * i + 2)
                (Nat.le_succ _))
              ((powProIsoIdx_strictMono ht).monotone
                (a := 2 * (i + 1)) (b := 2 * (i + 1) + 1) (Nat.le_succ _))).hom.app
            ((powBaseTensorModuleSystem f ht).obj (powProIsoIdx t (2 * i + 1))) =
      (powBaseTensorModuleSystem f ht).trans
        ((powProIsoIdx_strictMono ht).monotone (proIsoIdx_odd_le_odd i)) :=
  (powRegularComparison f ht).bwdFwd
    ((powProIsoIdx_strictMono ht).monotone (a := 2 * i + 1) (b := 2 * i + 2) (Nat.le_succ _))
    ((powProIsoIdx_strictMono ht).monotone (a := 2 * (i + 1)) (b := 2 * (i + 1) + 1)
      (Nat.le_succ _))
    (powCrossStructure f ht i) (powCrossStructure_eq f ht i) (powComparisonArrow f ht i)
    (powMulBaseHom_comp_powComparisonArrow f ht i)
    ((powBaseTensorModuleSystem f ht).obj (powProIsoIdx t (2 * i + 1))) rfl
    (powProIsoFwd f ht i) HEq.rfl
    ((powBaseTensorModuleSystem f ht).trans
      ((powProIsoIdx_strictMono ht).monotone (proIsoIdx_odd_le_odd i))) HEq.rfl

/-- **The second step of the proof of Tag 0GZJ:** the system `({}_{t+n}K_t)` and the system
`(K_{t+n} ⊗_R K_t)` of left differential graded modules over the Koszul algebras are
pro-isomorphic in the derived category.

The indices are the multiples of `t`, the comparison maps are those of Tag 0GZ7
(`Koszul.powComparisonArrow`), the maps in the other direction are the multiplication maps, and
the two composition identities are the two composites of Tag 0GZ7. -/
@[stacks 0GZJ "the pro-isomorphism of ({}_nK_t) with (K_n ⊗_R K_t) in the derived category"]
def powProIsoDerived :
    ProIsoDerived (powRestrictedModuleSystem f ht) (powBaseTensorModuleSystem f ht) where
  idx := powProIsoIdx t
  idx_strictMono := powProIsoIdx_strictMono ht
  fwd := powProIsoFwd f ht
  bwd := powProIsoBwd f ht
  fwd_bwd := powProIsoFwdBwd f ht
  bwd_fwd := powProIsoBwdFwd f ht

end Koszul

end
