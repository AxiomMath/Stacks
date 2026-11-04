module

public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.Curves.NodeMulticrossBridge
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.MulticrossBranches.Completion
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
import all StacksFrontier.AlgebraicGeometry.Variety.MulticrossBranches.MulticrossDelta
import all StacksFrontier.RingTheory.Branches.Completion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Multicross singularities and the delta invariant

Let `k` be an algebraically closed field and `X` a reduced one-dimensional algebraic
`k`-scheme.  At a closed point `x` of `X` the completed local ring is a multicross ring with at
least two branches exactly when the delta invariant of `X` at `x` is the number of branches of
`X` at `x` minus one **and** `x` has at least two branches.  The second conjunct cannot be
dropped: at a nonsingular closed point the delta invariant is `0` and the number of branches is
`1`, so the numerical condition holds while the point is not a singularity at all.

## Main results

* `Stacks.Curves.encard_minimalPrimes_multicross` — the `n`-branch multicross ring has `n`
  minimal primes.
* `Stacks.Curves.numberOfBranchesOfLocalRing_eq_encard_minimalPrimes_adicCompletion` — for a
  one-dimensional Noetherian local ring with separably closed residue field the number of
  branches is the number of minimal primes of the completion.
* `Ring.nonempty_adicCompletion_algEquiv_multicross_iff` — the numerical criterion for the
  completion to be a multicross ring with at least two branches.
* `Stacks.Curves.isMulticrossSingularity_iff_deltaInvariant_eq_and_two_le_numberOfBranches` and
  `Stacks.Curves.isMulticrossSingularity_iff_deltaInvariant_eq_of_not_isRegularLocalRing` — the
  same criterion at a closed point of a reduced one-dimensional algebraic scheme, in the
  unconditional form and in the form restricted to a singular point.
* `Stacks.Curves.deltaInvariant_eq_and_not_isMulticrossSingularity_of_isRegularLocalRing` — at a
  nonsingular closed point the numerical condition holds and the multicross condition fails.

## Implementation notes

The numerical criterion is the two halves of Tag 0C1V together with the branch count of the
multicross ring.  That count is what connects them: the equality case of Tag 0C1V produces a
multicross description of the completion with one factor for each branch, and its converse
needs to be told how many branches there are, so both directions go through the identity
"number of branches = number of minimal primes of the completion".  The latter is Tag 0C2D for
the branch counts of a completion, plus the fact that a complete local ring is its own
henselization.

Over an algebraically closed field the hypotheses of the ring-theoretic criterion are supplied
by the scheme: the local ring is Nagata because the scheme is locally of finite type over a
field, its residue field is the base field at a closed point, and its dimension is at most that
of the scheme while a reduced local ring of dimension zero is a field, hence regular.

## References

* [Stacks Project, Tag 0C1X](https://stacks.math.columbia.edu/tag/0C1X)
* [Stacks Project, Tag 0C1V](https://stacks.math.columbia.edu/tag/0C1V)
* [Stacks Project, Tag 0C1W](https://stacks.math.columbia.edu/tag/0C1W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

universe u v

namespace Stacks.Curves

/-! ### The multicross ring: branch count and the one-branch case -/

/-- **The `n`-branch multicross ring has exactly `n` minimal primes**, the kernels of the `n`
branch projections. -/
theorem encard_minimalPrimes_multicross (k : Type u) [Field k] (n : ℕ) :
    (minimalPrimes ↥(multicross k n)).encard = (n : ℕ∞) := by
  rw [minimalPrimes_multicross_eq_range_projectionKernel, ← Set.image_univ,
    (multicrossProjectionKernel_injective k n).injOn.encard_image, Set.encard_univ]
  simp

/-- The one-branch multicross ring is the ring of formal power series in one variable: the
condition on constant coefficients is vacuous. -/
def multicrossOneRingEquiv (k : Type u) [CommRing k] :
    ↥(multicross k 1) ≃+* PowerSeries k :=
  RingEquiv.ofBijective
    ((Pi.evalRingHom (fun _ : Fin 1 => PowerSeries k) 0).comp (multicross k 1).subtype)
    ⟨fun f g h => Subtype.ext (funext fun i => by
        obtain rfl : i = 0 := Subsingleton.elim i 0
        exact h),
      fun g => ⟨⟨fun _ => g, by rw [mem_multicross]; exact fun _ _ => rfl⟩, rfl⟩⟩

/-- **The one-branch multicross ring is regular**, being the power series ring in one variable
over a field. -/
theorem isRegularLocalRing_multicross_one (k : Type u) [Field k] :
    IsRegularLocalRing ↥(multicross k 1) :=
  IsRegularLocalRing.of_ringEquiv (R := PowerSeries k) (multicrossOneRingEquiv k).symm

/-! ### The number of branches and the minimal primes of the completion -/

/-- **For a one-dimensional Noetherian local ring with separably closed residue field the number
of branches is the number of minimal primes of the completion.**  Completion preserves the
branch counts (Tag 0C2D) and a complete local ring is its own henselization. -/
theorem numberOfBranchesOfLocalRing_eq_encard_minimalPrimes_adicCompletion
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsSepClosed (ResidueField A)] (hdim : ringKrullDim A = 1) :
    numberOfBranchesOfLocalRing A =
      (minimalPrimes (AdicCompletion (maximalIdeal A) A)).encard := by
  let Ahat := AdicCompletion (maximalIdeal A) A
  let : IsLocalRing Ahat := AdicCompletion.isLocalRing_of_fg
    (maximalIdeal A).fg_of_isNoetherianRing
  let : IsAdicComplete (maximalIdeal Ahat) Ahat :=
    AdicCompletion.isAdicComplete_of_fg (maximalIdeal A).fg_of_isNoetherianRing
  let : HenselianLocalRing Ahat := henselianLocalRing_of_isAdicComplete_maximalIdeal Ahat
  let eK := residueFieldAlgEquiv_completion A
  let : IsSepClosed (ResidueField Ahat) := IsSepClosed.of_ringEquiv eK.symm.toRingEquiv
  let Dh := henselizationData A
  let H := Dh.carrier
  let : CommRing H := Dh.commRing
  let : IsLocalRing H := Dh.isLocalRing
  let : Algebra A H := Dh.algebra
  let : IsHenselization A (ResidueField A) H := Dh.isHenselization
  let DhatH := henselizationData Ahat
  let Hhat := DhatH.carrier
  let : CommRing Hhat := DhatH.commRing
  let : IsLocalRing Hhat := DhatH.isLocalRing
  let : Algebra Ahat Hhat := DhatH.algebra
  let : IsHenselization Ahat (ResidueField Ahat) Hhat := DhatH.isHenselization
  let Dsh := strictHenselizationData A
  let Sh := Dsh.carrier
  let : CommRing Sh := Dsh.commRing
  let : IsLocalRing Sh := Dsh.isLocalRing
  let : Algebra A Sh := Dsh.algebra
  let : IsHenselization A (SeparableClosure (ResidueField A)) Sh := Dsh.isHenselization
  let DhatSh := strictHenselizationData Ahat
  let HhatSh := DhatSh.carrier
  let : CommRing HhatSh := DhatSh.commRing
  let : IsLocalRing HhatSh := DhatSh.isLocalRing
  let : Algebra Ahat HhatSh := DhatSh.algebra
  let : IsHenselization Ahat (SeparableClosure (ResidueField Ahat)) HhatSh :=
    DhatSh.isHenselization
  have hbranches : numberOfBranchesOfLocalRing A = numberOfBranchesOfLocalRing Ahat :=
    calc
      numberOfBranchesOfLocalRing A = numberOfGeometricBranchesOfLocalRing A :=
        numberOfBranches_eq_numberOfGeometricBranches_of_sepClosed A
      _ = numberOfGeometricBranchesOfLocalRing Ahat :=
        (numberOfBranches_and_numberOfGeometricBranches_eq_adicCompletion_of_dimension_one
          A H Hhat Sh HhatSh (SeparableClosure (ResidueField A))
          (SeparableClosure (ResidueField Ahat)) hdim).2
      _ = numberOfBranchesOfLocalRing Ahat :=
        (numberOfBranches_eq_numberOfGeometricBranches_of_sepClosed Ahat).symm
  let : IsHenselization Ahat (ResidueField Ahat) Ahat := isHenselization_self Ahat
  obtain ⟨eH⟩ := exists_algEquiv_of_isHenselization Ahat Hhat Ahat
    (ResidueField Ahat) (ResidueField Ahat) AlgEquiv.refl
  rw [hbranches, numberOfBranchesOfLocalRing_eq_encard_minimalPrimes]
  exact encard_minimalPrimes_eq_of_ringEquiv eH.toRingEquiv

/-! ### Dimension one at a singular point -/

/-- A Noetherian local ring which is a field is regular: its maximal ideal is generated by the
empty set. -/
private theorem isRegularLocalRing_of_isField (A : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (h : IsField A) : IsRegularLocalRing A := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp h]
  simpa using ringKrullDim_nonneg_of_nontrivial (R := A)

/-- **A reduced Noetherian local ring of dimension at most one which is not regular has
dimension exactly one.**  A reduced local ring of dimension zero is a field, hence regular. -/
theorem ringKrullDim_eq_one_of_not_isRegularLocalRing (A : Type v) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsReduced A] (hle : ringKrullDim A ≤ (1 : WithBot ℕ∞))
    (hsing : ¬ IsRegularLocalRing A) : ringKrullDim A = 1 := by
  have hne0 : ringKrullDim A ≠ 0 := by
    intro hdim
    let : Ring.KrullDimLE 0 A := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
    exact hsing (isRegularLocalRing_of_isField A Ring.KrullDimLE.isField_of_isReduced)
  have hbot : ringKrullDim A ≠ ⊥ := fun h => by
    simpa [h] using (ringKrullDim_nonneg_of_nontrivial (R := A))
  lift ringKrullDim A to ℕ∞ using hbot with d hd
  have hd1 : d ≤ 1 := by exact_mod_cast hle
  lift d to ℕ using ne_top_of_le_ne_top (by simp) hd1 with n hn
  have hn1 : n ≤ 1 := by exact_mod_cast hd1
  have hn0 : n ≠ 0 := fun he => hne0 (by norm_num [he])
  obtain rfl : n = 1 := by omega
  norm_num

end Stacks.Curves

namespace Ring

open Stacks.Curves

/-- The coefficient map of the multicross ring, in the form the equality case of Tag 0C1V states
its compatibility. -/
private theorem algebraMap_multicross_eq (k : Type u) [Field k] (n : ℕ) :
    (algebraMap k ↥(multicross k n)) =
      (RingHom.pi fun _ : Fin n ↦ PowerSeries.C).codRestrict (multicross k n) (by
        intro a
        rw [mem_multicross]
        simp) := rfl

/-- If the completion of a one-dimensional Noetherian local ring with separably closed residue
field is the `n`-branch multicross ring, the ring has `n` branches. -/
private theorem numberOfBranchesOfLocalRing_eq_of_ringEquiv_multicross
    {k : Type u} [Field k] (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsSepClosed (ResidueField A)] (hdim : ringKrullDim A = 1) {n : ℕ}
    (e : AdicCompletion (maximalIdeal A) A ≃+* ↥(multicross k n)) :
    numberOfBranchesOfLocalRing A = (n : ℕ∞) := by
  rw [numberOfBranchesOfLocalRing_eq_encard_minimalPrimes_adicCompletion A hdim,
    encard_minimalPrimes_eq_of_ringEquiv e, encard_minimalPrimes_multicross]

/-- **The completion of a reduced one-dimensional Nagata local algebra over a separably closed
field, with residue field the base field, is a multicross ring with at least two branches if and
only if its delta invariant is the number of branches minus one and it has at least two
branches.** -/
theorem nonempty_adicCompletion_algEquiv_multicross_iff
    (k : Type u) (A : Type v) [Field k] [IsSepClosed k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsReduced A] (hNagata : IsNagataRing A)
    (hdim : ringKrullDim A = 1) (hres : Nonempty (ResidueField A ≃ₐ[k] k)) :
    (∃ n : ℕ, 2 ≤ n ∧
        Nonempty (AdicCompletion (maximalIdeal A) A ≃ₐ[k] ↥(multicross k n))) ↔
      (Ring.deltaInvariant A = numberOfBranchesOfLocalRing A - 1 ∧
        2 ≤ numberOfBranchesOfLocalRing A) := by
  let : IsNoetherianRing A := hNagata.1
  let : IsSepClosed (ResidueField A) :=
    IsSepClosed.of_ringEquiv (Classical.choice hres).toRingEquiv
  constructor
  · rintro ⟨n, hn, ⟨e⟩⟩
    have hcount := numberOfBranchesOfLocalRing_eq_of_ringEquiv_multicross A hdim e.toRingEquiv
    have hcompat : e.toRingEquiv.toRingHom.comp
        (algebraMap k (AdicCompletion (maximalIdeal A) A)) = algebraMap k ↥(multicross k n) :=
      RingHom.ext fun a => e.commutes a
    refine ⟨deltaInvariant_eq_numberOfBranches_sub_one_of_adicCompletion_algEquiv_multicross
      k A hNagata hdim hres n hcount e.toRingEquiv (hcompat.trans (algebraMap_multicross_eq k n)),
      ?_⟩
    rw [hcount]
    exact_mod_cast hn
  · rintro ⟨heq, hge2⟩
    obtain ⟨n, hcount, e, he⟩ :=
      adicCompletion_algEquiv_multicross_of_deltaInvariant_eq k A hNagata hdim hres heq
    refine ⟨n, ?_, ⟨{ e with commutes' := fun a => ?_ }⟩⟩
    · rw [hcount] at hge2
      exact_mod_cast hge2
    · rw [algebraMap_multicross_eq k n]
      exact DFunLike.congr_fun he a

/-- **The equality of the delta invariant with the number of branches minus one forces at least
two branches at a point which is not regular.**  With fewer branches the equality case of
Tag 0C1V presents the completion as the one-branch multicross ring, which is regular. -/
theorem two_le_numberOfBranches_of_deltaInvariant_eq_of_not_isRegularLocalRing
    (k : Type u) (A : Type v) [Field k] [IsSepClosed k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsReduced A] (hNagata : IsNagataRing A)
    (hdim : ringKrullDim A = 1) (hres : Nonempty (ResidueField A ≃ₐ[k] k))
    (hsing : ¬ IsRegularLocalRing A)
    (heq : Ring.deltaInvariant A = numberOfBranchesOfLocalRing A - 1) :
    2 ≤ numberOfBranchesOfLocalRing A := by
  let : IsNoetherianRing A := hNagata.1
  obtain ⟨n, hcount, e, -⟩ :=
    adicCompletion_algEquiv_multicross_of_deltaInvariant_eq k A hNagata hdim hres heq
  rw [hcount]
  by_contra hlt
  have hn2 : ¬ 2 ≤ n := fun h => hlt (by exact_mod_cast h)
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · have hsub : Subsingleton ↥(multicross k 0) :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    have h : e.symm (0 : ↥(multicross k 0)) = e.symm 1 := congrArg e.symm (hsub.elim _ _)
    rw [map_zero, map_one] at h
    exact one_ne_zero h.symm
  · let : IsRegularLocalRing ↥(multicross k 1) := isRegularLocalRing_multicross_one k
    exact hsing (isRegularLocalRing_iff_adicCompletion_maximalIdeal.mpr
      (IsRegularLocalRing.of_ringEquiv e.symm))

/-- **An integrally closed domain has delta invariant zero**: the canonical map to the integral
closure in the fraction field is already surjective. -/
@[sga "7 X 2.24" "more general"]
theorem deltaInvariant_eq_zero_of_isIntegrallyClosed (A : Type v) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] : deltaInvariant A = 0 := by
  have hrange :
      LinearMap.range (Algebra.linearMap A ↥(integralClosure A (FractionRing A))) = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun y => ?_
    obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff (K := FractionRing A)).mp inferInstance y.2
    exact ⟨a, Subtype.ext ha⟩
  exact Module.length_eq_zero_iff.mpr (Submodule.Quotient.subsingleton_iff.mpr hrange)

/-- **A one-dimensional regular local ring with separably closed residue field has delta
invariant zero and a single branch, and its completion is not a multicross ring with at least
two branches.**  So the numerical equality of clause (2) of Stacks 0C1X holds at such a ring
while the multicross condition of clause (1) fails. -/
@[sga "7 X 2.24" "more general"]
theorem deltaInvariant_eq_sub_one_and_not_multicross_of_isRegularLocalRing
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A] [IsRegularLocalRing A]
    [IsSepClosed (ResidueField A)] (hdim : ringKrullDim A = 1) :
    (deltaInvariant A = numberOfBranchesOfLocalRing A - 1 ∧
        numberOfBranchesOfLocalRing A = 1) ∧
      ¬ ∃ n : ℕ, 2 ≤ n ∧
        Nonempty (AdicCompletion (maximalIdeal A) A ≃ₐ[k] ↥(multicross k n)) := by
  have hregdimA : IsRegularLocalRing A ∧ ringKrullDim A = 1 := ⟨inferInstance, hdim⟩
  obtain ⟨-, -, hdomA, hicA, -⟩ := ((isDiscreteValuationRing_tfae A).out 3 5).mp hregdimA
  let : IsDomain A := hdomA
  let : IsIntegrallyClosed A := hicA
  have hregHat : IsRegularLocalRing (AdicCompletion (maximalIdeal A) A) :=
    isRegularLocalRing_iff_adicCompletion_maximalIdeal.mp inferInstance
  have hdimHat : ringKrullDim (AdicCompletion (maximalIdeal A) A) = 1 :=
    (IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal (A := A)).trans hdim
  have hregdimHat : IsRegularLocalRing (AdicCompletion (maximalIdeal A) A) ∧
      ringKrullDim (AdicCompletion (maximalIdeal A) A) = 1 := ⟨hregHat, hdimHat⟩
  obtain ⟨-, -, hdomHat, -, -⟩ :=
    ((isDiscreteValuationRing_tfae (AdicCompletion (maximalIdeal A) A)).out 3 5).mp hregdimHat
  let : IsDomain (AdicCompletion (maximalIdeal A) A) := hdomHat
  have hbranch : numberOfBranchesOfLocalRing A = 1 := by
    rw [numberOfBranchesOfLocalRing_eq_encard_minimalPrimes_adicCompletion A hdim,
      IsDomain.minimalPrimes_eq_singleton_bot, Set.encard_singleton]
  refine ⟨⟨?_, hbranch⟩, ?_⟩
  · rw [deltaInvariant_eq_zero_of_isIntegrallyClosed A, hbranch]
    simp
  · rintro ⟨n, hn, ⟨e⟩⟩
    have hcount := numberOfBranchesOfLocalRing_eq_of_ringEquiv_multicross A hdim e.toRingEquiv
    rw [hbranch] at hcount
    have hn1 : n = 1 := by exact_mod_cast hcount.symm
    omega

/-- **The completion of a reduced one-dimensional Nagata local algebra over a separably closed
field, with residue field the base field, which is not regular is a multicross ring with at
least two branches if and only if its delta invariant is the number of branches minus one.** -/
theorem nonempty_adicCompletion_algEquiv_multicross_iff_of_not_isRegularLocalRing
    (k : Type u) (A : Type v) [Field k] [IsSepClosed k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsReduced A] (hNagata : IsNagataRing A)
    (hdim : ringKrullDim A = 1) (hres : Nonempty (ResidueField A ≃ₐ[k] k))
    (hsing : ¬ IsRegularLocalRing A) :
    (∃ n : ℕ, 2 ≤ n ∧
        Nonempty (AdicCompletion (maximalIdeal A) A ≃ₐ[k] ↥(multicross k n))) ↔
      Ring.deltaInvariant A = numberOfBranchesOfLocalRing A - 1 := by
  rw [nonempty_adicCompletion_algEquiv_multicross_iff k A hNagata hdim hres]
  exact and_iff_left_of_imp
    (two_le_numberOfBranches_of_deltaInvariant_eq_of_not_isRegularLocalRing k A hNagata hdim
      hres hsing)

end Ring

namespace Stacks.Curves

/-- The algebra and finiteness data the ring-theoretic criterion needs at a closed point of a
reduced scheme locally of finite type over an algebraically closed field whose local ring there
is one-dimensional. -/
@[ega "I 6.4.2" "special case"]
private theorem nagata_and_residueField_of_isClosed
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (x : X) (hx : IsClosed ({x} : Set X)) :
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x trivial).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    IsNagataRing (X.presheaf.stalk x) ∧
      Nonempty (ResidueField (X.presheaf.stalk x) ≃ₐ[k] k) := by
  intro kToStalk
  let : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  exact ⟨isNagataRing_stalk_of_locallyOfFiniteType k (X ↘ Spec (.of k)) x,
    ⟨(AlgEquiv.ofBijective (Algebra.ofId k (ResidueField (X.presheaf.stalk x)))
      ⟨(algebraMap k (ResidueField (X.presheaf.stalk x))).injective,
        surjective_evaluation_of_isAlgClosed k (X ↘ Spec (.of k)) x hx⟩).symm⟩⟩

/-- **Stacks 0C1X, clauses (1) and (2).**  Let `k` be an algebraically closed field, `X` a
reduced algebraic `k`-scheme and `x ∈ X` a closed point at which the local ring is
one-dimensional.  Then `x` defines a multicross singularity if and only if the delta invariant
of `X` at `x` is the number of branches of `X` at `x` minus one **and** `x` has at least two
branches.

Clause (2) is supplemented by `2 ≤` the number of branches: the source's unrestricted
equivalence is false at a nonsingular closed point, where the delta invariant is `0` and the
number of branches is `1`, so (2) holds while (1) fails because Definition 0C1W requires
`n ≥ 2`.  The tag sits on `Stacks.Curves.isMulticrossSingularity_tfae`, which adds clause (3). -/
theorem isMulticrossSingularity_iff_deltaInvariant_eq_and_two_le_numberOfBranches
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsReduced X] (x : X)
    (hx : IsClosed ({x} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    IsMulticrossSingularity k X x ↔
      (Ring.deltaInvariant (X.presheaf.stalk x) = numberOfBranches X x - 1 ∧
        2 ≤ numberOfBranches X x) := by
  let kToStalk : k →+* X.presheaf.stalk x :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
      X.presheaf.germ ⊤ x trivial).hom
  let : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  let : IsReduced (X.presheaf.stalk x) :=
    AlgebraicGeometry.isReduced_stalk_of_isReduced X x
  obtain ⟨hNagata, hres⟩ := nagata_and_residueField_of_isClosed k X x hx
  rw [isMulticrossSingularity_iff_of_isClosed k X x hx]
  exact Ring.nonempty_adicCompletion_algEquiv_multicross_iff k (X.presheaf.stalk x) hNagata
    hdim hres

/-- **Stacks 0C1X, clauses (1) and (2), at a singular point.**  At a closed point of a reduced
one-dimensional algebraic scheme over an algebraically closed field whose local ring there is
not regular, `x` defines a multicross singularity if and only if the delta invariant of `X` at
`x` is the number of branches of `X` at `x` minus one.

Clause (2) is restricted to a point whose local ring is not regular: the source's unrestricted
equivalence is false at a nonsingular closed point, where the delta invariant is `0` and the
number of branches is `1`, so (2) holds while (1) fails because Definition 0C1W requires
`n ≥ 2`.  The tag sits on `Stacks.Curves.isMulticrossSingularity_tfae`, which adds clause (3). -/
theorem isMulticrossSingularity_iff_deltaInvariant_eq_of_not_isRegularLocalRing
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsReduced X]
    (hX : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X))
    (hsing : ¬ IsRegularLocalRing (X.presheaf.stalk x)) :
    IsMulticrossSingularity k X x ↔
      Ring.deltaInvariant (X.presheaf.stalk x) = numberOfBranches X x - 1 := by
  let kToStalk : k →+* X.presheaf.stalk x :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
      X.presheaf.germ ⊤ x trivial).hom
  let : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  let : IsReduced (X.presheaf.stalk x) :=
    AlgebraicGeometry.isReduced_stalk_of_isReduced X x
  obtain ⟨hNagata, hres⟩ := nagata_and_residueField_of_isClosed k X x hx
  let : IsNoetherianRing (X.presheaf.stalk x) := hNagata.1
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 :=
    ringKrullDim_eq_one_of_not_isRegularLocalRing (X.presheaf.stalk x)
      (hX ▸ ringKrullDim_stalk_le_topologicalKrullDim x) hsing
  rw [isMulticrossSingularity_iff_deltaInvariant_eq_and_two_le_numberOfBranches k X x hx hdim]
  exact and_iff_left_of_imp fun heq =>
    Ring.two_le_numberOfBranches_of_deltaInvariant_eq_of_not_isRegularLocalRing k
      (X.presheaf.stalk x) hNagata hdim hres hsing heq

/-- **At a nonsingular closed point of a one-dimensional algebraic scheme over an algebraically
closed field the numerical clause (2) of Stacks 0C1X holds while clause (1) fails**: the delta
invariant is `0` and there is exactly one branch, so the delta invariant is the number of
branches minus one, yet the point is not a singularity.  This is the obstruction to the
equivalence as the source states it. -/
theorem deltaInvariant_eq_and_not_isMulticrossSingularity_of_isRegularLocalRing
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] (x : X) (hx : IsClosed ({x} : Set X))
    (hreg : IsRegularLocalRing (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1) :
    (Ring.deltaInvariant (X.presheaf.stalk x) = numberOfBranches X x - 1 ∧
        numberOfBranches X x = 1) ∧
      ¬ IsMulticrossSingularity k X x := by
  let kToStalk : k →+* X.presheaf.stalk x :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
      X.presheaf.germ ⊤ x trivial).hom
  let : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  let : IsRegularLocalRing (X.presheaf.stalk x) := hreg
  obtain ⟨-, ⟨eres⟩⟩ := nagata_and_residueField_of_isClosed k X x hx
  let : IsSepClosed (ResidueField (X.presheaf.stalk x)) :=
    IsSepClosed.of_ringEquiv eres.toRingEquiv
  rw [isMulticrossSingularity_iff_of_isClosed k X x hx]
  exact Ring.deltaInvariant_eq_sub_one_and_not_multicross_of_isRegularLocalRing k
    (X.presheaf.stalk x) hdim

end Stacks.Curves

end
