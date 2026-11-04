module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppNormalFiniteSupport

/-!
# The all-conjugates bridge for a finite base change

Let `A ⊆ B` be an extension of discrete valuation rings with fraction fields `K ⊆ L`, and let
`K₁ / K` be finite.  The reduced base change `(L ⊗[K] K₁) ⧸ nilradical` is a finite product of
fields — the *conjugate factors* — and a weak solution for `A → B` is a condition on **all** of
them at once.

This file supplies the glue between the two halves of that statement which already exist
separately:

* `IsDiscreteValuationRing.exists_tensorProduct_quotNilradical_equiv_pi_fields`
  (`Abhyankar.lean`) produces the factor decomposition, as a `K`-algebra equivalence together
  with the two compatibility equations for `L` and for `K₁`;
* `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_factor_solutions`
  (`EppAlgClosedResidue.lean`) consumes a factor family, a per-factor weak solution, and a
  `K₁`-algebra equivalence, and returns one further finite extension of `K` solving `A → B`.

The mismatch is exactly the scalars: the decomposition is a `K`-algebra equivalence, the combiner
demands a `K₁`-algebra one.  `reducedTensorPiEquivOfRight` closes it, using the `K₁`-compatibility
equation the decomposition already carries, and
`exists_finite_extension_isWeakSolution_of_reducedFactorSolutions` is the resulting bridge: it
takes the decomposition in the shape the decomposition theorem produces, and asks for a weak
solution at every factor.

## What this does *not* do, and why

**It is not a proof of Tag 09F9, and it does not descend a weak solution along one embedding.**
Two independent constraints bound it, and both are load-bearing.

*First*, the mechanism this file exists to avoid.  The Stacks proof of Tag 09ET (3) descends a
weak solution by identifying `L' ⊗_K K₁` with a product of copies of `L' ⊗_{K'} K'₁`.  The copies
are indexed by the `K`-algebra maps `τ : F → L'` and the `τ`-th copy receives `F` through `τ`, so
only the factor at the distinguished embedding is `L' ⊗_{K'} K'₁`; the hypothesis constrains that
one factor and says nothing about the `[F : K] - 1` conjugates.
`StacksFrontier.RingTheory.DiscreteValuationRing.EppConditionalDescent` proves the factors are
genuinely distinct (`Stacks.WeakSolution.Obstruction.conjugateFactor_injective`) and
the counterexample to clause (3) of Tag 09ET exhibits an `A ⊂ B` where the conjugate condition is
not merely unproved but false.  Accordingly nothing below picks a factor: the per-factor hypothesis
`hsol` is quantified over the whole index set, and the conclusion is obtained from all factors
simultaneously through the combiner.

*Second*, the combiner's own hypotheses.  `R` must be complete with perfect residue field, and each
`S i` complete: the combiner uses those hypotheses to preserve a weak solution while the
per-factor solutions are amalgamated into one common finite overfield.

The remaining mathematical obstruction to the general statement is therefore precisely this, and it
is stated here rather than papered over: one needs either

* common-overfield stability of weak solutions under Epp's perfect-core hypothesis with an explicit
  finite-coefficient bound per factor, or
* a single common extension constructed for all factors from the outset, rather than one extension
  per factor amalgamated afterwards.

Note also what is *not* available as a shortcut: the universal containment
`perfectCore κ_B ≤ range (κ_{A₁} → κ_B)` does **not** follow from finite-support absorption, since
the perfect core need not be finite over `κ_A`; see
`StacksFrontier.RingTheory.DiscreteValuationRing.EppFiniteSupport`.

## Main definitions

* `IsDiscreteValuationRing.reducedTensorPiEquivOfRight`: a `K`-algebra decomposition of the reduced
  base change into a product, whose `K₁`-compatibility equation holds, is a `K₁`-algebra
  decomposition.

## Main results

* `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_reducedFactorSolutions`: if
  every field factor of a decomposition of `(L ⊗[K] K₁) ⧸ nilradical` admits a weak solution over
  the given complete base, then a single further finite extension of `K` is a weak solution for
  `A → B`.
* `exists_finite_extension_isWeakSolution_of_forall_reducedFactorSolutions`:
  the same with the decomposition discharged internally, so that the hypothesis is the per-factor
  solvability alone and no presentation data has to be supplied.
* `IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages`: the synchronized form,
  in which the per-factor solutions are all packaged over **one shared** second extension `K₂` and
  the conclusion is that a *supplied* base change `D₂` over that same `K₂` is a weak solution. No
  completeness and no perfect residue field are assumed: fixing `K₂` in advance is
  exactly what removes the amalgamation step those hypotheses paid for.

## References

* [The Stacks Project, Tag 09EN](https://stacks.math.columbia.edu/tag/09EN)
* [The Stacks Project, Tag 09F8](https://stacks.math.columbia.edu/tag/09F8)
-/

@[expose] public section

open scoped TensorProduct

universe u uA uB uC uK uL uF uD₁ uD₂ v

namespace IsDiscreteValuationRing

/-- **A `K`-algebra decomposition of the reduced base change is a `K₁`-algebra decomposition.**

The reduced base change `(L ⊗[K] K₁) ⧸ nilradical` carries a `K₁`-algebra structure through the
right factor.  A decomposition `decomp` of it into a product of `K₁`-algebras which is only known
to be `K`-linear is automatically `K₁`-linear as soon as it sends the image of `a : K₁` to the
constant family `algebraMap K₁ (E i) a`, which is the second compatibility equation produced by
`exists_tensorProduct_quotNilradical_equiv_pi_fields`.

This is the scalar bookkeeping that lets the factor decomposition feed the all-factor combiner; it
asserts nothing about the individual factors and in particular distinguishes none of them. -/
noncomputable def reducedTensorPiEquivOfRight
    (K : Type uK) (L : Type uL) (K₁ : Type uF)
    [Field K] [Field L] [Field K₁] [Algebra K L] [Algebra K K₁]
    {ι : Type v} (E : ι → Type uD₁) [∀ i, CommRing (E i)] [∀ i, Algebra K (E i)]
    [∀ i, Algebra K₁ (E i)]
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hright : ∀ i (a : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) a)) i =
      algebraMap K₁ (E i) a) :
    letI : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
    letI : Algebra K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) :=
      Ideal.Quotient.algebra K₁
    ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K₁] ∀ i, E i := by
  letI : Algebra K₁ (L ⊗[K] K₁) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra K₁ (ReducedTensorTower.Reduction (L ⊗[K] K₁)) :=
    Ideal.Quotient.algebra K₁
  refine { __ := decomp.toRingEquiv, commutes' := ?_ }
  intro a
  ext i
  have h := hright i a
  rw [Algebra.TensorProduct.includeRight_apply] at h
  change decomp (Ideal.Quotient.mk _ ((1 : L) ⊗ₜ[K] a)) i = _
  exact h

/-- Applying `reducedTensorPiEquivOfRight` is applying the underlying `K`-algebra
decomposition. -/
@[simp]
theorem reducedTensorPiEquivOfRight_apply
    (K : Type uK) (L : Type uL) (K₁ : Type uF)
    [Field K] [Field L] [Field K₁] [Algebra K L] [Algebra K K₁]
    {ι : Type v} (E : ι → Type uD₁) [∀ i, CommRing (E i)] [∀ i, Algebra K (E i)]
    [∀ i, Algebra K₁ (E i)]
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hright : ∀ i (a : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) a)) i =
      algebraMap K₁ (E i) a)
    (x : ReducedTensorTower.Reduction (L ⊗[K] K₁)) :
    reducedTensorPiEquivOfRight K L K₁ E decomp hright x = decomp x := rfl

/-- **The all-conjugates bridge.**

Let `A ⊆ B` be an extension of discrete valuation rings with fraction fields `K ⊆ L`, let `K₁ / K`
be finite, and let `R` be a complete discrete valuation ring with fraction field `K₁`, integral
over `A`, whose residue field is perfect.  Suppose the reduced base change
`(L ⊗[K] K₁) ⧸ nilradical` is decomposed as a product of fields `E i`, compatibly with `L` and
with `K₁`, and each factor is presented by a complete discrete valuation ring `S i` with fraction
field `E i`.  If **every** factor admits a weak solution over `R`, then one further finite
extension of `K` is a weak solution for `A → B`.

Every factor is required, and that is the point.  The conjugate factors of `L ⊗[K] K₁` are
pairwise distinct (`Stacks.WeakSolution.Obstruction.conjugateFactor_injective`), a weak solution
  constrains all of them
simultaneously, and a hypothesis at one distinguished factor does not suffice — that is the step of
the Stacks proof of Tag 09ET (3) that fails.

The completeness of `R` and of each `S i`, and perfectness of the residue field of `R`, are
inherited from
`exists_finite_extension_isWeakSolution_of_factor_solutions`, where they are used to amalgamate
the per-factor solutions into a single finite overfield; they are not removable.  See the module
docstring for the obstruction this leaves in the general case. -/
theorem exists_finite_extension_isWeakSolution_of_reducedFactorSolutions
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ : Type uF)
    (R : Type uC)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Module.Finite K K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R]
    [Algebra R K₁] [IsFractionRing R K₁]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [PerfectField (IsLocalRing.ResidueField R)]
    {ι : Type v} [Finite ι] (E : ι → Type uD₁) (S : ι → Type uD₂)
    [∀ i, Field (E i)] [∀ i, CommRing (S i)] [∀ i, IsDomain (S i)]
    [∀ i, IsDiscreteValuationRing (S i)]
    [∀ i, Algebra K (E i)] [∀ i, Algebra K₁ (E i)] [∀ i, Algebra L (E i)]
    [∀ i, IsScalarTower K K₁ (E i)]
    [∀ i, Algebra R (S i)] [∀ i, IsDiscreteValuationRing.IsExtension R (S i)]
    [∀ i, Algebra B (S i)] [∀ i, Algebra.IsIntegral B (S i)]
    [∀ i, Algebra R (E i)] [∀ i, Algebra (S i) (E i)]
    [∀ i, IsFractionRing (S i) (E i)]
    [∀ i, IsScalarTower R (S i) (E i)] [∀ i, IsScalarTower R K₁ (E i)]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (S i)) (S i)]
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i =
      algebraMap L (E i) l)
    (hright : ∀ i (a : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) a)) i =
      algebraMap K₁ (E i) a)
    (hA : ∀ a : A, algebraMap K K₁ (algebraMap A K a) =
      algebraMap R K₁ (algebraMap A R a))
    (hB : ∀ i b, algebraMap L (E i) (algebraMap B L b) =
      algebraMap (S i) (E i) (algebraMap B (S i) b))
    (hsquare : ∀ i a, algebraMap B (S i) (algebraMap A B a) =
      algebraMap R (S i) (algebraMap A R a))
    (hsol : ∀ i, ∃ (F : Type uF) (_ : Field F) (_ : Algebra K₁ F) (_ : Algebra R F)
      (_ : IsScalarTower R K₁ F) (_ : Module.Finite K₁ F),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uC,uD₂,uF,uD₁,uF,
        max uD₁ uF,uF,max uD₁ uF} R (S i) K₁ (E i) F, D.IsWeakSolution) :
    ∃ (F : Type uF) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA,uB,uK,uL,uF,
        max uL uF,uF,max uL uF} A B K L F, D.IsWeakSolution := by
  refine exists_finite_extension_isWeakSolution_of_factor_solutions A B K L K₁ R E S
    hA hB hsquare hsol (reducedTensorPiEquivOfRight K L K₁ E decomp hright) hleft

/-- **The all-conjugates bridge, with the factor decomposition discharged.**

Same conclusion as `exists_finite_extension_isWeakSolution_of_reducedFactorSolutions`, but the
caller no longer supplies the decomposition: its existence is
`exists_tensorProduct_quotNilradical_equiv_pi_fields`, so the only thing owed is a weak solution at
each factor of whatever decomposition is handed over.  What remains of the hypothesis is therefore
exactly the mathematical content — the per-factor solutions — with no presentation data attached.

The hypothesis quantifies over the decomposition rather than fixing one.  That costs nothing in
practice: the factors of `(L ⊗[K] K₁) ⧸ nilradical` are its quotients by the maximal ideals, so any
two decompositions differ by a permutation and factorwise isomorphism, and a construction solving
one solves them all.  It does mean `hfactors` must be established for the decomposition it is
given, which is the honest form of "solve every conjugate factor": no factor may be singled out,
and in particular the distinguished compositum carries no privilege — the error of the Stacks proof
of Tag 09ET (3).

Everything is taken in a single universe, which is where the decomposition theorem and the combiner
meet.  As in `exists_finite_extension_isWeakSolution_of_reducedFactorSolutions`, the combiner uses
completeness of `R` and of the factor rings, and perfectness of the residue field of `R`. -/
theorem exists_finite_extension_isWeakSolution_of_forall_reducedFactorSolutions
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ R : Type uK)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Module.Finite K K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R]
    [Algebra R K₁] [IsFractionRing R K₁]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [PerfectField (IsLocalRing.ResidueField R)]
    (hA : ∀ a : A, algebraMap K K₁ (algebraMap A K a) =
      algebraMap R K₁ (algebraMap A R a))
    (hfactors : ∀ (n : ℕ) (E : Fin n → Type (max uL uK)) (_ : ∀ i, Field (E i))
      (_ : ∀ i, Algebra K (E i)) (_ : ∀ i, Algebra L (E i)) (_ : ∀ i, Algebra K₁ (E i))
      (_ : ∀ i, IsScalarTower K L (E i)) (_ : ∀ i, IsScalarTower K K₁ (E i))
      (_ : ∀ i, Module.Finite L (E i))
      (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i),
      (∀ i (l : L), decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i =
        algebraMap L (E i) l) →
      (∀ i (a : K₁), decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) a)) i =
        algebraMap K₁ (E i) a) →
      ∃ (S : Fin n → Type (max uL uK)) (_ : ∀ i, CommRing (S i)) (_ : ∀ i, IsDomain (S i))
        (_ : ∀ i, IsDiscreteValuationRing (S i)) (_ : ∀ i, Algebra R (S i))
        (_ : ∀ i, IsDiscreteValuationRing.IsExtension R (S i))
        (_ : ∀ i, Algebra B (S i)) (_ : ∀ i, Algebra.IsIntegral B (S i))
        (_ : ∀ i, Algebra R (E i)) (_ : ∀ i, Algebra (S i) (E i))
        (_ : ∀ i, IsFractionRing (S i) (E i))
        (_ : ∀ i, IsScalarTower R (S i) (E i)) (_ : ∀ i, IsScalarTower R K₁ (E i))
        (_ : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (S i)) (S i)),
        (∀ i b, algebraMap L (E i) (algebraMap B L b) =
            algebraMap (S i) (E i) (algebraMap B (S i) b)) ∧
          (∀ i a, algebraMap B (S i) (algebraMap A B a) =
            algebraMap R (S i) (algebraMap A R a)) ∧
          ∀ i, ∃ (F : Type uK) (_ : Field F) (_ : Algebra K₁ F) (_ : Algebra R F)
            (_ : IsScalarTower R K₁ F) (_ : Module.Finite K₁ F),
            ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uK, max uL uK, uK, max uL uK,
              uK, max uL uK, uK, max uL uK}
              R (S i) K₁ (E i) F, D.IsWeakSolution) :
    ∃ (F : Type uK) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK, max uL uK, uK,
        max uL uK} A B K L F,
        D.IsWeakSolution := by
  obtain ⟨n, E, hEfield, hEK, hEL, hEK₁, hEKL, hEKK₁, hEfin, decomp, -, hleft, hright⟩ :=
    exists_tensorProduct_quotNilradical_equiv_pi_fields.{uK, uL, uK, uL} K L K₁
  let := hEfield
  let := hEK
  let := hEL
  let := hEK₁
  let := hEKL
  let := hEKK₁
  let := hEfin
  obtain ⟨S, hScomm, hSdom, hSdvr, hRS, hRSext, hBS, hBSint, hRE, hSE, hSEfrac,
    hRSE, hRK₁E, hScomplete, hB, hsquare, hsol⟩ :=
    hfactors n E hEfield hEK hEL hEK₁ hEKL hEKK₁ hEfin decomp hleft hright
  let := hScomm
  let := hSdom
  let := hSdvr
  let := hRS
  let := hRSext
  let := hBS
  let := hBSint
  let := hRE
  let := hSE
  let := hSEfrac
  let := hRSE
  let := hRK₁E
  let := hScomplete
  exact exists_finite_extension_isWeakSolution_of_reducedFactorSolutions A B K L K₁ R E S
    decomp hleft hright hA hB hsquare hsol

/-- **The all-conjugates bridge, synchronized over one shared second extension.**

Let `A ⊆ B` be an extension of discrete valuation rings with fraction fields `K ⊆ L`, let `K₁ / K`
be finite with `R` a discrete valuation ring integral over `A` and fraction field `K₁`, and let
`K₂ / K₁` be a further finite extension. Given a base change `D₂` of `A → B` along `K₂`, if every
field factor of the reduced base change `(L ⊗[K] K₁) ⧸ nilradical` admits a weak solution
**packaged over that very same `K₂`**, then `D₂` is a weak solution.

This differs from `exists_finite_extension_isWeakSolution_of_forall_reducedFactorSolutions` in
where the second extension comes from, and that difference is the whole point.

* There, each factor supplies its *own* finite extension `F` of `K₁`, and the combiner must
  afterwards amalgamate the family `{F i}` into one common overfield. Preserving a weak solution
  across that amalgamation is what forces `R` to be complete with perfect residue field and each
  factor ring to be complete.
* Here `K₂` is fixed **before** the factors are examined, and the hypothesis is that all of them
  are solved over it simultaneously. There is nothing left to amalgamate, so the completeness and
  `PerfectField` assumptions are simply absent: this routes through
  `isWeakSolution_of_iterated_packages` directly, which asks for none of them.
* And the conclusion is correspondingly sharper. There it is the mere *existence* of some finite
  extension of `K` that solves `A → B`. Here it is that the caller's own `D₂` is a weak solution —
  the identified base change, not an unnamed one.

The cost of dropping those hypotheses is that synchronization is now the caller's obligation: a
single `K₂` must work for every factor at once. That is a real demand, and it is the honest place
to put it. What it is *not* is a licence to constrain one factor and infer the rest. As in the
unsynchronized bridge, `hfactors` is quantified over every index of the decomposition it is handed;
no factor is distinguished and the distinguished compositum carries no privilege. The conjugate
factors are pairwise distinct (`Stacks.WeakSolution.Obstruction.conjugateFactor_injective`) and the
  conjugate condition
can genuinely fail, so the step of the Stacks proof
of Tag 09ET (3) that descends along one embedding is not available and is not used.

The factor decomposition is discharged internally by
`exists_tensorProduct_quotNilradical_equiv_pi_fields`, so no presentation data is owed; the
hypothesis quantifies over the decomposition rather than fixing one, which costs nothing since the
factors are the quotients by the maximal ideals and any two decompositions differ by a permutation
and factorwise isomorphism. -/
theorem isWeakSolution_of_forall_reducedFactorPackages
    (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ K₂ R : Type uK)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Module.Finite K K₁]
    [Algebra K K₂] [Algebra K₁ K₂] [Algebra A K₂]
    [IsScalarTower K K₁ K₂] [Module.Finite K K₂] [Module.Finite K₁ K₂]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₂]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R]
    [Algebra R K₁] [IsFractionRing R K₁] [Algebra R K₂] [IsScalarTower R K₁ K₂]
    (D₂ : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK, max uL uK, uK, max
      uL uK} A B K L K₂)
    (hA : ∀ a : A, algebraMap A K₂ a = algebraMap R K₂ (algebraMap A R a))
    (hfactors : ∀ (n : ℕ) (E : Fin n → Type (max uL uK)) (_ : ∀ i, Field (E i))
      (_ : ∀ i, Algebra K (E i)) (_ : ∀ i, Algebra L (E i)) (_ : ∀ i, Algebra K₁ (E i))
      (_ : ∀ i, IsScalarTower K L (E i)) (_ : ∀ i, IsScalarTower K K₁ (E i))
      (_ : ∀ i, Module.Finite L (E i))
      (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i),
      (∀ i (l : L), decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i =
        algebraMap L (E i) l) →
      (∀ i (a : K₁), decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) a)) i =
        algebraMap K₁ (E i) a) →
      ∃ (S : Fin n → Type (max uL uK)) (_ : ∀ i, CommRing (S i)) (_ : ∀ i, IsDomain (S i))
        (_ : ∀ i, IsDiscreteValuationRing (S i)) (_ : ∀ i, Algebra R (S i))
        (_ : ∀ i, IsDiscreteValuationRing.IsExtension R (S i))
        (_ : ∀ i, Algebra B (S i)) (_ : ∀ i, Algebra.IsIntegral B (S i))
        (_ : ∀ i, Algebra R (E i)) (_ : ∀ i, Algebra (S i) (E i))
        (_ : ∀ i, IsFractionRing (S i) (E i))
        (_ : ∀ i, IsScalarTower R (S i) (E i)) (_ : ∀ i, IsScalarTower R K₁ (E i)),
        (∀ i b, algebraMap L (E i) (algebraMap B L b) =
            algebraMap (S i) (E i) (algebraMap B (S i) b)) ∧
          (∀ i a, algebraMap B (S i) (algebraMap A B a) =
            algebraMap R (S i) (algebraMap A R a)) ∧
          ∀ i, ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uK, max uL uK, uK, max uL
            uK, uK, max uL uK, uK, max uL uK}
            R (S i) K₁ (E i) K₂, D.IsWeakSolution) :
    D₂.IsWeakSolution := by
  classical
  obtain ⟨n, E, hEfield, hEK, hEL, hEK₁, hEKL, hEKK₁, hEfin, decomp, -, hleft, hright⟩ :=
    exists_tensorProduct_quotNilradical_equiv_pi_fields.{uK, uL, uK, uL} K L K₁
  let := hEfield
  let := hEK
  let := hEL
  let := hEK₁
  let := hEKL
  let := hEKK₁
  let := hEfin
  obtain ⟨S, hScomm, hSdom, hSdvr, hRS, hRSext, hBS, hBSint, hRE, hSE, hSEfrac,
    hRSE, hRK₁E, hB, hsquare, hsol⟩ :=
    hfactors n E hEfield hEK hEL hEK₁ hEKL hEKK₁ hEfin decomp hleft hright
  let := hScomm
  let := hSdom
  let := hSdvr
  let := hRS
  let := hRSext
  let := hBS
  let := hBSint
  let := hRE
  let := hSE
  let := hSEfrac
  let := hRSE
  let := hRK₁E
  choose D hD using hsol
  refine isWeakSolution_of_iterated_packages A B K L K₁ K₂ R D₂ E S hA hB hsquare D hD
    (reducedTensorPiEquivOfRight K L K₁ E decomp hright) hleft

/-- **One finite normal base change absorbs a finite coefficient set in every conjugate factor.**

Given finitely many elements of `L` integral over `K`, there is a finite normal extension `K₁ / K`
such that in **every** field factor of **every** decomposition of `(L ⊗[K] K₁) ⧸ nilradical`, each
of those elements lies in the image of `K₁`.

This is the finite-coefficient mechanism that makes an all-factor argument possible, and it is the
reason no universal statement about the perfect core is required.  `K₁` is built from the finitely
many coefficients in play — the splitting field of the product of their minimal polynomials
(`Stacks.EppTheorem.exists_normal_finite_minpoly_representatives`) — and normality is what makes it
  serve
all the conjugates at once: once a normal extension contains one root of a minimal polynomial it
contains them all, so the factor indexed by any embedding is covered, not merely the factor at a
distinguished one (`Stacks.EppTheorem.finset_maps_mem_fieldRange_of_normal`).

Contrast the perfect core, which need not be finite over the residue field of the base and
therefore cannot be absorbed this way; nothing here asserts that it can.

The general form, in which the normal extension sits strictly inside the base change, is
`Stacks.EppTheorem.finset_maps_mem_fieldRange_of_normal` applied factorwise. -/
theorem exists_finite_normal_baseChange_forall_reducedFactor_mem_fieldRange
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    (s : Finset L) (hint : ∀ x ∈ s, IsIntegral K x) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : FiniteDimensional K K₁)
      (_ : Normal K K₁),
      ∀ (n : ℕ) (E : Fin n → Type u) (_ : ∀ i, Field (E i)) (_ : ∀ i, Algebra K (E i))
        (_ : ∀ i, Algebra L (E i)) (_ : ∀ i, Algebra K₁ (E i))
        (_ : ∀ i, IsScalarTower K L (E i)) (_ : ∀ i, IsScalarTower K K₁ (E i))
        (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i),
        (∀ i (l : L), decomp (Ideal.Quotient.mk _
            ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i =
          algebraMap L (E i) l) →
        ∀ (i : Fin n), ∀ x ∈ s, decomp (Ideal.Quotient.mk _
            ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) x)) i ∈
          (algebraMap K₁ (E i)).fieldRange := by
  obtain ⟨N, hNfield, hNalg, hNfin, hNnormal, hrep⟩ :=
    Stacks.EppTheorem.exists_normal_finite_minpoly_representatives s hint
  let := hNfield
  let := hNalg
  let := hNfin
  let := hNnormal
  refine ⟨N, hNfield, hNalg, hNfin, hNnormal, ?_⟩
  intro n E hEfield hEK hEL hEN hEKL hEKN decomp hleft i x hx
  let := hEfield
  let := hEK
  let := hEL
  let := hEN
  let := hEKL
  let := hEKN
  rw [hleft i x]
  exact Stacks.EppTheorem.finset_maps_mem_fieldRange_of_normal (N := N) s
    (fun y hy => ⟨hint y hy, hrep y hy⟩) x hx

end IsDiscreteValuationRing
