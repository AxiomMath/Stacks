module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedTensorFree
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedTensorFreeFinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateExpansionSupport
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare

/-!
# The hypotheses `hinj` and `hlift` of [Stacks, Tag 07JH] at the divided power polynomial algebra

`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedTensorFree.lean` proves the injectivity
hypothesis `hinj` of [Stacks, Tag 07JH] *from a basis of `Ω` carried as a hypothesis*, because at
the time it was written the freeness of the module of divided power differentials on the `d x_i`
was `private` inside the proof of the divided power Poincaré lemma.  It is no longer private:
`Crystalline.dividedPowerDifferentialsBasis` of
`StacksFrontier/AlgebraicGeometry/Crystalline/DividedPowerPoincare.lean` is that basis.  This module
feeds it to the two statements of `CompletedTensorFree` that ask for one, so that at
`Ω = Ω¹_{P/A,δ}` for `P = A⟨x_w : w ∈ W⟩` the divided power polynomial algebra the hypothesis is
discharged rather than assumed.

For `hinj` the index type `W` is arbitrary — in particular infinite is allowed — and no
Hausdorffness hypothesis is carried beyond item (07JB), which the first-order crystal data
already have.

The factorisation hypothesis `hlift` is discharged here too, at the same `Ω`, through
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedTensorFreeFinite.lean`, but **only for `W`
finite**.  That asymmetry is real and not an artefact: `hinj` is `p`-adic Hausdorffness of
`M ⊗_P Ω`, which is coordinatewise in a basis, while `hlift` rests on `p`-adic *precompleteness*
of the same module, and the finitely supported families in a complete module are complete only
over a finite index type.

**What this is and is not.**  It is the two algebraic hypotheses of the tag at one concrete `Ω`,
and nothing more.

* No `@[stacks 07JH]` attribute is placed here: [Stacks, Tag 07JH] is
  `...SmallSite.crystalPairFunctor_isEquivalence` of `SmallSite/CrystalPairEquivalence.lean`,
  which does not go through the reduction below.  Of the three hypotheses of
  `Crystalline.GlobalCrystallineSituation.SmallSite.equivalence07JH_of_isEquivalence_functor`,
  this discharges `hinj` for any `W` and `hlift` for `W` finite.  What remains is
  `Functor.IsEquivalence Rd.functor` — the geometric half, which by
  `Crystalline.GlobalCrystallineSituation.SmallSite.faithful_functor07JG_iff` contains the
  faithfulness half of the tag's own conclusion — and under it a term of
  `Crystalline.GlobalCrystallineSituation.SmallSite.Reduction07JG`, which the library assembles
  only from levelwise inputs (`...SmallSite.reduction07JGWholeSpaceOfLevelwise`); see the note on
  `equivalence07JH_of_isEquivalence_functor_dividedPowerDifferentials_of_finite` below for which
  of its fields are available.
* `Ω` is the differentials of the divided power *polynomial* algebra, not of the `p`-adically
  completed divided power envelope `D` that the source's own situation takes.  The envelope is a
  quotient of a completion of such a `P`, and the library has no statement that its differentials
  are free, so the instantiation below is a special case of the tag's setting and is stated as
  one.  The general statements in `CompletedTensorFree` continue to carry the basis.

## Main results

* `Crystalline.forall_injective_toCompletedTensor_dividedPowerDifferentials` — the hypothesis
  `hinj`, verbatim and with no freeness hypothesis, when `Ω` is the module of divided power
  differentials of the divided power polynomial algebra.
* `Crystalline.equivalence07JH_of_isEquivalence_functor_dividedPowerDifferentials` — the
  reduction of [Stacks, Tag 07JH] at that `Ω` with two hypotheses rather than three.
* `Crystalline.forall_exists_firstOrderConnection_dividedPowerDifferentials` — the hypothesis
  `hlift`, verbatim and with nothing carried, at the same `Ω` for `W` finite.
* `Crystalline.equivalence07JH_of_isEquivalence_functor_dividedPowerDifferentials_of_finite` —
  **the reduction of [Stacks, Tag 07JH] at that `Ω`, for `W` finite, with one hypothesis rather
  than three.**
* `Crystalline.finite_notMem_pPowSmul_dividedPowerDifferentials` — the hypothesis `hsupp` of the
  Taylor convergence theorem at the same `Ω`, through
  `Crystalline.finite_notMem_pPowSmul_of_isCoordinateExpansion` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/CoordinateExpansionSupport.lean`.

## References

* [Stacks Project, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
-/

@[expose] public section

open scoped TensorProduct

universe u uI w

namespace Crystalline

open DividedPowers

attribute [local instance low] setIndexedDividedPowerPolynomialCommRing
  coefficientDividedPowerRingAlgebra setIndexedDividedPowerPolynomialAlgebra'
  setIndexedDividedPowerPolynomialDividedPowerRingAlgebra

attribute [local implicit_reducible] coefficientDividedPowerRing
  DividedPowers.setIndexedDividedPowerPolynomialDividedPowerRing

section Hinj

variable (A : Type u) [CommRing A] (W : Type u)
  [Module (↑(setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W))ᵐᵒᵖ
    (dividedPowerDifferentials (A := A)
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W).dividedPowers)]
  [IsCentralScalar (↑(setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W))
    (dividedPowerDifferentials (A := A)
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W).dividedPowers)]
  {g : A →+* ↑(setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W)}
  (d : DividedPowerDerivation A
    (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W) g
    (dividedPowerDifferentials (A := A)
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W).dividedPowers))
  (p : ℕ) {κ : Type uI}
  (dx : κ → dividedPowerDifferentials (A := A)
    (setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W).dividedPowers)

/-- **The hypothesis `hinj` of [Stacks, Tag 07JH] for the divided power polynomial algebra, with
no freeness hypothesis carried.**  For `P = A⟨x_w : w ∈ W⟩` and `Ω = Ω¹_{P/A,δ}` the canonical map
`M ⊗_P Ω → M ⊗̂_P Ω` is injective on the module of every first-order crystal datum.

This is `Crystalline.forall_injective_toCompletedTensor_of_basis` fed
`Crystalline.dividedPowerDifferentialsBasis`, the basis of `Ω` on the differentials of the
variables.  The index type `W` is arbitrary, and the only Hausdorffness used is item (07JB),
which is a field of the data.

The two instance arguments are the right action of `P` on `Ω` and its agreement with the left
action.  They carry no mathematical content — `P` is commutative — but
`Crystalline.FirstOrderCrystal` cannot be formed without them, so they are arguments here exactly
as they are variables of the general statement. -/
theorem forall_injective_toCompletedTensor_dividedPowerDifferentials :
    ∀ Q : FirstOrderCrystal.{u, u, u, uI, u} A
      (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W) g
      (dividedPowerDifferentials (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers) d p dx,
      Function.Injective (toCompletedTensor p
        (↑(setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W))
        (dividedPowerDifferentials (A := A)
          (setIndexedDividedPowerPolynomialDividedPowerRing
            (coefficientDividedPowerRing A) W).dividedPowers) Q.carrier) :=
  forall_injective_toCompletedTensor_of_basis (d := d) p dx (dividedPowerDifferentialsBasis A W)

end Hinj

section Reduction

open CategoryTheory AlgebraicGeometry GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (A : Type u) [CommRing A] (W : Type u)
  [Module (↑(setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W))ᵐᵒᵖ
    (dividedPowerDifferentials (A := A)
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W).dividedPowers)]
  [IsCentralScalar (↑(setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W))
    (dividedPowerDifferentials (A := A)
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W).dividedPowers)]
  {g : A →+* ↑(setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W)}
  {d : DividedPowerDerivation A
    (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W) g
    (dividedPowerDifferentials (A := A)
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W).dividedPowers)}
  {p : ℕ} {ι : Type uI}
  {dx : ι → dividedPowerDifferentials (A := A)
    (setIndexedDividedPowerPolynomialDividedPowerRing
      (coefficientDividedPowerRing A) W).dividedPowers}
  [IsAffine S.X] [IsAffine S.S.scheme] {hp : IsNilpotent (S.p : Γ(S.X, ⊤))}

/-- **At `Ω = Ω¹_{P/A,δ}` the reduction of [Stacks, Tag 07JH] has two open hypotheses, not
three.**  The theorem
`Crystalline.GlobalCrystallineSituation.SmallSite.equivalence07JH_of_isEquivalence_functor`
reduces the tag, for a given reduction datum, to `Functor.IsEquivalence Rd.functor`, the
injectivity hypothesis `hinj` and the factorisation `hlift`.  At the differentials of the divided
power polynomial algebra the middle one is a theorem,
`Crystalline.forall_injective_toCompletedTensor_dividedPowerDifferentials`, so only the outer two
are left.

No `@[stacks 07JH]` attribute is placed on this reduction; [Stacks, Tag 07JH] is
`...SmallSite.crystalPairFunctor_isEquivalence`.  Two hypotheses remain here, and the statement is
about a given reduction datum: every producer of
`Crystalline.GlobalCrystallineSituation.SmallSite.Reduction07JG` in the library consumes a datum
of its own, so no closed term of it has been constructed, and
`StacksFrontier/AlgebraicGeometry/Crystalline/Reduction07JGWitness.lean` exhibits a
`PreReduction07JG` that fails its remaining field. -/
theorem equivalence07JH_of_isEquivalence_functor_dividedPowerDifferentials
    (Rd : Reduction07JG S A
      (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W) g
      (dividedPowerDifferentials (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers) d p dx hp)
    (hR : Functor.IsEquivalence Rd.functor)
    (hlift : ∀ P : Pair.{u, u, uI, u} p
      (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W)
      (dividedPowerDifferentials (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers) dx
      (derivationFun A
        (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W) g
        (dividedPowerDifferentials (A := A)
          (setIndexedDividedPowerPolynomialDividedPowerRing
            (coefficientDividedPowerRing A) W).dividedPowers) d),
      ∃ nabla : FirstOrderConnection
        (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W)
        (dividedPowerDifferentials (A := A)
          (setIndexedDividedPowerPolynomialDividedPowerRing
            (coefficientDividedPowerRing A) W).dividedPowers)
        (derivationFun A
          (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W) g
          (dividedPowerDifferentials (A := A)
            (setIndexedDividedPowerPolynomialDividedPowerRing
              (coefficientDividedPowerRing A) W).dividedPowers) d) P.carrier,
        ∀ m : P.carrier, toCompletedTensor p
          (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W)
          (dividedPowerDifferentials (A := A)
            (setIndexedDividedPowerPolynomialDividedPowerRing
              (coefficientDividedPowerRing A) W).dividedPowers) P.carrier
          (TensorProduct.comm
            (↑(setIndexedDividedPowerPolynomialDividedPowerRing
              (coefficientDividedPowerRing A) W))
            (dividedPowerDifferentials (A := A)
              (setIndexedDividedPowerPolynomialDividedPowerRing
                (coefficientDividedPowerRing A) W).dividedPowers) P.carrier (nabla m)) =
            P.nabla m) :
    Equivalence07JH Rd :=
  equivalence07JH_of_isEquivalence_functor Rd hR
    (forall_injective_toCompletedTensor_dividedPowerDifferentials A W d p dx) hlift

/-- **The hypothesis `hlift` of [Stacks, Tag 07JH] at the divided power polynomial algebra in
finitely many variables, with nothing carried.**  For `P = A⟨x_w : w ∈ W⟩` with `W` finite and
`Ω = Ω¹_{P/A,δ}` the connection of every pair factors through the uncompleted tensor product
`M ⊗_P Ω`.

This is `Crystalline.forall_exists_firstOrderConnection_of_finite_basis` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedTensorFreeFinite.lean` fed
`Crystalline.dividedPowerDifferentialsBasis`, the basis of `Ω` on the differentials of the
variables, whose index type is `W` itself.

`[Finite W]` is the one thing added, and unlike the index type of
`Crystalline.forall_injective_toCompletedTensor_dividedPowerDifferentials` it cannot be dropped:
the hypothesis rests on `p`-adic *precompleteness* of `M ⊗_P Ω`, and the finitely supported
families in a complete module are complete only for a finite index type — the limit of a
coordinatewise convergent family need not be finitely supported.  So this statement and the
injectivity one are genuinely different in their hypotheses, not uniformly so. -/
theorem forall_exists_firstOrderConnection_dividedPowerDifferentials [Finite W] :
    ∀ P : Pair.{u, u, uI, u} p
      (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W)
      (dividedPowerDifferentials (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers) dx
      (derivationFun A
        (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W) g
        (dividedPowerDifferentials (A := A)
          (setIndexedDividedPowerPolynomialDividedPowerRing
            (coefficientDividedPowerRing A) W).dividedPowers) d),
      ∃ nabla : FirstOrderConnection
        (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W)
        (dividedPowerDifferentials (A := A)
          (setIndexedDividedPowerPolynomialDividedPowerRing
            (coefficientDividedPowerRing A) W).dividedPowers)
        (derivationFun A
          (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W) g
          (dividedPowerDifferentials (A := A)
            (setIndexedDividedPowerPolynomialDividedPowerRing
              (coefficientDividedPowerRing A) W).dividedPowers) d) P.carrier,
        ∀ m : P.carrier, toCompletedTensor p
          (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W)
          (dividedPowerDifferentials (A := A)
            (setIndexedDividedPowerPolynomialDividedPowerRing
              (coefficientDividedPowerRing A) W).dividedPowers) P.carrier
          (TensorProduct.comm
            (↑(setIndexedDividedPowerPolynomialDividedPowerRing
              (coefficientDividedPowerRing A) W))
            (dividedPowerDifferentials (A := A)
              (setIndexedDividedPowerPolynomialDividedPowerRing
                (coefficientDividedPowerRing A) W).dividedPowers) P.carrier (nabla m)) =
            P.nabla m :=
  forall_exists_firstOrderConnection_of_finite_basis A _ g _ d p dx
    (dividedPowerDifferentialsBasis A W)

/-- **At `Ω = Ω¹_{P/A,δ}` with finitely many variables the reduction of [Stacks, Tag 07JH] has
one open hypothesis, not three.**
`Crystalline.GlobalCrystallineSituation.SmallSite.equivalence07JH_of_isEquivalence_functor`
reduces the tag, for a given reduction datum, to `Functor.IsEquivalence Rd.functor`, the
injectivity hypothesis `hinj` and the factorisation `hlift`.  At the differentials of the divided
power polynomial algebra in finitely many variables both of the latter are theorems —
`Crystalline.forall_injective_toCompletedTensor_dividedPowerDifferentials` and
`Crystalline.forall_exists_firstOrderConnection_dividedPowerDifferentials` — so the geometric
hypothesis is all that is left.

No `@[stacks 07JH]` attribute is placed on this reduction; [Stacks, Tag 07JH] is
`...SmallSite.crystalPairFunctor_isEquivalence`, which does not go through it.

* `Functor.IsEquivalence Rd.functor` is not discharged here and is not a weak hypothesis: by
  `Crystalline.GlobalCrystallineSituation.SmallSite.faithful_functor07JG_iff` its faithfulness
  half is exactly the faithfulness half of the tag's conclusion.
* The statement is about a given reduction datum, and every producer of
  `Crystalline.GlobalCrystallineSituation.SmallSite.Reduction07JG` in the library consumes a
  datum of its own, so no closed term of it has been constructed.  Of its twelve fields two are
  available at the source's own system of levels — `levelSystem` and `ringEquiv`, the latter
  being `Crystalline.GlobalCrystallineSituation.SmallSite.envelopeLevelRingLimitEquiv` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/WholeSpaceSystemLevelRings.lean` — and
  `levelSystem_isLevel` holds there by reflexivity.  The field `functor` is now assembled too,
  as `...SmallSite.LevelComparison07JG.functor` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/LevelFirstOrderCrystal.lean`, from the comparison
  datum of the levels; what that datum still asks for, and what
  `...SmallSite.levelReduction07JGOfLevelwise` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelReductionAssembly.lean` consumes, is
  the differentials `...SmallSite.LevelForms07JG` of the levels, the bijectivity field
  `...SmallSite.LevelBaseChangeData.bijective_extensionSectionsMap`, and the source's own `D(1)`
  and `D(2)` coefficient computations.
  `StacksFrontier/AlgebraicGeometry/Crystalline/Reduction07JGWitness.lean` exhibits a
  `PreReduction07JG` over the zero ring that fails `levelSystem_isLevel`. -/
theorem equivalence07JH_of_isEquivalence_functor_dividedPowerDifferentials_of_finite [Finite W]
    (Rd : Reduction07JG S A
      (setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W) g
      (dividedPowerDifferentials (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers) d p dx hp)
    (hR : Functor.IsEquivalence Rd.functor) :
    Equivalence07JH Rd :=
  equivalence07JH_of_isEquivalence_functor_dividedPowerDifferentials A W Rd hR
    (forall_exists_firstOrderConnection_dividedPowerDifferentials A W)

end Reduction

/-! ### The hypothesis `hsupp` at the same `Ω` -/

section Hsupp

variable (A : Type u) [CommRing A] (W : Type u) (p : ℕ) {M : Type w} [AddCommGroup M]
  [Module (↑(setIndexedDividedPowerPolynomialDividedPowerRing
    (coefficientDividedPowerRing A) W)) M]
  {dd : ↑(setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W) →
    dividedPowerDifferentials (A := A)
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W).dividedPowers}
  {nabla : CompletedConnection p
    (↑(setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W))
    (dividedPowerDifferentials (A := A)
      (setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W).dividedPowers) dd M}
  {theta : W → (M → M)}

/-- **The hypothesis `hsupp` of the Taylor convergence theorem at the divided power polynomial
algebra, with nothing carried.**  If the coordinate expansion `∇ m = ∑_w θ_w(m) d x_w` of a
completed connection converges, with the `d x_w` the differentials of the variables themselves,
then for every `n` only finitely many `w` have `θ_w(m) ∉ p^n M`.

This is `Crystalline.finite_notMem_pPowSmul_of_isCoordinateExpansion` with its basis supplied by
`Crystalline.dividedPowerDifferentialsBasis`, whose `w`-th vector is `d x_w`.  The index type `W`
is arbitrary. -/
theorem finite_notMem_pPowSmul_dividedPowerDifferentials
    (hco : IsCoordinateExpansion p
      (↑(setIndexedDividedPowerPolynomialDividedPowerRing (coefficientDividedPowerRing A) W))
      (dividedPowerDifferentials (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers)
      (fun i ↦ dividedPowerDifferential (A := A)
        (setIndexedDividedPowerPolynomialDividedPowerRing
          (coefficientDividedPowerRing A) W).dividedPowers
        (dividedPowerPolynomialVariable (coefficientDividedPowerRing A) i)) nabla theta)
    (m : M) (n : ℕ) :
    {i : W | theta i m ∉ pPowSmul p
      (↑(setIndexedDividedPowerPolynomialDividedPowerRing
        (coefficientDividedPowerRing A) W)) M n}.Finite :=
  finite_notMem_pPowSmul_of_isCoordinateExpansion p _ _ M hco
    (dividedPowerDifferentialsBasis A W)
    (fun i ↦ (dividedPowerDifferentialsBasis_apply A W i).symm) m n

end Hsupp

end Crystalline

end
