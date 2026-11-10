module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeComposite
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeIsoValues
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootCompletedAssembly
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootGenuineBaseChange

/-!
# Tag 07N1: the completed de Rham complexes along a `p`-th root extension

This module proves [Stacks, Lemma 60.25.3, Tag 07N1].  Let `(D, J̄, γ̄)` be a divided power ring
over `A` with `p` nilpotent modulo `J̄`, let `λ ∈ D`, let `D'` be the `p`-adic completion of
`D[z]⟨ξ⟩/(ξ - (z^p - λ))` and let `Ω^•_{D'}` be the `p`-adic completion of the divided power forms
of `D'`.  For a `D`-module `M` with an integrable completed connection, the canonical map of
complexes `c_M^• : M ⊗^∧_D Ω^•_D → M ⊗^∧_D Ω^•_{D'}` of (07PY) has a map `e_M^•` in the opposite
direction such that both composites are homotopic to multiplication by `p`.

## How

The proof assembles three pieces.

* At every level `pⁿ` the completed connection induces an integrable connection on `M / pⁿ M`
  (`Crystalline.CompletedLevels.levelConnection`), and the uncompleted form of the lemma —
  [Stacks, Lemma 60.25.2, Tag 07Q7] with the operator `θ` of the source's proof — applies to it
  along `D → B' = D[z]⟨ξ⟩/(ξ - (z^p - λ))`, with `e ∘ c = p` on the nose
  (`Crystalline.PthRootExtension.exists_reverse_pthRootExtension`).
* The reverse maps and homotopies of the levels are compatible with the transition maps, because
  the canonical maps are injective and the integrating homotopy is natural in the module; they
  assemble into a reverse map and homotopy of the completed complexes along `D → B'`
  (`Crystalline.PthRootExtension.completedReverse`,
  `Crystalline.PthRootExtension.completedHomotopy`).
* The base change of completed de Rham complexes along `B' → D'` is bijective in every degree
  (`Crystalline.PthRootExtension.bijective_genuineTransfer`), by [Stacks, Lemma 60.20.1, Tag 07KK]
  at every level, so the data transport from the forms of `B'` to the forms of `D'`.

## Main results

* `Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension` —
  [Stacks, Lemma 60.25.3, Tag 07N1] for every divided power ring with `p` nilpotent modulo its
  divided power ideal; its specialisation to Situation 07MD is in
  `StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootCompletedSituation`.

## Implementation notes

`genuineCompletedTerm` is a `def` with its `AddCommGroup` and `Module` instances stated
explicitly, rather than an `abbrev`.  As an `abbrev` it is reducible, so each of the forty-odd
statements built over it would carry the whole unfolded tower of completed tensors and completed
divided power forms into the term the kernel then had to check.  The axioms are the same either
way; the cost is not.  Cold build times, which is the path a full build takes:

|                             | `abbrev` | `def` |
| --------------------------- | -----: | ----: |
| this module                 | 156 s  | 84 s  |
| its phase 1 (statements)    | 110 s  | 63 s  |
| `PthRootCompletedSituation` | 272 s  | 59 s  |

Phase 1 elaborates the statements with their proofs stubbed out, so most of the cost was in the
statements, and 91 s of this module's total was billed to kernel type checking -- not to tactics,
and not to instance search, which came to 3 s.

Instance search keys a goal into its discrimination tree unfolding only `@[reducible]`
definitions, so it does not find an instance for a `def`: that is what the two `inferInstanceAs`
instances below supply, and why `@[instance_reducible]` is not enough on its own.  Each of them
states the instances of `genuineCompletedTerm`'s *own* underlying type -- the argument of the
`inferInstanceAs` is the body of the definition, and the `Module` is over
`completedPrimeRingSelf B p lam`, the ring that body's `CompletedTensor` is already taken over.
Neither re-indexes a tensor product over a second spelling of its ring, and no ring-sheaf
vocabulary occurs in this module at all.
`genuineCarrier` and `twiceCarrier` are deliberately left as `abbrev`s -- folding them too cuts
this module to 88 s but breaks `PthRootCompletedSituation`, whose statement names
`genuineCarrier` in a context where the corresponding instance is not found.

## References

* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Lemma 60.25.2, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
* [Stacks Project, Tag 07PY](https://stacks.math.columbia.edu/tag/07PY)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
-/

@[expose] public noncomputable section

open DividedPowers Stacks.DeRham.DifferentialDescent

open scoped TensorProduct

universe u

namespace Crystalline

namespace CompletedLevels

/-! ### Transporting the homotopy data along an isomorphism of complexes -/

section Transport

variable (p : ℕ) {S T T' : ℕ → Type*} [∀ q, AddCommGroup (S q)] [∀ q, AddCommGroup (T q)]
  [∀ q, AddCommGroup (T' q)] (dS : ∀ q, S q →+ S (q + 1)) (dT : ∀ q, T q →+ T (q + 1))
  (dT' : ∀ q, T' q →+ T' (q + 1)) (c : ∀ q, S q →+ T q) (Φ : ∀ q, T q ≃+ T' q)
  (hΦ : ∀ q y, dT' q (Φ q y) = Φ (q + 1) (dT q y))
  (e : ∀ q, T q →+ S q) (h : ∀ q, T (q + 1) →+ T q)

/-- Transporting along `Φ` commutes with the differentials. -/
private theorem symm_apply_differential
    (hΦ : ∀ q y, dT' q (Φ q y) = Φ (q + 1) (dT q y)) (q : ℕ) (y : T' q) :
    (Φ (q + 1)).symm (dT' q y) = dT q ((Φ q).symm y) :=
  (Φ (q + 1)).symm_apply_eq.2 (by rw [← hΦ, AddEquiv.apply_symm_apply])

include hΦ in
/-- The transported map is a map of complexes. -/
theorem transport_chain (he : ∀ q y, e (q + 1) (dT q y) = dS q (e q y)) (q : ℕ) (y : T' q) :
    e (q + 1) ((Φ (q + 1)).symm (dT' q y)) = dS q (e q ((Φ q).symm y)) := by
  rw [symm_apply_differential dT dT' Φ hΦ, he]

include hΦ in
/-- The transported homotopy identity in degree zero. -/
theorem transport_zero
    (h0 : ∀ y, h 0 (dT 0 y) = p • y - c 0 (e 0 y)) (y : T' 0) :
    Φ 0 (h 0 ((Φ 1).symm (dT' 0 y))) = p • y - Φ 0 (c 0 (e 0 ((Φ 0).symm y))) := by
  rw [symm_apply_differential dT dT' Φ hΦ, h0, map_sub, map_nsmul, AddEquiv.apply_symm_apply]

include hΦ in
/-- The transported homotopy identity in positive degree. -/
theorem transport_succ
    (hs : ∀ q y, dT q (h q y) + h (q + 1) (dT (q + 1) y) = p • y - c (q + 1) (e (q + 1) y))
    (q : ℕ) (y : T' (q + 1)) :
    dT' q (Φ q (h q ((Φ (q + 1)).symm y))) +
        Φ (q + 1) (h (q + 1) ((Φ (q + 1 + 1)).symm (dT' (q + 1) y))) =
      p • y - Φ (q + 1) (c (q + 1) (e (q + 1) ((Φ (q + 1)).symm y))) := by
  rw [symm_apply_differential dT dT' Φ hΦ, hΦ, ← map_add, hs, map_sub, map_nsmul,
    AddEquiv.apply_symm_apply]

include hΦ in
/-- The transported square-zero identity. -/
theorem transport_sq (hsq : ∀ q y, dT (q + 1) (dT q y) = 0) (q : ℕ) (y : T' q) :
    dT' (q + 1) (dT' q y) = 0 := by
  rw [← (Φ q).apply_symm_apply y, hΦ, hΦ, hsq, map_zero]

include hΦ in
/-- The transported square-zero identity, as an identity of additive maps. -/
theorem transport_comp_eq_zero (hsq : ∀ q, (dT (q + 1)).comp (dT q) = 0) (q : ℕ) :
    (dT' (q + 1)).comp (dT' q) = 0 :=
  AddMonoidHom.ext fun y ↦ transport_sq dT dT' Φ hΦ
    (fun q y ↦ DFunLike.congr_fun (hsq q) y) q y

end Transport

end CompletedLevels

namespace PthRootExtension

open CompletedLevels

section FormsMaps

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (lam : (B : Type u)) (hp : p ≠ 0)
  (hpnil : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))

/-- The structure map `B → D'` factors through `B'`. -/
theorem algebraMap_completedPrimeRingSelf (b : (B : Type u)) :
    algebraMap (B : Type u) (completedPrimeRingSelf B p lam) b =
      algebraMap (primeRing B p lam) (completedPrimeRingSelf B p lam)
        (algebraMap (B : Type u) (primeRing B p lam) b) := by
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply]
  rfl

/-- The rings `B → B' → D'` form a scalar tower. -/
instance isScalarTower_completedPrimeRingSelf :
    IsScalarTower (B : Type u) (primeRing B p lam) (completedPrimeRingSelf B p lam) :=
  IsScalarTower.of_algebraMap_eq (algebraMap_completedPrimeRingSelf B p lam)

/-- **The comparison `Ω̂^q_B → Ω̂^q_{D'}` of completed divided power forms along `B → D'`**, the
composite of the comparisons along `B → B'` and `B' → D'`. -/
def completedPrimeFormsMap (q : ℕ) :
    completedDividedPowerForms p A B.dividedPowers q →ₛₗ[algebraMap (B : Type u)
      (completedPrimeRingSelf B p lam)]
      completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil) q where
  toFun x := genuineCompletedFormsMap A B p lam hp hpnil q (primeCompletedFormsMap A B p lam hp q x)
  map_add' x y := (congrArg (genuineCompletedFormsMap A B p lam hp hpnil q)
    ((primeCompletedFormsMap A B p lam hp q).map_add x y)).trans
    ((genuineCompletedFormsMap A B p lam hp hpnil q).map_add _ _)
  map_smul' b x := (congrArg (genuineCompletedFormsMap A B p lam hp hpnil q)
    ((primeCompletedFormsMap A B p lam hp q).map_smulₛₗ b x)).trans
    (((genuineCompletedFormsMap A B p lam hp hpnil q).map_smulₛₗ _ _).trans
      (congrArg (· • genuineCompletedFormsMap A B p lam hp hpnil q
        (primeCompletedFormsMap A B p lam hp q x))
        (algebraMap_completedPrimeRingSelf B p lam b).symm))

/-- The comparison along `B → D'` as a composite. -/
theorem completedPrimeFormsMap_apply (q : ℕ) (x : completedDividedPowerForms p A B.dividedPowers q)
    :
    completedPrimeFormsMap A B p lam hp hpnil q x =
      genuineCompletedFormsMap A B p lam hp hpnil q (primeCompletedFormsMap A B p lam hp q x) := rfl

/-- The comparison of completed forms along `B' → D'` is multiplicative. -/
theorem genuineCompletedFormsMap_wedge (q : ℕ)
    (x : completedDividedPowerForms p A (primeDividedPowers B p lam hp) q)
    (y : completedDividedPowerForms p A (primeDividedPowers B p lam hp) 1) :
    genuineCompletedFormsMap A B p lam hp hpnil (q + 1)
        (completedDividedPowerWedgeOnRing p A (primeDividedPowers B p lam hp) q x y) =
      completedDividedPowerWedgeOnRing p A (completedPrimeDividedPowers B p lam hp hpnil) q
        (genuineCompletedFormsMap A B p lam hp hpnil q x)
        (genuineCompletedFormsMap A B p lam hp hpnil 1 y) :=
  completedMapDifferentialForms_wedge p A _ _ _ (isDPMorphism_genuineAlgHom A B p lam hp hpnil) q x
      y

/-- The comparison of completed forms along `B' → D'` commutes with the de Rham differentials. -/
theorem genuineCompletedFormsMap_deRham (q : ℕ)
    (x : completedDividedPowerForms p A (primeDividedPowers B p lam hp) q) :
    genuineCompletedFormsMap A B p lam hp hpnil (q + 1)
        (completedDividedPowerDeRham p A (primeDividedPowers B p lam hp) q x) =
      completedDividedPowerDeRham p A (completedPrimeDividedPowers B p lam hp hpnil) q
        (genuineCompletedFormsMap A B p lam hp hpnil q x) :=
  completedMapDifferentialForms_deRham p A _ _ _ (isDPMorphism_genuineAlgHom A B p lam hp hpnil) q x

/-- The comparison of completed forms along `B' → D'` is compatible with the differentials. -/
theorem genuineCompletedFormsMap_differential (b : primeRing B p lam) :
    genuineCompletedFormsMap A B p lam hp hpnil 1
        (completedDividedPowerDifferentialOnRing p A (primeDividedPowers B p lam hp) b) =
      completedDividedPowerDifferentialOnRing p A (completedPrimeDividedPowers B p lam hp hpnil)
        (algebraMap (primeRing B p lam) (completedPrimeRingSelf B p lam) b) :=
  completedMapDifferentialForms_completedFormsDifferential_of p A _ _ _
    (isDPMorphism_genuineAlgHom A B p lam hp hpnil) b

/-- The comparison of completed forms along `B → B'` is multiplicative. -/
theorem primeCompletedFormsMap_wedge (q : ℕ)
    (x : completedDividedPowerForms p A B.dividedPowers q)
    (y : completedDividedPowerForms p A B.dividedPowers 1) :
    primeCompletedFormsMap A B p lam hp (q + 1)
        (completedDividedPowerWedgeOnRing p A B.dividedPowers q x y) =
      completedDividedPowerWedgeOnRing p A (primeDividedPowers B p lam hp) q
        (primeCompletedFormsMap A B p lam hp q x) (primeCompletedFormsMap A B p lam hp 1 y) :=
  completedMapDifferentialForms_wedge p A _ _ _ (isDPMorphism_primeAlgHom A B p lam hp) q x y

/-- The comparison of completed forms along `B → B'` commutes with the de Rham differentials. -/
theorem primeCompletedFormsMap_deRham (q : ℕ)
    (x : completedDividedPowerForms p A B.dividedPowers q) :
    primeCompletedFormsMap A B p lam hp (q + 1)
        (completedDividedPowerDeRham p A B.dividedPowers q x) =
      completedDividedPowerDeRham p A (primeDividedPowers B p lam hp) q
        (primeCompletedFormsMap A B p lam hp q x) :=
  completedMapDifferentialForms_deRham p A _ _ _ (isDPMorphism_primeAlgHom A B p lam hp) q x

/-- The comparison of completed forms along `B → D'` is compatible with the differentials. -/
theorem completedPrimeFormsMap_differential (b : (B : Type u)) :
    completedPrimeFormsMap A B p lam hp hpnil 1
        (completedDividedPowerDifferentialOnRing p A B.dividedPowers b) =
      completedDividedPowerDifferentialOnRing p A (completedPrimeDividedPowers B p lam hp hpnil)
        (algebraMap (B : Type u) (completedPrimeRingSelf B p lam) b) := by
  rw [completedPrimeFormsMap_apply, primeCompletedFormsMap_differential,
    genuineCompletedFormsMap_differential, ← IsScalarTower.algebraMap_apply]

/-- The comparison of completed forms along `B → D'` is multiplicative. -/
theorem completedPrimeFormsMap_wedge (q : ℕ)
    (x : completedDividedPowerForms p A B.dividedPowers q)
    (y : completedDividedPowerForms p A B.dividedPowers 1) :
    completedPrimeFormsMap A B p lam hp hpnil (q + 1)
        (completedDividedPowerWedgeOnRing p A B.dividedPowers q x y) =
      completedDividedPowerWedgeOnRing p A (completedPrimeDividedPowers B p lam hp hpnil) q
        (completedPrimeFormsMap A B p lam hp hpnil q x)
        (completedPrimeFormsMap A B p lam hp hpnil 1 y) :=
  (congrArg (genuineCompletedFormsMap A B p lam hp hpnil (q + 1))
    (primeCompletedFormsMap_wedge A B p lam hp q x y)).trans
    (genuineCompletedFormsMap_wedge A B p lam hp hpnil q _ _)

/-- The comparison of completed forms along `B → D'` commutes with the de Rham differentials. -/
theorem completedPrimeFormsMap_deRham (q : ℕ)
    (x : completedDividedPowerForms p A B.dividedPowers q) :
    completedPrimeFormsMap A B p lam hp hpnil (q + 1)
        (completedDividedPowerDeRham p A B.dividedPowers q x) =
      completedDividedPowerDeRham p A (completedPrimeDividedPowers B p lam hp hpnil) q
        (completedPrimeFormsMap A B p lam hp hpnil q x) :=
  (congrArg (genuineCompletedFormsMap A B p lam hp hpnil (q + 1))
    (primeCompletedFormsMap_deRham A B p lam hp q x)).trans
    (genuineCompletedFormsMap_deRham A B p lam hp hpnil q _)

end FormsMaps

section Target

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (lam : (B : Type u)) (hp : p ≠ 0)
  (hpnil : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))
  (M : Type u) [AddCommGroup M] [Module (B : Type u) M]
  (nabla : CompletedConnection p (B : Type u) (completedDividedPowerForms p A B.dividedPowers 1)
    (completedDividedPowerDifferentialOnRing p A B.dividedPowers) M)

/-- **The base change `M ⊗̂_B D' = (D' ⊗_B M)^∧` of `M` to the ring `D'` of
[Stacks, Tag 07N1].** -/
abbrev genuineCarrier : Type u :=
  CompletedConnection.baseChangeCarrier p (B : Type u) (completedPrimeRingSelf B p lam) M

/-- **The base-changed completed connection on `M ⊗̂_B D'`**, with values in the completed forms
of `D'`. -/
abbrev genuineCompletedConnection :
    CompletedConnection p (completedPrimeRingSelf B p lam)
      (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil) 1)
      (completedDividedPowerDifferentialOnRing p A (completedPrimeDividedPowers B p lam hp hpnil))
      (genuineCarrier B p lam M) :=
  CompletedConnection.baseChange p (B : Type u) (completedPrimeRingSelf B p lam) M
    (completedDividedPowerForms p A B.dividedPowers 1)
    (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil) 1)
    (completedDividedPowerDifferentialOnRing p A (completedPrimeDividedPowers B p lam hp hpnil))
    (completedPrimeFormsMap A B p lam hp hpnil 1) nabla
    (completedDividedPowerDifferentialOnRing_add p A _)
    (completedDividedPowerDifferentialOnRing_mul p A _)
    (completedPrimeFormsMap_differential A B p lam hp hpnil)

/-- The degree-`q` term `M ⊗̂_B Ω^q_{D'}` of the target complex of [Stacks, Tag 07N1]. -/
def genuineCompletedTerm (q : ℕ) : Type u :=
  CompletedTensor p (completedPrimeRingSelf B p lam)
    (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil) q)
    (genuineCarrier B p lam M)

/-- The additive group structure on `M ⊗̂_B Ω^q_{D'}`. -/
instance instAddCommGroupGenuineCompletedTerm (q : ℕ) :
    AddCommGroup (genuineCompletedTerm A B p lam hp hpnil M q) :=
  inferInstanceAs (AddCommGroup (CompletedTensor p (completedPrimeRingSelf B p lam)
    (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil) q)
    (genuineCarrier B p lam M)))

/-- The `D'`-module structure on `M ⊗̂_B Ω^q_{D'}`. -/
instance instModuleGenuineCompletedTerm (q : ℕ) :
    Module (completedPrimeRingSelf B p lam) (genuineCompletedTerm A B p lam hp hpnil M q) :=
  inferInstanceAs (Module (completedPrimeRingSelf B p lam)
    (CompletedTensor p (completedPrimeRingSelf B p lam)
      (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil) q)
      (genuineCarrier B p lam M)))

/-- The differential of the target complex `M ⊗̂_B Ω^•_{D'}`. -/
abbrev genuineCompletedDifferential (q : ℕ) :
    genuineCompletedTerm A B p lam hp hpnil M q →+ genuineCompletedTerm A B p lam hp hpnil M
        (q + 1) :=
  CompletedDeRham.differential p (completedPrimeRingSelf B p lam)
    (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil))
    (completedDividedPowerWedgeOnRing p A (completedPrimeDividedPowers B p lam hp hpnil))
    (completedDividedPowerDeRham p A (completedPrimeDividedPowers B p lam hp hpnil))
    (genuineCarrier B p lam M) (genuineCompletedConnection A B p lam hp hpnil M nabla)
    (isGradedLeibniz_completedDividedPowerOnRing p A _) q

/-- **The canonical map `c_M^•` of [Stacks, Tag 07PY]** along `B → D'`, in degree `q`. -/
abbrev genuineCompletedComparison (q : ℕ) :
    baseCompletedTerm A B p M q →+ genuineCompletedTerm A B p lam hp hpnil M q :=
  CompletedDeRham.baseChangeTerm p (B : Type u) (completedPrimeRingSelf B p lam) M
    (completedDividedPowerForms p A B.dividedPowers)
    (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil))
    (completedPrimeFormsMap A B p lam hp hpnil) q

/-- The base change along `B' → D'` of `M' = M ⊗̂_B B'`. -/
abbrev twiceCarrier : Type u :=
  CompletedConnection.baseChangeCarrier p (primeRing B p lam) (completedPrimeRingSelf B p lam)
    (primeCarrier B p lam M)

/-- The connection of `M' ⊗̂_{B'} D'`. -/
abbrev twiceConnection :=
  CompletedConnection.baseChange p (primeRing B p lam) (completedPrimeRingSelf B p lam)
    (primeCarrier B p lam M) (completedDividedPowerForms p A (primeDividedPowers B p lam hp) 1)
    (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil) 1)
    (completedDividedPowerDifferentialOnRing p A (completedPrimeDividedPowers B p lam hp hpnil))
    (genuineCompletedFormsMap A B p lam hp hpnil 1) (primeCompletedConnection A B p lam hp M nabla)
    (completedDividedPowerDifferentialOnRing_add p A _)
    (completedDividedPowerDifferentialOnRing_mul p A _)
    (genuineCompletedFormsMap_differential A B p lam hp hpnil)

/-- The base change map along `B' → D'`. -/
abbrev genuineTransfer₁ (q : ℕ) :=
  CompletedDeRham.baseChangeTerm p (primeRing B p lam) (completedPrimeRingSelf B p lam)
    (primeCarrier B p lam M) (completedDividedPowerForms p A (primeDividedPowers B p lam hp))
    (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil))
    (genuineCompletedFormsMap A B p lam hp hpnil) q

/-- The identification `(M ⊗̂_B B') ⊗̂_{B'} D' ≅ M ⊗̂_B D'` on the terms. -/
abbrev genuineTransfer₂ (q : ℕ) :=
  CompletedDeRham.horizontalTerm p (completedPrimeRingSelf B p lam) (twiceCarrier B p lam M)
    (genuineCarrier B p lam M)
    (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil))
    (CompletedConnection.baseChangeComposite p (B : Type u) (primeRing B p lam)
      (completedPrimeRingSelf B p lam) M) q

/-- **The transfer `M ⊗̂_{B'} Ω^q_{B'} → M ⊗̂_B Ω^q_{D'}`** from the complex of the extension `B'`
to the complex of `D'`. -/
abbrev genuineTransfer (q : ℕ) :
    primeCompletedTerm A B p lam hp M q →+ genuineCompletedTerm A B p lam hp hpnil M q :=
  (genuineTransfer₂ A B p lam hp hpnil M q).comp (genuineTransfer₁ A B p lam hp hpnil M q)

/-- The transfer carries the canonical map along `B → B'` to the canonical map along `B → D'`. -/
theorem genuineTransfer_comparison (q : ℕ) (x : baseCompletedTerm A B p M q) :
    genuineTransfer A B p lam hp hpnil M q (primeCompletedComparison A B p lam hp M q x) =
      genuineCompletedComparison A B p lam hp hpnil M q x :=
  (CompletedDeRham.horizontalTerm_baseChangeComposite p (B : Type u) (primeRing B p lam)
    (completedPrimeRingSelf B p lam) M
    (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil)) q _).trans
    (CompletedDeRham.baseChangeTerm_comp p (B : Type u) (primeRing B p lam)
      (completedPrimeRingSelf B p lam) M (completedDividedPowerForms p A B.dividedPowers)
      (completedDividedPowerForms p A (primeDividedPowers B p lam hp))
      (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil))
      (primeCompletedFormsMap A B p lam hp) (genuineCompletedFormsMap A B p lam hp hpnil)
      (completedPrimeFormsMap A B p lam hp hpnil) (fun _ _ ↦ rfl) q x)

/-- **The transfer is a map of complexes.** -/
theorem genuineTransfer_differential (q : ℕ) (y : primeCompletedTerm A B p lam hp M q) :
    genuineCompletedDifferential A B p lam hp hpnil M nabla q (genuineTransfer A B p lam hp hpnil M
        q y) =
      genuineTransfer A B p lam hp hpnil M (q + 1) (primeCompletedDifferential A B p lam hp M nabla
          q y) := by
  have h1 := DFunLike.congr_fun (CompletedDeRham.baseChangeTerm_comm p (primeRing B p lam)
    (completedPrimeRingSelf B p lam) (primeCarrier B p lam M)
    (completedDividedPowerForms p A (primeDividedPowers B p lam hp))
    (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil))
    (genuineCompletedFormsMap A B p lam hp hpnil)
    (completedDividedPowerWedgeOnRing p A (primeDividedPowers B p lam hp))
    (completedDividedPowerWedgeOnRing p A (completedPrimeDividedPowers B p lam hp hpnil))
    (completedDividedPowerDeRham p A (primeDividedPowers B p lam hp))
    (completedDividedPowerDeRham p A (completedPrimeDividedPowers B p lam hp hpnil))
    (completedDividedPowerDifferentialOnRing p A (completedPrimeDividedPowers B p lam hp hpnil))
    (primeCompletedConnection A B p lam hp M nabla)
    (completedDividedPowerDifferentialOnRing_add p A _)
    (completedDividedPowerDifferentialOnRing_mul p A _)
    (genuineCompletedFormsMap_differential A B p lam hp hpnil)
    (isGradedLeibniz_completedDividedPowerOnRing p A _)
    (isGradedLeibniz_completedDividedPowerOnRing p A _)
    (genuineCompletedFormsMap_wedge A B p lam hp hpnil)
    (genuineCompletedFormsMap_deRham A B p lam hp hpnil) q) y
  have hnabla : ∀ m : twiceCarrier B p lam M,
      genuineCompletedConnection A B p lam hp hpnil M nabla
          (CompletedConnection.baseChangeComposite p (B : Type u) (primeRing B p lam)
            (completedPrimeRingSelf B p lam) M m) =
        AdicCompletion.map (pAdicIdeal (A := completedPrimeRingSelf B p lam) p)
          (TensorProduct.map (CompletedConnection.baseChangeComposite p (B : Type u)
            (primeRing B p lam) (completedPrimeRingSelf B p lam) M) LinearMap.id)
          (twiceConnection A B p lam hp hpnil M nabla m) := fun m ↦
    (CompletedConnection.baseChange_baseChangeComposite p (B : Type u) (primeRing B p lam)
      (completedPrimeRingSelf B p lam) M (completedDividedPowerForms p A B.dividedPowers 1)
      (completedDividedPowerForms p A (primeDividedPowers B p lam hp) 1)
      (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil) 1)
      (completedDividedPowerDifferentialOnRing p A (primeDividedPowers B p lam hp))
      (completedDividedPowerDifferentialOnRing p A (completedPrimeDividedPowers B p lam hp hpnil))
      (primeCompletedFormsMap A B p lam hp 1) (genuineCompletedFormsMap A B p lam hp hpnil 1)
      (completedPrimeFormsMap A B p lam hp hpnil 1) nabla
      (completedDividedPowerDifferentialOnRing_add p A _)
      (completedDividedPowerDifferentialOnRing_mul p A _)
      (primeCompletedFormsMap_differential A B p lam hp)
      (completedDividedPowerDifferentialOnRing_add p A _)
      (completedDividedPowerDifferentialOnRing_mul p A _)
      (genuineCompletedFormsMap_differential A B p lam hp hpnil) (fun _ ↦ rfl)
      (completedPrimeFormsMap_differential A B p lam hp hpnil) m).trans
      (CompletedDeRham.horizontalTerm_baseChangeComposite p (B : Type u) (primeRing B p lam)
        (completedPrimeRingSelf B p lam) M
        (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil)) 1 _).symm
  have h2 := CompletedDeRham.horizontalTerm_comm p (completedPrimeRingSelf B p lam)
    (twiceCarrier B p lam M) (genuineCarrier B p lam M)
    (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil))
    (CompletedConnection.baseChangeComposite p (B : Type u) (primeRing B p lam)
      (completedPrimeRingSelf B p lam) M)
    (completedDividedPowerWedgeOnRing p A (completedPrimeDividedPowers B p lam hp hpnil))
    (completedDividedPowerDeRham p A (completedPrimeDividedPowers B p lam hp hpnil))
    (twiceConnection A B p lam hp hpnil M nabla) (genuineCompletedConnection A B p lam hp hpnil M
        nabla)
    (isGradedLeibniz_completedDividedPowerOnRing p A _) hnabla q
    (genuineTransfer₁ A B p lam hp hpnil M q y)
  exact h2.trans (congrArg (genuineTransfer₂ A B p lam hp hpnil M (q + 1)) h1)

/-- **The transfer is bijective in every degree.** -/
theorem bijective_genuineTransfer [Fact p.Prime] [Algebra (IntegersAtPrime p) A] (q : ℕ) :
    Function.Bijective (genuineTransfer A B p lam hp hpnil M q) :=
  (CompletedDeRham.horizontalTerm_bijective p (completedPrimeRingSelf B p lam)
      (twiceCarrier B p lam M) (genuineCarrier B p lam M)
      (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil))
      (CompletedConnection.baseChangeCompositeEquiv p (B : Type u) (primeRing B p lam)
        (completedPrimeRingSelf B p lam) M) q).comp
    (bijective_genuineBaseChangeValues_completed A B p lam hp hpnil q (primeCarrier B p lam M))

/-- The transfer as an additive equivalence. -/
abbrev genuineTransferEquiv [Fact p.Prime] [Algebra (IntegersAtPrime p) A] (q : ℕ) :
    primeCompletedTerm A B p lam hp M q ≃+ genuineCompletedTerm A B p lam hp hpnil M q :=
  AddEquiv.ofBijective (genuineTransfer A B p lam hp hpnil M q)
    (bijective_genuineTransfer A B p lam hp hpnil M q)

end Target

section SquareZero

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (lam : (B : Type u)) (hp : p ≠ 0) (M : Type u) [AddCommGroup M] [Module (B : Type u) M]
  (nabla : CompletedConnection p (B : Type u) (completedDividedPowerForms p A B.dividedPowers 1)
    (completedDividedPowerDifferentialOnRing p A B.dividedPowers) M)
  (hint : IsCompletedIntegrable p A (B : Type u) B.dividedPowers M nabla)

include hint in
/-- **The source complex `M ⊗̂_B Ω^•_B` is a complex**: at every level its differentials are the
extended connection of an integrable connection. -/
theorem isSquareZero_baseCompleted :
    CompletedDeRham.IsSquareZero p (B : Type u) (completedDividedPowerForms p A B.dividedPowers)
      (completedDividedPowerWedgeOnRing p A B.dividedPowers)
      (completedDividedPowerDeRham p A B.dividedPowers) M nabla
      (isGradedLeibniz_completedDividedPowerOnRing p A B.dividedPowers) :=
  comp_eq_zero_of_levels (pAdicIdeal (A := (B : Type u)) p)
    (baseCompletedDifferential A B p M nabla)
    (fun q n ↦ (baseLevelEquiv A B p M q n).toAddEquiv)
    (fun n q ↦ dXn A B p M nabla (sourceDeRham A (B : Type u)) n q)
    (fun n q x ↦ baseLevel_differential A B p M nabla (sourceDeRham A (B : Type u)) n q x)
    (fun n q t ↦ LinearMap.congr_fun (extendedConnection_comp_self_eq_zero
      (sourceDeRham A (B : Type u)) (baseFormsProjection A B) (Submodule.mkQ_surjective _)
      (baseFormsGenerationHypothesis A B (sourceDeRham A (B : Type u)))
      (levelNabla A B p M nabla n)
      (levelNabla_integrable A B p M nabla hint (sourceDeRham A (B : Type u)) n) q) t)

include hint in
/-- **The target complex `M' ⊗̂_{B'} Ω^•_{B'}` is a complex.** -/
theorem isSquareZero_primeCompleted :
    CompletedDeRham.IsSquareZero p (primeRing B p lam)
      (completedDividedPowerForms p A (primeDividedPowers B p lam hp))
      (completedDividedPowerWedgeOnRing p A (primeDividedPowers B p lam hp))
      (completedDividedPowerDeRham p A (primeDividedPowers B p lam hp)) (primeCarrier B p lam M)
      (primeCompletedConnection A B p lam hp M nabla)
      (isGradedLeibniz_completedDividedPowerOnRing p A (primeDividedPowers B p lam hp)) :=
  comp_eq_zero_of_levels (pAdicIdeal (A := primeRing B p lam) p)
    (primeCompletedDifferential A B p lam hp M nabla)
    (fun q n ↦ (primeLevelEquiv A B p lam hp M q n).toAddEquiv)
    (fun n q ↦ dYn A B p lam hp M nabla (sourceDeRham A (primeRing B p lam)) n q)
    (fun n q y ↦ primeLevel_differential A B p lam hp M nabla (sourceDeRham A (primeRing B p lam))
      n q y)
    (fun n q t ↦ LinearMap.congr_fun (extendedConnection_comp_self_eq_zero
      (sourceDeRham A (primeRing B p lam)) (primeFormsProjection A B p lam hp)
      (Submodule.mkQ_surjective _)
      (primeFormsGenerationHypothesis A B p lam hp (sourceDeRham A (primeRing B p lam)))
      (primeConnection A B p lam hp _ (levelNabla A B p M nabla n))
      (baseChange_isIntegrable (sourceDeRham A (B : Type u)) (sourceDeRham A (primeRing B p lam))
        (baseFormsProjection A B) (primeFormsProjection A B p lam hp)
        (Submodule.mkQ_surjective _) (baseFormsGenerationHypothesis A B (sourceDeRham A (B : Type
            u)))
        (Submodule.mkQ_surjective _)
        (primeFormsGenerationHypothesis A B p lam hp (sourceDeRham A (primeRing B p lam)))
        (primeFormsComparison A B p lam hp)
        (primeFormsComparison_dividedPowerDifferential A B p lam hp)
        (levelNabla A B p M nabla n)
        (levelNabla_integrable A B p M nabla hint (sourceDeRham A (B : Type u)) n)) q) t)

end SquareZero

section Pieces

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (lam : (B : Type u)) (hp : p ≠ 0)
  (hpnil : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))
  (M : Type u) [AddCommGroup M] [Module (B : Type u) M]
  (nabla : CompletedConnection p (B : Type u) (completedDividedPowerForms p A B.dividedPowers 1)
    (completedDividedPowerDifferentialOnRing p A B.dividedPowers) M)

/-- **The canonical map `c_M^•` of (07PY) along `B → D'` is a map of complexes.** -/
theorem genuineCompletedComparison_comm (q : ℕ) :
    (genuineCompletedDifferential A B p lam hp hpnil M nabla q).comp
        (genuineCompletedComparison A B p lam hp hpnil M q) =
      (genuineCompletedComparison A B p lam hp hpnil M (q + 1)).comp
        (baseCompletedDifferential A B p M nabla q) :=
  CompletedDeRham.baseChangeTerm_comm p (B : Type u) (completedPrimeRingSelf B p lam) M
    (completedDividedPowerForms p A B.dividedPowers)
    (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil))
    (completedPrimeFormsMap A B p lam hp hpnil)
    (completedDividedPowerWedgeOnRing p A B.dividedPowers)
    (completedDividedPowerWedgeOnRing p A (completedPrimeDividedPowers B p lam hp hpnil))
    (completedDividedPowerDeRham p A B.dividedPowers)
    (completedDividedPowerDeRham p A (completedPrimeDividedPowers B p lam hp hpnil))
    (completedDividedPowerDifferentialOnRing p A (completedPrimeDividedPowers B p lam hp hpnil))
    nabla (completedDividedPowerDifferentialOnRing_add p A _)
    (completedDividedPowerDifferentialOnRing_mul p A _)
    (completedPrimeFormsMap_differential A B p lam hp hpnil)
    (isGradedLeibniz_completedDividedPowerOnRing p A _)
    (isGradedLeibniz_completedDividedPowerOnRing p A _)
    (completedPrimeFormsMap_wedge A B p lam hp hpnil)
    (completedPrimeFormsMap_deRham A B p lam hp hpnil) q

variable [Fact p.Prime] [Algebra (IntegersAtPrime p) A] [Nontrivial (XiAlg B)]
  [Algebra (IntegersAtPrime p) (B : Type u)]
  (hint : IsCompletedIntegrable p A (B : Type u) B.dividedPowers M nabla)

omit [Nontrivial (XiAlg B)] [Algebra (IntegersAtPrime p) (B : Type u)] in
/-- The transfer `M ⊗̂_{B'} Ω^•_{B'} ≅ M ⊗̂_B Ω^•_{D'}` commutes with the differentials. -/
theorem genuineTransferEquiv_differential (q : ℕ) (y : primeCompletedTerm A B p lam hp M q) :
    genuineCompletedDifferential A B p lam hp hpnil M nabla q
        (genuineTransferEquiv A B p lam hp hpnil M q y) =
      genuineTransferEquiv A B p lam hp hpnil M (q + 1)
        (primeCompletedDifferential A B p lam hp M nabla q y) :=
  genuineTransfer_differential A B p lam hp hpnil M nabla q y

omit [Nontrivial (XiAlg B)] [Algebra (IntegersAtPrime p) (B : Type u)] in
include hint in
/-- **The target complex `M ⊗̂_B Ω^•_{D'}` is a complex.** -/
theorem isSquareZero_genuineCompleted :
    CompletedDeRham.IsSquareZero p (completedPrimeRingSelf B p lam)
      (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil))
      (completedDividedPowerWedgeOnRing p A (completedPrimeDividedPowers B p lam hp hpnil))
      (completedDividedPowerDeRham p A (completedPrimeDividedPowers B p lam hp hpnil))
      (genuineCarrier B p lam M) (genuineCompletedConnection A B p lam hp hpnil M nabla)
      (isGradedLeibniz_completedDividedPowerOnRing p A _) :=
  transport_comp_eq_zero (primeCompletedDifferential A B p lam hp M nabla)
    (genuineCompletedDifferential A B p lam hp hpnil M nabla)
    (fun q ↦ genuineTransferEquiv A B p lam hp hpnil M q)
    (genuineTransferEquiv_differential A B p lam hp hpnil M nabla)
    (isSquareZero_primeCompleted A B p lam hp M nabla hint)

omit [Nontrivial (XiAlg B)] [Algebra (IntegersAtPrime p) (B : Type u)] in
/-- The transfer carries the comparison map along `B → B'` to the one along `B → D'`. -/
theorem genuineTransferEquiv_symm_comparison (q : ℕ) (x : baseCompletedTerm A B p M q) :
    (genuineTransferEquiv A B p lam hp hpnil M q).symm
        (genuineCompletedComparison A B p lam hp hpnil M q x) =
      primeCompletedComparison A B p lam hp M q x :=
  (genuineTransferEquiv A B p lam hp hpnil M q).symm_apply_eq.mpr
    (genuineTransfer_comparison A B p lam hp hpnil M q x).symm

/-- The reverse map `e_M^•` along `B → D'`, in degree `q`. -/
noncomputable abbrev genuineReverse (S : SourceDeRham A (B : Type u))
    (S' : SourceDeRham A (primeRing B p lam)) (q : ℕ) :
    genuineCompletedTerm A B p lam hp hpnil M q →+ baseCompletedTerm A B p M q :=
  (completedReverse A B p lam hp M nabla hint S S' q).comp
    (genuineTransferEquiv A B p lam hp hpnil M q).symm.toAddMonoidHom

/-- The homotopy `h` along `B → D'`, in degree `q`. -/
noncomputable abbrev genuineHomotopy (q : ℕ) :
    genuineCompletedTerm A B p lam hp hpnil M (q + 1) →+ genuineCompletedTerm A B p lam hp hpnil M
        q :=
  (genuineTransferEquiv A B p lam hp hpnil M q).toAddMonoidHom.comp
    ((completedHomotopy A B p lam hp M q).comp
      (genuineTransferEquiv A B p lam hp hpnil M (q + 1)).symm.toAddMonoidHom)

variable (S : SourceDeRham A (B : Type u)) (S' : SourceDeRham A (primeRing B p lam))

/-- The reverse map `e_M^•` is a map of complexes. -/
theorem genuineReverse_differential (q : ℕ)
    (y : genuineCompletedTerm A B p lam hp hpnil M q) :
    genuineReverse A B p lam hp hpnil M nabla hint S S' (q + 1)
        (genuineCompletedDifferential A B p lam hp hpnil M nabla q y) =
      baseCompletedDifferential A B p M nabla q
        (genuineReverse A B p lam hp hpnil M nabla hint S S' q y) :=
  transport_chain (baseCompletedDifferential A B p M nabla)
    (primeCompletedDifferential A B p lam hp M nabla)
    (genuineCompletedDifferential A B p lam hp hpnil M nabla)
    (fun q ↦ genuineTransferEquiv A B p lam hp hpnil M q)
    (genuineTransferEquiv_differential A B p lam hp hpnil M nabla)
    (completedReverse A B p lam hp M nabla hint S S')
    (completedReverse_differential A B p lam hp M nabla hint S S') q y

/-- `e_M^• ∘ c_M^• = p`. -/
theorem genuineReverse_comparison (q : ℕ) (x : baseCompletedTerm A B p M q) :
    genuineReverse A B p lam hp hpnil M nabla hint S S' q
        (genuineCompletedComparison A B p lam hp hpnil M q x) = p • x :=
  (congrArg (completedReverse A B p lam hp M nabla hint S S' q)
    (genuineTransferEquiv_symm_comparison A B p lam hp hpnil M q x)).trans
    (completedReverse_comparison A B p lam hp M nabla hint S S' q x)

/-- The homotopy identity `h d = p - c_M^• ∘ e_M^•` in degree zero. -/
theorem genuineHomotopy_zero (y : genuineCompletedTerm A B p lam hp hpnil M 0) :
    genuineHomotopy A B p lam hp hpnil M 0
        (genuineCompletedDifferential A B p lam hp hpnil M nabla 0 y) =
      p • y - genuineCompletedComparison A B p lam hp hpnil M 0
        (genuineReverse A B p lam hp hpnil M nabla hint S S' 0 y) :=
  (transport_zero p (primeCompletedDifferential A B p lam hp M nabla)
    (genuineCompletedDifferential A B p lam hp hpnil M nabla)
    (primeCompletedComparison A B p lam hp M) (fun q ↦ genuineTransferEquiv A B p lam hp hpnil M q)
    (genuineTransferEquiv_differential A B p lam hp hpnil M nabla)
    (completedReverse A B p lam hp M nabla hint S S') (completedHomotopy A B p lam hp M)
    (completedHomotopy_zero A B p lam hp M nabla hint S S') y).trans
    (congrArg (p • y - ·) (genuineTransfer_comparison A B p lam hp hpnil M 0 _))

/-- The homotopy identity `d h + h d = p - c_M^• ∘ e_M^•` in positive degree. -/
theorem genuineHomotopy_succ (q : ℕ) (y : genuineCompletedTerm A B p lam hp hpnil M (q + 1)) :
    genuineCompletedDifferential A B p lam hp hpnil M nabla q
          (genuineHomotopy A B p lam hp hpnil M q y) +
        genuineHomotopy A B p lam hp hpnil M (q + 1)
          (genuineCompletedDifferential A B p lam hp hpnil M nabla (q + 1) y) =
      p • y - genuineCompletedComparison A B p lam hp hpnil M (q + 1)
        (genuineReverse A B p lam hp hpnil M nabla hint S S' (q + 1) y) :=
  (transport_succ p (primeCompletedDifferential A B p lam hp M nabla)
    (genuineCompletedDifferential A B p lam hp hpnil M nabla)
    (primeCompletedComparison A B p lam hp M) (fun q ↦ genuineTransferEquiv A B p lam hp hpnil M q)
    (genuineTransferEquiv_differential A B p lam hp hpnil M nabla)
    (completedReverse A B p lam hp M nabla hint S S') (completedHomotopy A B p lam hp M)
    (completedHomotopy_succ A B p lam hp M nabla hint S S') q y).trans
    (congrArg (p • y - ·) (genuineTransfer_comparison A B p lam hp hpnil M (q + 1) _))

omit [Algebra (IntegersAtPrime p) (B : Type u)] in
/-- The homotopy vanishes on the image of `c_M^•`. -/
theorem genuineHomotopy_comparison (q : ℕ) (x : baseCompletedTerm A B p M (q + 1)) :
    genuineHomotopy A B p lam hp hpnil M q
      (genuineCompletedComparison A B p lam hp hpnil M (q + 1) x) = 0 :=
  ((congrArg (fun z ↦ genuineTransferEquiv A B p lam hp hpnil M q
      (completedHomotopy A B p lam hp M q z))
    (genuineTransferEquiv_symm_comparison A B p lam hp hpnil M (q + 1) x)).trans
    (congrArg (genuineTransferEquiv A B p lam hp hpnil M q)
      (completedHomotopy_comparison A B p lam hp M q x))).trans (map_zero _)

include hint in
/-- **The reverse map and the homotopy along `B → D'`**, for a nontrivial `B`. -/
theorem exists_reverse_genuineCompleted :
    ∃ (e : ∀ q : ℕ, genuineCompletedTerm A B p lam hp hpnil M q →+ baseCompletedTerm A B p M q)
      (h : ∀ q : ℕ, genuineCompletedTerm A B p lam hp hpnil M (q + 1) →+
        genuineCompletedTerm A B p lam hp hpnil M q),
      (∀ (q : ℕ) (y : genuineCompletedTerm A B p lam hp hpnil M q),
        e (q + 1) (genuineCompletedDifferential A B p lam hp hpnil M nabla q y) =
          baseCompletedDifferential A B p M nabla q (e q y)) ∧
      (∀ (q : ℕ) (x : baseCompletedTerm A B p M q),
        e q (genuineCompletedComparison A B p lam hp hpnil M q x) = p • x) ∧
      (∀ y : genuineCompletedTerm A B p lam hp hpnil M 0,
        h 0 (genuineCompletedDifferential A B p lam hp hpnil M nabla 0 y) =
          p • y - genuineCompletedComparison A B p lam hp hpnil M 0 (e 0 y)) ∧
      (∀ (q : ℕ) (y : genuineCompletedTerm A B p lam hp hpnil M (q + 1)),
        genuineCompletedDifferential A B p lam hp hpnil M nabla q (h q y) +
            h (q + 1) (genuineCompletedDifferential A B p lam hp hpnil M nabla (q + 1) y) =
          p • y - genuineCompletedComparison A B p lam hp hpnil M (q + 1) (e (q + 1) y)) ∧
      (∀ (q : ℕ) (x : baseCompletedTerm A B p M (q + 1)),
        h q (genuineCompletedComparison A B p lam hp hpnil M (q + 1) x) = 0) :=
  ⟨genuineReverse A B p lam hp hpnil M nabla hint (sourceDeRham A (B : Type u))
      (sourceDeRham A (primeRing B p lam)),
    genuineHomotopy A B p lam hp hpnil M,
    genuineReverse_differential A B p lam hp hpnil M nabla hint _ _,
    genuineReverse_comparison A B p lam hp hpnil M nabla hint _ _,
    genuineHomotopy_zero A B p lam hp hpnil M nabla hint _ _,
    genuineHomotopy_succ A B p lam hp hpnil M nabla hint _ _,
    genuineHomotopy_comparison A B p lam hp hpnil M⟩

end Pieces

section Main

variable (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime] [Algebra (IntegersAtPrime p) A]
  (B : DividedPowerRing.{u}) [Algebra A (B : Type u)]
  (hpnil : IsNilpotent (Ideal.Quotient.mk B.ideal ((p : ℕ) : (B : Type u))))
  (lam : (B : Type u)) (M : Type u) [AddCommGroup M] [Module (B : Type u) M]
  (nabla : CompletedConnection p (B : Type u) (completedDividedPowerForms p A B.dividedPowers 1)
    (completedDividedPowerDifferentialOnRing p A B.dividedPowers) M)

/-- **[Stacks, Lemma 60.25.3, Tag 07N1], for any divided power ring.**  The statement in
Situation 07MD itself is
`Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension_situation`.

Let `(D, J̄, γ̄)` be a divided power ring over `A` in which `p` is nilpotent modulo `J̄`, with `A`
a `ℤ_{(p)}`-algebra — in Situation 07MD this is the `p`-adically completed divided power envelope
`D` of (07J8) with its divided powers of [Stacks, Tag 07KG]; nothing about `D` beyond these
properties is used.  Write `Ω^q_D` for the `p`-adic completion of the divided power forms of `D`
over `A` (07J9).  Let `λ ∈ D`, let `D'` be the `p`-adic completion of
`D[z]⟨ξ⟩/(ξ - (z^p - λ))` with the divided powers `γ̂'` of [Stacks, Tag 07KD], and let `Ω^q_{D'}`
be the `p`-adic completion of the divided power forms **of `D'`** over `A`.  Let `M` be a
`D`-module with a connection `∇ : M → M ⊗̂_D Ω_D` (07JC) which is integrable in the sense of
[Stacks, Remark 60.6.1, Tag 07I0] (07JD): the composite `M → M ⊗̂ Ω¹ → M ⊗̂ Ω²` vanishes.  Then:

* `M ⊗^∧_D Ω^•_D` and `M ⊗^∧_D Ω^•_{D'} = (M ⊗̂_D D') ⊗̂_{D'} Ω^•_{D'}` are complexes, the second
  for the base-changed connection;
* the canonical map `c_M^• : M ⊗^∧_D Ω^•_D → M ⊗^∧_D Ω^•_{D'}` of (07PY),
  `Crystalline.CompletedDeRham.baseChangeTerm`, is a map of complexes;
* there is a map of complexes `e_M^•` in the opposite direction with `e_M^• ∘ c_M^• = p` — so it is
  homotopic to `p` by the zero homotopy — and a homotopy `h` with `h d = p - c_M^• ∘ e_M^•` in
  degree `0` and `d h + h d = p - c_M^• ∘ e_M^•` in positive degrees, so that `c_M^• ∘ e_M^•` is
  homotopic to multiplication by `p`; moreover `h ∘ c_M^• = 0`.

The hypotheses (07JB), `p`-adic completeness of `M`, and (07JE), topological quasi-nilpotence of
`∇`, are not needed and are not assumed. -/
theorem exists_homotopyInverse_completedPthRootExtension
    (hint : IsCompletedIntegrable p A (B : Type u) B.dividedPowers M nabla) :
    CompletedDeRham.IsSquareZero p (B : Type u) (completedDividedPowerForms p A B.dividedPowers)
        (completedDividedPowerWedgeOnRing p A B.dividedPowers)
        (completedDividedPowerDeRham p A B.dividedPowers) M nabla
        (isGradedLeibniz_completedDividedPowerOnRing p A B.dividedPowers) ∧
      CompletedDeRham.IsSquareZero p (completedPrimeRingSelf B p lam)
        (completedDividedPowerForms p A
          (completedPrimeDividedPowers B p lam (Fact.out : p.Prime).ne_zero hpnil))
        (completedDividedPowerWedgeOnRing p A
          (completedPrimeDividedPowers B p lam (Fact.out : p.Prime).ne_zero hpnil))
        (completedDividedPowerDeRham p A
          (completedPrimeDividedPowers B p lam (Fact.out : p.Prime).ne_zero hpnil))
        (genuineCarrier B p lam M)
        (genuineCompletedConnection A B p lam (Fact.out : p.Prime).ne_zero hpnil M nabla)
        (isGradedLeibniz_completedDividedPowerOnRing p A _) ∧
      (∀ q : ℕ, (genuineCompletedDifferential A B p lam (Fact.out : p.Prime).ne_zero hpnil M nabla
          q).comp (genuineCompletedComparison A B p lam (Fact.out : p.Prime).ne_zero hpnil M q) =
        (genuineCompletedComparison A B p lam (Fact.out : p.Prime).ne_zero hpnil M (q + 1)).comp
          (baseCompletedDifferential A B p M nabla q)) ∧
      ∃ (e : ∀ q : ℕ, genuineCompletedTerm A B p lam (Fact.out : p.Prime).ne_zero hpnil M q →+
          baseCompletedTerm A B p M q)
        (h : ∀ q : ℕ, genuineCompletedTerm A B p lam (Fact.out : p.Prime).ne_zero hpnil M (q + 1) →+
          genuineCompletedTerm A B p lam (Fact.out : p.Prime).ne_zero hpnil M q),
        (∀ (q : ℕ) (y : genuineCompletedTerm A B p lam (Fact.out : p.Prime).ne_zero hpnil M q),
          e (q + 1) (genuineCompletedDifferential A B p lam (Fact.out : p.Prime).ne_zero hpnil M
            nabla q y) = baseCompletedDifferential A B p M nabla q (e q y)) ∧
        (∀ (q : ℕ) (x : baseCompletedTerm A B p M q),
          e q (genuineCompletedComparison A B p lam (Fact.out : p.Prime).ne_zero hpnil M q x) =
            p • x) ∧
        (∀ y : genuineCompletedTerm A B p lam (Fact.out : p.Prime).ne_zero hpnil M 0,
          h 0 (genuineCompletedDifferential A B p lam (Fact.out : p.Prime).ne_zero hpnil M nabla 0
            y) = p • y - genuineCompletedComparison A B p lam (Fact.out : p.Prime).ne_zero hpnil M 0
              (e 0 y)) ∧
        (∀ (q : ℕ) (y : genuineCompletedTerm A B p lam (Fact.out : p.Prime).ne_zero hpnil M
            (q + 1)),
          genuineCompletedDifferential A B p lam (Fact.out : p.Prime).ne_zero hpnil M nabla q
              (h q y) +
            h (q + 1) (genuineCompletedDifferential A B p lam (Fact.out : p.Prime).ne_zero hpnil M
              nabla (q + 1) y) =
            p • y - genuineCompletedComparison A B p lam (Fact.out : p.Prime).ne_zero hpnil M
              (q + 1) (e (q + 1) y)) ∧
        (∀ (q : ℕ) (x : baseCompletedTerm A B p M (q + 1)),
          h q (genuineCompletedComparison A B p lam (Fact.out : p.Prime).ne_zero hpnil M (q + 1)
            x) = 0) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  by_cases hB : Nontrivial (B : Type u)
  · have := nontrivial_xiAlg B
    let : Algebra (IntegersAtPrime p) (B : Type u) :=
      ((algebraMap A (B : Type u)).comp (algebraMap (IntegersAtPrime p) A)).toAlgebra
    exact ⟨isSquareZero_baseCompleted A B p M nabla hint,
      isSquareZero_genuineCompleted A B p lam hp hpnil M nabla hint,
      genuineCompletedComparison_comm A B p lam hp hpnil M nabla,
      exists_reverse_genuineCompleted A B p lam hp hpnil M nabla hint⟩
  · have : Subsingleton (B : Type u) := not_nontrivial_iff_subsingleton.mp hB
    have : Subsingleton (completedPrimeRingSelf B p lam) := subsingleton_of_zero_eq_one (by
      rw [← map_one (algebraMap (B : Type u) (completedPrimeRingSelf B p lam)),
        Subsingleton.elim (1 : (B : Type u)) 0, map_zero])
    have : ∀ q, Subsingleton (baseCompletedTerm A B p M q) :=
      fun q ↦ Module.subsingleton (B : Type u) _
    have : ∀ q, Subsingleton (genuineCompletedTerm A B p lam hp hpnil M q) :=
      fun q ↦ Module.subsingleton (completedPrimeRingSelf B p lam) _
    have : ∀ q, Subsingleton (CompletedTensor p (completedPrimeRingSelf B p lam)
        (completedDividedPowerForms p A (completedPrimeDividedPowers B p lam hp hpnil) q)
        (genuineCarrier B p lam M)) :=
      fun q ↦ Module.subsingleton (completedPrimeRingSelf B p lam) _
    exact ⟨fun _ ↦ AddMonoidHom.ext fun _ ↦ Subsingleton.elim _ _,
      fun _ ↦ AddMonoidHom.ext fun _ ↦ Subsingleton.elim _ _,
      fun _ ↦ AddMonoidHom.ext fun _ ↦ Subsingleton.elim _ _, fun _ ↦ 0, fun _ ↦ 0,
      fun _ _ ↦ Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _,
      fun _ ↦ Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _,
      fun _ _ ↦ Subsingleton.elim _ _⟩

end Main

end PthRootExtension

end Crystalline
