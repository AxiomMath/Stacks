module

public import StacksFrontier.Algebra.Module.ProZeroTowerLimit
public import StacksFrontier.RingTheory.Module.AdicSystem.Hom

/-!
# The adic comparison of Stacks 09BB, read on compatible sequences

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `P`, `Q` two finite `A`-modules.  Reducing the
target modulo `I ^ k` kills `I ^ k Hom(P, Q)`, so there is a comparison

`Hom_A(P, Q) / I ^ k Hom_A(P, Q) ⟶ Hom_A(P, Q / I ^ k Q)`,   `[f] ↦ (x ↦ [f x])`,

`Stacks.AdicSystem.HomSections.homAdicComparison`.  It is an isomorphism at no single level — its
kernel and its cokernel are killed by a power of `I` and no more, which is the Artin–Rees content
of Stacks 09BB — and the point of this file is that it nevertheless becomes a **bijection on the
inverse limits**:

`lim_n Hom_A(P, Q) / I ^ n Hom_A(P, Q) ≃ lim_n Hom_A(P, Q / I ^ n Q)`,

`Stacks.AdicSystem.HomSections.bijective_homAdicComparisonSectionsMap`, the limits being taken as
compatible sequences in the sense of `StacksFrontier.Algebra.Module.SuccTowerSections` and indexed so
that the term at `n` is the quotient at level `n + 1`.

That is the form in which the chartwise half of Stacks 08B6 consumes the commutative algebra: on
an affine étale chart of an algebraic space the sections of the internal Hom and of the adic
quotients are exactly the modules above, and the sheaf-theoretic comparison is exactly
`[f] ↦ (x ↦ [f x])`.

## Main definitions

* `Stacks.AdicSystem.HomSections.homAdicComparison` — the comparison at one level.
* `Stacks.AdicSystem.HomSections.homAdicTargetTransition` — the transition maps of the tower
  `Hom_A(P, Q / I ^ n Q)`.
* `Stacks.AdicSystem.HomSections.quotientSourceHomEquiv` — a module annihilated by `I ^ k`
  receives the same maps from `P` as from `P / I ^ k P`.
* `Stacks.AdicSystem.HomSections.adicCompletionSuccSectionsEquiv` — the adic completion is the
  compatible sequences of the tower of adic quotients.
* `Stacks.AdicSystem.HomSections.homAdicComparison_transitionMap` — the comparison is a map of
  towers.

## Main results

* `Stacks.AdicSystem.HomSections.bijective_homAdicComparisonSectionsMap` — **the comparison is a
  bijection on the inverse limits.**

## Implementation notes

The proof consumes
`Stacks.AdicSystem.HomComparison.hom_isom_quotient_systems_mittagLeffler_and_completion`
(Stacks 09BB) through its existential statement, every internal of which is `private`.  What that
statement offers about the inverse limits is one clause: an isomorphism
`limit HomSys ≅ AdicCompletion I Hom_A(P, Q)` of its own system `HomSys` of the
`Hom_A(P / I ^ n P, Q / I ^ n Q)` with the adic completion, whose components are the comparison
read through `AdicCompletion.eval`.  Three identifications turn that into the statement above, and
each is carried out separately.

* `limit HomSys` is the compatible sequences of the tower, by
  `Stacks.ProZero.towerSectionsLimitEquiv`.
* `AdicCompletion I Hom_A(P, Q)` is the compatible sequences of the tower of its own adic
  quotients, by `Stacks.AdicSystem.HomSections.adicCompletionSuccSectionsEquiv`, and the indices
  of the two towers differ by one, which `Stacks.SuccTower.sectionsShift` absorbs.  The shift is
  genuine and is not left to a definitional unfolding: `HomSys` is indexed so that its term at
  `n` is the quotient at level `n`, and both the geometry and the statement here are indexed from
  level `1`.
* The source of a map out of `P` into a module annihilated by `I ^ k` may be replaced by
  `P / I ^ k P`, which is `Stacks.AdicSystem.HomSections.quotientSourceHomEquiv`; this is what
  makes `HomSys` the tower whose bijectivity is wanted.

Only bijectivity is transported, so every comparison of towers is needed levelwise and as an
equivalence of types alone.  The two equivalences of towers are both taken in the direction which
*adds* the quotient — `Stacks.AdicSystem.HomSections.quotientSourceHomEquiv` precomposes with a
projection — and never in the direction which factors a map through one.  That is not cosmetic:
with either used the other way round the elaborator has to unfold `Submodule.liftQ` at a class
before it can compare two transition maps, and it does not finish.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.AdicSystem.HomSections

variable {A : Type u} [CommRing A] (I : Ideal A) (P : Type v) (Q : Type w)
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]

/-! ### The comparison at one level -/

/-- Postcomposition with the projection `Q ⟶ Q / I ^ k Q`. -/
def postcompMk (k : ℕ) :
    (P →ₗ[A] Q) →ₗ[A] (P →ₗ[A] (Q ⧸ I ^ k • (⊤ : Submodule A Q))) :=
  LinearMap.compRight A (Submodule.mkQ (I ^ k • (⊤ : Submodule A Q)))

/-- Postcomposition with the projection kills `I ^ k Hom_A(P, Q)`, because `I ^ k` annihilates
`Q / I ^ k Q`. -/
theorem pow_smul_top_le_ker_postcompMk (k : ℕ) :
    I ^ k • (⊤ : Submodule A (P →ₗ[A] Q)) ≤ LinearMap.ker (postcompMk I P Q k) := by
  refine Submodule.smul_le.2 fun r hr f _ => LinearMap.mem_ker.2 (LinearMap.ext fun x => ?_)
  show Submodule.Quotient.mk ((r • f) x) = 0
  rw [LinearMap.smul_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hr Submodule.mem_top

/-- **The adic comparison for the module of homomorphisms**, at one level:

`Hom_A(P, Q) / I ^ k Hom_A(P, Q) ⟶ Hom_A(P, Q / I ^ k Q)`,   `[f] ↦ (x ↦ [f x])`.

This is the comparison of Stacks 09BB with the source of the homomorphisms left unquotiented;
`Stacks.AdicSystem.HomSections.quotientSourceHomEquiv` identifies the two targets. -/
def homAdicComparison (k : ℕ) :
    ((P →ₗ[A] Q) ⧸ I ^ k • (⊤ : Submodule A (P →ₗ[A] Q))) →ₗ[A]
      (P →ₗ[A] (Q ⧸ I ^ k • (⊤ : Submodule A Q))) :=
  Submodule.liftQ _ (postcompMk I P Q k) (pow_smul_top_le_ker_postcompMk I P Q k)

/-- The comparison on the class of a homomorphism: `[f] ↦ (x ↦ [f x])`. -/
theorem homAdicComparison_mk (k : ℕ) (f : P →ₗ[A] Q) (x : P) :
    homAdicComparison I P Q k (Submodule.Quotient.mk f) x =
      Submodule.Quotient.mk (f x) := rfl

/-- The transition maps of the tower `Hom_A(P, Q / I ^ (n + 1) Q)`: postcomposition with the
transition maps of the adic quotients of `Q`. -/
def homAdicTargetTransition (n : ℕ) :
    (P →ₗ[A] (Q ⧸ I ^ (n + 1 + 1) • (⊤ : Submodule A Q))) →ₗ[A]
      (P →ₗ[A] (Q ⧸ I ^ (n + 1) • (⊤ : Submodule A Q))) :=
  LinearMap.compRight A (AdicCompletion.transitionMap I Q (Nat.le_succ (n + 1)))

/-! ### Quotienting the source of a homomorphism -/

/-- **A module annihilated by `I ^ k` receives the same homomorphisms from `P` as from
`P / I ^ k P`.**  A homomorphism out of `P` kills `I ^ k P`, so it factors, uniquely, through the
quotient. -/
def quotientSourceHomEquiv (k : ℕ) (Z : Type*) [AddCommGroup Z] [Module A Z]
    (hZ : ∀ r ∈ I ^ k, ∀ z : Z, r • z = 0) :
    ((P ⧸ I ^ k • (⊤ : Submodule A P)) →ₗ[A] Z) ≃ (P →ₗ[A] Z) where
  toFun g := g.comp (Submodule.mkQ _)
  invFun f := Submodule.liftQ _ f
    (Submodule.smul_le.2 fun r hr x _ => LinearMap.mem_ker.2
      ((f.map_smul r x).trans (hZ r hr (f x))))
  left_inv _ := Submodule.linearMap_qext _ rfl
  right_inv _ := rfl

/-- The identification of `Stacks.AdicSystem.HomSections.quotientSourceHomEquiv` on a
homomorphism out of the quotient. -/
theorem quotientSourceHomEquiv_apply (k : ℕ) (Z : Type*) [AddCommGroup Z] [Module A Z]
    (hZ : ∀ r ∈ I ^ k, ∀ z : Z, r • z = 0)
    (g : (P ⧸ I ^ k • (⊤ : Submodule A P)) →ₗ[A] Z) (x : P) :
    quotientSourceHomEquiv I P k Z hZ g x = g (Submodule.Quotient.mk x) := rfl

/-- `I ^ k` annihilates `Q / I ^ k Q`. -/
theorem smul_eq_zero_quotient_pow_smul_top (k : ℕ) (r : A) (hr : r ∈ I ^ k)
    (z : Q ⧸ I ^ k • (⊤ : Submodule A Q)) : r • z = 0 := by
  induction z using Submodule.Quotient.induction_on with
  | H y =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top

/-! ### The adic completion as the compatible sequences of its quotient tower -/

/-- Descending from level `k` to level `n` and then to level `m` is descending from `k` to `m`.
By `rfl` on the class of an element. -/
theorem transitionMap_transitionMap (X : Type*) [AddCommGroup X] [Module A X] {m n k : ℕ}
    (h₁ : m ≤ n) (h₂ : n ≤ k) (z : X ⧸ I ^ k • (⊤ : Submodule A X)) :
    AdicCompletion.transitionMap I X h₁ (AdicCompletion.transitionMap I X h₂ z) =
      AdicCompletion.transitionMap I X (h₁.trans h₂) z := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

/-- A sequence of adic quotients compatible with the successor transitions is compatible with
every transition. -/
theorem transitionMap_apply_of_le (X : Type*) [AddCommGroup X] [Module A X]
    (x : ∀ n : ℕ, X ⧸ I ^ n • (⊤ : Submodule A X))
    (hx : ∀ n : ℕ, AdicCompletion.transitionMap I X (Nat.le_succ n) (x (n + 1)) = x n)
    {m n : ℕ} (h : m ≤ n) : AdicCompletion.transitionMap I X h (x n) = x m := by
  induction n, h using Nat.le_induction with
  | base =>
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x m)
      rw [← hy]
      rfl
  | succ k hk ih =>
      exact (transitionMap_transitionMap I X hk (Nat.le_succ k) (x (k + 1))).symm.trans
        ((congrArg (AdicCompletion.transitionMap I X hk) (hx k)).trans ih)

/-- **Mathlib's `AdicCompletion` is the compatible sequences of the tower of adic quotients.**
The two differ only in whether compatibility is imposed for the successor transitions alone or
for all of them, and `Stacks.AdicSystem.HomSections.transitionMap_apply_of_le` says that is the
same condition.

`Stacks.ProZero.adicTowerSectionsEquiv` is this identification for a tower in `ModuleCat`.  It is
restated here at the plain spelling because crossing between the two is what costs: the
`CategoryTheory.ConcreteCategory` coercion of a `CategoryTheory.ModuleCat` morphism has to be
unfolded before the two compatibility conditions can be compared, and the elaborator does not
finish doing so. -/
def adicCompletionSuccSectionsEquiv (X : Type*) [AddCommGroup X] [Module A X] :
    { x : ∀ n : ℕ, X ⧸ I ^ n • (⊤ : Submodule A X) //
        ∀ n : ℕ, AdicCompletion.transitionMap I X (Nat.le_succ n) (x (n + 1)) = x n } ≃
      AdicCompletion I X where
  toFun x := ⟨x.1, fun h => transitionMap_apply_of_le I X x.1 x.2 h⟩
  invFun a := ⟨a.1, fun n => a.2 (Nat.le_succ n)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The components of `Stacks.AdicSystem.HomSections.adicCompletionSuccSectionsEquiv`. -/
theorem eval_adicCompletionSuccSectionsEquiv (X : Type*) [AddCommGroup X] [Module A X]
    (x : { x : ∀ n : ℕ, X ⧸ I ^ n • (⊤ : Submodule A X) //
        ∀ n : ℕ, AdicCompletion.transitionMap I X (Nat.le_succ n) (x (n + 1)) = x n }) (n : ℕ) :
    AdicCompletion.eval I X n (adicCompletionSuccSectionsEquiv I X x) = x.1 n := rfl

/-- **A linear equivalence carrying `I ^ k` times the whole module to `I ^ k` times the whole
module intertwines the transition maps of the two adic quotient towers.**  Both transition maps
fix a class, so this is `rfl` on one.

It is stated here, in a module whose elaboration costs nothing, rather than at the spelling of
its consumer: the equivalence a geometric consumer supplies is built out of sheaf-theoretic
data, and `rfl` on a class of such a section is a defeq the elaborator does not finish. -/
theorem transitionMap_quotientEquiv {Y : Type*} {Z : Type*} [AddCommGroup Y] [Module A Y]
    [AddCommGroup Z] [Module A Z] (f : Y ≃ₗ[A] Z)
    (hf : ∀ k : ℕ, Submodule.map (f : Y →ₗ[A] Z) (I ^ k • (⊤ : Submodule A Y)) =
      I ^ k • (⊤ : Submodule A Z)) (k : ℕ)
    (w : Y ⧸ I ^ (k + 1) • (⊤ : Submodule A Y)) :
    Submodule.Quotient.equiv _ _ f (hf k)
        (AdicCompletion.transitionMap I Y (Nat.le_succ k) w) =
      AdicCompletion.transitionMap I Z (Nat.le_succ k)
        (Submodule.Quotient.equiv _ _ f (hf (k + 1)) w) := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (I ^ (k + 1) • (⊤ : Submodule A Y)) w
  rw [← hy]
  rfl

/-! ### The comparison on the inverse limits -/

/-- **The comparison is a map of towers:** reducing the target one level further and comparing is
comparing and then reducing.  Checked on the class of a homomorphism, where both sides are
`x ↦ [f x]`. -/
theorem homAdicComparison_transitionMap (n : ℕ)
    (z : (P →ₗ[A] Q) ⧸ I ^ (n + 1 + 1) • (⊤ : Submodule A (P →ₗ[A] Q))) :
    homAdicComparison I P Q (n + 1)
        (AdicCompletion.transitionMap I (P →ₗ[A] Q) (Nat.le_succ (n + 1)) z) =
      homAdicTargetTransition I P Q n (homAdicComparison I P Q (n + 1 + 1) z) := by
  induction z using Submodule.Quotient.induction_on with
  | H f => exact LinearMap.ext fun x => rfl

/-- **The adic comparison for the module of homomorphisms, on compatible sequences.**  The two
towers are indexed so that the term at `n` is the quotient at level `n + 1`. -/
def homAdicComparisonSectionsMap :
    { x : ∀ n : ℕ, (P →ₗ[A] Q) ⧸ I ^ (n + 1) • (⊤ : Submodule A (P →ₗ[A] Q)) //
        ∀ n : ℕ, AdicCompletion.transitionMap I (P →ₗ[A] Q) (Nat.le_succ (n + 1)) (x (n + 1)) =
          x n } →
      { y : ∀ n : ℕ, P →ₗ[A] (Q ⧸ I ^ (n + 1) • (⊤ : Submodule A Q)) //
        ∀ n : ℕ, homAdicTargetTransition I P Q n (y (n + 1)) = y n } :=
  Stacks.SuccTower.sectionsMap _ _ (fun n => homAdicComparison I P Q (n + 1))
    (homAdicComparison_transitionMap I P Q)

/-- The terms of `Stacks.AdicSystem.HomSections.homAdicComparisonSectionsMap`. -/
theorem homAdicComparisonSectionsMap_apply
    (x : { x : ∀ n : ℕ, (P →ₗ[A] Q) ⧸ I ^ (n + 1) • (⊤ : Submodule A (P →ₗ[A] Q)) //
        ∀ n : ℕ, AdicCompletion.transitionMap I (P →ₗ[A] Q) (Nat.le_succ (n + 1)) (x (n + 1)) =
          x n }) (n : ℕ) :
    (homAdicComparisonSectionsMap I P Q x).1 n = homAdicComparison I P Q (n + 1) (x.1 n) := rfl

/-- **The adic comparison for the module of homomorphisms is a bijection on the inverse
limits:**

`lim_n Hom_A(P, Q) / I ^ n Hom_A(P, Q) ≃ lim_n Hom_A(P, Q / I ^ n Q)`

for a Noetherian ring `A` and finite modules `P`, `Q`.  At no single level is the comparison
either injective or surjective; the content is Stacks 09BB, consumed through its one clause about
the inverse limits — the isomorphism of the limit of its system of homomorphisms between the adic
quotients with the adic completion of `Hom_A(P, Q)`, whose components are the comparison. -/
theorem bijective_homAdicComparisonSectionsMap [IsNoetherianRing A] [Module.Finite A P]
    [Module.Finite A Q] : Function.Bijective (homAdicComparisonSectionsMap I P Q) := by
  obtain ⟨homTransition, -, comparison, hc1, -, hc3, -, -, -, ⟨homLimitIso, hlim⟩, -⟩ :=
    Stacks.AdicSystem.HomComparison.hom_isom_quotient_systems_mittagLeffler_and_completion
      (A := A) (M := P) (N := Q) I
  -- the compatible sequences of the system of Stacks 09BB are the adic completion of `Hom (P, Q)`,
  -- the components of the identification being the comparison
  obtain ⟨eTgt, heTgt⟩ : ∃ eTgt :
      { x : ∀ n : ℕ, (P ⧸ I ^ n • (⊤ : Submodule A P)) →ₗ[A]
            (Q ⧸ I ^ n • (⊤ : Submodule A Q)) //
          ∀ n : ℕ, homTransition n (x (n + 1)) = x n } ≃ AdicCompletion I (P →ₗ[A] Q),
      ∀ x (n : ℕ),
        comparison n (AdicCompletion.eval I (P →ₗ[A] Q) n (eTgt x)) = x.1 n :=
    ⟨(Stacks.ProZero.towerSectionsLimitEquiv
        (fun n => ModuleCat.of A ((P ⧸ I ^ n • (⊤ : Submodule A P)) →ₗ[A]
          (Q ⧸ I ^ n • (⊤ : Submodule A Q))))
        (fun n => ModuleCat.ofHom (homTransition n))).toEquiv.trans
      homLimitIso.toLinearEquiv.toEquiv,
      fun x n => (hlim _ n).trans (Stacks.ProZero.limit_π_towerSectionsLimitEquiv
        (fun n => ModuleCat.of A ((P ⧸ I ^ n • (⊤ : Submodule A P)) →ₗ[A]
          (Q ⧸ I ^ n • (⊤ : Submodule A Q))))
        (fun n => ModuleCat.ofHom (homTransition n)) x n)⟩
  -- the adic completion is the compatible sequences of its own adic quotient tower, shifted
  obtain ⟨eSrc, heSrc⟩ : ∃ eSrc :
      { x : ∀ n : ℕ, (P →ₗ[A] Q) ⧸ I ^ (n + 1) • (⊤ : Submodule A (P →ₗ[A] Q)) //
          ∀ n : ℕ, AdicCompletion.transitionMap I (P →ₗ[A] Q) (Nat.le_succ (n + 1)) (x (n + 1)) =
            x n } ≃ AdicCompletion I (P →ₗ[A] Q),
      ∀ x (n : ℕ), AdicCompletion.eval I (P →ₗ[A] Q) (n + 1) (eSrc x) = x.1 n :=
    ⟨(Stacks.SuccTower.sectionsShift fun n x =>
        AdicCompletion.transitionMap I (P →ₗ[A] Q) (Nat.le_succ n) x).symm.trans
      (adicCompletionSuccSectionsEquiv I (P →ₗ[A] Q)),
      fun x n => x.2 n⟩
  -- the comparison is therefore a bijection on the compatible sequences, at the shifted indexing
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : { x : ∀ n : ℕ, (P →ₗ[A] Q) ⧸ I ^ (n + 1) • (⊤ : Submodule A (P →ₗ[A] Q))
        // ∀ n : ℕ, AdicCompletion.transitionMap I (P →ₗ[A] Q) (Nat.le_succ (n + 1)) (x (n + 1)) =
          x n } ≃
      { y : ∀ n : ℕ, (P ⧸ I ^ (n + 1) • (⊤ : Submodule A P)) →ₗ[A]
            (Q ⧸ I ^ (n + 1) • (⊤ : Submodule A Q)) //
          ∀ n : ℕ, homTransition (n + 1) (y (n + 1)) = y n },
      ∀ x (n : ℕ), (Λ x).1 n = comparison (n + 1) (x.1 n) := by
    refine ⟨eSrc.trans (eTgt.symm.trans
      (Stacks.SuccTower.sectionsShift fun n x => homTransition n x)), fun x n => ?_⟩
    rw [Equiv.trans_apply, Equiv.trans_apply, Stacks.SuccTower.sectionsShift_apply,
      ← heTgt (eTgt.symm (eSrc x)) (n + 1), Equiv.apply_symm_apply, heSrc]
  -- quotienting the source of a homomorphism identifies the two targets
  obtain ⟨cb, hcb⟩ : ∃ cb :
      { y : ∀ n : ℕ, (P ⧸ I ^ (n + 1) • (⊤ : Submodule A P)) →ₗ[A]
            (Q ⧸ I ^ (n + 1) • (⊤ : Submodule A Q)) //
          ∀ n : ℕ, homTransition (n + 1) (y (n + 1)) = y n } ≃
      { y : ∀ n : ℕ, P →ₗ[A] (Q ⧸ I ^ (n + 1) • (⊤ : Submodule A Q)) //
          ∀ n : ℕ, homAdicTargetTransition I P Q n (y (n + 1)) = y n },
      ∀ y (n : ℕ), (cb y).1 n = quotientSourceHomEquiv I P (n + 1) _
        (smul_eq_zero_quotient_pow_smul_top I Q (n + 1)) (y.1 n) :=
    ⟨Stacks.SuccTower.sectionsCongr (fun n y => homTransition (n + 1) y)
      (fun n y => homAdicTargetTransition I P Q n y)
      (fun n => quotientSourceHomEquiv I P (n + 1) _
        (smul_eq_zero_quotient_pow_smul_top I Q (n + 1)))
      (fun n y => LinearMap.ext fun m => hc1 (n + 1) y m), fun y n => rfl⟩
  have key : homAdicComparisonSectionsMap I P Q = Λ.trans cb := by
    funext x
    refine Subtype.ext (funext fun n => ?_)
    rw [Equiv.trans_apply, hcb, hΛ, homAdicComparisonSectionsMap_apply]
    obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective
      (I ^ (n + 1) • (⊤ : Submodule A (P →ₗ[A] Q))) (x.1 n)
    rw [← hf]
    exact LinearMap.ext fun m => (hc3 (n + 1) f m).symm
  rw [key]
  exact (Λ.trans cb).bijective

end Stacks.AdicSystem.HomSections

end
