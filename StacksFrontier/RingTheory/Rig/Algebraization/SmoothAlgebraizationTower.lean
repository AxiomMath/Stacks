module

public import StacksFrontier.RingTheory.Restricted.RigSmoothSmoothLocus
public import StacksFrontier.RingTheory.Rig.Algebraization.AlgebraizationTower

/-!
# Compatible systems of smooth algebraizations of the quotients `B ⧸ aⁿ⁺¹ B`

The rig-smooth counterpart of `Rig.AlgebraizationTower`, for the induction of Gabber–Zavyalov
(the main claim of Stacks 0GAX).  Let `A` be Noetherian, `a ∈ I`, and `B` rig-smooth over
`(A, I)`.  A `Rig.SmoothAlgebraizationTower` is a system of finite type `A ⧸ (aⁿ⁺¹)`-algebras `Cₙ`,
each smooth over the complement of `V(I)`, with surjections `Cₙ₊₁ → Cₙ` of kernel `aⁿ⁺¹ Cₙ₊₁` and
identifications `Cₙ^∧ ≅ B ⧸ aⁿ⁺¹ B` compatible with the transitions.

## Main definitions

* `Rig.SmoothAlgebraizationStage`: one level of such a system.
* `Rig.SmoothAlgebraizationTower`: the system, extending `Rig.AlgebraizationTowerData`; its limit
  `B' = lim Cₙ` (Stacks 0AJN) and the comparison map `B' → B` are
  `Rig.AlgebraizationTowerData.limit` and `Rig.AlgebraizationTowerData.toCarrier`, shared with the
  étale system `Rig.AlgebraizationTower` of Stacks 0AKA.

## Main results

* `Rig.nonempty_smoothAlgebraizationTower`: levels which lift one step at a time assemble into a
  system.
* `Rig.SmoothAlgebraizationTower.exists_quotient_smoothAwayFrom`: every `B' ⧸ aⁿ⁺¹ B'` is a finite
  type `A ⧸ (aⁿ⁺¹)`-algebra smooth over the complement of `V(I)`.
-/

@[expose] public section

namespace Rig

universe u

section Stage

variable {A : Type u} [CommRing A] (I : Ideal A) (a : A) (B : Type u) [CommRing B] [Algebra A B]

/-- One level of the compatible system of the rig-smooth algebraization: a finite type
`A ⧸ (aⁿ⁺¹)`-algebra `C`, smooth over the complement of `V(I)`, with an `A`-algebra isomorphism
between its `I`-adic completion and `B ⧸ aⁿ⁺¹ B`. -/
public structure SmoothAlgebraizationStage (n : ℕ) where
  /-- The algebra `C`. -/
  C : Type u
  [commRing : CommRing C]
  [algebraQuot : Algebra (A ⧸ Ideal.span {a ^ (n + 1)}) C]
  [algebra : Algebra A C]
  [isScalarTower : IsScalarTower A (A ⧸ Ideal.span {a ^ (n + 1)}) C]
  [finiteType : Algebra.FiniteType (A ⧸ Ideal.span {a ^ (n + 1)}) C]
  /-- `C` is smooth over the complement of `V(I)`. -/
  smooth : SmoothAwayFrom (A ⧸ Ideal.span {a ^ (n + 1)})
    (I.map (Ideal.Quotient.mk (Ideal.span {a ^ (n + 1)}))) C
  /-- The identification of the completion of `C` with `B ⧸ aⁿ⁺¹ B`. -/
  equiv : AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A]
    B ⧸ (Ideal.span {a ^ (n + 1)}).map (algebraMap A B)

attribute [instance] SmoothAlgebraizationStage.commRing SmoothAlgebraizationStage.algebraQuot
  SmoothAlgebraizationStage.algebra SmoothAlgebraizationStage.isScalarTower
  SmoothAlgebraizationStage.finiteType

end Stage

/-- A compatible system of smooth algebraizations of the quotients `B ⧸ aⁿ⁺¹ B`: the data
`Rig.AlgebraizationTowerData I a B` — finite type `A ⧸ (aⁿ⁺¹)`-algebras `Cₙ` with surjections
`Cₙ₊₁ → Cₙ` of kernel `aⁿ⁺¹ Cₙ₊₁` and `A`-algebra isomorphisms `Cₙ^∧ ≅ B ⧸ aⁿ⁺¹ B` of `I`-adic
completions compatible with the transitions — with every `Cₙ` smooth over the complement of
`V(I)`.  The Lean index `n` stands for the source's `C_{n+1}`. -/
public structure SmoothAlgebraizationTower {A : Type u} [CommRing A] (I : Ideal A) (a : A)
    (B : Type u) [CommRing B] [Algebra A B] extends AlgebraizationTowerData I a B where
  /-- Each `C_{n+1}` is smooth over the complement of `V(I)`. -/
  smooth : ∀ n, SmoothAwayFrom (A ⧸ Ideal.span {a ^ (n + 1)})
    (I.map (Ideal.Quotient.mk (Ideal.span {a ^ (n + 1)}))) (C n)

section Assembly

variable {A : Type u} [CommRing A] (I : Ideal A) (a : A) (B : Type u) [CommRing B] [Algebra A B]

/-- **Assembling the levels.**  If there is a level `0` and every level `n` lifts to a level
`n + 1` along a surjection of kernel `aⁿ⁺¹` compatible with the identifications of the
completions, then there is a compatible system `Rig.SmoothAlgebraizationTower I a B`. -/
public theorem nonempty_smoothAlgebraizationTower
    (h0 : Nonempty (SmoothAlgebraizationStage I a B 0))
    (hnext : ∀ (n : ℕ) (St : SmoothAlgebraizationStage I a B n),
      ∃ (T : SmoothAlgebraizationStage I a B (n + 1)) (p : T.C →ₐ[A] St.C),
        Function.Surjective p ∧
        RingHom.ker p.toRingHom = (Ideal.span {a ^ (n + 1)}).map (algebraMap A T.C) ∧
        ∀ x : T.C, St.equiv (algebraMap St.C _ (p x)) =
          Ideal.Quotient.factor (Ideal.map_mono (Ideal.span_singleton_le_span_singleton.mpr
            (pow_dvd_pow a (Nat.le_succ (n + 1))))) (T.equiv (algebraMap T.C _ x))) :
    Nonempty (SmoothAlgebraizationTower I a B) := by
  let st : ∀ n, SmoothAlgebraizationStage I a B n := fun n =>
    Nat.rec (motive := fun n => SmoothAlgebraizationStage I a B n) h0.some
      (fun n St => (hnext n St).choose) n
  exact ⟨{
    C := fun n => (st n).C
    commRing := fun n => (st n).commRing
    algebraQuot := fun n => (st n).algebraQuot
    algebra := fun n => (st n).algebra
    isScalarTower := fun n => (st n).isScalarTower
    finiteType := fun n => (st n).finiteType
    smooth := fun n => (st n).smooth
    transition := fun n => (hnext n (st n)).choose_spec.choose
    transition_surjective := fun n => (hnext n (st n)).choose_spec.choose_spec.1
    transition_ker := fun n => (hnext n (st n)).choose_spec.choose_spec.2.1
    equiv := fun n => (st n).equiv
    equiv_transition := fun n => (hnext n (st n)).choose_spec.choose_spec.2.2 }⟩

end Assembly

namespace SmoothAlgebraizationTower

variable {A : Type u} [CommRing A] {I : Ideal A} {a : A} {B : Type u} [CommRing B] [Algebra A B]

/-- **Every quotient of the limit is smooth off `V(I)`.**  For each `n`, `B' ⧸ aⁿ⁺¹ B'` is a finite
type `A ⧸ (aⁿ⁺¹)`-algebra smooth over the complement of `V(I)`: it is the level `Cₙ`. -/
theorem exists_quotient_smoothAwayFrom (T : SmoothAlgebraizationTower I a B) (n : ℕ) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra (A ⧸ Ideal.span {a ^ (n + 1)}) C)
      (_ : Algebra A C) (_ : IsScalarTower A (A ⧸ Ideal.span {a ^ (n + 1)}) C),
      Algebra.FiniteType (A ⧸ Ideal.span {a ^ (n + 1)}) C ∧
      SmoothAwayFrom (A ⧸ Ideal.span {a ^ (n + 1)}) (I.map (Ideal.Quotient.mk _)) C ∧
      Nonempty ((T.limit.carrier ⧸ (Ideal.span {a ^ (n + 1)}).map
        (algebraMap A T.limit.carrier)) ≃ₐ[A] C) :=
  ⟨T.C n, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, T.smooth n,
    ⟨T.quotientEquiv n⟩⟩

end SmoothAlgebraizationTower

end Rig

end
