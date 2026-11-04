module

public import StacksFrontier.Deformation.FlatAlgebraLiftCompletion
import all StacksFrontier.Deformation.FlatAlgebraLiftCompletion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0DZ3 with Stacks 0DZ2 taken only where it is used

`StacksFrontier.Deformation.FlatAlgebraLiftCompletion` proves Stacks 0DZ3 — flat lifts of a finite
type flat `A`-algebra `B` to `A'` exist exactly when flat lifts of its `𝔟`-adic completion do —
from the hypothesis `Deformation.FlatModuleLiftBaseChangeStatement`, which is Stacks 0DZ2
quantified over *every* surjection `A' → A` and every pair of cartesian squares over it. That
quantification is more than the proof consumes, and this file narrows it twice.

**Relativizing to the surjection in hand.** `Deformation.FlatModuleLiftBaseChangeStatementAt A' A`
is Stacks 0DZ2 at one fixed surjection `A' → A`, and `FlatModuleLiftBaseChangeStatement` is that
statement quantified over the surjection. Every proof of Stacks 0DZ3 applies Stacks 0DZ2 only at
the surjection it is given, so each has an `_at` form carrying the relativized hypothesis. This
is what makes the square-zero case unconditional:
`StacksFrontier.Deformation.FlatModuleLiftBaseChangeAbstract` proves
`FlatModuleLiftBaseChangeStatementAt A' A` outright whenever the kernel of `A' → A` has square
zero, which the quantified form — false at a nilpotent kernel — can never be.

**Narrowing to one instance.** Relativizing is not the end of it. The two assemblies
`Deformation.hasFlatAlgebraLift_imp_baseChange_of_presentation_at` and
`Deformation.hasFlatAlgebraLift_of_baseChange_of_presentation_at` apply Stacks 0DZ2 exactly once
each, and both at the same data: `(P', P, Q', Q) = (P', P, Q', P ⊗_{P'} Q')`, `M = B` and
`N = Q ⊗_P B`, the first through `mp` and the second through `mpr`. So neither needs the
statement; each needs one biconditional, `Deformation.FlatModuleLiftBaseChangeInstance`, and that
is the hypothesis they carry. The relativized statement is applied in exactly one place,
`Deformation.flatModuleLiftBaseChangeInstance_of_statementAt`, which discharges Stacks 0DZ2's own
premises from the data its callers already carry.

The narrowing does not reach the equivalence itself: the three tagged equivalences for Stacks
0DZ3, 0DZ7 and 0DZB choose their presentation inside the proof, out of
`Algebra.FiniteType.iff_quotient_mvPolynomial''`, so the rings at which the instance is needed
are not nameable in their statements. They keep the relativized statement, and the bridge above
is applied inside each of their proofs.

**The forward implication needs no Stacks 0DZ2 at all.** Stacks 0DZ3's rings are Noetherian, so
flatness of `(B')^∧` over `A'` is `Module.Flat.trans` of `A' → B'` with `B' → (B')^∧`, the second
factor being flat because `B'` is Noetherian (`AdicCompletion.flat_of_isNoetherian`) and not
because completion preserves flatness. That `B'` is Noetherian follows from the tag's own
hypotheses: `ker(B' → B) = ker(A' → A)·B'` is nilpotent and finitely generated and the quotient
is `B`. The identification of the base change is the other half, and it is where finiteness
enters: `B` is a finite `B'`-module because `B' → B` is surjective, so `ofTensorProductAlgEquiv`
identifies `(B')^∧ ⊗_{B'} B` with the completion of `B`. The result,
`Deformation.hasFlatAlgebraLift_adicCompletion_of_hasFlatAlgebraLift_of_isNoetherianRing`, needs
neither finite type nor flatness of `B` over `A` nor the syntomic hypothesis. Only the converse
is still conditional.

## Main definitions

* `Deformation.FlatModuleLiftBaseChangeStatementAt`: Stacks 0DZ2 at one fixed surjection
  `A' → A`.
* `Deformation.FlatModuleLiftBaseChangeInstance`: its conclusion at one named square and one
  named module — the only instance of it the two assemblies apply, and the hypothesis they carry.

## Main results

* `Deformation.flatModuleLiftBaseChangeInstance_of_statementAt`: the relativized statement
  supplies the instance.
* `Deformation.hasFlatAlgebraLift_adicCompletion_of_hasFlatAlgebraLift_of_isNoetherianRing`: the
  implication from `B` to its completion, **unconditionally**.
* `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion_at`: the implication from
  the completion back to `B`, from Stacks 0DZ2 at the surjection in hand.
* `Deformation.hasFlatAlgebraLift_adicCompletion_iff_at`: Stacks 0DZ3 with Stacks 0DZ2 taken only
  at the surjection in hand.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 0DZ3](https://stacks.math.columbia.edu/tag/0DZ3)
* [Stacks Project, Tag 0DYC](https://stacks.math.columbia.edu/tag/0DYC)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Deformation

/-- **Stacks 0DZ2 with the source's hypotheses, for a finite module.** For two cartesian
squares of Noetherian rings `A' → P' → Q'` over `A → P → Q` with flat horizontal maps and
surjective vertical maps with nilpotent kernels, an ideal `J'` of `P'` with
`P'/J' = Q'/J'Q'`, and a `P`-module `M` finite
over `P` and flat over `A` whose localization `M_g` has an `A'`-flat `(P')_g`-module lift for
every `g ∈ J'`: `M` has an `A'`-flat `P'`-module lift if and only if `Q ⊗_P M` has an
`A'`-flat `Q'`-module lift.

**This statement is FALSE, at every universe.**
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement` of
`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutation` proves
`¬ FlatModuleLiftBaseChangeStatement.{0}` outright, and
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement_ulift` of
`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutationUniverse` proves
`¬ FlatModuleLiftBaseChangeStatement.{u}` for a universe parameter `u`, by instantiating this
definition at the `ULift`s of the counterexample's rings. The counterexample — the
Artin–Schreier obstruction on the nodal cubic, with a finite cyclic `M`, so that the finiteness
restriction added here does not save the statement — is set out in the module documentation of
the first of those two files and is not repeated here. Every theorem below that takes this
statement as a hypothesis is therefore vacuous. It is kept because it is the exact shape those
proofs consume, and because naming the false statement is how the defect stays visible.

The cartesian condition is carried by the identities `ker(P' → P) = ker(A' → A) · P'` and
`ker(Q' → Q) = ker(A' → A) · Q'` together with the scalar towers, which is what the proof of
Stacks 0DZ3 produces and consumes. -/
def FlatModuleLiftBaseChangeStatementAt (A' A : Type u) [CommRing A'] [CommRing A]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] : Prop :=
  ∀ (P' P Q' Q : Type u)
    [CommRing P'] [CommRing P] [CommRing Q'] [CommRing Q]
    [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing Q'] [IsNoetherianRing Q]
    [Algebra A' P'] [Algebra A' Q'] [Algebra A' P] [Algebra A' Q]
    [Algebra A P] [Algebra A Q] [Algebra P' P] [Algebra P' Q'] [Algebra P' Q]
    [Algebra P Q] [Algebra Q' Q]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' P' Q']
    [IsScalarTower A' Q' Q] [IsScalarTower A P Q] [IsScalarTower P' P Q]
    [IsScalarTower P' Q' Q],
    Function.Surjective (algebraMap A' A) →
    IsNilpotent (RingHom.ker (algebraMap A' A)) →
    Function.Surjective (algebraMap P' P) →
    RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P') →
    Function.Surjective (algebraMap Q' Q) →
    RingHom.ker (algebraMap Q' Q) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' Q') →
    Module.Flat A' P' → Module.Flat A' Q' → Module.Flat P' Q' → Module.Flat P Q →
    ∀ (J' : Ideal P'),
      Function.Bijective (Ideal.quotientMap (J'.map (algebraMap P' Q')) (algebraMap P' Q')
        Ideal.le_comap_map) →
    ∀ (M : Type u) [AddCommGroup M] [Module P M] [Module A M] [IsScalarTower A P M]
      [Module.Finite P M] [Module.Flat A M] (N : Type u) [AddCommGroup N] [Module Q N],
      Nonempty ((Q ⊗[P] M) ≃ₗ[Q] N) →
      (∀ g ∈ J',
        letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
          (Localization.awayMap (algebraMap P' P) g).toAlgebra
        ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
          (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
          Module.Flat A' L ∧ Nonempty
            ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
              ≃ₗ[Localization.Away (algebraMap P' P g)]
                (Localization.Away (algebraMap P' P g) ⊗[P] M))) →
      ((∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
          (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
          Nonempty ((P ⊗[P'] M') ≃ₗ[P] M)) ↔
        (∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
          (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
          Nonempty ((Q ⊗[Q'] N') ≃ₗ[Q] N)))

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### The one instance of Stacks 0DZ2 that the comparison consumes -/

/-- The scalar tower `A' → Q' → P ⊗_{P'} Q'` over an `A'`-algebra structure that factors through
`P'`. -/
private theorem isScalarTower_tensorProduct_right (A' P' P Q' : Type u)
    [CommRing A'] [CommRing P'] [CommRing P] [CommRing Q']
    [Algebra A' P'] [Algebra A' P] [Algebra A' Q'] [Algebra P' P] [Algebra P' Q']
    [IsScalarTower A' P' P] [IsScalarTower A' P' Q'] :
    IsScalarTower A' Q' (P ⊗[P'] Q') := by
  refine IsScalarTower.of_algebraMap_eq fun a' => ?_
  change (algebraMap A' P a') ⊗ₜ[P'] (1 : Q') = (1 : P) ⊗ₜ[P'] (algebraMap A' Q' a')
  rw [IsScalarTower.algebraMap_apply A' P' P, IsScalarTower.algebraMap_apply A' P' Q']
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul _

/-- The kernel of `Q' → P ⊗_{P'} Q'` is `ker(A' → A) · Q'` when that of `P' → P` is
`ker(A' → A) · P'` and `P' → P` is surjective. -/
private theorem ker_algebraMap_tensorProduct_right (A' A P' P Q' : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' Q'] [Algebra P' P] [Algebra P' Q']
    [IsScalarTower A' P' P] [IsScalarTower A' P' Q']
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P')) :
    RingHom.ker (algebraMap Q' (P ⊗[P'] Q')) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' Q') := by
  have h := ker_includeRight P' P Q' hsurjP
  rw [hkerP, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h
  exact h

/-- **Stacks 0DZ2 at a single square.** For a surjection `P' → P` of `A'`-algebras, a
`P'`-algebra `Q'` and a `P`-algebra `B`: `B` has an `A'`-flat `P'`-module lift if and only if
its base change to `Q = P ⊗_{P'} Q'` has an `A'`-flat `Q'`-module lift.

This is the conclusion of `Deformation.FlatModuleLiftBaseChangeStatementAt` at the one instance
of its data that the two implications of Stacks 0DZ3 below apply it to: the upper right corner
is `Q = P ⊗_{P'} Q'`, the module is `M = B` and its base change is `N = Q ⊗_P B`. Every
hypothesis of Stacks 0DZ2 is discharged there from data those lemmas already carry, which is
`Deformation.flatModuleLiftBaseChangeInstance_of_statementAt`; so this is a strictly weaker
hypothesis than `Deformation.FlatModuleLiftBaseChangeStatementAt A' A`, asking for the
comparison at four named rings and one named module instead of at every square and every
module.

The weakening is not a repair of anything. `Deformation.FlatModuleLiftBaseChangeStatement` and
its faithful restatement are refuted at every universe, so a consumer carrying the quantified
form is vacuous; a consumer carrying this instance is conditional on a statement that is not
known to be false. It is not known to be true either, and no tag becomes unconditional by
taking it. -/
def FlatModuleLiftBaseChangeInstance (A' P' P Q' B : Type u)
    [CommRing A'] [CommRing P'] [CommRing P] [CommRing Q'] [CommRing B]
    [Algebra A' P'] [Algebra A' Q'] [Algebra P' P] [Algebra P' Q'] [Algebra P B] : Prop :=
  (∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
      (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
      Nonempty ((P ⊗[P'] M') ≃ₗ[P] B)) ↔
    (∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
      (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
      Nonempty (((P ⊗[P'] Q') ⊗[Q'] N') ≃ₗ[P ⊗[P'] Q'] ((P ⊗[P'] Q') ⊗[P] B)))

/-- The one instance of Stacks 0DZ2 that the two implications of Stacks 0DZ3 consume, deduced
from Stacks 0DZ2 at the surjection `A' → A`. The upper right corner of the second square is
taken to be `Q = P ⊗_{P'} Q'`, whose reduction `Q' → Q` is surjective with kernel
`ker(A' → A) · Q'` because `P' → P` is; the module is `M = B`, finite over `P` because `P → B`
is surjective, and its base change is `N = Q ⊗_P B`. -/
theorem flatModuleLiftBaseChangeInstance_of_statementAt
    (A' A P' P B Q' : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing Q']
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B] [Algebra A' Q']
    [Algebra A P] [Algebra A B] [Algebra P' P] [Algebra P' B] [Algebra P B] [Algebra P' Q']
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [IsScalarTower A' P' Q']
    [Module.Flat A' P'] [Module.Flat A B] [Module.Flat P' Q']
    (h0DZ2 : FlatModuleLiftBaseChangeStatementAt.{u} A' A)
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (J' : Ideal P')
    (hquot : Function.Bijective (Ideal.quotientMap (J'.map (algebraMap P' Q'))
      (algebraMap P' Q') Ideal.le_comap_map))
    (hloc : ∀ g ∈ J',
      letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
        (Localization.awayMap (algebraMap P' P) g).toAlgebra
      ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
        (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
        Module.Flat A' L ∧ Nonempty
          ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
            ≃ₗ[Localization.Away (algebraMap P' P g)]
              (Localization.Away (algebraMap P' P g) ⊗[P] B))) :
    FlatModuleLiftBaseChangeInstance.{u} A' P' P Q' B := by
  have hsurjQ : Function.Surjective (algebraMap Q' (P ⊗[P'] Q')) :=
    surjective_includeRight P' P Q' hsurjP
  have hkerQ := ker_algebraMap_tensorProduct_right A' A P' P Q' hsurjP hkerP
  have : IsNoetherianRing (P ⊗[P'] Q') :=
    isNoetherianRing_of_surjective Q' (P ⊗[P'] Q') (algebraMap Q' (P ⊗[P'] Q')) hsurjQ
  have hflatA'Q' : Module.Flat A' Q' := Module.Flat.trans A' P' Q'
  have : Module.Finite P B := Module.Finite.of_surjective (Algebra.linearMap P B) hsurjB
  have : IsScalarTower A' Q' (P ⊗[P'] Q') := isScalarTower_tensorProduct_right A' P' P Q'
  exact h0DZ2 P' P Q' (P ⊗[P'] Q') hsurjA hnilA hsurjP hkerP hsurjQ hkerQ
    inferInstance hflatA'Q' inferInstance inferInstance J' hquot B
    ((P ⊗[P'] Q') ⊗[P] B) ⟨LinearEquiv.refl _ _⟩ hloc

/-- The assembly of the first implication of Stacks 0DZ3 out of Stacks 0DZ2 and the two
presentations, with Stacks 0DZ2 taken only at the one instance the proof applies it to:
`Deformation.FlatModuleLiftBaseChangeInstance A' P' P Q' B`. `B` is presented by `P` over `P'`;
its base change `C` to `Q = P ⊗_{P'} Q'` is presented by `Q` over `Q'`; and the two
module-lifting problems are compared by that instance. -/
public theorem hasFlatAlgebraLift_imp_baseChange_of_presentation_at
    (A' A P' P B Q' : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing Q']
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B] [Algebra A' Q']
    [Algebra A P] [Algebra A B] [Algebra P' P] [Algebra P' B] [Algebra P B] [Algebra P' Q']
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [IsScalarTower A' P' Q']
    [Algebra.FormallySmooth A' P'] [Module.Flat A' P'] [Module.Flat A B] [Module.Flat P' Q']
    (h0DZ2 : FlatModuleLiftBaseChangeInstance.{u} A' P' P Q' B)
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (C : Type u) [CommRing C] [Algebra A' C] [Algebra A C] [IsScalarTower A' A C]
    (e : (((P ⊗[P'] Q') ⊗[P] B)) ≃+* C)
    (hAe : ∀ a : A, algebraMap A C a =
      e ((algebraMap A (P ⊗[P'] Q') a) ⊗ₜ[P] (1 : B))) :
    HasFlatAlgebraLift A' A B → HasFlatAlgebraLift A' A C := by
  have hsurjQ : Function.Surjective (algebraMap Q' (P ⊗[P'] Q')) :=
    surjective_includeRight P' P Q' hsurjP
  have hkerQ := ker_algebraMap_tensorProduct_right A' A P' P Q' hsurjP hkerP
  have hnilQ : IsNilpotent (RingHom.ker (algebraMap Q' (P ⊗[P'] Q'))) := by
    rw [hkerQ]
    exact isNilpotent_ideal_map hnilA _
  have : IsScalarTower A' Q' (P ⊗[P'] Q') := isScalarTower_tensorProduct_right A' P' P Q'
  -- the comparison of the two base changes of `Q'`
  obtain ⟨eQQ, heQQ⟩ := exists_algEquiv_tensorBaseChange A' A P' P Q' hsurjA hsurjP hkerP
    (fun a => IsScalarTower.algebraMap_apply A P (P ⊗[P'] Q') a)
  -- the presentation of the base change of `B`
  let : Algebra (P ⊗[P'] Q') C :=
    (e.toRingHom.comp (algebraMap (P ⊗[P'] Q') ((P ⊗[P'] Q') ⊗[P] B))).toAlgebra
  let : Algebra Q' C :=
    ((algebraMap (P ⊗[P'] Q') C).comp (algebraMap Q' (P ⊗[P'] Q'))).toAlgebra
  have : IsScalarTower Q' (P ⊗[P'] Q') C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A (P ⊗[P'] Q') C := IsScalarTower.of_algebraMap_eq hAe
  have : IsScalarTower A' (P ⊗[P'] Q') C := IsScalarTower.to₁₃₄ A' A (P ⊗[P'] Q') C
  have : IsScalarTower A' Q' C := IsScalarTower.to₁₂₄ A' Q' (P ⊗[P'] Q') C
  have hsurjC : Function.Surjective (algebraMap (P ⊗[P'] Q') C) :=
    e.surjective.comp (surjective_tmul_one P B hsurjB (P ⊗[P'] Q'))
  have eC : (((P ⊗[P'] Q') ⊗[P] B)) ≃ₗ[P ⊗[P'] Q'] C :=
    (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)).toLinearEquiv
  intro hB
  refine hasFlatAlgebraLift_of_exists_flatModuleLift hsurjQ hnilQ hsurjC eQQ heQQ ?_
  obtain ⟨N', _, _, _, _, hflatN', ⟨eN⟩⟩ := h0DZ2.mp
    (exists_flatModuleLift_of_hasFlatAlgebraLift hsurjA hnilA hsurjP hkerP hB)
  exact ⟨N', inferInstance, inferInstance, inferInstance, inferInstance, hflatN',
    ⟨eN.trans eC⟩⟩

/-- The assembly of the second implication of Stacks 0DZ3 out of Stacks 0DZ2 and the two
presentations, with Stacks 0DZ2 taken only at the one instance the proof applies it to:
`Deformation.FlatModuleLiftBaseChangeInstance A' P' P Q' B`. A flat algebra lift of `C` along
which the structure map of `C` lifts to `Q'` is an `A'`-flat `Q'`-module lift of `C`; that
instance turns it into an `A'`-flat `P'`-module lift of `B`, which is a flat algebra lift of `B`
by Nakayama. -/
public theorem hasFlatAlgebraLift_of_baseChange_of_presentation_at
    (A' A P' P B Q' C : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing Q']
    [CommRing C]
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B] [Algebra A' Q']
    [Algebra A P] [Algebra A B] [Algebra P' P] [Algebra P' B] [Algebra P B] [Algebra P' Q']
    [Algebra A' C] [Algebra A C] [Algebra Q' C]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [IsScalarTower A' P' Q'] [IsScalarTower A' A C]
    [Algebra.FormallySmooth A' P'] [Module.Flat A' P'] [Module.Flat A B] [Module.Flat P' Q']
    (h0DZ2 : FlatModuleLiftBaseChangeInstance.{u} A' P' P Q' B)
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (ePP : (A ⊗[A'] P') ≃ₐ[A] P)
    (hePP : ∀ x : P', ePP (1 ⊗ₜ[A'] x) = algebraMap P' P x)
    (e : (((P ⊗[P'] Q') ⊗[P] B)) ≃+* C)
    (hAe : ∀ a : A, algebraMap A C a =
      e ((algebraMap A (P ⊗[P'] Q') a) ⊗ₜ[P] (1 : B)))
    (hQe : ∀ x : Q', algebraMap Q' C x = e (((1 : P) ⊗ₜ[P'] x) ⊗ₜ[P] (1 : B)))
    (hlift : ∀ (C' : Type u) (_ : CommRing C') (_ : Algebra A' C')
      (eC : (A ⊗[A'] C') ≃ₐ[A] C), ∃ g : Q' →ₐ[A'] C',
        ∀ x : Q', eC (1 ⊗ₜ[A'] (g x)) = algebraMap Q' C x) :
    HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B := by
  have hsurjQ : Function.Surjective (algebraMap Q' (P ⊗[P'] Q')) :=
    surjective_includeRight P' P Q' hsurjP
  have hkerQ := ker_algebraMap_tensorProduct_right A' A P' P Q' hsurjP hkerP
  have hnilP : IsNilpotent (RingHom.ker (algebraMap P' P)) := by
    rw [hkerP]
    exact isNilpotent_ideal_map hnilA _
  -- the presentation of `C` over `Q = P ⊗_{P'} Q'`
  let : Algebra (P ⊗[P'] Q') C :=
    (e.toRingHom.comp (algebraMap (P ⊗[P'] Q') ((P ⊗[P'] Q') ⊗[P] B))).toAlgebra
  have hQ2 : ∀ x : Q', algebraMap Q' C x =
      algebraMap (P ⊗[P'] Q') C (algebraMap Q' (P ⊗[P'] Q') x) := by
    intro x
    rw [hQe x]
    rfl
  have : IsScalarTower Q' (P ⊗[P'] Q') C := IsScalarTower.of_algebraMap_eq hQ2
  have : IsScalarTower A (P ⊗[P'] Q') C := IsScalarTower.of_algebraMap_eq hAe
  have eC : (((P ⊗[P'] Q') ⊗[P] B)) ≃ₗ[P ⊗[P'] Q'] C :=
    (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)).toLinearEquiv
  rintro ⟨C', _, _, hflatC', ⟨eCa⟩⟩
  obtain ⟨g, hg⟩ := hlift C' inferInstance inferInstance eCa
  refine hasFlatAlgebraLift_of_exists_flatModuleLift hsurjP hnilP hsurjB ePP hePP (h0DZ2.mpr ?_)
  obtain ⟨N', _, _, _, _, hflatN', ⟨eN⟩⟩ :=
    exists_flatModuleLift_of_algebraLift hsurjA hsurjQ hkerQ C' hflatC' eCa g hg
  exact ⟨N', inferInstance, inferInstance, inferInstance, inferInstance, hflatN',
    ⟨eN.trans eC.symm⟩⟩

/-- The second implication of Stacks 0DZ3 for the completed presentation: the lifting
hypothesis of `Deformation.hasFlatAlgebraLift_of_baseChange_of_presentation` is supplied by
Stacks 0DYC when `Q'` is the `J'`-adic completion of `P'` and `J'` lands in the ideal of
completeness of `C`.

Stacks 0DZ2 is taken here only at the surjection `A' → A` in hand, as
`Deformation.FlatModuleLiftBaseChangeStatementAt`. The form quantified over every surjection is
`Deformation.hasFlatAlgebraLift_of_adicCompletion_of_presentation`, which specializes `h0DZ2` to
this one. -/
private theorem hasFlatAlgebraLift_of_adicCompletion_of_presentation_at
    (A' A P' P B C : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing C]
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing C]
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B] [Algebra A' C]
    [Algebra A P] [Algebra A B] [Algebra A C] [Algebra P' P] [Algebra P' B] [Algebra P B]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [IsScalarTower A' A C]
    [Algebra.FormallySmooth A' P'] [Module.Flat A' P'] [Module.Flat A B]
    (h0DZ2 : FlatModuleLiftBaseChangeStatementAt.{u} A' A)
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (ePP : (A ⊗[A'] P') ≃ₐ[A] P)
    (hePP : ∀ x : P', ePP (1 ⊗ₜ[A'] x) = algebraMap P' P x)
    (J' : Ideal P') [Module.Flat P' (AdicCompletion J' P')]
    [IsNoetherianRing (AdicCompletion J' P')]
    (hloc : ∀ g ∈ J',
      letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
        (Localization.awayMap (algebraMap P' P) g).toAlgebra
      ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
        (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
        Module.Flat A' L ∧ Nonempty
          ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
            ≃ₗ[Localization.Away (algebraMap P' P g)]
              (Localization.Away (algebraMap P' P g) ⊗[P] B)))
    (c : Ideal C) (hc : IsAdicComplete c C)
    (e : (((P ⊗[P'] AdicCompletion J' P') ⊗[P] B)) ≃+* C)
    (hAe : ∀ a : A, algebraMap A C a =
      e ((algebraMap A (P ⊗[P'] AdicCompletion J' P') a) ⊗ₜ[P] (1 : B)))
    (hJc : ∀ g ∈ J', e (((algebraMap P' P g) ⊗ₜ[P']
      (1 : AdicCompletion J' P')) ⊗ₜ[P] (1 : B)) ∈ c) :
    HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B := by
  -- the algebra structures on `C` over the completed presentation
  let : Algebra (P ⊗[P'] AdicCompletion J' P') C :=
    (e.toRingHom.comp (algebraMap (P ⊗[P'] AdicCompletion J' P')
      ((P ⊗[P'] AdicCompletion J' P') ⊗[P] B))).toAlgebra
  let : Algebra (AdicCompletion J' P') C :=
    ((algebraMap (P ⊗[P'] AdicCompletion J' P') C).comp
      (algebraMap (AdicCompletion J' P') (P ⊗[P'] AdicCompletion J' P'))).toAlgebra
  let : Algebra P' C := ((algebraMap (AdicCompletion J' P') C).comp
    (algebraMap P' (AdicCompletion J' P'))).toAlgebra
  have : IsScalarTower A' (AdicCompletion J' P') (P ⊗[P'] AdicCompletion J' P') :=
    isScalarTower_tensorProduct_right A' P' P (AdicCompletion J' P')
  have : IsScalarTower (AdicCompletion J' P') (P ⊗[P'] AdicCompletion J' P') C :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A (P ⊗[P'] AdicCompletion J' P') C :=
    IsScalarTower.of_algebraMap_eq hAe
  have : IsScalarTower A' (P ⊗[P'] AdicCompletion J' P') C :=
    IsScalarTower.to₁₃₄ A' A (P ⊗[P'] AdicCompletion J' P') C
  have : IsScalarTower A' (AdicCompletion J' P') C :=
    IsScalarTower.to₁₂₄ A' (AdicCompletion J' P') (P ⊗[P'] AdicCompletion J' P') C
  have : IsScalarTower P' (AdicCompletion J' P') C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A' P' C := IsScalarTower.to₁₂₄ A' P' (AdicCompletion J' P') C
  -- the image of `J'` in `C` lies in the ideal of completeness
  have hJcC : ∀ g ∈ J', algebraMap P' C g ∈ c := by
    intro g hg
    have hval : algebraMap P' C g =
        e (((1 : P) ⊗ₜ[P'] (algebraMap P' (AdicCompletion J' P') g)) ⊗ₜ[P] (1 : B)) := rfl
    rw [hval, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    exact hJc g hg
  refine hasFlatAlgebraLift_of_baseChange_of_presentation_at A' A P' P B
    (AdicCompletion J' P') C
    (flatModuleLiftBaseChangeInstance_of_statementAt A' A P' P B (AdicCompletion J' P') h0DZ2
      hsurjA hnilA hsurjP hkerP hsurjB J' (bijective_quotientMap_adicCompletion J') hloc)
    hsurjA hnilA hsurjP hkerP hsurjB ePP hePP e hAe (fun _ => rfl)
    (fun C' _ _ eCa => ?_)
  exact exists_algHom_adicCompletion_of_algebraLift A' A P' C C' hsurjA hnilA J' c hc hJcC
    (fun _ => rfl) eCa

/-! ### The forward implication, without Stacks 0DZ2 -/

/-- **The adic completion of a flat algebra lift is a flat algebra lift of the adic
completion.** Let `A' → A` be a surjection of rings with nilpotent kernel and `A'` Noetherian,
let `B` be a Noetherian `A`-algebra and let `𝔟 ⊆ B` be an ideal. If `B` has a flat lift `B'` to
`A'`, then the `𝔟'`-adic completion of `B'`, at the preimage `𝔟'` of `𝔟` under the reduction
`B' → B`, is a flat lift of the `𝔟`-adic completion of `B` to `A'`.

This is the forward implication of Stacks 0DZ3 proved outright: it carries no `h0DZ2`, no
syntomic hypothesis, no finite type and no flatness of `B` over `A`, and the Noetherian
hypothesis on `A` is replaced by the weaker `IsNoetherianRing B` that the proof actually
consumes. Nilpotence of the kernel and Noetherianness of `A'` are used, both only to get
`IsNoetherianRing B'`.

The proof is the construction the two sibling tags use, and the obstruction the implementation
notes record — that a completion of a flat module need not be flat — does **not** bite under
this tag's own hypotheses. Let `ρ : B' → B` be the reduction, surjective because `A' → A` is,
with kernel `ker(A' → A)·B'`. That kernel is nilpotent and finitely generated, so `B'` is
complete along it and `B' / ker ρ ≅ B` is Noetherian, whence `B'` is Noetherian by
`noetherian_of_isAdicComplete_fg`. Over a Noetherian ring an adic completion is flat
(`AdicCompletion.flat_of_isNoetherian`), so `C' = (B')^∧_{𝔟'}` is flat over `B'` and therefore
over `A'`. For the identification of the base change: `ρ` surjective makes `B` a finite
`B'`-module, so `C' ⊗_{B'} B` is the `𝔟'B`-adic completion of `B` by
`ofTensorProductAlgEquiv` — this is the step that needs `B` finite over `B'` and `B'`
Noetherian, and it is what the general case lacks — and `𝔟'B = 𝔟`; while
`A ⊗_{A'} C' ≅ B ⊗_{B'} C'` by `Deformation.exists_algEquiv_tensorBaseChange`, both being `C'`
modulo `ker(A' → A)·C'`.

This declaration deliberately carries **no** Stacks attribute: one implication of a
biconditional is not the tag. The 0DZ3 registration is on
`Deformation.hasFlatAlgebraLift_iff_hasFlatAlgebraLift_adicCompletion`, which does not carry
`h0DZ2`; the published proof of 0DZ3 routes through Stacks 0DZ2, which is false as stated (a
Stacks erratum). The section note below gives the analysis. What is proved outright
is this half of the tag; the converse at a nilpotent kernel is open. -/
@[sga "1 IV 3.1" "more general"]
theorem hasFlatAlgebraLift_adicCompletion_of_hasFlatAlgebraLift_of_isNoetherianRing
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing B] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (b : Ideal B) :
    HasFlatAlgebraLift A' A B → HasFlatAlgebraLift A' A (AdicCompletion b B) := by
  classical
  let : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  rintro ⟨B', _, _, hflatB', ⟨eB'⟩⟩
  have := hflatB'
  -- the reduction of the lift: a surjection with kernel `ker(A' → A)·B'`
  set rho : B' →ₐ[A'] B :=
    (eB'.restrictScalars A').toAlgHom.comp Algebra.TensorProduct.includeRight with hrhodef
  have hrhosurj : Function.Surjective rho :=
    (eB'.restrictScalars A').surjective.comp (surjective_includeRight A' A B' hsurjA)
  have hrhoker : RingHom.ker rho = (RingHom.ker (algebraMap A' A)).map (algebraMap A' B') :=
    ker_comp_includeRight B B' hsurjA (eB'.restrictScalars A')
  let : Algebra B' B := rho.toRingHom.toAlgebra
  have hsurjP : Function.Surjective (algebraMap B' B) := hrhosurj
  have hkerP : RingHom.ker (algebraMap B' B) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' B') := hrhoker
  have : IsScalarTower A' B' B :=
    IsScalarTower.of_algebraMap_eq fun a' => (rho.commutes a').symm
  have : Module.Finite B' B := Module.Finite.of_surjective (Algebra.linearMap B' B) hsurjP
  -- `B'` is Noetherian: a nilpotent thickening with finitely generated kernel of Noetherian `B`
  have hrhonil : IsNilpotent (RingHom.ker rho) := by
    rw [hrhoker]
    exact isNilpotent_ideal_map hnilA _
  have hrhofg : (RingHom.ker rho).FG := by
    rw [hrhoker]
    exact Ideal.FG.map (IsNoetherian.noetherian (RingHom.ker (algebraMap A' A))) _
  have : IsNoetherianRing B' :=
    noetherian_of_isAdicComplete_fg B' (RingHom.ker rho) hrhofg
      (IsAdicComplete.of_isNilpotent _ hrhonil)
      (isNoetherianRing_of_ringEquiv B
        (Ideal.quotientKerAlgEquivOfSurjective hrhosurj).symm.toRingEquiv)
  -- present `𝔟` as the image of an ideal of `B'`, namely of its preimage
  obtain ⟨b', hb'⟩ : ∃ b' : Ideal B', b'.map (algebraMap B' B) = b :=
    ⟨b.comap (algebraMap B' B), Ideal.map_comap_of_surjective _ hsurjP b⟩
  subst hb'
  have : IsScalarTower A' B' (AdicCompletion b' B') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra A (B ⊗[B'] AdicCompletion b' B') :=
    ((algebraMap B (B ⊗[B'] AdicCompletion b' B')).comp (algebraMap A B)).toAlgebra
  -- the two base changes of the completed lift agree, and `C' ⊗_{B'} B` is the completion
  obtain ⟨e1, -⟩ := exists_algEquiv_tensorBaseChange A' A B' B (AdicCompletion b' B')
    hsurjA hsurjP hkerP (fun _ => rfl)
  let e2 : (B ⊗[B'] AdicCompletion b' B') ≃ₐ[B']
      AdicCompletion (b'.map (algebraMap B' B)) B :=
    (Algebra.TensorProduct.comm B' B (AdicCompletion b' B')).trans
      (ofTensorProductAlgEquiv b' B)
  refine ⟨AdicCompletion b' B', inferInstance, inferInstance,
    Module.Flat.trans A' B' (AdicCompletion b' B'),
    ⟨AlgEquiv.ofRingEquiv (f := e1.toRingEquiv.trans e2.toRingEquiv) fun a => ?_⟩⟩
  -- the composite is `A`-linear: `algebraMap A B a` comes from `B'`, over which both are maps
  obtain ⟨x, hx⟩ := hsurjP (algebraMap A B a)
  rw [RingEquiv.trans_apply]
  show e2 (e1 (algebraMap A (A ⊗[A'] AdicCompletion b' B') a)) =
    algebraMap A (AdicCompletion (b'.map (algebraMap B' B)) B) a
  rw [e1.commutes a]
  have key : algebraMap A (B ⊗[B'] AdicCompletion b' B') a =
      algebraMap B' (B ⊗[B'] AdicCompletion b' B') x := by
    show algebraMap B (B ⊗[B'] AdicCompletion b' B') (algebraMap A B a) = _
    rw [← hx, ← IsScalarTower.algebraMap_apply B' B (B ⊗[B'] AdicCompletion b' B')]
  rw [key, e2.commutes x]
  show AdicCompletion.of _ B (algebraMap B' B x) =
    AdicCompletion.of _ B (algebraMap A B a)
  rw [hx]

/-! ### Stacks 0DZ3 -/

/-- **The second implication of Stacks 0DZ3.** A flat lift of the `𝔟`-adic completion of `B` to
`A'` gives one of `B`: a flat algebra lift of the completion is an `A'`-flat module lift over
the completed presentation `Q'`, and Stacks 0DZ2 transports that lift back to `P'`. -/
theorem hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion_at
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (h0DZ2 : FlatModuleLiftBaseChangeStatementAt.{u} A' A)
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h)) :
    HasFlatAlgebraLift A' A (AdicCompletion b B) → HasFlatAlgebraLift A' A B := by
  classical
  let : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A B)
  let : Algebra (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) :=
    (MvPolynomial.map (algebraMap A' A)).toAlgebra
  have hsurjP : Function.Surjective
      (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A)) :=
    MvPolynomial.map_surjective _ hsurjA
  have hkerP : RingHom.ker
      (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A)) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' (MvPolynomial (Fin n) A')) :=
    MvPolynomial.ker_map (algebraMap A' A)
  have : IsScalarTower A' (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) := by
    refine IsScalarTower.of_algebraMap_eq fun a' => ?_
    show MvPolynomial.C (algebraMap A' A a') =
      MvPolynomial.map (algebraMap A' A) (MvPolynomial.C a')
    rw [MvPolynomial.map_C]
  let : Algebra (MvPolynomial (Fin n) A) B := f.toRingHom.toAlgebra
  have : IsScalarTower A (MvPolynomial (Fin n) A) B :=
    IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  have hsurjB : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B) := hf
  let : Algebra (MvPolynomial (Fin n) A') B :=
    ((algebraMap (MvPolynomial (Fin n) A) B).comp
      (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A))).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A' (MvPolynomial (Fin n) A) B :=
    IsScalarTower.to₁₃₄ A' A (MvPolynomial (Fin n) A) B
  have : IsScalarTower A' (MvPolynomial (Fin n) A') B :=
    IsScalarTower.to₁₂₄ A' (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B
  have hsurjPB : Function.Surjective (algebraMap (MvPolynomial (Fin n) A') B) :=
    hsurjB.comp hsurjP
  have hfinP'B : Module.Finite (MvPolynomial (Fin n) A') B :=
    Module.Finite.of_surjective (Algebra.linearMap (MvPolynomial (Fin n) A') B) hsurjPB
  have hnoethB : IsNoetherianRing B :=
    isNoetherianRing_of_surjective (MvPolynomial (Fin n) A) B
      (algebraMap (MvPolynomial (Fin n) A) B) hsurjB
  set I' : Ideal (MvPolynomial (Fin n) A') :=
    Ideal.comap (algebraMap (MvPolynomial (Fin n) A') B) b with hI'def
  have hb : I'.map (algebraMap (MvPolynomial (Fin n) A') B) = b :=
    Ideal.map_comap_of_surjective _ hsurjPB b
  -- the completed presentation, written at the ideal `𝔟` itself
  obtain ⟨e, he⟩ : ∃ e : (((MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) A']
        AdicCompletion I' (MvPolynomial (Fin n) A')) ⊗[MvPolynomial (Fin n) A] B))
        ≃+* AdicCompletion b B,
      ∀ p : MvPolynomial (Fin n) A,
        e ((p ⊗ₜ[MvPolynomial (Fin n) A'] (1 : AdicCompletion I' (MvPolynomial (Fin n) A')))
            ⊗ₜ[MvPolynomial (Fin n) A] (1 : B)) =
          AdicCompletion.of b B (algebraMap (MvPolynomial (Fin n) A) B p) := by
    rw [← hb]
    exact exists_ringEquiv_tensorAdicCompletion A (MvPolynomial (Fin n) A')
      (MvPolynomial (Fin n) A) B I'
  -- the completion of `B` is Noetherian and complete along the extension of `𝔟`
  have hbfg : b.FG := IsNoetherian.noetherian b
  have hbquot : IsNoetherianRing (B ⧸ b) :=
    isNoetherianRing_of_surjective B (B ⧸ b) (Ideal.Quotient.mk b)
      Ideal.Quotient.mk_surjective
  have hCnoeth : IsNoetherianRing (AdicCompletion b B) :=
    (completion_noetherian B b hbquot hbfg).1
  have hCcomplete : IsAdicComplete (b.map (algebraMap B (AdicCompletion b B)))
      (AdicCompletion b B) := (completion_noetherian B b hbquot hbfg).2
  -- the base change of the polynomial presentation along `A' → A`
  have hePP : ∀ x : MvPolynomial (Fin n) A',
      MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A' A ((1 : A) ⊗ₜ[A'] x) =
        algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) x := by
    intro x
    rw [← MvPolynomial.algebraTensorAlgEquiv_symm_map (σ := Fin n) A' A x,
      AlgEquiv.apply_symm_apply]
    rfl
  -- the image of `𝔭'` in the completion of `B` lies in the ideal of completeness
  have hJc : ∀ g ∈ I',
      e (((algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) g)
          ⊗ₜ[MvPolynomial (Fin n) A'] (1 : AdicCompletion I' (MvPolynomial (Fin n) A')))
        ⊗ₜ[MvPolynomial (Fin n) A] (1 : B)) ∈
      b.map (algebraMap B (AdicCompletion b B)) := by
    intro g hg
    rw [he (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) g),
      ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B g]
    exact Ideal.mem_map_of_mem _ hg
  refine hasFlatAlgebraLift_of_adicCompletion_of_presentation_at A' A
    (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B (AdicCompletion b B) h0DZ2 hsurjA
    hnilA hsurjP hkerP hsurjB (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A' A) hePP I'
    (fun g hg => exists_flatModuleLift_localization_of_syntomic A' A
      (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B hsurjA hnilA hsurjP hkerP b hsyn
      g hg)
    (b.map (algebraMap B (AdicCompletion b B))) hCcomplete e (fun a => ?_) hJc
  show algebraMap A _ a = e (((algebraMap A (MvPolynomial (Fin n) A) a)
    ⊗ₜ[MvPolynomial (Fin n) A'] (1 : AdicCompletion I' (MvPolynomial (Fin n) A')))
      ⊗ₜ[MvPolynomial (Fin n) A] (1 : B))
  rw [he (algebraMap A (MvPolynomial (Fin n) A) a),
    ← IsScalarTower.algebraMap_apply A (MvPolynomial (Fin n) A) B]
  rfl

/-- **Stacks 0DZ3 with Stacks 0DZ2 taken only at the surjection `A' → A` in hand.** For a
surjection `A' → A` of Noetherian rings with nilpotent kernel and a finite type flat
`A`-algebra `B` with `A → B_h` syntomic for every `h` in an ideal `𝔟`, flat lifts of `B` to
`A'` exist exactly when flat lifts of the `𝔟`-adic completion of `B` do. -/
theorem hasFlatAlgebraLift_adicCompletion_iff_at
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (h0DZ2 : FlatModuleLiftBaseChangeStatementAt.{u} A' A)
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h)) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A (AdicCompletion b B) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  exact ⟨hasFlatAlgebraLift_adicCompletion_of_hasFlatAlgebraLift_of_isNoetherianRing A' A B
      hsurjA hnilA b,
    hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion_at A' A B h0DZ2 hsurjA hnilA b hsyn⟩

/-- **The first implication of Stacks 0DZ3**, with Stacks 0DZ2 taken only at the surjection
`A' → A` in hand. A flat lift of `B` to `A'` gives one of the `𝔟`-adic completion of `B`.

This is subsumed by
`Deformation.hasFlatAlgebraLift_adicCompletion_of_hasFlatAlgebraLift_of_isNoetherianRing`,
which proves the same implication outright and under fewer hypotheses; `h0DZ2` is not used for
it any more and is carried only because this is the form the equivalence's `mp` direction
takes. -/
theorem hasFlatAlgebraLift_adicCompletion_of_hasFlatAlgebraLift_at
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (h0DZ2 : FlatModuleLiftBaseChangeStatementAt.{u} A' A)
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h)) :
    HasFlatAlgebraLift A' A B → HasFlatAlgebraLift A' A (AdicCompletion b B) :=
  (hasFlatAlgebraLift_adicCompletion_iff_at A' A B h0DZ2 hsurjA hnilA b hsyn).mp

end Deformation

end
