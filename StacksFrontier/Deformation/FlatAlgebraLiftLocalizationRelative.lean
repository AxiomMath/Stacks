module

public import StacksFrontier.Deformation.FlatAlgebraLiftLocalization
public import StacksFrontier.Deformation.FlatModuleLiftBaseChangeAbstract
import all StacksFrontier.Deformation.FlatAlgebraLiftLocalization

/-!
# Stacks 0DZ7 with Stacks 0DZ2 taken only where it is used

`StacksFrontier.Deformation.FlatAlgebraLiftLocalization` proves Stacks 0DZ7 — flat lifts of a
finite type flat `A`-algebra `B` to `A'` exist exactly when flat lifts of a localization `S⁻¹B`
do — from the hypothesis `Deformation.FlatModuleLiftBaseChangeStatement`, Stacks 0DZ2 quantified
over every surjection `A' → A`. This file does for Stacks 0DZ7 what
`StacksFrontier.Deformation.FlatAlgebraLiftCompletionRelative` does for Stacks 0DZ3: it separates
the two implications, proves the forward one outright, relativizes the hypothesis of the
converse to the surjection in hand, and so discharges it at a square-zero kernel.

**The forward implication is unconditional.** A flat lift `B'` of `B` localizes: the preimage
`S'` of `S` in `B'` gives `(S')⁻¹B'`, which is `A'`-flat because a localization of a flat module
is flat, and whose reduction is `S⁻¹B` because localization commutes with the pushout square
`B = A ⊗_{A'} B'`. `Deformation.hasFlatAlgebraLift_localization_of_hasFlatAlgebraLift` assumes
nothing beyond surjectivity of `A' → A` — no Stacks 0DZ2, no syntomic hypothesis, no nilpotence,
no finite type, no flatness and no Noetherian hypothesis.

**The converse is relativized, and proved at a square-zero kernel.**
`Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_localization_at` carries
`Deformation.FlatModuleLiftBaseChangeStatementAt A' A` rather than the quantified statement, and
`Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_localization_of_sqZero` is that lemma with
the hypothesis discharged by
`Deformation.flatModuleLiftBaseChangeStatementAt_of_sq_zero`. This is not a repair of Stacks
0DZ7, which states a nilpotent kernel; it is the case a small extension of Artinian bases
supplies, which is what Stacks 0DZ9 consumes.

**Two disjoint special cases bound where a counterexample could live.** When `A' → A` admits a
ring section both sides of the biconditional are true outright
(`Deformation.hasFlatAlgebraLift_localization_iff_of_split`), and when `S` meets every prime
containing `𝔟` — in particular when `1 ∈ 𝔟` — the hypothesis `hSb` is vacuously satisfiable only
in degenerate ways (`Deformation.hasFlatAlgebraLift_localization_iff_of_forall_isPrime`,
`Deformation.hasFlatAlgebraLift_localization_iff_of_one_mem`). Neither says anything about the
comparison the tag is about, and neither carries a Stacks attribute.

**Why the hypothesis cannot be narrowed to the instance.** Assumed at every upper right corner
the consumption site admits, the instance of Stacks 0DZ2 already yields a flat lift of `B` to
`A'` with no hypothesis on `B` beyond its presentation — that is
`Deformation.exists_flatModuleLift_of_forall_flatModuleLiftBaseChangeInstance` and
`Deformation.hasFlatAlgebraLift_of_forall_flatModuleLiftBaseChangeInstance` here — so
discharging it would prove that flat deformations of presented algebras are never obstructed.
`Deformation.not_hasFlatAlgebraLift_of_localization_of_presentation` is the contrapositive form
in which that is recorded.

## Main results

* `Deformation.hasFlatAlgebraLift_localization_of_hasFlatAlgebraLift`: the forward implication
  of Stacks 0DZ7, unconditionally.
* `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_localization_at`: the converse, from
  Stacks 0DZ2 at the surjection in hand.
* `Deformation.hasFlatAlgebraLift_localization_iff_at`: Stacks 0DZ7 with Stacks 0DZ2 taken only
  at the surjection in hand.
* `Deformation.hasFlatAlgebraLift_localization_iff_of_sqZero` and
  `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_localization_of_sqZero`: the same at a
  square-zero kernel, with no hypothesis standing for Stacks 0DZ2.
* `Deformation.hasFlatAlgebraLift_of_split`,
  `Deformation.hasFlatAlgebraLift_localization_iff_of_split`: the split case.
* `Deformation.hasFlatAlgebraLift_of_forall_flatModuleLiftBaseChangeInstance`: what assuming the
  instance at every corner would prove.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 0DZ7](https://stacks.math.columbia.edu/tag/0DZ7)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Deformation

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ### The forward implication of Stacks 0DZ7, unconditionally -/

/-- **The forward implication of Stacks 0DZ7, with no hypothesis beyond surjectivity of
`A' → A`.** If `B` has a flat lift to `A'`, then so does every localization `S⁻¹B`.

The proof is a direct construction and uses none of the obstruction calculus: let `B'` be a flat
lift of `B`, let `ρ : B' → B` be its reduction — surjective because `A' → A` is — and let
`S' = ρ⁻¹(S)`. Then `C' = (S')⁻¹B'` is flat over `A'`, being a localization of `B'`, and its
base change to `A` is the localization of `B` at `ρ(S') = S`, hence is `C`. The identification
is read off as a pushout: `A ⊗_{A'} C'` is the pushout of `A' → C'` along `A' → A`, which
factors through `B'`, so it is also the pushout of `B' → C'` along `ρ`, and a pushout of a
localization is a localization.

None of the tag's remaining hypotheses is used: not the Noetherian hypotheses, not nilpotence of
the kernel, not finite type or flatness of `B`, and — crucially — neither the syntomic hypothesis
`hsyn` nor the condition `hSb` on `S`. They are needed only for the converse, which is where the
obstruction calculus and hence Stacks 0DZ2 enter.

This declaration deliberately carries **no** Stacks attribute: one implication of a
biconditional is not the tag. The 0DZ7 registration is on
`Deformation.hasFlatAlgebraLift_iff_hasFlatAlgebraLift_localization`, which does not carry
`h0DZ2` -- every published proof of 0DZ7 routes through Stacks 0DZ2, which is false as stated
(a Stacks erratum). The section note above the declaration gives the analysis.
What is proved outright is this half of the tag; the converse at a nilpotent kernel is
open. -/
theorem hasFlatAlgebraLift_localization_of_hasFlatAlgebraLift
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (S : Submonoid B) (C : Type u) [CommRing C] [Algebra B C] [IsLocalization S C]
    [Algebra A C] [IsScalarTower A B C] :
    HasFlatAlgebraLift A' A B → HasFlatAlgebraLift A' A C := by
  classical
  rintro ⟨B', _, _, hflatB', ⟨e⟩⟩
  let : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  -- the reduction of the lift, a surjection
  set rho : B' →ₐ[A'] B :=
    (e.restrictScalars A').toAlgHom.comp Algebra.TensorProduct.includeRight
  have hrhoapp : ∀ b' : B', rho b' = e ((1 : A) ⊗ₜ[A'] b') := fun _ => rfl
  have hrhosurj : Function.Surjective rho :=
    (e.restrictScalars A').surjective.comp (surjective_includeRight A' A B' hsurjA)
  let : Algebra B' B := rho.toRingHom.toAlgebra
  have : IsScalarTower A' B' B :=
    IsScalarTower.of_algebraMap_eq fun a' => (rho.commutes a').symm
  -- the localization of the lift at the preimage of `S`
  set S' : Submonoid B' := S.comap (rho : B' →+* B) with hS'def
  have hflatC' : Module.Flat A' (Localization S') := by
    have := hflatB'
    infer_instance
  -- `A ⊗_{A'} (S')⁻¹B'` as a `B`-algebra, through `B = A ⊗_{A'} B'`
  set sigma : B →ₐ[A] (A ⊗[A'] Localization S') :=
    (Algebra.TensorProduct.map (AlgHom.id A A)
      (IsScalarTower.toAlgHom A' B' (Localization S'))).comp
        (e.symm : B →ₐ[A] (A ⊗[A'] B')) with hsigmadef
  let : Algebra B (A ⊗[A'] Localization S') := sigma.toRingHom.toAlgebra
  have : IsScalarTower A B (A ⊗[A'] Localization S') :=
    IsScalarTower.of_algebraMap_eq fun a => (sigma.commutes a).symm
  let : Algebra B' (A ⊗[A'] Localization S') :=
    ((algebraMap (Localization S') (A ⊗[A'] Localization S')).comp
      (algebraMap B' (Localization S'))).toAlgebra
  have : IsScalarTower B' (Localization S') (A ⊗[A'] Localization S') :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower B' B (A ⊗[A'] Localization S') := by
    refine IsScalarTower.of_algebraMap_eq fun b' => ?_
    show (1 : A) ⊗ₜ[A'] (algebraMap B' (Localization S') b') =
      sigma (algebraMap B' B b')
    rw [hsigmadef]
    show (1 : A) ⊗ₜ[A'] (algebraMap B' (Localization S') b') =
      Algebra.TensorProduct.map (AlgHom.id A A)
        (IsScalarTower.toAlgHom A' B' (Localization S')) (e.symm (rho b'))
    rw [hrhoapp b', AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul]
    rfl
  have : IsScalarTower A' B (A ⊗[A'] Localization S') :=
    IsScalarTower.of_algebraMap_eq fun a' => by
      rw [IsScalarTower.algebraMap_apply A' A B a',
        ← IsScalarTower.algebraMap_apply A B (A ⊗[A'] Localization S'),
        ← IsScalarTower.algebraMap_apply A' A (A ⊗[A'] Localization S')]
  -- `B = A ⊗_{A'} B'` is a pushout square, and so is `A ⊗_{A'} (S')⁻¹B'`
  have hpoB : Algebra.IsPushout A' B' A B := by
    refine Algebra.IsPushout.of_equiv (R := A') (R' := B') (S := A)
      (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun b' => (hrhoapp b').symm) ?_
    exact RingHom.ext fun a => e.commutes a
  have hpo : Algebra.IsPushout B' B (Localization S') (A ⊗[A'] Localization S') :=
    ((Algebra.IsPushout.comp_iff A' B' A (S' := B) (T := Localization S')
      (T' := A ⊗[A'] Localization S')).mp inferInstance).symm
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid B S')
      (A ⊗[A'] Localization S') :=
    (Algebra.isLocalization_iff_isPushout S' (Localization S')).mpr hpo
  have hSS' : Algebra.algebraMapSubmonoid B S' = S := by
    rw [hS'def]
    exact Submonoid.map_comap_eq_of_surjective hrhosurj S
  rw [hSS'] at hloc
  have := hloc
  exact ⟨Localization S', inferInstance, inferInstance, hflatC',
    ⟨(IsLocalization.algEquiv S (A ⊗[A'] Localization S') C).restrictScalars A⟩⟩

/-! ### The presentation the converse feeds to Stacks 0DZ2 is smooth -/

/-! ### Stacks 0DZ7 for a split surjection, unconditionally -/

/-- **A flat algebra lift exists outright when the surjection `A' → A` splits.** The splitting
is carried by `[Algebra A A']` together with `[IsScalarTower A A' A]`, which says exactly that
`A → A' → A` is the identity, i.e. that `algebraMap A A'` is a ring section of
`algebraMap A' A`. Then every `A`-flat `A`-algebra `B` has a flat lift to `A'`, namely
`A' ⊗_A B` through that section.

Nothing else is assumed: not surjectivity of `algebraMap A' A`, not nilpotence of its kernel,
not finite type of `B`, and no Noetherian hypothesis. The lift is flat because flatness is
stable under base change, and its reduction is `A ⊗_{A'} (A' ⊗_A B) = A ⊗_A B = B`, the
cancellation being where the section is used.

**This is not a repair of Stacks 0DZ7, and is not offered as one.** It is a disjoint special
case: it makes *both* sides of the tag's biconditional true outright, so it says nothing about
the comparison the tag is about. What it is for is bounding where a counterexample to the open
converse could live. Every hypothesis of Stacks 0DZ2 and of Stacks 0DZ7 is satisfied by a split
base, so no counterexample to either can have one — in particular the base of the known
refutation of Stacks 0DZ2, `A' = NC[t]/t³` over `A = NC`, splits, and the force of that
refutation comes entirely from its `P'` being a non-trivial deformation of `P`, which a smooth
`P'` over a split base cannot be. See the implementation notes. -/
theorem hasFlatAlgebraLift_of_split (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A A'] [IsScalarTower A A' A] [Algebra A B] [Module.Flat A B] :
    HasFlatAlgebraLift A' A B :=
  ⟨A' ⊗[A] B, inferInstance, inferInstance, inferInstance,
    ⟨(Algebra.TensorProduct.cancelBaseChange A A' A A B).trans
      (Algebra.TensorProduct.lid A B)⟩⟩

/-- **Stacks 0DZ7 for a split surjection, unconditionally and at a nilpotent kernel.** For a
surjection `A' → A` admitting a ring section and a flat `A`-algebra `B`, flat lifts of `B` to
`A'` and of any localization `S⁻¹B` both exist, so the tag's biconditional holds.

The two sides are discharged separately by `Deformation.hasFlatAlgebraLift_of_split`, the
localization being `A`-flat as a localization of an `A`-flat algebra. Neither the syntomic
hypothesis `hsyn`, nor the condition `hSb` on `S`, nor finite type of `B`, nor any Noetherian
hypothesis is used. It carries no Stacks attribute: a biconditional both of whose sides are
unconditionally true is not evidence for the comparison the tag asserts, and the open converse
is the case of a base with no section. -/
theorem hasFlatAlgebraLift_localization_iff_of_split
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A A'] [IsScalarTower A A' A] [Algebra A B] [Module.Flat A B]
    (S : Submonoid B) (C : Type u) [CommRing C] [Algebra B C] [IsLocalization S C]
    [Algebra A C] [IsScalarTower A B C] :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A C := by
  have : Module.Flat B C := IsLocalization.flat C S
  have : Module.Flat A C := Module.Flat.trans A B C
  exact iff_of_true (hasFlatAlgebraLift_of_split A' A B) (hasFlatAlgebraLift_of_split A' A C)

/-! ### Stacks 0DZ7 where `V(𝔟)` is everything, and what that closes off -/

/-- **Stacks 0DZ7 is trivial when every prime of `B` contains `𝔟`**, that is when `V(𝔟)` is all
of `Spec B` — equivalently when `𝔟 ≤ nilradical B`. The tag's condition `hSb` says that no prime
containing `𝔟` meets `S`; if every prime contains `𝔟`, that makes every element of `S` a unit, so
`algebraMap B C` is an isomorphism (`IsLocalization.atUnits`) and the two sides of the
biconditional are the same statement about the same algebra.

Nothing is assumed about `A' → A` — not surjectivity, not nilpotence of its kernel — and nothing
about `B` beyond its `A`-algebra structure.

**This is not a repair of the tag** and, like
`Deformation.hasFlatAlgebraLift_localization_iff_of_split`, it carries no attribute: the
hypothesis collapses `S⁻¹B` onto `B`, so the comparison the tag asserts is not being tested. Its
use is to bound where the open converse can have content, and in particular to close off one
route to it. The module obstruction of the dévissage lives in
`Ext²_{P_j}(M_j, M_j ⊗ K_j P_j)`, which is supported inside `Supp_{P_j} M_j`, the image of
`Spec B`; so asking — as route 5 of the implementation notes does — that its support lie inside
`V(J')` is, through that bound and nothing else, asking exactly that `V(𝔟) = Spec B`. This lemma
says that wherever that is so, the tag has nothing left to assert. -/
theorem hasFlatAlgebraLift_localization_iff_of_forall_isPrime
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B]
    (S : Submonoid B) (C : Type u) [CommRing C] [Algebra B C] [IsLocalization S C]
    [Algebra A C] [IsScalarTower A B C]
    (b : Ideal B)
    (hbq : ∀ q : Ideal B, q.IsPrime → b ≤ q)
    (hSb : ∀ q : Ideal B, q.IsPrime → b ≤ q → ∀ s ∈ S, s ∉ q) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A C := by
  have hunits : S ≤ IsUnit.submonoid B := by
    intro s hs
    rw [IsUnit.mem_submonoid_iff]
    by_contra hns
    have hne : Ideal.span ({s} : Set B) ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact hns
    obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ hne
    have : m.IsPrime := hmax.isPrime
    exact hSb m inferInstance (hbq m inferInstance) s hs
      (hle (Ideal.mem_span_singleton_self s))
  exact hasFlatAlgebraLift_congr
    ((IsLocalization.atUnits B S hunits : B ≃ₐ[B] C).restrictScalars A)

/-! ### Stacks 0DZ7 where `V(𝔟)` is empty, and what that closes off -/

/-- **Stacks 0DZ7 holds outright when `1 ∈ 𝔟`**, that is when `V(𝔟)` is empty, so that `hsyn`
asserts syntomy of `A → B` itself. Then `B` has a flat lift to `A'` by Stacks 07M8, through
`Deformation.hasFlatAlgebraLift_of_syntomic`, and `S⁻¹B` has one by the unconditional forward
implication; both sides of the tag's biconditional are true.

Only surjectivity of `A' → A` is used — not nilpotence of its kernel, not `hSb`, not finite type
of `B`, not flatness of `B` over `A` (which syntomy supplies) and no Noetherian hypothesis.

**This is not a repair of the tag** and carries no attribute, for the reason that
`Deformation.hasFlatAlgebraLift_localization_iff_of_split` and
`Deformation.hasFlatAlgebraLift_localization_iff_of_forall_isPrime` carry none: both sides hold,
so the comparison the tag asserts is not being tested. Its use is to bound the open converse
from the opposite end to `Deformation.hasFlatAlgebraLift_localization_iff_of_forall_isPrime`,
which bounds it at `V(𝔟) = Spec B`. When `𝔟 = ⊤` the condition `hSb` is vacuous, no prime
containing `⊤` existing, so the tag's hypotheses put no condition on `S` whatever and the region
reads as the easiest place to look for a counterexample. It is empty. In particular the witness
recorded in route 5 of the implementation notes — `B = A[x, y]/(x², y²)` over a field `A`, a
global complete intersection, so `𝔟 = ⊤` is admissible — refutes that route's *support*
hypothesis and cannot be turned against the tag, and this lemma is the reason. -/
theorem hasFlatAlgebraLift_localization_iff_of_one_mem
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (S : Submonoid B) (C : Type u) [CommRing C] [Algebra B C] [IsLocalization S C]
    [Algebra A C] [IsScalarTower A B C]
    (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (hone : (1 : B) ∈ b) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A C := by
  have : Algebra.Syntomic A (Localization.Away (1 : B)) := hsyn 1 hone
  have hsynB : Algebra.Syntomic A B :=
    RingHom.syntomic_of_algEquiv
      ((IsLocalization.atOne B (Localization.Away (1 : B))).restrictScalars A).symm
  have hB : HasFlatAlgebraLift A' A B := hasFlatAlgebraLift_of_syntomic A' A B hsurjA hsynB
  exact iff_of_true hB
    (hasFlatAlgebraLift_localization_of_hasFlatAlgebraLift A' A B hsurjA S C hB)

/-! ### Stacks 0DZ7 -/

/-- `A'` acts on `P ⊗_{P'} Q'` through `Q'` as it does through `P`. -/
private theorem isScalarTower_tensorProduct_right
    (A' P' P Q' : Type*) [CommRing A'] [CommRing P'] [CommRing P] [CommRing Q']
    [Algebra A' P'] [Algebra A' P] [Algebra A' Q'] [Algebra P' P] [Algebra P' Q']
    [IsScalarTower A' P' P] [IsScalarTower A' P' Q'] :
    IsScalarTower A' Q' (P ⊗[P'] Q') := by
  refine IsScalarTower.of_algebraMap_eq fun a' => ?_
  have e1 : algebraMap A' (P ⊗[P'] Q') a' = (algebraMap A' P a') ⊗ₜ[P'] (1 : Q') := rfl
  have e2 : algebraMap Q' (P ⊗[P'] Q') (algebraMap A' Q' a') =
      (1 : P) ⊗ₜ[P'] (algebraMap A' Q' a') := rfl
  rw [e1, e2, IsScalarTower.algebraMap_apply A' P' P, IsScalarTower.algebraMap_apply A' P' Q',
    Algebra.algebraMap_eq_smul_one (R := P') (A := P),
    Algebra.algebraMap_eq_smul_one (R := P') (A := Q'), TensorProduct.smul_tmul]

/-- The kernel of `Q' → P ⊗_{P'} Q'` is the extension of `ker (A' → A)` to `Q'`. -/
private theorem ker_algebraMap_tensorProduct_right
    (A' A P' P Q' : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra P' P] [Algebra P' Q']
    [IsScalarTower A' P' Q'] (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P')) :
    RingHom.ker (algebraMap Q' (P ⊗[P'] Q')) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' Q') := by
  have h := ker_includeRight P' P Q' hsurjP
  rw [hkerP, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h
  exact h

/-- In the localized presentation `(P ⊗_{P'} Q') ⊗_P B ≅ C`, `A` acts on `C` through `B`. -/
private theorem algebraMap_eq_tensorLocalization
    (A P' P B Q' C : Type*) [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing Q']
    [CommRing C] [Algebra P' P] [Algebra P' Q'] [Algebra A P] [Algebra A B] [Algebra P B]
    [Algebra A C] [Algebra B C] [IsScalarTower A P B] [IsScalarTower A B C]
    (e : ((P ⊗[P'] Q') ⊗[P] B) ≃+* C)
    (he : ∀ p : P, e ((p ⊗ₜ[P'] (1 : Q')) ⊗ₜ[P] (1 : B)) =
      algebraMap B C (algebraMap P B p)) (a : A) :
    algebraMap A C a = e ((algebraMap A (P ⊗[P'] Q') a) ⊗ₜ[P] (1 : B)) := by
  change algebraMap A C a = e (((algebraMap A P a) ⊗ₜ[P'] (1 : Q')) ⊗ₜ[P] (1 : B))
  rw [he (algebraMap A P a), ← IsScalarTower.algebraMap_apply A P B]
  exact IsScalarTower.algebraMap_apply A B C a

/-- Elements of `T' ⊆ P'` are units in `C`, so a formally smooth presentation `P'` of a flat lift
`C'` of `C` lifts along `Q' = T'⁻¹P'`. -/
private theorem exists_algHom_of_tensorLocalization
    (A' A P' P B Q' C C' : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing P]
    [CommRing B] [CommRing Q'] [CommRing C] [CommRing C'] (T' : Submonoid P')
    [Algebra A' A] [Algebra A' P'] [Algebra A' C] [Algebra A' C'] [Algebra A C] [Algebra P' P]
    [Algebra P' B] [Algebra P B] [IsScalarTower P' P B] [Algebra B C] [Algebra P' C]
    [Algebra P' Q'] [IsLocalization T' Q'] [IsLocalization (Algebra.algebraMapSubmonoid B T') C]
    [Algebra A' Q'] [IsScalarTower A' P' Q'] [Algebra Q' C] [IsScalarTower P' Q' C]
    [IsScalarTower A' A C] [IsScalarTower A' P' C] [Algebra.FormallySmooth A' P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (e : ((P ⊗[P'] Q') ⊗[P] B) ≃+* C)
    (he : ∀ p : P, e ((p ⊗ₜ[P'] (1 : Q')) ⊗ₜ[P] (1 : B)) =
      algebraMap B C (algebraMap P B p))
    (hQe : ∀ x : Q', algebraMap Q' C x = e (((1 : P) ⊗ₜ[P'] x) ⊗ₜ[P] (1 : B)))
    (eCa : (A ⊗[A'] C') ≃ₐ[A] C) :
    ∃ g : Q' →ₐ[A'] C', ∀ x : Q', eCa (1 ⊗ₜ[A'] (g x)) = algebraMap Q' C x := by
  refine exists_algHom_localization_of_algebraLift A' A P' C C' hsurjA hnilA T' Q'
    (fun t ht => ?_) eCa
  have hval : algebraMap P' C t = algebraMap B C (algebraMap P' B t) := by
    rw [IsScalarTower.algebraMap_apply P' Q' C, hQe,
      Algebra.algebraMap_eq_smul_one (R := P') (A := Q'), ← TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one (R := P') (A := P), he (algebraMap P' P t),
      ← IsScalarTower.algebraMap_apply P' P B]
  rw [hval]
  exact IsLocalization.map_units C
    ⟨algebraMap P' B t, Algebra.mem_algebraMapSubmonoid_of_mem ⟨t, ht⟩⟩

/-- Elements of the preimage of `S` under a surjection `φ : P' → B` are units modulo the preimage
of `𝔟`, when `S` meets no prime containing `𝔟`. -/
private theorem isUnit_quotient_mk_comap_of_forall_isPrime
    {P' B : Type*} [CommRing P'] [CommRing B] (φ : P' →+* B) (hφ : Function.Surjective φ)
    (b : Ideal B) (S : Submonoid B) (hSb : ∀ q : Ideal B, q.IsPrime → b ≤ q → ∀ s ∈ S, s ∉ q)
    (t : P') (ht : t ∈ S.comap φ) : IsUnit (Ideal.Quotient.mk (b.comap φ) t) := by
  refine isUnit_quotient_mk_of_forall_isPrime _ t (fun q hq hIq htq => ?_)
  have hkerle : RingHom.ker φ ≤ q := by
    refine le_trans (fun x hx => ?_) hIq
    rw [Ideal.mem_comap, RingHom.mem_ker.mp hx]
    exact b.zero_mem
  exact hSb (q.map φ) (Ideal.map_isPrime_of_surjective hφ hkerle)
    ((Ideal.map_comap_of_surjective φ hφ b).ge.trans (Ideal.map_mono hIq)) _ ht
    (Ideal.mem_map_of_mem _ htq)

/-- **The converse of Stacks 0DZ7, with Stacks 0DZ2 taken only at the surjection `A' → A` in
hand.** For a surjection `A' → A` of Noetherian rings with nilpotent kernel and a finite type
flat `A`-algebra `B` with `A → B_h` syntomic for every `h` in an ideal `𝔟`, and a multiplicative
subset `S ⊆ B` meeting no prime of `B` containing `𝔟`: if `S⁻¹B` has a flat lift to `A'`, so
does `B`.

This is the half of Stacks 0DZ7 that needs the obstruction calculus; the forward implication is
`Deformation.hasFlatAlgebraLift_localization_of_hasFlatAlgebraLift` and needs none of it. The
proof applies Stacks 0DZ2 only at the surjection it is given, so it is the relativized statement
`Deformation.FlatModuleLiftBaseChangeStatementAt` that is consumed, and it is consumed at one
single instance of its data: `P' = A'[x_1, …, x_n]`, `P = A[x_1, …, x_n]`, `Q'` the localization
of `P'` at the preimage of `S`, `M = B`. That `P'` is smooth over `A'`
(`AlgebraicGeometry.smooth_mvPolynomial`), while the `P'` that refutes Stacks 0DZ2 is not; so this
declaration, and not the general statement, is where a smooth form of Stacks 0DZ2 can be
substituted. See the module's implementation notes. -/
theorem hasFlatAlgebraLift_of_hasFlatAlgebraLift_localization_at
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (h0DZ2 : FlatModuleLiftBaseChangeStatementAt.{u} A' A)
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B]
    (S : Submonoid B) (C : Type u) [CommRing C] [Algebra B C] [IsLocalization S C]
    [Algebra A C] [IsScalarTower A B C]
    (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (hSb : ∀ q : Ideal B, q.IsPrime → b ≤ q → ∀ s ∈ S, s ∉ q) :
    HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B := by
  classical
  let : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A' C := ((algebraMap A C).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A C := IsScalarTower.of_algebraMap_eq' rfl
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
  have hnoethB : IsNoetherianRing B :=
    isNoetherianRing_of_surjective (MvPolynomial (Fin n) A) B
      (algebraMap (MvPolynomial (Fin n) A) B) hsurjB
  -- the preimages of `𝔟` and of `S` in the polynomial algebra over `A'`
  set I' : Ideal (MvPolynomial (Fin n) A') :=
    Ideal.comap (algebraMap (MvPolynomial (Fin n) A') B) b
  set T' : Submonoid (MvPolynomial (Fin n) A') :=
    S.comap (algebraMap (MvPolynomial (Fin n) A') B)
  have hT' : Algebra.algebraMapSubmonoid B T' = S :=
    Submonoid.map_comap_eq_of_surjective hsurjPB S
  have : IsLocalization (Algebra.algebraMapSubmonoid B T') C := by
    rw [hT']
    infer_instance
  have : Module.Flat (MvPolynomial (Fin n) A') (Localization T') :=
    IsLocalization.flat (Localization T') T'
  -- every element of `T'` is invertible modulo `𝔭'`, so `P'/𝔭' = Q'/𝔭'Q'`
  have hunitI := isUnit_quotient_mk_comap_of_forall_isPrime
    (algebraMap (MvPolynomial (Fin n) A') B) hsurjPB b S hSb
  have hquot : Function.Bijective (Ideal.quotientMap
      (I'.map (algebraMap (MvPolynomial (Fin n) A') (Localization T')))
      (algebraMap (MvPolynomial (Fin n) A') (Localization T')) Ideal.le_comap_map) :=
    bijective_quotientMap_localization T' (Localization T') I' hunitI
  -- the presentation of the localization of `B`
  obtain ⟨e, he⟩ := exists_ringEquiv_tensorLocalization (MvPolynomial (Fin n) A')
    (MvPolynomial (Fin n) A) B T' (Localization T') C
  have hAe := algebraMap_eq_tensorLocalization A (MvPolynomial (Fin n) A')
    (MvPolynomial (Fin n) A) B (Localization T') C e he
  intro h
  -- the algebra structures on `C` over the localized presentation
  let : Algebra (MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) A'] Localization T') C :=
    (e.toRingHom.comp (algebraMap
      (MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) A'] Localization T')
      ((MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) A'] Localization T')
        ⊗[MvPolynomial (Fin n) A] B))).toAlgebra
  let : Algebra (Localization T') C :=
    ((algebraMap (MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) A'] Localization T') C).comp
      (algebraMap (Localization T')
        (MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) A'] Localization T'))).toAlgebra
  let : Algebra (MvPolynomial (Fin n) A') C :=
    ((algebraMap (Localization T') C).comp
      (algebraMap (MvPolynomial (Fin n) A') (Localization T'))).toAlgebra
  have := isScalarTower_tensorProduct_right A' (MvPolynomial (Fin n) A')
    (MvPolynomial (Fin n) A) (Localization T')
  have : IsScalarTower (Localization T')
      (MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) A'] Localization T') C :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A
      (MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) A'] Localization T') C :=
    IsScalarTower.of_algebraMap_eq hAe
  have : IsScalarTower A'
      (MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) A'] Localization T') C :=
    IsScalarTower.to₁₃₄ A' A
      (MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) A'] Localization T') C
  have : IsScalarTower A' (Localization T') C :=
    IsScalarTower.to₁₂₄ A' (Localization T')
      (MvPolynomial (Fin n) A ⊗[MvPolynomial (Fin n) A'] Localization T') C
  have : IsScalarTower (MvPolynomial (Fin n) A') (Localization T') C :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A' (MvPolynomial (Fin n) A') C :=
    IsScalarTower.to₁₂₄ A' (MvPolynomial (Fin n) A') (Localization T') C
  -- the base change of the polynomial presentation along `A' → A`
  have hePP : ∀ x : MvPolynomial (Fin n) A',
      MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A' A ((1 : A) ⊗ₜ[A'] x) =
        algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) x := by
    intro x
    rw [← MvPolynomial.algebraTensorAlgEquiv_symm_map (σ := Fin n) A' A x,
      AlgEquiv.apply_symm_apply]
    rfl
  have hloc : ∀ g ∈ I',
      let : Algebra (Localization.Away g)
          (Localization.Away (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) g)) :=
        (Localization.awayMap
          (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A)) g).toAlgebra
      ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
        (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
        Module.Flat A' L ∧ Nonempty
          ((Localization.Away
              (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) g)
                ⊗[Localization.Away g] L)
            ≃ₗ[Localization.Away
              (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) g)]
              (Localization.Away
                (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) g)
                  ⊗[MvPolynomial (Fin n) A] B)) :=
    fun g hg => exists_flatModuleLift_localization_of_syntomic A' A (MvPolynomial (Fin n) A')
      (MvPolynomial (Fin n) A) B hsurjA hnilA hsurjP hkerP b hsyn g hg
  refine hasFlatAlgebraLift_of_baseChange_of_presentation_at A' A
    (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B (Localization T') C
    (flatModuleLiftBaseChangeInstance_of_statementAt A' A (MvPolynomial (Fin n) A')
      (MvPolynomial (Fin n) A) B (Localization T') h0DZ2 hsurjA hnilA hsurjP hkerP hsurjB I'
      hquot hloc)
    hsurjA hnilA
    hsurjP hkerP hsurjB (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A' A) hePP
    e hAe (fun _ => rfl) (fun C' _ _ eCa => ?_) h
  exact exists_algHom_of_tensorLocalization A' A (MvPolynomial (Fin n) A')
    (MvPolynomial (Fin n) A) B (Localization T') C C' T' hsurjA hnilA e he (fun _ => rfl) eCa

/-- **Stacks 0DZ7 with Stacks 0DZ2 taken only at the surjection `A' → A` in hand.** For a
surjection `A' → A` of Noetherian rings with nilpotent kernel and a
finite type flat `A`-algebra `B` with `A → B_h` syntomic for every `h` in an ideal `𝔟`, and a
multiplicative subset `S ⊆ B` meeting no prime of `B` containing `𝔟`, flat lifts of `B` to `A'`
exist exactly when flat lifts of `S⁻¹B` do.

Only the converse consumes `h0DZ2`, and it consumes the relativized statement
`Deformation.FlatModuleLiftBaseChangeStatementAt`, because it applies Stacks 0DZ2 only at the
surjection the lemma is given. The forward implication is
`Deformation.hasFlatAlgebraLift_localization_of_hasFlatAlgebraLift`, which assumes nothing
beyond surjectivity of `A' → A`. -/
theorem hasFlatAlgebraLift_localization_iff_at
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (h0DZ2 : FlatModuleLiftBaseChangeStatementAt.{u} A' A)
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B]
    (S : Submonoid B) (C : Type u) [CommRing C] [Algebra B C] [IsLocalization S C]
    [Algebra A C] [IsScalarTower A B C]
    (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (hSb : ∀ q : Ideal B, q.IsPrime → b ≤ q → ∀ s ∈ S, s ∉ q) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A C :=
  ⟨hasFlatAlgebraLift_localization_of_hasFlatAlgebraLift A' A B hsurjA S C,
    hasFlatAlgebraLift_of_hasFlatAlgebraLift_localization_at A' A B h0DZ2 hsurjA hnilA S C b
      hsyn hSb⟩

/-! ### What discharging the instance of Stacks 0DZ2 at its consumption site would prove -/

/-- **The instance of Stacks 0DZ2, taken at the hypotheses of its consumption site, asserts
outright the lift it is meant to compare.** The right clause of
`Deformation.FlatModuleLiftBaseChangeInstance` is free when `Q'` is the zero ring: the
comparison ring `P ⊗_{P'} Q'` is then zero as well, every module over it is zero, and `N' = Q'`
is an `A'`-flat `Q'`-module whose base change is linearly equivalent to that of `B` for want of
anything to tell two zero modules apart. So the instance's `mpr` hands back its left clause —
that `B` has an `A'`-flat `P'`-module lift — with nothing whatever assumed about `B`.

The hypothesis here is not the instance at arbitrary data but the instance at every upper right
corner the two assemblies of Stacks 0DZ3 admit, which is what a proof of the instance *at their
hypotheses* would supply: `Deformation.hasFlatAlgebraLift_imp_baseChange_of_presentation_at`
and `Deformation.hasFlatAlgebraLift_of_baseChange_of_presentation_at` ask of `Q'` exactly that
it be a Noetherian `P'`-algebra, flat over `P'`, and an `A'`-algebra over `P'`. The witness
`P' ⧸ ⊤` satisfies all four and the proof below discharges them, so no hypothesis of those
assemblies rules this corner out. The smoothness of `P'` they also carry is untouched by the
specialization, as is the surjectivity of `P → B`. -/
theorem exists_flatModuleLift_of_forall_flatModuleLiftBaseChangeInstance
    (A' P' P B : Type u) [CommRing A'] [CommRing P'] [CommRing P] [CommRing B]
    [IsNoetherianRing P'] [Algebra A' P'] [Algebra P' P] [Algebra P B]
    (h : ∀ (Q' : Type u) (_ : CommRing Q') (_ : IsNoetherianRing Q') (_ : Algebra A' Q')
      (_ : Algebra P' Q') (_ : IsScalarTower A' P' Q') (_ : Module.Flat P' Q'),
      FlatModuleLiftBaseChangeInstance.{u} A' P' P Q' B) :
    ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
      (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
      Nonempty ((P ⊗[P'] M') ≃ₗ[P] B) := by
  have hsub : Subsingleton (P' ⧸ (⊤ : Ideal P')) := Ideal.Quotient.subsingleton_iff.mpr rfl
  have hnoeth : IsNoetherianRing (P' ⧸ (⊤ : Ideal P')) :=
    isNoetherianRing_of_surjective P' (P' ⧸ (⊤ : Ideal P'))
      (Ideal.Quotient.mk (⊤ : Ideal P')) Ideal.Quotient.mk_surjective
  have htow : IsScalarTower A' P' (P' ⧸ (⊤ : Ideal P')) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- a subsingleton module is a retract of the ring, hence flat over it
  have hflatP : Module.Flat P' (P' ⧸ (⊤ : Ideal P')) :=
    Module.Flat.of_retract (M := P') 0 0 (LinearMap.ext fun _ => Subsingleton.elim _ _)
  have hflatA : Module.Flat A' (P' ⧸ (⊤ : Ideal P')) :=
    Module.Flat.of_retract (M := A') 0 0 (LinearMap.ext fun _ => Subsingleton.elim _ _)
  refine (h (P' ⧸ (⊤ : Ideal P')) inferInstance hnoeth inferInstance inferInstance htow
    hflatP).mpr ?_
  -- the comparison ring is zero, so both modules in the right clause are zero
  have hzero : Subsingleton (P ⊗[P'] (P' ⧸ (⊤ : Ideal P'))) :=
    Module.subsingleton (P' ⧸ (⊤ : Ideal P')) _
  have h1 : Subsingleton ((P ⊗[P'] (P' ⧸ (⊤ : Ideal P'))) ⊗[P' ⧸ (⊤ : Ideal P')]
      (P' ⧸ (⊤ : Ideal P'))) :=
    Module.subsingleton (P ⊗[P'] (P' ⧸ (⊤ : Ideal P'))) _
  have h2 : Subsingleton ((P ⊗[P'] (P' ⧸ (⊤ : Ideal P'))) ⊗[P] B) :=
    Module.subsingleton (P ⊗[P'] (P' ⧸ (⊤ : Ideal P'))) _
  exact ⟨P' ⧸ (⊤ : Ideal P'), inferInstance, inferInstance, inferInstance, inferInstance,
    hflatA, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩

/-- **Discharging the instance of Stacks 0DZ2 at the hypotheses of its consumption site would
prove that every presented flat algebra lifts, which is strictly stronger than Stacks 0DZ7.**
Along a formally smooth presentation an `A'`-flat `P'`-module lift of `B` *is* a flat algebra
lift of `B` (`Deformation.hasFlatAlgebraLift_iff_exists_flatModuleLift_of_formallySmooth`), so
the specialization of the previous theorem to a zero upper right corner turns the instance into
`Deformation.HasFlatAlgebraLift A' A B`, with no hypothesis on `B` beyond its presentation.

Both sides of Stacks 0DZ7 then hold outright — the flat lift of `B` localizes, by
`Deformation.hasFlatAlgebraLift_localization_of_hasFlatAlgebraLift` — so the tag would follow,
but from a statement that settles the lifting problem itself rather than the comparison the tag
asserts. That is the precise sense in which the instance cannot be discharged at its
consumption site: a proof of it there is a proof that flat deformations of presented algebras
are never obstructed, and the converse of Stacks 0DZ7 would be a corollary of something far
stronger than itself. The implication runs the other way too, the forward half of the instance
being free base change along `P' → Q'`; that half is
`Deformation.exists_flatModuleLift_baseChange_of_flat`, which is not in this module's import
closure, and the converse implication is not proved here.

What this does *not* say is that the instance is false at the data the converse supplies. It
says that at the site's hypotheses the instance is a statement about one of its clauses rather
than about the comparison, so the hypothesis to narrow is
`Deformation.FlatModuleLiftBaseChangeStatementAt` — where the ideal `J'`, the identification
`P'/J' = Q'/J'Q'` and the local liftability are present — and not the instance that
`Deformation.flatModuleLiftBaseChangeInstance_of_statementAt` produces from it. -/
theorem hasFlatAlgebraLift_of_forall_flatModuleLiftBaseChangeInstance
    (A' A P' P B : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B]
    [IsNoetherianRing P']
    [Algebra A' A] [Algebra A' P'] [Algebra A' B]
    [Algebra A P] [Algebra A B] [Algebra P' P] [Algebra P' B] [Algebra P B]
    [IsScalarTower A' A B] [IsScalarTower A' P' B] [IsScalarTower A P B]
    [IsScalarTower P' P B] [Algebra.FormallySmooth A' P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (ePP : (A ⊗[A'] P') ≃ₐ[A] P)
    (hePP : ∀ x : P', ePP (1 ⊗ₜ[A'] x) = algebraMap P' P x)
    (h : ∀ (Q' : Type u) (_ : CommRing Q') (_ : IsNoetherianRing Q') (_ : Algebra A' Q')
      (_ : Algebra P' Q') (_ : IsScalarTower A' P' Q') (_ : Module.Flat P' Q'),
      FlatModuleLiftBaseChangeInstance.{u} A' P' P Q' B) :
    HasFlatAlgebraLift A' A B :=
  (hasFlatAlgebraLift_iff_exists_flatModuleLift_of_formallySmooth hsurjA hnilA hsurjP hkerP
      hsurjB ePP hePP).mpr
    (exists_flatModuleLift_of_forall_flatModuleLiftBaseChangeInstance A' P' P B h)

/-! ### What a counterexample at the presentation the converse builds would settle -/

/-- **A counterexample to Stacks 0DZ2 at a presentation refutes the converse of Stacks 0DZ7 at
that presentation.** Let `A' → A` be a surjection with nilpotent kernel, let `P' → P` be a
surjection over it with kernel `ker(A' → A) · P'` and `P'` formally smooth over `A'`, let
`P → B` be a surjection and let `C` present the base change `(P ⊗_{P'} Q') ⊗_P B`. If the base
change of `B` has an `A'`-flat `Q'`-module lift and `B` has **no** `A'`-flat `P'`-module lift,
then flat lifts of `C` to `A'` do not give flat lifts of `B`.

The two hypotheses `hQlift` and `hPnolift` are the right-hand clause of
`Deformation.FlatModuleLiftBaseChangeInstance A' P' P Q' B` and the negation of its left-hand
clause; so together they are exactly what refuting Stacks 0DZ2 at this square means, and they
are stated as separate hypotheses rather than as `¬ FlatModuleLiftBaseChangeInstance` so that a
witness module supplies them directly.

This is the transport that makes such a witness bite on Stacks 0DZ7: its conclusion is the
negation of the implication that
`Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_localization_at` proves from `h0DZ2`, at
the presentation that proof builds. Both clauses of the instance are algebra-lifting statements
in disguise and that is the whole proof: a flat algebra lift of `B` yields the left clause by
`Deformation.exists_flatModuleLift_of_hasFlatAlgebraLift`, which is where
`Algebra.FormallySmooth A' P'` is spent, and the right clause yields `HasFlatAlgebraLift A' A C`
by Nakayama over the base-changed presentation `Q' → P ⊗_{P'} Q' → C`, which is
`Deformation.hasFlatAlgebraLift_of_exists_flatModuleLift`. So the assumed implication closes the
loop from `hQlift` back to the left clause, contradicting `hPnolift`.

What this assumes is strictly less than what the positive direction assumes: no Noetherian
hypothesis, no flatness of `P'` or of `Q'` over anything, no ideal `J'`, no identification
`P'/J' = Q'/J'Q'` and no local liftability. Those are hypotheses of Stacks 0DZ2 that a
counterexample has to *satisfy*, not hypotheses this transport needs; a witness which satisfies
them in addition refutes `Deformation.FlatModuleLiftBaseChangeStatementSmooth` of
`StacksFrontier.Deformation.FlatModuleLiftSmoothBaseChange` — the source's statement at a smooth
`P'`, not stated in this library.

The conclusion is about the implication at one presentation and does not by itself refute the
tag: Stacks 0DZ7 puts the syntomic hypothesis `hsyn` and the condition `hSb` on its data, and a
witness must satisfy those too for the contradiction to reach
`Deformation.hasFlatAlgebraLift_localization_iff_at`. What
`Deformation.not_hasFlatAlgebraLift_of_localization_of_presentation` adds is that for `Q'` a
localization of `P'` the presentation `e` of the base change need not be supplied either: it is
read off `C` being the corresponding localization of `B`. -/
theorem not_hasFlatAlgebraLift_of_baseChange_of_presentation_at
    (A' A P' P B Q' C : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing Q']
    [CommRing C]
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B] [Algebra A' Q']
    [Algebra A P] [Algebra A B] [Algebra P' P] [Algebra P' B] [Algebra P B] [Algebra P' Q']
    [Algebra A' C] [Algebra A C]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [IsScalarTower A' P' Q'] [IsScalarTower A' A C]
    [Algebra.FormallySmooth A' P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (e : (((P ⊗[P'] Q') ⊗[P] B)) ≃+* C)
    (hAe : ∀ a : A, algebraMap A C a =
      e ((algebraMap A (P ⊗[P'] Q') a) ⊗ₜ[P] (1 : B)))
    (hQlift : ∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
      (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
      Nonempty (((P ⊗[P'] Q') ⊗[Q'] N') ≃ₗ[P ⊗[P'] Q'] ((P ⊗[P'] Q') ⊗[P] B)))
    (hPnolift : ¬ ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
      (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
      Nonempty ((P ⊗[P'] M') ≃ₗ[P] B)) :
    ¬ (HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B) := by
  intro himp
  have hsurjQ : Function.Surjective (algebraMap Q' (P ⊗[P'] Q')) :=
    surjective_includeRight P' P Q' hsurjP
  have hkerQ := ker_algebraMap_tensorProduct_right A' A P' P Q' hsurjP hkerP
  have hnilQ : IsNilpotent (RingHom.ker (algebraMap Q' (P ⊗[P'] Q'))) := by
    rw [hkerQ]
    exact isNilpotent_ideal_map hnilA _
  -- the scalar tower over the upper left corner that is not canonical
  have := isScalarTower_tensorProduct_right A' P' P Q'
  -- the comparison of the two base changes of `Q'`
  obtain ⟨eQQ, heQQ⟩ := exists_algEquiv_tensorBaseChange A' A P' P Q' hsurjA hsurjP hkerP
    (fun a => IsScalarTower.algebraMap_apply A P (P ⊗[P'] Q') a)
  -- the presentation of `C` over `Q = P ⊗_{P'} Q'`
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
  obtain ⟨N', _, _, _, _, hflatN', ⟨eN⟩⟩ := hQlift
  exact hPnolift (exists_flatModuleLift_of_hasFlatAlgebraLift hsurjA hnilA hsurjP hkerP
    (himp (hasFlatAlgebraLift_of_exists_flatModuleLift hsurjQ hnilQ hsurjC eQQ heQQ
      ⟨N', inferInstance, inferInstance, inferInstance, inferInstance, hflatN',
        ⟨eN.trans eC⟩⟩)))

/-- **What a counterexample has to satisfy to settle Stacks 0DZ7, and that it then does.** Let
`A' → A` be a surjection with nilpotent kernel, let `P' → P` be a surjection over it with kernel
`ker(A' → A) · P'` and `P'` formally smooth over `A'`, let `P → B` be a surjection, let `Q'` be
the localization of `P'` at a multiplicative subset `T'` and let `C` be the localization of `B`
at the image of `T'`. If the base change of `B` to `Q = P ⊗_{P'} Q'` has an `A'`-flat
`Q'`-module lift and `B` has **no** `A'`-flat `P'`-module lift, then flat lifts of `C` to `A'`
do not give flat lifts of `B`: the converse of Stacks 0DZ7 fails at this presentation, and with
it the biconditional, the forward implication being
`Deformation.hasFlatAlgebraLift_localization_of_hasFlatAlgebraLift`.

This is `Deformation.not_hasFlatAlgebraLift_of_baseChange_of_presentation_at` with the
presentation `(P ⊗_{P'} Q') ⊗_P B ≅ C` of the base change read off the two localizations rather
than supplied, so that the data a witness has to produce is exactly the hypothesis list above:

* the square `A' → A`, `P' → P` with `hsurjA`, `hnilA`, `hsurjP`, `hkerP`;
* `Algebra.FormallySmooth A' P'`, which is where `P'` must be a smooth — in practice
  polynomial — presentation, and which is what makes this a counterexample to a *smooth* form
  of Stacks 0DZ2 rather than to the refuted published one;
* a surjection `P → B`, so `B` is a presented algebra and its module lifts are its algebra
  lifts;
* a multiplicative `T' ⊆ P'` and the two localizations `Q'`, `C`;
* `hQlift` and `hPnolift`, the right-hand clause of
  `Deformation.FlatModuleLiftBaseChangeInstance A' P' P Q' B` and the negation of its left-hand
  clause.

To contradict `Deformation.hasFlatAlgebraLift_localization_iff_at`, and so to settle the tag
rather than this presentation of it, a witness must additionally satisfy that lemma's remaining
hypotheses — the Noetherian hypotheses, `Algebra.FiniteType A B`, `Module.Flat A B`, and an
ideal `𝔟` with `hsyn` and `hSb` — none of which this transport needs.

Two features are then forced, by what is already proved in this file, and `Q'` being a
localization obstructs neither. A witness meeting those remaining hypotheses cannot have
`ker(A' → A)` of square zero, by
`Deformation.hasFlatAlgebraLift_localization_iff_of_sqZero`; and a witness with `B` flat over
`A` cannot have `algebraMap A' A` admitting a ring section, by
`Deformation.hasFlatAlgebraLift_localization_iff_of_split` — in either case both sides of the
tag hold outright, so `hPnolift` is unavailable. Nothing in this hypothesis list bounds `P'`:
`T'`, `Q'`, `C` and the two clauses are all free in it, so a polynomial `P'` in any number of
variables is admissible. -/
theorem not_hasFlatAlgebraLift_of_localization_of_presentation
    (A' A P' P B : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B]
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B]
    [Algebra A P] [Algebra A B] [Algebra P' P] [Algebra P' B] [Algebra P B]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [Algebra.FormallySmooth A' P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (T' : Submonoid P') (Q' : Type u) [CommRing Q'] [Algebra P' Q'] [IsLocalization T' Q']
    [Algebra A' Q'] [IsScalarTower A' P' Q']
    (C : Type u) [CommRing C] [Algebra A' C] [Algebra A C] [Algebra B C]
    [IsScalarTower A' A C] [IsScalarTower A B C]
    [IsLocalization (Algebra.algebraMapSubmonoid B T') C]
    (hQlift : ∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
      (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
      Nonempty (((P ⊗[P'] Q') ⊗[Q'] N') ≃ₗ[P ⊗[P'] Q'] ((P ⊗[P'] Q') ⊗[P] B)))
    (hPnolift : ¬ ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
      (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
      Nonempty ((P ⊗[P'] M') ≃ₗ[P] B)) :
    ¬ (HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B) := by
  obtain ⟨e, he⟩ := exists_ringEquiv_tensorLocalization P' P B T' Q' C
  refine not_hasFlatAlgebraLift_of_baseChange_of_presentation_at A' A P' P B Q' C hsurjA hnilA
    hsurjP hkerP hsurjB e (algebraMap_eq_tensorLocalization A P' P B Q' C e he) hQlift
    hPnolift

/-! ### Deformations of localizations along a square-zero thickening -/

/-- **Stacks 0DZ7 at a square-zero kernel, unconditionally.** For a surjection `A' → A` of
Noetherian rings whose kernel has square zero and a finite type flat `A`-algebra `B` with
`A → B_h` syntomic for every `h` in an ideal `𝔟`, and a multiplicative subset `S ⊆ B` meeting
no prime of `B` containing `𝔟`: flat lifts of `B` to `A'` exist exactly when flat lifts of
`S⁻¹B` do.

This is `Deformation.hasFlatAlgebraLift_localization_iff_at` with its hypothesis `h0DZ2`
discharged by `Deformation.flatModuleLiftBaseChangeStatementAt_of_sq_zero`, which proves
Stacks 0DZ2 in the shape that proof consumes whenever the kernel of `A' → A` has square zero.
It subsumes `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_localization_of_sqZero`,
which is the same statement's second implication. -/
theorem hasFlatAlgebraLift_localization_iff_of_sqZero
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hzeroA : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    [Algebra.FiniteType A B] [Module.Flat A B]
    (S : Submonoid B) (C : Type u) [CommRing C] [Algebra B C] [IsLocalization S C]
    [Algebra A C] [IsScalarTower A B C]
    (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (hSb : ∀ q : Ideal B, q.IsPrime → b ≤ q → ∀ s ∈ S, s ∉ q) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A C :=
  hasFlatAlgebraLift_localization_iff_at A' A B
    (flatModuleLiftBaseChangeStatementAt_of_sq_zero A' A hsurjA hzeroA) hsurjA ⟨2, hzeroA⟩ S C b
    hsyn hSb

/-- **The second implication of Stacks 0DZ3's comparison at a square-zero kernel.** This is
`Deformation.hasFlatAlgebraLift_of_baseChange_of_presentation` with the hypothesis `h0DZ2`
discharged: the presentation is the literal base change `P' ⊗_{A'} A`, at which Stacks 0DZ2 is
proved for a square-zero kernel. -/
theorem hasFlatAlgebraLift_of_baseChange_of_presentation_of_sqZero
    (A' A P' B Q' C : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing B] [CommRing Q'] [CommRing C]
    [IsNoetherianRing P'] [IsNoetherianRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' B] [Algebra A' Q']
    [Algebra A B] [Algebra P' B] [Algebra (TensorProduct A' P' A) B] [Algebra P' Q']
    [Algebra A' C] [Algebra A C] [Algebra Q' C]
    [IsScalarTower A' A B] [IsScalarTower A' P' B]
    [IsScalarTower A (TensorProduct A' P' A) B] [IsScalarTower P' (TensorProduct A' P' A) B]
    [IsScalarTower A' P' Q'] [IsScalarTower A' A C]
    [Module.Flat A' P'] [Module.Flat A B] [Module.Flat P' Q']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hzeroA : (RingHom.ker (algebraMap A' A)) ^ 2 = ⊥)
    (hsurjB : Function.Surjective (algebraMap (TensorProduct A' P' A) B))
    (J' : Ideal P')
    (hquot : Function.Bijective (Ideal.quotientMap (J'.map (algebraMap P' Q'))
      (algebraMap P' Q') Ideal.le_comap_map))
    (hloc : ∀ g ∈ J',
      letI : Algebra (Localization.Away g)
          (Localization.Away (algebraMap P' (TensorProduct A' P' A) g)) :=
        (Localization.awayMap (algebraMap P' (TensorProduct A' P' A)) g).toAlgebra
      ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
        (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
        Module.Flat A' L ∧ Nonempty
          ((Localization.Away (algebraMap P' (TensorProduct A' P' A) g)
              ⊗[Localization.Away g] L)
            ≃ₗ[Localization.Away (algebraMap P' (TensorProduct A' P' A) g)]
              (Localization.Away (algebraMap P' (TensorProduct A' P' A) g)
                ⊗[TensorProduct A' P' A] B)))
    (e : (((TensorProduct A' P' A ⊗[P'] Q') ⊗[TensorProduct A' P' A] B)) ≃+* C)
    (hAe : ∀ a : A, algebraMap A C a =
      e ((algebraMap A (TensorProduct A' P' A ⊗[P'] Q') a)
        ⊗ₜ[TensorProduct A' P' A] (1 : B)))
    (hQe : ∀ x : Q', algebraMap Q' C x =
      e ((((1 : TensorProduct A' P' A) ⊗ₜ[P'] x)) ⊗ₜ[TensorProduct A' P' A] (1 : B)))
    (hlift : ∀ (C' : Type u) (_ : CommRing C') (_ : Algebra A' C')
      (eC : (A ⊗[A'] C') ≃ₐ[A] C), ∃ g : Q' →ₐ[A'] C',
        ∀ x : Q', eC (1 ⊗ₜ[A'] (g x)) = algebraMap Q' C x) :
    HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B := by
  have hsurjP : Function.Surjective (algebraMap P' (TensorProduct A' P' A)) :=
    surjective_tmul_one A' A hsurjA P'
  have hkerP : RingHom.ker (algebraMap P' (TensorProduct A' P' A)) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P') :=
    Algebra.ker_algebraMap_tensorProduct_left A' P' A
  have hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)) := ⟨2, hzeroA⟩
  have hnilP : IsNilpotent (RingHom.ker (algebraMap P' (TensorProduct A' P' A))) := by
    rw [hkerP]
    exact isNilpotent_ideal_map hnilA _
  have : IsNoetherianRing (TensorProduct A' P' A) :=
    isNoetherianRing_of_surjective P' (TensorProduct A' P' A)
      (algebraMap P' (TensorProduct A' P' A)) hsurjP
  have hsurjQ : Function.Surjective
      (algebraMap Q' (TensorProduct A' P' A ⊗[P'] Q')) :=
    surjective_includeRight P' (TensorProduct A' P' A) Q' hsurjP
  have hkerQ := ker_algebraMap_tensorProduct_right A' A P' (TensorProduct A' P' A) Q' hsurjP hkerP
  have := isScalarTower_tensorProduct_right A' P' (TensorProduct A' P' A) Q'
  have hfinPB : Module.Finite (TensorProduct A' P' A) B :=
    Module.Finite.of_surjective (Algebra.linearMap (TensorProduct A' P' A) B) hsurjB
  -- the presentation of `C` over `Q = P ⊗_{P'} Q'`
  let : Algebra (TensorProduct A' P' A ⊗[P'] Q') C :=
    (e.toRingHom.comp (algebraMap (TensorProduct A' P' A ⊗[P'] Q')
      ((TensorProduct A' P' A ⊗[P'] Q') ⊗[TensorProduct A' P' A] B))).toAlgebra
  have hQ2 : ∀ x : Q', algebraMap Q' C x =
      algebraMap (TensorProduct A' P' A ⊗[P'] Q') C
        (algebraMap Q' (TensorProduct A' P' A ⊗[P'] Q') x) := by
    intro x
    rw [hQe x]
    rfl
  have : IsScalarTower Q' (TensorProduct A' P' A ⊗[P'] Q') C :=
    IsScalarTower.of_algebraMap_eq hQ2
  have : IsScalarTower A (TensorProduct A' P' A ⊗[P'] Q') C :=
    IsScalarTower.of_algebraMap_eq hAe
  have eC : (((TensorProduct A' P' A ⊗[P'] Q') ⊗[TensorProduct A' P' A] B))
      ≃ₗ[TensorProduct A' P' A ⊗[P'] Q'] C :=
    (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)).toLinearEquiv
  obtain ⟨ePP, hePP⟩ : ∃ ePP : (A ⊗[A'] P') ≃ₐ[A] TensorProduct A' P' A,
      ∀ x : P', ePP (1 ⊗ₜ[A'] x) = algebraMap P' (TensorProduct A' P' A) x :=
    ⟨AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm A' A P').toRingEquiv)
      (fun a => by
        show (Algebra.TensorProduct.comm A' A P') (a ⊗ₜ[A'] (1 : P')) = (1 : P') ⊗ₜ[A'] a
        rw [Algebra.TensorProduct.comm_tmul]),
      fun x => by
        show (Algebra.TensorProduct.comm A' A P') ((1 : A) ⊗ₜ[A'] x) = x ⊗ₜ[A'] (1 : A)
        rw [Algebra.TensorProduct.comm_tmul]⟩
  rintro ⟨C', _, _, hflatC', ⟨eCa⟩⟩
  obtain ⟨gq, hgq⟩ := hlift C' inferInstance inferInstance eCa
  refine hasFlatAlgebraLift_of_exists_flatModuleLift hsurjP hnilP hsurjB ePP hePP ?_
  exact (exists_flatModuleLift_iff_baseChange_of_sqZero A' A P' Q' hsurjA hzeroA J' hquot
    B C ⟨eC⟩ hloc).mpr
      (exists_flatModuleLift_of_algebraLift hsurjA hsurjQ hkerQ C' hflatC' eCa gq hgq)

/-- **Stacks 0DZ7, the implication from the localization, at a square-zero kernel.** For a
surjection `A' → A` of Noetherian rings with square-zero kernel and a finite type flat
`A`-algebra `B` with `A → B_h` syntomic for every `h` in an ideal `𝔟`, and a multiplicative
subset `S ⊆ B` meeting no prime of `B` containing `𝔟`: if `S⁻¹B` has a flat lift to `A'`, so
does `B`.

This is the second implication of
`Deformation.hasFlatAlgebraLift_iff_hasFlatAlgebraLift_localization` at a square-zero kernel,
where Stacks 0DZ2 is a theorem rather than a hypothesis. The presentation used is
`P = P' ⊗_{A'} A` for the polynomial algebra `P' = A'[x_1, …, x_n]`, which is the shape at which
Stacks 0DZ2 is proved here; the polynomial algebra over `A` is brought across
`MvPolynomial.algebraTensorAlgEquiv`. -/
theorem hasFlatAlgebraLift_of_hasFlatAlgebraLift_localization_of_sqZero
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hzeroA : (RingHom.ker (algebraMap A' A)) ^ 2 = ⊥)
    [Algebra.FiniteType A B] [Module.Flat A B]
    (S : Submonoid B) (C : Type u) [CommRing C] [Algebra B C] [IsLocalization S C]
    [Algebra A C] [IsScalarTower A B C]
    (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (hSb : ∀ q : Ideal B, q.IsPrime → b ≤ q → ∀ s ∈ S, s ∉ q) :
    HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B := by
  classical
  have hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)) := ⟨2, hzeroA⟩
  let : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A' C := ((algebraMap A C).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A C := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A B)
  -- the presentation, taken as the base change of the polynomial algebra over `A'`
  obtain ⟨ψ, hψP, hψA⟩ :
      ∃ ψ : TensorProduct A' (MvPolynomial (Fin n) A') A ≃+* MvPolynomial (Fin n) A,
        (∀ x : MvPolynomial (Fin n) A',
          ψ (algebraMap (MvPolynomial (Fin n) A')
            (TensorProduct A' (MvPolynomial (Fin n) A') A) x) =
              MvPolynomial.map (algebraMap A' A) x) ∧
        (∀ a : A, ψ (algebraMap A (TensorProduct A' (MvPolynomial (Fin n) A') A) a) =
          algebraMap A (MvPolynomial (Fin n) A) a) := by
    refine ⟨((Algebra.TensorProduct.comm A' (MvPolynomial (Fin n) A') A).trans
      ((MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A' A).restrictScalars A')).toRingEquiv,
      fun x => ?_, fun a => ?_⟩
    · show MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A'
        A ((Algebra.TensorProduct.comm A' (MvPolynomial (Fin n) A') A)
          (x ⊗ₜ[A'] (1 : A))) = _
      rw [Algebra.TensorProduct.comm_tmul,
        ← MvPolynomial.algebraTensorAlgEquiv_symm_map (σ := Fin n) A' A x,
        AlgEquiv.apply_symm_apply]
    · show MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A'
        A ((Algebra.TensorProduct.comm A' (MvPolynomial (Fin n) A') A)
          ((1 : MvPolynomial (Fin n) A') ⊗ₜ[A'] a)) = _
      rw [Algebra.TensorProduct.comm_tmul]
      exact (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A' A).commutes a
  let : Algebra (TensorProduct A' (MvPolynomial (Fin n) A') A) B :=
    ((f : MvPolynomial (Fin n) A →+* B).comp (ψ : _ →+* MvPolynomial (Fin n) A)).toAlgebra
  have hPB : ∀ z, algebraMap (TensorProduct A' (MvPolynomial (Fin n) A') A) B z =
    f (ψ z) := fun _ => rfl
  have : IsScalarTower A (TensorProduct A' (MvPolynomial (Fin n) A') A) B :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [hPB, hψA]
      exact (f.commutes a).symm
  let : Algebra (MvPolynomial (Fin n) A') B :=
    ((algebraMap (TensorProduct A' (MvPolynomial (Fin n) A') A) B).comp
      (algebraMap (MvPolynomial (Fin n) A')
        (TensorProduct A' (MvPolynomial (Fin n) A') A))).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin n) A')
      (TensorProduct A' (MvPolynomial (Fin n) A') A) B :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A' (TensorProduct A' (MvPolynomial (Fin n) A') A) B :=
    IsScalarTower.to₁₃₄ A' A (TensorProduct A' (MvPolynomial (Fin n) A') A) B
  have : IsScalarTower A' (MvPolynomial (Fin n) A') B :=
    IsScalarTower.of_algebraMap_eq fun a' => by
      rw [IsScalarTower.algebraMap_apply A' (TensorProduct A' (MvPolynomial (Fin n) A') A) B,
        IsScalarTower.algebraMap_apply A' (MvPolynomial (Fin n) A')
          (TensorProduct A' (MvPolynomial (Fin n) A') A)]
      rfl
  have hsurjP : Function.Surjective (algebraMap (MvPolynomial (Fin n) A')
      (TensorProduct A' (MvPolynomial (Fin n) A') A)) :=
    surjective_tmul_one A' A hsurjA (MvPolynomial (Fin n) A')
  have hkerP : RingHom.ker (algebraMap (MvPolynomial (Fin n) A')
      (TensorProduct A' (MvPolynomial (Fin n) A') A)) =
      (RingHom.ker (algebraMap A' A)).map
        (algebraMap A' (MvPolynomial (Fin n) A')) :=
    Algebra.ker_algebraMap_tensorProduct_left A' (MvPolynomial (Fin n) A') A
  have hsurjB : Function.Surjective
      (algebraMap (TensorProduct A' (MvPolynomial (Fin n) A') A) B) := by
    intro y
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨ψ.symm x, by rw [hPB, RingEquiv.apply_symm_apply]⟩
  have hsurjPB : Function.Surjective
      (algebraMap (MvPolynomial (Fin n) A') B) := by
    rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin n) A')
      (TensorProduct A' (MvPolynomial (Fin n) A') A) B]
    exact hsurjB.comp hsurjP
  -- the preimages of `𝔟` and of `S` in the polynomial algebra over `A'`
  set I' : Ideal (MvPolynomial (Fin n) A') :=
    Ideal.comap (algebraMap (MvPolynomial (Fin n) A') B) b
  set T' : Submonoid (MvPolynomial (Fin n) A') :=
    S.comap (algebraMap (MvPolynomial (Fin n) A') B)
  have hT' : Algebra.algebraMapSubmonoid B T' = S :=
    Submonoid.map_comap_eq_of_surjective hsurjPB S
  have : IsLocalization (Algebra.algebraMapSubmonoid B T') C := by
    rw [hT']
    infer_instance
  have : Module.Flat (MvPolynomial (Fin n) A') (Localization T') :=
    IsLocalization.flat (Localization T') T'
  -- every element of `T'` is invertible modulo `I'`, so `P'/I' = Q'/I'Q'`
  have hunitI := isUnit_quotient_mk_comap_of_forall_isPrime
    (algebraMap (MvPolynomial (Fin n) A') B) hsurjPB b S hSb
  have hquot : Function.Bijective (Ideal.quotientMap
      (I'.map (algebraMap (MvPolynomial (Fin n) A') (Localization T')))
      (algebraMap (MvPolynomial (Fin n) A') (Localization T')) Ideal.le_comap_map) :=
    bijective_quotientMap_localization T' (Localization T') I' hunitI
  -- the presentation of the localization of `B`
  obtain ⟨e, he⟩ := exists_ringEquiv_tensorLocalization (MvPolynomial (Fin n) A')
    (TensorProduct A' (MvPolynomial (Fin n) A') A) B T' (Localization T') C
  have hAe := algebraMap_eq_tensorLocalization A (MvPolynomial (Fin n) A')
    (TensorProduct A' (MvPolynomial (Fin n) A') A) B (Localization T') C e he
  -- the algebra structures on `C` over the localized presentation
  let : Algebra (TensorProduct A' (MvPolynomial (Fin n) A') A ⊗[MvPolynomial (Fin n) A']
      Localization T') C :=
    (e.toRingHom.comp (algebraMap
      (TensorProduct A' (MvPolynomial (Fin n) A') A ⊗[MvPolynomial (Fin n) A'] Localization T')
      ((TensorProduct A' (MvPolynomial (Fin n) A') A ⊗[MvPolynomial (Fin n) A']
        Localization T') ⊗[TensorProduct A' (MvPolynomial (Fin n) A') A] B))).toAlgebra
  let : Algebra (Localization T') C :=
    ((algebraMap (TensorProduct A' (MvPolynomial (Fin n) A') A ⊗[MvPolynomial (Fin n) A']
        Localization T') C).comp
      (algebraMap (Localization T')
        (TensorProduct A' (MvPolynomial (Fin n) A') A ⊗[MvPolynomial (Fin n) A']
          Localization T'))).toAlgebra
  let : Algebra (MvPolynomial (Fin n) A') C :=
    ((algebraMap (Localization T') C).comp
      (algebraMap (MvPolynomial (Fin n) A') (Localization T'))).toAlgebra
  have hQe : ∀ x : Localization T', algebraMap (Localization T') C x =
      e ((((1 : TensorProduct A' (MvPolynomial (Fin n) A') A)
        ⊗ₜ[MvPolynomial (Fin n) A'] x))
          ⊗ₜ[TensorProduct A' (MvPolynomial (Fin n) A') A] (1 : B)) := fun _ => rfl
  have := isScalarTower_tensorProduct_right A' (MvPolynomial (Fin n) A')
    (TensorProduct A' (MvPolynomial (Fin n) A') A) (Localization T')
  have : IsScalarTower (Localization T')
      (TensorProduct A' (MvPolynomial (Fin n) A') A ⊗[MvPolynomial (Fin n) A']
        Localization T') C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A (TensorProduct A' (MvPolynomial (Fin n) A') A
      ⊗[MvPolynomial (Fin n) A'] Localization T') C := IsScalarTower.of_algebraMap_eq hAe
  have : IsScalarTower A' (TensorProduct A' (MvPolynomial (Fin n) A') A
      ⊗[MvPolynomial (Fin n) A'] Localization T') C :=
    IsScalarTower.to₁₃₄ A' A (TensorProduct A' (MvPolynomial (Fin n) A')
      A ⊗[MvPolynomial (Fin n) A'] Localization T') C
  have : IsScalarTower A' (Localization T') C :=
    IsScalarTower.to₁₂₄ A' (Localization T') (TensorProduct A' (MvPolynomial (Fin n) A') A
      ⊗[MvPolynomial (Fin n) A'] Localization T') C
  have : IsScalarTower (MvPolynomial (Fin n) A') (Localization T') C :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A' (MvPolynomial (Fin n) A') C :=
    IsScalarTower.to₁₂₄ A' (MvPolynomial (Fin n) A') (Localization T') C
  refine hasFlatAlgebraLift_of_baseChange_of_presentation_of_sqZero A' A
    (MvPolynomial (Fin n) A') B (Localization T') C hsurjA hzeroA hsurjB I' hquot
    (fun g hg => exists_flatModuleLift_localization_of_syntomic A' A
      (MvPolynomial (Fin n) A') (TensorProduct A' (MvPolynomial (Fin n) A') A) B
      hsurjA hnilA hsurjP hkerP b hsyn g hg)
    e hAe hQe (fun C' _ _ eCa => ?_)
  exact exists_algHom_of_tensorLocalization A' A (MvPolynomial (Fin n) A')
    (TensorProduct A' (MvPolynomial (Fin n) A') A) B (Localization T') C C' T' hsurjA hnilA e he
    hQe eCa

end Deformation

end
