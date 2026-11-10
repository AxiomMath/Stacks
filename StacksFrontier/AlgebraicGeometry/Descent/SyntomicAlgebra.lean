module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothAlgebra
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.RingHomProperty
public import StacksFrontier.RingTheory.LocalCompleteIntersection.Localization
public import StacksFrontier.RingTheory.Syntomic.Defs

/-!
# Syntomicity descends along a faithfully flat algebra of finite presentation

Let `R → A → B` be ring maps with `B` faithfully flat and of finite presentation over `A`. If
`B` is syntomic over `R`, then so is `A`. This is the commutative algebra content of the descent
of syntomicity along a surjective flat morphism of schemes locally of finite presentation.

Syntomicity is flatness, finite presentation and local complete intersection fibres. The first
descends by faithfully flat descent of flatness and the second by the finitely presented model
of `A → B`, both exactly as for smoothness. What is left is the fibre over a prime `p` of `R`:
the base change `κ(p) ⊗[R] B` is again faithfully flat over `κ(p) ⊗[R] A`, so the fibre
statement is the descent of the local complete intersection property along a faithfully flat
algebra over a field.

That last statement is Avramov's theorem. Over a field the local complete intersection property
of a finite type algebra is the intrinsic complete intersection property of all of its local
rings (**Stacks 09Q6**), and for a prime `p` of `A` faithful flatness provides a prime `q` of `B`
above it, making `A_p → B_q` a flat local homomorphism of Noetherian local rings whose target is
a complete intersection; **Stacks 09Q2** then says that the source is one too.

## Main definitions

* `Stacks.RingTheory.SyntomicDescent.LciDescendsAlongFaithfullyFlatSyntomic` names the descent of
  the local-complete-intersection condition over a field along a faithfully flat syntomic
  algebra, so that a development can quantify over it; the theorem below proves it.

## Main results

* `Stacks.RingTheory.SyntomicDescent.isLocalCompleteIntersection_of_faithfullyFlat`: over a
  field, the local complete intersection property descends along a faithfully flat algebra.
* `Stacks.RingTheory.SyntomicDescent.syntomic_of_faithfullyFlat`: syntomicity descends along a
  faithfully flat algebra of finite presentation.
* `Stacks.RingTheory.SyntomicDescent.ringHom_syntomic_of_faithfullyFlat`: the same statement for
  ring homomorphisms, which is the form the scheme-level descent consumes.

## Implementation notes

The fibre over `p` is Mathlib's `Ideal.Fiber`, that is `κ(p) ⊗[R] A`, and the faithfully flat
algebra over it is `κ(p) ⊗[R] B`. The map between them is `Algebra.TensorProduct.map`, and that
it exhibits `κ(p) ⊗[R] B` as the base change of `B` along `A → κ(p) ⊗[R] A` is
`Algebra.IsPushout.comp_iff` applied to the tower `R → A → B` and the scalar extension
`R → κ(p)`; this is the same bookkeeping as in
`Stacks.RingTheory.SmoothDescent.smooth_of_faithfullyFlat`, and it is kept separate from the
field case so that each statement is usable on its own.

The complete intersection property of a Noetherian local ring `A` is
`LocalCompleteIntersection.IsCompleteIntersectionRing A`, a condition on the completion of `A`,
while Stacks 09Q2 is stated with the presentation-free
`LocalCompleteIntersection.IsCompleteIntersectionCompleteLocalRing` of that completion. The two
differ by the assertion that the completion is a Noetherian complete local ring, which is
automatic; `isCompleteIntersectionCompleteLocalRing_adicCompletion` records the passage.

## References

* [Stacks Project, Tag 02K3](https://stacks.math.columbia.edu/tag/02K3)
* [Stacks Project, Tag 02KK](https://stacks.math.columbia.edu/tag/02KK)
* [Stacks Project, Tag 05B7](https://stacks.math.columbia.edu/tag/05B7)
* [Stacks Project, Tag 09Q2](https://stacks.math.columbia.edu/tag/09Q2)
* [Stacks Project, Tag 09Q6](https://stacks.math.columbia.edu/tag/09Q6)
* [Stacks Project, Tag 09Q7](https://stacks.math.columbia.edu/tag/09Q7)
-/

@[expose] public section

open TensorProduct

universe u v

namespace Stacks.RingTheory.SyntomicDescent

/-- A local complete intersection over a field is of finite type over it: it is covered by
finitely many principal localizations which are global complete intersections, and those are of
finite type. -/
theorem finiteType_of_isLocalCompleteIntersection (k : Type*) [Field k] (S : Type*) [CommRing S]
    [Algebra k S] (h : IsLocalCompleteIntersection k S) : Algebra.FiniteType k S := by
  obtain ⟨s, hs, hg⟩ := h
  exact Algebra.FiniteType.of_span_eq_top_target s hs fun g hgs ↦ (hg g hgs).finiteType

/-- The complete intersection property of a Noetherian local ring, read as the
presentation-free property of its completion. The completion of a Noetherian local ring is a
Noetherian complete local ring, which is the only difference between the two conditions. -/
theorem isCompleteIntersectionCompleteLocalRing_adicCompletion (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A]
    (hA : LocalCompleteIntersection.IsCompleteIntersectionRing A) :
    LocalCompleteIntersection.IsCompleteIntersectionCompleteLocalRing
      (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩, hA⟩

/-- Over a field, the local complete intersection property descends along a faithfully flat
algebra: if `k → A → B` are algebras over a field `k` with `B` faithfully flat over `A` and a
local complete intersection over `k`, and `A` is of finite type over `k`, then `A` is a local
complete intersection over `k`.

This is a consequence of Avramov's theorem, not a statement of it: Stacks 09Q6 reads both sides
as the intrinsic complete intersection property of all local rings, and the descending half of
Stacks 09Q7 — `LocalCompleteIntersection.isCompleteIntersectionRing_of_flat` — applies to the
flat local homomorphism `A_p → B_q` for a prime `q` of `B` above `p`. Tag 09Q7 itself is the
biconditional for a flat local homomorphism of Noetherian local rings and is carried by
`LocalCompleteIntersection.isCompleteIntersectionRing_iff_of_flat`. -/
theorem isLocalCompleteIntersection_of_faithfullyFlat {k : Type u} {A B : Type v} [Field k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [Module.FaithfullyFlat A B] [Algebra.FiniteType k A]
    (hB : IsLocalCompleteIntersection k B) : IsLocalCompleteIntersection k A := by
  have hBft : Algebra.FiniteType k B := finiteType_of_isLocalCompleteIntersection k B hB
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hBring :=
    (LocalCompleteIntersection.isLocalCompleteIntersection_iff_isLocalCompleteIntersectionRing
      k B).mp hB
  refine (LocalCompleteIntersection.isLocalCompleteIntersection_iff_isLocalCompleteIntersectionRing
    k A).mpr ?_
  intro p hp
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := B) p
  have : q.IsPrime := hq
  have : q.LiesOver p := hqp
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have hflat :=
    LocalCompleteIntersection.isCompleteIntersectionCompleteLocalRing_adicCompletion_iff_of_flat
      (Localization.AtPrime p) (Localization.AtPrime q)
  exact (hflat.mp (isCompleteIntersectionCompleteLocalRing_adicCompletion _ (hBring q))).1.2

/-- **Descent of the local-complete-intersection condition over a field along a faithfully flat
syntomic algebra.** For `k → A → B` with `k` a field, `A` of finite type over `k`, and `A → B`
syntomic and faithfully flat: if `B` is a local complete intersection over `k`, then so is `A`.

This is the statement a development of Stacks 02K3 may carry as a hypothesis rather than prove;
it is named so that such a development can quantify over it. It is
`isLocalCompleteIntersection_of_faithfullyFlat` with the extra hypothesis that `A → B` be
syntomic, so the theorem above already discharges it. -/
def LciDescendsAlongFaithfullyFlatSyntomic : Prop :=
  ∀ (k A B : Type u) [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra A B]
    [Algebra k B] [IsScalarTower k A B] [Module.FaithfullyFlat A B] [Algebra.Syntomic A B]
    [Algebra.FiniteType k A],
    IsLocalCompleteIntersection k B → IsLocalCompleteIntersection k A

/-- The fibres of a descent situation are again descent situations: for a tower `R → A → B` with
`B` faithfully flat over `A`, the base change `T ⊗[R] B` is faithfully flat over `T ⊗[R] A` for
any `R`-algebra `T`, so over a field `T` the local complete intersection property descends from
the one fibre to the other. -/
theorem isLocalCompleteIntersection_tensorProduct {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation R A] (T : Type u) [Field T]
    [Algebra R T] (hB : IsLocalCompleteIntersection T (T ⊗[R] B)) :
    IsLocalCompleteIntersection T (T ⊗[R] A) := by
  let _ : Algebra A (T ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra B (T ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra (T ⊗[R] A) (T ⊗[R] B) :=
    (Algebra.TensorProduct.map (AlgHom.id T T) (IsScalarTower.toAlgHom R A B)).toRingHom.toAlgebra
  let _ : Algebra A (T ⊗[R] B) := ((algebraMap B (T ⊗[R] B)).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B (T ⊗[R] B) := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower T (T ⊗[R] A) (T ⊗[R] B) := .of_algebraMap_eq fun t =>
    ((Algebra.TensorProduct.map (AlgHom.id T T) (IsScalarTower.toAlgHom R A B)).commutes t).symm
  have : IsScalarTower A (T ⊗[R] A) (T ⊗[R] B) := .of_algebraMap_eq fun a => by
    change (1 : T) ⊗ₜ[R] (algebraMap A B a) =
      Algebra.TensorProduct.map (AlgHom.id T T) (IsScalarTower.toAlgHom R A B) (1 ⊗ₜ[R] a)
    simp
  have : IsScalarTower R (T ⊗[R] A) (T ⊗[R] B) := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R T (T ⊗[R] B),
      IsScalarTower.algebraMap_apply R T (T ⊗[R] A),
      ← IsScalarTower.algebraMap_apply T (T ⊗[R] A) (T ⊗[R] B)]
  have : Algebra.IsPushout A (T ⊗[R] A) B (T ⊗[R] B) :=
    ((Algebra.IsPushout.comp_iff R A T (T ⊗[R] A) (T := B) (T' := T ⊗[R] B)).mp
      inferInstance).symm
  have : Module.FaithfullyFlat (T ⊗[R] A) (T ⊗[R] B) :=
    Module.FaithfullyFlat.of_linearEquiv (T ⊗[R] A) ((T ⊗[R] A) ⊗[A] B)
      (Algebra.IsPushout.equiv A (T ⊗[R] A) B (T ⊗[R] B)).symm.toLinearEquiv
  have : Algebra.FiniteType T (T ⊗[R] A) := Algebra.FiniteType.of_finitePresentation
  exact isLocalCompleteIntersection_of_faithfullyFlat (k := T) (A := T ⊗[R] A) (B := T ⊗[R] B) hB

/-- **Descent of syntomicity along a faithfully flat algebra of finite presentation.** Let
`R → A → B` be ring maps with `B` faithfully flat and of finite presentation over `A`. If `B` is
syntomic over `R`, then `A` is syntomic over `R`.

This is the algebra content of Stacks 05B7, and through it of Stacks 02K3 and of the syntomic
case of Stacks 02KM. -/
theorem syntomic_of_faithfullyFlat {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [Module.FaithfullyFlat A B]
    [Algebra.FinitePresentation A B] [Algebra.Syntomic R B] : Algebra.Syntomic R A := by
  have : Algebra.FinitePresentation R A :=
    Stacks.RingTheory.SmoothDescent.finitePresentation_of_faithfullyFlat (B := B)
  have : Module.Flat R A := Stacks.Etale.flat_of_flat_of_faithfullyFlat R A B
  refine ⟨inferInstance, inferInstance, fun p _ => ?_⟩
  exact isLocalCompleteIntersection_tensorProduct (A := A) (B := B) p.ResidueField
    (Algebra.Syntomic.isLocalCompleteIntersection_fiber p)

/-- **Descent of syntomicity along a faithfully flat ring map of finite presentation.** If
`ψ : A →+* B` is faithfully flat and of finite presentation and `ψ.comp φ` is syntomic, then
`φ : R →+* A` is syntomic. -/
theorem ringHom_syntomic_of_faithfullyFlat {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] (φ : R →+* A) (ψ : A →+* B) (hcomp : (ψ.comp φ).Syntomic)
    (hff : ψ.FaithfullyFlat) (hfp : ψ.FinitePresentation) : φ.Syntomic := by
  let _ : Algebra R A := φ.toAlgebra
  let _ : Algebra A B := ψ.toAlgebra
  let _ : Algebra R B := (ψ.comp φ).toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq fun _ => rfl
  have : Module.FaithfullyFlat A B := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  have : Algebra.FinitePresentation A B := RingHom.finitePresentation_algebraMap.mp hfp
  have : Algebra.Syntomic R B := hcomp
  exact syntomic_of_faithfullyFlat (B := B)

end Stacks.RingTheory.SyntomicDescent

end
