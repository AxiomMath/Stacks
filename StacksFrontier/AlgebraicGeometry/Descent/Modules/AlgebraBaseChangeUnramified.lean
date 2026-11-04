module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.AlgebraBaseChangeFiniteness
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.BaseChangeFlat
public import StacksFrontier.RingTheory.Unramified.Basic

/-!
# Descent of unramifiedness along universally injective ring maps

Let `R → S` be a universally injective map of commutative rings. An `R`-algebra is formally
unramified, unramified, or étale exactly when its base change to `S` is.

## Main results

* `Algebra.formallyUnramified_iff_tensorProduct_of_universallyInjective`: formal
  unramifiedness descends and ascends along a universally injective base-ring map.
* `Algebra.unramified_iff_baseChange_of_universallyInjective`: the same for unramifiedness.
* `Algebra.etale_iff_baseChange_of_universallyInjective`: the same for étaleness.

## Implementation notes

Formal unramifiedness and unramifiedness are stated for the base change in the source order
`A ⊗[R] S`, equipped with its canonical right-hand `S`-algebra structure, while étaleness is
stated for `S ⊗[R] A`; the two are interchanged by `Algebra.TensorProduct.commRight`. Since
`Algebra.TensorProduct.rightAlgebra` is not a global instance, it is enabled locally here.

Formal unramifiedness is the vanishing of the module of differentials, and the differentials
of the base change are the base change of the differentials, so one direction is a tensor
factor of a trivial module and the other uses that `ω ↦ 1 ⊗ ω` is injective. Unramifiedness
adds finite type and étaleness adds flatness and finite presentation; each of those descends
separately.

## References

* [Stacks Project, Tag 08XE](https://stacks.math.columbia.edu/tag/08XE)
-/

@[expose] public section

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace Algebra

/-- Formal unramifiedness descends and ascends along a universally injective base-ring map. -/
@[stacks 08XE "formally_unramified"]
theorem formallyUnramified_iff_tensorProduct_of_universallyInjective
    (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] (hRS : Algebra.UniversallyInjective R S) :
    Algebra.FormallyUnramified R A ↔
      Algebra.FormallyUnramified S (TensorProduct R A S) := by
  have hswap : Algebra.FormallyUnramified S (TensorProduct R S A) ↔
      Algebra.FormallyUnramified S (TensorProduct R A S) :=
    ⟨fun _ => .of_equiv (Algebra.TensorProduct.commRight R S A),
      fun _ => .of_equiv (Algebra.TensorProduct.commRight R S A).symm⟩
  rw [← hswap, Algebra.formallyUnramified_iff R A,
    Algebra.formallyUnramified_iff S (TensorProduct R S A)]
  let e : (S ⊗[R] Ω[A⁄R]) ≃ₗ[S] Ω[(S ⊗[R] A)⁄S] :=
    KaehlerDifferential.tensorKaehlerEquivBase R S A (S ⊗[R] A)
  refine ⟨fun _ => e.symm.toEquiv.subsingleton, fun _ => ?_⟩
  have : Subsingleton (S ⊗[R] Ω[A⁄R]) := e.toEquiv.subsingleton
  exact ((hRS (Ω[A⁄R])).comp
    (_root_.TensorProduct.lid R (Ω[A⁄R])).symm.injective).subsingleton

/-- Unramifiedness descends and ascends along a universally injective ring map. -/
@[stacks 08XE "unramified"]
theorem unramified_iff_baseChange_of_universallyInjective
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : Algebra.UniversallyInjective R S)
    (A : Type u) [CommRing A] [Algebra R A] :
    Algebra.Unramified R A ↔ Algebra.Unramified S (A ⊗[R] S) :=
  have hf := formallyUnramified_iff_tensorProduct_of_universallyInjective R S A hRS
  have ht := finiteType_iff_tensorProduct R S A hRS
  ⟨fun h => ⟨hf.mp h.formallyUnramified, ht.mp h.finiteType⟩,
    fun h => ⟨hf.mpr h.formallyUnramified, ht.mpr h.finiteType⟩⟩

/-- Étaleness is flatness together with unramifiedness and finite presentation. -/
private theorem etale_iff_flat_and_unramified_and_finitePresentation
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    Algebra.Etale R A ↔
      Module.Flat R A ∧ Algebra.Unramified R A ∧ Algebra.FinitePresentation R A :=
  (Algebra.Etale.tfae R A).out 1 3

/-- Étaleness descends and ascends along a universally injective ring map. -/
@[stacks 08XE "etale"]
theorem etale_iff_baseChange_of_universallyInjective
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    (hRS : Algebra.UniversallyInjective R S)
    (A : Type u) [CommRing A] [Algebra R A] :
    Algebra.Etale R A ↔ Algebra.Etale S (TensorProduct R S A) := by
  have hu : Algebra.Unramified S (TensorProduct R A S) ↔
      Algebra.Unramified S (TensorProduct R S A) :=
    ⟨fun _ => .of_equiv (Algebra.TensorProduct.commRight R S A).symm,
      fun _ => .of_equiv (Algebra.TensorProduct.commRight R S A)⟩
  rw [etale_iff_flat_and_unramified_and_finitePresentation,
    etale_iff_flat_and_unramified_and_finitePresentation]
  exact and_congr (Module.flat_iff_baseChange_of_universallyInjective hRS A)
    (and_congr ((unramified_iff_baseChange_of_universallyInjective hRS A).trans hu)
      (finitePresentation_iff_baseChange_of_universallyInjective hRS A))

end Algebra

end
