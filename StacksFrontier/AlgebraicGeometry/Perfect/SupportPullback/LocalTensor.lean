module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of a finite module along a local homomorphism

Let `R → S` be a local homomorphism of local rings and `M` a finite `R`-module. Then
`S ⊗[R] M` vanishes exactly when `M` does. This is the local form of Nakayama's lemma that
detects nonvanishing of a base change on residue fields.

## Main results

* `IsLocalRing.subsingleton_tensorProduct_of_isLocalHom`: vanishing of the base change.
* `IsLocalRing.nontrivial_tensorProduct_of_isLocalHom`: the same statement read on
  nonvanishing.

## Implementation notes

Writing `k` and `l` for the residue fields of `R` and `S`, the chain is

`S ⊗[R] M = 0 → l ⊗[S] (S ⊗[R] M) = 0 ≅ l ⊗[R] M ≅ l ⊗[k] (k ⊗[R] M) → k ⊗[R] M = 0 → M = 0`,

where the two middle steps cancel a base change, the next one uses that `l` is a nonzero
vector space over `k` and hence faithfully flat, and the last is
`IsLocalRing.subsingleton_tensorProduct`, which is where finiteness of `M` enters.

Locality of `R → S` is what makes `l` an algebra over `k`; Mathlib already supplies that
algebra structure and the scalar towers through it, so the only structures created here are
the two towers through `S` itself.
-/

@[expose] public section

open scoped TensorProduct

namespace IsLocalRing

/-- A finite module over a local ring vanishes exactly when its base change along a local
homomorphism of local rings vanishes. -/
@[ega "0 1.7.5" "Nakayama step"]
theorem subsingleton_tensorProduct_of_isLocalHom
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Subsingleton (S ⊗[R] M) ↔ Subsingleton M := by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  let : IsScalarTower R S (ResidueField S) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R (ResidueField S) (ResidueField S) := IsScalarTower.right
  have h1 : Subsingleton (ResidueField S ⊗[S] (S ⊗[R] M)) := inferInstance
  have h2 : Subsingleton (ResidueField S ⊗[R] M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R S (ResidueField S)
      (ResidueField S) M).toEquiv.subsingleton_congr.mp h1
  have h3 : Subsingleton (ResidueField S ⊗[ResidueField R] (ResidueField R ⊗[R] M)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R (ResidueField R) (ResidueField S)
      (ResidueField S) M).toEquiv.subsingleton_congr.mpr h2
  have h4 : Subsingleton (ResidueField R ⊗[R] M) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right
      (ResidueField R) (ResidueField S)).mp h3
  exact IsLocalRing.subsingleton_tensorProduct.mp h4

/-- The base change of a finite module along a local homomorphism of local rings is nonzero
exactly when the module is nonzero. -/
@[ega "0 1.7.5" "Nakayama step"]
theorem nontrivial_tensorProduct_of_isLocalHom
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Nontrivial (S ⊗[R] M) ↔ Nontrivial M :=
  not_subsingleton_iff_nontrivial.symm.trans
    ((not_congr subsingleton_tensorProduct_of_isLocalHom).trans not_subsingleton_iff_nontrivial)

end IsLocalRing

end
