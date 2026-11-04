module

public import Mathlib.RingTheory.Etale.Descent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Projective

/-!
# Formal smoothness descends along faithfully flat base change

Let `R → S` be a ring map and `R → R'` a faithfully flat ring map. Then `S` is formally smooth
over `R` if and only if `R' ⊗_R S` is formally smooth over `R'`. The forward direction is
stability under base change. For the converse we use that formal smoothness is equivalent to
`Ω_{S/R}` being projective together with the vanishing of `H¹(L_{S/R})`: both properties are
recovered from the base change, the first by descent of projectivity (Tag 05A9) along the
faithfully flat map `S → S ⊗_R R'`, the second because `R' ⊗_R H¹(L_{S/R}) = H¹(L_{R' ⊗ S/R'})`
for flat `R'`.

## References

* [Stacks Project, Tag 06CM](https://stacks.math.columbia.edu/tag/06CM)
-/

@[expose] public section

open TensorProduct

namespace Algebra.FormallySmooth

variable (R S R' : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommRing R'] [Algebra R R']

/-- Let `R → R'` be faithfully flat. Then `S` is formally smooth over `R` if and only if the
base change `R' ⊗_R S` is formally smooth over `R'`. -/
@[stacks 06CM "The source's `S' = S ⊗_R R'` is written `R' ⊗[R] S`, Mathlib's order for a base
change.",
  ega "0 19.3.5" "(iii), special case",
  ega "0 19.4.6" "special case",
  sga "3 XIX 2.1" "special case"]
theorem iff_tensorProduct_of_faithfullyFlat [Module.FaithfullyFlat R R'] :
    FormallySmooth R S ↔ FormallySmooth R' (R' ⊗[R] S) := by
  refine ⟨fun _ ↦ inferInstance, fun hS' ↦ ?_⟩
  obtain ⟨hproj', hH1'⟩ := (formallySmooth_iff R' (R' ⊗[R] S)).mp hS'
  refine (formallySmooth_iff R S).mpr ⟨?_, ?_⟩
  · let _ : Algebra R' (S ⊗[R] R') := TensorProduct.rightAlgebra
    let e : S ⊗[R] R' ≃ₐ[R'] R' ⊗[R] S :=
      .ofRingEquiv (f := TensorProduct.comm R S R') <| by simp [RingHom.algebraMap_toAlgebra]
    have : FormallySmooth R' (S ⊗[R] R') := .of_equiv e.symm
    have : Module.Projective (S ⊗[R] R') ((S ⊗[R] R') ⊗[S] Ω[S⁄R]) :=
      .of_equiv (KaehlerDifferential.tensorKaehlerEquiv R R' S (S ⊗[R] R')).symm
    exact Module.Projective.of_projective_tensorProduct (S ⊗[R] R')
  · have : Subsingleton (R' ⊗[R] H1Cotangent R S) := (tensorH1CotangentOfFlat R S R').subsingleton
    exact Module.FaithfullyFlat.lTensor_reflects_triviality R R' (H1Cotangent R S)

end Algebra.FormallySmooth
