module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleLocalHom
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.CompletionCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.UnramifiedCompletion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An étale local homomorphism with no residue field extension completes to an isomorphism

An étale local homomorphism of Noetherian local rings which induces an isomorphism on residue
fields induces an isomorphism on `𝔪`-adic completions. This is the ring-level content of the
statement that an elementary étale neighbourhood does not change the completed local ring.

Surjectivity is Stacks 039H part (2), which needs only formal unramifiedness and the residue
field isomorphism. Injectivity is faithful flatness: an étale homomorphism is flat, flatness
passes to the completions by Stacks 0C4G, and a flat local homomorphism of local rings is
faithfully flat, hence injective.

## Main results

* `RingHom.bijective_adicCompletionMap_of_isEtaleLocalHom`: an étale local homomorphism inducing
  a bijection of residue fields induces a bijection of completions.

## Implementation notes

The statement is phrased with `Function.Bijective (adicCompletionMap f ..)` rather than as the
existence of a `RingEquiv` between the two completions, which is the shape in which Stacks 0AGX
is already available (`exists_adicCompletion_ringEquiv_of_flat`). The difference matters: an
abstract equivalence between the completions carries no information about the canonical map, and
every consumer here needs the canonical map itself to be invertible, so that a congruence
between maps into the completion can be composed with its inverse.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace RingHom

/-- A flat local homomorphism of local rings is injective. Flatness together with locality gives
faithful flatness, and a faithfully flat algebra has injective structure map.

Kept private: `Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.injective_of_flat_of_isLocalHom`
is the same statement, but it sits downstream among the proper flat families, so importing it
here would point the étale criteria at that development. -/
@[ega "0 6.5.1" "special case"]
private theorem injective_of_flat_of_isLocalHom {A : Type u} {B : Type v}
    [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] (hf : f.Flat) :
    Function.Injective f := by
  let : Algebra A B := f.toAlgebra
  have hflat : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hf
  have hloc : IsLocalHom (algebraMap A B) := ‹IsLocalHom f›
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective A B

/-- An étale local homomorphism of Noetherian local rings whose residue field map is bijective
induces a bijection on `𝔪`-adic completions. -/
@[sga "3 XI 1.4" "(ii)"]
theorem bijective_adicCompletionMap_of_isEtaleLocalHom {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] (hf : IsEtaleLocalHom f)
    (hκ : Function.Bijective (ResidueField.map f)) :
    Function.Bijective
      (adicCompletionMap f (maximalIdeal A) (maximalIdeal B) (map_maximalIdeal_le f)) := by
  have hsurj := surjective_adicCompletionMap_of_bijective_residueFieldMap f hf.2.1 hf.2.2 hκ
  have hflat : (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
      (map_maximalIdeal_le f)).Flat := (adicCompletionMap_flat_iff f).mpr hf.1
  have : IsLocalHom (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
      (map_maximalIdeal_le f)) := AdicCompletion.isLocalHom_adicCompletionMap f
  exact ⟨injective_of_flat_of_isLocalHom _ hflat, hsurj⟩

end RingHom

end
