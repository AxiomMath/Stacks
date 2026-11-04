module

public import StacksFrontier.Homology.HomComplex.DerivedInternalHom
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse

/-!
# The two derived tensor products on `D(ModuleCat.{u} R)` agree

Let `R` be a commutative ring in the universe `u`. The library reaches the derived tensor
product of `R`-modules by two different constants, and on the derived category
`D(ModuleCat.{u} R)` -- the one whose module universe is the ring's own -- both are available at
once:

* `StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor R`, the tensor half of
  `StacksDraft.DerivedHom.derivedHomAdjunction` over `R` itself, built directly on the monoidal
  category `CochainComplex (ModuleCat.{u} R) ℤ`;
* `(StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{u, u, u + 1} R).tensor`, the tensor half
  of the adjunction carrying the tagged statement of [stacks 0A63], which is
  `StacksDraft.DerivedHom.derivedHomAdjunction` over `ULift.{u} R` conjugated by
  `StacksDraft.DerivedHom.derivedScalarEquivalence`.

These are genuinely different constants: the second is built over the lifted ring and transported,
and the equation between them is not closed by `rfl`. Every comparison in
`StacksFrontier.RingTheory.Dualizing.AdjunctionCoherence` relates the second to the model-level
tensor product over `ULift.{v} R`, which is where the two vocabularies meet when the module
universe is independent of the ring's; none of them compares it with the model-level tensor
product over `R`. This module supplies that comparison, at the module universe where both
constants exist.

## Main results

* `StacksDraft.DerivedHom.derivedTensorOverRing_iso_modelTensor_of_kFlat`: the two bifunctors
  agree at a pair of complexes whose **second** member is K-flat, the first being arbitrary.
* `StacksDraft.DerivedHom.nonempty_derivedTensorOverRing_iso_modelTensor`: the two bifunctors
  agree at an arbitrary pair of objects of `D(ModuleCat.{u} R)`.

## Implementation notes

Both bifunctors are computed by the ordinary total tensor product of representatives as soon as
the second representative is K-flat: for the model-level one this is
`StacksDraft.DerivedHom.DerivedHomData.tensorIso`, a component of its tensor comparison field,
and for the transported one it is
`CochainComplex.DerivedTensor.derivedTensor_comparison`, which reads the transport through
`StacksDraft.DerivedHom.derivedTensorModelIso` and the scalar comparison of total tensor
products. The two targets are the same complex: at module universe equal to the ring universe the
total tensor product `CochainComplex.DerivedTensor.tensorComplex` of
`CochainComplex.DerivedTensor.moduleTensor` *is* the monoidal product of
`CochainComplex (ModuleCat.{u} R) ℤ`, as
`CochainComplex.DerivedTensor.tensorHom_eq_mapBifunctorMap` records on morphisms. So the K-flat
comparison is one composite of the two, and the general case follows by moving both objects to
K-flat representatives, which exist by `CochainComplex.KFlat.exists_kFlat_representative`.

The general statement is `Nonempty` of an isomorphism rather than an isomorphism: the K-flat
representatives are chosen, and nothing here makes the choice natural. That is enough for the
consumers, whose hypotheses and conclusions are themselves `Nonempty` of an isomorphism of
objects. Promoting the comparison to an isomorphism of bifunctors -- which is what an isomorphism
of the two adjunctions in the sense of
`StacksDraft.DerivedHom.DerivedHomAdjunction.TransportIso` would need -- requires the naturality
of `CochainComplex.DerivedTensor.derivedTensor_comparison` in both variables together with an
extension of the resulting comparison off the K-flat complexes, neither of which is recorded.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex.DerivedTensor

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.DerivedHom

variable (R : Type u) [CommRing R]

/-- **The two derived tensor products agree at a K-flat second representative.** For an arbitrary
cochain complex `K` of `R`-modules and a K-flat one `L`, the tensor bifunctor of
`StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` -- the one of the tagged statement of
[stacks 0A63] -- and the model-level bifunctor
`StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor` over `R` itself take the same value on
the pair of localizations.

Both are the localization of the total tensor product `K ⊗ L`: for the second this is the
tensor comparison field of `StacksDraft.DerivedHom.derivedHomAdjunction`, and for the first it is
`CochainComplex.DerivedTensor.derivedTensor_comparison`. Only `L` is required to be K-flat,
because neither comparison asks more. -/
public def derivedTensorOverRing_iso_modelTensor_of_kFlat
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.KFlat) :
    (derivedHomAdjunctionOverRing.{u, u, u + 1} R).tensor.obj
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      (DerivedInternalHom.Model.tensor R).obj
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  derivedTensor_comparison.{u, u} R K L hL ≪≫
    ((derivedHomAdjunction (R := R)).tensorIso K L hL).symm

/-- **The two derived tensor products on `D(ModuleCat.{u} R)` agree at every pair of objects.**
The tensor bifunctor of `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, which is the one
appearing in the tagged statement of [stacks 0A63], and the model-level bifunctor
`StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor` over `R` itself take isomorphic values
on every pair of objects of the derived category.

Nothing is assumed of the two objects. The isomorphism is produced from
`StacksDraft.DerivedHom.derivedTensorOverRing_iso_modelTensor_of_kFlat` by moving both arguments
to K-flat representatives, so it depends on the choice of those and is not claimed to be natural;
this is the form in which a statement about one of the two tensor products, with hypothesis and
conclusion both isomorphisms of objects, becomes a statement about the other. -/
public theorem nonempty_derivedTensorOverRing_iso_modelTensor
    (K L : DerivedCategory (ModuleCat.{u} R)) :
    Nonempty ((derivedHomAdjunctionOverRing.{u, u, u + 1} R).tensor.obj (K, L) ≅
      (DerivedInternalHom.Model.tensor R).obj (K, L)) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative.{u, u} K
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative.{u, u} L
  exact ⟨(derivedHomAdjunctionOverRing.{u, u, u + 1} R).tensor.mapIso
      (eP.symm.prod eQ.symm) ≪≫
    derivedTensorOverRing_iso_modelTensor_of_kFlat R P Q hQ ≪≫
    (DerivedInternalHom.Model.tensor R).mapIso (eP.prod eQ)⟩

end StacksDraft.DerivedHom

end
