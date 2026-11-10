module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison

/-!
# The relative dualizing module does not depend on the factorization

The relative dualizing module `ω_{B/A} = Hom_A(B', A) ⊗_{B'} B` of Tag 0BSZ is computed from a
finite-open factorization `A → B' → B`, and a quasi-finite map of Noetherian rings admits many
such factorizations. That the module is independent of the factorization is the content of
`StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleChange` (comparison of the module
computed from a factorization with the one computed from a larger finite algebra inside `B`) and
`StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison` (the canonical comparison
`Stacks.Discriminant.dualizingModuleEquiv` of two factorizations, and its coherence), both of
which this file re-exports.

What remains here is the ring epimorphism half of the flatness/epimorphism pair that the
comparison rests on, obtained by descent along `ULift`.

## Main results

* `Stacks.Discriminant.algebraEpi_of_ulift`: being an epimorphism of algebras descends along
  `ULift`.
* `Stacks.Discriminant.finiteOpenFactorization_epi`: the algebra map of a finite-open
  factorization is an epimorphism of rings.

## Implementation notes

`finiteOpenFactorization_epi` goes through
`Stacks.Discriminant.specMap_ulift_isOpenImmersion`, which upgrades the affine ring-theoretic
open-immersion data recorded in `Stacks.Discriminant.FiniteOpenFactorization` to a
scheme-theoretic open immersion. The `ULift` appears only because `Spec` needs its two rings in
one universe, and the factorization's intermediate algebra is deliberately left in an
independent universe; `algebraEpi_of_ulift` is what brings the conclusion back down.

## References

* [Stacks Project, Tag 0BT1](https://stacks.math.columbia.edu/tag/0BT1)
* [Stacks Project, Tag 0BT0](https://stacks.math.columbia.edu/tag/0BT0)
* [Stacks Project, Tag 0BSZ](https://stacks.math.columbia.edu/tag/0BSZ)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped TensorProduct

universe u v w

namespace Stacks.Discriminant

/-- If the `ULift` of an algebra map is an epimorphism of algebras, so is the map itself. -/
theorem algebraEpi_of_ulift
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (h : letI : Algebra (ULift.{w} R) (ULift.{w} S) := ULift.algebra' R (ULift.{w} S)
      Algebra.IsEpi (ULift.{w} R) (ULift.{w} S)) : Algebra.IsEpi R S := by
  let : Algebra (ULift.{w} R) (ULift.{w} S) := ULift.algebra' R (ULift.{w} S)
  rw [Algebra.isEpi_iff_forall_one_tmul_eq] at h ⊢
  intro s
  let e : ULift.{w} (S ⊗[R] S) ≃ₐ[R]
      ULift.{w} S ⊗[ULift.{w} R] ULift.{w} S :=
    Algebra.TensorProduct.uliftEquiv.{w, w, w, w} R R S S
  have hs := congrArg e.symm (h (ULift.up s))
  dsimp [e] at hs
  simp only [Algebra.TensorProduct.uliftEquiv_symm_tmul] at hs
  simpa using congrArg ULift.down hs

/-- The algebra map of a finite-open factorization is an epimorphism of rings: the induced
morphism of spectra is an open immersion, hence a monomorphism of schemes. -/
theorem finiteOpenFactorization_epi
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) : Algebra.IsEpi F.middle B := by
  let f : F.middle →+* B := algebraMap F.middle B
  let fU : ULift.{max v w} F.middle →+* ULift.{max v w} B :=
    f.ulift.{max v w, max v w}
  have hOpen := specMap_ulift_isOpenImmersion f
    F.isOpenEmbedding_comap F.awayMap_bijective
  have hEpi : Epi (CommRingCat.ofHom fU) := by
    apply (op_mono_iff _).mp
    apply (Functor.mono_map_iff_mono AlgebraicGeometry.Scheme.Spec _).mp
    change Mono (AlgebraicGeometry.Scheme.Spec.map (CommRingCat.ofHom fU).op)
    rw [AlgebraicGeometry.Scheme.Spec_map]
    exact inferInstanceAs (Mono (AlgebraicGeometry.Spec.map (CommRingCat.ofHom fU)))
  let : Algebra (ULift.{max v w} F.middle) (ULift.{max v w} B) :=
    ULift.algebra' F.middle (ULift.{max v w} B)
  exact algebraEpi_of_ulift (R := F.middle) (S := B)
    (CommRingCat.epi_iff_epi.mp hEpi)

end Stacks.Discriminant

end
