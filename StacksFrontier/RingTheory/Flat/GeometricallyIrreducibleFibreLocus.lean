module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.AffineApproximationFibre
public import StacksFrontier.RingTheory.GeometricallyIntegral.FibreLocusSchemeBridge
public import StacksFrontier.RingTheory.GeometricallyIntegral.GoodIrreducible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The geometrically irreducible fibre locus is constructible

Stacks 055B says that the level sets of the number of geometrically irreducible components of the
fibres of a morphism of finite presentation are locally constructible. Its scheme-level statement
is proved in `StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.ShrinkingConsequences`.
This file transports the level set at `1` to the affine, ring-theoretic form that the Noetherian
approximation of Stacks 05FT consumes: `Algebra.geometricallyIrreducibleFibreLocus A C` is a
constructible subset of `Spec A` whenever `A` is Noetherian and `C` is a finite type `A`-algebra.

Together with `Algebra.isConstructible_geometricallyIntegralFibreLocus` this removes one of the
two hypotheses of `Algebra.projective_of_geometricallyIntegral_fibres_of_isConstructible_halves`,
so that Stacks 05FT now rests on the affine case of Stacks 0579 — constructibility of the
geometrically *reduced* fibre locus — and on nothing else.

## Main results

* `Algebra.geometricallyIrreducible_iff_forall_irreducibleSpace_tensorProduct`: the fibrewise form
  of geometric irreducibility for a ring map, the irreducible analogue of
  `Algebra.geometricallyIntegral_iff_forall_isDomain_tensorProduct`.
* `Algebra.isConstructible_geometricallyIrreducibleFibreLocus_of_finiteType`: the affine case of
  the level set `n = 1` of Stacks 055B, **unconditionally**.
* `Algebra.projective_of_geometricallyIntegral_fibres_of_isConstructible_reduced`: Stacks 05FT
  granted the affine case of Stacks 0579 alone.

## Implementation notes

The comparison of the two readings of the fibre condition at a prime `p` is
`Algebra.mem_geometricallyIrreducibleFibreLocus_iff_fiberToSpecResidueField`, which lives in
`StacksFrontier.RingTheory.GeometricallyIntegral.FibreLocusSchemeBridge` and is imported here. Its
content is Mathlib's `AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso`, an isomorphism of
*arrows* between the scheme-theoretic fibre of `Spec C ⟶ Spec A` at `p` and
`Spec (κ(p) ⊗[A] C) ⟶ Spec κ(p)` — geometric irreducibility is a morphism property stable under
base change, hence invariant under such an isomorphism — together with the collapse of the
quantifier over all fields `K` over `A` with `ker (A → K) = p` to the quantifier over all field
extensions of `κ(p)`.

Local constructibility becomes constructibility because `Spec A` is quasi-compact, through
`Topology.IsLocallyConstructible.isConstructible_of_subset_of_isCompact`; no Noetherian
hypothesis is needed for that step. The Noetherian hypothesis is used only to upgrade finite type
to finite presentation, which is what Stacks 055B asks of the morphism.

## References

* [Stacks Project, Tag 055B](https://stacks.math.columbia.edu/tag/055B)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat Topology

open scoped TensorProduct

universe u

namespace Algebra

/-- **The fibrewise form of geometric irreducibility for a ring map.** `Spec S ⟶ Spec R` is
geometrically irreducible exactly when `Spec (S ⊗[R] K)` is irreducible for every field `K`
carrying an `R`-algebra structure.

This is the irreducible analogue of
`Algebra.geometricallyIntegral_iff_forall_isDomain_tensorProduct` and has the same proof: the
quantifier of `AlgebraicGeometry.geometrically` over field-valued points of the base is read on
an affine chart through `AlgebraicGeometry.pullbackSpecIso`. -/
public theorem geometricallyIrreducible_iff_forall_irreducibleSpace_tensorProduct
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap R S))) ↔
      ∀ (K : Type u) [Field K] [Algebra R K], IrreducibleSpace (PrimeSpectrum (S ⊗[R] K)) := by
  rw [geometricallyIrreducible_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  refine forall_congr' fun K => ?_
  exact ⟨fun h _ _ => (pullbackSpecIso R S K).hom.homeomorph.irreducibleSpace_iff.1 (h ..),
    fun h _ _ => (pullbackSpecIso R S K).hom.homeomorph.irreducibleSpace_iff.2 h⟩

/-- The fibre `κ(p) ⊗[A] C` of `C` at a prime `p`, base changed along a field extension `L` of
`κ(p)`, is the fibre `C ⊗[A] L` of `C` at the field-valued point `L`. -/
public noncomputable def fibreBaseChangeEquiv (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] (p : Ideal A) [p.IsPrime] (L : Type u) [Field L] [Algebra p.ResidueField L]
    [Algebra A L] [IsScalarTower A p.ResidueField L] :
    ((p.Fiber C) ⊗[p.ResidueField] L) ≃+* (C ⊗[A] L) :=
  ((Algebra.TensorProduct.comm p.ResidueField (p.Fiber C) L).toRingEquiv).trans
    (((Algebra.TensorProduct.cancelBaseChange A p.ResidueField L L C).toRingEquiv).trans
      (Algebra.TensorProduct.comm A L C).toRingEquiv)

/-- **The affine case of the level set `n = 1` of Stacks 055B.** For a Noetherian ring `A` and a
finite type `A`-algebra `C`, the geometrically irreducible fibre locus of `C` is a constructible
subset of `Spec A`.

Over a Noetherian ring a finite type algebra is of finite presentation, so Stacks 055B applies to
`Spec C ⟶ Spec A` and makes the locus of geometrically irreducible fibres locally constructible;
`Algebra.mem_geometricallyIrreducibleFibreLocus_iff_fiberToSpecResidueField` identifies that
locus with this one, and `Spec A` being quasi-compact upgrades local constructibility to
constructibility.

This discharges the hypothesis `hirr` of
`Algebra.projective_of_geometricallyIntegral_fibres_of_isConstructible_halves`. -/
@[ega "IV 9.7.7" "(i), special case"]
public theorem isConstructible_geometricallyIrreducibleFibreLocus_of_finiteType
    (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] :
    IsConstructible (geometricallyIrreducibleFibreLocus A C) := by
  have : Algebra.FinitePresentation A C := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have hlfp : LocallyOfFinitePresentation (Spec.map (ofHom (algebraMap A C))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      (RingHom.finitePresentation_algebraMap.2 ‹_›)
  have hloc : IsLocallyConstructible (geometricallyIrreducibleFibreLocus A C) := by
    have hset : geometricallyIrreducibleFibreLocus A C =
        {y : ↥(Spec (.of A)) |
          GeometricallyIrreducible
            ((Spec.map (ofHom (algebraMap A C))).fiberToSpecResidueField y)} :=
      Set.ext fun p => mem_geometricallyIrreducibleFibreLocus_iff_fiberToSpecResidueField A C p
    rw [hset]
    exact isLocallyConstructible_geometricallyIrreducible_fiber _
      ⟨hlfp, inferInstance, inferInstance⟩
  exact hloc.isConstructible_of_subset_of_isCompact (Set.subset_univ _) isCompact_univ

/-- **Stacks 05FT granted the affine case of Stacks 0579 alone.** Let `R → S` be flat of finite
presentation with geometrically integral fibres. If over every Noetherian ring the geometrically
*reduced* fibre locus of a finite type algebra is constructible, then `S` is a projective
`R`-module.

This is `Algebra.projective_of_geometricallyIntegral_fibres_of_isConstructible_halves` with its
second hypothesis — the affine case of the level set `n = 1` of Stacks 055B — discharged by
`Algebra.isConstructible_geometricallyIrreducibleFibreLocus_of_finiteType`. By
`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus_iff_isConstructible` the
remaining hypothesis is interchangeable with the good half of Stacks 0578 at the generic point of
an integral base, and it is the only thing between this statement and Stacks 05FT. -/
public theorem projective_of_geometricallyIntegral_fibres_of_isConstructible_reduced
    (hred : ∀ (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
      [Algebra.FiniteType A C], IsConstructible (geometricallyReducedFibreLocus A C))
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      letI : Algebra p.ResidueField (S ⊗[R] p.ResidueField) :=
        Algebra.TensorProduct.rightAlgebra
      Algebra.IsGeometricallyIntegral p.ResidueField (S ⊗[R] p.ResidueField)) :
    Module.Projective R S :=
  projective_of_geometricallyIntegral_fibres_of_isConstructible_halves hred
    (fun A C _ _ _ _ _ => isConstructible_geometricallyIrreducibleFibreLocus_of_finiteType A C) h

/-- **The remaining hypothesis of Stacks 05FT, in the form the complete dévissage consumes it.**
Constructibility of the geometrically *integral* fibre locus over a Noetherian base follows from
constructibility of the geometrically *reduced* one, the irreducible half being
`Algebra.isConstructible_geometricallyIrreducibleFibreLocus_of_finiteType` and the two halves
meeting through `Algebra.isConstructible_geometricallyIntegralFibreLocus` (Stacks 05DY). -/
public theorem isConstructible_geometricallyIntegralFibreLocus_of_isConstructible_reduced
    (hred : ∀ (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
      [Algebra.FiniteType A C], IsConstructible (geometricallyReducedFibreLocus A C))
    (A C : Type u) [CommRing A] [IsNoetherianRing A] [CommRing C] [Algebra A C]
    [Algebra.FiniteType A C] :
    IsConstructible (geometricallyIntegralFibreLocus A C) :=
  isConstructible_geometricallyIntegralFibreLocus A C
    (isConstructible_geometricallyIrreducibleFibreLocus_of_finiteType A C) (hred A C)

end Algebra

end
