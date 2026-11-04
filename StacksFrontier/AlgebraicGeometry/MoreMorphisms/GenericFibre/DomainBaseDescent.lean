module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.AwayModel
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.SpecModel
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FunctionFieldEssFiniteType
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyReducedOfTensor

/-!
# Steps B to F of Stacks Tag 0559 over a domain base

The first proof of Stacks Tag 0559 from Step B to the end, over the spectrum of a domain. The
hypersurface model of the function field is produced over the fraction field `K` of the base ring
`R` by Step B, descended to a localization `R_a` of `R` away from one nonzero element by Steps C
and F (`AlgebraicGeometry.exists_away_specModel`), and handed to the assembly of Steps D, E and F
over the principal open `D(a) ⊆ Spec R`
(`AlgebraicGeometry.exists_open_geometricallyIrreducible_of_awayModel`).

The fraction field of `R` is realized as the residue field of `Spec R` at its generic point
(`AlgebraicGeometry.isFractionRing_specResidueField_genericPoint`) and the function field of `X`
as the residue field of `X` at its generic point; the extension between them is the residue field
map of `f`, and the two hypotheses on it that Step B needs — being essentially of finite type and
geometrically reduced — come from `f` being locally of finite type
(`AlgebraicGeometry.essFiniteType_specResidueField_residueField`) and from the one hypothesis of
this module (`Algebra.isGeometricallyReduced_of_isDomain_tensor_isAlgClosure`).

## The remaining hypothesis

What is assumed here is that `κ(ηₓ) ⊗_K K̄` is a domain, for `K̄` an algebraic closure of `K`;
equivalently, that the function field of the generic fibre of `f` stays a domain after one base
change to an algebraically closed field. It is the same hypothesis that Step B is stated with
(`AlgebraicGeometry.exists_mvPolynomial_model_residueField`). In the source it is read off the
generic fibre being geometrically integral, which is not available in the library: the passage
from a geometrically integral scheme to the residue field at its generic point is a separate
piece of work, and nothing in this directory claims it.

## Main results

* `AlgebraicGeometry.exists_open_geometricallyIrreducible_of_isDomain_tensor`: **Steps B to F of
  Stacks Tag 0559 over a domain base.**

## Implementation notes

The `S`-algebra structure on the function field is the one induced by the lift of evaluation at
the chosen generators through the quotient, which is the map
`AlgebraicGeometry.exists_away_specModel` characterizes its field of fractions clause by.

No Stacks tag is attached: Steps B to F are not themselves tags of the source, and the result
still carries a hypothesis.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), the first proof
-/

@[expose] public section

open CategoryTheory MvPolynomial

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **Steps B to F of Stacks Tag 0559 over a domain base.** Let `R` be a domain and let
`f : X ⟶ Spec R` be a finite type morphism with `X` integral, whose generic point lies over the
generic point of `Spec R` and whose fibre there is geometrically irreducible. If the residue
field of `X` at its generic point stays a domain after base change to an algebraic closure of the
residue field of `Spec R` at its generic point, then `X` has geometrically irreducible fibres
over a nonempty open subscheme of `Spec R`. -/
theorem exists_open_geometricallyIrreducible_of_isDomain_tensor (R : CommRingCat.{u}) [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec R) [IsIntegral X] [LocallyOfFiniteType f] [QuasiCompact f]
    (hgen : f (genericPoint X) = genericPoint (Spec R))
    (hgi : GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint (Spec R))))
    (hdom : letI := residueFieldAlgebraOfEq f hgen
      IsDomain (X.residueField (genericPoint X) ⊗[(Spec R).residueField (genericPoint (Spec R))]
        AlgebraicClosure ((Spec R).residueField (genericPoint (Spec R))))) :
    ∃ V : (Spec R).Opens, Nonempty V ∧ GeometricallyIrreducible (f ∣_ V) := by
  let _ := specResidueFieldAlgebra R (genericPoint (Spec R))
  let _ := residueFieldAlgebraOfEq f hgen
  have _ : IsFractionRing ↥R ↥((Spec R).residueField (genericPoint (Spec R))) :=
    isFractionRing_specResidueField_genericPoint R
  have _ : Algebra.EssFiniteType ↥((Spec R).residueField (genericPoint (Spec R)))
      ↥(X.residueField (genericPoint X)) :=
    essFiniteType_specResidueField_residueField R f hgen
  have _ : Algebra.IsGeometricallyReduced ↥((Spec R).residueField (genericPoint (Spec R)))
      ↥(X.residueField (genericPoint X)) :=
    Algebra.isGeometricallyReduced_of_isDomain_tensor_isAlgClosure _ _
      (AlgebraicClosure ↥((Spec R).residueField (genericPoint (Spec R)))) hdom
  obtain ⟨a, n, v, ι, P, ha, hιcomp, -, hker, hSdom, hSinj, hSlft, hSgi, hSfrac⟩ :=
    exists_away_specModel ↥R ↥((Spec R).residueField (genericPoint (Spec R)))
      ↥(X.residueField (genericPoint X))
      (AlgebraicClosure ↥((Spec R).residueField (genericPoint (Spec R)))) hdom
  -- Evaluation at the chosen generators, lifted through the quotient.
  let E : MvPolynomial (Fin (n + 1)) ↥((Spec R).residueField (genericPoint (Spec R))) →ₐ[_]
      ↥(X.residueField (genericPoint X)) := aeval v
  have hPker : Ideal.span {P} ≤ RingHom.ker (E.toRingHom.comp (MvPolynomial.map ι)) := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    have hmem : P.map ι ∈ RingHom.ker E.toRingHom := by
      rw [show RingHom.ker E.toRingHom = _ from hker]
      exact Ideal.mem_span_singleton_self _
    exact hmem
  let ψ : (MvPolynomial (Fin (n + 1)) (Localization.Away a) ⧸ Ideal.span {P}) →+*
      ↥(X.residueField (genericPoint X)) :=
    Ideal.Quotient.lift (Ideal.span {P}) (E.toRingHom.comp (MvPolynomial.map ι))
      fun _ hx ↦ hPker hx
  have hψcomp : ψ.comp (Ideal.Quotient.mk (Ideal.span {P})) =
      E.toRingHom.comp (MvPolynomial.map ι) := RingHom.ext fun _ ↦ rfl
  -- The model, as a ring in `CommRingCat` with its structure morphism.
  let S : CommRingCat.{u} :=
    CommRingCat.of (MvPolynomial (Fin (n + 1)) (Localization.Away a) ⧸ Ideal.span {P})
  have _ : IsDomain ↥S := hSdom
  let _ : Algebra ↥S ↥(X.residueField (genericPoint X)) := ψ.toAlgebra
  let φ : CommRingCat.of (Localization.Away a) ⟶ S :=
    CommRingCat.ofHom (algebraMap (Localization.Away a)
      (MvPolynomial (Fin (n + 1)) (Localization.Away a) ⧸ Ideal.span {P}))
  have _ : LocallyOfFiniteType (Spec.map φ) := hSlft
  have _ : GeometricallyIrreducible (Spec.map φ) := hSgi
  have hfrac : IsFractionRing ↥S ↥(X.residueField (genericPoint X)) := hSfrac ψ hψcomp
  -- The two `R`-algebra structures on the function field agree.
  have hval : ∀ r : ↥R, ψ (algebraMap (Localization.Away a)
      (MvPolynomial (Fin (n + 1)) (Localization.Away a) ⧸ Ideal.span {P})
      (algebraMap ↥R (Localization.Away a) r)) =
      algebraMap ↥((Spec R).residueField (genericPoint (Spec R)))
        ↥(X.residueField (genericPoint X))
        (algebraMap ↥R ↥((Spec R).residueField (genericPoint (Spec R))) r) := by
    intro r
    change E (MvPolynomial.map ι (C (algebraMap ↥R (Localization.Away a) r))) = _
    rw [MvPolynomial.map_C, MvPolynomial.aeval_C,
      show ι (algebraMap ↥R (Localization.Away a) r) =
        algebraMap ↥R ↥((Spec R).residueField (genericPoint (Spec R))) r from
        RingHom.congr_fun hιcomp r]
  have hmodel : CommRingCat.ofHom (algebraMap ↥R (Localization.Away a)) ≫ φ ≫
      CommRingCat.ofHom (algebraMap ↥S ↥(X.residueField (genericPoint X))) =
      (Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.Γevaluation (genericPoint X) := by
    rw [← algebraMap_comp_residueFieldMapOfEq R f hgen]
    exact CommRingCat.hom_ext (RingHom.ext hval)
  exact exists_open_geometricallyIrreducible_of_awayModel f hgen hgi ha φ hSinj hfrac hmodel

/-- The input of Step B of Stacks Tag 0559, as a statement about every morphism the reduced form
of the tag is applied to: the residue field at the generic point of the source stays a domain
after one base change to an algebraic closure of the residue field at the generic point of the
base. In the source this is read off the generic fibre being geometrically integral. -/
def GenericResidueFieldIsDomainTensor : Prop :=
  ∀ (R : CommRingCat.{u}) [IsDomain R] {X : Scheme.{u}} (f : X ⟶ Spec R) [IsIntegral X]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (hgen : f (genericPoint X) = genericPoint (Spec R)),
      GeometricallyIrreducible (f.fiberToSpecResidueField (genericPoint (Spec R))) →
      GeometricallyReduced (f.fiberToSpecResidueField (genericPoint (Spec R))) →
      letI := residueFieldAlgebraOfEq f hgen
      IsDomain (X.residueField (genericPoint X) ⊗[(Spec R).residueField (genericPoint (Spec R))]
        AlgebraicClosure ((Spec R).residueField (genericPoint (Spec R))))

/-- **Stacks Tag 0559 over a domain base, reduced to Step B's input.** The special case of
Tag 0559 that Step A reduces the tag to follows from
`AlgebraicGeometry.GenericResidueFieldIsDomainTensor`. The hypothesis that the generic point of
the source lies over the generic point of the base, which is not part of that special case, is
supplied by its geometrically irreducible generic fibre
(`AlgebraicGeometry.map_genericPoint_of_geometricallyIrreducible_fiber`). -/
theorem geometricallyIrreducibleAfterShrinkingOverDomain_of_isDomainTensor
    (H : GenericResidueFieldIsDomainTensor.{u}) :
    GeometricallyIrreducibleAfterShrinkingOverDomain.{u} := by
  intro R _ X f hint hlft hqc _ _ hgi hgr
  have hint' : IsIntegral X := hint
  have hlft' : LocallyOfFiniteType f := hlft
  have hqc' : QuasiCompact f := hqc
  have hirr : IrreducibleSpace X := irreducibleSpace_of_isIntegral X
  have hgen : f (genericPoint X) = genericPoint (Spec R) :=
    map_genericPoint_of_geometricallyIrreducible_fiber f
      (by simpa using genericPoint_spec (Spec R)) hgi
  exact exists_open_geometricallyIrreducible_of_isDomain_tensor R f hgen hgi
    (H R f hgen hgi hgr)

/-- **Stacks Tag 0559, reduced to Step B's input.** The conclusion of Tag 0559 follows from
`AlgebraicGeometry.GenericResidueFieldIsDomainTensor`, through Step A
(`AlgebraicGeometry.geometricallyIrreducibleAfterShrinking_of_overDomain`). -/
theorem geometricallyIrreducibleAfterShrinking_of_isDomainTensor
    (H : GenericResidueFieldIsDomainTensor.{u}) :
    GeometricallyIrreducibleAfterShrinking.{u} :=
  geometricallyIrreducibleAfterShrinking_of_overDomain
    (geometricallyIrreducibleAfterShrinkingOverDomain_of_isDomainTensor H)

end AlgebraicGeometry

end
