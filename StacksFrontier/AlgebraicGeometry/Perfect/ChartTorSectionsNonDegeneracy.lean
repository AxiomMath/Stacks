module

public import StacksFrontier.AlgebraicGeometry.Perfect.ChartTorDimensionSectionsCrossing
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectNotFibrewise
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.DerivedTilde.Quasicoherent

/-!
# The chart crossing of Stacks 0DI2 at a named morphism and a nonzero object

`Scheme.Hom.exists_hasTorAmplitudeOver_resLE_iff_hasFiniteTorDimension_derivedSections`
is a biconditional with six binders — the morphism, the object, quasi-coherence of its cohomology
sheaves, the two affine opens and the inclusion between them. Instantiating all six at once with
named terms, at an object which is not a zero object, is what shows the statement is about
something.

The instance taken is the one the rest of this material uses: the structure morphism
`Spec k[ε] ⟶ Spec k` of the dual numbers over a field, which is flat and locally of finite
presentation, with the residue field of `k[ε]` placed in degree zero
(`AlgebraicGeometry.dualNumberResidueComplex`), and both affine opens taken to be `⊤`.

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_dualNumberResidueComplex`: the residue complex of
  `Spec k[ε]` lies in `D_QCoh`, which is the hypothesis the crossing asks of its object.
* `AlgebraicGeometry.not_isZero_and_exists_hasTorAmplitudeOver_iff_dualNumberResidueComplex`:
  **the certificate.** The residue complex is not a zero object, and the chart crossing holds of
  it on `⊤` over `⊤` with no binder left.

## Implementation notes

This asserts nothing the Stacks Project asserts and carries no `@[stacks]` attribute; it is a
certificate that the crossing is not vacuous, in the sense of the test that an instantiation of
every quantified binder by terms assuming nothing must elaborate. It does not claim that either
side of the biconditional holds at this instance: the sheaf side of the Tor-dimension clause
that is known to hold here, by
`AlgebraicGeometry.not_isZero_and_chartHasFiniteTorDimension_top_dualNumberResidueComplex`, is
the ringed-space reading, and joining it to the stalkwise reading is
`AlgebraicGeometry.Scheme.Hom.chartTorSpellingsAgree`.

## References

* [The Stacks Project, Lemma 36.35.3 (0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [The Stacks Project, Lemma 36.21.3 (0DHY)](https://stacks.math.columbia.edu/tag/0DHY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open StacksDraft.TorAmplitude
open AlgebraicGeometry.BaseChangeTorAmplitude
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The residue complex of `Spec k[ε]` has quasi-coherent cohomology sheaves.** It is the
sheafification of a module placed in degree zero, so its cohomology is that sheaf in degree zero
and zero elsewhere, and the sheafification of a module is quasi-coherent. -/
public theorem isQuasicoherent_homology_dualNumberResidueComplex (k : Type u) [Field k] (i : ℤ) :
    ((DerivedCategory.homologyFunctor
        (Spec (CommRingCat.of (DualNumber k))).Modules i).obj
      (dualNumberResidueComplex k)).IsQuasicoherent := by
  have e := (((tilde.functor (CommRingCat.of (DualNumber k))).mapDerivedCategorySingleFunctor
    0).app (ModuleCat.of _ (IsLocalRing.ResidueField (DualNumber k)))).symm
  refine ObjectProperty.prop_of_iso
    (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of (DualNumber k))).ringCatSheaf)
    ((DerivedCategory.homologyFunctor
      (Spec (CommRingCat.of (DualNumber k))).Modules i).mapIso e) ?_
  exact (DerivedCategoryB.derivedCategoryBPlus_singleFunctor_obj
    (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of (DualNumber k))).ringCatSheaf)
    (isQuasicoherent_isWeakSerre (CommRingCat.of (DualNumber k)))
    ((tilde.functor (CommRingCat.of (DualNumber k))).obj
      (ModuleCat.of _ (IsLocalRing.ResidueField (DualNumber k)))) inferInstance).2 i

/-- **The chart crossing of Stacks 0DI2 at a nonzero object, with no binder left.** Over the
structure morphism `Spec k[ε] ⟶ Spec k` of the dual numbers, the residue complex of `k[ε]` is
not a zero object, and for it the stalkwise sheaf-side Tor-dimension condition on the affine
open `⊤` over the affine open `⊤` is exactly finite Tor dimension of its complex of sections
over `k`.

Every binder of
`Scheme.Hom.exists_hasTorAmplitudeOver_resLE_iff_hasFiniteTorDimension_derivedSections`
is instantiated: the morphism by `AlgebraicGeometry.dualNumberStructureMap`, the object by
`AlgebraicGeometry.dualNumberResidueComplex`, the quasi-coherence hypothesis by
`AlgebraicGeometry.isQuasicoherent_homology_dualNumberResidueComplex`, the two affine opens by
`AlgebraicGeometry.isAffineOpen_top`, and the inclusion by `le_top`. -/
public theorem not_isZero_and_exists_hasTorAmplitudeOver_iff_dualNumberResidueComplex
    (k : Type u) [Field k] :
    ¬ IsZero (dualNumberResidueComplex k) ∧
      ((∃ a b : ℤ, HasTorAmplitudeOver
          ((dualNumberStructureMap k).resLE ⊤ ⊤ le_top)
          ((Scheme.Modules.restrictFunctor
            (⊤ : (Spec (CommRingCat.of (DualNumber k))).Opens).ι).mapDerivedCategory.obj
              (dualNumberResidueComplex k)) a b) ↔
        (letI : Algebra Γ(Spec (CommRingCat.of k), ⊤)
            Γ(Spec (CommRingCat.of (DualNumber k)), ⊤) :=
          ((dualNumberStructureMap k).appLE ⊤ ⊤ le_top).hom.toAlgebra
         HasFiniteTorDimension
           (PseudoCoherence.canonicalDerivedTensoringDatum
             Γ(Spec (CommRingCat.of k), ⊤)).tensor
           (PseudoCoherence.canonicalDerivedTensoringDatum
             Γ(Spec (CommRingCat.of k), ⊤)).comparison
           (PseudoCoherence.canonicalDerivedTensoringDatum
             Γ(Spec (CommRingCat.of k), ⊤)).isLeftDerived
           ((ModuleCat.restrictScalars (algebraMap Γ(Spec (CommRingCat.of k), ⊤)
               Γ(Spec (CommRingCat.of (DualNumber k)), ⊤))).mapDerivedCategory.obj
             ((derivedSectionsUnbounded (Spec (CommRingCat.of (DualNumber k))) ⊤).obj
               (dualNumberResidueComplex k))))) :=
  ⟨not_isZero_dualNumberResidueComplex k,
    Scheme.Hom.exists_hasTorAmplitudeOver_resLE_iff_hasFiniteTorDimension_derivedSections
      (dualNumberStructureMap k) (dualNumberResidueComplex k)
      (isQuasicoherent_homology_dualNumberResidueComplex k)
      (isAffineOpen_top (Spec (CommRingCat.of k)))
      (isAffineOpen_top (Spec (CommRingCat.of (DualNumber k)))) le_top⟩

end AlgebraicGeometry

end
