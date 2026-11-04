module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Composition
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletedLocalCohomologyLimit
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence

/-!
# Shrinking the support ideal does not change completed local cohomology

Let `I` and `J` be finitely generated ideals of a commutative ring `A` and let `M` be an
`A`-module. Write `RΓ_J(M)` for local cohomology with support in `V(J)` and `(-)^∧` for derived
`I`-adic completion. If `J'` is a further ideal with `V(J') ∩ V(I) = V(J) ∩ V(I)`, then

`RΓ_{J'}(M)^∧ = RΓ_I(RΓ_{J'}(M))^∧ = RΓ_{I + J'}(M)^∧ = RΓ_{I + J}(M)^∧ = RΓ_I(RΓ_J(M))^∧`
`= RΓ_J(M)^∧`,

the outer two identifications being Stacks 0A6W and the inner two Stacks 0BJC together with the
fact that local cohomology sees an ideal only through its zero locus. Composing the unit of
derived completion with this chain gives a canonical map `RΓ_{J'}(M) ⟶ RΓ_J(M)^∧`.

## Main definitions

* `Stacks.Algebraization.localCohomologyDerivedIsoOfZeroLocusEq` — local cohomology depends on
  its support ideal only through the zero locus of that ideal.
* `Stacks.Algebraization.localCohomologyDerivedCompIso` — `RΓ_I(RΓ_J(K)) ≅ RΓ_{J + I}(K)`, the
  composition isomorphism of Stacks 0BJC.
* `Stacks.Algebraization.completedLocalCohomologyCounitIso` — `RΓ_I(K)^∧ ≅ K^∧`, the
  content of Stacks 0A6W.
* `Stacks.Algebraization.completedLocalCohomologySupIso` — `RΓ_J(M)^∧ ≅ RΓ_{J + I}(M)^∧`.
* `Stacks.Algebraization.completedLocalCohomologyShrinkIso` — the chain above:
  `RΓ_{J'}(M)^∧ ≅ RΓ_J(M)^∧` whenever `V(J') ∩ V(I) = V(J) ∩ V(I)`.
* `Stacks.Algebraization.localCohomologyToCompletedLocalCohomology` — the canonical map
  `RΓ_{J'}(M) ⟶ RΓ_J(M)^∧`.

## Main results

* `Stacks.Algebraization.derivedPowerTorsionProperty_eq_of_zeroLocus_eq` — two ideals with the
  same zero locus cut out the same power-torsion objects of the derived category.
* `Stacks.Algebraization.zeroLocus_sup_inter_eq` — `V(J' + I) = V(J + I)` follows from
  `V(J') ∩ V(I) = V(J) ∩ V(I)`.

## Implementation notes

Local cohomology `Stacks.LocalCohomology.localCohomologyDerived` is the coreflection onto the
objects with power-torsion cohomology of Stacks 0A6Q, so it is `RΓ_{V(𝔞)}` by construction; its
comparison with the torsion model (Stacks 0955) is not used.

Derived completion is `Dualizing.derivedCompletion`, the reflection onto the derived
`I`-complete objects of `Dualizing.derivedCompletionReflection`, and
`Dualizing.completedLocalCohomology` is the composite `RΓ_J(M)^∧` named in Stacks 0EEW.

The module universe is the ring universe throughout, which is where
`Dualizing.completedLocalCohomology` lives.

## References

* [Stacks Project, Tag 0DXP](https://stacks.math.columbia.edu/tag/0DXP)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 0A6W](https://stacks.math.columbia.edu/tag/0A6W)
* [Stacks Project, Tag 0BJC](https://stacks.math.columbia.edu/tag/0BJC)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A]

/-- Two ideals with the same zero locus cut out the same power-torsion objects of the derived
category. -/
public theorem derivedPowerTorsionProperty_eq_of_zeroLocus_eq
    (A : Type u) [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (hzero : PrimeSpectrum.zeroLocus (J : Set A) = PrimeSpectrum.zeroLocus (I : Set A)) :
    Dualizing.derivedPowerTorsionProperty.{u, u} A J hJ =
      Dualizing.derivedPowerTorsionProperty.{u, u} A I hI := by
  funext K
  refine propext (forall_congr' fun i ↦ ?_)
  rw [isIPowerTorsion_iff_support_subset A _ J hJ, isIPowerTorsion_iff_support_subset A _ I hI,
    hzero]

/-- Local cohomology sees its support ideal only through the zero locus of that ideal: if
`V(J) = V(I)` then `RΓ_{V(J)}(K) ≅ RΓ_{V(I)}(K)`. -/
public def localCohomologyDerivedIsoOfZeroLocusEq
    (A : Type u) [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (hzero : PrimeSpectrum.zeroLocus (J : Set A) = PrimeSpectrum.zeroLocus (I : Set A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj K ≅
      (Stacks.LocalCohomology.localCohomologyDerived A I hI).obj K :=
  let E := ObjectProperty.fullSubcategoryCongr
    (derivedPowerTorsionProperty_eq_of_zeroLocus_eq A I J hI hJ hzero)
  have hIncl : E.functor ⋙ (Dualizing.derivedPowerTorsionProperty A I hI).ι ≅
      (Dualizing.derivedPowerTorsionProperty A J hJ).ι := Iso.refl _
  (Dualizing.derivedPowerTorsionProperty A J hJ).ι.mapIso
    (((Dualizing.localCohomologyAdjunction.{u, u} A J hJ).rightAdjointUniq
      ((E.toAdjunction.comp
        (Dualizing.localCohomologyAdjunction.{u, u} A I hI)).ofNatIsoLeft hIncl)).app K)

/-- Iterated local cohomology is local cohomology supported on the intersection of the supports:
`RΓ_I(RΓ_J(K)) ≅ RΓ_{J + I}(K)` in the derived category (Stacks 0BJC). -/
public def localCohomologyDerivedCompIso
    (A : Type u) [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (Stacks.LocalCohomology.localCohomologyDerived A I hI).obj
        ((Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj K) ≅
      (Stacks.LocalCohomology.localCohomologyDerived A (J + I)
        (Submodule.FG.sup hJ hI)).obj K :=
  (Dualizing.derivedPowerTorsionProperty A (J + I) (Submodule.FG.sup hJ hI)).ι.mapIso
    ((Dualizing.localCohomologyCompIso A J I hJ hI).app K)

/-- The isomorphism `RΓ_I(K)^∧ ≅ K^∧` given by derived `I`-adic completion of the counit
`RΓ_I(K) ⟶ K` (Stacks 0A6W). -/
public def completedLocalCohomologyCounitIso
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (Dualizing.derivedCompletion A I hI ⋙ (Dualizing.derivedCompleteProperty A I).ι).obj
        ((Stacks.LocalCohomology.localCohomologyDerived A I hI).obj K) ≅
      (Dualizing.derivedCompletion A I hI ⋙ (Dualizing.derivedCompleteProperty A I).ι).obj K :=
  @asIso _ _ _ _ _ (Dualizing.isIso_derivedCompletion_map_localCohomologyCounit A I hI
    (Dualizing.derivedCompletion A I hI) (Dualizing.derivedCompletionReflection A I hI).2 K)

/-- The isomorphism `RΓ_J(M)^∧ ≅ RΓ_{J + I}(M)^∧` of derived `I`-adic completions. -/
public def completedLocalCohomologySupIso
    (A : Type u) [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (M : ModuleCat.{u} A) :
    Dualizing.completedLocalCohomology A I J hI hJ M ≅
      Dualizing.completedLocalCohomology A I (J + I) hI (Submodule.FG.sup hJ hI) M :=
  (completedLocalCohomologyCounitIso A I hI
      ((Stacks.LocalCohomology.localCohomologyDerived A J hJ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))).symm ≪≫
    (Dualizing.derivedCompletion A I hI ⋙
      (Dualizing.derivedCompleteProperty A I).ι).mapIso
        (localCohomologyDerivedCompIso A I J hI hJ
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))

/-- If `V(J') ∩ V(I) = V(J) ∩ V(I)` then `V(J' + I) = V(J + I)`. -/
public theorem zeroLocus_sup_inter_eq
    (A : Type u) [CommRing A] (I J J' : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    PrimeSpectrum.zeroLocus ((J' + I : Ideal A) : Set A) =
      PrimeSpectrum.zeroLocus ((J + I : Ideal A) : Set A) := by
  rwa [Ideal.add_eq_sup, Ideal.add_eq_sup, PrimeSpectrum.zeroLocus_sup,
    PrimeSpectrum.zeroLocus_sup]

/-- For ideals `J'` and `J` with `V(J') ∩ V(I) = V(J) ∩ V(I)`, the derived `I`-adic completions
of `RΓ_{J'}(M)` and of `RΓ_J(M)` agree:

`RΓ_{J'}(M)^∧ = RΓ_{J' + I}(M)^∧ = RΓ_{J + I}(M)^∧ = RΓ_J(M)^∧`. -/
public def completedLocalCohomologyShrinkIso
    (A : Type u) [CommRing A] (I J J' : Ideal A) (hI : I.FG) (hJ : J.FG) (hJ' : J'.FG)
    (M : ModuleCat.{u} A)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    Dualizing.completedLocalCohomology A I J' hI hJ' M ≅
      Dualizing.completedLocalCohomology A I J hI hJ M :=
  completedLocalCohomologySupIso A I J' hI hJ' M ≪≫
    (Dualizing.derivedCompletion A I hI ⋙
      (Dualizing.derivedCompleteProperty A I).ι).mapIso
        (localCohomologyDerivedIsoOfZeroLocusEq A (J + I) (J' + I)
          (Submodule.FG.sup hJ hI) (Submodule.FG.sup hJ' hI)
          (zeroLocus_sup_inter_eq A I J J' hV)
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ≪≫
    (completedLocalCohomologySupIso A I J hI hJ M).symm

/-- For ideals `J'` and `J` with `V(J') ∩ V(I) = V(J) ∩ V(I)`, the canonical map
`RΓ_{J'}(M) ⟶ RΓ_J(M)^∧`: the unit of derived `I`-adic completion at `RΓ_{J'}(M)`, followed by
the identification `Stacks.Algebraization.completedLocalCohomologyShrinkIso`. -/
public def localCohomologyToCompletedLocalCohomology
    (A : Type u) [CommRing A] (I J J' : Ideal A) (hI : I.FG) (hJ : J.FG) (hJ' : J'.FG)
    (M : ModuleCat.{u} A)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    (Stacks.LocalCohomology.localCohomologyDerived A J' hJ').obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ⟶
      Dualizing.completedLocalCohomology A I J hI hJ M :=
  (Dualizing.derivedCompletionReflection A I hI).2.unit.app
      ((Stacks.LocalCohomology.localCohomologyDerived A J' hJ').obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ≫
    (completedLocalCohomologyShrinkIso A I J J' hI hJ hJ' M hV).hom

end Stacks.Algebraization

end
