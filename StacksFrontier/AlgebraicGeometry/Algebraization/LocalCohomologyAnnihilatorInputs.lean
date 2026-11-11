module

public import StacksFrontier.RingTheory.LocalCohomology.AnnihilatorLocalCohomologyI
public import StacksFrontier.RingTheory.LocalCohomology.BoundedBelow
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.CohomologicalDimension
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.HighBoundTFAE
import StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator

/-!
# Boundedness and annihilator inputs for completed local cohomology

Let `I` and `J` be ideals of a Noetherian ring `A` and let `M` be a finite `A`-module. The
truncation argument annihilating the cohomology of `RHom_A(RΓ_I(A), RΓ_{I+J}(M))` needs three
inputs about the two sides: that `RΓ_I(A)` lies in degrees `≤ d` when the cohomological dimension
of `I` is at most `d`; that `RΓ_{I+J}(M[0])` lies in degrees `≥ 0`; and, for every degree
`j ≤ s + d`, an element outside a given prime annihilating `H^j_{V(I+J)}(M)`.

This file supplies them, in both models of local cohomology that the library carries: the
support-indexed `Stacks.LocalCohomology.derivedSectionsWithSupportIn` and the coreflection
`Dualizing.localCohomologyFunctor` of Stacks 0A6Q, which agree over a Noetherian ring by
Stacks 0955.

## Main results

* `Stacks.LocalCohomology.isZero_localCohomologyModule_of_cohomologicalDimension_le` and
  `Stacks.LocalCohomology.isLE_localCohomologyDerived_single_of_cohomologicalDimension_le` —
  a bound on the cohomological dimension of `I` makes `RΓ_{V(I)}(M[0])` an object of degrees
  `≤ d`, in the coreflection model.
* `Stacks.LocalCohomology.derivedSectionsWithSupportInIsoLocalCohomologyDerived` — the
  identification of the two models over a Noetherian ring, as a natural isomorphism.
* `Stacks.LocalCohomology.isZero_localCohomologyWithSupportIn_of_cohomologicalDimension_le` and
  `Stacks.LocalCohomology.isLE_derivedSectionsWithSupportIn_single_of_cohomologicalDimension_le`
  — the same bound in the support-indexed model.
* `Stacks.LocalCohomology.isGE_localCohomologyDerived_single` — `RΓ_{V(I)}(M[0])` lies in
  degrees `≥ 0`, in the coreflection model.
* `Stacks.LocalCohomology.exists_notMem_mem_annihilator_localCohomologyWithSupportIn_of_dualizing`
  — Stacks 0EFE, deduced from Faltings' annihilator theorem, Stacks 0EFC.
* `Stacks.LocalCohomology.exists_notMem_mem_annihilator_localCohomologyWithSupportIn_sup` and
  `Stacks.LocalCohomology.exists_notMem_mem_annihilator_localCohomologyModule_sup` — for a prime
  outside `V(I) ∩ V(J)`, one element outside it annihilating `H^j_{V(I+J)}(M)` in every degree
  `j ≤ s + d`, in each of the two models.

## Implementation notes

The vanishing above the cohomological dimension is Stacks 0DX7: a bound `cd(A, I) ≤ d` upgrades
to `IsLocalCohomologyBound A I hI d` because the cohomological dimension is itself a bound, and
the second clause of the equivalence `Stacks.LocalCohomology.localCohomology_vanishing_tfae`
propagates the vanishing from `A` to an arbitrary module.

The lower bound is `Stacks.LocalCohomology.isGE_derivedSectionsWithSupportIn_single`, which holds
over any ring in the support-indexed model; it is transported to the coreflection model along
Stacks 0955.

The hypothesis `hFaltings` of
`Stacks.LocalCohomology.exists_notMem_and_mem_annihilator_localCohomologyWithSupportIn` is
exactly the statement of `Stacks.LocalCohomology.exists_ideal_le_annihilator_localCohomology_iff`
— Stacks 0EFC — quantified over the two supports, the degree and the dualizing complex, so it is
discharged by that theorem.

No degree bound `0 ≤ s + d` is needed in the combined statements: in negative degrees the local
cohomology of a module vanishes, so `1` annihilates it, and Stacks 0EFE is invoked only when some
degree in the range is nonnegative.

## References

* [Stacks Project, Tag 0EFH](https://stacks.math.columbia.edu/tag/0EFH)
* [Stacks Project, Tag 0EFE](https://stacks.math.columbia.edu/tag/0EFE)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
* [Stacks Project, Tag 0DX7](https://stacks.math.columbia.edu/tag/0DX7)
* [Stacks Project, Tag 0DX8](https://stacks.math.columbia.edu/tag/0DX8)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.Algebraization (enatToEInt krullDimToEInt)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- The local cohomology `H^i_{V(I)}(M)` of any module vanishes in every degree `i` strictly
above a bound `d` on the cohomological dimension of `I`. -/
theorem isZero_localCohomologyModule_of_cohomologicalDimension_le
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ)
    (hcd : cohomologicalDimension A I hI ≤ d) (M : ModuleCat.{u} A) (i : ℤ) (hi : d < i) :
    IsZero (localCohomologyModule A I hI M i) := by
  have hb := isLocalCohomologyBound_cohomologicalDimension A I hI
  have hd : (-1 : ℤ) ≤ d := hb.1.trans hcd
  have hvan : ∀ j : ℤ, d < j → IsZero (localCohomologyModule A I hI (ModuleCat.of A A) j) :=
    fun j hj => hb.2 j (lt_of_le_of_lt hcd hj)
  refine (((localCohomology_vanishing_tfae.{u, u} A I hI d hd).out 1 2
    (a := ∀ j : ℤ, d < j → IsZero (localCohomologyModule A I hI (ModuleCat.of A A) j))
    (b := ∀ (N : ModuleCat.{u} A) (j : ℤ), d < j →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
        ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
          ((Dualizing.localCohomologyFunctor A I hI).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)))))).mp hvan) M i hi

/-- A bound `d` on the cohomological dimension of `I` places the local cohomology
`RΓ_{V(I)}(M[0])` of Stacks 0A6Q in degrees `≤ d`. -/
@[stacks 0EFH "the use of hypothesis (3): `H^i(RΓ_I(A)) = 0` for `i > d` when `cd(A, I) ≤ d`"]
theorem isLE_localCohomologyDerived_single_of_cohomologicalDimension_le
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ)
    (hcd : cohomologicalDimension A I hI ≤ d) (M : ModuleCat.{u} A) :
    ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
      ((Dualizing.localCohomologyFunctor A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))).IsLE d :=
  (DerivedCategory.isLE_iff _ d).mpr fun i hi =>
    isZero_localCohomologyModule_of_cohomologicalDimension_le A I hI d hcd M i hi

/-- **The two models of local cohomology agree over a Noetherian ring**, as a natural
isomorphism: derived sections with support in `V(I)` and the coreflection `RΓ_{V(I)}` of
Stacks 0A6Q are identified by the canonical comparison of Stacks 0A6U. -/
def derivedSectionsWithSupportInIsoLocalCohomologyDerived
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG) :
    derivedSectionsWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A)) ≅
      Dualizing.localCohomologyFunctor.{u, u} A I hI ⋙
        (Dualizing.derivedPowerTorsionProperty A I hI).ι :=
  have := isIso_compareSectionsWithSupportLocalCohomology.{u, u} A I hI
  asIso (compareSectionsWithSupportLocalCohomology.{u, u} A I hI)

/-- The local cohomology `H^i_{V(I)}(M)` with support in `V(I)` vanishes in every degree `i`
strictly above a bound `d` on the cohomological dimension of `I`. -/
theorem isZero_localCohomologyWithSupportIn_of_cohomologicalDimension_le
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG) (d : ℤ)
    (hcd : cohomologicalDimension A I hI ≤ d) (M : ModuleCat.{u} A) (i : ℤ) (hi : d < i) :
    IsZero (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i) :=
  (isZero_localCohomologyModule_of_cohomologicalDimension_le A I hI d hcd M i hi).of_iso
    (localCohomologyWithSupportInIsoLocalCohomologyModule A I hI M i)

/-- A bound `d` on the cohomological dimension of `I` places the derived sections with support in
`V(I)` of a module in degrees `≤ d`. -/
theorem isLE_derivedSectionsWithSupportIn_single_of_cohomologicalDimension_le
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG) (d : ℤ)
    (hcd : cohomologicalDimension A I hI ≤ d) (M : ModuleCat.{u} A) :
    ((derivedSectionsWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).IsLE d :=
  (DerivedCategory.isLE_iff _ d).mpr fun i hi =>
    isZero_localCohomologyWithSupportIn_of_cohomologicalDimension_le A I hI d hcd M i hi

/-- The local cohomology `RΓ_{V(I)}(M[0])` of Stacks 0A6Q of a module placed in degree zero lies
in degrees `≥ 0`. -/
@[stacks 0EFH "the boundedness the truncation reduction needs: `RΓ_{V(I)}(M[0])` lies in
degrees `≥ 0`"]
theorem isGE_localCohomologyDerived_single
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A) :
    ((Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
      ((Dualizing.localCohomologyFunctor A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))).IsGE 0 :=
  have := isGE_derivedSectionsWithSupportIn_single.{u, u} A
    (PrimeSpectrum.zeroLocus (I : Set A)) M
  DerivedCategory.TStructure.t.isGE_of_iso
    ((derivedSectionsWithSupportInIsoLocalCohomologyDerived A I hI).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) 0

/-- **Stacks 0EFE.** For `M` finite over a Noetherian ring `A` with a dualizing
complex and `p` a prime outside `V(I)`, if `depth_{A_{p'}}(M_{p'}) + dim((A/p')_q) > s` for all
primes `p' ⊆ p` and all `q ∈ V(I)` with `p' ⊆ q`, then some `f ∈ A` outside `p` annihilates
`H^i_{V(I)}(M)` for every `i ≤ s`. -/
@[stacks 0EFE]
theorem exists_notMem_mem_annihilator_localCohomologyWithSupportIn_of_dualizing
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (p : PrimeSpectrum A) (s : ℤ) (hs : 0 ≤ s)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hp : p ∉ PrimeSpectrum.zeroLocus (I : Set A))
    (hdepth : ∀ x y : PrimeSpectrum A, x.asIdeal ≤ p.asIdeal →
      y ∈ PrimeSpectrum.zeroLocus (I : Set A) → x.asIdeal ≤ y.asIdeal →
      enatToEInt
          (Module.depth (Localization.AtPrime x.asIdeal)
            (maximalIdeal (Localization.AtPrime x.asIdeal))
            (LocalizedModule x.asIdeal.primeCompl M)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime y.asIdeal) ⧸
            x.asIdeal.map (algebraMap A (Localization.AtPrime y.asIdeal)))) > (s : EInt)) :
    ∃ f : A, f ∉ p.asIdeal ∧ ∀ i : ℤ, i ≤ s →
      f ∈ Module.annihilator A
        (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.zeroLocus (I : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) :=
  exists_notMem_and_mem_annihilator_localCohomologyWithSupportIn A M I p s hs omega homega
    (fun T T' hTT' hT hT' s₀ hs₀ ω hω =>
      exists_ideal_le_annihilator_localCohomology_iff A M T T' hTT' hT hT' s₀ hs₀ ω hω)
    hp hdepth

/-- **The per-degree annihilator input of Stacks 0EFH, in the support-indexed model.** For `M`
finite over a Noetherian ring `A` with a dualizing complex and `p` a prime outside
`V(J) ∩ V(I)`, the depth-plus-dimension inequality in the range `s + d` gives one element of `A`
outside `p` annihilating `H^j_{V(I+J)}(M)` for every `j ≤ s + d`. -/
@[stacks 0EFH "the per-degree annihilator input: a single element outside `p` annihilating
`H^j_{V(I+J)}(M)` for every `j ≤ s + d`"]
theorem exists_notMem_mem_annihilator_localCohomologyWithSupportIn_sup
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (p : PrimeSpectrum A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hp : p ∉ PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (hdepth : ∀ x y : PrimeSpectrum A, x.asIdeal ≤ p.asIdeal →
      y ∈ PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) →
      x.asIdeal ≤ y.asIdeal →
      enatToEInt
          (Module.depth (Localization.AtPrime x.asIdeal)
            (maximalIdeal (Localization.AtPrime x.asIdeal))
            (LocalizedModule x.asIdeal.primeCompl M)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime y.asIdeal) ⧸
            x.asIdeal.map (algebraMap A (Localization.AtPrime y.asIdeal)))) >
        ((s + d : ℤ) : EInt)) :
    ∃ f : A, f ∉ p.asIdeal ∧ ∀ j : ℤ, j ≤ s + d →
      f ∈ Module.annihilator A
        (localCohomologyWithSupportIn.{u, u} A
          (PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal A) : Set A))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) j) := by
  have hmem : ∀ y : PrimeSpectrum A,
      y ∈ PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal A) : Set A) ↔
        y ∈ PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) := by
    intro y
    rw [PrimeSpectrum.zeroLocus_sup]
    exact and_comm
  by_cases hb : 0 ≤ s + d
  · refine exists_notMem_mem_annihilator_localCohomologyWithSupportIn_of_dualizing
      A M (I ⊔ J) p (s + d) hb omega homega (fun hpmem => hp ((hmem p).mp hpmem))
      (fun x y hx hy hxy => hdepth x y hx ((hmem y).mp hy) hxy)
  · refine ⟨1, p.isPrime.one_notMem, fun j hj => ?_⟩
    have := subsingleton_localCohomologyWithSupportIn_single_of_neg.{u, u} A
      (PrimeSpectrum.zeroLocus ((I ⊔ J : Ideal A) : Set A)) (ModuleCat.of A M) j (by omega)
    refine Module.mem_annihilator.mpr fun x => ?_
    rw [one_smul]
    exact Subsingleton.elim x 0

/-- **The per-degree annihilator input of Stacks 0EFH, in the coreflection model.** The
annihilator of the previous statement, transported to the local cohomology `RΓ_{V(I+J)}` of
Stacks 0A6Q along the comparison of Stacks 0955. -/
@[stacks 0EFH "the per-degree annihilator input, in the `RΓ_{V(I+J)}` coreflection model"]
theorem exists_notMem_mem_annihilator_localCohomologyModule_sup
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (p : PrimeSpectrum A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hp : p ∉ PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (hdepth : ∀ x y : PrimeSpectrum A, x.asIdeal ≤ p.asIdeal →
      y ∈ PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) →
      x.asIdeal ≤ y.asIdeal →
      enatToEInt
          (Module.depth (Localization.AtPrime x.asIdeal)
            (maximalIdeal (Localization.AtPrime x.asIdeal))
            (LocalizedModule x.asIdeal.primeCompl M)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime y.asIdeal) ⧸
            x.asIdeal.map (algebraMap A (Localization.AtPrime y.asIdeal)))) >
        ((s + d : ℤ) : EInt)) :
    ∃ f : A, f ∉ p.asIdeal ∧ ∀ j : ℤ, j ≤ s + d →
      f ∈ Module.annihilator A
        (localCohomologyModule A (I ⊔ J) (I ⊔ J).fg_of_isNoetherianRing
          (ModuleCat.of A M) j) := by
  obtain ⟨f, hfp, hf⟩ := exists_notMem_mem_annihilator_localCohomologyWithSupportIn_sup
    A M I J p s d omega homega hp hdepth
  refine ⟨f, hfp, fun j hj => ?_⟩
  have e := localCohomologyWithSupportInIsoLocalCohomologyModule A (I ⊔ J)
    (I ⊔ J).fg_of_isNoetherianRing (ModuleCat.of A M) j
  refine Module.mem_annihilator.mpr fun x => ?_
  have hx := Module.mem_annihilator.mp (hf j hj) (e.inv x)
  have := congrArg (fun y => e.hom y) hx
  simpa only [map_smul, map_zero, ← ConcreteCategory.comp_apply, e.inv_hom_id,
    ConcreteCategory.id_apply] using this

end Stacks.LocalCohomology

end
