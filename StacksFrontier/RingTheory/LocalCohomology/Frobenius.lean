module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.ChangeOfRings
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence

/-!
# Frobenius and local cohomology

Let `A` be a commutative ring in which a prime number `p` vanishes and let `I ⊆ A` be a finitely
generated ideal. Derived extension of scalars along the Frobenius endomorphism `a ↦ a ^ p` fixes
the local cohomology `RΓ_{V(I)}(A)` of the regular module up to isomorphism.

Two things go into this. Base change for local cohomology (Stacks tag 0ALZ,
`Stacks.LocalCohomology.localCohomologyBaseChangeSingleIso`) carries `RΓ_{V(I)}(A)` to
`RΓ_{V(IA)}` of the derived extension of scalars of the regular module, and that extension is
again the regular module
(`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsRegularIso`). What remains is
that the extended ideal `I A = (a ^ p : a ∈ I)` cuts out the same closed subset as `I`: it is
contained in `I`, and `I` is contained in its radical because `a ^ p` lies in it
for every `a ∈ I`. Local cohomology depends on the ideal only through that closed subset, since
having `I`-power-torsion cohomology does.

## Main definitions

* `Stacks.LocalCohomology.frobeniusOfNatCastEqZero` is the Frobenius endomorphism under the
  literal hypothesis `(p : A) = 0`, which also covers the zero ring.

## Main results

* `Stacks.LocalCohomology.localCohomologyOfRing_frobeniusIso` is the Frobenius base-change
  isomorphism for the local cohomology of the regular module.

## Implementation notes

The Frobenius is built from `(p : A) = 0` directly rather than from a characteristic
typeclass, so that the zero ring is included; `powMonoidHom p` supplies multiplicativity and the
freshman's binomial theorem additivity.

The support `V(I)` is represented by the ideal `I` itself, and derived tensor product over
Frobenius by derived extension of scalars along it. The local cohomology of the regular module
is `Stacks.LocalCohomology.localCohomologyDerived` applied to `A` placed in degree zero.

## References

* [Stacks Project, Tag 0EC6](https://stacks.math.columbia.edu/tag/0EC6)
-/

public noncomputable section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- The Frobenius endomorphism `a ↦ a ^ p` of a commutative ring in which the prime `p`
vanishes. The hypothesis is the literal equation `(p : A) = 0`, so the zero ring is included. -/
@[expose] def frobeniusOfNatCastEqZero (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime)
    (hp0 : (p : A) = 0) : A →+* A where
  __ := powMonoidHom p
  map_zero' := zero_pow hp.pos.ne'
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp x y
    simpa [hp0] using hr

/-- The Frobenius endomorphism raises to the `p`-th power. -/
@[simp] theorem frobeniusOfNatCastEqZero_apply (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime)
    (hp0 : (p : A) = 0) (a : A) : frobeniusOfNatCastEqZero A p hp hp0 a = a ^ p := rfl

/-! ### The part of tag 0957 that the Frobenius isomorphism consumes -/

/-- Derived extension of scalars along a homomorphism of commutative rings carries the local
cohomology of the regular module of the source, with support in a finitely generated ideal, to
the local cohomology of the regular module of the target with support in the extended ideal.

This is a `private` stand-in for the part of Stacks tag 0957 that
`Stacks.LocalCohomology.localCohomologyOfRing_frobeniusIso` consumes; delete it when that tag
lands. It is base change for local cohomology (Stacks tag 0ALZ) at the regular module, followed
by the identification of its derived extension of scalars with the regular module of the
target. -/
private def regularBaseChangeIso (A B : Type u) [CommRing A] [CommRing B] (f : A →+* B)
    (I : Ideal A) (hI : I.FG) :
    (derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
        ((localCohomologyDerived A I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) ≅
      (localCohomologyDerived B (I.map f) (hI.map f)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) :=
  localCohomologyBaseChangeSingleIso.{u, u, u} f I hI (ModuleCat.of A A) ≪≫
    (localCohomologyDerived B (I.map f) (hI.map f)).mapIso
      (derivedExtensionScalarsRegularIso.{u} f)

/-! ### Local cohomology depends on the ideal only through its radical -/

/-- Two finitely generated ideals with the same radical have the same power-torsion property on
the derived category: a module is `I`-power-torsion exactly when its support lies in `V(I)`. -/
private theorem derivedPowerTorsionProperty_eq_of_radical_eq (A : Type u) [CommRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (hrad : J.radical = I.radical) :
    Dualizing.derivedPowerTorsionProperty.{u, u} A J hJ =
      Dualizing.derivedPowerTorsionProperty.{u, u} A I hI := by
  have hzero : PrimeSpectrum.zeroLocus (J : Set A) = PrimeSpectrum.zeroLocus (I : Set A) :=
    PrimeSpectrum.zeroLocus_eq_iff.mpr hrad
  funext K
  refine propext (forall_congr' fun i => ?_)
  rw [isIPowerTorsion_iff_support_subset A _ J hJ, isIPowerTorsion_iff_support_subset A _ I hI,
    hzero]

/-- Local cohomology with support in a finitely generated ideal depends on the ideal only
through its radical: the two coreflections onto the same full subcategory of the derived
category agree. -/
private def localCohomologyDerivedObjIsoOfRadicalEq (A : Type u) [CommRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (hrad : J.radical = I.radical)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (localCohomologyDerived A J hJ).obj K ≅ (localCohomologyDerived A I hI).obj K := by
  have hProp := derivedPowerTorsionProperty_eq_of_radical_eq A I J hI hJ hrad
  let E := ObjectProperty.fullSubcategoryCongr hProp
  have hIncl : E.functor ⋙ (Dualizing.derivedPowerTorsionProperty A I hI).ι ≅
      (Dualizing.derivedPowerTorsionProperty A J hJ).ι := Iso.refl _
  exact (Dualizing.derivedPowerTorsionProperty A J hJ).ι.mapIso
    (((Dualizing.localCohomologyAdjunction.{u, u} A J hJ).rightAdjointUniq
      ((E.toAdjunction.comp (Dualizing.localCohomologyAdjunction.{u, u} A I hI)).ofNatIsoLeft
        hIncl)).app K)

/-! ### The Frobenius isomorphism -/

/-- **Stacks Project, Tag 0EC6.** For a commutative ring `A` in which a prime `p` vanishes and a
finitely generated ideal `I`, derived extension of scalars along the Frobenius endomorphism
fixes the local cohomology `RΓ_{V(I)}(A)` of the regular module up to isomorphism. -/
@[stacks 0EC6]
def localCohomologyOfRing_frobeniusIso (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime)
    (hp0 : (p : A) = 0) (I : Ideal A) (hI : I.FG) :
    (derivedExtensionScalarsGeneral.{u, u, u} (frobeniusOfNatCastEqZero A p hp hp0)).functor.obj
        ((localCohomologyDerived A I hI).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) ≅
      (localCohomologyDerived A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) :=
  let F := frobeniusOfNatCastEqZero A p hp hp0
  have hmap : I.map F ≤ I := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change x ^ p ∈ I
    exact Ideal.pow_le_self hp.pos.ne' (Ideal.pow_mem_pow hx p)
  have hle : I ≤ (I.map F).radical := fun x hx =>
    Ideal.mem_radical_iff.mpr ⟨p, Ideal.mem_map_of_mem F hx⟩
  have hrad : (I.map F).radical = I.radical :=
    le_antisymm (Ideal.radical_mono hmap)
      ((Ideal.radical_mono hle).trans_eq (Ideal.radical_idem _))
  regularBaseChangeIso A A F I hI ≪≫
    localCohomologyDerivedObjIsoOfRadicalEq A I (I.map F) hI (hI.map F) hrad
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))

end Stacks.LocalCohomology

end
