module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
public import StacksFrontier.Homology.ExtendScalars.DerivedHomology
public import StacksFrontier.Homology.Perfect.FibreDescent
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Homology.Perfect.Local
public import StacksFrontier.Homology.Perfect.Module
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation
public import StacksFrontier.RingTheory.PseudoCoherentMap.PolynomialLocalizationFibre
public import StacksFrontier.RingTheory.PseudoCoherentMap.TorAmplitudeFlatDescent
import all StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Localising a polynomial presentation at a prime

Let `P → B` be a surjection of commutative rings, let `q` be a prime of `P` containing its
kernel and write `q̄ = q · B` for the corresponding prime of `B`. This file identifies the base
change `P_q ⊗_P B` with the localisation `B_{q̄}`, and carries a Tor-amplitude bound for `B_{q̄}`
over `A_{q̄ ∩ A}` down to a bound over `A`, for a base ring `A` sitting under the whole picture.

Both are steps in the source's proof of [stacks 069C] (3) ⟹ (1): having chosen a polynomial
presentation `A[x_1, …, x_n] ↠ B`, it applies [stacks 068X] at every prime `q` of the polynomial
algebra, and the object it applies it to is the localisation of `B` at `q`, whose Tor-amplitude
bound over the base comes from the hypothesis of (3) at the prime `q̄`.

## Main results

* `RingHom.map_primeCompl_of_surjective`: `q.primeCompl` maps onto `(q · B).primeCompl`.
* `RingHom.isLocalization_tensorProduct_localizationAtPrime`: `P_q ⊗_P B` is a model of `B_{q̄}`.
* `RingHom.liesOver_map_of_surjective`: `q̄` lies over `q`.
* `RingHom.restrictScalarsTowerSelfIso`, `RingHom.restrictScalarsTowerCompareIso`: for a tower
  `A → S → T` of rings, `T` read as an `A`-module through `S` is `T` read as an `A`-module, so
  two intermediate rings give the same `A`-module.
* `RingHom.exists_hasTorAmplitudeCanonical_localizationAtPrime`: the Tor-amplitude bound for
  `B_{q̄}` over `A`, in the form [stacks 068X] reads it when applied to `A → P_q`.
* `RingHom.extendScalarsLocalizationIso`: the base change of `B` to `P_q`, as a `P_q`-module, is
  `B_{q̄}`. This is the object [stacks 068W] hands to [stacks 068X], read at the model the
  hypothesis of 069C (3) is stated at.
* `RingHom.isPerfect_derivedExtensionScalars_single_atPrime`: for `P = A[x_1, …, x_n]`, the
  derived base change of `B[0]` to `P_q` is perfect, at every prime `q` of `P`.
* `RingHom.isPerfectModule_mvPolynomial_of_forall_localizationAtPrime`: `B` is a perfect
  `A[x_1, …, x_n]`-module. This is the affine core of [stacks 069C] (3) ⟹ (1).

## Implementation notes

The identification `P_q ⊗_P B ≅ B_{q̄}` is not written as a ring isomorphism: it is the
observation that the base change is *a* localisation of `B` at `q̄.primeCompl`, by
`IsLocalization.tensorRight` together with the fact that a surjection carries `q.primeCompl`
onto `q̄.primeCompl`. Everything downstream is then free to pick whichever model is convenient,
and the tag's statement is read at `Localization.AtPrime`.

**The restriction-of-scalars seam.** The two readings of `B_{q̄}` as an `A`-module, one through
`A_{q̄ ∩ A}` and one through `P_q`, have the same underlying abelian group and the same scalar
action, but the `Module` arguments of `LinearEquiv.toModuleIso` are *implicit*, so writing the
comparison as a `LinearEquiv` on the carrier of a `ModuleCat.restrictScalars` object makes
instance search supply a different — definitionally but not reducibly equal — structure, and the
elaborator rejects it. `RingHom.restrictScalarsTowerSelfIso` avoids the seam by composing only
prepared isomorphisms, `ModuleCat.restrictScalarsComp'App` and
`StacksDraft.TorAmplitude.FaithfullyFlat.restrictScalarsSelfEquiv`; the scalar towers it needs
are the ones Mathlib's `Localization.AtPrime.IsLiesOverAlgebra` supplies.

## References

* [The Stacks Project, Lemma 37.61.11 (069C)](https://stacks.math.columbia.edu/tag/069C)
* [The Stacks Project, Lemma 15.83.1 (068X)](https://stacks.math.columbia.edu/tag/068X)
-/

@[expose] public section

universe u

open CategoryTheory StacksDraft.TorAmplitude

open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

namespace RingHom

section Localization

variable {P B : Type u} [CommRing P] [CommRing B] [Algebra P B]

/-- For a surjection `P → B` and an ideal `q` of `P` containing its kernel, `q · B` restricts
back to `q`. -/
private theorem comap_map_eq_of_surjective_of_ker_le (hs : Function.Surjective (algebraMap P B))
    (q : Ideal P) (hI : RingHom.ker (algebraMap P B) ≤ q) :
    Ideal.comap (algebraMap P B) (q.map (algebraMap P B)) = q := by
  rw [Ideal.comap_map_of_surjective _ hs]
  simpa [RingHom.ker_eq_comap_bot] using hI

/-- For a surjection `P → B` and a prime `q` of `P` containing its kernel, the multiplicative set
`q.primeCompl` maps onto the multiplicative set of the prime `q · B`. -/
public theorem map_primeCompl_of_surjective (hs : Function.Surjective (algebraMap P B))
    (q : Ideal P) [q.IsPrime] (hI : RingHom.ker (algebraMap P B) ≤ q) :
    haveI : (q.map (algebraMap P B)).IsPrime := Ideal.map_isPrime_of_surjective hs hI
    Submonoid.map (algebraMap P B) q.primeCompl =
      (q.map (algebraMap P B)).primeCompl := by
  have : (q.map (algebraMap P B)).IsPrime := Ideal.map_isPrime_of_surjective hs hI
  have hcomap := comap_map_eq_of_surjective_of_ker_le hs q hI
  ext b
  simp only [Submonoid.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro hmem
    exact hx (hcomap ▸ (Ideal.mem_comap.mpr hmem))
  · intro hb
    obtain ⟨x, rfl⟩ := hs b
    exact ⟨x, fun hx => hb (Ideal.mem_map_of_mem _ hx), rfl⟩

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A : Type u} [CommRing A] [Algebra A P] [Algebra A B] [IsScalarTower A P B]

/-- For a surjection `P → B` and a prime `q` of `P` containing its kernel, the base change
`P_q ⊗_P B` is a model of the localisation of `B` at the prime `q · B`. -/
public theorem isLocalization_tensorProduct_localizationAtPrime
    (hs : Function.Surjective (algebraMap P B))
    (q : Ideal P) [q.IsPrime] (hI : RingHom.ker (algebraMap P B) ≤ q) :
    haveI : (q.map (algebraMap P B)).IsPrime := Ideal.map_isPrime_of_surjective hs hI
    IsLocalization (q.map (algebraMap P B)).primeCompl
      (TensorProduct P (Localization.AtPrime q) B) := by
  have : (q.map (algebraMap P B)).IsPrime := Ideal.map_isPrime_of_surjective hs hI
  rw [← map_primeCompl_of_surjective hs q hI]
  exact IsLocalization.tensorRight (A := Localization.AtPrime q) (M := q.primeCompl)

/-- `q · B` lies over `q` for a surjection `P → B` whose kernel is contained in `q`. -/
public theorem liesOver_map_of_surjective (hs : Function.Surjective (algebraMap P B))
    (q : Ideal P) [q.IsPrime] (hI : RingHom.ker (algebraMap P B) ≤ q) :
    (q.map (algebraMap P B)).LiesOver q :=
  ⟨(comap_map_eq_of_surjective_of_ker_le hs q hI).symm⟩

end Localization

section Tower

/-- For a tower `A → S → T` of commutative rings, the ring `T` read as an `A`-module through
`S` is the ring `T` read as an `A`-module through `A → T`.

This is the bridge the restriction-of-scalars seam needs. It is composed out of the prepared
isomorphisms `ModuleCat.restrictScalarsComp'App` and
`StacksDraft.TorAmplitude.FaithfullyFlat.restrictScalarsSelfEquiv` rather than written as a
`LinearEquiv` on the carrier of a `ModuleCat.restrictScalars` object, whose `Module` argument
is implicit and is filled by instance search with a different — definitionally equal but not
reducibly equal — structure. -/
public noncomputable def restrictScalarsTowerSelfIso (A S T : Type u) [CommRing A] [CommRing S]
    [CommRing T] [Algebra A S] [Algebra S T] [Algebra A T] [IsScalarTower A S T] :
    (ModuleCat.restrictScalars (algebraMap A S)).obj (ModuleCat.of S T) ≅
      ModuleCat.of A T :=
  (ModuleCat.restrictScalars (algebraMap A S)).mapIso
      (StacksDraft.TorAmplitude.FaithfullyFlat.restrictScalarsSelfEquiv S T).toModuleIso.symm ≪≫
    (ModuleCat.restrictScalarsComp'App (algebraMap A S) (algebraMap S T) (algebraMap A T)
      (IsScalarTower.algebraMap_eq A S T) (ModuleCat.of T T)).symm ≪≫
    (StacksDraft.TorAmplitude.FaithfullyFlat.restrictScalarsSelfEquiv A T).toModuleIso

/-- The two readings of `T` as an `A`-module, through two intermediate rings `S` and `S'`,
agree. -/
public noncomputable def restrictScalarsTowerCompareIso (A S S' T : Type u) [CommRing A]
    [CommRing S] [CommRing S'] [CommRing T] [Algebra A S] [Algebra S T] [Algebra A S']
    [Algebra S' T] [Algebra A T] [IsScalarTower A S T] [IsScalarTower A S' T] :
    (ModuleCat.restrictScalars (algebraMap A S)).obj (ModuleCat.of S T) ≅
      (ModuleCat.restrictScalars (algebraMap A S')).obj (ModuleCat.of S' T) :=
  restrictScalarsTowerSelfIso A S T ≪≫ (restrictScalarsTowerSelfIso A S' T).symm

/-! ### The Tor-amplitude bound over the base ring -/

section Base

variable {P B : Type u} [CommRing P] [CommRing B] [Algebra P B]
  {A : Type u} [CommRing A] [Algebra A P] [Algebra A B] [IsScalarTower A P B]

/-- **The `A`-side Tor-amplitude bound of the affine core of Stacks 069C.** Let `P → B` be
surjective, let `q` be a prime of `P` containing its kernel and let `q̄ = q · B` be the
corresponding prime of `B`. If `B_{q̄}` has finite Tor dimension over `A_{q̄ ∩ A}` — which is the
hypothesis of Stacks 069C (3) at the point `q̄` — then `B_{q̄}`, read as an `A`-module through
`P_q`, has finite Tor dimension over `A` itself.

This is the form the Tor-amplitude hypothesis of [stacks 068X] takes when that lemma is applied
to `A → P_q`, which is the step the source's proof of 069C (3) ⟹ (1) performs at every prime of
a polynomial presentation. Both readings of `B_{q̄}` as an `A`-module — through `A_{q̄ ∩ A}` and
through `P_q` — are the reading through `A → B → B_{q̄}`, which is what
`RingHom.restrictScalarsTowerCompareIso` records; the descent of the bound from `A_{q̄ ∩ A}` to
`A` is `RingHom.hasTorAmplitudeCanonical_single_restrictScalars_of_flat`. -/
public theorem exists_hasTorAmplitudeCanonical_localizationAtPrime
    (hs : Function.Surjective (algebraMap P B))
    (q : Ideal P) [q.IsPrime] (hI : RingHom.ker (algebraMap P B) ≤ q) :
    haveI : (q.map (algebraMap P B)).IsPrime := Ideal.map_isPrime_of_surjective hs hI
    haveI : (q.map (algebraMap P B)).LiesOver q := liesOver_map_of_surjective hs q hI
    letI : Algebra (Localization.AtPrime q)
        (Localization.AtPrime (q.map (algebraMap P B))) :=
      Localization.AtPrime.algebraOfLiesOver q (q.map (algebraMap P B))
    letI : Algebra (Localization.AtPrime (Ideal.under A (q.map (algebraMap P B))))
        (Localization.AtPrime (q.map (algebraMap P B))) :=
      Localization.AtPrime.algebraOfLiesOver (Ideal.under A (q.map (algebraMap P B)))
        (q.map (algebraMap P B))
    HasFiniteTorDimensionCanonical
        (Localization.AtPrime (Ideal.under A (q.map (algebraMap P B))))
        ((DerivedCategory.singleFunctor
            (ModuleCat.{u} (Localization.AtPrime
              (Ideal.under A (q.map (algebraMap P B))))) 0).obj
          (ModuleCat.of (Localization.AtPrime (Ideal.under A (q.map (algebraMap P B))))
            (Localization.AtPrime (q.map (algebraMap P B))))) →
      ∃ a b : ℤ, HasTorAmplitudeCanonical A
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          ((ModuleCat.restrictScalars (algebraMap A (Localization.AtPrime q))).obj
            (ModuleCat.of (Localization.AtPrime q)
              (Localization.AtPrime (q.map (algebraMap P B)))))) a b := by
  have : (q.map (algebraMap P B)).IsPrime := Ideal.map_isPrime_of_surjective hs hI
  have : (q.map (algebraMap P B)).LiesOver q := liesOver_map_of_surjective hs q hI
  let : Algebra (Localization.AtPrime q)
      (Localization.AtPrime (q.map (algebraMap P B))) :=
    Localization.AtPrime.algebraOfLiesOver q (q.map (algebraMap P B))
  let : Algebra (Localization.AtPrime (Ideal.under A (q.map (algebraMap P B))))
      (Localization.AtPrime (q.map (algebraMap P B))) :=
    Localization.AtPrime.algebraOfLiesOver (Ideal.under A (q.map (algebraMap P B)))
      (q.map (algebraMap P B))
  intro h
  have hflat : Module.Flat A
      (Localization.AtPrime (Ideal.under A (q.map (algebraMap P B)))) :=
    IsLocalization.flat _ (Ideal.under A (q.map (algebraMap P B))).primeCompl
  obtain ⟨a, b, htor⟩ :=
    (hasFiniteTorDimensionCanonical_iff_exists_hasTorAmplitudeCanonical _ _).mp h
  exact ⟨a, b, AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
      (restrictScalarsTowerCompareIso A
        (Localization.AtPrime (Ideal.under A (q.map (algebraMap P B))))
        (Localization.AtPrime q) (Localization.AtPrime (q.map (algebraMap P B))))) a b
    (hasTorAmplitudeCanonical_single_restrictScalars_of_flat
      (ModuleCat.of (Localization.AtPrime (Ideal.under A (q.map (algebraMap P B))))
        (Localization.AtPrime (q.map (algebraMap P B)))) a b htor)⟩

/-! ### The base change of the target at a prime of the presentation -/

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The base change of `B` to `P_q` is the localisation `B_{q·B}`, as a `P_q`-module.**

The carrier of `ModuleCat.extendScalars` is identified with the tensor product by
`StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv`, and the tensor product with
the localisation by `RingHom.isLocalization_tensorProduct_localizationAtPrime`. That the
resulting ring isomorphism is `P_q`-linear is not part of being an isomorphism of `B`-algebras:
it is the equality of two ring maps `P_q → B_{q·B}` which agree on the image of `P`, and
`IsLocalization.ringHom_ext` makes agreement on `P` enough. -/
@[ega "0 6.3.1" "special case"]
public noncomputable def extendScalarsLocalizationIso
    (hs : Function.Surjective (algebraMap P B))
    (q : Ideal P) [q.IsPrime] (hI : RingHom.ker (algebraMap P B) ≤ q) :
    haveI : (q.map (algebraMap P B)).IsPrime := Ideal.map_isPrime_of_surjective hs hI
    haveI : (q.map (algebraMap P B)).LiesOver q := liesOver_map_of_surjective hs q hI
    letI : Algebra (Localization.AtPrime q)
        (Localization.AtPrime (q.map (algebraMap P B))) :=
      Localization.AtPrime.algebraOfLiesOver q (q.map (algebraMap P B))
    (ModuleCat.extendScalars (algebraMap P (Localization.AtPrime q))).obj
        (ModuleCat.of P B) ≅
      ModuleCat.of (Localization.AtPrime q)
        (Localization.AtPrime (q.map (algebraMap P B))) := by
  haveI : (q.map (algebraMap P B)).IsPrime := Ideal.map_isPrime_of_surjective hs hI
  haveI : (q.map (algebraMap P B)).LiesOver q := liesOver_map_of_surjective hs q hI
  letI : Algebra (Localization.AtPrime q)
      (Localization.AtPrime (q.map (algebraMap P B))) :=
    Localization.AtPrime.algebraOfLiesOver q (q.map (algebraMap P B))
  haveI := isLocalization_tensorProduct_localizationAtPrime hs q hI
  let eRing : TensorProduct P (Localization.AtPrime q) B ≃ₐ[B]
      Localization.AtPrime (q.map (algebraMap P B)) :=
    IsLocalization.algEquiv (q.map (algebraMap P B)).primeCompl _ _
  have hLlin : (eRing.toRingEquiv.toRingHom).comp
        (algebraMap (Localization.AtPrime q) (TensorProduct P (Localization.AtPrime q) B)) =
      algebraMap (Localization.AtPrime q)
        (Localization.AtPrime (q.map (algebraMap P B))) := by
    refine IsLocalization.ringHom_ext q.primeCompl ?_
    ext c
    change eRing (algebraMap P (Localization.AtPrime q) c ⊗ₜ[P] (1 : B)) = _
    rw [show (algebraMap P (Localization.AtPrime q) c) ⊗ₜ[P] (1 : B)
          = (c • (1 : Localization.AtPrime q)) ⊗ₜ[P] (1 : B) by
        rw [Algebra.smul_def, mul_one], TensorProduct.smul_tmul]
    change eRing (algebraMap B (TensorProduct P (Localization.AtPrime q) B)
        (c • (1 : B))) = _
    rw [eRing.commutes, Algebra.smul_def, mul_one]
    exact (Localization.localRingHom_to_map q (q.map (algebraMap P B))
      (algebraMap P B) Ideal.LiesOver.over c).symm
  exact LinearEquiv.toModuleIso
    ((StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv P
      (Localization.AtPrime q) (ModuleCat.of P B)).trans
      { __ := eRing.toAddEquiv
        map_smul' l x := by
          change eRing (l • x) = l • eRing x
          rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← hLlin]
          rfl })

/-! ### Perfectness at a prime of the presentation -/

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Stacks 068X at a prime of a polynomial presentation.** Let `A → B` be a ring map presented
by a surjection `P = A[x_1, …, x_n] ↠ B`, let `B[0]` be pseudo-coherent over `P` and assume
every localisation of `B` at a prime has finite Tor dimension over the corresponding localisation
of `A`, which is condition (3) of [stacks 069C]. Then for every prime `q` of `P` the derived base
change of `B[0]` to `P_q` is perfect.

This is the step [stacks 068W] consumes. Either the kernel of `P → B` is not contained in `q`, in
which case the base change vanishes, or it is, in which case the base change is the localisation
`B_{q·B}` and [stacks 068X] applies to `A → P_q`: that map is flat, its fibres have global
dimension at most `n` by `RingHom.polynomial_localization_fibre_globalDimension_le`, and the
Tor-amplitude bound over `A` is
`RingHom.exists_hasTorAmplitudeCanonical_localizationAtPrime`. -/
public theorem isPerfect_derivedExtensionScalars_single_atPrime {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B]
    [IsScalarTower A (MvPolynomial (Fin n) A) B]
    (hs : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
    (hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) A)) 0).obj
        (ModuleCat.of (MvPolynomial (Fin n) A) B)))
    (h : ∀ (q' : Ideal B) (_ : q'.IsPrime),
      letI : Algebra (Localization.AtPrime (Ideal.under A q')) (Localization.AtPrime q') :=
        Localization.AtPrime.algebraOfLiesOver (Ideal.under A q') q'
      HasFiniteTorDimensionCanonical (Localization.AtPrime (Ideal.under A q'))
        ((DerivedCategory.singleFunctor
            (ModuleCat.{u} (Localization.AtPrime (Ideal.under A q'))) 0).obj
          (ModuleCat.of (Localization.AtPrime (Ideal.under A q'))
            (Localization.AtPrime q'))))
    (q : Ideal (MvPolynomial (Fin n) A)) [q.IsPrime] :
    StacksDraft.Perfect.IsPerfect
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap (MvPolynomial (Fin n) A) (Localization.AtPrime q))).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) A)) 0).obj
          (ModuleCat.of (MvPolynomial (Fin n) A) B))) := by
  have hflatPL : (algebraMap (MvPolynomial (Fin n) A) (Localization.AtPrime q)).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (Localization.AtPrime q) q.primeCompl)
  refine StacksDraft.Perfect.isPerfect_of_iso
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsSingleIso.{u, u, u}
      (algebraMap (MvPolynomial (Fin n) A) (Localization.AtPrime q)) hflatPL
      (ModuleCat.of (MvPolynomial (Fin n) A) B)) ?_
  have : Module.Flat A (Localization.AtPrime q) := inferInstance
  by_cases hI : RingHom.ker (algebraMap (MvPolynomial (Fin n) A) B) ≤ q
  · have : (q.map (algebraMap (MvPolynomial (Fin n) A) B)).IsPrime :=
      Ideal.map_isPrime_of_surjective hs hI
    have : (q.map (algebraMap (MvPolynomial (Fin n) A) B)).LiesOver q :=
      liesOver_map_of_surjective hs q hI
    let : Algebra (Localization.AtPrime q)
        (Localization.AtPrime (q.map (algebraMap (MvPolynomial (Fin n) A) B))) :=
      Localization.AtPrime.algebraOfLiesOver q
        (q.map (algebraMap (MvPolynomial (Fin n) A) B))
    let : Algebra (Localization.AtPrime
          (Ideal.under A (q.map (algebraMap (MvPolynomial (Fin n) A) B))))
        (Localization.AtPrime (q.map (algebraMap (MvPolynomial (Fin n) A) B))) :=
      Localization.AtPrime.algebraOfLiesOver
        (Ideal.under A (q.map (algebraMap (MvPolynomial (Fin n) A) B)))
        (q.map (algebraMap (MvPolynomial (Fin n) A) B))
    obtain ⟨a, b, hbound⟩ := exists_hasTorAmplitudeCanonical_localizationAtPrime hs q hI
      (h (q.map (algebraMap (MvPolynomial (Fin n) A) B)) inferInstance)
    set Xext := (ModuleCat.extendScalars
      (algebraMap (MvPolynomial (Fin n) A) (Localization.AtPrime q))).obj
      (ModuleCat.of (MvPolynomial (Fin n) A) B) with hXext
    have hpcL : StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime q)) 0).obj Xext) := by
      obtain ⟨E, hE, ⟨eE⟩⟩ :=
        (StacksDraft.PseudoCoherence.totalDerivedExtensionScalars_preserves_pseudoCoherent.{u, u, u}
          (algebraMap (MvPolynomial (Fin n) A) (Localization.AtPrime q)) _).2 hpc
      exact ⟨E, hE, ⟨eE ≪≫
        CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsSingleIso.{u, u, u}
          (algebraMap (MvPolynomial (Fin n) A) (Localization.AtPrime q)) hflatPL
          (ModuleCat.of (MvPolynomial (Fin n) A) B)⟩⟩
    have hampCan : HasTorAmplitudeCanonical A
        ((ModuleCat.restrictScalars
            (algebraMap A (Localization.AtPrime q))).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime q)) 0).obj
            Xext)) a b := by
      refine AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
        (((ModuleCat.restrictScalars
            (algebraMap A (Localization.AtPrime q))).mapDerivedCategorySingleFunctor 0).app
          Xext).symm a b ?_
      exact AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
          ((ModuleCat.restrictScalars (algebraMap A (Localization.AtPrime q))).mapIso
            (extendScalarsLocalizationIso hs q hI)).symm) a b hbound
    have hamp := StacksDraft.Perfect.hasTorAmplitudeIn_flatRepresentative_of_hasTorAmplitude
      (canonicalTensorComparison A) (canonicalTensorIsLeftDerived A) _ a b
      ((hasTorAmplitude_iff_hasFlatRepresentative (canonicalTensorComparison A)
        (canonicalTensorIsLeftDerived A) _ a b).mpr
        ((hasTorAmplitudeCanonical_iff_hasFlatRepresentative A _ a b).mp hampCan))
    exact (StacksDraft.Perfect.isPerfect_and_torAmplitude_of_flat_of_fibre_globalDimension_le
      (A := A) (B := Localization.AtPrime q) a b n
      (polynomial_localization_fibre_globalDimension_le A n q) _ hpcL hamp).1
  · apply isPerfect_of_isZero
    apply (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime q)) 0).map_isZero
    rw [ModuleCat.isZero_iff_subsingleton]
    obtain ⟨x, hxI, hxq⟩ := Set.not_subset.mp hI
    have : Subsingleton (TensorProduct (MvPolynomial (Fin n) A) (Localization.AtPrime q) B) := by
      refine IsLocalization.subsingleton
        (M := Algebra.algebraMapSubmonoid B q.primeCompl) ?_
      exact ⟨x, hxq, hxI⟩
    exact (StacksDraft.TorAmplitude.FaithfullyFlat.extendScalarsCarrierEquiv
      (MvPolynomial (Fin n) A) (Localization.AtPrime q)
      (ModuleCat.of (MvPolynomial (Fin n) A) B)).toEquiv.subsingleton

/-! ### Perfectness over the polynomial algebra -/

open StacksDraft.Perfect in
/-- **The affine core of [stacks 069C], over the polynomial algebra.** Let `A → B` be presented
by a surjection `P = A[x_1, …, x_n] ↠ B` with `B[0]` pseudo-coherent over `P`, and assume
condition (3) of [stacks 069C]: every localisation of `B` at a prime has finite Tor dimension
over the corresponding localisation of `A`. Then `B` is a perfect `P`-module.

This is [stacks 068W] applied to `B[0]`, which is bounded below and pseudo-coherent, with
perfectness at every prime stalk supplied by
`RingHom.isPerfect_derivedExtensionScalars_single_atPrime`. -/
public theorem isPerfectModule_mvPolynomial_of_forall_localizationAtPrime {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] (n : ℕ) [Algebra (MvPolynomial (Fin n) A) B]
    [IsScalarTower A (MvPolynomial (Fin n) A) B]
    (hs : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B))
    (hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) A)) 0).obj
        (ModuleCat.of (MvPolynomial (Fin n) A) B)))
    (h : ∀ (q' : Ideal B) (_ : q'.IsPrime),
      letI : Algebra (Localization.AtPrime (Ideal.under A q')) (Localization.AtPrime q') :=
        Localization.AtPrime.algebraOfLiesOver (Ideal.under A q') q'
      HasFiniteTorDimensionCanonical (Localization.AtPrime (Ideal.under A q'))
        ((DerivedCategory.singleFunctor
            (ModuleCat.{u} (Localization.AtPrime (Ideal.under A q'))) 0).obj
          (ModuleCat.of (Localization.AtPrime (Ideal.under A q'))
            (Localization.AtPrime q')))) :
    StacksDraft.Perfect.IsPerfect
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) A)) 0).obj
        (ModuleCat.of (MvPolynomial (Fin n) A) B)) :=
  ((isPerfect_iff_isPerfect_at_primes_of_isBoundedBelow_and_stalkwise_criteria.{u, u}
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) A)) 0).obj
      (ModuleCat.of (MvPolynomial (Fin n) A) B)) hpc).2.2.2.2
      ⟨0, inferInstance⟩).mpr
    fun q => isPerfect_derivedExtensionScalars_single_atPrime n hs hpc h q.asIdeal

/-! ### The affine core of Stacks 069C -/

/-- **The affine core of [stacks 069C] (3) ⟹ (1).** A pseudo-coherent ring map `φ : A → B` all
of whose localisations `B_q` have finite Tor dimension over `A_{q ∩ A}` has finite Tor
dimension.

This is the source's argument: choose a presentation `A[x_1, …, x_n] ↠ B`, which exists because
a pseudo-coherent ring map is of finite type, and note that `B` is pseudo-coherent as a module
over the polynomial algebra through *that* presentation, by [stacks 065H]. Then
`RingHom.isPerfectModule_mvPolynomial_of_forall_localizationAtPrime` makes `B` a perfect module
over the polynomial algebra, and [stacks 068Y] turns that into perfectness of the ring map, whose
Tor-dimension half is the conclusion. -/
public theorem hasFiniteTorDimensionRingHom_of_forall_localizationAtPrime {A B : Type u}
    [CommRing A] [CommRing B] (φ : A →+* B) (hφ : φ.PseudoCoherent)
    (h : letI : Algebra A B := φ.toAlgebra
      ∀ (q : Ideal B) (_ : q.IsPrime),
        letI : Algebra (Localization.AtPrime (Ideal.under A q)) (Localization.AtPrime q) :=
          Localization.AtPrime.algebraOfLiesOver (Ideal.under A q) q
        HasFiniteTorDimensionCanonical (Localization.AtPrime (Ideal.under A q))
          ((DerivedCategory.singleFunctor
              (ModuleCat.{u} (Localization.AtPrime (Ideal.under A q))) 0).obj
            (ModuleCat.of (Localization.AtPrime (Ideal.under A q))
              (Localization.AtPrime q)))) :
    AlgebraicGeometry.HasFiniteTorDimensionRingHom φ := by
  let : Algebra A B := φ.toAlgebra
  have hpcm : Algebra.PseudoCoherent A B := hφ
  obtain ⟨n, α, hα⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
  let : Module (MvPolynomial (Fin n) A) B := Module.compHom B α.toRingHom
  let algPB : Algebra (MvPolynomial (Fin n) A) B :=
    Algebra.ofModule (fun r x y => mul_assoc (α r) x y)
      (fun r x y => by
        change x * (α r * y) = α r * (x * y)
        ring)
  have hmap : algebraMap (MvPolynomial (Fin n) A) B = α.toRingHom :=
    RingHom.ext fun r => mul_one (α r)
  have : IsScalarTower A (MvPolynomial (Fin n) A) B := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [hmap]
    exact α.comp_algebraMap.symm
  have hs : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B) := by
    rwa [hmap]
  have hpcP : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (MvPolynomial (Fin n) A)) 0).obj
        (ModuleCat.of (MvPolynomial (Fin n) A) B)) := by
    obtain ⟨E, hE, ⟨eE⟩⟩ :=
      (PseudoCoherence.isPseudoCoherentFrom_polynomialPresentation_independent (R := A)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) 0).2.mp
        ((Algebra.pseudoCoherent_iff_exists_polynomialPresentation A B).mp hpcm) n α hα
    exact ⟨E, hE, ⟨eE ≪≫ ((ModuleCat.restrictScalars.{u}
      α.toRingHom).mapDerivedCategorySingleFunctor 0).app (ModuleCat.of B B)⟩⟩
  have hperf := isPerfectModule_mvPolynomial_of_forall_localizationAtPrime n hs hpcP h
  have : Algebra.Perfect A B :=
    Algebra.perfect_iff_pseudoCoherent_and_exists_finite_projective_resolution.mpr ⟨hpcm, n, α, hα,
      (StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution B).mp hperf⟩
  exact (AlgebraicGeometry.hasFiniteTorDimensionRingHom_iff_forall φ).mpr fun D =>
    Algebra.Perfect.moduleHasFiniteTorDimension D.comparison D.isLeftDerived

end Base

end Tower

end RingHom

end

