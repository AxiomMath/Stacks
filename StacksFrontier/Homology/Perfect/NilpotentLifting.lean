module

public import Mathlib
public import StacksCore.RingTheory.Nakayama
public import StacksFrontier.Algebra.Module.Projective.Nakayama
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.Perfect.Lifting
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.Homology.TorAmplitude.Nilpotent
public import StacksFrontier.RingTheory.Henselian.Pair.Lifting.Projective
public import StacksFrontier.RingTheory.Module.Projective.Lifting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting a complex of projective modules across a nilpotent or henselian quotient

Let `I` be an ideal of a commutative ring `R`. A bounded above complex of projective
`R ⧸ I`-modules representing the derived reduction of an object `K` of `D(R)` is the reduction of
a bounded above complex of projective `R`-modules representing `K`, provided `I` is nilpotent;
the same holds for *finite* projective modules and a pseudo-coherent `K` when `(R, I)` is a
henselian pair. Both are instances of the lifting theorem [stacks 0BCA] at a class of projective
modules; the instance at finite stably free modules is [stacks 0BCB], in
`StacksFrontier.Homology.Perfect.Lifting`.

## Main results

* `StacksDraft.Perfect.exists_boundedAbove_projective_lift_representing` ([stacks 09AR]): the
  lifting theorem for projective modules across a nilpotent quotient.
* `StacksDraft.Perfect.exists_boundedAbove_projective_lift_representing_of_surjective`: the same
  statement for an arbitrary surjection of commutative rings with nilpotent kernel, with the two
  ring universes and the module universe independent. The previous result is its instance at
  `Ideal.Quotient.mk`.
* `StacksDraft.Perfect.exists_boundedAbove_finiteProjective_lift_representing` ([stacks 0BCE]):
  the lifting theorem for finite projective modules over a henselian pair, together with the
  assertion that freeness of a term of the given complex is inherited by the corresponding term
  of the lift.
* `StacksDraft.Perfect.exists_boundedAbove_finiteProjective_lift_representing_of_datum`: the same
  statement against an arbitrary datum of total derived extension of scalars, from which the
  previous result is the instance at the canonical one.

## Implementation notes

### The henselian case

The three conditions [stacks 0BCA] imposes on a class of modules are verified for finite
projective modules as follows. Closure under finite direct sums and complementary summands is
immediate from the splitting of a biproduct. Detection of surjectivity is Nakayama's lemma, which
applies because the ideal of a henselian pair lies in the Jacobson radical. That every term of the
given complex is a reduction is [stacks 0D4A]: reduction modulo the ideal of a henselian pair is
a bijection on isomorphism classes of finite projective modules. The remaining condition, that the
object already have a bounded above representative with terms in the class, holds because a
pseudo-coherent object is represented by a bounded above complex of finite free modules.

The final assertion, that the lift is free wherever the given complex is, is [stacks 0BC6]: a
finite free module with the same reduction as a finite projective module is isomorphic to it. Its
proof needs a finite free `R`-module reducing to the given free `R ⧸ I`-module, which is the free
module on a basis index of the latter; the degenerate case in which `R ⧸ I` is trivial is handled
separately, since a trivial quotient of a ring in whose Jacobson radical `I` lies forces `R`
itself to be trivial.

### The nilpotent case

Here the class of modules is *all* projective modules, and the same three conditions come out as
follows. Closure under sums and summands is the splitting of a biproduct again. Surjectivity is
detected by [stacks 00DV (11)] (`LinearMap.surjective_of_surjective_comp_mkQ_of_isNilpotent`),
which needs no finiteness because `I` is nilpotent. Every term of the given complex is a
reduction by [stacks 07LV]
(`Module.exists_projective_quotient_smul_top_linearEquiv_of_isNilpotent`).

The remaining condition — that `K` already have *some* bounded above representative with
projective terms — is the only substantial input, and it is where the nilpotence of `I` is spent
a second time. A bounded above projective representative exists as soon as `K` is bounded above
(`StacksDraft.TorAmplitude.exists_projective_representative_of_isLE`), and the derived reduction
of `K` reflects an upper bound because `I` is nilpotent. That reflection is the one-sided form of
[stacks 0H75], `StacksDraft.TorAmplitude.isLE_of_hasTorAmplitudeAbove_derivedExtensionScalars`,
whose hypothesis is Tor amplitude *above* `b` for the reduction — not merely `IsLE b`, which does
not imply it. The Tor-amplitude bound is available for free from the data at hand: the prescribed
complex `E` is strictly bounded above by `b` with projective, hence flat, hence K-flat terms, so
its derived tensor product with any module in degree zero is computed by an ordinary tensor
product with a complex concentrated in degrees at most zero, which is again strictly bounded
above by `b`. This is `isZero_derivedTensor_single_of_isStrictlyLE` below.

### Universes in the nilpotent case

Ring and module universes are kept independent throughout: `R : Type u` and modules in
`ModuleCat.{max v u}`. The reflection of an upper bound above, however, is only available with the
module universe equal to the universe of the ring, since the K-flat theory and the monoidal
structure on `ModuleCat` both need that. So the nilpotent statement is proved first with all
universes equal (`exists_projective_quotient_lift`) and then transported: the source ring is
replaced by a `ULift` of itself into the module universe, and the target by the quotient by the
kernel of the composite. The transport of the *hypothesis* is the only delicate part, because it
is a statement about derived extension of scalars; `derivedExtensionScalars_equiv_iso` supplies
the required square, by identifying two total left derived functors of the same termwise functor
read through the two coefficient equivalences.

## References

* [Stacks Project, Tag 09AR](https://stacks.math.columbia.edu/tag/09AR)
* [Stacks Project, Tag 0BCE](https://stacks.math.columbia.edu/tag/0BCE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

section HenselianPairLift

/-- An ideal contained in the Jacobson radical has every element of `1 + I` a unit. -/
private theorem isUnit_one_add_of_le_jacobson
    {R : Type u} [CommRing R] {I : Ideal R} (hjac : I ≤ (⊥ : Ideal R).jacobson) :
    ∀ x ∈ I, IsUnit (1 + x) := by
  intro x hx
  simpa [add_comm] using Ideal.mem_jacobson_bot.mp (hjac hx) 1

/-- Condition (2) of [stacks 0BCA] for the class of finite projective modules. -/
private theorem finiteProjective_biprod_iff
    {R : Type u} [CommRing R] (M N : ModuleCat.{max v u} R) :
    ((Module.Finite R M ∧ Module.Projective R M) ∧
        (Module.Finite R (↑(M ⊞ N) : Type (max v u)) ∧
          Module.Projective R (↑(M ⊞ N) : Type (max v u)))) ↔
      ((Module.Finite R M ∧ Module.Projective R M) ∧
        (Module.Finite R N ∧ Module.Projective R N)) := by
  have e : (↑(M ⊞ N) : Type (max v u)) ≃ₗ[R] (M × N) :=
    (ModuleCat.biprodIsoProd M N).toLinearEquiv
  constructor
  · rintro ⟨hM, hfin, hproj⟩
    have : Module.Finite R (M × N) := Module.Finite.equiv e
    have : Module.Projective R (M × N) := Module.Projective.of_equiv e
    exact ⟨hM,
      Module.Finite.of_surjective (LinearMap.snd R M N) LinearMap.snd_surjective,
      Module.Projective.of_split (LinearMap.inr R M N) (LinearMap.snd R M N)
        (LinearMap.ext fun _ => rfl)⟩
  · rintro ⟨hM, hNfin, hNproj⟩
    have := hM.1
    have := hM.2
    exact ⟨hM, Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩

/-- Condition (4) of [stacks 0BCA] for finite projective modules: every term of a complex of
finite projective `R ⧸ I`-modules is a reduction, for a henselian pair `(R, I)`. -/
private theorem finiteProjective_terms_of_henselian
    {R : Type u} [CommRing R] (I : Ideal R) (hI : HenselianPair R I)
    (E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ)
    (hEterms : ∀ i,
      Module.Finite (R ⧸ I) (E.X i) ∧ Module.Projective (R ⧸ I) (E.X i)) (i : ℤ) :
    ∃ M : ModuleCat.{max v u} R, (Module.Finite R M ∧ Module.Projective R M) ∧ Nonempty
      (E.X i ≅ (ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).obj M) := by
  have := (hEterms i).1
  have := (hEterms i).2
  obtain ⟨M, hadd, hmod, hMfin, hMproj, ⟨e⟩⟩ :=
    (henselianPair_finiteProjective_quotient_bijective.{u, max v u, max v u} I hI).1
      (E.X i : Type (max v u))
  let _ := hadd
  let _ := hmod
  exact ⟨ModuleCat.of R M, ⟨hMfin, hMproj⟩,
    ⟨(e.symm.trans (extendScalarsQuotEquiv.{u, v} I M).symm).toModuleIso⟩⟩

/-- Condition (5) of [stacks 0BCA] for finite projective modules: a pseudo-coherent object has a
bounded above representative with finite projective terms. -/
private theorem finiteProjective_representative_of_isPseudoCoherent
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{max v u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    ∃ KC : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, Module.Finite R (KC.X i) ∧ Module.Projective R (KC.X i)) ∧
        (∃ b, KC.IsStrictlyLE b) ∧ Nonempty ((DerivedCategory.Q).obj KC ≅ K) := by
  obtain ⟨KC, hKC, hKCiso⟩ := hK
  refine ⟨KC, fun i => ?_, hKC.upperBound, hKCiso⟩
  have : Module.Free R (KC.X i) := (hKC.finiteFree i).2
  exact ⟨(hKC.finiteFree i).1, inferInstance⟩

/-- [stacks 0BCE] against an arbitrary datum of total derived extension of scalars. The tagged
statement `StacksDraft.Perfect.exists_boundedAbove_finiteProjective_lift_representing` is the
instance of this at the canonical datum. -/
theorem exists_boundedAbove_finiteProjective_lift_representing_of_datum
    {R : Type u} [CommRing R] (I : Ideal R)
    (D : TotalDerivedExtensionScalars.{u, v, u} (Ideal.Quotient.mk I))
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ)
    (hEbdd : ∃ b, E.IsStrictlyLE b)
    (hEterms : ∀ i,
      Module.Finite (R ⧸ I) (E.X i) ∧ Module.Projective (R ⧸ I) (E.X i))
    (hErep : Nonempty ((DerivedCategory.Q).obj E ≅ D.functor.obj K))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hI : HenselianPair R I) :
    ∃ P : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i)) ∧
      (∃ b, P.IsStrictlyLE b) ∧
      Nonempty
        (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P ≅ E) ∧
      Nonempty ((DerivedCategory.Q).obj P ≅ K) ∧
      (∀ i, Module.Free (R ⧸ I) (E.X i) → Module.Free R (P.X i)) := by
  classical
  have hunit : ∀ x ∈ I, IsUnit (1 + x) := isUnit_one_add_of_le_jacobson hI.le_jacobson
  let Pc : ModuleCat.{max v u} R → Prop :=
    fun M => Module.Finite R M ∧ Module.Projective R M
  have hterms := finiteProjective_terms_of_henselian I hI E hEterms
  have hKrep := finiteProjective_representative_of_isPseudoCoherent K hK
  obtain ⟨P, hP, hPbdd, ⟨eRed⟩, hPrep⟩ :=
    exists_boundedAbove_lift_representing_of_datum.{u, v} I D Pc K E
      (fun _ h => h.2)
      (fun M₁ M₂ => finiteProjective_biprod_iff M₁ M₂)
      (fun _ N f _ hN hf => have := hN.1; surjective_of_extendScalars_surjective I hunit f hf)
      hEbdd hterms hErep hKrep
  refine ⟨P, hP, hPbdd, ⟨eRed⟩, hPrep, fun i hEfree => ?_⟩
  have := (hP i).1
  have := (hP i).2
  have := (hEterms i).1
  exact free_of_free_reduction.{u, v} I hunit (P.X i) (E.X i)
    ((extendScalarsQuotEquiv.{u, v} I (P.X i)).symm.trans
      ((HomologicalComplex.eval _ (ComplexShape.up ℤ) i).mapIso eRed).toLinearEquiv)

/-- [stacks 0BCE] with the lift compatible with a prescribed identification. Against an
arbitrary datum `D` of total derived extension of scalars, and for a chosen isomorphism
`eGiven : E ≅ K ⊗ᴸ[R] R ⧸ I` in `D(R ⧸ I)`, the lift `P` comes with isomorphisms
`eRed : P ⊗[R] R ⧸ I ≅ E` of complexes and `eK : P ≅ K` in `D(R)` such that the comparison
`P ⊗[R] R ⧸ I ⟶ P ⊗ᴸ[R] R ⧸ I`, followed by `eRed` and `eGiven`, is `eK ⊗ᴸ R ⧸ I`. This is the
form in which the proof of Stacks 0DL7 uses Stacks 0BCE: "`α` is represented by an isomorphism
`E ⊗ B ≅ P ⊗ B`". -/
theorem exists_boundedAbove_finiteProjective_lift_representing_iso_of_datum
    {R : Type u} [CommRing R] (I : Ideal R)
    (D : TotalDerivedExtensionScalars.{u, v, u} (Ideal.Quotient.mk I))
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ)
    (hEbdd : ∃ b, E.IsStrictlyLE b)
    (hEterms : ∀ i,
      Module.Finite (R ⧸ I) (E.X i) ∧ Module.Projective (R ⧸ I) (E.X i))
    (eGiven : (DerivedCategory.Q).obj E ≅ D.functor.obj K)
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hI : HenselianPair R I) :
    ∃ P : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i)) ∧
      (∃ b, P.IsStrictlyLE b) ∧
      ∃ eRed :
        ((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P ≅ E,
      ∃ eK : (DerivedCategory.Q).obj P ≅ K,
        D.comparison.app P ≫ DerivedCategory.Q.map eRed.hom ≫ eGiven.hom =
          D.functor.map eK.hom := by
  classical
  have hunit : ∀ x ∈ I, IsUnit (1 + x) := isUnit_one_add_of_le_jacobson hI.le_jacobson
  let Pc : ModuleCat.{max v u} R → Prop :=
    fun M => Module.Finite R M ∧ Module.Projective R M
  have hterms := finiteProjective_terms_of_henselian I hI E hEterms
  have hKrep := finiteProjective_representative_of_isPseudoCoherent K hK
  exact exists_boundedAbove_lift_representing_iso.{u, v} I D Pc K E
    (fun _ h => h.2)
    (fun M₁ M₂ => finiteProjective_biprod_iff M₁ M₂)
    (fun _ N f _ hN hf => have := hN.1; surjective_of_extendScalars_surjective I hunit f hf)
    hEbdd hterms eGiven hKrep

/-- **Stacks 0BCE.** Let `(R, I)` be a henselian pair and let `K` be a pseudo-coherent object of
`D(R)`. A bounded above complex `E` of finite projective `R ⧸ I`-modules representing
`K ⊗ᴸ[R] R ⧸ I` lifts to a bounded above complex `P` of finite projective `R`-modules
representing `K` with `P ⊗[R] R ⧸ I` isomorphic to `E`. Moreover `P` is free in every degree in
which `E` is free. -/
@[stacks 0BCE]
theorem exists_boundedAbove_finiteProjective_lift_representing
    {R : Type u} [CommRing R] (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ)
    (hEbdd : ∃ b, E.IsStrictlyLE b)
    (hEterms : ∀ i,
      Module.Finite (R ⧸ I) (E.X i) ∧ Module.Projective (R ⧸ I) (E.X i))
    (hErep : Nonempty
      ((DerivedCategory.Q).obj E ≅
        (totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)).functor.obj K))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hI : HenselianPair R I) :
    ∃ P : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∀ i, Module.Finite R (P.X i) ∧ Module.Projective R (P.X i)) ∧
      (∃ b, P.IsStrictlyLE b) ∧
      Nonempty
        (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P ≅ E) ∧
      Nonempty ((DerivedCategory.Q).obj P ≅ K) ∧
      (∀ i, Module.Free (R ⧸ I) (E.X i) → Module.Free R (P.X i)) :=
  exists_boundedAbove_finiteProjective_lift_representing_of_datum.{u, v} I
    (totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)) K E hEbdd hEterms hErep hK hI

end HenselianPairLift

/-! ### Lifting a complex of projective modules across a nilpotent quotient -/

section NilpotentProjectiveLift

/-! #### All universes equal

The derived-tensor input to the nilpotent case is only available with the module universe equal
to the universe of the ring, so the whole argument is carried out there first. -/

/-- **Tor amplitude above from a bounded above K-flat representative.** If `E` is K-flat and
strictly bounded above by `b`, then for every module `M` the derived tensor product of `E` with
`M` placed in cohomological degree zero has no cohomology above `b`.

Represent `M[0]` by a complex `P` of projectives concentrated in degrees at most `0`, which is
K-flat, and compute the derived tensor product through the K-flat comparison of the bifunctor.
What is left is the total tensor product `E ⊗ P`, which is strictly bounded above by `b`. -/
private theorem isZero_derivedTensor_single_of_isStrictlyLE {S : Type w} [CommRing S]
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct S)
    (E : CochainComplex (ModuleCat.{w} S) ℤ) (b : ℤ) (hb : E.IsStrictlyLE b) (hE : E.KFlat)
    (M : ModuleCat.{w} S) (i : ℤ) (hi : b < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).obj
      ((T.tensor.obj (DerivedCategory.Q.obj E)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{w} S) 0).obj M))) := by
  obtain ⟨P, hPproj, hPLE, ⟨eP⟩⟩ :=
    TorAmplitude.exists_projective_representative_of_isLE
      ((DerivedCategory.singleFunctor (ModuleCat.{w} S) 0).obj M) 0
      ((DerivedCategory.isLE_iff _ 0).1 inferInstance)
  have := hPLE
  have hPKF : P.KFlat := TorAmplitude.kFlat_of_isStrictlyLE_projective P 0 hPproj
  have : CochainComplex.IsStrictlyLE (MonoidalCategory.tensorObj E P) b := by
    have h : CochainComplex.IsStrictlyLE (MonoidalCategory.tensorObj E P) (b + 0) :=
      TotalTensorComplex.tensor_isStrictlyLE E P b 0
    simpa only [add_zero] using h
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).mapIso
        ((T.tensor.obj (DerivedCategory.Q.obj E)).mapIso eP ≪≫ T.comparison E P hE hPKF) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{w} S) i).app
        (MonoidalCategory.tensorObj E P))
  apply ShortComplex.isZero_homology_of_isZero_X₂
  exact CochainComplex.isZero_of_isStrictlyLE (MonoidalCategory.tensorObj E P) b i hi

/-- **Derived reduction modulo a nilpotent ideal reflects an upper cohomological bound.** If the
derived reduction of `K` is represented by a complex `E` of projective `R ⧸ I`-modules strictly
bounded above by `b`, and `I` is nilpotent, then `K` itself has no cohomology above `b`.

This is the one-sided form of [stacks 0H75],
`StacksDraft.TorAmplitude.isLE_of_hasTorAmplitudeAbove_derivedExtensionScalars`, whose hypothesis
is a Tor-amplitude bound from above on the reduction; that bound is supplied by
`isZero_derivedTensor_single_of_isStrictlyLE` at `E`. -/
private theorem isLE_of_nilpotent_reduction {S : Type w} [CommRing S] (I : Ideal S)
    (hI : IsNilpotent I)
    (D : TotalDerivedExtensionScalars.{w, w, w} (Ideal.Quotient.mk I))
    (K : DerivedCategory (ModuleCat.{w} S)) (b : ℤ)
    (E : CochainComplex (ModuleCat.{w} (S ⧸ I)) ℤ) (hb : E.IsStrictlyLE b)
    (hEprojective : ∀ i : ℤ, Module.Projective (S ⧸ I) (E.X i))
    (hErep : Nonempty (DerivedCategory.Q.obj E ≅ D.functor.obj K)) :
    K.IsLE b := by
  have hEproj : ∀ i : ℤ, Projective (E.X i) := fun i => by
    have := hEprojective i
    infer_instance
  have hEKF : E.KFlat := TorAmplitude.kFlat_of_isStrictlyLE_projective E b hEproj
  -- The comparison carried by `D` has its target spelled as `extensionOfScalarsComplexGeneral`,
  -- which is not reducibly the composite the citation asks for, so the derived-functor
  -- certificate is re-registered at the spelling instance search will look for.
  have : D.functor.IsLeftDerivedFunctor
      (show DerivedCategory.Q (C := ModuleCat.{w} S) ⋙ D.functor ⟶
        (ModuleCat.extendScalars.{w, w, w} (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q from D.comparison)
      (HomologicalComplex.quasiIso (ModuleCat.{w} S) (ComplexShape.up ℤ)) := D.isLeftDerived
  refine TorAmplitude.isLE_of_hasTorAmplitudeAbove_derivedExtensionScalars
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hI) D.functor D.comparison
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct S)
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (S ⧸ I)) K b ?_
  intro M i hi
  refine (isZero_derivedTensor_single_of_isStrictlyLE
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (S ⧸ I)) E b hb hEKF M i
    hi).of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{w} (S ⧸ I)) i).mapIso
      (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        (S ⧸ I)).tensor.mapIso hErep.some).app _).symm)

/-- [stacks 09AR] with the module universe equal to the universe of the ring, and for the
canonical quotient map. This is [stacks 0BCA] at the class of all projective modules, whose three
conditions are the splitting of a biproduct, [stacks 00DV (11)] and [stacks 07LV]; the bounded
above projective representative of `K` it also requires comes from
`isLE_of_nilpotent_reduction`. -/
private theorem exists_projective_quotient_lift {S : Type w} [CommRing S] (I : Ideal S)
    (hI : IsNilpotent I)
    (D : TotalDerivedExtensionScalars.{w, w, w} (Ideal.Quotient.mk I))
    (E : CochainComplex (ModuleCat.{w} (S ⧸ I)) ℤ)
    (K : DerivedCategory (ModuleCat.{w} S))
    (hEbdd : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEprojective : ∀ i : ℤ, Module.Projective (S ⧸ I) (E.X i))
    (hErep : Nonempty (DerivedCategory.Q.obj E ≅ D.functor.obj K)) :
    ∃ P : CochainComplex (ModuleCat.{w} S) ℤ,
      (∃ b : ℤ, P.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Projective S (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
      Nonempty (((ModuleCat.extendScalars.{w, w, w} (Ideal.Quotient.mk I)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P ≅ E) := by
  classical
  obtain ⟨b, hb⟩ := hEbdd
  have hKLE : K.IsLE b := isLE_of_nilpotent_reduction I hI D K b E hb hEprojective hErep
  have hKrep : ∃ KC : CochainComplex (ModuleCat.{w} S) ℤ,
      (∀ i, Module.Projective S (KC.X i)) ∧ (∃ c : ℤ, KC.IsStrictlyLE c) ∧
        Nonempty (DerivedCategory.Q.obj KC ≅ K) := by
    obtain ⟨KC, hKCproj, hKCLE, ⟨eKC⟩⟩ :=
      TorAmplitude.exists_projective_representative_of_isLE K b
        ((DerivedCategory.isLE_iff K b).1 hKLE)
    refine ⟨KC, fun i => ?_, ⟨b, hKCLE⟩, ⟨eKC.symm⟩⟩
    have := hKCproj i
    infer_instance
  have hsum (M N : ModuleCat.{w} S) :
      (Module.Projective S M ∧ Module.Projective S ↑(M ⊞ N)) ↔
        (Module.Projective S M ∧ Module.Projective S N) := by
    constructor
    · rintro ⟨hM, hMN⟩
      have : Projective (M ⊞ N) := inferInstance
      have : Projective N := (show Retract N (M ⊞ N) from
        ⟨biprod.inr, biprod.snd, biprod.inr_snd⟩).projective
      exact ⟨hM, inferInstance⟩
    · rintro ⟨hM, hN⟩
      have : Projective M := inferInstance
      have : Projective N := inferInstance
      exact ⟨hM, inferInstance⟩
  have hsurj (M N : ModuleCat.{w} S) (g : M ⟶ N)
      (_ : Module.Projective S M) (_ : Module.Projective S N)
      (hg : Function.Surjective
        (((ModuleCat.extendScalars.{w, w, w} (Ideal.Quotient.mk I)).map g).hom)) :
      Function.Surjective g.hom := by
    apply LinearMap.surjective_of_surjective_comp_mkQ_of_isNilpotent I g.hom hI
    let q := TensorProduct.quotTensorEquivQuotSMul (N : Type w) I
    let η := (ModuleCat.extendRestrictScalarsAdj (Ideal.Quotient.mk I)).unit.app M
    have hη : Function.Surjective η.hom := by
      let qM := TensorProduct.quotTensorEquivQuotSMul (M : Type w) I
      intro z
      obtain ⟨x, hx⟩ := (I • (⊤ : Submodule S (M : Type w))).mkQ_surjective (qM z)
      refine ⟨x, qM.injective ?_⟩
      show qM ((1 : S ⧸ I) ⊗ₜ[S] x) = qM z
      simpa [qM] using hx
    intro y
    obtain ⟨z, hz⟩ := hg (q.symm y)
    obtain ⟨x, rfl⟩ := hη z
    refine ⟨x, ?_⟩
    have h := congrArg q hz
    change q ((1 : S ⧸ I) ⊗ₜ[S] g.hom x) = q (q.symm y) at h
    simpa [q] using h
  have hterms (i : ℤ) : ∃ M : ModuleCat.{w} S,
      Module.Projective S M ∧ Nonempty (E.X i ≅
        (ModuleCat.extendScalars.{w, w, w} (Ideal.Quotient.mk I)).obj M) := by
    have := hEprojective i
    obtain ⟨M, _, _, hM, ⟨e⟩⟩ :=
      Module.exists_projective_quotient_smul_top_linearEquiv_of_isNilpotent
        (R := S) (I := I) (Q := (E.X i : Type w)) hI
    exact ⟨ModuleCat.of S M, hM, ⟨((extendScalarsQuotEquiv.{w, w} I M).trans e).toModuleIso.symm⟩⟩
  obtain ⟨P, hPterms, hPbdd, hPred, hPrep⟩ :=
    exists_boundedAbove_lift_representing_of_datum.{w, w} I D
      (fun M => Module.Projective S M) K E (fun _ h => h) hsum hsurj ⟨b, hb⟩ hterms hErep hKrep
  exact ⟨P, hPbdd, hPterms, hPrep, hPred⟩

/-! #### Transport to independent universes -/

/-- An additive equivalence of abelian categories induces a localized equivalence of the
categories of complexes up to quasi-isomorphism. -/
private lemma isLocalizedEquivalence_mapHomologicalComplexUpToQuasiIso {C D : Type*}
    [Category* C] [Category* D] [Abelian C] [Abelian D] (G : C ⥤ D) [G.Additive]
    [G.IsEquivalence] :
    (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).IsLocalizedEquivalence := by
  let : (G.mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence :=
    (G.asEquivalence.mapHomologicalComplex (ComplexShape.up ℤ)).isEquivalence_functor
  let : (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor.IsEquivalence :=
    inferInstanceAs (G.mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence
  let : (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).IsInduced := by
    refine ⟨?_⟩
    ext K L f
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology f G
  exact LocalizerMorphism.isLocalizedEquivalence_of_isInduced _

/-- An additive equivalence of abelian categories induces an equivalence of derived
categories. -/
private lemma mapDerivedCategory_isEquivalence {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (G : C ⥤ D) [G.Additive] [G.IsEquivalence] :
    G.mapDerivedCategory.IsEquivalence := by
  let : (G.mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence :=
    (G.asEquivalence.mapHomologicalComplex (ComplexShape.up ℤ)).isEquivalence_functor
  let : (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor.IsEquivalence :=
    inferInstanceAs (G.mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence
  have := isLocalizedEquivalence_mapHomologicalComplexUpToQuasiIso G
  let : CatCommSq (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  exact (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)).isEquivalence
    DerivedCategory.Q DerivedCategory.Q _

/-- Termwise extension of scalars corresponds to itself under a commutative square of ring
equivalences, by conjugating the identification of the two restriction-of-scalars composites
through the extend/restrict adjunctions. -/
private noncomputable def extensionScalars_equiv_iso
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    {A' B' : Type (max u v w)} [CommRing A'] [CommRing B']
    (f : A →+* B) (f' : A' →+* B') (eA : A' ≃+* A) (eB : B' ≃+* B)
    (h : f'.comp eA.symm.toRingHom = eB.symm.toRingHom.comp f) :
    ModuleCat.restrictScalars.{max u v w} eA.toRingHom ⋙
      ModuleCat.extendScalars.{max u v w, max u v w, max u v w} f' ≅
    ModuleCat.extendScalars.{u, w, max u v w} f ⋙
      ModuleCat.restrictScalars.{max u v w} eB.toRingHom := by
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max u v w} eA
  let H := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max u v w} eB
  let adj₁ := E.toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj.{max u v w, max u v w, max u v w} f')
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj.{max u v w, u, w} f).comp H.toAdjunction
  refine (conjugateIsoEquiv adj₂ adj₁).symm ?_
  exact (ModuleCat.restrictScalarsComp _ _).symm ≪≫
    ModuleCat.restrictScalarsCongr h.symm ≪≫ ModuleCat.restrictScalarsComp _ _

/-- The canonical total derived extensions of scalars correspond under a commutative square of
ring equivalences. Both composites are total left derived functors of the same termwise functor —
the source one read through the coefficient equivalence downstairs, by
`LocalizerMorphism.isLeftDerivedFunctor_iff_precomp` — so they are canonically isomorphic, and
`extensionScalars_equiv_iso` identifies the two termwise functors. -/
private noncomputable def derivedExtensionScalars_equiv_iso
    {A : Type u} {B : Type w} [CommRing A] [CommRing B]
    {A' B' : Type (max u v w)} [CommRing A'] [CommRing B']
    (f : A →+* B) (f' : A' →+* B') (eA : A' ≃+* A) (eB : B' ≃+* B)
    (h : f'.comp eA.symm.toRingHom = eB.symm.toRingHom.comp f) :
    (derivedExtensionScalarsGeneral.{u, v, w} f).functor ⋙
      (ModuleCat.restrictScalars.{max u v w} eB.toRingHom).mapDerivedCategory ≅
    (ModuleCat.restrictScalars.{max u v w} eA.toRingHom).mapDerivedCategory ⋙
      (totalDerivedExtensionScalars.{max u v w, max u v w, max u v w} f').functor := by
  let G := ModuleCat.restrictScalars.{max u v w} eA.toRingHom
  let H := ModuleCat.restrictScalars.{max u v w} eB.toRingHom
  let : G.IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv eA).isEquivalence_functor
  let : H.IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv eB).isEquivalence_functor
  let : H.mapDerivedCategory.IsEquivalence := mapDerivedCategory_isEquivalence H
  let : (G.mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence :=
    (G.asEquivalence.mapHomologicalComplex (ComplexShape.up ℤ)).isEquivalence_functor
  let : (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor.IsEquivalence :=
    inferInstanceAs (G.mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence
  have := isLocalizedEquivalence_mapHomologicalComplexUpToQuasiIso G
  let D := derivedExtensionScalarsGeneral.{u, v, w} f
  let D' := totalDerivedExtensionScalars.{max u v w, max u v w, max u v w} f'
  let F := ModuleCat.extendScalars.{u, w, max u v w} f
  let F' := ModuleCat.extendScalars.{max u v w, max u v w, max u v w} f'
  let : F.Additive := (ModuleCat.extendRestrictScalarsAdj.{max u v w, u, w} f).left_adjoint_additive
  let : F'.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v w, max u v w, max u v w} f').left_adjoint_additive
  let α := (Functor.associator _ _ _).inv ≫ Functor.whiskerRight D.comparison H.mapDerivedCategory
  -- `β` is deliberately left unascribed: its target is the one `D'.comparison` actually carries,
  -- `extensionOfScalarsComplexGeneral f'`, and ascribing the definitionally equal composite
  -- `F'.mapHomologicalComplex _ ⋙ Q` instead makes the compatibility goal below ill-typed at
  -- `implicit` transparency, so that neither `rw` nor `simp` will touch it.
  let β := (Functor.associator DerivedCategory.Q G.mapDerivedCategory D'.functor).inv ≫
      Functor.whiskerRight G.mapDerivedCategoryFactors.hom D'.functor ≫
      (Functor.associator (G.mapHomologicalComplex (ComplexShape.up ℤ)) DerivedCategory.Q
        D'.functor).hom ≫
      Functor.whiskerLeft (G.mapHomologicalComplex (ComplexShape.up ℤ)) D'.comparison
  have : (G.mapDerivedCategory ⋙ D'.functor).IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (ModuleCat.{max u v w} A) (ComplexShape.up ℤ)) := by
    apply (LocalizerMorphism.isLeftDerivedFunctor_iff_precomp
      (G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory G.mapDerivedCategoryFactors.symm
      β D'.comparison (Iso.refl _) (Iso.refl _) ?_).1 inferInstance
    dsimp only [β, Functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism]
    simp
  let τ : (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
      H.mapDerivedCategory ≅ G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ H.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ H)) (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (extensionScalars_equiv_iso.{u, v, w} f f' eA eB h)
            (ComplexShape.up ℤ)).symm) _ ≪≫
      Functor.associator _ _ _
  exact Functor.leftDerivedNatIso _ _ α β
    (HomologicalComplex.quasiIso (ModuleCat.{max u v w} A) (ComplexShape.up ℤ)) τ

/-! #### The endpoints -/

/-- **[stacks 09AR] for an arbitrary surjection.** Let `f : R' → R` be a surjective map of
commutative rings whose kernel is nilpotent. A bounded above complex `E` of projective
`R`-modules representing the derived extension of scalars of an object `K` of `D(R')` lifts to a
bounded above complex `P` of projective `R'`-modules representing `K`, whose reduction
`R ⊗_{R'} P` is isomorphic to `E`.

The tagged statement `StacksDraft.Perfect.exists_boundedAbove_projective_lift_representing` is
the instance of this at `f = Ideal.Quotient.mk I`. -/
public theorem exists_boundedAbove_projective_lift_representing_of_surjective
    {R' : Type u} {R : Type w} [CommRing R'] [CommRing R] (f : R' →+* R)
    (hf : Function.Surjective f)
    (E : CochainComplex (ModuleCat.{max v u w} R) ℤ)
    (K : DerivedCategory (ModuleCat.{max v u w} R'))
    (hEbdd : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEprojective : ∀ i : ℤ, Module.Projective R (E.X i))
    (hErep : Nonempty
      ((DerivedCategory.Q).obj E ≅
        (derivedExtensionScalarsGeneral.{u, v, w} f).functor.obj K))
    (hI : IsNilpotent (RingHom.ker f)) :
    ∃ P : CochainComplex (ModuleCat.{max v u w} R') ℤ,
      (∃ b : ℤ, P.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Projective R' (P.X i)) ∧
      Nonempty ((DerivedCategory.Q).obj P ≅ K) ∧
      Nonempty
        (((ModuleCat.extendScalars.{u, w, max v u w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P ≅ E) := by
  classical
  let S := ULift.{max v w} R'
  let eA : S ≃+* R' := ULift.ringEquiv
  let g : S →+* R := f.comp eA.toRingHom
  have hg : Function.Surjective g := hf.comp eA.surjective
  let I := RingHom.ker g
  let f' := Ideal.Quotient.mk I
  let eB : S ⧸ I ≃+* R := RingHom.quotientKerEquivOfSurjective hg
  have hsquare : f'.comp eA.symm.toRingHom = eB.symm.toRingHom.comp f := by
    ext x
    apply eB.injective
    show g (eA.symm x) = eB (eB.symm (f x))
    simp [g]
  have hInil : IsNilpotent I := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, le_antisymm ?_ bot_le⟩
    show (RingHom.ker f).comap eA.toRingHom ^ n ≤ ⊥
    apply (Ideal.le_comap_pow eA.toRingHom n).trans
    rw [hn]
    show RingHom.ker eA.toRingHom ≤ ⊥
    intro x hx
    show x = 0
    change eA x = 0 at hx
    exact eA.injective (hx.trans (map_zero eA).symm)
  let G := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max u v w} eA
  let H := ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max u v w} eB
  let GC := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let HC := H.mapHomologicalComplex (ComplexShape.up ℤ)
  let : G.functor.Additive := inferInstanceAs (ModuleCat.restrictScalars eA.toRingHom).Additive
  let : G.inverse.Additive := inferInstanceAs (ModuleCat.restrictScalars eA.symm.toRingHom).Additive
  let : H.functor.Additive := inferInstanceAs (ModuleCat.restrictScalars eB.toRingHom).Additive
  let : G.functor.IsEquivalence := G.isEquivalence_functor
  let : H.functor.IsEquivalence := H.isEquivalence_functor
  let : G.functor.mapDerivedCategory.IsEquivalence := mapDerivedCategory_isEquivalence G.functor
  let : HC.functor.IsEquivalence := HC.isEquivalence_functor
  let E' : CochainComplex (ModuleCat.{max u v w} (S ⧸ I)) ℤ := HC.functor.obj E
  let K' := G.functor.mapDerivedCategory.obj K
  have hb' : ∃ b : ℤ, E'.IsStrictlyLE b := hEbdd.imp fun b hb => by
    have := hb
    show CochainComplex.IsStrictlyLE
      ((H.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj E) b
    infer_instance
  have hp' (i : ℤ) : Module.Projective (S ⧸ I) (E'.X i) := by
    have := hEprojective i
    have : Projective (E.X i) := inferInstance
    have : Projective (H.functor.obj (E.X i)) :=
      (H.map_projective_iff (E.X i)).2 inferInstance
    show Module.Projective (S ⧸ I) (H.functor.obj (E.X i))
    infer_instance
  have he' : Nonempty (DerivedCategory.Q.obj E' ≅
      (totalDerivedExtensionScalars.{max u v w, max u v w, max u v w} f').functor.obj K') :=
    ⟨(H.functor.mapDerivedCategoryFactors.app E).symm ≪≫
      H.functor.mapDerivedCategory.mapIso hErep.some ≪≫
      (derivedExtensionScalars_equiv_iso.{u, v, w} f f' eA eB hsquare).app K⟩
  obtain ⟨P', hbP', hpP', ⟨eK'⟩, ⟨eRed'⟩⟩ :=
    exists_projective_quotient_lift.{max u v w} I hInil
      (totalDerivedExtensionScalars.{max u v w, max u v w, max u v w} f') E' K' hb' hp' he'
  let P : CochainComplex (ModuleCat.{max u v w} R') ℤ := GC.inverse.obj P'
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · refine hbP'.imp fun b hb => ?_
    have := hb
    show CochainComplex.IsStrictlyLE
      ((G.inverse.mapHomologicalComplex (ComplexShape.up ℤ)).obj P') b
    infer_instance
  · intro i
    have := hpP' i
    have : Projective (P'.X i) := inferInstance
    have : Projective (G.inverse.obj (P'.X i)) :=
      (G.symm.map_projective_iff (P'.X i)).2 inferInstance
    show Module.Projective R' (G.inverse.obj (P'.X i))
    infer_instance
  · exact ⟨G.functor.mapDerivedCategory.preimageIso
      (G.functor.mapDerivedCategoryFactors.app P ≪≫
        DerivedCategory.Q.mapIso (GC.counitIso.app P') ≪≫ eK')⟩
  · let F := ModuleCat.extendScalars.{u, w, max u v w} f
    let F' := ModuleCat.extendScalars.{max u v w, max u v w, max u v w} f'
    let : F.Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v w, u, w} f).left_adjoint_additive
    let : F'.Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v w, max u v w, max u v w}
        f').left_adjoint_additive
    let q := Functor.mapHomologicalComplexCompIso
        (extensionScalars_equiv_iso.{u, v, w} f f' eA eB hsquare) (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ H.functor))
        (ComplexShape.up ℤ)).symm
    exact ⟨HC.functor.preimageIso ((q.app P).symm ≪≫
      (F'.mapHomologicalComplex (ComplexShape.up ℤ)).mapIso (GC.counitIso.app P') ≪≫ eRed')⟩

/-- **Stacks 09AR.** Let `I` be a nilpotent ideal of a commutative ring `R` and let `K` be an
object of `D(R)`. A bounded above complex `E` of projective `R ⧸ I`-modules representing
`K ⊗ᴸ[R] R ⧸ I` lifts to a bounded above complex `P` of projective `R`-modules representing `K`,
with `P ⊗[R] R ⧸ I` isomorphic to `E`. -/
@[stacks 09AR, sga "5 XV 3.Lemma1" "existence of L', v, w"]
public theorem exists_boundedAbove_projective_lift_representing
    {R : Type u} [CommRing R] (I : Ideal R)
    (E : CochainComplex (ModuleCat.{max v u} (R ⧸ I)) ℤ)
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (hEbdd : ∃ b : ℤ, E.IsStrictlyLE b)
    (hEprojective : ∀ i : ℤ, Module.Projective (R ⧸ I) (E.X i))
    (hErep : Nonempty
      ((DerivedCategory.Q).obj E ≅
        (totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)).functor.obj K))
    (hI : IsNilpotent I) :
    ∃ P : CochainComplex (ModuleCat.{max v u} R) ℤ,
      (∃ b : ℤ, P.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Projective R (P.X i)) ∧
      Nonempty ((DerivedCategory.Q).obj P ≅ K) ∧
      Nonempty
        (((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P ≅ E) :=
  exists_boundedAbove_projective_lift_representing_of_surjective.{u, v, u}
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective E K hEbdd hEprojective hErep
    (by simpa only [Ideal.mk_ker] using hI)

end NilpotentProjectiveLift

/-! ### Pseudo-coherence modulo a nilpotent ideal -/

section PseudoCoherenceModNilpotent

/-- A submodule of `M` whose image in `M / IM` is everything, for `I` nilpotent, is already
everything: `⊤ = N + I ⊤` iterates to `⊤ = N + I ^ k ⊤` for every `k`, and `I ^ k = 0`
eventually. -/
private theorem span_eq_top_of_nilpotent_of_sup_smul_top
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : IsNilpotent I) (N : Submodule R M)
    (hsup : (⊤ : Submodule R M) = N ⊔ I • ⊤) : N = ⊤ := by
  obtain ⟨c, hc⟩ := hI
  have key : ∀ k : ℕ, (⊤ : Submodule R M) = N ⊔ (I ^ k) • ⊤ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep : (I ^ k) • (⊤ : Submodule R M) ≤ N ⊔ (I ^ (k + 1)) • ⊤ := by
        rw [show (I ^ k) • (⊤ : Submodule R M) = I ^ k • (N ⊔ I • ⊤) by rw [← hsup],
          Submodule.smul_sup]
        apply sup_le
        · exact le_sup_of_le_left Submodule.smul_le_right
        · rw [← mul_smul, pow_succ]
          exact le_sup_right
      apply le_antisymm
      · calc
          (⊤ : Submodule R M) = N ⊔ (I ^ k) • ⊤ := ih
          _ ≤ N ⊔ (I ^ (k + 1)) • ⊤ := sup_le le_sup_left hstep
      · exact le_top
  have h := key c
  rw [hc] at h
  simpa using h.symm

/-- **Finiteness descends through a nilpotent surjection.** If the extension of scalars of `M`
along a surjection `f : R' → R` with nilpotent kernel is a finite `R`-module, then `M` is a
finite `R'`-module: lift a finite generating set of `M / (ker f) M` and apply
`span_eq_top_of_nilpotent_of_sup_smul_top`. -/
private theorem finite_of_finite_extendScalars_of_surjective_of_nilpotent
    {R' R M : Type*} [CommRing R'] [CommRing R] [AddCommGroup M] [Module R' M]
    (f : R' →+* R) (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    [Module.Finite R ((ModuleCat.extendScalars f).obj (ModuleCat.of R' M))] :
    Module.Finite R' M := by
  let : Algebra R' R := f.toAlgebra
  have : Module.Finite R' R :=
    Module.Finite.of_surjective (Algebra.linearMap R' R) hf
  let eRing := RingHom.quotientKerEquivOfSurjective hf
  let eLin : (R' ⧸ RingHom.ker f) ≃ₗ[R'] R :=
    eRing.toAddEquiv.toLinearEquiv fun r x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      show f (r * x) = f r * f x
      exact map_mul f r x
  let : Module R' ((ModuleCat.extendScalars f).obj (ModuleCat.of R' M) : Type _) :=
    Module.compHom _ f
  have : IsScalarTower R' R
      ((ModuleCat.extendScalars f).obj (ModuleCat.of R' M) : Type _) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : ((ModuleCat.extendScalars f).obj (ModuleCat.of R' M) : Type _) ≃ₗ[R']
      M ⧸ (RingHom.ker f • (⊤ : Submodule R' M)) :=
    (TensorProduct.AlgebraTensorModule.congr eLin.symm (LinearEquiv.refl R' M)).trans
      (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker f))
  have : Module.Finite R'
      ((ModuleCat.extendScalars f).obj (ModuleCat.of R' M) : Type _) :=
    Module.Finite.trans R _
  have : Module.Finite R' (M ⧸ (RingHom.ker f • (⊤ : Submodule R' M))) :=
    Module.Finite.equiv e
  obtain ⟨S, hSfin, hSspan⟩ :=
    (Submodule.fg_def.mp (Module.Finite.fg_top (R := R')
      (M := M ⧸ (RingHom.ker f • (⊤ : Submodule R' M)))))
  let T : Set M := Quotient.out '' S
  let N : Submodule R' M := Submodule.span R' T
  have hTfin : T.Finite := hSfin.image _
  have hNfg : N.FG := Submodule.fg_span hTfin
  have hmap : N.map (RingHom.ker f • (⊤ : Submodule R' M)).mkQ = ⊤ := by
    show (Submodule.span R' T).map (RingHom.ker f • (⊤ : Submodule R' M)).mkQ = ⊤
    rw [Submodule.map_span, Set.image_image]
    simpa [T] using hSspan
  have hsup : (⊤ : Submodule R' M) = N ⊔ RingHom.ker f • ⊤ := by
    apply_fun Submodule.comap (RingHom.ker f • (⊤ : Submodule R' M)).mkQ at hmap
    simpa [Submodule.comap_map_mkQ, sup_comm] using hmap.symm
  have hNtop := span_eq_top_of_nilpotent_of_sup_smul_top (RingHom.ker f) hnil N hsup
  exact ⟨hNtop ▸ hNfg⟩

/-- **Stacks 0H76.** Derived extension of scalars along a surjective map of commutative rings
with nilpotent kernel preserves *and reflects* pseudo-coherence.

Preservation is [stacks 0650]. Reflection is [stacks 09AR]: a bounded above finite projective
representative of the reduction, which exists by [stacks 064U], lifts to a bounded above
projective representative of `K`, whose terms are finite because their extensions of scalars
are and the kernel is nilpotent. -/
@[stacks 0H76, sga "6 I 2.16.2" "(i), punctual"]
public theorem isPseudoCoherent_derivedExtensionScalars_iff
    {R' R : Type u} [CommRing R'] [CommRing R] (f : R' →+* R)
    (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    (K : DerivedCategory (ModuleCat.{max v u} R')) :
    PseudoCoherence.IsPseudoCoherent
        ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj K) ↔
      PseudoCoherence.IsPseudoCoherent K := by
  constructor
  · intro hK
    obtain ⟨E, hEbdd, hEterms, hErep⟩ :=
      (StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
        ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj K) 0).2.1.mp hK
    obtain ⟨P, hPbdd, hPprojective, hPrep, hPE⟩ :=
      exists_boundedAbove_projective_lift_representing_of_surjective.{u, v, u}
        f hf E K hEbdd (fun i => (hEterms i).2) hErep hnil
    refine
      (StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
        K 0).2.1.mpr ⟨P, hPbdd, fun i => ⟨?_, hPprojective i⟩, hPrep⟩
    have : Module.Finite R (E.X i) := (hEterms i).1
    let ei : (E.X i : Type (max v u)) ≃ₗ[R]
        ((((ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P).X i : Type (max v u)) :=
      ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).mapIso
        hPE.some).symm.toLinearEquiv
    have : Module.Finite R
        ((((ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P).X i : Type (max v u)) :=
      Module.Finite.equiv ei
    have hfin : Module.Finite R
        ((ModuleCat.extendScalars.{u, u, max v u} f).obj (P.X i)) := by
      rw [← Functor.mapHomologicalComplex_obj_X]
      infer_instance
    exact finite_of_finite_extendScalars_of_surjective_of_nilpotent f hf hnil
  · exact (PseudoCoherence.totalDerivedExtensionScalars_preserves_pseudoCoherent f K).2

end PseudoCoherenceModNilpotent

/-! ### Perfection modulo a nilpotent ideal -/

section PerfectModNilpotent

/-- **Nakayama for finiteness over a nilpotent quotient.** A module whose reduction modulo a
nilpotent ideal is finite is itself finite: lift a finite generating set of the reduction. -/
@[sga "3 VIB 1.3.0" "special case"]
private lemma finite_of_finite_quotient_of_isNilpotent
    {R : Type u} [CommRing R] (I : Ideal R) (M : Type (max v u))
    [AddCommGroup M] [Module R M]
    [Module.Finite R (M ⧸ I • (⊤ : Submodule R M))]
    (hI : IsNilpotent I) : Module.Finite R M := by
  classical
  rw [Module.finite_def] at *
  obtain ⟨s, hs⟩ := ‹(⊤ : Submodule R (M ⧸ I • (⊤ : Submodule R M))).FG›
  let lift : M ⧸ I • (⊤ : Submodule R M) → M :=
    Function.surjInv (I • (⊤ : Submodule R M)).mkQ_surjective
  refine ⟨s.image lift, ?_⟩
  apply Submodule.span_eq_top_of_span_image_mkQ_eq_top_of_isNilpotent I hI
  rw [Finset.coe_image, Set.image_image]
  have himage :
      ((I • (⊤ : Submodule R M)).mkQ ∘ lift) '' (s : Set _) = (s : Set _) := by
    ext x
    simp [lift]
  show Submodule.span R (((I • (⊤ : Submodule R M)).mkQ ∘ lift) '' (s : Set _)) = ⊤
  rw [himage, hs]

/-- **Stacks 07LU.** An object of `D(R)` whose derived reduction modulo a nilpotent ideal `I` is
perfect is itself perfect.

A bounded complex of finite projective `R ⧸ I`-modules representing the reduction lifts, by
[stacks 09AR], to a bounded above complex `P` of projective `R`-modules representing `K`. Each
term of `P` is finite because its reduction is, by Nakayama for a nilpotent ideal
(`finite_of_finite_quotient_of_isNilpotent`), and `P` vanishes below the lower bound of the given
complex because a module with vanishing reduction modulo a nilpotent ideal vanishes. -/
@[stacks 07LU]
public theorem isPerfect_of_isPerfect_mod_isNilpotent
    {R : Type u} [CommRing R] (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{max v u} R))
    (hK : IsPerfect
      ((totalDerivedExtensionScalars.{u, u, v} (Ideal.Quotient.mk I)).functor.obj K))
    (hI : IsNilpotent I) :
    IsPerfect K := by
  obtain ⟨E, a, b, hEge, hEle, hEfinite, hEprojective, hErep⟩ := hK
  obtain ⟨P, hPle, hPprojective, hPrep, hPred⟩ :=
    exists_boundedAbove_projective_lift_representing.{u, v} I E K
      ⟨b, hEle⟩ hEprojective (hErep.map Iso.symm) hI
  refine ⟨P, a, hPle.choose, ?_, hPle.choose_spec, ?_, hPprojective, hPrep.map Iso.symm⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have hred : IsZero
        ((ModuleCat.extendScalars.{u, u, max v u} (Ideal.Quotient.mk I)).obj (P.X i)) :=
      (Iso.isZero_iff ((HomologicalComplex.eval _ (ComplexShape.up ℤ) i).mapIso hPred.some)).2
        (E.isZero_of_isStrictlyGE a i hi)
    apply ModuleCat.isZero_iff_subsingleton.mpr
    have : Subsingleton ((P.X i) ⧸ I • (⊤ : Submodule R (P.X i))) :=
      ⟨fun x y ↦ (extendScalarsQuotEquiv.{u, v} I (P.X i)).symm.injective <|
        @Subsingleton.elim _ (ModuleCat.isZero_iff_subsingleton.mp hred) _ _⟩
    have htop : (⊤ : Submodule R (P.X i)) ≤ I • ⊤ := by
      intro x _
      rw [← Submodule.Quotient.mk_eq_zero]
      exact Subsingleton.elim _ _
    have hz := Submodule.eq_bot_of_le_smul_of_isNilpotent I
      (⊤ : Submodule R (P.X i)) hI htop
    exact ⟨fun x y ↦ sub_eq_zero.mp <| by
      have hxy : x - y ∈ (⊤ : Submodule R (P.X i)) := trivial
      rw [hz] at hxy
      exact hxy⟩
  · intro i
    have : Module.Finite (R ⧸ I)
        ((HomologicalComplex.eval (ModuleCat.{max v u} (R ⧸ I)) (ComplexShape.up ℤ) i).obj E) :=
      hEfinite i
    have : Module.Finite (R ⧸ I) ((P.X i) ⧸ I • (⊤ : Submodule R (P.X i))) :=
      Module.Finite.equiv ((extendScalarsQuotEquiv.{u, v} I (P.X i)).symm.trans
        ((HomologicalComplex.eval _ (ComplexShape.up ℤ) i).mapIso hPred.some).toLinearEquiv).symm
    have : Module.Finite R ((P.X i) ⧸ I • (⊤ : Submodule R (P.X i))) :=
      Module.Finite.trans (R ⧸ I) _
    exact finite_of_finite_quotient_of_isNilpotent.{u, v} I (P.X i) hI

end PerfectModNilpotent

end StacksDraft.Perfect

end
