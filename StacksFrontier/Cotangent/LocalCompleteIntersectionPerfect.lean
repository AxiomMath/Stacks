module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Flat.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.NaiveComparison
public import StacksFrontier.Cotangent.TensorProduct
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Defs
public import StacksFrontier.RingTheory.NaiveCotangent.ConormalFiniteProjective

/-!
# The cotangent complex of a local complete intersection is perfect of amplitude `[-1, 0]`

Let `A → B` be a local complete intersection map, so that `B = A[x₁, …, x_n]/J` with `J`
Koszul-regular for some — equivalently any — finite polynomial presentation. Then `L_{B/A}` is a
perfect object of `D(B)` with Tor amplitude in `[-1, 0]`.

The source's proof picks a finite polynomial presentation `P = A[x₁, …, x_n] → B` with kernel
`J` and runs in two steps.

1. The two-term complex `NL(P → B) : J/J² → ⨁ B dxᵢ` consists of finite projective `B`-modules:
   its degree-`0` term is free on the variables, and its degree `-1` term `J/J²` is finite
   projective because a Koszul-regular ideal is quasi-regular (Tag 062I) and the conormal module
   of a quasi-regular ideal is finite projective (Tag 08RK). Independence of the presentation is
   Tag 07CZ.
2. `L_{B/A}` is quasi-isomorphic to `NL(P → B)`. The source gets this from Tag 08RB, which
   identifies `NL(P → B)` with `τ_{≥ -1} L_{B/A}`, together with Tag 08SK, which kills
   `Hⁱ(L_{B/P})` outside `{-1, 0}` and hence — through the fundamental triangle 08QS of
   `A → P → B` and the computation 08QH of `L_{P/A}` for a polynomial algebra — kills
   `Hⁱ(L_{B/A})` outside `[-1, 0]`.

Step 1 is what this file proves. Step 2 is **not** available in this library: of Tag 08RB only
the degree-zero clause `CommAlgCat.cotangentComplexHomologyZeroIsoNaive` is formalized, the
comparison map of Tag 08R7 is not constructed, and Tag 08SK is absent altogether. The
quasi-isomorphism of step 2 is therefore a hypothesis of the theorem below, recorded as an
isomorphism in `D(B)` between `L_{B/A}` and the naive complex of the given presentation. It is
the content of two *other* Stacks tags, and it is strictly weaker than the conclusion: on its own
it says nothing about the terms of `NL(P → B)`, which is exactly where the
local-complete-intersection hypothesis does its work.

## Main results

* `CommAlgCat.isPerfect_and_hasTorAmplitude_naiveComplex_of_isLocalCompleteIntersection`: step 1,
  unconditionally. For a local complete intersection `A → B`, the naive cotangent complex of
  every finite polynomial presentation of `B` over `A` is perfect with Tor amplitude in
  `[-1, 0]`.
* `CommAlgCat.isPerfect_and_hasTorAmplitude_cotangentComplexDerived_of_isLocalCompleteIntersection`:
  **Tag 08SL**, in the conditional form described above. Both assertions of the source —
  perfectness and Tor amplitude in `[-1, 0]` — are proved.

## Implementation notes

Perfectness is `StacksDraft.Perfect.IsPerfect` (Tag 0657 (1)): an isomorphism in `D(B)` with a
bounded complex of finite projective modules. Tor amplitude is
`StacksDraft.TorAmplitude.HasTorAmplitudeCanonical` (Tag 0652 (1) read at the canonical derived
tensor product of Tag 0BYI); it is obtained from the same complex through Tag 0654, since a
projective module is flat. The cotangent complex is `CommAlgCat.cotangentComplexDerived` (Tag
08PN, localized), and the naive complex of a presentation is
`Algebra.Extension.naiveComplex` (Tag 08R9).

A finite polynomial presentation is `Algebra.Generators A B ι` with `ι` finite; its
`Algebra.Generators.toExtension` has underlying ring `MvPolynomial ι A`, so the ring of the
presentation, the algebra `B` and the modules all live in one universe, which is the universe the
naive complex and the Tor-amplitude predicate are stated in. This is the universe pattern the
rest of the cotangent library uses for derived-category statements, as in
`CommAlgCat.isZero_cotangentComplexDerived_of_etale`.

## References

* [Stacks Project, Tag 08SL](https://stacks.math.columbia.edu/tag/08SL)
* [Stacks Project, Tag 08RK](https://stacks.math.columbia.edu/tag/08RK)
* [Stacks Project, Tag 07CZ](https://stacks.math.columbia.edu/tag/07CZ)
* [Stacks Project, Tag 0654](https://stacks.math.columbia.edu/tag/0654)
* [Stacks Project, Tag 0657](https://stacks.math.columbia.edu/tag/0657)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CommAlgCat

/-! ### The terms of the naive complex -/

/-- Finiteness and projectivity transport along an isomorphism of modules. -/
private lemma finite_projective_of_iso {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (e : M ≅ N) (hfin : Module.Finite R N) (hproj : Module.Projective R N) :
    Module.Finite R M ∧ Module.Projective R M :=
  ⟨Module.Finite.equiv e.symm.toLinearEquiv, Module.Projective.of_equiv e.symm.toLinearEquiv⟩

/-- A zero module is finite and projective. -/
private lemma finite_projective_of_isZero {R : Type u} [Ring R] {M : ModuleCat.{u} R}
    (h : IsZero M) : Module.Finite R M ∧ Module.Projective R M := by
  have hs : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp h
  have hfree : Module.Free R ↥M := Module.Free.of_subsingleton R ↥M
  exact ⟨Module.Finite.of_surjective (0 : R →ₗ[R] M)
      (fun x => ⟨0, Subsingleton.elim _ _⟩), Module.Projective.of_free⟩

/-- For a local complete intersection, every term of the naive cotangent complex of a finite
polynomial presentation is a finite projective module: the degree `-1` term is the conormal
module `J/J²`, finite projective by
`Algebra.Generators.cotangent_finite_projective_of_isLocalCompleteIntersection`,
the degree `0` term is free on the variables, and all other terms vanish. -/
@[sga "3 III 4.22" "Affine case", sga "6 0 4.4" "partial"]
private lemma finite_projective_naiveComplex_X
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {ι : Type u} [Finite ι]
    (P : Algebra.Generators A B ι)
    (h : RingHom.IsLocalCompleteIntersection (algebraMap A B)) (i : ℤ) :
    Module.Finite B ((Algebra.Extension.naiveComplex P.toExtension).X i) ∧
      Module.Projective B ((Algebra.Extension.naiveComplex P.toExtension).X i) := by
  by_cases hone : i = -1
  · subst hone
    obtain ⟨hfin, hproj⟩ :=
      Algebra.Generators.cotangent_finite_projective_of_isLocalCompleteIntersection P h
    exact finite_projective_of_iso
      (Algebra.Extension.naiveComplexXNegOneIso P.toExtension) hfin hproj
  · by_cases hzero : i = 0
    · subst hzero
      exact finite_projective_of_iso (Algebra.Extension.naiveComplexXZeroIso P.toExtension)
        (Module.Finite.of_basis P.cotangentSpaceBasis) inferInstance
    · exact finite_projective_of_isZero
        (Algebra.Extension.isZero_naiveComplex_X P.toExtension i hone hzero)

/-- The naive cotangent complex of a presentation is concentrated in degrees `≥ -1`. -/
private lemma naiveComplex_isStrictlyGE {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Extension.{u} A B) :
    (Algebra.Extension.naiveComplex P).IsStrictlyGE (-1) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact Algebra.Extension.isZero_naiveComplex_X P i (by omega) (by omega)

/-- The naive cotangent complex of a presentation is concentrated in degrees `≤ 0`. -/
private lemma naiveComplex_isStrictlyLE {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (P : Algebra.Extension.{u} A B) :
    (Algebra.Extension.naiveComplex P).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact Algebra.Extension.isZero_naiveComplex_X P i (by omega) (by omega)

/-! ### Perfectness and Tor amplitude -/

/-- An object of `D(B)` isomorphic to the naive cotangent complex of a finite polynomial
presentation of a local complete intersection `A → B` is perfect with Tor amplitude in
`[-1, 0]`. -/
@[sga "6 0 4.4" "special case"]
private lemma isPerfect_and_hasTorAmplitude_of_iso_naiveComplex
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {ι : Type u} [Finite ι]
    (P : Algebra.Generators A B ι)
    (hlci : RingHom.IsLocalCompleteIntersection (algebraMap A B))
    (K : DerivedCategory (ModuleCat.{u} B))
    (e : K ≅ DerivedCategory.Q.obj (Algebra.Extension.naiveComplex P.toExtension)) :
    StacksDraft.Perfect.IsPerfect K ∧
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical B K (-1) 0 := by
  have hterm := finite_projective_naiveComplex_X P hlci
  have hGE := naiveComplex_isStrictlyGE P.toExtension
  have hLE := naiveComplex_isStrictlyLE P.toExtension
  refine ⟨⟨Algebra.Extension.naiveComplex P.toExtension, -1, 0, hGE, hLE,
    fun i => (hterm i).1, fun i => (hterm i).2, ⟨e⟩⟩, ?_⟩
  rw [StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative]
  refine ⟨Algebra.Extension.naiveComplex P.toExtension, fun i => ?_, hGE, hLE, ⟨e⟩⟩
  have := (hterm i).2
  exact Module.Flat.of_projective

/-- For a local complete intersection map `A → B`, the naive cotangent complex `NL(P → B)` of
every finite polynomial presentation `P → B` of `B` over `A` is a perfect object of `D(B)` with
Tor amplitude in `[-1, 0]`.

This is the unconditional content of Stacks 08SL's proof: the two terms of `NL(P → B)` are the
conormal module `J/J²` of the presentation, finite projective by Tag 08RK through Tags 07CZ and
062I, and the free module `⨁ B dxᵢ` on the variables. Passing from here to `L_{B/A}` needs the
quasi-isomorphism `NL(P → B) ≅ L_{B/A}` of Tags 08RB and 08SK, which is why
`isPerfect_and_hasTorAmplitude_cotangentComplexDerived_of_isLocalCompleteIntersection` takes it
as a hypothesis. -/
theorem isPerfect_and_hasTorAmplitude_naiveComplex_of_isLocalCompleteIntersection
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {ι : Type u} [Finite ι]
    (P : Algebra.Generators A B ι)
    (hlci : RingHom.IsLocalCompleteIntersection (algebraMap A B)) :
    StacksDraft.Perfect.IsPerfect
        (DerivedCategory.Q.obj (Algebra.Extension.naiveComplex P.toExtension)) ∧
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical B
        (DerivedCategory.Q.obj (Algebra.Extension.naiveComplex P.toExtension)) (-1) 0 :=
  isPerfect_and_hasTorAmplitude_of_iso_naiveComplex P hlci _ (Iso.refl _)

/-- **Stacks 08SL.** Let `A → B` be a local complete intersection map. Then the cotangent complex
`L_{B/A}` is a perfect object of `D(B)` with Tor amplitude in `[-1, 0]`.

The quasi-isomorphism `L_{B/A} ≅ NL(P → B)` with the naive complex of a finite polynomial
presentation `P` is taken as the hypothesis `e`: it is the conjunction of Tag 08RB and Tag 08SK,
neither of which is available in this library (see the module documentation). What the local
complete intersection hypothesis supplies, and what is proved here, is that the two terms of
`NL(P → B)` are finite projective `B`-modules — the conormal module `J/J²` by Tag 08RK through
Tags 07CZ and 062I, and `⨁ B dxᵢ` by the canonical basis of the cotangent space. Perfectness is
then immediate from the definition and the Tor-amplitude bound follows by Tag 0654, a projective
module being flat. -/
@[stacks 08SL "perfectness and Tor amplitude in [-1, 0] are both proved, conditionally on the
hypothesis e that L_{B/A} is isomorphic in D(B) to the naive complex of the given finite
polynomial presentation; that isomorphism is Tag 08RB (only its degree-zero clause is in this
library) together with Tag 08SK (absent from this library). All the local complete intersection
hypothesis is used for, finite projectivity of the two terms, is proved"]
theorem isPerfect_and_hasTorAmplitude_cotangentComplexDerived_of_isLocalCompleteIntersection
    (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) {ι : Type u} [Finite ι]
    (P : Algebra.Generators A ↥B ι)
    (hlci : RingHom.IsLocalCompleteIntersection (algebraMap A ↥B))
    (e : cotangentComplexDerived.{u, u} A B ≅
      DerivedCategory.Q.obj (Algebra.Extension.naiveComplex P.toExtension)) :
    StacksDraft.Perfect.IsPerfect (cotangentComplexDerived.{u, u} A B) ∧
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical ↥B
        (cotangentComplexDerived.{u, u} A B) (-1) 0 :=
  isPerfect_and_hasTorAmplitude_of_iso_naiveComplex P hlci _ e

end CommAlgCat

end
