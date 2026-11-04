module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import StacksFrontier.AlgebraicGeometry.Seminormalization.CandidateCategory
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RingColimit

/-!
# Transporting the candidate conditions along algebra maps, and finding a presentation

For a commutative ring `A`, the objects of `Algebra.SeminormalizationIndex A` are explicit
finite presentations `P` whose structure morphism `Spec P.algebra ⟶ Spec A` is a universal
homeomorphism inducing isomorphisms on all residue fields.  This file supplies the three
operations on that pair of conditions which the filteredness of the index needs: transport
along an isomorphism of `A`-algebras, composition with a quotient by an ideal of nilpotents,
and the passage from an abstract finitely presented `A`-algebra with those two properties to an
object of `Algebra.SeminormalizationIndex A` isomorphic to it.

## Main results

* `AlgebraicGeometry.universalHomeomorphism_specMap_of_algEquiv` and
  `AlgebraicGeometry.isIso_residueFieldMap_specMap_of_algEquiv`: both conditions transport
  along an isomorphism of `A`-algebras.
* `AlgebraicGeometry.universalHomeomorphism_specMap_quotient_of_nilpotent` and
  `AlgebraicGeometry.isIso_residueFieldMap_specMap_quotient_of_nilpotent`: the quotient map by
  an ideal all of whose elements are nilpotent is a universal homeomorphism on spectra and
  induces isomorphisms on all residue fields.
* `AlgebraicGeometry.exists_seminormalizationIndex_algEquiv`: a finitely presented `A`-algebra
  satisfying the two conditions is isomorphic to the algebra of an object of
  `Algebra.SeminormalizationIndex A`.

## Implementation notes

`AlgebraicGeometry.specMap_algebraMap_eq_comp` records that an `A`-algebra map `φ : R ⟶ S`
factors the structure morphism of `S` over `A` through that of `R`; every transport statement
here is that factorization followed by the two-out-of-three property of universal
homeomorphisms and by `AlgebraicGeometry.Scheme.residueFieldMap_comp`.  The nilpotent quotient
is handled through the characterization of universal homeomorphisms as the integral,
universally injective, surjective morphisms: such a quotient map is a closed immersion, hence
integral and universally injective, and surjective on spectra because the ideal lies in the
nilradical.

The presentation statement is a `Nonempty` of a sigma type rather than a choice of data, so
that no arbitrary presentation is baked into a definition; a user who needs the data applies
`Classical.choice`.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

No hypothesis beyond those of Tag 0EUS is used: the rings are arbitrary commutative rings,
with no Noetherian or reducedness assumption, and finite presentation is assumed only where it
is part of the definition of `Algebra.SeminormalizationIndex`.

## What is not done

Nothing here mentions the category structure on `Algebra.SeminormalizationIndex A`, a colimit
or a cocone; filteredness of the index is proved in
`StacksFrontier.AlgebraicGeometry.Seminormalization.IndexFiltered`.  No statement here is
about `AlgebraicGeometry.IsSeminormalizationCandidate`, which is a property of objects of
`Over X` for a scheme `X` rather than of algebras.

## References

* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {A R S : Type u} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]

/-- An `A`-algebra map `φ : R →ₐ[A] S` factors the structure morphism of `Spec S` over
`Spec A` through the structure morphism of `Spec R`. -/
theorem specMap_algebraMap_eq_comp (φ : R →ₐ[A] S) :
    Spec.map (CommRingCat.ofHom (algebraMap A S)) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A R)) := by
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact (φ.commutes a).symm

/-- If `Spec R ⟶ Spec A` and `Spec S ⟶ Spec R` are universal homeomorphisms, so is
`Spec S ⟶ Spec A`. -/
theorem universalHomeomorphism_specMap_comp_algHom (φ : R →ₐ[A] S)
    (hR : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A R))))
    (hφ : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom φ.toRingHom))) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A S))) := by
  rw [specMap_algebraMap_eq_comp φ]
  exact hasTwoOutOfThreeProperty_universalHomeomorphism.comp_mem _ _ hφ hR

/-- If `Spec R ⟶ Spec A` and `Spec S ⟶ Spec R` induce isomorphisms on all residue fields, so
does `Spec S ⟶ Spec A`. -/
theorem isIso_residueFieldMap_specMap_comp_algHom (φ : R →ₐ[A] S)
    (hR : ∀ y : Spec (CommRingCat.of R),
      IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A R))).residueFieldMap y))
    (hφ : ∀ x : Spec (CommRingCat.of S),
      IsIso ((Spec.map (CommRingCat.ofHom φ.toRingHom)).residueFieldMap x))
    (x : Spec (CommRingCat.of S)) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A S))).residueFieldMap x) := by
  rw [specMap_algebraMap_eq_comp φ, Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' (hR _) (hφ x)

/-- The map on spectra induced by an isomorphism of `A`-algebras is an isomorphism. -/
private lemma isIso_specMap_toAlgHom (e : R ≃ₐ[A] S) :
    IsIso (Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom)) :=
  inferInstanceAs (IsIso (Spec.map (RingEquiv.toCommRingCatIso e.toRingEquiv).hom))

/-- Being a universal homeomorphism over `Spec A` transports along an isomorphism of
`A`-algebras. -/
theorem universalHomeomorphism_specMap_of_algEquiv (e : R ≃ₐ[A] S)
    (hR : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A R)))) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A S))) := by
  have := isIso_specMap_toAlgHom e
  exact universalHomeomorphism_specMap_comp_algHom e.toAlgHom hR
    (universalHomeomorphism_of_isIso _)

/-- Inducing isomorphisms on all residue fields transports along an isomorphism of
`A`-algebras. -/
theorem isIso_residueFieldMap_specMap_of_algEquiv (e : R ≃ₐ[A] S)
    (hR : ∀ y : Spec (CommRingCat.of R),
      IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A R))).residueFieldMap y))
    (x : Spec (CommRingCat.of S)) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A S))).residueFieldMap x) := by
  have := isIso_specMap_toAlgHom e
  exact isIso_residueFieldMap_specMap_comp_algHom e.toAlgHom hR (fun _ => inferInstance) x

/-- The quotient of a commutative ring by an ideal all of whose elements are nilpotent gives a
universal homeomorphism on spectra. -/
theorem universalHomeomorphism_specMap_quotient_of_nilpotent (R : Type u) [CommRing R]
    (I : Ideal R) (hI : ∀ x ∈ I, IsNilpotent x) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  let F := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hs : Surjective F := ⟨by
    show Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.mk I))
    exact (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical
      fun x hx => mem_nilradical.mpr (hI x hx)).2⟩
  have hc : IsClosedImmersion F :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact (universalHomeomorphism_iff_integral_universallyInjective_surjective F).mpr
    ⟨inferInstance, inferInstance, hs⟩

/-- The quotient of a commutative ring by any ideal induces isomorphisms on all residue
fields, because it is a closed immersion on spectra. -/
theorem isIso_residueFieldMap_specMap_quotient (R : Type u) [CommRing R] (I : Ideal R)
    (x : Spec (CommRingCat.of (R ⧸ I))) :
    IsIso ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).residueFieldMap x) := by
  let f := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hf : IsClosedImmersion f :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hsurj : Function.Surjective (f.residueFieldMap x).hom := by
    intro y
    obtain ⟨z, hz⟩ := (Spec (CommRingCat.of (R ⧸ I))).residue_surjective x y
    obtain ⟨w, hw⟩ := hf.stalkMap_surjective x z
    refine ⟨(Spec (CommRingCat.of R)).residue (f x) w, ?_⟩
    have heq := congrArg (fun φ => φ w)
      (congrArg CommRingCat.Hom.hom (Scheme.residue_residueFieldMap f x))
    change (f.residueFieldMap x).hom ((Spec (CommRingCat.of R)).residue (f x) w) =
      (Spec (CommRingCat.of (R ⧸ I))).residue x (f.stalkMap x w) at heq
    rwa [hw, hz] at heq
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨RingHom.injective _, hsurj⟩

/-- A finitely presented `A`-algebra whose structure morphism on spectra is a universal
homeomorphism inducing isomorphisms on all residue fields is isomorphic, as an `A`-algebra, to
the algebra of an object of `Algebra.SeminormalizationIndex A`. -/
theorem exists_seminormalizationIndex_algEquiv (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] (hfp : Algebra.FinitePresentation A C)
    (huh : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A C))))
    (hres : ∀ x : Spec (CommRingCat.of C),
      IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A C))).residueFieldMap x)) :
    Nonempty (Σ P : Algebra.SeminormalizationIndex A, P.obj.algebra ≃ₐ[A] C) := by
  obtain ⟨n, I, e, hI⟩ := (Algebra.FinitePresentation.iff (R := A) (A := C)).mp hfp
  let P : Algebra.FinitelyPresentedAlgebraPresentation A := ⟨n, I, hI⟩
  let eP : P.algebra ≃ₐ[A] C :=
    { toRingEquiv := e.toRingEquiv
      commutes' := by
        intro a
        show e.toRingEquiv (algebraMap A (MvPolynomial (Fin n) A ⧸ I) a) = algebraMap A C a
        exact e.commutes a }
  exact ⟨⟨⟨P, universalHomeomorphism_specMap_of_algEquiv eP.symm huh,
    isIso_residueFieldMap_specMap_of_algEquiv eP.symm hres⟩, eP⟩⟩

end AlgebraicGeometry

end
