module

public import StacksFrontier.AlgebraicGeometry.SchemeJTwoLocal.JTwoTFAE
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwo
public import StacksFrontier.RingTheory.Regular.SingularLocus

/-!
# Local criteria for a scheme to be J-2

For a locally Noetherian scheme the J-2 condition is local: it can be tested on the members of
an arbitrary open covering, on the ring of sections of every affine open, or on the rings of
sections of the members of a single affine open covering. The condition is moreover inherited
by every scheme locally of finite type over the given one, and on an affine scheme it is the
ring-theoretic J-2 condition of its ring of sections.

## Main results

* `AlgebraicGeometry.Scheme.isJ2_of_locallyOfFiniteType`: a scheme locally of finite type over
  a J-2 scheme is J-2.
* `AlgebraicGeometry.Scheme.isJ2_tfae`: the four equivalent local characterizations.
* `AlgebraicGeometry.Scheme.isJ2_Spec_iff`: on the spectrum of a Noetherian ring the
  scheme-theoretic and the ring-theoretic J-2 conditions agree.

## Implementation notes

An open covering is an indexed family of opens whose supremum is `⊤`. Passing from an arbitrary
open covering to an affine one refines each member by the affine opens it contains, which is the
only place the basis of affine opens is used.

Local Noetherianity of a scheme locally of finite type over a locally Noetherian base is
automatic, by `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`. Since
`AlgebraicGeometry.Scheme.IsJ2` takes local Noetherianity as an instance argument, the statements
below request it as an instance argument too rather than carrying a `letI` in their types; being
a `Prop`, which proof is supplied makes no difference to the resulting statement.

The ring-theoretic condition is stated for the section ring `Γ(X, U)` of an affine open, which on
a spectrum differs from the original ring by `AlgebraicGeometry.Scheme.ΓSpecIso`. Transporting
the condition along a ring isomorphism is immediate from its definition, an isomorphism being of
finite type.

## References

* [Stacks Project, Tag 07R4](https://stacks.math.columbia.edu/tag/07R4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Regularity of a local ring is invariant under ring isomorphism. -/
private lemma isRegularLocalRing_iff_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : IsRegularLocalRing A ↔ IsRegularLocalRing B :=
  ⟨fun _ => IsRegularLocalRing.of_ringEquiv e, fun _ => IsRegularLocalRing.of_ringEquiv e.symm⟩

/-- On a spectrum the regular locus is the set of primes with regular localization: the stalk at
a prime is the localization there. -/
private lemma regularLocus_Spec (R : Type u) [CommRing R] :
    regularLocus (Spec (.of R)) =
      {p : PrimeSpectrum R | IsRegularLocalRing (Localization.AtPrime p.asIdeal)} := by
  ext p
  let : p.asIdeal.IsPrime := p.2
  change IsRegularLocalRing ((Spec (.of R)).presheaf.stalk p) ↔
    IsRegularLocalRing (Localization.AtPrime p.asIdeal)
  exact isRegularLocalRing_iff_of_ringEquiv (Spec.stalkIso (.of R) p).commRingCatIsoToRingEquiv

/-- An open immersion identifies stalks, hence pulls the regular locus back to the regular
locus. -/
private lemma preimage_regularLocus {S T : Scheme.{u}} (f : S ⟶ T) [IsOpenImmersion f] :
    f.base ⁻¹' regularLocus T = regularLocus S := by
  ext x
  change IsRegularLocalRing (T.presheaf.stalk (f x)) ↔ IsRegularLocalRing (S.presheaf.stalk x)
  have : IsIso (f.stalkMap x) := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 x
  exact isRegularLocalRing_iff_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

/-- Openness of the regular locus of an affine open is the J-1 condition on its section ring. -/
private theorem isOpen_regularLocus_affineOpen_iff {X : Scheme.{u}} (U : X.affineOpens) :
    IsOpen (regularLocus U.1.toScheme) ↔ _root_.IsJ1 Γ(X, U.1) := by
  let e := U.2.isoSpec
  have hsurj : Function.Surjective e.hom.base :=
    (ConcreteCategory.bijective_of_isIso (C := TopCat) _).surjective
  calc
    IsOpen (regularLocus U.1.toScheme) ↔
        IsOpen (e.hom.base ⁻¹' regularLocus (Spec (.of Γ(X, U.1)))) :=
      Iff.of_eq (congrArg IsOpen (preimage_regularLocus e.hom).symm)
    _ ↔ IsOpen (regularLocus (Spec (.of Γ(X, U.1)))) :=
      ((TopCat.homeoOfIso (asIso e.hom.base)).isOpenEmbedding.isOpen_iff_preimage_isOpen
        fun y _ => Set.mem_range.mpr (hsurj y)).symm
    _ ↔ _root_.IsJ1 Γ(X, U.1) := isOpen_regularLocus_spec_iff _

/-- If an affine open is J-2 as a scheme, its section ring is J-2. -/
private theorem isJ2_sectionRing_of_isJ2_affineOpen_noetherianOpen {X : Scheme.{u}}
    (U : X.affineOpens) [IsLocallyNoetherian U.1.toScheme] (hU : IsJ2 U.1.toScheme) :
    _root_.IsJ2 Γ(X, U.1) := by
  intro A _ _ _
  let φ : CommRingCat.of Γ(X, U.1) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (algebraMap Γ(X, U.1) A)
  have : LocallyOfFiniteType (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have : LocallyOfFiniteType (Spec.map φ ≫ U.2.isoSpec.inv) := locallyOfFiniteType_comp _ _
  exact (isOpen_regularLocus_spec_iff A).mp
    (hU.isOpen_regularLocus (Spec.map φ ≫ U.2.isoSpec.inv))

/-- The preimages of the members of an open covering form an open covering. -/
private lemma isOpenCover_preimage {X Y : Scheme.{u}} (f : Y ⟶ X) {ι : Type u} {U : ι → X.Opens}
    (hU : IsOpenCover U) : IsOpenCover fun i => f ⁻¹ᵁ U i := by
  refine Opens.ext (Set.eq_univ_of_forall fun y => ?_)
  obtain ⟨i, hi⟩ := hU.exists_mem (f y)
  simpa only [Opens.coe_iSup, Set.mem_iUnion] using ⟨i, hi⟩

/-- Refining every member of an open covering by the affine opens it contains gives an affine
open covering. -/
private lemma isOpenCover_affineOpens_le {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}
    (hU : IsOpenCover U) :
    IsOpenCover fun j : Σ i, {V : X.affineOpens // (V : X.Opens) ≤ U i} =>
      (j.2.1 : X.Opens) := by
  refine Opens.ext (Set.eq_univ_of_forall fun x => ?_)
  simp only [Opens.coe_iSup, Set.mem_iUnion]
  obtain ⟨i, hi⟩ := hU.exists_mem x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hi (U i).2
  exact ⟨⟨i, ⟨⟨W, hW⟩, hWU⟩⟩, hxW⟩

/-- If the section rings of an affine open covering are J-2, the regular locus of every scheme
locally of finite type over the base is open. -/
@[ega "IV 7.8.6" "more general"]
private theorem isOpen_regularLocus_of_isJ2_affineCover {X Y : Scheme.{u}} {ι : Type u}
    (U : ι → X.affineOpens) (hU : (⨆ i, (U i : X.Opens)) = ⊤)
    (hJ2 : ∀ i, _root_.IsJ2 Γ(X, (U i : X.Opens))) (f : Y ⟶ X) [LocallyOfFiniteType f] :
    IsOpen (regularLocus Y) := by
  have hV := isOpenCover_affineOpens_le (isOpenCover_preimage f (IsOpenCover.mk hU))
  rw [hV.isOpen_iff_coe_preimage]
  intro j
  let : Algebra Γ(X, (U j.1 : X.Opens)) Γ(Y, (j.2.1.1 : Y.Opens)) :=
    (f.appLE (U j.1).1 j.2.1.1 j.2.2).hom.toAlgebra
  have : Algebra.FiniteType Γ(X, (U j.1 : X.Opens)) Γ(Y, (j.2.1.1 : Y.Opens)) :=
    f.finiteType_appLE (U j.1).2 j.2.1.2 j.2.2
  exact preimage_regularLocus (Scheme.Opens.ι j.2.1.1) ▸
    (isOpen_regularLocus_affineOpen_iff j.2.1).2 (hJ2 j.1 Γ(Y, (j.2.1.1 : Y.Opens)))

/-- The ring-theoretic J-2 condition transports along a ring isomorphism: an isomorphism is of
finite type, so the two rings have the same finite type algebras. -/
private lemma isJ2_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    (h : _root_.IsJ2 A) : _root_.IsJ2 B := by
  let : Algebra A B := e.toRingHom.toAlgebra
  have : Algebra.FiniteType A B :=
    Algebra.FiniteType.equiv inferInstance (AlgEquiv.ofRingEquiv (R := A) (f := e) fun _ => rfl)
  intro C _ _ _
  let : Algebra A C := ((algebraMap B C).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType A C := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  exact h C

/-- **Stacks Project, Tag 07R4.** On the spectrum of a Noetherian ring the scheme-theoretic J-2
condition is the ring-theoretic one. -/
@[stacks 07R4 "the affine case"]
public theorem isJ2_Spec_iff (R : Type u) [CommRing R] [IsNoetherianRing R] :
    IsJ2 (Spec (.of R)) ↔ _root_.IsJ2 R := by
  constructor
  · intro h
    have h3 : ∀ U : (Spec (.of R)).affineOpens, _root_.IsJ2 Γ(Spec (.of R), (U : _)) :=
      ((isJ2_tfae (Spec (.of R))).out 1 3).mp h
    exact isJ2_of_ringEquiv (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
      (h3 ⟨⊤, isAffineOpen_top _⟩)
  · intro h
    have h4 : ∃ (I : Type u) (U : I → (Spec (.of R)).affineOpens),
        (⨆ i, (U i : (Spec (.of R)).Opens)) = ⊤ ∧
          ∀ i, _root_.IsJ2 Γ(Spec (.of R), (U i : _)) :=
      ⟨PUnit.{u + 1}, fun _ => ⟨⊤, isAffineOpen_top _⟩, by simp,
        fun _ => isJ2_of_ringEquiv (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv h⟩
    exact ((isJ2_tfae (Spec (.of R))).out 4 1).mp h4

end AlgebraicGeometry.Scheme
