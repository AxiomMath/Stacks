module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Residue fields of affine schemes and of prime ideals

A point of `Spec R` has two residue fields: the scheme-theoretic one, `(Spec R).residueField`,
and the algebraic one, `Ideal.ResidueField` of the corresponding prime. They agree, and a
morphism `Spec.map f` induces the same map on both. This file records that comparison and
the transfer of `IsIso` across it, so that a statement about scheme-theoretic residue fields
can be proved by a computation with `Ideal.ResidueField.map`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.specResidueFieldMap_bridge` identifies the residue-field map of
  `Spec.map f` with `Ideal.ResidueField.map` of the underlying ring map.
* `AlgebraicGeometry.idealResidueFieldMap_isIso_of_specMap` and
  `AlgebraicGeometry.specResidueFieldMap_isIso_of_idealResidueFieldMap` transfer `IsIso`
  in either direction across that identification.
* `AlgebraicGeometry.idealResidueFieldMap_comp` is the composition law for
  `Ideal.ResidueField.map`, and `AlgebraicGeometry.idealResidueFieldMap_id_isIso` says that the
  map attached to the identity and two equal primes is an isomorphism.
* `AlgebraicGeometry.isIso_residueFieldMap_of_isIso_comp` cancels a composite in the second
  factor of a residue-field map.

## Implementation notes

The comparison isomorphism is Mathlib's `Scheme.Spec.residueFieldIso`. Conjugating by it turns
the scheme-theoretic map into the algebraic one; both directions of the resulting `IsIso`
transfer are recorded because the proofs below use each of them.

## References

* [Stacks Project, Tag 0CN7](https://stacks.math.columbia.edu/tag/0CN7)
* [Stacks Project, Tag 0CN8](https://stacks.math.columbia.edu/tag/0CN8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A point of an affine scheme is a prime ideal of the ring, so its underlying ideal is
prime. This bridging instance lets `Ideal.ResidueField` be applied to a point of `Spec R`. -/
instance specPoint_asIdeal_isPrime (R : CommRingCat.{u}) (y : Spec R) :
    y.asIdeal.IsPrime :=
  y.isPrime

/-- Conjugating the residue-field map of `Spec.map f` by the comparison isomorphisms between
the scheme-theoretic and the algebraic residue fields yields `Ideal.ResidueField.map` of the
underlying ring map. -/
lemma specResidueFieldMap_bridge {R T : CommRingCat.{u}} (f : R ⟶ T) (z : Spec T) :
    ((Scheme.Spec.residueFieldIso R (Spec.map f z)).inv ≫
      (Spec.map f).residueFieldMap z ≫ (Scheme.Spec.residueFieldIso T z).hom).hom =
      Ideal.ResidueField.map (Spec.map f z).asIdeal z.asIdeal f.hom
        (by simpa only [Spec.map_apply] using PrimeSpectrum.comap_asIdeal f.hom z) := by
  apply Ideal.ResidueField.ringHom_ext
  ext r
  simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
  have H := (Spec.map f).SpecMap_residueFieldMap_fromSpecResidueField z
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R (Spec.map f z),
    ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField T z] at H
  simp only [← Spec.map_comp, Category.assoc] at H
  have H' := Spec.map_injective H
  have H'' := congrArg
    (fun h : R ⟶ (Spec T).residueField z => h ≫ (Scheme.Spec.residueFieldIso T z).hom) H'
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at H''
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using
    congrArg (fun h : R ⟶ CommRingCat.of z.asIdeal.ResidueField => h.hom r) H''

/-- The residue-field map of `Spec.map f`, conjugated by the comparison isomorphisms, is an
isomorphism iff the algebraic residue-field map of `f` is. -/
private lemma isIso_conj_residueFieldMap_iff
    {R S : CommRingCat.{u}} (f : R ⟶ S) (q : Spec S) :
    IsIso ((Scheme.Spec.residueFieldIso R (Spec.map f q)).inv ≫
      (Spec.map f).residueFieldMap q ≫ (Scheme.Spec.residueFieldIso S q).hom) ↔
    IsIso (CommRingCat.ofHom
      (Ideal.ResidueField.map (Spec.map f q).asIdeal q.asIdeal f.hom
        (by simpa only [Spec.map_apply] using PrimeSpectrum.comap_asIdeal f.hom q))) := by
  rw [CommRingCat.hom_ext (g := CommRingCat.ofHom _) (specResidueFieldMap_bridge f q)]
  rfl

/-- If `Spec.map f` induces an isomorphism on the scheme-theoretic residue field at `q`, then
the algebraic residue-field map of the underlying ring map is an isomorphism. -/
lemma idealResidueFieldMap_isIso_of_specMap
    {R S : CommRingCat.{u}} (f : R ⟶ S) (q : Spec S)
    (hf : IsIso ((Spec.map f).residueFieldMap q)) :
    IsIso (CommRingCat.ofHom
      (Ideal.ResidueField.map (Spec.map f q).asIdeal q.asIdeal f.hom
        (by simpa only [Spec.map_apply] using PrimeSpectrum.comap_asIdeal f.hom q))) :=
  (isIso_conj_residueFieldMap_iff f q).1 inferInstance

/-- The converse transfer: an isomorphism of algebraic residue fields gives an isomorphism of
the scheme-theoretic residue fields. -/
lemma specResidueFieldMap_isIso_of_idealResidueFieldMap
    {R S : CommRingCat.{u}} (f : R ⟶ S) (q : Spec S)
    (hf : IsIso (CommRingCat.ofHom
      (Ideal.ResidueField.map (Spec.map f q).asIdeal q.asIdeal f.hom
        (by simpa only [Spec.map_apply] using PrimeSpectrum.comap_asIdeal f.hom q)))) :
    IsIso ((Spec.map f).residueFieldMap q) := by
  have := (isIso_conj_residueFieldMap_iff f q).2 hf
  have := IsIso.of_isIso_comp_left (Scheme.Spec.residueFieldIso R (Spec.map f q)).inv
    ((Spec.map f).residueFieldMap q ≫ (Scheme.Spec.residueFieldIso S q).hom)
  exact IsIso.of_isIso_comp_right _ (Scheme.Spec.residueFieldIso S q).hom

/-- `Ideal.ResidueField.map` is functorial in the ring map. -/
lemma idealResidueFieldMap_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (I : Ideal R) [I.IsPrime] (J : Ideal S) [J.IsPrime] (K : Ideal T) [K.IsPrime]
    (f : R →+* S) (g : S →+* T)
    (hI : I = J.comap f) (hJ : J = K.comap g) :
    Ideal.ResidueField.map I K (g.comp f)
        (by rw [hI, hJ, Ideal.comap_comap f g]) =
      (Ideal.ResidueField.map J K g hJ).comp (Ideal.ResidueField.map I J f hI) := by
  apply Ideal.ResidueField.ringHom_ext
  ext r
  simp [Ideal.ResidueField.map_algebraMap, RingHom.comp_apply]

/-- The residue-field map attached to the identity ring map and two equal primes is an
isomorphism. -/
lemma idealResidueFieldMap_id_isIso
    {R : Type u} [CommRing R] (I J : Ideal R) [I.IsPrime] [J.IsPrime]
    (h : I = J) : IsIso (CommRingCat.ofHom (Ideal.ResidueField.map I J (RingHom.id R) h)) := by
  subst J
  have hm : Ideal.ResidueField.map I I (RingHom.id R) rfl = RingHom.id _ := by
    apply Ideal.ResidueField.ringHom_ext
    ext r
    show Ideal.ResidueField.map I I (RingHom.id R) rfl
        (algebraMap R I.ResidueField r) = algebraMap R I.ResidueField r
    simpa using (Ideal.ResidueField.map_algebraMap I I (RingHom.id R) rfl r)
  rw [hm]
  exact (ConcreteCategory.isIso_iff_bijective _).2 Function.bijective_id

/-- If a composite of ring maps is an isomorphism and the second factor is injective, the first
factor is an isomorphism. -/
private lemma isIso_left_of_isIso_comp {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) [IsIso (f ≫ g)] (hg : Function.Injective g.hom) :
    IsIso f :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (.of_comp_left (ConcreteCategory.bijective_of_isIso (f ≫ g)) hg)

/-- If the residue-field map of a composite `a ≫ f` at `x` is an isomorphism, then so is the
residue-field map of `f` at `a x`. -/
lemma isIso_residueFieldMap_of_isIso_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (f : Y ⟶ Z) (x : X)
    (h : IsIso ((a ≫ f).residueFieldMap x)) :
    IsIso (f.residueFieldMap (a x)) := by
  have : IsIso (f.residueFieldMap (a x) ≫ a.residueFieldMap x) :=
    (Scheme.residueFieldMap_comp a f x) ▸ h
  exact isIso_left_of_isIso_comp _ _ (a.residueFieldMap x).hom.injective

end AlgebraicGeometry

end
