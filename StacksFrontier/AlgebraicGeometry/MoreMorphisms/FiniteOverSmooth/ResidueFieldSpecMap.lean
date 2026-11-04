module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The residue field map of a morphism of affine schemes

Let `φ : R ⟶ S` be a homomorphism of commutative rings and let `𝔮 ⊂ S` be a prime. The morphism
`Spec φ` carries the point `𝔮` to the point `φ⁻¹(𝔮)`, and hence induces a homomorphism
`κ(φ⁻¹(𝔮)) ⟶ κ(𝔮)` of residue fields of the schemes `Spec R` and `Spec S`. On the other hand
`φ` induces a homomorphism `κ(φ⁻¹(𝔮)) → κ(𝔮)` of residue fields of *ideals*,
`Ideal.ResidueField.map`. This file identifies the two, under the canonical isomorphisms
`Scheme.Spec.residueFieldIso`.

The identification is what lets an algebraic statement about the residue field of a prime be read
as a statement about the residue field of a scheme at a point, and conversely. It is used in
Stacks 052E to transport the purely transcendental residue field extension produced at the level
of rings to the residue field extension of the smooth morphism in the conclusion.

## Main results

* `AlgebraicGeometry.residueFieldMap_specMap`: the residue field map of `Spec φ` at `𝔮` is
  `Ideal.ResidueField.map`, conjugated by `Scheme.Spec.residueFieldIso`.
* `AlgebraicGeometry.residueFieldMap_specMap_apply`: the same identification, elementwise.
* `AlgebraicGeometry.residueFieldMap_specMap_apply_of_eq`: the elementwise form with the prime
  below presented separately.

## Implementation notes

Both residue field maps are induced by maps of local rings — the stalk map of `Spec φ` on one
side and `Localization.localRingHom` on the other — and Mathlib's
`AlgebraicGeometry.Scheme.localRingHom_comp_stalkIso` already identifies those two. The proof
therefore evaluates both sides at a residue class and appeals to the elementwise form of that
identification.

The point `Spec φ 𝔮` of `Spec R` is definitionally the prime `φ⁻¹(𝔮)`, but the two spellings are
not interchangeable at the transparency at which `rw` and typeclass inference operate: the
statement is phrased with `PrimeSpectrum.comap`, so that `IsPrime` can be found for the ideal,
and the proof is conducted with `change` and `exact`, which run at default transparency.

## References

* [Stacks Project, Tag 052E](https://stacks.math.columbia.edu/tag/052E)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The residue field map of a morphism of affine schemes.** For a ring homomorphism
`φ : R ⟶ S` and a prime `𝔮 ⊂ S`, the map `κ(Spec φ 𝔮) ⟶ κ(𝔮)` of residue fields of schemes
induced by `Spec φ` agrees with the map `κ(φ⁻¹(𝔮)) → κ(𝔮)` of residue fields of ideals, under
the canonical isomorphisms of `Scheme.Spec.residueFieldIso`. -/
theorem residueFieldMap_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S) (q : PrimeSpectrum S) :
    (Spec.map φ).residueFieldMap q =
      (Scheme.Spec.residueFieldIso R (PrimeSpectrum.comap φ.hom q)).hom ≫
        CommRingCat.ofHom
          (Ideal.ResidueField.map (PrimeSpectrum.comap φ.hom q).asIdeal q.asIdeal φ.hom rfl) ≫
        (Scheme.Spec.residueFieldIso S q).inv := by
  let : IsLocalRing ((Spec S).presheaf.stalk q) := (Spec S).toLocallyRingedSpace.isLocalRing q
  let : IsLocalRing ((Spec R).presheaf.stalk ((Spec.map φ).base q)) :=
    (Spec R).toLocallyRingedSpace.isLocalRing _
  apply CommRingCat.hom_ext
  ext z
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  show IsLocalRing.residue _ ((Spec.map φ).stalkMap q w) =
    IsLocalRing.residue _ ((Spec.stalkIso S q).inv.hom
      (Localization.localRingHom (PrimeSpectrum.comap φ.hom q).asIdeal q.asIdeal φ.hom rfl
        ((Spec.stalkIso R (PrimeSpectrum.comap φ.hom q)).hom.hom w)))
  exact congrArg (IsLocalRing.residue _) (Scheme.localRingHom_comp_stalkIso_apply φ q w).symm

/-- The elementwise form of `AlgebraicGeometry.residueFieldMap_specMap`: the canonical
isomorphisms of `Scheme.Spec.residueFieldIso` intertwine the residue field map of `Spec φ` with
`Ideal.ResidueField.map`. -/
theorem residueFieldMap_specMap_apply {R S : CommRingCat.{u}} (φ : R ⟶ S) (q : PrimeSpectrum S)
    (z : (Spec R).residueField ((Spec.map φ).base q)) :
    (Scheme.Spec.residueFieldIso S q).hom ((Spec.map φ).residueFieldMap q z) =
      Ideal.ResidueField.map (PrimeSpectrum.comap φ.hom q).asIdeal q.asIdeal φ.hom rfl
        ((Scheme.Spec.residueFieldIso R (PrimeSpectrum.comap φ.hom q)).hom z) := by
  have h : (Spec.map φ).residueFieldMap q z =
      (Scheme.Spec.residueFieldIso S q).inv
        (Ideal.ResidueField.map (PrimeSpectrum.comap φ.hom q).asIdeal q.asIdeal φ.hom rfl
          ((Scheme.Spec.residueFieldIso R (PrimeSpectrum.comap φ.hom q)).hom z)) :=
    congrArg (fun m : _ ⟶ _ => CommRingCat.Hom.hom m z) (residueFieldMap_specMap φ q)
  rw [h]
  exact (Scheme.Spec.residueFieldIso S q).inv_hom_id_apply _

/-- `AlgebraicGeometry.residueFieldMap_specMap_apply` with the point of `Spec R` and the prime
below presented separately, as they are at a call site: `𝔭` is any prime contracting from `𝔮`,
and the point of `Spec R` below `𝔮` is identified with it by `hpt`. -/
theorem residueFieldMap_specMap_apply_of_eq {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S) (hp : p.asIdeal = q.asIdeal.comap φ.hom)
    (hpt : (Spec.map φ).base q = p) (z : (Spec R).residueField p) :
    (Scheme.Spec.residueFieldIso S q).hom
        ((Spec.map φ).residueFieldMap q (((Spec R).residueFieldCongr hpt).inv z)) =
      Ideal.ResidueField.map p.asIdeal q.asIdeal φ.hom hp
        ((Scheme.Spec.residueFieldIso R p).hom z) := by
  obtain rfl : p = PrimeSpectrum.comap φ.hom q := PrimeSpectrum.ext hp
  exact residueFieldMap_specMap_apply φ q z

end AlgebraicGeometry
