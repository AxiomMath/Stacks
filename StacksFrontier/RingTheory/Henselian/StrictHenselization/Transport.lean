module

public import StacksFrontier.RingTheory.Henselian.StrictHenselization.ExistenceData
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Quotient

/-!
# Transporting a strict henselization along an isomorphism of the base ring

Let `(R, 𝔪, κ)` be a local ring, let `κ ⊆ κ^sep` be a separable algebraic closure of its residue
field and let `Rsh` be a strict henselization of `R` with respect to it. If `e : R ≃+* R'` is an
isomorphism onto another local ring, then `Rsh` is also a strict henselization of `R'`, for the
`R'`-algebra structure obtained by transporting the old one along `e` and for `κ^sep` viewed as a
separable algebraic closure of the residue field of `R'`.

`Stacks.StrictHenselization.IsStrictHenselization.reindex` moves the chosen separable algebraic
closure and leaves the base ring alone; this file moves the base ring and leaves the strict
henselization itself alone. Together they say that the predicate only depends on the local
`R`-algebra `R → Rsh` up to isomorphism, which is what makes `R^sh` well defined.

## Main results

* `Stacks.StrictHenselization.IsStrictHenselization.ofRingEquiv`: a strict henselization of `R`
  is a strict henselization of any ring isomorphic to `R`, together with the identity pinning the
  transported structure map down.

## Implementation notes

*The residue field of the new base.* Every field of `IsStrictHenselization` except the last two is
either untouched (`henselian`, `sepClosed`, `residueFieldEquiv`) or a direct transport along `e`
(`isLocalHom`, `isFilteredColimitEtale`, `maximalIdeal_map`). The remaining work is the separable
algebraic closure: `κ^sep` is an extension of `(maximalIdeal R).ResidueField`, and it has to become
one of `(maximalIdeal R').ResidueField`. The two residue fields are identified by
`Stacks.StrictHenselization.residueFieldEquivOfRingEquiv`, the bijection
`Ideal.ResidueField.map` induces because a ring isomorphism is surjective on stalks, and the
transported algebra structure together with its compatibility square is produced by
`Stacks.StrictHenselization.exists_isSepClosure_of_ringEquiv`.

Mathlib's `Ideal.residueFieldRingEquiv` is not usable here: it is stated for two primes of a
`LiesOver` pair with an `IsLiesOverAlgebra` instance on the localizations, which an isomorphism of
local rings does not provide. The compatibility of `Ideal.ResidueField.map` with composition is
instead obtained pointwise, from `Ideal.algebraMap_residueField_surjective`: the maximal ideal is
maximal, so `R → κ(𝔪)` is surjective and two ring maps out of `κ(𝔪)` agreeing on the image of `R`
are equal.

## References

* [StacksProject 04GP](https://stacks.math.columbia.edu/tag/04GP), existence of `R → R^{sh}`
* [StacksProject 04GQ](https://stacks.math.columbia.edu/tag/04GQ), the strict henselization
* [StacksProject 08HT](https://stacks.math.columbia.edu/tag/08HT), uniqueness up to unique
  isomorphism

## Tags

strict henselization, strictly henselian, separable algebraic closure, local ring, ring
isomorphism, residue field
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace Stacks.StrictHenselization

/-- **The residue field isomorphism induced by an isomorphism of local rings.** A ring
isomorphism is surjective, hence surjective on stalks, so the canonical embedding
`Ideal.ResidueField.map` of residue fields it induces at the maximal ideals is bijective. -/
public noncomputable def residueFieldEquivOfRingEquiv {R : Type u} {R' : Type v} [CommRing R]
    [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (e : R ≃+* R') :
    haveI : IsLocalHom (e : R →+* R') := IsLocalHom.of_surjective _ e.surjective
    (maximalIdeal R).ResidueField ≃+* (maximalIdeal R').ResidueField :=
  haveI : IsLocalHom (e : R →+* R') := IsLocalHom.of_surjective _ e.surjective
  RingEquiv.ofBijective
    (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal R') (e : R →+* R')
      (maximalIdeal_comap (e : R →+* R')).symm)
    ((RingHom.surjectiveOnStalks_of_surjective e.surjective).residueFieldMap_bijective _ _ _)

/-- `Stacks.StrictHenselization.residueFieldEquivOfRingEquiv` on a residue class. -/
public theorem residueFieldEquivOfRingEquiv_algebraMap {R : Type u} {R' : Type v} [CommRing R]
    [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (e : R ≃+* R') (x : R) :
    residueFieldEquivOfRingEquiv e (algebraMap R (maximalIdeal R).ResidueField x)
      = algebraMap R' (maximalIdeal R').ResidueField (e x) :=
  Ideal.ResidueField.map_algebraMap _ _ _ _ x

/-- **A strict henselization transports along an isomorphism of the base ring** (Stacks 04GQ).
Let `Rsh` be a strict henselization of the local ring `R` with respect to the separable algebraic
closure `κ^sep` of its residue field, and let `e : R ≃+* R'` be an isomorphism onto a local ring
`R'`. If `Rsh` is an `R'`-algebra and `κ^sep` an extension of the residue field of `R'` in a way
compatible with `e` — `hpin` for the structure map, `hres` for the residue field — then `Rsh` is a
strict henselization of `R'` with respect to `κ^sep`. Both compatibilities are supplied by
`Stacks.StrictHenselization.exists_isStrictHenselization_of_ringEquiv`, which transports the two
structures as well. -/
public noncomputable def IsStrictHenselization.ofRingEquiv {R : Type u} [CommRing R]
    [IsLocalRing R] {R' : Type u} [CommRing R'] [IsLocalRing R']
    {κsep : Type v} [Field κsep] [Algebra (maximalIdeal R).ResidueField κsep]
      [IsSepClosure (maximalIdeal R).ResidueField κsep]
      [Algebra (maximalIdeal R').ResidueField κsep]
      [IsSepClosure (maximalIdeal R').ResidueField κsep]
    {Rsh : Type w} [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh] [Algebra R' Rsh]
    (h : IsStrictHenselization R κsep Rsh) (e : R ≃+* R')
    (hpin : ∀ x : R, algebraMap R' Rsh (e x) = algebraMap R Rsh x)
    (hres : ∀ x : R, algebraMap (maximalIdeal R').ResidueField κsep
          (algebraMap R' (maximalIdeal R').ResidueField (e x))
        = algebraMap (maximalIdeal R).ResidueField κsep
          (algebraMap R (maximalIdeal R).ResidueField x)) :
    IsStrictHenselization R' κsep Rsh := by
  haveI := h.isLocalHom
  haveI hlocR' : IsLocalHom (algebraMap R' Rsh) := by
    refine ⟨fun {a} ha => ?_⟩
    obtain ⟨x, rfl⟩ := e.surjective a
    rw [hpin] at ha
    exact (isUnit_of_map_unit (algebraMap R Rsh) x ha).map (e : R →+* R')
  refine
    { isLocalHom := hlocR'
      henselian := h.henselian
      sepClosed := h.sepClosed
      isFilteredColimitEtale := ?_
      maximalIdeal_map := ?_
      residueFieldEquiv := h.residueFieldEquiv
      residueFieldEquiv_comp := ?_ }
  · exact StacksDraft.indEtale_of_equiv e (RingEquiv.refl Rsh)
      (fun a => (hpin a).symm) h.isFilteredColimitEtale
  · have : IsLocalHom (e : R →+* R') := IsLocalHom.of_surjective _ e.surjective
    have hm : (maximalIdeal R).map (e : R →+* R') = maximalIdeal R' := by
      rw [← IsLocalRing.maximalIdeal_comap (e : R →+* R')]
      exact Ideal.map_comap_of_surjective (e : R →+* R') e.surjective _
    rw [← hm, Ideal.map_map,
      show (algebraMap R' Rsh).comp (e : R →+* R') = algebraMap R Rsh from
        RingHom.ext fun x => hpin x]
    exact h.maximalIdeal_map
  · refine RingHom.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal R') y
    obtain ⟨r, rfl⟩ := e.surjective x
    have key := RingHom.congr_fun h.residueFieldEquiv_comp
      (algebraMap R (maximalIdeal R).ResidueField r)
    rw [RingHom.comp_apply] at key
    rw [RingHom.comp_apply, hres, key, Ideal.ResidueField.map_algebraMap,
      Ideal.ResidueField.map_algebraMap, hpin]

/-- **A strict henselization of `R` is a strict henselization of every ring isomorphic to `R`**
(Stacks 04GQ). Let `Rsh` be a strict henselization of the local ring `R` with respect to the
separable algebraic closure `κ^sep` of its residue field, and let `e : R ≃+* R'` be an isomorphism
onto a local ring `R'`. Then `Rsh` carries an `R'`-algebra structure and `κ^sep` an extension
structure over the residue field of `R'` for which `Rsh` is a strict henselization of `R'` with
respect to `κ^sep`. The returned identity `algebraMap R' Rsh (e x) = algebraMap R Rsh x` pins the
transported structure map down. -/
public theorem exists_isStrictHenselization_of_ringEquiv {R : Type u} [CommRing R] [IsLocalRing R]
    {R' : Type u} [CommRing R'] [IsLocalRing R']
    {κsep : Type v} [Field κsep] [Algebra (maximalIdeal R).ResidueField κsep]
      [IsSepClosure (maximalIdeal R).ResidueField κsep]
    {Rsh : Type w} [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (h : IsStrictHenselization R κsep Rsh) (e : R ≃+* R') :
    ∃ (_ : Algebra R' Rsh) (_ : Algebra (maximalIdeal R').ResidueField κsep)
      (_ : IsSepClosure (maximalIdeal R').ResidueField κsep),
      Nonempty (IsStrictHenselization R' κsep Rsh) ∧
        ∀ x : R, algebraMap R' Rsh (e x) = algebraMap R Rsh x := by
  have : IsLocalHom (e.symm : R' →+* R) := IsLocalHom.of_surjective _ e.symm.surjective
  let algR' : Algebra R' Rsh := ((algebraMap R Rsh).comp (e.symm : R' →+* R)).toAlgebra
  have halg : (algebraMap R' Rsh) = (algebraMap R Rsh).comp (e.symm : R' →+* R) :=
    RingHom.algebraMap_toAlgebra _
  have hpin : ∀ x : R, algebraMap R' Rsh (e x) = algebraMap R Rsh x := fun x => by
    rw [halg, RingHom.comp_apply, RingEquiv.coe_toRingHom, e.symm_apply_apply]
  obtain ⟨algκ', hsep, hκ⟩ := QuotientDescent.exists_isSepClosure_of_ringEquiv (M := κsep)
    (residueFieldEquivOfRingEquiv e)
  let := algκ'
  refine ⟨algR', algκ', hsep, ⟨h.ofRingEquiv e hpin fun x => ?_⟩, hpin⟩
  rw [← residueFieldEquivOfRingEquiv_algebraMap e x]
  exact RingHom.congr_fun hκ _

end Stacks.StrictHenselization

end
