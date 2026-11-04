module

public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.ResidueField
public import StacksFrontier.RingTheory.Etale.ResidueFieldExtension
public import StacksCore.Tactic.StacksAttribute

/-!
# Realizing a prescribed residue field extension by an étale neighbourhood

Given a point `s` of a scheme `S` and a finite separable extension `k` of the residue field
`κ(s)`, there is an étale neighbourhood of `(S, s)` whose distinguished point has residue field
`k` over `κ(s)`. Together with Tag 02LE this says that the residue field extensions realized by
étale neighbourhoods are exactly the finite separable ones.

## Main results

* `AlgebraicGeometry.exists_etaleNeighborhood_residueField_algEquiv` realizes a finite
  separable extension as the residue field of an étale neighbourhood.
* `AlgebraicGeometry.exists_etaleNeighborhood_residueField_algEquiv_and_isAffine` is the same
  statement with the neighbourhood moreover affine.

## Implementation notes

The algebra structure on the residue field of the distinguished point is induced by the
canonical residue field map `AlgebraicGeometry.EtaleNeighborhood.residueFieldMap` of the
neighbourhood. Thus the algebra equivalence records compatibility with the given extension of
the base residue field, not merely an isomorphism of the underlying fields.

The construction is local on the base: after choosing an affine chart `Spec R ⟶ S` around `s`,
the extension is realized on the ring level by
`Algebra.exists_etale_liesOver_residueFieldRingEquiv` (Tag 00UD), and the resulting residue field
map is compared with the residue field map over the scheme `S`.

## References

* [Stacks Project, Tag 02LF](https://stacks.math.columbia.edu/tag/02LF)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- Along an affine chart `i : Spec R ⟶ S` of a neighbourhood of `s`, the residue field map of
the composite `Spec T ⟶ Spec R ⟶ S` agrees with the residue field map of `i` followed by the
map of residue fields of primes induced by `f : R ⟶ T`. -/
lemma chartResidueFieldMap_bridge {S : Scheme.{u}} {s : S}
    (R : CommRingCat.{u}) (i : Spec R ⟶ S) [IsOpenImmersion i]
    (y : Spec R) (hy : i y = s)
    (T : CommRingCat.{u}) (f : R ⟶ T) (z : Spec T)
    (hz : Spec.map f z = y) :
    ((S.residueFieldCongr hy).inv ≫
      (i.residueFieldMap y) ≫
      (Scheme.Spec.residueFieldIso R y).hom ≫
      CommRingCat.ofHom (Ideal.ResidueField.map y.asIdeal z.asIdeal f.hom
        (by rw [← hz]; rfl))).hom =
      ((S.residueFieldCongr (by simpa [hz] using hy)).inv ≫
        ((Spec.map f ≫ i).residueFieldMap z) ≫
        (Scheme.Spec.residueFieldIso T z).hom).hom := by
  subst y
  rw [← specResidueFieldMap_bridge f z]
  simp only [CommRingCat.ofHom_hom, Scheme.residueFieldMap_comp,
    Iso.hom_inv_id_assoc]
  rfl

/-- The construction realizing a finite separable extension of `κ(s)` étale-locally, in the
form it is produced: the neighbourhood is the spectrum of an étale algebra over an affine chart
around `s`, so its scheme is affine. Affineness is recorded here because an existential that
forgets it cannot recover it, and consumers that have to place the neighbourhood in a size
cutoff site need it. -/
@[ega "IV 18.8.6" "more general", sga "2 XIV 3.4"]
theorem exists_etaleNeighborhood_residueField_algEquiv_and_isAffine
    (S : Scheme.{u}) (s : S) (k : Type v) [Field k]
    [Algebra (S.residueField s) k]
    [Module.Finite (S.residueField s) k]
    [Algebra.IsSeparable (S.residueField s) k] :
    ∃ U : EtaleNeighborhood S s,
      letI := U.residueFieldMap.hom.toAlgebra
      Nonempty (U.scheme.residueField U.point ≃ₐ[S.residueField s] k) ∧ IsAffine U.scheme := by
  obtain ⟨R, i, _, y, hy⟩ := S.exists_Spec_apply_eq s
  let h : S.residueField s ≃+* y.asIdeal.ResidueField :=
    ((S.residueFieldCongr hy).symm ≪≫ asIso (i.residueFieldMap y) ≪≫
      Scheme.Spec.residueFieldIso R y).commRingCatIsoToRingEquiv
  let : Algebra y.asIdeal.ResidueField k :=
    ((algebraMap (S.residueField s) k).comp h.symm.toRingHom).toAlgebra
  have hcomp : (algebraMap y.asIdeal.ResidueField k).comp h.toRingHom =
      algebraMap (S.residueField s) k := by
    ext a
    change algebraMap (S.residueField s) k (h.symm (h a)) = _
    simp
  have : Module.Finite y.asIdeal.ResidueField k :=
    Module.Finite.of_equiv_equiv h (RingEquiv.refl k) hcomp
  have : Algebra.IsSeparable y.asIdeal.ResidueField k :=
    Algebra.IsSeparable.of_equiv_equiv h (RingEquiv.refl k) hcomp
  obtain ⟨T, _, _, _, q, _, _, e, he⟩ :=
    Algebra.exists_etale_liesOver_residueFieldRingEquiv y.asIdeal k
  let f : R ⟶ CommRingCat.of T := CommRingCat.ofHom (algebraMap R T)
  let z : Spec (CommRingCat.of T) := ⟨q, inferInstance⟩
  have hz : Spec.map f z = y := PrimeSpectrum.ext (q.over_def y.asIdeal).symm
  have : Etale (Spec.map f) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  let U : EtaleNeighborhood S s :=
    { scheme := Spec (CommRingCat.of T)
      point := z
      toBase := Spec.map f ≫ i
      map_point := by simpa [hz] using hy }
  refine ⟨U, ?_, inferInstance⟩
  let := U.residueFieldMap.hom.toAlgebra
  refine ⟨AlgEquiv.ofRingEquiv (f :=
    (Scheme.Spec.residueFieldIso (CommRingCat.of T) z).commRingCatIsoToRingEquiv.trans e)
      fun a => ?_⟩
  change e ((Scheme.Spec.residueFieldIso (CommRingCat.of T) z).hom
    (U.residueFieldMap.hom a)) = algebraMap (S.residueField s) k a
  have hb' : e ((Ideal.ResidueField.map y.asIdeal q (algebraMap R T)
      (q.over_def y.asIdeal)) (h a)) =
      e ((Scheme.Spec.residueFieldIso (CommRingCat.of T) z).hom
        (U.residueFieldMap.hom a)) := by
    convert congrArg (fun g : S.residueField s →+* q.ResidueField => e (g a))
      (chartResidueFieldMap_bridge R i y hy (CommRingCat.of T) f z hz) using 1 <;> rfl
  rw [← hb']
  simpa only [RingHom.comp_apply, RingEquiv.coe_toRingHom] using
    (congrArg (fun g : y.asIdeal.ResidueField →+* k => g (h a)) he).trans
      (congrArg (fun g : S.residueField s →+* k => g a) hcomp)

/-- **Stacks Project, Tag 02LF.** Every finite separable extension of the
residue field at a point is realized by the residue field at the chosen point
of an étale neighborhood. -/
@[stacks 02LF, sga "2 XIV 3.4", ega "IV 18.8.6" "more general"]
theorem exists_etaleNeighborhood_residueField_algEquiv
    (S : Scheme.{u}) (s : S) (k : Type v) [Field k]
    [Algebra (S.residueField s) k]
    [Module.Finite (S.residueField s) k]
    [Algebra.IsSeparable (S.residueField s) k] :
    ∃ U : EtaleNeighborhood S s,
      letI := U.residueFieldMap.hom.toAlgebra
      Nonempty (U.scheme.residueField U.point ≃ₐ[S.residueField s] k) := by
  obtain ⟨U, hU, -⟩ := exists_etaleNeighborhood_residueField_algEquiv_and_isAffine S s k
  exact ⟨U, hU⟩

end AlgebraicGeometry
