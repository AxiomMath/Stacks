module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Chart
public import StacksFrontier.AlgebraicGeometry.LimitApproxFinish.StageOpenImmersion

/-!
# Tag 01Z9 with its image

`AlgebraicGeometry.isOpenImmersion_iSup_basicOpen_comp_SpecMap_of_isPullback` says that in a
cartesian square of rings, a finite union of standard opens of `Spec R'` which descend from
`Spec B` and on which that side becomes an isomorphism maps by an open immersion to `Spec B'`.
This file identifies the image: it is the union of the standard opens of the *lifts* of the
descended elements to `B'`.  At the level of the fibre-product rings this gives the two
hypotheses of the image equality of `AlgebraicGeometry.exists_isFiniteTypeOpenModel_opensRange_eq`:
that the standard opens of the charting family lie inside the image of the open immersion and
cover it.

## Main results

* `AlgebraicGeometry.apply_comm_of_isPullback`: the commutation of the square on elements.
* `AlgebraicGeometry.bijective_awayMap_of_isPullback`: Tag 01Z8, in the form
  `RingFibreProduct.isPullback_localization_away`, read as: bijectivity of the away map
  propagates across a cartesian square, from the side where it is assumed to the opposite side.
* `AlgebraicGeometry.opensRange_iSup_basicOpen_comp_SpecMap_of_isPullback`: the image equality.
* `AlgebraicGeometry.opensRange_iSup_basicOpen_comp_SpecMap_snd`: the specialization to the
  fibre product `Stacks.FibreProduct.obj`, where the lift of a compatible pair *is* that pair,
  and the two equations characterizing it hold by reflexivity.  This is the form the gluing of
  Tag 07RN consumes.

## Implementation notes

The lifts `q` are hypotheses rather than chosen elements, since the open-immersion statement
chooses them inside its proof and they do not appear in its statement; in the application they
are explicit, an element of a fibre product being a compatible pair.  The image equality rests on
the restriction of `Spec B' ⟶ Spec R'` over the standard open of each lift being an
isomorphism, which is `AlgebraicGeometry.bijective_awayMap_of_isPullback`.

One inclusion of the image equality is the inverse-image computation
`AlgebraicGeometry.SpecMap_preimage_basicOpen` applied to a point; the other is
`AlgebraicGeometry.opensRange_basicOpen_ι_comp_SpecMap`, the image of one standard open on which
the away map is bijective, composed with the inclusion of that standard open into the union.
That inclusion is `AlgebraicGeometry.Scheme.homOfLE`; its action on points is not reduced by
`rfl`, so the argument goes through the fact that it composes with the inclusion of the union to
give the inclusion of the member, rather than through the points.

The open-immersion statement is for bare types carrying `CommRing`, while the fibre product is an
object of `CommRingCat`; the bridge is that `CommRingCat.of ↥X` is `X` again and
`CommRingCat.ofHom φ.hom` is `φ`, both handled by `simp`.

The image equality is stated under a `haveI` introducing the open-immersion instance.  Two
`AlgebraicGeometry.Scheme.Hom.opensRange` terms built from different instances are equal, the
open being a structure with a propositional second field, so a consumer carrying its own instance
may use the statement unchanged; the specialization takes the instance as a hypothesis.

All four rings live in the single universe `u`.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z8](https://stacks.math.columbia.edu/tag/01Z8)
* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

section Abstract

variable {B R B' R' : Type u} [CommRing B] [CommRing R] [CommRing B'] [CommRing R']
  (s : B →+* R) (p : B' →+* B) (r : B' →+* R') (t : R' →+* R)
  (hcart : IsPullback (CommRingCat.ofHom p) (CommRingCat.ofHom r)
    (CommRingCat.ofHom s) (CommRingCat.ofHom t))

include hcart

/-- A cartesian square of rings commutes on elements. -/
lemma apply_comm_of_isPullback (b : B') : s (p b) = t (r b) :=
  congrArg (fun k : B' →+* R ↦ k b)
    (by simpa using congrArg CommRingCat.Hom.hom hcart.w)

/-- **Bijectivity of an away map crosses a cartesian square of rings.**  This is Tag 01Z8, in
the form `RingFibreProduct.isPullback_localization_away`: localizing a cartesian
square at an element of the upper left corner is again cartesian, so the side opposite to a
bijective one is bijective. -/
lemma bijective_awayMap_of_isPullback (b : B')
    (hloc : Function.Bijective (Localization.awayMap s (p b))) :
    Function.Bijective (Localization.awayMap r b) := by
  have hlocPB := RingFibreProduct.isPullback_localization_away s t p r hcart b (p b)
    (r b) rfl rfl (apply_comm_of_isPullback s p r t hcart b)
  have hs : IsIso (CommRingCat.ofHom (Localization.awayMap s (p b))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hloc
  have haway := hlocPB.isIso_snd_of_isIso
  have hmap : Localization.awayMap r b =
      Localization.awayLift ((algebraMap R' (Localization.Away (r b))).comp r) b
        (IsLocalization.Away.algebraMap_isUnit (r b)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers b)
    ext x
    simp [Localization.awayMap, IsLocalization.Away.map, Localization.awayLift]
  exact (ConcreteCategory.isIso_iff_bijective _).1 (by simpa only [hmap] using haway)

/-- **Tag 01Z9 with its image.**  In a cartesian square of rings, let `q : Fin n → B'` be
elements of the upper left corner on which the opposite side becomes an isomorphism.  Then the
union of the standard opens of their images in `R'` maps by an open immersion to `Spec B'` —
which is Tag 01Z9 — *with image exactly the union of the standard opens of the
`q i`*.

The lifts `q` are data here; in the application they are explicit, an element of a fibre
product being a compatible pair. -/
theorem opensRange_iSup_basicOpen_comp_SpecMap_of_isPullback {n : ℕ} (q : Fin n → B')
    (hloc : ∀ i, Function.Bijective (Localization.awayMap s (p (q i)))) :
    haveI := isOpenImmersion_iSup_basicOpen_comp_SpecMap_of_isPullback s p r t hcart
      (fun i ↦ r (q i)) (fun i ↦ p (q i))
      (fun i ↦ (apply_comm_of_isPullback s p r t hcart (q i)).symm) hloc
    ((⨆ i, PrimeSpectrum.basicOpen (r (q i)) : (Spec (.of R')).Opens).ι ≫
        Spec.map (CommRingCat.ofHom r)).opensRange =
      (⨆ i, PrimeSpectrum.basicOpen (q i) : (Spec (.of B')).Opens) := by
  have hoi := isOpenImmersion_iSup_basicOpen_comp_SpecMap_of_isPullback s p r t hcart
    (fun i ↦ r (q i)) (fun i ↦ p (q i))
    (fun i ↦ (apply_comm_of_isPullback s p r t hcart (q i)).symm) hloc
  refine le_antisymm (fun y hy ↦ ?_) (iSup_le fun i y hy ↦ ?_)
  · obtain ⟨x, rfl⟩ := Scheme.Hom.mem_opensRange.mp hy
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.2
    exact Opens.mem_iSup.mpr ⟨i, (SpecMap_preimage_basicOpen (CommRingCat.ofHom r) (q i)).ge hi⟩
  · have hbij := bijective_awayMap_of_isPullback s p r t hcart (q i) (hloc i)
    have hoi' := isOpenImmersion_basicOpen_ι_comp_SpecMap r (q i) hbij
    rw [← opensRange_basicOpen_ι_comp_SpecMap r (q i) hbij] at hy
    obtain ⟨z, rfl⟩ := Scheme.Hom.mem_opensRange.mp hy
    have hle : (PrimeSpectrum.basicOpen (r (q i)) : (Spec (.of R')).Opens) ≤
        (⨆ i, PrimeSpectrum.basicOpen (r (q i)) : (Spec (.of R')).Opens) :=
      le_iSup (fun i ↦ (PrimeSpectrum.basicOpen (r (q i)) : (Spec (.of R')).Opens)) i
    have hfac : (Spec (.of R')).homOfLE hle ≫
        (⨆ i, PrimeSpectrum.basicOpen (r (q i)) : (Spec (.of R')).Opens).ι ≫
          Spec.map (CommRingCat.ofHom r) =
        Scheme.Opens.ι (X := Spec (.of R')) (PrimeSpectrum.basicOpen (r (q i))) ≫
          Spec.map (CommRingCat.ofHom r) := Scheme.homOfLE_ι_assoc _ _ _
    exact Scheme.Hom.mem_opensRange.mpr ⟨(Spec (.of R')).homOfLE hle z,
      congrArg (fun k : Scheme.Opens.toScheme (X := Spec (.of R'))
        (PrimeSpectrum.basicOpen (r (q i))) ⟶ Spec (.of B') ↦ k z) hfac⟩

end Abstract

/-- **Tag 01Z9 with its image, for the fibre product of two ring maps.**  The lifts are the
compatible pairs themselves, so nothing has to be chosen: the two equations characterizing a
lift hold by reflexivity.

This is the form the one-affine-open step of Tag 07RN consumes: it discharges the two
hypotheses of `AlgebraicGeometry.exists_isFiniteTypeOpenModel_opensRange_eq` at the level of the
fibre-product ring, namely that the standard opens of the charting family lie inside the image of
the model of the overlap and cover it. -/
theorem opensRange_iSup_basicOpen_comp_SpecMap_snd {B R R' : CommRingCat.{u}} (s : B ⟶ R)
    (t : R' ⟶ R) {n : ℕ} (g : Fin n → B) (f : Fin n → R') (hf : ∀ l, s (g l) = t (f l))
    (hloc : ∀ l, Function.Bijective (Localization.awayMap s.hom (g l)))
    (_hoi : IsOpenImmersion ((⨆ l, PrimeSpectrum.basicOpen (f l) : (Spec R').Opens).ι ≫
      Spec.map (Stacks.FibreProduct.snd s t))) :
    ((⨆ l, PrimeSpectrum.basicOpen (f l) : (Spec R').Opens).ι ≫
        Spec.map (Stacks.FibreProduct.snd s t)).opensRange =
      (⨆ l, PrimeSpectrum.basicOpen (Stacks.FibreProduct.mk s t (g l) (f l) (hf l)) :
        (Spec (Stacks.FibreProduct.obj s t)).Opens) := by
  have hcart : IsPullback (CommRingCat.ofHom (Stacks.FibreProduct.fst s t).hom)
      (CommRingCat.ofHom (Stacks.FibreProduct.snd s t).hom)
      (CommRingCat.ofHom s.hom) (CommRingCat.ofHom t.hom) := by
    simpa using Stacks.FibreProduct.isPullback s t
  simpa using opensRange_iSup_basicOpen_comp_SpecMap_of_isPullback s.hom
    (Stacks.FibreProduct.fst s t).hom (Stacks.FibreProduct.snd s t).hom t.hom hcart
    (fun l ↦ Stacks.FibreProduct.mk s t (g l) (f l) (hf l)) (fun l ↦ hloc l)

end AlgebraicGeometry
