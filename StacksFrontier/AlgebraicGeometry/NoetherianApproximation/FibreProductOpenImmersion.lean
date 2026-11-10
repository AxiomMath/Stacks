module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.RingTheory.FibreProduct.Localization
public import StacksCore.Tactic.StacksAttribute

/-!
# Open immersions from cartesian squares of rings

Consider a cartesian square of commutative rings with `B'` in the upper left, `B` in the upper
right, `R'` in the lower left and `R` in the lower right.  An open subset of `Spec R'` which is
covered by finitely many standard opens `D(f_i)` such that `f_i` comes from an element `g_i` of
`B` and such that `B_{g_i} → R_{g_i}` is an isomorphism maps by an open immersion to `Spec B'`.

## Main results

* `AlgebraicGeometry.isOpenImmersion_iSup_basicOpen_comp_SpecMap_of_isPullback` gives the open
  immersion induced on the specified finite union of standard opens.

## Implementation notes

The cartesian diagram is expressed by `CategoryTheory.IsPullback` in `CommRingCat`.  The
isomorphism `B_{g_i} ≅ R_{s(g_i)}` is expressed intrinsically by bijectivity of the canonical
localization map induced by `s`; this retains its compatibility with the maps from `B`.  The
induced morphism is the composite of the inclusion of the open subscheme with the spectrum
morphism associated to the lower horizontal ring map.

## References

* [Stacks Project, Tag 01Z9](https://stacks.math.columbia.edu/tag/01Z9)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- In a cartesian square of commutative rings, the square commutes elementwise. -/
private lemma apply_eq_apply_of_isPullback_commRingCat
    {B R B' R' : Type u} [CommRing B] [CommRing R] [CommRing B'] [CommRing R']
    {s : B →+* R} {p : B' →+* B} {r : B' →+* R'} {t : R' →+* R}
    (hcart : IsPullback (CommRingCat.ofHom p) (CommRingCat.ofHom r)
      (CommRingCat.ofHom s) (CommRingCat.ofHom t)) (x : B') : s (p x) = t (r x) :=
  congrArg (fun k : B' →+* R ↦ k x) (by simpa using congrArg CommRingCat.Hom.hom hcart.w)

/-- In a cartesian square of commutative rings, compatible elements of the two sides lift to the
fibre product corner. -/
private lemma exists_eq_and_eq_of_isPullback_commRingCat
    {B R B' R' : Type u} [CommRing B] [CommRing R] [CommRing B'] [CommRing R']
    {s : B →+* R} {p : B' →+* B} {r : B' →+* R'} {t : R' →+* R}
    (hcart : IsPullback (CommRingCat.ofHom p) (CommRingCat.ofHom r)
      (CommRingCat.ofHom s) (CommRingCat.ofHom t))
    {f : R'} {g : B} (hfg : t f = s g) : ∃ q : B', p q = g ∧ r q = f := by
  let A := MvPolynomial (Fin 1) B'
  let φB : A →+* B := MvPolynomial.eval₂Hom p (fun _ ↦ g)
  let φR : A →+* R' := MvPolynomial.eval₂Hom r (fun _ ↦ f)
  have hφ : CommRingCat.ofHom φB ≫ CommRingCat.ofHom s =
      CommRingCat.ofHom φR ≫ CommRingCat.ofHom t := by
    apply CommRingCat.hom_ext
    ext <;> simp [φB, φR, hfg, apply_eq_apply_of_isPullback_commRingCat hcart]
  obtain ⟨q, hqB, hqR⟩ := hcart.exists_lift (CommRingCat.ofHom φB) (CommRingCat.ofHom φR) hφ
  refine ⟨q.hom (MvPolynomial.X 0), ?_, ?_⟩
  · exact (ConcreteCategory.congr_hom hqB (MvPolynomial.X 0)).trans
      (MvPolynomial.eval₂Hom_X' p (fun _ ↦ g) 0)
  · exact (ConcreteCategory.congr_hom hqR (MvPolynomial.X 0)).trans
      (MvPolynomial.eval₂Hom_X' r (fun _ ↦ f) 0)

/-- In a cartesian square of commutative rings, if the localization of the right side at the
image of `q` is an isomorphism, then `Spec` of the bottom map restricted to `D(q)` is an open
immersion. -/
private lemma isOpenImmersion_SpecMap_restrict_basicOpen_of_isPullback
    {B R B' R' : Type u} [CommRing B] [CommRing R] [CommRing B'] [CommRing R']
    {s : B →+* R} {p : B' →+* B} {r : B' →+* R'} {t : R' →+* R}
    (hcart : IsPullback (CommRingCat.ofHom p) (CommRingCat.ofHom r)
      (CommRingCat.ofHom s) (CommRingCat.ofHom t))
    (q : B') (hloc : Function.Bijective (Localization.awayMap s (p q))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom r) ∣_ PrimeSpectrum.basicOpen q) := by
  have hlocPB := RingFibreProduct.isPullback_localization_away s t p r hcart
    q (p q) (r q) rfl rfl (apply_eq_apply_of_isPullback_commRingCat hcart q)
  have : IsIso (CommRingCat.ofHom (Localization.awayMap s (p q))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hloc
  have hmap : Localization.awayMap r q =
      Localization.awayLift ((algebraMap R' (Localization.Away (r q))).comp r) q (by
        rw [RingHom.comp_apply]
        exact IsLocalization.Away.algebraMap_isUnit _) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers q)
    ext x
    simp [Localization.awayMap, IsLocalization.Away.map, Localization.awayLift]
  have : IsIso (CommRingCat.ofHom (Localization.awayMap r q)) := by
    simpa only [hmap] using hlocPB.isIso_snd_of_isIso
  exact (MorphismProperty.arrow_mk_iso_iff @IsOpenImmersion
    (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom r) q)).mpr (IsOpenImmersion.of_isIso _)

/-- In a cartesian square of rings, a finite union of standard opens which descend from the
other side of the square and on which that side becomes an isomorphism maps by an open
immersion to the spectrum of the remaining corner. -/
@[stacks 01Z9]
lemma isOpenImmersion_iSup_basicOpen_comp_SpecMap_of_isPullback
    {B R B' R' : Type u} [CommRing B] [CommRing R] [CommRing B'] [CommRing R']
    (s : B →+* R) (p : B' →+* B) (r : B' →+* R') (t : R' →+* R)
    (hcart : IsPullback (CommRingCat.ofHom p) (CommRingCat.ofHom r)
      (CommRingCat.ofHom s) (CommRingCat.ofHom t))
    {n : ℕ} (f : Fin n → R') (g : Fin n → B)
    (hfg : ∀ i, t (f i) = s (g i))
    (hloc : ∀ i, Function.Bijective (Localization.awayMap s (g i))) :
    IsOpenImmersion
      ((⨆ i, PrimeSpectrum.basicOpen (f i) : (Spec (.of R')).Opens).ι ≫
        Spec.map (CommRingCat.ofHom r)) := by
  choose q hqB hqR using fun i ↦ exists_eq_and_eq_of_isPullback_commRingCat hcart (hfg i)
  let U : (Spec (.of R')).Opens := ⨆ i, PrimeSpectrum.basicOpen (f i)
  let V (i : Fin n) : (Spec (.of B')).Opens := PrimeSpectrum.basicOpen (q i)
  apply IsZariskiLocalAtTarget.of_range_subset_iSup
    (P := @IsOpenImmersion) (f := U.ι ≫ Spec.map (CommRingCat.ofHom r)) V ?_ ?_
  · rintro x ⟨y, rfl⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show y.1 ∈ ⨆ i, PrimeSpectrum.basicOpen (f i) from y.property)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
    change r (q i) ∉ y.1.asIdeal
    simpa only [hqR i] using (PrimeSpectrum.mem_basicOpen (f i) y.1).mp hi
  · intro i
    have h₂ : IsOpenImmersion (Spec.map (CommRingCat.ofHom r) ∣_ V i) :=
      isOpenImmersion_SpecMap_restrict_basicOpen_of_isPullback hcart (q i) (hqB i ▸ hloc i)
    rw [morphismRestrict_comp]
    have h₁ : IsOpenImmersion (U.ι ∣_ Spec.map (CommRingCat.ofHom r) ⁻¹ᵁ V i) :=
      IsZariskiLocalAtTarget.restrict (P := @IsOpenImmersion) inferInstance _
    exact MorphismProperty.comp_mem @IsOpenImmersion _ _ h₁ h₂

end AlgebraicGeometry
